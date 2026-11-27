#!/usr/bin/env python3
"""omega-flight Python 3 reference robotics control loop baseline.

Implements the exact bit-for-bit Q16.16 fixed-point PID + Discrete-Time CBF +
WattCBF + FIPS 180-4 SHA-256 flight recorder chain as om/flight_core.om and
ref/flight_ref.c, using Python's hashlib.sha256 as an independent oracle.
"""

import hashlib
import struct
import sys
import time

FL_Q16 = 65536
FL_DT_INV = 10000
FL_G_ACCEL = 642908160

FL_Z_MIN = 32768000
FL_Z_MAX = 7864320000
FL_VZ_MIN = -393216000
FL_VZ_MAX = 524288000
FL_AZ_MIN = -393216000
FL_AZ_MAX = 786432000
FL_TAU_Z = 2
FL_K_Z = 20001

FL_R_MAX_SQ = 62500000000
FL_PXY_MIN = -11585191936
FL_PXY_MAX = 11585191936
FL_VXY_MIN = -983040000
FL_VXY_MAX = 983040000
FL_AXY_MIN = -393216000
FL_AXY_MAX = 393216000
FL_TAU_XY = 3
FL_K_XY = 30001

FL_TILT_MIN = -29491200
FL_TILT_MAX = 29491200
FL_WTILT_MIN = -98304000
FL_WTILT_MAX = 98304000
FL_ATILT_MIN = -393216000
FL_ATILT_MAX = 393216000
FL_TAU_TILT = 1
FL_K_TILT = 10001

FL_P_MAX_MW = 800000
FL_ERR_CAP = 6553600000
FL_INT_CAP = 3276800000
FL_TERR_CAP = 131072000

REC_STRUCT = struct.Struct("<QQqqqqqqqqqqqqQQ")


def tdiv(a: int, b: int) -> int:
    """Truncating integer division toward zero (matches Omega div, C /, Lean Int.tdiv)."""
    return a // b if a >= 0 else -((-a) // b)


def clamp(x: int, lo: int, hi: int) -> int:
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x


def acbf_lo(p: int, v: int, pmin: int, vmin: int, amin: int, kc: int) -> int:
    bar = -tdiv(FL_DT_INV * (p - pmin), kc)
    vlo = vmin if vmin > bar else bar
    if v + tdiv(amin, FL_DT_INV) < vlo:
        return (vlo - v) * FL_DT_INV
    return amin


def acbf_hi(p: int, v: int, pmax: int, vmax: int, amax: int, kc: int) -> int:
    bar = tdiv(FL_DT_INV * (pmax - p), kc)
    vhi = vmax if vmax < bar else bar
    if v + tdiv(amax, FL_DT_INV) > vhi:
        return (vhi - v) * FL_DT_INV
    return amax


def power_mw(ax: int, ay: int, az: int, vz: int) -> int:
    tz = tdiv(FL_G_ACCEL + az, FL_Q16)
    tx = tdiv(-ax if ax < 0 else ax, FL_Q16)
    ty = tdiv(-ay if ay < 0 else ay, FL_Q16)
    vzp = tdiv(vz, FL_Q16) if vz > 0 else 0
    return 25 * (tz + tx + ty) + tdiv(tz * vzp, 375)


class Flight:
    __slots__ = (
        "px", "py", "pz", "vx", "vy", "vz", "roll", "pitch", "wroll", "wpitch",
        "ix", "iy", "iz", "pwr", "ticks", "ovrd",
        "tx", "ty", "tz", "troll", "tpitch",
        "watt_clamps", "epoch", "chain",
    )

    def __init__(self) -> None:
        self.px = 0
        self.py = 0
        self.pz = 655360000
        self.vx = 0
        self.vy = 0
        self.vz = 0
        self.roll = 0
        self.pitch = 0
        self.wroll = 0
        self.wpitch = 0
        self.ix = 0
        self.iy = 0
        self.iz = 0
        self.pwr = 0
        self.ticks = 0
        self.ovrd = 0
        self.tx = 0
        self.ty = 0
        self.tz = 655360000
        self.troll = 0
        self.tpitch = 0
        self.watt_clamps = 0
        self.epoch = 0
        self.chain = b"\x00" * 32

    def step_tick(self, tk: int, seal: bool) -> int:
        ph = (tk // 100000) % 4
        if ph == 0:
            self.tx, self.ty, self.tz, self.troll, self.tpitch = (
                12451840000, 11796480000, 8519680000, 0, 0
            )
        elif ph == 1:
            self.tx, self.ty, self.tz, self.troll, self.tpitch = (
                -12451840000, -12124160000, -327680000, 39321600, 0
            )
        elif ph == 2:
            self.tx, self.ty, self.tz, self.troll, self.tpitch = (
                10485760000, -11141120000, 5242880000, 0, -36044800
            )
        else:
            self.tx, self.ty, self.tz, self.troll, self.tpitch = (
                9175040000, -9830400000, 4915200000, 0, 0
            )

        # PID
        ex = clamp(self.tx - self.px, -FL_ERR_CAP, FL_ERR_CAP)
        self.ix = clamp(self.ix + tdiv(ex, FL_DT_INV), -FL_INT_CAP, FL_INT_CAP)
        uax = tdiv(ex * 3, 2) + tdiv(self.ix, 8) - tdiv(self.vx * 5, 2)

        ey = clamp(self.ty - self.py, -FL_ERR_CAP, FL_ERR_CAP)
        self.iy = clamp(self.iy + tdiv(ey, FL_DT_INV), -FL_INT_CAP, FL_INT_CAP)
        uay = tdiv(ey * 3, 2) + tdiv(self.iy, 8) - tdiv(self.vy * 5, 2)

        ez = clamp(self.tz - self.pz, -FL_ERR_CAP, FL_ERR_CAP)
        self.iz = clamp(self.iz + tdiv(ez, FL_DT_INV), -FL_INT_CAP, FL_INT_CAP)
        uaz = ez * 2 + tdiv(self.iz, 4) - tdiv(self.vz * 5, 2)

        er = clamp(self.troll - self.roll, -FL_TERR_CAP, FL_TERR_CAP)
        uar = er * 12 - self.wroll * 4

        ep = clamp(self.tpitch - self.pitch, -FL_TERR_CAP, FL_TERR_CAP)
        uap = ep * 12 - self.wpitch * 4

        # CBF bounds + shield
        ax_lo = acbf_lo(self.px, self.vx, FL_PXY_MIN, FL_VXY_MIN, FL_AXY_MIN, FL_K_XY)
        ax_hi = acbf_hi(self.px, self.vx, FL_PXY_MAX, FL_VXY_MAX, FL_AXY_MAX, FL_K_XY)
        ay_lo = acbf_lo(self.py, self.vy, FL_PXY_MIN, FL_VXY_MIN, FL_AXY_MIN, FL_K_XY)
        ay_hi = acbf_hi(self.py, self.vy, FL_PXY_MAX, FL_VXY_MAX, FL_AXY_MAX, FL_K_XY)
        az_lo = acbf_lo(self.pz, self.vz, FL_Z_MIN, FL_VZ_MIN, FL_AZ_MIN, FL_K_Z)
        az_hi = acbf_hi(self.pz, self.vz, FL_Z_MAX, FL_VZ_MAX, FL_AZ_MAX, FL_K_Z)
        ar_lo = acbf_lo(self.roll, self.wroll, FL_TILT_MIN, FL_WTILT_MIN, FL_ATILT_MIN, FL_K_TILT)
        ar_hi = acbf_hi(self.roll, self.wroll, FL_TILT_MAX, FL_WTILT_MAX, FL_ATILT_MAX, FL_K_TILT)
        ap_lo = acbf_lo(self.pitch, self.wpitch, FL_TILT_MIN, FL_WTILT_MIN, FL_ATILT_MIN, FL_K_TILT)
        ap_hi = acbf_hi(self.pitch, self.wpitch, FL_TILT_MAX, FL_WTILT_MAX, FL_ATILT_MAX, FL_K_TILT)

        sar = clamp(uar, ar_lo, ar_hi)
        sap = clamp(uap, ap_lo, ap_hi)
        ax1 = clamp(uax, ax_lo, ax_hi)
        ay1 = clamp(uay, ay_lo, ay_hi)
        az1 = clamp(uaz, az_lo, az_hi)
        p1 = power_mw(ax1, ay1, az1, self.vz)
        flags = 0

        if p1 <= FL_P_MAX_MW:
            sax, say, saz = ax1, ay1, az1
            self.pwr = p1
        else:
            self.watt_clamps += 1
            flags |= 2
            tx1 = tdiv(-ax1 if ax1 < 0 else ax1, FL_Q16)
            ty1 = tdiv(-ay1 if ay1 < 0 else ay1, FL_Q16)
            vzp = tdiv(self.vz, FL_Q16) if self.vz > 0 else 0
            remp = FL_P_MAX_MW - 25 * (tx1 + ty1)
            azcap = az_lo
            if remp > 0:
                tzm = tdiv(remp * 375, 9375 + vzp)
                azcap = tzm * FL_Q16 - FL_G_ACCEL
            hi_b = az_hi if az_hi < azcap else azcap
            if az_lo > hi_b:
                hi_b = az_lo
            az2 = clamp(az1, az_lo, hi_b)
            p2 = power_mw(ax1, ay1, az2, self.vz)
            if p2 <= FL_P_MAX_MW:
                sax, say, saz = ax1, ay1, az2
                self.pwr = p2
            else:
                sax = clamp(0, ax_lo, ax_hi)
                say = clamp(0, ay_lo, ay_hi)
                saz = az_lo
                self.pwr = power_mw(sax, say, saz, self.vz)

        if sax != uax or say != uay or saz != uaz or sar != uar or sap != uap:
            self.ovrd += 1
            flags |= 1

        # Plant
        self.vx += tdiv(sax, FL_DT_INV)
        self.px += tdiv(self.vx, FL_DT_INV)
        self.vy += tdiv(say, FL_DT_INV)
        self.py += tdiv(self.vy, FL_DT_INV)
        self.vz += tdiv(saz, FL_DT_INV)
        self.pz += tdiv(self.vz, FL_DT_INV)
        self.wroll += tdiv(sar, FL_DT_INV)
        self.roll += tdiv(self.wroll, FL_DT_INV)
        self.wpitch += tdiv(sap, FL_DT_INV)
        self.pitch += tdiv(self.wpitch, FL_DT_INV)
        self.ticks += 1

        # Safety check
        viol = 0
        xmm = tdiv(self.px, FL_Q16)
        ymm = tdiv(self.py, FL_Q16)
        if (
            self.px < FL_PXY_MIN or self.px > FL_PXY_MAX
            or self.vx < FL_VXY_MIN or self.vx > FL_VXY_MAX
            or FL_TAU_XY * self.vx > FL_PXY_MAX - self.px
            or FL_TAU_XY * self.vx < FL_PXY_MIN - self.px
            or self.py < FL_PXY_MIN or self.py > FL_PXY_MAX
            or self.vy < FL_VXY_MIN or self.vy > FL_VXY_MAX
            or FL_TAU_XY * self.vy > FL_PXY_MAX - self.py
            or FL_TAU_XY * self.vy < FL_PXY_MIN - self.py
            or self.pz < FL_Z_MIN or self.pz > FL_Z_MAX
            or self.vz < FL_VZ_MIN or self.vz > FL_VZ_MAX
            or FL_TAU_Z * self.vz > FL_Z_MAX - self.pz
            or FL_TAU_Z * self.vz < FL_Z_MIN - self.pz
            or xmm * xmm + ymm * ymm > FL_R_MAX_SQ
            or self.roll < FL_TILT_MIN or self.roll > FL_TILT_MAX
            or self.wroll < FL_WTILT_MIN or self.wroll > FL_WTILT_MAX
            or FL_TAU_TILT * self.wroll > FL_TILT_MAX - self.roll
            or FL_TAU_TILT * self.wroll < FL_TILT_MIN - self.roll
            or self.pitch < FL_TILT_MIN or self.pitch > FL_TILT_MAX
            or self.wpitch < FL_WTILT_MIN or self.wpitch > FL_WTILT_MAX
            or FL_TAU_TILT * self.wpitch > FL_TILT_MAX - self.pitch
            or FL_TAU_TILT * self.wpitch < FL_TILT_MIN - self.pitch
            or self.pwr > FL_P_MAX_MW
        ):
            viol = 1

        if seal:
            body = REC_STRUCT.pack(
                self.epoch, self.ticks,
                self.px, self.py, self.pz,
                self.vx, self.vy, self.vz,
                self.roll, self.pitch,
                sax, say, saz, self.pwr,
                self.ovrd, flags,
            )
            self.chain = hashlib.sha256(self.chain + body).digest()
            self.epoch += 1

        return viol


def main() -> int:
    fl = Flight()
    viol = 0
    t0 = time.monotonic_ns()
    for tk in range(1000000):
        viol += fl.step_tick(tk, ((tk + 1) % 100) == 0)
    t1 = time.monotonic_ns()
    print(f"BENCH_1M_NS={t1 - t0}")
    print("BENCH_1M_TICKS=1000000")
    print(f"BENCH_1M_EPOCHS={fl.epoch}")
    print(f"BENCH_1M_OVERRIDES={fl.ovrd}")
    print(f"BENCH_1M_WATT_CLAMPS={fl.watt_clamps}")
    print(f"BENCH_1M_VIOLATIONS={viol}")
    print(
        f"BENCH_1M_PX={fl.px} PY={fl.py} PZ={fl.pz} "
        f"VX={fl.vx} VY={fl.vy} VZ={fl.vz} ROLL={fl.roll} PITCH={fl.pitch}"
    )
    print(f"BENCH_1M_CHAIN_SHA256={fl.chain.hex()}")

    # 10,000 live real-time paced 10 kHz ticks (100 us hard deadline)
    fl = Flight()
    lat = [0] * 10000
    rt_viol = 0
    miss = 0
    rt0 = time.monotonic_ns()
    for tk in range(10000):
        rel = rt0 + tk * 100000
        while time.monotonic_ns() < rel:
            pass
        ts = time.monotonic_ns()
        rt_viol += fl.step_tick(tk, ((tk + 1) % 100) == 0)
        te = time.monotonic_ns()
        wns = te - ts
        lat[tk] = wns if wns > 0 else 0
        if te > rel + 100000:
            miss += 1
    rt1 = time.monotonic_ns()
    lat.sort()
    print(f"RT_10K_TOTAL_NS={rt1 - rt0}")
    print(f"RT_10K_WORK_P50_NS={lat[5000]}")
    print(f"RT_10K_WORK_P99_NS={lat[9900]}")
    print(f"RT_10K_WORK_P999_NS={lat[9990]}")
    print(f"RT_10K_WORK_MAX_NS={lat[9999]}")
    print(f"RT_10K_MISSED_100US={miss}")
    print(f"RT_10K_VIOLATIONS={rt_viol}")
    print(f"RT_10K_OVERRIDES={fl.ovrd}")
    print(f"RT_10K_CHAIN_SHA256={fl.chain.hex()}")
    return 1 if (viol or rt_viol) else 0


if __name__ == "__main__":
    sys.exit(main())
