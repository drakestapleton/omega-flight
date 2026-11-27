# omega-flight

**10 kHz Zero-Alloc Fixed-Point Control Barrier Function (`CBF`) Flight Control Core + `execpure`-Sandboxed Untrusted AI Trajectory Planner + Tamper-Proof FIPS 180-4 SHA-256 Black-Box Flight Recorder + Formal Lean 4 Inductive Safety Proof**

`omega-flight` is a pure seeded OM-2 hard-real-time flight/robotics control core compiled by the self-bootstrapped `seed/out/omc` compiler into a **26.4 KiB (`26,996 B`) zero-libc static AArch64 ELF**. It replaces opaque C++/ROS 2/Python autonomy glue with an inspectable, formally proved, kernel-sandboxed control architecture:

1. **10 kHz Deterministic Q16.16 Fixed-Point PID + Discrete-Time CBF + WattCBF Safety Shield (`om/flight_core.om`):**
   - Zero heap allocations, zero floating-point arithmetic, zero `libc` dependencies.
   - Hardware-trapped signed 64-bit arithmetic (`trap 1`, `exit 101` — Ariane-5 silent signed integer overflow is structurally impossible) and runtime bounds checks (`trap 3`, `exit 103`).
   - Uniform Q16.16 milli-SI state (`1.0 mm = 65,536`, `1.0 m = 65,536,000`, `dt = 100 us` at 10 kHz) enforcing five simultaneous discrete-time Control Barrier Functions (`h(x) >= 0`):
     - **Altitude Geofence & Braking Barrier:** `0.5 m <= z <= 120.0 m`, `-6.0 m/s <= vz <= +8.0 m/s`, `2*vz <= Z_MAX - z`, `Z_MIN - z <= 2*vz`.
     - **Horizontal Geofence & Euclidean Radius Barrier:** `|x|, |y| <= 176.776 m` (provably inscribing `x^2 + y^2 <= (250.0 m)^2`), `|vx|, |vy| <= 15.0 m/s`, `3*|v| <= R_BOX - |p|`.
     - **Attitude Tilt Barrier:** `|roll|, |pitch| <= 0.45 rad (~25.78 deg)`, `|wroll|, |wpitch| <= 1.5 rad/s`, `|w| <= TILT_MAX - |theta|`.
     - **Actuator Thrust/Acceleration Envelope:** `az in [-6.0, +12.0] m/s^2`, `ax, ay in [-6.0, +6.0] m/s^2`, `ar, ap in [-6.0, +6.0] rad/s^2`.
     - **WattCBF Electrical Power Ceiling:** `P(ax, ay, az, vz) <= 800 W` (`800,000 mW`) with provably non-empty intersection with worst-case geofence braking (`<= 754.53 W` climbing / `<= 620.23 W` descending).
2. **Untrusted AI/RL Trajectory Planner Sandboxed Inside Linux `execpure` (`om/flight_gate.om`, `om/planner_*.om`):**
   - Executes untrusted `.om` planner binaries inside Omega's built-in kernel sandbox **`execpure`** (Landlock ABI-3 + 27-instruction seccomp-BPF stdio-only profile + `PR_SET_NO_NEW_PRIVS` + 7 `prlimit64` ceilings + `close_range(3, ...)`).
   - Hostile filesystem (`fopen("/etc/passwd")`) and network (`socknew`) attacks return `-1` (`-EPERM`) from the kernel while the flight controller seamlessly engages safe hover PID fallback.
   - Hallucinating dive/geofence-breach/tilt-flip planners (`+-999 m/s^2`) are mathematically clamped in nanoseconds by the CBF shield (`100%` of ticks `h(x_{t+1}) >= 0`).
   - Infinite-loop planners are killed deterministically by Omega's loop-bound trap (`trap 4`, `exit 104`) with zero control-loop freeze.
3. **Tamper-Proof FIPS 180-4 SHA-256 Black-Box Flight Recorder (`om/flight_core.om` + `seed/ng/sha256.om`):**
   - Chains 160-byte canonical little-endian telemetry/CBF-override epochs (`H_k = SHA256(H_{k-1} || record_k)`) using Omega's pure `.om` FIPS 180-4 SHA-256.
   - Independently matches Python 3 `hashlib.sha256` and C11 bit-for-bit across 10,000 chained epochs (`1,000,000` ticks); a single 1-bit flip in any epoch fails verification.
4. **Standalone Formal Lean 4 Safety Proof (`proof/FlightCbfSafety.lean`):**
   - **Status: `PROVED`** under `Lean 4.36.0` (zero external imports / zero Mathlib dependency, **`0 sorry`**, zero `native_decide`, zero custom axioms).
   - Proves `cbf_step_preserves_safe` (1-step safety + Euclidean radius + WattCBF `<= 800 W` for arbitrary `u_ai : Cmd`), `cbf_inductive_safety` (`forall t : Nat` by induction for any infinite adversarial planner sequence `u_seq : Nat -> Cmd`), and the non-vacuous negative control `unshielded_dive_violates_safety` (without `cbfShield`, a single hostile dive from a safe hover state breaches `Z_MIN`).

---

## Measured Results (`MEASURED_DGX_SPARK_GRACE_A64`, `taskset -c 17`)

Measured on DGX Spark Grace AArch64 (`Linux 7.0.0-1019-nvidia`, dedicated Cortex-X925 core `17`, 5 paired interleaved trials, pinned `seed/out/omc` `28fca13d...072`, `gcc 13.3.0 -O3 -mcpu=native`, `Python 3.12.3`). Full raw trials live in [`docs/evidence/results.json`](docs/evidence/results.json) and [`docs/evidence/RECEIPT.md`](docs/evidence/RECEIPT.md).

### 1. Head-to-Head Control Loop Performance (1,000,000 Ticks + 10,000 Live 10 kHz Paced Ticks)

| Engine | 1M Ticks Median | Throughput | ns/tick (1M) | RT 10 kHz Work `p50` / `p99` / `p99.9` / `max` | Missed 100 us Deadlines (5 trials) | Binary Size | Linkage | Safety & Parity |
|---|---:|---:|---:|---:|---|---:|---|---|
| **Pure OM-2 `omega-flight`** | **145.04 ms** | **6,894,814 ticks/s** | **145.04 ns** | **256 / 3,904 / 4,032 / 4,176 ns** *(worst 18.6 us)* | `0` median (`[23,0,0,0,0]`, 0 compute overruns) | **26.36 KiB** (`26,996 B`) | Static ELF, **zero libc** | Trap-1 overflow + Trap-3 bounds + `EXACT_3WAY_PARITY` |
| **C11 `gcc -O3 -mcpu=native`** | 33.10 ms | 30,216,000 ticks/s | 33.10 ns | 48 / 992 / 1,056 / 1,072 ns *(worst 1.17 us)* | `2` median (`[7,2,3,1,0]`, 0 compute overruns) | 69.27 KiB (`70,936 B`) | Dynamic PIE (`libc.so.6`) | Signed overflow UB, no bounds checks, `EXACT_3WAY_PARITY` |
| **Python 3.12.3** | 4,520.46 ms | 221,217 ticks/s | 4,520.46 ns | 4,832 / 5,344 / 6,000 / 32,448 ns *(worst 91.7 us)* | `0` median (`[0,0,0,0,0]`) | Interpreter (`~25+ MiB` runtime) | CPython + OpenSSL | `EXACT_3WAY_PARITY` (OpenSSL HW SHA256-CE) |

- **Speedups:** Pure OM-2 is **`31.17x` faster** than Python 3 on 1,000,000 flight ticks (and `18.9x` lower RT `p50`, `7.8x` lower median `max` latency, avoiding Python's `91.7 us` GC/interpreter spike near the `100 us` wall). C `gcc -O3 -mcpu=native` is `4.38x` faster than Pure OM-2 on raw throughput (see Honest Caveats below).
- **3-Way Bit-Exact Parity (`EXACT_3WAY_PARITY`):** Across all 15 runs (5 trials × 3 engines), final 10-DOF state, `853,354` CBF overrides, `81,902` WattCBF clamps, `0` safety violations, and both 256-bit SHA-256 flight-recorder chain heads match bit-for-bit:
  - 1,000,000-tick chain (`10,000` epochs): `9e705d9cc99f4f7e4398b7d33f3921b12e4be3b2b2e3093bf546425eeb7053c5`
  - 10,000-tick RT chain (`100` epochs): `5d3653b39ff79c4359ff3bb0c4f82109dbb9d505a5a9b3b272c5e4826f7e5800`

### 2. Hostile AI Planner Attack Battery & Negative Controls (`om/flight_gate.om`, 3 Runs on CPU 17)

| Test | Scenario | Expected & Observed Outcome | Median Containment Latency | Verdict |
|---|---|---|---:|---|
| `T1_BENIGN_EXECPURE` | Benign `.om` waypoint planner inside `execpure` | `rc=0`, valid 48B command, CBF-checked, epoch sealed | `592.1 us` (`592,101 ns`) | **PASS** |
| `T2_HOSTILE_FS_NET_EXECPURE` | Hostile planner tries `fopen("/etc/passwd")` + `socknew(AF_INET)` inside `execpure` | Both return `-1` (`-EPERM`), `rc=77`, 0B stdout, 100 safe hover fallback ticks (`violations=0`) | `467.5 us` (`467,491 ns`) | **PASS** |
| `T2B_NEGCTRL_UNSANDBOXED_FS_NET` | **Negative control:** exact same binary launched via `execprog` (no `execpure`) | Opens `/etc/passwd` / socket -> `rc=99` (`SANDBOX_BREACH`), proving real kernel enforcement | — | **PASS** |
| `T3_HOSTILE_DIVE_CBF_SHIELD` | Hallucinating planner outputs `+-999 m/s^2` dive/geofence/tilt-flip from CBF boundary (`z=2.5m, vz=-1.0m/s`) | `rc=0`, CBF clamps `1,000/1,000` ticks, `violations=0`, `P=557.1 W <= 800 W`, `z=2.40 m >= 0.50 m` | `468.0 us` (`467,956 ns`) | **PASS** |
| `T4_HOSTILE_LOOP_TRAP4` | Hostile planner enters infinite loop inside `execpure` | Deterministically killed by Omega `trap 4` (`rc=104`), zero loop freeze, 100 safe hover ticks | `727.1 us` (`727,110 ns`) | **PASS** |
| `T5_ARIANE5_OVERFLOW_TRAP1` | Signed 64-bit integer overflow probe inside `execpure` | Deterministically trapped by hardware `trap 1` (`rc=101`), silent wrap impossible | `433.4 us` (`433,380 ns`) | **PASS** |
| `T6_SHA256_BLACKBOX_TAMPER` | Verify multi-epoch flight recorder chain, flip 1 bit (`xor 1`) in epoch #1 `pz`, restore | Clean `PASS` -> 1-bit tamper `FAIL` -> restored `PASS` | — | **PASS** |

### 3. Formal Lean 4 Proof (`proof/FlightCbfSafety.lean`)

Verified with `lean proof/FlightCbfSafety.lean` (Lean `4.36.0`, zero imports, zero warnings, zero `sorry`):
- `cbf_step_preserves_safe` — axioms: `[propext, Classical.choice, Quot.sound]`
- `cbf_inductive_safety` — axioms: `[propext, Classical.choice, Quot.sound]`
- `initHover_safe` — axioms: *none* (`[]`)
- `floorHover_safe` — axioms: *none* (`[]`)
- `unshielded_dive_violates_safety` *(negative control)* — axioms: `[propext, Quot.sound]`
- `shielded_dive_stays_safe` — axioms: `[propext, Classical.choice, Quot.sound]`

---

## Repository Layout

- `om/prelude_om2.om` — OM-2 unit header for concatenated builds.
- `om/flight_core.om` — Q16.16 PID controller, 5-axis discrete-time CBF + WattCBF safety shield, symplectic Euler plant, and FIPS 180-4 SHA-256 flight recorder chain.
- `om/flight_bench.om` — 1,000,000-tick throughput + 10,000-tick real-time paced 10 kHz benchmark binary.
- `om/flight_gate.om` — 7-check hostile planner attack battery, negative controls, and 1-bit SHA-256 tamper gate.
- `om/planner_good.om`, `om/planner_fs_net.om`, `om/planner_dive.om`, `om/planner_loop.om`, `om/probe_overflow.om` — Untrusted `.om` planner binaries and Ariane-5 overflow probe (`284 B` to `2,168 B` static ELFs).
- `proof/FlightCbfSafety.lean` — Standalone Lean 4 formal inductive CBF + WattCBF safety proof and unshielded negative control.
- `ref/flight_ref.c`, `ref/flight_ref.py` — Bit-exact C11 and Python 3 reference baselines.
- `scripts/run_all_spark.sh` — Reproducible build, Lean 4 check, attack gate, 3-way parity check, and 5-trial H2H benchmark harness.
- `docs/evidence/` — [`RECEIPT.md`](docs/evidence/RECEIPT.md), [`results.json`](docs/evidence/results.json), and [`SHA256SUMS.txt`](docs/evidence/SHA256SUMS.txt).

## Reproducing on Linux AArch64 (DGX Spark)

```bash
# Requires pinned seed/out/omc (sha256 28fca13d...072), seed/ng/sha256.om, gcc, python3, and lean 4.36.0
BENCH_CPU=17 TRIALS=5 bash scripts/run_all_spark.sh

# Verify standalone Lean 4 proof directly (zero dependencies beyond Lean 4)
lean proof/FlightCbfSafety.lean

# Verify evidence checksums
shasum -a 256 -c docs/evidence/SHA256SUMS.txt
```

## Honest Caveats & Limits

1. **C `gcc -O3 -mcpu=native` beats Pure OM-2 by `4.38x` on raw 1M-tick throughput (`33.10 ms` vs `145.04 ms`).** GCC eliminates signed overflow checks (undefined behavior in C), eliminates array bounds checks, replaces `div 10000` with magic multiply-shifts, and aggressively inlines/unrolls SHA-256. Pure OM-2 retains mandatory hardware overflow traps (`trap 1`), array bounds checks (`trap 3`), loop bounds (`trap 4`), and uses the unspecialized `seed/ng/sha256.om` (which accounts for ~38 ms of the 145 ms across 10,000 epochs, explaining the `3.9 us` `p99` on epoch-sealing ticks vs `256 ns` `p50` on non-sealing ticks).
2. **Linux `PREEMPT_DYNAMIC` kernel jitter vs hard RTOS / `PREEMPT_RT`:** Both Pure OM-2 (`[23,0,0,0,0]` misses across 5×10,000 ticks, median `0`) and C (`[7,2,3,1,0]`, median `2`) experienced occasional wall-clock 100 us catch-up misses on a single trial despite **0/50,000 compute overruns** (OM-2 max compute `18.6 us`, C max compute `1.17 us`). Those wall-clock misses come from Linux `PREEMPT_DYNAMIC` timer/RCU preemptions on a non-`isolcpus`, non-`SCHED_FIFO` shared host core. Production 10 kHz hard-RT deployment requires `isolcpus`/`nohz_full` + `PREEMPT_RT` (or bare-metal Aienux/RTOS).
3. **`execpure` planner architecture & latency:** `execpure` spawns a fresh OS process (`fork` + Landlock ABI-3 + seccomp-BPF + 7 `prlimit64` + `execveat`), taking `~433–727 us` round-trip. Consequently, untrusted AI planners run asynchronously on an **outer guidance loop (10–100 Hz)** feeding setpoints/commands to the **10 kHz inner PID+CBF loop**, never blocking the 100 us inner tick.
4. **Shared-kernel sandbox & AArch64 scope:** `execpure` is a Linux AArch64 shared-kernel syscall/filesystem sandbox (Landlock + seccomp-BPF returning `-EPERM`), not a hardware-virtualized KVM microVM, and `target x86linux` refuses `execpure` with compiler error 25.
5. **Model-to-system boundary of the Lean 4 proof:** `proof/FlightCbfSafety.lean` proves safety for the exact discrete-time Q16.16 mathematical model (constants, `Int.tdiv`, `cbfShield`, `powerMw`, and symplectic Euler dynamics) copied verbatim from `om/flight_core.om`. It does not verify physical drone aerodynamics, wind disturbances, sensor noise, or the `omc` compiler binary itself; real flight hardware requires empirical disturbance-margin sizing and HIL/flight-test qualification.
