/* omega-flight C11 reference baseline (gcc -O3 -mcpu=native)
 * Bit-for-bit identical Q16.16 PID + Discrete-Time CBF + WattCBF + SHA-256 flight recorder
 * compared against pure seeded OM-2 om/flight_core.om + om/flight_bench.om.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static const int64_t FL_Q16       = 65536LL;
static const int64_t FL_DT_INV    = 10000LL;
static const int64_t FL_G_ACCEL   = 642908160LL;

static const int64_t FL_Z_MIN     = 32768000LL;
static const int64_t FL_Z_MAX     = 7864320000LL;
static const int64_t FL_VZ_MIN    = -393216000LL;
static const int64_t FL_VZ_MAX    = 524288000LL;
static const int64_t FL_AZ_MIN    = -393216000LL;
static const int64_t FL_AZ_MAX    = 786432000LL;
static const int64_t FL_TAU_Z     = 2LL;
static const int64_t FL_K_Z       = 20001LL;

static const int64_t FL_R_MAX_SQ  = 62500000000LL;
static const int64_t FL_PXY_MIN   = -11585191936LL;
static const int64_t FL_PXY_MAX   = 11585191936LL;
static const int64_t FL_VXY_MIN   = -983040000LL;
static const int64_t FL_VXY_MAX   = 983040000LL;
static const int64_t FL_AXY_MIN   = -393216000LL;
static const int64_t FL_AXY_MAX   = 393216000LL;
static const int64_t FL_TAU_XY    = 3LL;
static const int64_t FL_K_XY      = 30001LL;

static const int64_t FL_TILT_MIN  = -29491200LL;
static const int64_t FL_TILT_MAX  = 29491200LL;
static const int64_t FL_WTILT_MIN = -98304000LL;
static const int64_t FL_WTILT_MAX = 98304000LL;
static const int64_t FL_ATILT_MIN = -393216000LL;
static const int64_t FL_ATILT_MAX = 393216000LL;
static const int64_t FL_TAU_TILT  = 1LL;
static const int64_t FL_K_TILT    = 10001LL;

static const int64_t FL_P_MAX_MW  = 800000LL;
static const int64_t FL_ERR_CAP   = 6553600000LL;
static const int64_t FL_INT_CAP   = 3276800000LL;
static const int64_t FL_TERR_CAP  = 131072000LL;

/* FIPS 180-4 SHA-256 */
static const uint32_t SHA_K[64] = {
  0x428a2f98u,0x71374491u,0xb5c0fbcfu,0xe9b5dba5u,0x3956c25bu,0x59f111f1u,0x923f82a4u,0xab1c5ed5u,
  0xd807aa98u,0x12835b01u,0x243185beu,0x550c7dc3u,0x72be5d74u,0x80deb1feu,0x9bdc06a7u,0xc19bf174u,
  0xe49b69c1u,0xefbe4786u,0x0fc19dc6u,0x240ca1ccu,0x2de92c6fu,0x4a7484aau,0x5cb0a9dcu,0x76f988dau,
  0x983e5152u,0xa831c66du,0xb00327c8u,0xbf597fc7u,0xc6e00bf3u,0xd5a79147u,0x06ca6351u,0x14292967u,
  0x27b70a85u,0x2e1b2138u,0x4d2c6dfcu,0x53380d13u,0x650a7354u,0x766a0abbu,0x81c2c92eu,0x92722c85u,
  0xa2bfe8a1u,0xa81a664bu,0xc24b8b70u,0xc76c51a3u,0xd192e819u,0xd6990624u,0xf40e3585u,0x106aa070u,
  0x19a4c116u,0x1e376c08u,0x2748774cu,0x34b0bcb5u,0x391c0cb3u,0x4ed8aa4au,0x5b9cca4fu,0x682e6ff3u,
  0x748f82eeu,0x78a5636fu,0x84c87814u,0x8cc70208u,0x90befffau,0xa4506cebu,0xbef9a3f7u,0xc67178f2u
};

static inline uint32_t ror32(uint32_t x, unsigned n) { return (x >> n) | (x << (32u - n)); }

static void sha256_block(uint32_t h[8], const uint8_t blk[64]) {
  uint32_t w[64];
  for (int i = 0; i < 16; i++) {
    w[i] = ((uint32_t)blk[4*i] << 24) | ((uint32_t)blk[4*i+1] << 16) |
           ((uint32_t)blk[4*i+2] << 8) | (uint32_t)blk[4*i+3];
  }
  for (int i = 16; i < 64; i++) {
    uint32_t s0 = ror32(w[i-15], 7) ^ ror32(w[i-15], 18) ^ (w[i-15] >> 3);
    uint32_t s1 = ror32(w[i-2], 17) ^ ror32(w[i-2], 19) ^ (w[i-2] >> 10);
    w[i] = w[i-16] + s0 + w[i-7] + s1;
  }
  uint32_t a=h[0], b=h[1], c=h[2], d=h[3], e=h[4], f=h[5], g=h[6], hh=h[7];
  for (int i = 0; i < 64; i++) {
    uint32_t S1 = ror32(e, 6) ^ ror32(e, 11) ^ ror32(e, 25);
    uint32_t ch = (e & f) ^ ((~e) & g);
    uint32_t t1 = hh + S1 + ch + SHA_K[i] + w[i];
    uint32_t S0 = ror32(a, 2) ^ ror32(a, 13) ^ ror32(a, 22);
    uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
    uint32_t t2 = S0 + maj;
    hh = g; g = f; f = e; e = d + t1;
    d = c; c = b; b = a; a = t1 + t2;
  }
  h[0]+=a; h[1]+=b; h[2]+=c; h[3]+=d; h[4]+=e; h[5]+=f; h[6]+=g; h[7]+=hh;
}

static void sha256_bytes(const uint8_t *data, size_t n, uint8_t dig[32]) {
  uint32_t h[8] = {
    0x6a09e667u,0xbb67ae85u,0x3c6ef372u,0xa54ff53au,
    0x510e527fu,0x9b05688cu,0x1f83d9abu,0x5be0cd19u
  };
  size_t off = 0;
  while (off + 64 <= n) { sha256_block(h, data + off); off += 64; }
  uint8_t pad[128];
  memset(pad, 0, sizeof(pad));
  size_t rem = n - off;
  memcpy(pad, data + off, rem);
  pad[rem] = 0x80u;
  size_t end_len = (rem >= 56) ? 128 : 64;
  uint64_t bits = (uint64_t)n * 8ULL;
  for (int i = 0; i < 8; i++) pad[end_len - 1 - i] = (uint8_t)((bits >> (i * 8)) & 0xffu);
  sha256_block(h, pad);
  if (end_len == 128) sha256_block(h, pad + 64);
  for (int i = 0; i < 8; i++) {
    dig[4*i+0] = (uint8_t)(h[i] >> 24);
    dig[4*i+1] = (uint8_t)(h[i] >> 16);
    dig[4*i+2] = (uint8_t)(h[i] >> 8);
    dig[4*i+3] = (uint8_t)(h[i]);
  }
}

typedef struct {
  int64_t px, py, pz, vx, vy, vz, roll, pitch, wroll, wpitch;
  int64_t ix, iy, iz, pwr, ticks, ovrd;
  int64_t tx, ty, tz, troll, tpitch;
  int64_t u[5], s[5];
  uint64_t watt_clamps;
  uint64_t epoch;
  uint8_t chain[32];
} Flight;

static inline int64_t fl_clamp(int64_t x, int64_t lo, int64_t hi) {
  return x < lo ? lo : (x > hi ? hi : x);
}
static inline int64_t fl_abs(int64_t x) { return x < 0 ? -x : x; }
static inline int64_t fl_min(int64_t a, int64_t b) { return a < b ? a : b; }
static inline int64_t fl_max(int64_t a, int64_t b) { return a > b ? a : b; }

static inline int64_t fl_acbf_lo(int64_t p, int64_t v, int64_t pmin, int64_t vmin, int64_t amin, int64_t kc) {
  int64_t bar = -((FL_DT_INV * (p - pmin)) / kc);
  int64_t vlo = fl_max(vmin, bar);
  if (v + (amin / FL_DT_INV) < vlo) return (vlo - v) * FL_DT_INV;
  return amin;
}

static inline int64_t fl_acbf_hi(int64_t p, int64_t v, int64_t pmax, int64_t vmax, int64_t amax, int64_t kc) {
  int64_t bar = (FL_DT_INV * (pmax - p)) / kc;
  int64_t vhi = fl_min(vmax, bar);
  if (v + (amax / FL_DT_INV) > vhi) return (vhi - v) * FL_DT_INV;
  return amax;
}

static inline int64_t fl_power_mw(int64_t ax, int64_t ay, int64_t az, int64_t vz) {
  int64_t tz = (FL_G_ACCEL + az) / FL_Q16;
  int64_t tx = fl_abs(ax) / FL_Q16;
  int64_t ty = fl_abs(ay) / FL_Q16;
  int64_t vzp = vz > 0 ? (vz / FL_Q16) : 0;
  return 25LL * (tz + tx + ty) + (tz * vzp) / 375LL;
}

static inline int fl_check_safe(const Flight *f) {
  if (f->px < FL_PXY_MIN || f->px > FL_PXY_MAX || f->vx < FL_VXY_MIN || f->vx > FL_VXY_MAX) return 0;
  if (FL_TAU_XY * f->vx > FL_PXY_MAX - f->px || FL_TAU_XY * f->vx < FL_PXY_MIN - f->px) return 0;
  if (f->py < FL_PXY_MIN || f->py > FL_PXY_MAX || f->vy < FL_VXY_MIN || f->vy > FL_VXY_MAX) return 0;
  if (FL_TAU_XY * f->vy > FL_PXY_MAX - f->py || FL_TAU_XY * f->vy < FL_PXY_MIN - f->py) return 0;
  if (f->pz < FL_Z_MIN || f->pz > FL_Z_MAX || f->vz < FL_VZ_MIN || f->vz > FL_VZ_MAX) return 0;
  if (FL_TAU_Z * f->vz > FL_Z_MAX - f->pz || FL_TAU_Z * f->vz < FL_Z_MIN - f->pz) return 0;
  int64_t xmm = f->px / FL_Q16, ymm = f->py / FL_Q16;
  if (xmm * xmm + ymm * ymm > FL_R_MAX_SQ) return 0;
  if (f->roll < FL_TILT_MIN || f->roll > FL_TILT_MAX || f->wroll < FL_WTILT_MIN || f->wroll > FL_WTILT_MAX) return 0;
  if (FL_TAU_TILT * f->wroll > FL_TILT_MAX - f->roll || FL_TAU_TILT * f->wroll < FL_TILT_MIN - f->roll) return 0;
  if (f->pitch < FL_TILT_MIN || f->pitch > FL_TILT_MAX || f->wpitch < FL_WTILT_MIN || f->wpitch > FL_WTILT_MAX) return 0;
  if (FL_TAU_TILT * f->wpitch > FL_TILT_MAX - f->pitch || FL_TAU_TILT * f->wpitch < FL_TILT_MIN - f->pitch) return 0;
  if (f->pwr > FL_P_MAX_MW) return 0;
  return 1;
}

static void fl_init(Flight *f) {
  memset(f, 0, sizeof(*f));
  f->pz = 655360000LL;
  f->tz = 655360000LL;
}

static inline void fl_set_mission_target(Flight *f, uint64_t tk) {
  uint64_t ph = (tk / 100000ULL) % 4ULL;
  if (ph == 0) {
    f->tx = 12451840000LL; f->ty = 11796480000LL; f->tz = 8519680000LL; f->troll = 0; f->tpitch = 0;
  } else if (ph == 1) {
    f->tx = -12451840000LL; f->ty = -12124160000LL; f->tz = -327680000LL; f->troll = 39321600LL; f->tpitch = 0;
  } else if (ph == 2) {
    f->tx = 10485760000LL; f->ty = -11141120000LL; f->tz = 5242880000LL; f->troll = 0; f->tpitch = -36044800LL;
  } else {
    f->tx = 9175040000LL; f->ty = -9830400000LL; f->tz = 4915200000LL; f->troll = 0; f->tpitch = 0;
  }
}

static inline void fl_pid_step(Flight *f) {
  int64_t ex = fl_clamp(f->tx - f->px, -FL_ERR_CAP, FL_ERR_CAP);
  f->ix = fl_clamp(f->ix + ex / FL_DT_INV, -FL_INT_CAP, FL_INT_CAP);
  f->u[0] = (ex * 3LL) / 2LL + f->ix / 8LL - (f->vx * 5LL) / 2LL;

  int64_t ey = fl_clamp(f->ty - f->py, -FL_ERR_CAP, FL_ERR_CAP);
  f->iy = fl_clamp(f->iy + ey / FL_DT_INV, -FL_INT_CAP, FL_INT_CAP);
  f->u[1] = (ey * 3LL) / 2LL + f->iy / 8LL - (f->vy * 5LL) / 2LL;

  int64_t ez = fl_clamp(f->tz - f->pz, -FL_ERR_CAP, FL_ERR_CAP);
  f->iz = fl_clamp(f->iz + ez / FL_DT_INV, -FL_INT_CAP, FL_INT_CAP);
  f->u[2] = ez * 2LL + f->iz / 4LL - (f->vz * 5LL) / 2LL;

  int64_t er = fl_clamp(f->troll - f->roll, -FL_TERR_CAP, FL_TERR_CAP);
  f->u[3] = er * 12LL - f->wroll * 4LL;

  int64_t ep = fl_clamp(f->tpitch - f->pitch, -FL_TERR_CAP, FL_TERR_CAP);
  f->u[4] = ep * 12LL - f->wpitch * 4LL;
}

static inline uint64_t fl_cbf_shield(Flight *f) {
  int64_t ax_lo = fl_acbf_lo(f->px, f->vx, FL_PXY_MIN, FL_VXY_MIN, FL_AXY_MIN, FL_K_XY);
  int64_t ax_hi = fl_acbf_hi(f->px, f->vx, FL_PXY_MAX, FL_VXY_MAX, FL_AXY_MAX, FL_K_XY);
  int64_t ay_lo = fl_acbf_lo(f->py, f->vy, FL_PXY_MIN, FL_VXY_MIN, FL_AXY_MIN, FL_K_XY);
  int64_t ay_hi = fl_acbf_hi(f->py, f->vy, FL_PXY_MAX, FL_VXY_MAX, FL_AXY_MAX, FL_K_XY);
  int64_t az_lo = fl_acbf_lo(f->pz, f->vz, FL_Z_MIN, FL_VZ_MIN, FL_AZ_MIN, FL_K_Z);
  int64_t az_hi = fl_acbf_hi(f->pz, f->vz, FL_Z_MAX, FL_VZ_MAX, FL_AZ_MAX, FL_K_Z);
  int64_t ar_lo = fl_acbf_lo(f->roll, f->wroll, FL_TILT_MIN, FL_WTILT_MIN, FL_ATILT_MIN, FL_K_TILT);
  int64_t ar_hi = fl_acbf_hi(f->roll, f->wroll, FL_TILT_MAX, FL_WTILT_MAX, FL_ATILT_MAX, FL_K_TILT);
  int64_t ap_lo = fl_acbf_lo(f->pitch, f->wpitch, FL_TILT_MIN, FL_WTILT_MIN, FL_ATILT_MIN, FL_K_TILT);
  int64_t ap_hi = fl_acbf_hi(f->pitch, f->wpitch, FL_TILT_MAX, FL_WTILT_MAX, FL_ATILT_MAX, FL_K_TILT);

  f->s[3] = fl_clamp(f->u[3], ar_lo, ar_hi);
  f->s[4] = fl_clamp(f->u[4], ap_lo, ap_hi);

  int64_t ax1 = fl_clamp(f->u[0], ax_lo, ax_hi);
  int64_t ay1 = fl_clamp(f->u[1], ay_lo, ay_hi);
  int64_t az1 = fl_clamp(f->u[2], az_lo, az_hi);
  int64_t p1 = fl_power_mw(ax1, ay1, az1, f->vz);
  uint64_t flags = 0;

  if (p1 <= FL_P_MAX_MW) {
    f->s[0] = ax1; f->s[1] = ay1; f->s[2] = az1; f->pwr = p1;
  } else {
    f->watt_clamps++;
    flags |= 2ULL;
    int64_t tx1 = fl_abs(ax1) / FL_Q16;
    int64_t ty1 = fl_abs(ay1) / FL_Q16;
    int64_t vzp = f->vz > 0 ? (f->vz / FL_Q16) : 0;
    int64_t remp = FL_P_MAX_MW - 25LL * (tx1 + ty1);
    int64_t azcap = az_lo;
    if (remp > 0) {
      int64_t tzm = (remp * 375LL) / (9375LL + vzp);
      azcap = tzm * FL_Q16 - FL_G_ACCEL;
    }
    int64_t az2 = fl_clamp(az1, az_lo, fl_max(az_lo, fl_min(az_hi, azcap)));
    int64_t p2 = fl_power_mw(ax1, ay1, az2, f->vz);
    if (p2 <= FL_P_MAX_MW) {
      f->s[0] = ax1; f->s[1] = ay1; f->s[2] = az2; f->pwr = p2;
    } else {
      int64_t axm = fl_clamp(0, ax_lo, ax_hi);
      int64_t aym = fl_clamp(0, ay_lo, ay_hi);
      f->s[0] = axm; f->s[1] = aym; f->s[2] = az_lo;
      f->pwr = fl_power_mw(axm, aym, az_lo, f->vz);
    }
  }
  int ov = 0;
  for (int i = 0; i < 5; i++) if (f->u[i] != f->s[i]) ov = 1;
  if (ov) { f->ovrd++; flags |= 1ULL; }
  return flags;
}

static inline void fl_plant_step(Flight *f) {
  f->vx += f->s[0] / FL_DT_INV; f->px += f->vx / FL_DT_INV;
  f->vy += f->s[1] / FL_DT_INV; f->py += f->vy / FL_DT_INV;
  f->vz += f->s[2] / FL_DT_INV; f->pz += f->vz / FL_DT_INV;
  f->wroll += f->s[3] / FL_DT_INV; f->roll += f->wroll / FL_DT_INV;
  f->wpitch += f->s[4] / FL_DT_INV; f->pitch += f->wpitch / FL_DT_INV;
  f->ticks++;
}

static inline void put_u64_le(uint8_t *dst, uint64_t v) {
  for (int i = 0; i < 8; i++) dst[i] = (uint8_t)((v >> (i * 8)) & 0xffu);
}

static void fl_seal_epoch(Flight *f, uint64_t flags) {
  uint8_t rec[160];
  memcpy(rec, f->chain, 32);
  put_u64_le(rec + 32, f->epoch);
  put_u64_le(rec + 40, (uint64_t)f->ticks);
  put_u64_le(rec + 48, (uint64_t)f->px);
  put_u64_le(rec + 56, (uint64_t)f->py);
  put_u64_le(rec + 64, (uint64_t)f->pz);
  put_u64_le(rec + 72, (uint64_t)f->vx);
  put_u64_le(rec + 80, (uint64_t)f->vy);
  put_u64_le(rec + 88, (uint64_t)f->vz);
  put_u64_le(rec + 96, (uint64_t)f->roll);
  put_u64_le(rec + 104, (uint64_t)f->pitch);
  put_u64_le(rec + 112, (uint64_t)f->s[0]);
  put_u64_le(rec + 120, (uint64_t)f->s[1]);
  put_u64_le(rec + 128, (uint64_t)f->s[2]);
  put_u64_le(rec + 136, (uint64_t)f->pwr);
  put_u64_le(rec + 144, (uint64_t)f->ovrd);
  put_u64_le(rec + 152, flags);
  sha256_bytes(rec, 160, f->chain);
  f->epoch++;
}

static inline int64_t mono_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return (x > y) - (x < y);
}

static void print_hex32(const uint8_t d[32]) {
  for (int i = 0; i < 32; i++) printf("%02x", d[i]);
}

int main(void) {
  Flight fl;
  fl_init(&fl);
  uint64_t viol = 0;
  int64_t t0 = mono_ns();
  for (uint64_t tk = 0; tk < 1000000ULL; tk++) {
    fl_set_mission_target(&fl, tk);
    fl_pid_step(&fl);
    uint64_t flg = fl_cbf_shield(&fl);
    fl_plant_step(&fl);
    if (!fl_check_safe(&fl)) viol++;
    if ((tk + 1ULL) % 100ULL == 0ULL) fl_seal_epoch(&fl, flg);
  }
  int64_t t1 = mono_ns();
  printf("BENCH_1M_NS=%lld\n", (long long)(t1 - t0));
  printf("BENCH_1M_TICKS=1000000\n");
  printf("BENCH_1M_EPOCHS=%llu\n", (unsigned long long)fl.epoch);
  printf("BENCH_1M_OVERRIDES=%lld\n", (long long)fl.ovrd);
  printf("BENCH_1M_WATT_CLAMPS=%llu\n", (unsigned long long)fl.watt_clamps);
  printf("BENCH_1M_VIOLATIONS=%llu\n", (unsigned long long)viol);
  printf("BENCH_1M_PX=%lld PY=%lld PZ=%lld VX=%lld VY=%lld VZ=%lld ROLL=%lld PITCH=%lld\n",
         (long long)fl.px, (long long)fl.py, (long long)fl.pz,
         (long long)fl.vx, (long long)fl.vy, (long long)fl.vz,
         (long long)fl.roll, (long long)fl.pitch);
  printf("BENCH_1M_CHAIN_SHA256="); print_hex32(fl.chain); printf("\n");

  /* 10,000 live real-time paced 10 kHz ticks (100 us hard deadline) */
  static uint64_t lat[10000];
  fl_init(&fl);
  uint64_t rt_viol = 0, miss = 0;
  int64_t rt0 = mono_ns();
  for (uint64_t tk = 0; tk < 10000ULL; tk++) {
    int64_t rel = rt0 + (int64_t)tk * 100000LL;
    while (mono_ns() < rel) {
#if defined(__aarch64__)
      __asm__ __volatile__("yield" ::: "memory");
#endif
    }
    int64_t ts = mono_ns();
    fl_set_mission_target(&fl, tk);
    fl_pid_step(&fl);
    uint64_t flg = fl_cbf_shield(&fl);
    fl_plant_step(&fl);
    if (!fl_check_safe(&fl)) rt_viol++;
    if ((tk + 1ULL) % 100ULL == 0ULL) fl_seal_epoch(&fl, flg);
    int64_t te = mono_ns();
    int64_t wns = te - ts;
    lat[tk] = wns > 0 ? (uint64_t)wns : 0ULL;
    if (te > rel + 100000LL) miss++;
  }
  int64_t rt1 = mono_ns();
  qsort(lat, 10000, sizeof(uint64_t), cmp_u64);
  printf("RT_10K_TOTAL_NS=%lld\n", (long long)(rt1 - rt0));
  printf("RT_10K_WORK_P50_NS=%llu\n", (unsigned long long)lat[5000]);
  printf("RT_10K_WORK_P99_NS=%llu\n", (unsigned long long)lat[9900]);
  printf("RT_10K_WORK_P999_NS=%llu\n", (unsigned long long)lat[9990]);
  printf("RT_10K_WORK_MAX_NS=%llu\n", (unsigned long long)lat[9999]);
  printf("RT_10K_MISSED_100US=%llu\n", (unsigned long long)miss);
  printf("RT_10K_VIOLATIONS=%llu\n", (unsigned long long)rt_viol);
  printf("RT_10K_OVERRIDES=%lld\n", (long long)fl.ovrd);
  printf("RT_10K_CHAIN_SHA256="); print_hex32(fl.chain); printf("\n");
  return (viol || rt_viol) ? 1 : 0;
}
