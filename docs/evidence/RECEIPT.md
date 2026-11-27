# omega-flight Verification & Benchmark Receipt

- **Evidence Label:** `MEASURED_DGX_SPARK_GRACE_A64`
- **Status:** `VERIFIED` (Host-verified on DGX Spark Grace AArch64 Cortex-X925 CPU 17; formal model `PROVED` in Lean 4.36.0; physical drone HIL/flight test `NOT_RUN`)
- **Timestamp (UTC):** `2026-11-27T00:42:09Z`
- **Host:** `Linux spark-b87b 7.0.0-1019-nvidia #19~24.04.2-Ubuntu SMP PREEMPT_DYNAMIC aarch64`
- **CPU Pin:** `taskset -c 17` (single Cortex-X925 performance core, isolated from sibling benchmark workers; no GPU `/dev/aien-gpu` touched)
- **Compiler & Reference Pins:**
  - Seeded `omc`: `~/canon/omega-mv/seed/out/omc` — SHA-256 `28fca13d44054e26f78c33d1753fd5c005d08e9144d95985c90bd75b60885072`
  - Canonical FIPS 180-4 SHA-256 unit: `~/canon/omega-mv/seed/ng/sha256.om` — SHA-256 `d1493267d0c2e5f574c0a5634e81e122b17322ac05f67b3b3a8034bc39097c5e`
  - C compiler: `gcc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0` (`-O3 -mcpu=native -Wall -Wextra`)
  - Python baseline: `Python 3.12.3`
  - Proof checker: `Lean (version 4.36.0, aarch64-unknown-linux-gnu, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, Release)`

---

## 1. Formal Lean 4 Safety Proof (`proof/FlightCbfSafety.lean`)

Command:
```bash
PATH="$HOME/.elan/bin:$PATH" taskset -c 17 lean proof/FlightCbfSafety.lean
```

Observed output (exit code `0`, zero warnings, zero errors, zero `sorryAx`, zero `native_decide`, zero external imports):
```text
'OmegaFlight.cbf_step_preserves_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaFlight.cbf_inductive_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
'OmegaFlight.initHover_safe' does not depend on any axioms
'OmegaFlight.floorHover_safe' does not depend on any axioms
'OmegaFlight.unshielded_dive_violates_safety' depends on axioms: [propext, Quot.sound]
'OmegaFlight.shielded_dive_stays_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Model-to-system link:** All 30 physical constants (`Q16`, `DT_INV`, `G_ACCEL`, `Z_MIN..K_Z`, `R_MAX_MM..K_XY`, `TILT_MIN..K_TILT`, `P_MAX_MW`), truncating integer division (`Int.tdiv`), 1D CBF bounds (`aCbfLo`, `aCbfHi`), WattCBF power formula (`powerMw`, `wattAzCap`), 5-axis shield (`cbfShield`), and symplectic Euler step (`stepFlight`) in `proof/FlightCbfSafety.lean` were authored 1-to-1 against `om/flight_core.om`, `ref/flight_ref.c`, and `ref/flight_ref.py`. `unshielded_dive_violates_safety` provides a formal negative control proving that removing `cbfShield` causes an immediate geofence floor violation (`pz < Z_MIN`) on a single hostile dive tick.

---

## 2. Compiled Binary Sizes & Linkage Audit

| Binary | Kind | Size (bytes) | Size (KiB) | Linkage (`file` / `ldd`) |
|---|---|---:|---:|---|
| `bin/flight_bench` | Pure OM-2 control loop + benchmark | `26,996` | `26.36` | Static AArch64 ELF (`not a dynamic executable`, zero libc) |
| `bin/flight_gate` | Pure OM-2 `execpure` attack battery + tamper gate | `39,672` | `38.74` | Static AArch64 ELF (`not a dynamic executable`, zero libc) |
| `bin/planner_good` | Pure OM-2 benign waypoint AI planner | `2,168` | `2.12` | Static AArch64 ELF |
| `bin/planner_fs_net` | Pure OM-2 hostile FS+Net exfil planner | `1,572` | `1.54` | Static AArch64 ELF |
| `bin/planner_dive` | Pure OM-2 hostile dive/geofence/tilt planner | `1,060` | `1.04` | Static AArch64 ELF |
| `bin/planner_loop` | Pure OM-2 hostile infinite-loop planner | `420` | `0.41` | Static AArch64 ELF |
| `bin/probe_overflow` | Pure OM-2 Ariane-5 signed overflow probe | `284` | `0.28` | Static AArch64 ELF |
| `bin/flight_ref_c` | C11 `gcc -O3 -mcpu=native` reference | `70,936` | `69.27` | Dynamic PIE ELF (`libc.so.6`, `ld-linux-aarch64.so.1`, `linux-vdso.so.1`) |

Pure OM-2 `flight_bench` is **`2.63x` smaller** than C11 `flight_ref_c` while shipping zero external runtime dependencies.

---

## 3. Hostile AI Planner Attack Battery & Negative Controls (`om/flight_gate.om`)

Command (3 consecutive runs on CPU 17):
```bash
taskset -c 17 ./bin/flight_gate ./bin
```

All 3 runs printed `FLIGHT_GATE PASS pass=7 fail=0` (exit `0`) with identical chain digest `2bad9790d0efc8f25b9cb63841f15154625b3d6ca982db7e1e34bddfc89e4003`:

| Check | Run 1 | Run 2 | Run 3 | Median Containment | Verified Behavior |
|---|---:|---:|---:|---:|---|
| `T1_BENIGN_EXECPURE` | `592,101 ns` | `593,573 ns` | `493,828 ns` | **`592.10 us`** | `rc=0`, valid 48B command, CBF safe, epoch sealed |
| `T2_HOSTILE_FS_NET_EXECPURE` | `498,884 ns` | `435,108 ns` | `467,491 ns` | **`467.49 us`** | `fopen("/etc/passwd")==-1` & `socknew==-1` (`-EPERM`), `rc=77`, 100 safe hover ticks (`violations=0`) |
| `T2B_NEGCTRL_UNSANDBOXED_FS_NET` | `rc=99` | `rc=99` | `rc=99` | — | **Negative control:** same binary outside `execpure` breaches (`rc=99`), proving real kernel enforcement |
| `T3_HOSTILE_DIVE_CBF_SHIELD` | `467,956 ns` | `581,173 ns` | `444,164 ns` | **`467.96 us`** | `rc=0`, `+-999 m/s^2` clamped `1000/1000` ticks, `violations=0`, `power_mw=557,125 <= 800,000`, `pz_q16=157,448,188` (`2.40 m >= 0.50 m`) |
| `T4_HOSTILE_LOOP_TRAP4` | `770,102 ns` | `727,110 ns` | `670,597 ns` | **`727.11 us`** | Infinite loop deterministically killed by `trap 4` (`rc=104`), zero freeze, 100 safe hover ticks (`violations=0`) |
| `T5_ARIANE5_OVERFLOW_TRAP1` | `507,380 ns` | `433,380 ns` | `326,803 ns` | **`433.38 us`** | Signed 64-bit overflow killed by hardware `trap 1` (`rc=101`) |
| `T6_SHA256_BLACKBOX_TAMPER` | `PASS` | `PASS` | `PASS` | — | Clean chain `PASS`, 1-bit flip in epoch #1 `pz` (`xor 1`) `FAIL`, restored chain `PASS` |

---

## 4. Paired Interleaved H2H Benchmarks (5 Trials, `taskset -c 17`)

Command: `BENCH_CPU=17 TRIALS=5 bash scripts/run_all_spark.sh`

### 4.1 3-Way Bit-Exact Parity Verdict: `EXACT_3WAY_PARITY`

Every trial across Pure OM-2, C11 `gcc -O3 -mcpu=native`, and Python 3.12.3 (`hashlib.sha256`) produced identical values:
- `BENCH_1M_TICKS = 1,000,000`, `BENCH_1M_EPOCHS = 10,000`, `BENCH_1M_OVERRIDES = 853,354`, `BENCH_1M_WATT_CLAMPS = 81,902`, `BENCH_1M_VIOLATIONS = 0`
- Final state (Q16.16 milli-SI): `px=2967313043`, `py=-6109837904`, `pz=4097607891`, `vx=-983040000`, `vy=-983040000`, `vz=-393216000`, `roll=29481200`, `pitch=-1479`
- `BENCH_1M_CHAIN_SHA256 = 9e705d9cc99f4f7e4398b7d33f3921b12e4be3b2b2e3093bf546425eeb7053c5`
- `RT_10K_CHAIN_SHA256   = 5d3653b39ff79c4359ff3bb0c4f82109dbb9d505a5a9b3b272c5e4826f7e5800`

### 4.2 Summary Metrics (Medians over 5 Paired Interleaved Trials)

| Metric | Pure OM-2 (`omega-flight`) | C11 (`gcc -O3 -mcpu=native`) | Python 3.12.3 |
|---|---:|---:|---:|
| 1M Ticks Wall Time (median) | **145.04 ms** (`144.95..145.48 ms`) | 33.10 ms (`33.07..33.20 ms`) | 4,520.46 ms (`4,494.77..4,528.92 ms`) |
| 1M Ticks Throughput (median) | **6,894,813.7 ticks/s** | 30,216,000.0 ticks/s | 221,216.6 ticks/s |
| 1M Ticks Average ns/tick | **145.04 ns/tick** | 33.10 ns/tick | 4,520.46 ns/tick |
| RT 10 kHz Work `p50` (median) | **256 ns** | 48 ns | 4,832 ns |
| RT 10 kHz Work `p99` (median) | **3,904 ns** | 992 ns | 5,344 ns |
| RT 10 kHz Work `p99.9` (median) | **4,032 ns** | 1,056 ns | 6,000 ns |
| RT 10 kHz Work `max` (median / worst) | **4,176 ns** / `18,624 ns` | 1,072 ns / `1,168 ns` | 32,448 ns / `91,712 ns` |
| RT 10 kHz Compute Overruns (`>100 us`) | **0 / 50,000** | 0 / 50,000 | 0 / 50,000 |
| RT 10 kHz Wall-Clock Misses (`[T1..T5]`) | `0` median (`[23, 0, 0, 0, 0]`) | `2` median (`[7, 2, 3, 1, 0]`) | `0` median (`[0, 0, 0, 0, 0]`) |
| Speedup vs Python 3 | **`31.17x`** | `136.59x` | `1.00x` |
| Speedup vs Pure OM-2 | `1.00x` | `4.38x` | `0.032x` |

### 4.3 Raw Per-Trial Table

| Trial | OM-2 1M (ms) | OM-2 RT p50/p99/p99.9/max (ns) | OM-2 Miss | C 1M (ms) | C RT p50/p99/p99.9/max (ns) | C Miss | Py3 1M (ms) | Py3 RT p50/p99/p99.9/max (ns) | Py3 Miss |
|---:|---:|---|---:|---:|---|---:|---:|---|---:|
| 1 | 145.16 | 256 / 3904 / 4161 / 4784 | 23 | 33.20 | 48 / 1008 / 1056 / 1088 | 7 | 4520.46 | 4848 / 5344 / 6144 / 28736 | 0 |
| 2 | 145.01 | 240 / 3888 / 4032 / 4128 | 0 | 33.19 | 48 / 992 / 1056 / 1056 | 2 | 4514.30 | 4832 / 5344 / 6144 / 27840 | 0 |
| 3 | 145.04 | 256 / 3904 / 4016 / 4096 | 0 | 33.07 | 48 / 992 / 1056 / 1168 | 3 | 4494.77 | 4800 / 5344 / 5936 / 91712 | 0 |
| 4 | 144.95 | 256 / 3872 / 4016 / 4176 | 0 | 33.08 | 48 / 992 / 1040 / 1072 | 1 | 4528.92 | 4832 / 5344 / 6000 / 32448 | 0 |
| 5 | 145.48 | 256 / 3920 / 4048 / 18624 | 0 | 33.10 | 48 / 976 / 1056 / 1056 | 0 | 4521.39 | 4848 / 5360 / 6000 / 52881 | 0 |

---

## 5. Honest Caveats

1. **C vs Pure OM-2 throughput gap (`4.38x`):** `gcc -O3 -mcpu=native` compiles unchecked C11 arithmetic (signed overflow is UB, zero array bounds checks), optimizes constant `/ 10000` to multiply-shift sequences, and aggressively unrolls SHA-256. Pure OM-2 enforces mandatory hardware overflow traps (`trap 1`), array bounds checks (`trap 3`), loop bounds (`trap 4`), and links the general-purpose `seed/ng/sha256.om` (non-CE scalar software SHA-256).
2. **Non-`PREEMPT_RT` Linux wall-clock deadline misses:** Both OM-2 (`[23,0,0,0,0]`, 4/5 trials `0` misses) and C (`[7,2,3,1,0]`, 1/5 trials `0` misses) observed occasional wall-clock misses (`te > rel + 100 us`) during 1-second spin-paced runs on a stock `PREEMPT_DYNAMIC` Linux kernel without `isolcpus`/`nohz_full` or `SCHED_FIFO` while sibling cores were active. Actual per-tick compute work never exceeded `18.6 us` for OM-2 (`4.18 us` median max) or `1.17 us` for C (`0/50,000` compute overruns for both).
3. **Python 3 OpenSSL SHA-256 advantage vs GC tail spikes:** Python's `hashlib.sha256` calls C/OpenSSL hardware ARMv8 SHA256-CE, softening its `p99` epoch-seal jump (`5.34 us`), yet CPython's interpreter/GC still produced a `91.71 us` single-tick spike (`91.7%` of the 100 us deadline) and `31.17x` slower 1M-tick throughput.
4. **Planner sandbox boundary:** `execpure` runs a fresh Linux process (`~433–727 us` round-trip) using shared-kernel Landlock ABI-3 + seccomp-BPF (`-EPERM`), suitable for a 10–100 Hz outer AI guidance loop rather than inside a 100 us inner control tick, and is Linux AArch64-only (not a KVM microVM).
5. **Scope of formal proof:** Lean 4 proves safety of the discrete-time Q16.16 mathematical model matching `om/flight_core.om`; it does not model unmodeled aerodynamic disturbances, actuator lag, sensor noise, or verify `seed/out/omc` code generation.
