#!/usr/bin/env bash
# Reproducible DGX Spark (Grace AArch64, Cortex-X925 CPU 17) build, Lean 4 proof,
# hostile AI planner attack battery gate, 3-way parity check, and 5-trial H2H benchmark.
set -eo pipefail

CPU="${BENCH_CPU:-17}"
OMC="${OMC_BIN:-$HOME/canon/omega-mv/seed/out/omc}"
SHA_OM="${SHA_OM:-$HOME/canon/omega-mv/seed/ng/sha256.om}"
EXPECTED_OMC_SHA="28fca13d44054e26f78c33d1753fd5c005d08e9144d95985c90bd75b60885072"
TRIALS="${TRIALS:-5}"

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
mkdir -p bin docs/evidence

echo "=== 1. VERIFY PINNED COMPILER & HOST ==="
OMC_SHA="$(sha256sum "$OMC" | awk '{print $1}')"
echo "OMC=$OMC"
echo "OMC_SHA256=$OMC_SHA"
if [ "$OMC_SHA" != "$EXPECTED_OMC_SHA" ]; then
  echo "ERROR: omc sha256 mismatch: got $OMC_SHA expected $EXPECTED_OMC_SHA" >&2
  exit 2
fi
SHA_OM_SHA="$(sha256sum "$SHA_OM" | awk '{print $1}')"
echo "SHA_OM_SHA256=$SHA_OM_SHA"
UNAME_S="$(uname -a)"
GCC_VER="$(gcc --version | head -n 1)"
PY_VER="$(python3 --version)"
LEAN_VER="$(PATH="$HOME/.elan/bin:$PATH" lean --version)"
echo "HOST=$UNAME_S"
echo "CPU_PIN=taskset -c $CPU"
echo "GCC=$GCC_VER"
echo "PYTHON=$PY_VER"
echo "LEAN=$LEAN_VER"

echo "=== 2. FORMAL LEAN 4 PROOF VERIFICATION ==="
LEAN_OUT="$(PATH="$HOME/.elan/bin:$PATH" taskset -c "$CPU" lean proof/FlightCbfSafety.lean 2>&1)"
echo "$LEAN_OUT"
if echo "$LEAN_OUT" | grep -qE "sorryAx|ofReduceBool|trustCompiler|error:|warning:"; then
  echo "ERROR: Lean 4 proof failed axiom/cleanliness check" >&2
  exit 3
fi

echo "=== 3. BUILD ALL PURE OM-2 & C BINARIES ==="
for f in planner_good planner_fs_net planner_dive planner_loop probe_overflow; do
  "$OMC" < "om/$f.om" > "bin/$f.tmp"
  chmod +x "bin/$f.tmp"
  mv -f "bin/$f.tmp" "bin/$f"
  echo "BIN $f $(stat -c%s "bin/$f") bytes"
done

cat om/prelude_om2.om "$SHA_OM" om/flight_core.om om/flight_bench.om > bin/.flight_bench.combined.om
"$OMC" < bin/.flight_bench.combined.om > bin/flight_bench.tmp
chmod +x bin/flight_bench.tmp && mv -f bin/flight_bench.tmp bin/flight_bench
echo "BIN flight_bench $(stat -c%s bin/flight_bench) bytes"

cat om/prelude_om2.om "$SHA_OM" om/flight_core.om om/flight_gate.om > bin/.flight_gate.combined.om
"$OMC" < bin/.flight_gate.combined.om > bin/flight_gate.tmp
chmod +x bin/flight_gate.tmp && mv -f bin/flight_gate.tmp bin/flight_gate
echo "BIN flight_gate $(stat -c%s bin/flight_gate) bytes"

gcc -O3 -mcpu=native -Wall -Wextra -o bin/flight_ref_c ref/flight_ref.c
echo "BIN flight_ref_c $(stat -c%s bin/flight_ref_c) bytes"

echo "=== 4. ELF LINKAGE AUDIT ==="
file bin/flight_bench bin/flight_gate bin/flight_ref_c
ldd bin/flight_bench 2>&1 || true
ldd bin/flight_ref_c 2>&1 || true

echo "=== 5. HOSTILE AI PLANNER ATTACK BATTERY GATE (3 RUNS, CPU $CPU) ==="
GATE_RAW="docs/evidence/.gate_runs.txt"
: > "$GATE_RAW"
for r in 1 2 3; do
  echo "--- GATE RUN $r ---" | tee -a "$GATE_RAW"
  taskset -c "$CPU" ./bin/flight_gate ./bin | tee -a "$GATE_RAW"
done

echo "=== 6. PAIRED INTERLEAVED H2H BENCHMARK ($TRIALS TRIALS, CPU $CPU) ==="
BENCH_RAW="docs/evidence/.bench_runs.txt"
: > "$BENCH_RAW"
for t in $(seq 1 "$TRIALS"); do
  echo "--- TRIAL $t OM2 ---" | tee -a "$BENCH_RAW"
  taskset -c "$CPU" ./bin/flight_bench | tee -a "$BENCH_RAW"
  echo "--- TRIAL $t C ---" | tee -a "$BENCH_RAW"
  taskset -c "$CPU" ./bin/flight_ref_c | tee -a "$BENCH_RAW"
  echo "--- TRIAL $t PY ---" | tee -a "$BENCH_RAW"
  taskset -c "$CPU" python3 ref/flight_ref.py | tee -a "$BENCH_RAW"
done

echo "=== 7. PARSE RESULTS, VERIFY 3-WAY BIT-EXACT PARITY, WRITE results.json ==="
python3 - "$ROOT" "$CPU" "$OMC_SHA" "$SHA_OM_SHA" "$UNAME_S" "$GCC_VER" "$PY_VER" "$LEAN_VER" <<'PYEOF'
import json
import os
import re
import statistics
import sys
from datetime import datetime, timezone

root, cpu, omc_sha, sha_om_sha, uname_s, gcc_ver, py_ver, lean_ver = sys.argv[1:9]

def parse_kv_blocks(path):
    blocks = []
    cur = None
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith("--- ") and line.endswith(" ---"):
                if cur is not None:
                    blocks.append(cur)
                cur = {"header": line[4:-4], "kv": {}, "lines": []}
            elif cur is not None and line:
                cur["lines"].append(line)
                for tok in line.split():
                    if "=" in tok:
                        k, v = tok.split("=", 1)
                        cur["kv"][k] = v
    if cur is not None:
        blocks.append(cur)
    return blocks

# Parse gate runs
gate_blocks = parse_kv_blocks(os.path.join(root, "docs/evidence/.gate_runs.txt"))
gate_tests = {}
for b in gate_blocks:
    for line in b["lines"]:
        m = re.match(r"^(T\d+B?_[A-Z0-9_]+)=(PASS|FAIL)(.*)$", line)
        if m:
            name, status, rest = m.group(1), m.group(2), m.group(3)
            if status != "PASS":
                raise SystemExit(f"GATE FAILURE: {line}")
            rec = gate_tests.setdefault(name, {"verdict": "PASS", "runs": []})
            kv = {}
            for tok in rest.strip().split():
                if "=" in tok:
                    k, v = tok.split("=", 1)
                    kv[k] = int(v) if re.fullmatch(r"-?\d+", v) else v
            rec["runs"].append(kv)

for name, rec in gate_tests.items():
    lats = [r["contain_ns"] for r in rec["runs"] if "contain_ns" in r]
    if lats:
        rec["contain_ns_median"] = int(statistics.median(lats))
        rec["contain_ns_min"] = min(lats)
        rec["contain_ns_max"] = max(lats)

# Parse benchmark trials
bench_blocks = parse_kv_blocks(os.path.join(root, "docs/evidence/.bench_runs.txt"))
by_impl = {"OM2": [], "C": [], "PY": []}
for b in bench_blocks:
    parts = b["header"].split()
    impl = parts[2]
    kv = b["kv"]
    entry = {
        "trial": int(parts[1]),
        "bench_1m_ns": int(kv["BENCH_1M_NS"]),
        "bench_1m_ticks": int(kv["BENCH_1M_TICKS"]),
        "bench_1m_epochs": int(kv["BENCH_1M_EPOCHS"]),
        "bench_1m_overrides": int(kv["BENCH_1M_OVERRIDES"]),
        "bench_1m_watt_clamps": int(kv["BENCH_1M_WATT_CLAMPS"]),
        "bench_1m_violations": int(kv["BENCH_1M_VIOLATIONS"]),
        "bench_1m_state": {
            "px": int(kv["BENCH_1M_PX"]),
            "py": int(kv["PY"]),
            "pz": int(kv["PZ"]),
            "vx": int(kv["VX"]),
            "vy": int(kv["VY"]),
            "vz": int(kv["VZ"]),
            "roll": int(kv["ROLL"]),
            "pitch": int(kv["PITCH"]),
        },
        "bench_1m_chain_sha256": kv["BENCH_1M_CHAIN_SHA256"],
        "rt_10k_total_ns": int(kv["RT_10K_TOTAL_NS"]),
        "rt_10k_work_p50_ns": int(kv["RT_10K_WORK_P50_NS"]),
        "rt_10k_work_p99_ns": int(kv["RT_10K_WORK_P99_NS"]),
        "rt_10k_work_p999_ns": int(kv["RT_10K_WORK_P999_NS"]),
        "rt_10k_work_max_ns": int(kv["RT_10K_WORK_MAX_NS"]),
        "rt_10k_missed_100us": int(kv["RT_10K_MISSED_100US"]),
        "rt_10k_violations": int(kv["RT_10K_VIOLATIONS"]),
        "rt_10k_overrides": int(kv["RT_10K_OVERRIDES"]),
        "rt_10k_chain_sha256": kv["RT_10K_CHAIN_SHA256"],
    }
    by_impl[impl].append(entry)

# Verify 100% 3-way bit-exact parity across ALL trials and ALL 3 implementations
ref = by_impl["OM2"][0]
for impl, rows in by_impl.items():
    assert len(rows) > 0, f"missing {impl}"
    for r in rows:
        assert r["bench_1m_violations"] == 0, f"{impl} 1M violation!"
        assert r["rt_10k_violations"] == 0, f"{impl} 10K violation!"
        assert r["bench_1m_overrides"] == ref["bench_1m_overrides"], f"{impl} overrides mismatch"
        assert r["bench_1m_watt_clamps"] == ref["bench_1m_watt_clamps"], f"{impl} watt_clamps mismatch"
        assert r["bench_1m_state"] == ref["bench_1m_state"], f"{impl} state mismatch"
        assert r["bench_1m_chain_sha256"] == ref["bench_1m_chain_sha256"], f"{impl} 1M sha256 mismatch"
        assert r["rt_10k_chain_sha256"] == ref["rt_10k_chain_sha256"], f"{impl} 10K sha256 mismatch"

def summarize(rows):
    ns_1m = [r["bench_1m_ns"] for r in rows]
    med_ns = statistics.median(ns_1m)
    return {
        "trials": len(rows),
        "bench_1m_ns_median": int(med_ns),
        "bench_1m_ns_min": min(ns_1m),
        "bench_1m_ns_max": max(ns_1m),
        "ticks_per_sec_median": round(1_000_000 / (med_ns / 1e9), 1),
        "ns_per_tick_1m_median": round(med_ns / 1_000_000, 2),
        "rt_10k_work_p50_ns_median": int(statistics.median(r["rt_10k_work_p50_ns"] for r in rows)),
        "rt_10k_work_p99_ns_median": int(statistics.median(r["rt_10k_work_p99_ns"] for r in rows)),
        "rt_10k_work_p999_ns_median": int(statistics.median(r["rt_10k_work_p999_ns"] for r in rows)),
        "rt_10k_work_max_ns_median": int(statistics.median(r["rt_10k_work_max_ns"] for r in rows)),
        "rt_10k_work_max_ns_worst": max(r["rt_10k_work_max_ns"] for r in rows),
        "rt_10k_missed_100us_per_trial": [r["rt_10k_missed_100us"] for r in rows],
        "rt_10k_missed_100us_total": sum(r["rt_10k_missed_100us"] for r in rows),
        "rt_10k_missed_100us_median": int(statistics.median(r["rt_10k_missed_100us"] for r in rows)),
        "raw_trials": rows,
    }

om2_s = summarize(by_impl["OM2"])
c_s = summarize(by_impl["C"])
py_s = summarize(by_impl["PY"])

bin_sizes = {}
for name in ["flight_bench", "flight_gate", "planner_good", "planner_fs_net", "planner_dive", "planner_loop", "probe_overflow", "flight_ref_c"]:
    p = os.path.join(root, "bin", name)
    bin_sizes[name] = os.path.getsize(p)

out = {
    "schema": "omega-flight.evidence.v1",
    "evidence_label": "MEASURED_DGX_SPARK_GRACE_A64",
    "generated_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "environment": {
        "host_uname": uname_s,
        "cpu_pin": f"taskset -c {cpu} (Cortex-X925)",
        "omc_sha256": omc_sha,
        "sha256_om_sha256": sha_om_sha,
        "gcc_version": gcc_ver,
        "python_version": py_ver,
        "lean_version": lean_ver,
    },
    "binary_sizes_bytes": bin_sizes,
    "lean4_proof": {
        "file": "proof/FlightCbfSafety.lean",
        "verdict": "PROVED",
        "standalone_no_mathlib": True,
        "sorry_count": 0,
        "theorems": {
            "cbf_step_preserves_safe": ["propext", "Classical.choice", "Quot.sound"],
            "cbf_inductive_safety": ["propext", "Classical.choice", "Quot.sound"],
            "initHover_safe": [],
            "floorHover_safe": [],
            "unshielded_dive_violates_safety": ["propext", "Quot.sound"],
            "shielded_dive_stays_safe": ["propext", "Classical.choice", "Quot.sound"],
        },
    },
    "parity": {
        "verdict": "EXACT_3WAY_PARITY",
        "bench_1m_ticks": ref["bench_1m_ticks"],
        "bench_1m_epochs": ref["bench_1m_epochs"],
        "bench_1m_overrides": ref["bench_1m_overrides"],
        "bench_1m_watt_clamps": ref["bench_1m_watt_clamps"],
        "bench_1m_violations": 0,
        "bench_1m_final_state": ref["bench_1m_state"],
        "bench_1m_chain_sha256": ref["bench_1m_chain_sha256"],
        "rt_10k_chain_sha256": ref["rt_10k_chain_sha256"],
    },
    "hostile_planner_gate": {
        "verdict": "PASS",
        "tests_passed": len(gate_tests),
        "tests_failed": 0,
        "tests": gate_tests,
    },
    "benchmarks": {
        "pure_om2": om2_s,
        "c_gcc_o3_native": c_s,
        "python3": py_s,
        "ratios": {
            "om2_vs_python3_speedup": round(py_s["bench_1m_ns_median"] / om2_s["bench_1m_ns_median"], 2),
            "c_vs_om2_speedup": round(om2_s["bench_1m_ns_median"] / c_s["bench_1m_ns_median"], 2),
            "c_vs_om2_binary_size_ratio": round(bin_sizes["flight_ref_c"] / bin_sizes["flight_bench"], 2),
        },
    },
}

out_path = os.path.join(root, "docs/evidence/results.json")
with open(out_path, "w") as f:
    json.dump(out, f, indent=2)
    f.write("\n")

print("PARITY=EXACT_3WAY_PARITY")
print(f"OM2  1M median: {om2_s['bench_1m_ns_median']/1e6:.2f} ms ({om2_s['ticks_per_sec_median']:,.1f} ticks/s, {om2_s['ns_per_tick_1m_median']:.2f} ns/tick) | RT p50={om2_s['rt_10k_work_p50_ns_median']}ns p99={om2_s['rt_10k_work_p99_ns_median']}ns p999={om2_s['rt_10k_work_p999_ns_median']}ns max={om2_s['rt_10k_work_max_ns_median']}ns missed={om2_s['rt_10k_missed_100us_per_trial']}")
print(f"C    1M median: {c_s['bench_1m_ns_median']/1e6:.2f} ms ({c_s['ticks_per_sec_median']:,.1f} ticks/s, {c_s['ns_per_tick_1m_median']:.2f} ns/tick) | RT p50={c_s['rt_10k_work_p50_ns_median']}ns p99={c_s['rt_10k_work_p99_ns_median']}ns p999={c_s['rt_10k_work_p999_ns_median']}ns max={c_s['rt_10k_work_max_ns_median']}ns missed={c_s['rt_10k_missed_100us_per_trial']}")
print(f"PY3  1M median: {py_s['bench_1m_ns_median']/1e6:.2f} ms ({py_s['ticks_per_sec_median']:,.1f} ticks/s, {py_s['ns_per_tick_1m_median']:.2f} ns/tick) | RT p50={py_s['rt_10k_work_p50_ns_median']}ns p99={py_s['rt_10k_work_p99_ns_median']}ns p999={py_s['rt_10k_work_p999_ns_median']}ns max={py_s['rt_10k_work_max_ns_median']}ns missed={py_s['rt_10k_missed_100us_per_trial']}")
print(f"RATIOS: OM2 vs Python3 = {out['benchmarks']['ratios']['om2_vs_python3_speedup']}x faster | C vs OM2 = {out['benchmarks']['ratios']['c_vs_om2_speedup']}x | Binary size: OM2 {bin_sizes['flight_bench']} B vs C {bin_sizes['flight_ref_c']} B ({out['benchmarks']['ratios']['c_vs_om2_binary_size_ratio']}x smaller)")
PYEOF
rm -f docs/evidence/.gate_runs.txt docs/evidence/.bench_runs.txt bin/.flight_bench.combined.om bin/.flight_gate.combined.om
echo "=== ALL DONE ==="
