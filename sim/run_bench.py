"""Build the Verilator model of solver.py and run it on a directory of CNFs.

Usage:
  python sim/run_bench.py --cnf-dir DIR [--answers manifest.csv]
                          [--max-cycles 200000000] [--jobs 8] [--build build/sim]
                          [--out results.json] [--memory] [--plusargs +A +B]

Prints a summary: solved, wrong, timeouts, skipped, and a capped PAR-2 in
cycles (unsolved = 2 * max_cycles). With --answers (the public manifest CSV,
columns id and result_gbd), a SAT/UNSAT answer that contradicts the known
result counts as wrong, and so does a SAT model that fails the check.
Needs yosys and verilator on PATH (for example from oss-cad-suite).

By default it builds the competition build, whose memories are DP16KD
instances, with the behavioural model sim/dp16kd_sim.v; --memory builds the
Memory version instead (Solver.bram_primitives = False). --plusargs are passed
to the model (for example +dp16kd_collide=0..3 and +dp16kd_report, see
sim/dp16kd_sim.v).
"""

import argparse
import concurrent.futures as cf
import csv
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def build(build_dir, memory=False):
    os.makedirs(build_dir, exist_ok=True)
    subprocess.run([sys.executable, os.path.join(HERE, "export_verilog.py"), build_dir]
                   + (["--memory"] if memory else []), check=True)
    model = [] if memory else [os.path.join(HERE, "dp16kd_sim.v")]
    subprocess.run(
        ["verilator", "--cc", "--exe", "--build", "-O3", "-Wno-fatal", "-Wno-lint", "-Wno-style",
         "--x-assign", "fast", "--x-initial", "unique", "-j", "8",
         "-CFLAGS", "-O2", "-CFLAGS", f"-I{os.path.abspath(build_dir)}",
         "--top-module", "solver", "--Mdir", os.path.join(build_dir, "obj"),
         os.path.join(build_dir, "solver.v")] + model + [os.path.join(HERE, "tb.cpp")],
        check=True, stdout=subprocess.DEVNULL,
    )
    return os.path.join(build_dir, "obj", "Vsolver")


def run(binary, path, max_cycles, timeout_s, plusargs=()):
    try:
        p = subprocess.run([binary, path, str(max_cycles), *plusargs], capture_output=True, text=True,
                           timeout=timeout_s)
        return json.loads(p.stdout.strip().splitlines()[-1])
    except subprocess.TimeoutExpired:
        return {"file": path, "status": "sim_timeout", "cycles": max_cycles, "model_ok": None}
    except Exception as e:  # noqa: BLE001
        return {"file": path, "status": f"error: {e}", "cycles": max_cycles, "model_ok": None}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cnf-dir", required=True)
    ap.add_argument("--answers")
    ap.add_argument("--max-cycles", type=int, default=200_000_000)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--build", default=os.path.join(ROOT, "build", "sim"))
    ap.add_argument("--out")
    ap.add_argument("--timeout-s", type=int, default=1800)
    ap.add_argument("--only", nargs="*", help="instance ids to run (default: all)")
    ap.add_argument("--memory", action="store_true",
                    help="build the Memory version instead of the DP16KD one")
    ap.add_argument("--plusargs", nargs="*", default=[], help="plusargs for the model")
    a = ap.parse_args()

    binary = build(a.build, memory=a.memory)
    files = sorted(f for f in os.listdir(a.cnf_dir) if f.endswith(".cnf"))
    if a.only:
        files = [f for f in files if f[:-4] in set(a.only)]
    known = {}
    if a.answers:
        for r in csv.DictReader(open(a.answers)):
            known[r["id"]] = r["result_gbd"]

    results = []
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        futs = {ex.submit(run, binary, os.path.join(a.cnf_dir, f), a.max_cycles, a.timeout_s,
                          a.plusargs): f
                for f in files}
        for fut in cf.as_completed(futs):
            r = fut.result()
            iid = futs[fut][:-4]
            r["id"] = iid
            want = known.get(iid)
            wrong = False
            if r["status"] == "sat" and (r["model_ok"] is False or want == "unsat"):
                wrong = True
            if r["status"] == "unsat" and want == "sat":
                wrong = True
            r["wrong"] = wrong
            r["solved"] = r["status"] in ("sat", "unsat") and not wrong
            results.append(r)

    results.sort(key=lambda r: r["id"])
    solved = [r for r in results if r["solved"]]
    wrong = [r for r in results if r["wrong"]]
    par2 = sum(r["cycles"] if r["solved"] else 2 * a.max_cycles for r in results) / max(1, len(results))
    summary = {
        "instances": len(results),
        "solved": len(solved),
        "solved_sat": sum(r["status"] == "sat" for r in solved),
        "solved_unsat": sum(r["status"] == "unsat" for r in solved),
        "wrong": len(wrong),
        "wrong_ids": [r["id"] for r in wrong],
        "timeouts": sum(r["status"] in ("timeout", "sim_timeout") for r in results),
        "skipped_or_rejected": sum(r["status"] in ("skipped", "rejected") for r in results),
        "other": sorted({r["status"] for r in results} - {"sat", "unsat", "timeout", "sim_timeout",
                                                           "skipped", "rejected"}),
        "max_cycles": a.max_cycles,
        "par2_cycles": par2,
        "solved_ids": [r["id"] for r in solved],
    }
    if a.out:
        with open(a.out, "w") as f:
            json.dump({"summary": summary, "results": results}, f, indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
