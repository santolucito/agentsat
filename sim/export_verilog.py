"""Export the Solver (without the Wishbone shell) as Verilog for Verilator.

Usage: python sim/export_verilog.py OUT_DIR

Writes OUT_DIR/solver.v (top module `solver`) and OUT_DIR/caps.h with the
declared capacity. Needs `yosys` on PATH (for example from oss-cad-suite).
"""

import os
import subprocess
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from amaranth.back import rtlil  # noqa: E402

from solver import Solver  # noqa: E402


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    s = Solver()
    ports = [
        s.start, s.abort, s.nvars, s.nclauses, s.nlits, s.load_valid, s.load_data,
        s.model_addr, s.idle, s.load_ready, s.done, s.rejected, s.result, s.info,
        s.model_val,
    ]
    il = os.path.join(out, "solver.il")
    with open(il, "w") as f:
        f.write(rtlil.convert(s, name="solver", ports=ports))
    subprocess.run(
        ["yosys", "-q", "-p",
         f"read_rtlil {il}; proc; flatten; opt_clean; memory_collect; "
         f"write_verilog -noattr {os.path.join(out, 'solver.v')}"],
        check=True,
    )
    with open(os.path.join(out, "caps.h"), "w") as f:
        f.write(f"#define MAX_VARS {Solver.max_vars}ULL\n")
        f.write(f"#define MAX_CLAUSES {Solver.max_clauses}ULL\n")
        f.write(f"#define MAX_LITS {Solver.max_lits}ULL\n")


if __name__ == "__main__":
    main()
