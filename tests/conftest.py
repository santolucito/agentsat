import os
import sys

# `design.py` and `solver.py` sit one level up and import each other by name,
# the same way the platform's build resolves them.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

# The Amaranth simulator cannot run DP16KD instances: test the Memory build,
# which behaves the same cycle for cycle (sim/run_bench.py checks the DP16KD
# build in Verilator).
import solver  # noqa: E402

solver.Solver.bram_primitives = False
# The competition build leaves the read data of a same-word read/write
# collision undefined (no_rw_check); corrupt it here so tests catch a use.
solver.Bram.poison_collisions = True
