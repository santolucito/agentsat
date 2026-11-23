import os
import sys

# `design.py` and `solver.py` sit one level up and import each other by name,
# the same way the platform's build resolves them.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
