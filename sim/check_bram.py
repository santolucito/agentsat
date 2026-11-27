"""Lockstep check of the Bram wrapper: the DP16KD build (with sim/dp16kd_sim.v) against
the Memory build, for many shapes (all block widths, banks, bit masks), on random traffic
with many same-address read/write cycles, in every collision mode of the model.

Usage: python sim/check_bram.py [BUILD_DIR]   (needs yosys and verilator on PATH)
"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from amaranth import *
from amaranth.back import rtlil
from solver import Bram

CFGS = [(18, 81920, True), (31, 16384, False), (16, 16384, False), (14, 16384, False),
        (15, 16384, False), (1, 16384, False), (4, 4096, False), (2, 8192, False),
        (9, 2048, False), (18, 1024, False), (20, 5000, False), (7, 3000, False),
        (3, 100, False), (18, 4096, True), (36, 2048, False), (13, 40000, False)]

class Top(Elaboratable):
    def __init__(self):
        self.ports = []
        self.mm = Signal()
    def elaborate(self, platform):
        if hasattr(self, "_m"):
            return self._m
        self._m = m = Module()
        mm = []
        for i, (w, d, bm) in enumerate(CFGS):
            a = Bram(w, d, bit_mask=bm, primitives=True)
            b = Bram(w, d, bit_mask=bm, primitives=False)
            m.submodules[f"p{i}"] = a
            m.submodules[f"m{i}"] = b
            ab = len(a.rd.addr)
            ra, wa, wd, we = Signal(ab, name=f"ra{i}"), Signal(ab, name=f"wa{i}"), Signal(w, name=f"wd{i}"), Signal(name=f"we{i}")
            self.ports += [ra, wa, wd, we]
            m.d.comb += [a.rd.addr.eq(ra), b.rd.addr.eq(ra), a.wr.addr.eq(wa), b.wr.addr.eq(wa),
                         a.wr.data.eq(wd), b.wr.data.eq(wd), a.wr.en.eq(we), b.wr.en.eq(we)]
            if bm:
                mk = Signal(w, name=f"mk{i}")
                self.ports.append(mk)
                m.d.comb += [a.wr.mask.eq(mk), b.wr.mask.eq(mk)]
            # Compare only addresses in range (a Memory read past the end is undefined).
            inr = Signal(name=f"inr{i}")
            m.d.sync += inr.eq(ra < d)
            mm.append(inr & (a.rd.data != b.rd.data))
        m.d.comb += self.mm.eq(Cat(*mm).any())
        return m

TB = r"""#include "Vtop.h"
#include "verilated.h"
#include "ports.h"
#include <cstdio>
#include <random>
int main(int argc, char **argv) {
  VerilatedContext ctx; ctx.commandArgs(argc, argv);
  Vtop *top = new Vtop(&ctx);
  std::mt19937 rng(atoi(argv[1]));
  long cyc = atol(argv[2]); long bad = 0;
  // Narrow the address range sometimes to get many collisions / reuse.
  for (long c = 0; c < cyc; c++) {
    unsigned mode = (c / 10000) % 3;
    auto R = [&]() -> uint32_t { uint32_t x = rng(); if (mode == 1) x &= 0x1f; if (mode == 2) x &= 0x3e00f; return x; };
    DRIVE(R)
    top->clk = 0; top->eval();
    top->clk = 1; top->eval();
    top->eval();
    if (c > 2 && top->mm) { if (bad < 10) printf("mismatch at %ld\n", c); bad++; }
  }
  top->final();
  printf("cycles %ld mismatches %ld\n", cyc, bad);
  return bad != 0;
}
"""

t = Top()
out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(HERE), "build", "bram")
os.makedirs(out, exist_ok=True)
Fragment.get(t, None)
il = rtlil.convert(t, name="top", ports=t.ports + [t.mm])
open(f"{out}/top.il", "w").write(il)
subprocess.run(["yosys", "-q", "-p", f"read_rtlil {out}/top.il; proc; flatten; opt_clean; memory_collect; write_verilog -noattr {out}/top.v"], check=True)
# print port list for the C++ driver
with open(f"{out}/ports.h", "w") as f:
    f.write("#define DRIVE(R) \\\n")
    for p in t.ports:
        nb = len(p)
        f.write(f"  top->{p.name} = ((uint64_t)R() << 32 | R()) & ((1ULL<<{nb})-1); \\\n")
    f.write("\n")
with open(f"{out}/tb.cpp", "w") as f:
    f.write(TB)
subprocess.run(["verilator", "--cc", "--exe", "--build", "-O2", "-Wno-fatal", "-Wno-lint", "-Wno-style",
                "-j", "4", "-CFLAGS", f"-I{os.path.abspath(out)}", "--top-module", "top",
                "--Mdir", f"{out}/obj", f"{out}/top.v", os.path.join(HERE, "dp16kd_sim.v"),
                f"{out}/tb.cpp"], check=True, stdout=subprocess.DEVNULL)
bad = 0
for mode in range(4):
    p = subprocess.run([f"{out}/obj/Vtop", str(mode + 1), "600000", f"+dp16kd_collide={mode}",
                        "+dp16kd_report"], capture_output=True, text=True)
    coll = sum(int(l.split()[2]) for l in p.stderr.splitlines() if l.startswith("dp16kd_collisions"))
    print(f"collide mode {mode}: {p.stdout.strip().splitlines()[-1]}, {coll} block collisions")
    bad |= p.returncode
sys.exit(bad)
