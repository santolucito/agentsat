"""Smoke tests for the register-map shell in design.py.

These check the shell against a fake solver, so they keep working once you
replace the placeholder in solver.py. They are not the full conformance suite.
Run with:  pytest
"""

import pytest
from amaranth import Elaboratable, Module, Mux, Signal, signed
from amaranth.sim import Simulator

from design import (
    MAGIC,
    R_CTRL,
    R_INFO,
    R_LOAD,
    R_MAGIC,
    R_MAX_CLAUSES,
    R_MAX_LITS,
    R_MAX_VARS,
    R_MODEL,
    R_NCLAUSES,
    R_NLITS,
    R_NVARS,
    R_RESULT,
    R_STATUS,
    R_VERSION,
    VERSION,
    Entry,
)
from solver import Solver

BUSY, DONE, REJECTED = 1, 2, 4
START, ABORT = 1, 2
WINDOW = 256


class FakeSolver(Elaboratable):
    """Stand-in solver with the interface documented in solver.py.

    nlits == 99   -> UNSAT.  nvars == 7 -> never finishes (to test abort).
    Otherwise SAT, with variable i true when i is odd.
    """

    max_vars = 1000
    max_clauses = 1000
    max_lits = 1000

    def __init__(self):
        self.start = Signal()
        self.abort = Signal()
        self.nvars = Signal(32)
        self.nclauses = Signal(32)
        self.nlits = Signal(32)
        self.load_valid = Signal()
        self.load_data = Signal(signed(32))
        self.model_addr = Signal(32)
        self.idle = Signal()
        self.load_ready = Signal()
        self.done = Signal()
        self.rejected = Signal()
        self.result = Signal(2)
        self.info = Signal(32)
        self.model_val = Signal()
        self.loaded = Signal(32)  # words received, for the tests
        self.starts = Signal(8)  # start pulses received, for the tests

    def elaborate(self, platform):
        m = Module()
        with m.If(self.start):
            m.d.sync += self.starts.eq(self.starts + 1)
        run = Signal(4)
        active = Signal()
        abort_cnt = Signal(5)  # cycles spent clearing while `abort` is held
        clear_cycles = 12  # slower than the shell's own wait, so the wait is tested

        m.d.comb += [
            self.load_ready.eq(1),
            # Not idle while clearing; idle again once clearing has finished.
            self.idle.eq(
                ((abort_cnt == 0) & ~self.abort) | (abort_cnt == clear_cycles)
            ),
            self.result.eq(Mux(self.nlits == 99, 2, 1)),
            self.info.eq(0xABCD),
            self.model_val.eq(~self.model_addr[0]),  # 0-based even index = odd var
        ]
        with m.If(self.load_valid):
            m.d.sync += self.loaded.eq(self.loaded + 1)
        m.d.sync += self.done.eq(0)
        with m.If(self.abort):
            m.d.sync += [self.loaded.eq(0), active.eq(0), run.eq(0)]
            with m.If(abort_cnt != clear_cycles):
                m.d.sync += abort_cnt.eq(abort_cnt + 1)
        with m.Else():
            m.d.sync += abort_cnt.eq(0)
            with m.If(self.start):
                m.d.sync += [active.eq(1), run.eq(0)]
            with m.If(active & (self.nvars != 7)):
                m.d.sync += run.eq(run + 1)
                with m.If(run == 5):
                    m.d.sync += [self.done.eq(1), active.eq(0)]
        return m


async def wb(ctx, dut, adr, we=False, data=0):
    """One Wishbone transaction. Returns the read data."""
    ctx.set(dut.wb_adr, adr)
    ctx.set(dut.wb_we, int(we))
    ctx.set(dut.wb_dat_w, data & 0xFFFFFFFF)
    ctx.set(dut.wb_sel, 0xF)
    ctx.set(dut.wb_cyc, 1)
    ctx.set(dut.wb_stb, 1)
    for _ in range(50):
        await ctx.tick()
        if ctx.get(dut.wb_ack):
            break
    else:
        raise AssertionError(f"no ack for address {adr}")
    value = ctx.get(dut.wb_dat_r)
    await ctx.tick()  # the bridge holds the request through the ack cycle
    ctx.set(dut.wb_cyc, 0)
    ctx.set(dut.wb_stb, 0)
    await ctx.tick()
    return value


def s32(x):
    return x - (1 << 32) if x & (1 << 31) else x


async def wait_status(ctx, dut, mask, want, tries=100):
    for _ in range(tries):
        if (await wb(ctx, dut, R_STATUS)) & mask == want:
            return
    raise AssertionError(f"STATUS never reached mask {mask} == {want}")


async def load(ctx, dut, nvars, nclauses, nlits, words):
    await wb(ctx, dut, R_NVARS, True, nvars)
    await wb(ctx, dut, R_NCLAUSES, True, nclauses)
    await wb(ctx, dut, R_NLITS, True, nlits)
    for w in words:
        await wb(ctx, dut, R_LOAD, True, w)


def run_sim(dut, body):
    sim = Simulator(dut)
    sim.add_clock(1e-8)
    sim.add_testbench(body)
    sim.run()


def entry(solver_cls=FakeSolver):
    return Entry(solver_cls=solver_cls)


def test_identification_and_reserved_words():
    dut = entry()

    async def body(ctx):
        assert await wb(ctx, dut, R_MAGIC) == MAGIC
        assert await wb(ctx, dut, R_VERSION) == VERSION
        assert await wb(ctx, dut, R_MAX_VARS) == 1000
        assert await wb(ctx, dut, R_MAX_CLAUSES) == 1000
        assert await wb(ctx, dut, R_MAX_LITS) == 1000
        assert await wb(ctx, dut, R_STATUS) == 0
        assert await wb(ctx, dut, R_RESULT) == 0
        assert await wb(ctx, dut, R_INFO) == 0
        assert await wb(ctx, dut, 10) == 0  # SoC-owned counter
        assert await wb(ctx, dut, 11) == 0
        assert await wb(ctx, dut, 100) == 0  # reserved
        assert await wb(ctx, dut, WINDOW) == 0  # no model yet

    run_sim(dut, body)


def test_sat_solve_and_model_readback():
    dut = entry()

    async def body(ctx):
        words = [1, -2, 0, 3, 0, -4, 5, 0]  # 3 clauses, 5 literals
        await load(ctx, dut, 5, 3, 5, words)
        assert ctx.get(dut.solver.loaded) == len(words)  # nlits + nclauses
        await wb(ctx, dut, R_CTRL, True, START)
        await wait_status(ctx, dut, DONE, DONE)
        assert ctx.get(dut.solver.starts) == 1
        assert await wb(ctx, dut, R_STATUS) == DONE
        assert await wb(ctx, dut, R_RESULT) == 1
        assert await wb(ctx, dut, R_INFO) == 0xABCD
        # Word 7 and the 256-511 window share one stream.
        assert s32(await wb(ctx, dut, R_MODEL)) == 1
        assert s32(await wb(ctx, dut, WINDOW)) == -2
        assert s32(await wb(ctx, dut, WINDOW + 5)) == 3
        assert s32(await wb(ctx, dut, R_MODEL)) == -4
        assert s32(await wb(ctx, dut, WINDOW + 200)) == 5
        assert await wb(ctx, dut, R_MODEL) == 0  # past NVARS
        assert await wb(ctx, dut, WINDOW) == 0

    run_sim(dut, body)


def test_unsat_has_no_model():
    dut = entry()

    async def body(ctx):
        await load(ctx, dut, 5, 3, 99, [])
        await wb(ctx, dut, R_CTRL, True, START)
        await wait_status(ctx, dut, DONE, DONE)
        assert await wb(ctx, dut, R_RESULT) == 2
        assert await wb(ctx, dut, R_MODEL) == 0

    run_sim(dut, body)


def test_oversize_instance_is_rejected_and_abort_recovers():
    dut = entry()

    async def body(ctx):
        await load(ctx, dut, 2000, 3, 5, [])
        await wb(ctx, dut, R_CTRL, True, START)
        assert await wb(ctx, dut, R_STATUS) == REJECTED
        assert ctx.get(dut.solver.starts) == 0  # the solver is never started
        await wb(ctx, dut, R_CTRL, True, ABORT)
        await wait_status(ctx, dut, BUSY | DONE | REJECTED, 0)
        assert await wb(ctx, dut, R_NVARS) == 0  # write-only, reads 0

    run_sim(dut, body)


def test_size_write_after_done_is_ignored():
    dut = entry()

    async def body(ctx):
        await load(ctx, dut, 5, 1, 1, [1, 0])
        await wb(ctx, dut, R_CTRL, True, START)
        await wait_status(ctx, dut, DONE, DONE)
        assert s32(await wb(ctx, dut, R_MODEL)) == 1
        await wb(ctx, dut, R_NVARS, True, 3)  # not idle: ignored
        assert s32(await wb(ctx, dut, R_MODEL)) == -2  # read position unchanged
        assert s32(await wb(ctx, dut, R_MODEL)) == 3
        assert s32(await wb(ctx, dut, R_MODEL)) == -4
        assert s32(await wb(ctx, dut, R_MODEL)) == 5  # NVARS is still 5
        assert await wb(ctx, dut, R_MODEL) == 0

    run_sim(dut, body)


def test_abort_mid_solve_then_second_solve():
    dut = entry()

    async def body(ctx):
        await load(ctx, dut, 7, 1, 1, [1, 0])  # nvars == 7 never finishes
        await wb(ctx, dut, R_CTRL, True, START)
        assert await wb(ctx, dut, R_STATUS) == BUSY
        await wb(ctx, dut, R_CTRL, True, ABORT)
        # Still clearing: the runner must see busy until the solver is idle.
        assert await wb(ctx, dut, R_STATUS) == BUSY
        await wait_status(ctx, dut, BUSY | DONE | REJECTED, 0)
        assert await wb(ctx, dut, R_RESULT) == 0
        # The board is reusable with no rebuild.
        await load(ctx, dut, 5, 1, 1, [1, 0])
        await wb(ctx, dut, R_CTRL, True, START)
        await wait_status(ctx, dut, DONE, DONE)
        assert await wb(ctx, dut, R_RESULT) == 1
        assert s32(await wb(ctx, dut, R_MODEL)) == 1

    run_sim(dut, body)


def test_writes_ignored_while_busy():
    dut = entry()

    async def body(ctx):
        await load(ctx, dut, 7, 1, 1, [1, 0])
        await wb(ctx, dut, R_CTRL, True, START)
        await wb(ctx, dut, R_NVARS, True, 5)  # ignored: not idle
        await wb(ctx, dut, R_LOAD, True, 9)  # ignored: not idle
        assert ctx.get(dut.solver.loaded) == 2
        assert await wb(ctx, dut, R_STATUS) == BUSY  # still the never-finishing run

    run_sim(dut, body)
