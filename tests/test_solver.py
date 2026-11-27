"""End-to-end tests of the real Solver through the register-map shell.

Random small CNFs are solved in simulation and checked against brute force:
SAT answers must come with a model that satisfies every clause, and UNSAT
answers must match an unsatisfiable formula.
"""

import itertools
import random

import pytest

from design import Entry, R_CTRL, R_MAX_LITS, R_MAX_VARS, R_RESULT, R_STATUS
from solver import Solver
from test_register_map import (
    ABORT,
    BUSY,
    DONE,
    REJECTED,
    START,
    WINDOW,
    load,
    run_sim,
    s32,
    wb,
)

SAT, UNSAT = 1, 2


def brute_force(nvars, clauses):
    for bits in itertools.product([False, True], repeat=nvars):
        if all(any(bits[abs(l) - 1] == (l > 0) for l in c) for c in clauses):
            return SAT
    return UNSAT


def dpll(clauses):
    """A plain recursive DPLL reference, for instances too big to brute force."""

    def assign(cls, lit):
        out = []
        for c in cls:
            if lit in c:
                continue
            c2 = [x for x in c if x != -lit]
            if not c2:
                return None
            out.append(c2)
        return out

    def go(cls):
        while cls:
            unit = next((c[0] for c in cls if len(c) == 1), None)
            if unit is None:
                break
            cls = assign(cls, unit)
            if cls is None:
                return False
        if not cls:
            return True
        v = abs(cls[0][0])
        return any((c2 := assign(cls, lit)) is not None and go(c2) for lit in (v, -v))

    return SAT if go([sorted(set(c)) for c in clauses]) else UNSAT


def reference(nvars, clauses):
    if nvars <= 12:
        return brute_force(nvars, clauses)
    try:  # pysat (python-sat) when installed: fast on the larger instances
        from pysat.solvers import Solver as PySat
    except ImportError:
        return dpll(clauses)
    if any(len(c) == 0 for c in clauses):
        return UNSAT
    with PySat(name="m22", bootstrap_with=[list(c) for c in clauses]) as s:
        return SAT if s.solve() else UNSAT


def words_of(clauses):
    out = []
    for c in clauses:
        out += list(c) + [0]
    return out


async def solve(ctx, dut, nvars, clauses, max_polls=20000):
    """Run one instance the way the runner does. Returns (result, model)."""
    await wb(ctx, dut, R_CTRL, True, ABORT)
    for _ in range(100):
        if await wb(ctx, dut, R_STATUS) == 0:
            break
    else:
        raise AssertionError("not idle after abort")
    nlits = sum(len(c) for c in clauses)
    await load(ctx, dut, nvars, len(clauses), nlits, words_of(clauses))
    await wb(ctx, dut, R_CTRL, True, START)
    for _ in range(max_polls):
        st = await wb(ctx, dut, R_STATUS)
        if st & (DONE | REJECTED):
            break
    else:
        raise AssertionError("solver did not finish")
    assert st in (DONE, REJECTED), f"bad STATUS {st}"
    if st == REJECTED:
        return "rejected", None
    res = await wb(ctx, dut, R_RESULT)
    model = None
    if res == SAT:
        model = [s32(await wb(ctx, dut, WINDOW + (i % 256))) for i in range(nvars)]
        assert await wb(ctx, dut, WINDOW) == 0  # past NVARS
    return res, model


def check(nvars, clauses, res, model):
    want = reference(nvars, clauses)
    assert res == want, f"got {res}, want {want} for {clauses}"
    if res == SAT:
        assert [abs(l) for l in model] == list(range(1, nvars + 1))
        truth = {abs(l): l > 0 for l in model}
        for c in clauses:
            assert any(truth[abs(l)] == (l > 0) for l in c), f"clause {c} false"


def random_cnf(rng, nvars, nclauses, k):
    return [
        [rng.choice([-1, 1]) * rng.randint(1, nvars) for _ in range(rng.randint(1, k))]
        for _ in range(nclauses)
    ]


def test_capacity_registers():
    dut = Entry()

    async def body(ctx):
        assert await wb(ctx, dut, R_MAX_VARS) == Solver.max_vars > 0
        assert await wb(ctx, dut, R_MAX_LITS) == Solver.max_lits > 0

    run_sim(dut, body)


def test_fixed_instances():
    cases = [
        (1, [[1]]),
        (1, [[-1]]),
        (1, [[1], [-1]]),
        (2, [[1, 2], [-1, 2], [1, -2], [-1, -2]]),  # UNSAT
        (3, [[1, 1, 1], [-1, -1]]),  # duplicate literals
        (3, [[1, -1], [2, -2, 3]]),  # tautologies
        (3, [[1, 2, 3], [-1], [-2]]),  # needs propagation
        (5, []),  # no clauses
        (4, [[1, 2], [-1, 3], [-3, 4], [-4, -2], [-4, -1]]),
    ]
    dut = Entry()

    async def body(ctx):
        for nvars, clauses in cases:
            res, model = await solve(ctx, dut, nvars, clauses)
            check(nvars, clauses, res, model)

    run_sim(dut, body)


def test_empty_clause_is_unsat():
    dut = Entry()

    async def body(ctx):
        await load(ctx, dut, 2, 2, 1, [1, 0, 0])
        await wb(ctx, dut, R_CTRL, True, START)
        for _ in range(20):
            if await wb(ctx, dut, R_STATUS) == DONE:
                break
        assert await wb(ctx, dut, R_RESULT) == UNSAT

    run_sim(dut, body)


def test_literal_out_of_range_is_rejected():
    dut = Entry()

    async def body(ctx):
        await load(ctx, dut, 2, 1, 1, [3, 0])
        await wb(ctx, dut, R_CTRL, True, START)
        for _ in range(20):
            if await wb(ctx, dut, R_STATUS) == REJECTED:
                break
        else:
            raise AssertionError("not rejected")

    run_sim(dut, body)


@pytest.mark.parametrize("seed", range(6))
def test_random_instances(seed):
    rng = random.Random(seed)
    instances = []
    for _ in range(12):
        nvars = rng.randint(1, 9)
        nclauses = rng.randint(1, int(nvars * 4.5) + 1)
        instances.append((nvars, random_cnf(rng, nvars, nclauses, 3)))
    dut = Entry()

    async def body(ctx):
        for nvars, clauses in instances:
            res, model = await solve(ctx, dut, nvars, clauses)
            check(nvars, clauses, res, model)

    run_sim(dut, body)


def test_abort_mid_solve_then_solve_again():
    # A pigeonhole instance (4 pigeons, 3 holes) runs long enough to abort.
    def v(p, h):
        return p * 3 + h + 1

    php = [[v(p, h) for h in range(3)] for p in range(4)]
    for h in range(3):
        for p1 in range(4):
            for p2 in range(p1 + 1, 4):
                php.append([-v(p1, h), -v(p2, h)])
    small = (3, [[1, 2], [-1], [-2, 3]])
    dut = Entry()

    async def body(ctx):
        nlits = sum(len(c) for c in php)
        await load(ctx, dut, 12, len(php), nlits, words_of(php))
        await wb(ctx, dut, R_CTRL, True, START)
        assert await wb(ctx, dut, R_STATUS) == BUSY
        await wb(ctx, dut, R_CTRL, True, ABORT)
        for _ in range(10):
            if await wb(ctx, dut, R_STATUS) == 0:
                break
        else:
            raise AssertionError("not idle after abort")
        assert await wb(ctx, dut, R_RESULT) == 0
        res, model = await solve(ctx, dut, *small)
        check(*small, res, model)
        # And the long instance still gives the right answer from scratch.
        res, model = await solve(ctx, dut, 12, php, max_polls=200000)
        assert res == UNSAT

    run_sim(dut, body)


def planted_cnf(rng, nvars, nclauses):
    """Random 3-CNF satisfied by a hidden assignment that is mostly true, so
    a solver that decides false first has to flip decisions to find it."""
    hidden = [rng.random() < 0.8 for _ in range(nvars)]
    clauses = []
    while len(clauses) < nclauses:
        c = [rng.choice([-1, 1]) * v for v in rng.sample(range(1, nvars + 1), 3)]
        if any(hidden[abs(l) - 1] == (l > 0) for l in c):
            clauses.append(c)
    return clauses


@pytest.mark.parametrize("seed", range(4))
def test_planted_instances_need_backtracking(seed):
    rng = random.Random(100 + seed)
    instances = [(n, planted_cnf(rng, n, int(n * 4))) for n in (6, 8, 10, 12)]
    instances.append((2, [[1, 2], [1, -2]]))  # x1 must flip to true
    dut = Entry()

    async def body(ctx):
        for nvars, clauses in instances:
            res, model = await solve(ctx, dut, nvars, clauses, max_polls=200000)
            check(nvars, clauses, res, model)

    run_sim(dut, body)


@pytest.mark.parametrize("seed", range(3))
def test_threshold_3sat(seed):
    # Random 3-SAT near the phase transition: a mix of SAT and UNSAT.
    rng = random.Random(200 + seed)
    instances = []
    for _ in range(6):
        n = rng.randint(8, 12)
        instances.append(
            (n, [[rng.choice([-1, 1]) * v for v in rng.sample(range(1, n + 1), 3)]
                 for _ in range(int(n * 4.3))])
        )
    dut = Entry()

    async def body(ctx):
        for nvars, clauses in instances:
            res, model = await solve(ctx, dut, nvars, clauses, max_polls=200000)
            check(nvars, clauses, res, model)

    run_sim(dut, body)


# ---------------------------------------------------------------------------
# Watched-literal edge cases.


def run_cases(cases, max_polls=200000):
    dut = Entry()

    async def body(ctx):
        for nvars, clauses in cases:
            res, model = await solve(ctx, dut, nvars, clauses, max_polls=max_polls)
            check(nvars, clauses, res, model)

    run_sim(dut, body)


def test_duplicate_literals():
    run_cases([
        (1, [[1, 1]]),  # (x v x) is the unit x
        (1, [[1, 1], [-1]]),  # ... so this is UNSAT
        (1, [[1, 1, 1, 1], [-1, -1]]),
        (2, [[1, 1, 2], [-1]]),  # forces x2 through a duplicated watch
        (2, [[1, 1, 2], [-1], [-2]]),
        (2, [[1, 2, 2], [-1]]),
        (2, [[1, 2, 2], [-1], [-2, -2]]),
        (3, [[1, 2, 1, 2, 3], [-1], [-2]]),  # replacement scan skips copies
        (3, [[2, 1, 2, 1, 3, 3], [-1], [-2], [-3]]),
        (3, [[-1, -1, 2, 2, 3], [1], [-3, -3]]),
    ])


def test_tautologies():
    run_cases([
        (1, [[1, -1]]),
        (1, [[1, -1], [1], [-1, 1, -1]]),
        (2, [[1, -1, 2], [-2]]),
        (2, [[1, -1, 2], [-2], [2, -2], [-1]]),
        (3, [[1, 2, -1], [-2, 3, 2], [-3]]),
    ])


def test_unit_clauses():
    run_cases([
        (3, [[1], [1], [2], [-3]]),  # repeated units
        (3, [[1], [2], [-1]]),  # conflicting units, not adjacent
        (3, [[-2], [1, 2], [-1, 3], [-3, 2]]),  # unit then a chain to conflict
        (4, [[1, 2, 3, 4], [-1], [-2], [-3]]),  # units force the last literal
        (4, [[1, 2, 3, 4], [-4], [-2], [-3], [-1]]),
        (2, [[2], [1, -2], [-1, 2]]),
    ])


def test_long_clauses():
    rng = random.Random(5)
    n = 200
    long_c = list(range(1, n + 1))
    rng.shuffle(long_c)
    cases = [
        # A width-200 clause whose only non-false literal is found last in the
        # replacement scan, then nothing is left: SAT, then UNSAT.
        (n, [long_c] + [[-v] for v in range(1, n)]),
        (n, [long_c] + [[-v] for v in range(1, n + 1)]),
        # Width near 200 with duplicates and both polarities.
        (20, [[rng.choice([-1, 1]) * rng.randint(1, 20) for _ in range(190)]]
         + [[rng.choice([-1, 1]) * v for v in rng.sample(range(1, 21), 3)] for _ in range(60)]),
        (12, [[v for v in range(1, 13)] * 16]
         + [[-v] for v in range(1, 12)]),
    ]
    run_cases(cases)


def test_implication_chains():
    n = 300
    chain = [[1]] + [[-v, v + 1] for v in range(1, n)]
    run_cases([
        (n, chain),  # SAT, all true
        (n, chain + [[-n]]),  # UNSAT at the end of the chain
        (n, [[-v, v + 1] for v in range(1, n)] + [[-n]]),  # SAT, decisions follow
        # A chain through ternary clauses that only becomes unit late.
        (30, [[-v, -(v + 1), v + 2] for v in range(1, 29)] + [[1], [2], [-30]]),
    ])


def pigeonhole(holes):
    pigeons = holes + 1

    def v(p, h):
        return p * holes + h + 1

    cls = [[v(p, h) for h in range(holes)] for p in range(pigeons)]
    for h in range(holes):
        for a in range(pigeons):
            for b in range(a + 1, pigeons):
                cls.append([-v(a, h), -v(b, h)])
    return pigeons * holes, cls


def test_deep_backtracking():
    rng = random.Random(42)
    # Pigeonhole is UNSAT and needs the whole search tree; the planted
    # instances need many flips because the hidden model is mostly true.
    nv, cls = pigeonhole(4)
    cases = [(nv, cls)]
    cases += [(16, planted_cnf(rng, 16, 64)) for _ in range(2)]
    dut = Entry()

    async def body(ctx):
        res, _ = await solve(ctx, dut, *cases[0], max_polls=400000)
        assert res == UNSAT
        for nvars, clauses in cases[1:]:
            res, model = await solve(ctx, dut, nvars, clauses, max_polls=400000)
            check(nvars, clauses, res, model)

    run_sim(dut, body)


def test_abort_during_load_and_after_done():
    # A partial load, then ABORT; a finished solve, then ABORT. Each following
    # instance must behave as on a fresh board.
    a = (3, [[1, 2, 3], [-1, -2], [-2, -3], [-1, -3], [1], [2]])  # UNSAT
    b = (3, [[-1], [1, 2], [-2, 3]])  # SAT
    dut = Entry()

    async def body(ctx):
        await wb(ctx, dut, R_CTRL, True, ABORT)
        for _ in range(20):
            if await wb(ctx, dut, R_STATUS) == 0:
                break
        await load(ctx, dut, 3, 6, 9, words_of(a[1])[:7])  # stop mid-stream
        res, model = await solve(ctx, dut, *b)
        check(*b, res, model)
        res, model = await solve(ctx, dut, *a)
        check(*a, res, model)
        res, model = await solve(ctx, dut, *b)
        check(*b, res, model)

    run_sim(dut, body)


def test_abort_mid_solve_large_then_small():
    # Abort a long solve with many variables, then solve small instances
    # whose variables overlap the stale watch lists and assignments.
    nv, cls = pigeonhole(5)
    small = [(3, [[1, 2], [-1], [-2, 3]]), (2, [[1, 2], [1, -2], [-1, 2], [-1, -2]])]
    dut = Entry()

    async def body(ctx):
        nlits = sum(len(c) for c in cls)
        await wb(ctx, dut, R_CTRL, True, ABORT)
        for _ in range(20):
            if await wb(ctx, dut, R_STATUS) == 0:
                break
        await load(ctx, dut, nv, len(cls), nlits, words_of(cls))
        await wb(ctx, dut, R_CTRL, True, START)
        for _ in range(300):
            assert await wb(ctx, dut, R_STATUS) == BUSY
        for nvars, clauses in small:
            res, model = await solve(ctx, dut, nvars, clauses)
            check(nvars, clauses, res, model)

    run_sim(dut, body)


# ---------------------------------------------------------------------------
# Variables that occur in no clause.


def test_unused_variables_are_never_flipped():
    # Before the fix, every unused variable numbered below the used ones was
    # decided and flipped by chronological backtracking, doubling the run time
    # each: with 40 of them this UNSAT instance would never finish. Now they
    # are assigned false at start-up and never decided.
    k = 40
    a, b, c = k + 1, k + 2, k + 3
    unsat = [[s1 * a, s2 * b, s3 * c] for s1 in (1, -1) for s2 in (1, -1) for s3 in (1, -1)]
    sat = [[a, b], [-a, c], [-b, -c], [k + 5]]  # vars 1..40 and 44 unused
    cases = [
        (k + 3, unsat),
        (k + 5, sat),
        (k + 3, unsat + [[3, 7], [-3, 7], [3, -7], [-3, -7]]),  # interleaved
        (20, [[20], [-1, 2], [-2, 1]]),  # used vars below, unused in between
    ]
    run_cases(cases, max_polls=3000)


def test_size_rewrite_resets_load_position():
    # Spec 3.4: writing a size restarts the stream. (A rewrite with the same
    # values is not visible to the Solver; the runner always ABORTs first.)
    dut = Entry()

    async def body(ctx):
        await wb(ctx, dut, R_CTRL, True, ABORT)
        for _ in range(20):
            if await wb(ctx, dut, R_STATUS) == 0:
                break
        await load(ctx, dut, 1, 1, 1, [-1, 0])
        await load(ctx, dut, 2, 1, 1, [1, 0])  # (x1), 2 vars: SAT
        await wb(ctx, dut, R_CTRL, True, START)
        for _ in range(2000):
            st = await wb(ctx, dut, R_STATUS)
            if st & (DONE | REJECTED):
                break
        assert st == DONE
        assert await wb(ctx, dut, R_RESULT) == SAT
        assert s32(await wb(ctx, dut, WINDOW)) == 1

    run_sim(dut, body)


# ---------------------------------------------------------------------------
# CDCL: learning, backjumping, restarts and clause-database reduction.
#
# These drive the Solver directly (without the Wishbone shell) so that the
# FSM can be watched: the tests check that the events they are about really
# happen, not only that the answers are right.

from amaranth.sim import Simulator  # noqa: E402


def drive_solver(dut, instances, max_cycles=3_000_000, abort_after=None):
    """Solve each (nvars, clauses) in turn on one Solver, the way the shell
    does (abort, sizes, stream, start). Returns per instance (result, model,
    counts of FSM states entered). abort_after[i], if not None, aborts
    instance i after that many cycles and records result None."""
    out = []

    async def tb(ctx):
        fsm = dut.dbg["fsm"]
        names = {v: k for k, v in fsm.encoding.items()}
        for idx, (nvars, clauses) in enumerate(instances):
            ctx.set(dut.abort, 1)
            await ctx.tick()
            await ctx.tick()
            while not ctx.get(dut.idle):
                await ctx.tick()
            ctx.set(dut.abort, 0)
            await ctx.tick()
            ctx.set(dut.nvars, nvars)
            ctx.set(dut.nclauses, len(clauses))
            ctx.set(dut.nlits, sum(len(c) for c in clauses))
            await ctx.tick()
            for c in clauses:
                for x in list(c) + [0]:
                    ctx.set(dut.load_data, x)
                    ctx.set(dut.load_valid, 1)
                    await ctx.tick()
            ctx.set(dut.load_valid, 0)
            await ctx.tick()
            ctx.set(dut.start, 1)
            await ctx.tick()
            ctx.set(dut.start, 0)
            counts = {}
            last = None
            limit = max_cycles
            if abort_after is not None and abort_after[idx] is not None:
                limit = abort_after[idx]
            res = None
            for _ in range(limit):
                st = names[ctx.get(fsm.state)]
                if st != last:
                    counts[st] = counts.get(st, 0) + 1
                    last = st
                if ctx.get(dut.done) or ctx.get(dut.rejected):
                    break
                await ctx.tick()
            model = None
            if ctx.get(dut.rejected):
                res = "rejected"
            elif ctx.get(dut.done):
                res = ctx.get(dut.result)
                if res == SAT:
                    model = []
                    for v in range(nvars):
                        ctx.set(dut.model_addr, v)
                        await ctx.tick()
                        model.append((v + 1) if ctx.get(dut.model_val) else -(v + 1))
            elif abort_after is None or abort_after[idx] is None:
                raise AssertionError("solver did not finish")
            out.append((res, model, counts))

    sim = Simulator(dut)
    sim.add_clock(1e-6)
    sim.add_testbench(tb)
    sim.run()
    return out


def test_learned_unit_then_conflict_at_level_0():
    # x1 is forced by learning: deciding x1 false (the first phase) leads to a
    # conflict whose learned clause is the unit (x1); with x1 true, x3 and -x3
    # conflict at level 0: UNSAT.
    cls = [[1, 2], [1, -2], [-1, 3], [-1, -3]]
    # A satisfiable variant: the learned unit x1 is the answer.
    cls2 = [[1, 2, 4], [1, -2, 4], [1, 2, -4], [1, -2, -4], [-1, 3]]
    dut = Solver()
    (r1, m1, c1), (r2, m2, c2) = drive_solver(dut, [(3, cls), (4, cls2)])
    check(3, cls, r1, m1)
    check(4, cls2, r2, m2)
    assert c2.get("AU0", 0) >= 1  # a clause was learned
    assert m2[0] == 1


def test_backjump_over_several_levels():
    # Variables 5..8 are decided first (highest index first) and are
    # irrelevant; the conflict among 1..4 must jump back over them.
    core = [[1, 2], [1, -2, 3], [-3, -1], [-2, 4], [-4, -1], [1, 3, 4]]
    pad = [[5, 6, 7, 8], [-5, -6], [-7, -8]]
    for cls in (core + pad, core + pad + [[-1, -3, 2]]):
        dut = Solver()
        ((res, model, counts),) = drive_solver(dut, [(8, cls)])
        check(8, cls, res, model)


@pytest.mark.parametrize("holes", [3, 4, 5])
def test_pigeonhole_unsat_with_learning(holes):
    nv, cls = pigeonhole(holes)
    dut = Solver()
    ((res, model, counts),) = drive_solver(dut, [(nv, cls)], max_cycles=20_000_000)
    assert res == UNSAT
    assert counts.get("AU0", 0) > 0  # learned clauses
    assert counts.get("P0", 0) > 0  # backjumps


def test_restarts_and_reductions_happen():
    # Short intervals: restart every 4 x Luby conflicts, reduce every 20 + 10k.
    rng = random.Random(7)
    insts = [pigeonhole(5)]
    for n in (40, 50):
        insts.append((n, [[rng.choice([-1, 1]) * v for v in rng.sample(range(1, n + 1), 3)]
                          for _ in range(int(n * 4.3))]))
    dut = Solver(reduce_first=20, reduce_inc=10, restart_log2=2)
    results = drive_solver(dut, insts, max_cycles=20_000_000)
    for (nv, cls), (res, model, counts) in zip(insts, results):
        check(nv, cls, res, model)
    counts = results[0][2]
    assert counts.get("RS1", 0) >= 3, counts  # restarts
    assert counts.get("RD0", 0) >= 2, counts  # reductions
    assert counts.get("RCLR", 0) >= 1  # watch lists rebuilt


def test_tiny_store_forces_reductions_and_escalation():
    # A store just big enough to accept the instances: the learned area fills
    # up all the time, conflicts are dropped, and compaction escalates to
    # keeping only glue clauses or nothing. Answers must stay right.
    def words(nv, cls):
        return 2 * nv + 1 + sum(2 + len(c) for c in cls)

    rng = random.Random(11)
    insts = [pigeonhole(4)]
    for _ in range(3):
        n = rng.randint(18, 24)
        insts.append((n, [[rng.choice([-1, 1]) * v for v in rng.sample(range(1, n + 1), 3)]
                          for _ in range(int(n * 4.4))]))
    total = {}
    for nv, cls in insts:
        dut = Solver(sdepth=words(nv, cls) + 2 * nv + 16 + 16, reduce_first=10**6)
        ((res, model, counts),) = drive_solver(dut, [(nv, cls)], max_cycles=20_000_000)
        check(nv, cls, res, model)
        for k, v in counts.items():
            total[k] = total.get(k, 0) + v
    assert total.get("RCLR", 0) >= 3, total  # reductions (watch lists rebuilt)
    assert total.get("RD0", 0) > total["RCLR"], total  # some compactions escalated


def test_store_too_small_to_learn_is_rejected():
    # The formula fits but leaves fewer than 2 * nvars + 16 free words.
    dut = Solver(sdepth=1024)
    cls = [[v, v + 1] for v in range(1, 300)]
    ((res, model, counts),) = drive_solver(dut, [(300, cls)])
    assert res == "rejected"
    # Fewer variables: accepted and solved.
    dut = Solver(sdepth=1024)
    cls = [[v, -(v + 1)] for v in range(1, 100)] + [[100], [-1, 50]]
    ((res, model, counts),) = drive_solver(dut, [(100, cls)])
    check(100, cls, res, model)


def test_small_store_through_the_shell():
    # Many random instances with frequent reductions, through the full shell,
    # in one simulation (ABORT isolation between instances).
    rng = random.Random(3)
    instances = []
    for _ in range(25):
        n = rng.randint(5, 25)
        instances.append((n, random_cnf(rng, n, rng.randint(n, int(n * 5)), 4)))
    dut = Entry(solver_cls=lambda: Solver(sdepth=1500, reduce_first=8, reduce_inc=4,
                                          restart_log2=1))

    async def body(ctx):
        for nvars, clauses in instances:
            res, model = await solve(ctx, dut, nvars, clauses, max_polls=400000)
            if res == "rejected":
                continue
            check(nvars, clauses, res, model)

    run_sim(dut, body)


def test_abort_at_many_points_then_resolve():
    # Abort the same hard instance after different numbers of cycles (during
    # start-up, propagation, analysis, backjumps, restarts, reductions), and
    # solve a different instance after each abort.
    nv, php = pigeonhole(5)
    rng = random.Random(5)
    small = []
    for _ in range(6):
        n = rng.randint(8, 14)
        small.append((n, [[rng.choice([-1, 1]) * v for v in rng.sample(range(1, n + 1), 3)]
                          for _ in range(int(n * 4.3))]))
    seq, aborts = [], []
    for k, cut in enumerate([50, 300, 2000, 9000, 30000, 120000]):
        seq += [(nv, php), small[k]]
        aborts += [cut, None]
    dut = Solver(reduce_first=15, reduce_inc=5, restart_log2=1)
    results = drive_solver(dut, seq, max_cycles=5_000_000, abort_after=aborts)
    for (n, cls), cut, (res, model, counts) in zip(seq, aborts, results):
        if cut is None:
            check(n, cls, res, model)
    # And the hard one from scratch afterwards.
    ((res, model, counts),) = drive_solver(dut, [(nv, php)], max_cycles=20_000_000)
    assert res == UNSAT


@pytest.mark.parametrize("seed", range(3))
def test_threshold_3sat_larger(seed):
    # 40-70 variable random 3-SAT near the threshold: needs real learning.
    rng = random.Random(300 + seed)
    insts = []
    for _ in range(3):
        n = rng.randint(40, 70)
        insts.append((n, [[rng.choice([-1, 1]) * v for v in rng.sample(range(1, n + 1), 3)]
                          for _ in range(int(n * 4.26))]))
    dut = Solver()
    for (nv, cls), (res, model, counts) in zip(insts, drive_solver(dut, insts, 30_000_000)):
        check(nv, cls, res, model)
