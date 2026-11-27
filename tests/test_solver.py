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
    return brute_force(nvars, clauses) if nvars <= 12 else dpll(clauses)


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
