"""A baseline DPLL SAT solver in Amaranth, for the AgentSAT register map v1.

`design.py` implements the register map (docs/register_map_v1.md) and talks to
this module through the small interface documented in the template:

    in:  start, abort, nvars, nclauses, nlits, load_valid, load_data, model_addr
    out: idle, load_ready, done, rejected, result, info, model_val

Algorithm
---------
Plain DPLL with chronological backtracking. Unit propagation is done by
scanning every clause in order, and a pass is repeated until it makes no new
assignment.

For each clause the scan tracks: whether some literal is true, and how many
*distinct* unassigned literals it has (0, 1 or "2 or more"), remembering the
first one. At the end of a clause:

    satisfied            -> nothing
    0 unassigned         -> conflict, backtrack
    1 unassigned         -> imply that literal (push it on the trail)
    2+ unassigned        -> nothing

When a whole pass sees every clause satisfied, the answer is SAT. When a pass
makes no new assignment and some clause is still open, the solver decides the
lowest unassigned variable as false. On a conflict it pops the trail back to
the latest decision that has not been flipped yet and flips it to true. When
no such decision is left, the answer is UNSAT.

The scan is not pipelined: one literal takes four cycles (read the literal,
then read its variable's assignment). That keeps every read free of hazards
from the assignments a pass makes as it goes.

Memories
--------
    lits   MAX_LITS  x 16 bits: [15] first literal of a clause, [14] negative,
                                [13:0] variable index (0-based)
    asg    MAX_VARS  x  2 bits: [1] assigned, [0] value
    trail  MAX_VARS  x 16 bits: [15] decision, [14] flipped, [13:0] variable

Instance isolation: the assignment memory and the trail are cleared at every
START, before the solve, and the load pointer is cleared on ABORT. Nothing
else survives between instances.
"""

from amaranth import Cat, Const, Elaboratable, Module, Mux, ResetInserter, Signal, signed
from amaranth.lib.memory import Memory

VAR_BITS = 14

# Reason codes reported in INFO.
INFO_EMPTY_CLAUSE = 0x01  # an empty clause in the stream: UNSAT at once
INFO_BAD_LITERAL = 0x02  # literal outside 1..nvars, or too many literals
INFO_NO_DECISION = 0x03  # internal: nothing left to decide (should not happen)


class Solver(Elaboratable):
    # Largest instance this design holds. Set by the memory sizes below.
    max_vars = 1 << VAR_BITS  # 16384
    max_clauses = 1 << 16  # 65536 (clauses take no storage of their own)
    max_lits = 1 << 16  # 65536

    def __init__(self):
        # From the shell.
        self.start = Signal()
        self.abort = Signal()
        self.nvars = Signal(32)
        self.nclauses = Signal(32)
        self.nlits = Signal(32)
        self.load_valid = Signal()
        self.load_data = Signal(signed(32))
        self.model_addr = Signal(32)
        # To the shell.
        self.idle = Signal()
        self.load_ready = Signal()
        self.done = Signal()
        self.rejected = Signal()
        self.result = Signal(2)
        self.info = Signal(32)
        self.model_val = Signal()

    def elaborate(self, platform):
        m = Module()

        LIT_ABITS = (self.max_lits - 1).bit_length()
        VAR_ABITS = VAR_BITS

        m.submodules.lits = lits = Memory(shape=16, depth=self.max_lits, init=[])
        m.submodules.asg = asg = Memory(shape=2, depth=self.max_vars, init=[])
        m.submodules.trail = trail = Memory(shape=16, depth=self.max_vars, init=[])

        lits_r, lits_w = lits.read_port(), lits.write_port()
        asg_r, asg_w = asg.read_port(), asg.write_port()
        trail_r, trail_w = trail.read_port(), trail.write_port()

        # ---- load state (kept while idle) ----
        lp = Signal(LIT_ABITS + 1)  # literals stored
        clause_start = Signal(init=1)  # next literal starts a clause
        empty_clause = Signal()
        bad_input = Signal()

        # ---- solve state ----
        nv = Signal(VAR_ABITS + 1)  # number of variables (<= max_vars)
        li = Signal(LIT_ABITS + 1)  # literal index in the scan
        lit = Signal(16)  # the literal being evaluated
        lit_first = lit[15]
        lit_neg = lit[14]
        lit_var = lit[:VAR_ABITS]
        boundary_done = Signal()  # previous clause already finalized
        fin_end = Signal()  # this finalize ends the pass
        csat = Signal()  # current clause has a true literal
        cnt = Signal(2)  # distinct unassigned literals: 0, 1, 2 (= 2 or more)
        ulit = Signal(16)  # the first unassigned literal (first-flag cleared)
        changed = Signal()  # this pass made an assignment
        all_sat = Signal()  # every clause so far was satisfied
        tp = Signal(VAR_ABITS + 1)  # trail size
        ci = Signal(VAR_ABITS + 1)  # clear / decide index
        res = Signal(2)
        info = Signal(32)

        m.d.comb += [
            self.result.eq(res),
            self.info.eq(info),
        ]

        # Default memory port values.
        m.d.comb += [
            lits_w.en.eq(0),
            asg_w.en.eq(0),
            trail_w.en.eq(0),
        ]

        lit_mag = Signal(32)
        m.d.comb += lit_mag.eq(Mux(self.load_data < 0, -self.load_data, self.load_data))

        with m.FSM(init="IDLE"):
            with m.State("IDLE"):
                m.d.comb += [self.idle.eq(1), self.load_ready.eq(1)]
                with m.If(self.load_valid & ~self.abort):
                    with m.If(self.load_data == 0):
                        with m.If(clause_start):
                            m.d.sync += empty_clause.eq(1)
                        m.d.sync += clause_start.eq(1)
                    with m.Elif((lit_mag > self.nvars) | (lp >= self.max_lits)):
                        m.d.sync += bad_input.eq(1)
                    with m.Else():
                        m.d.comb += [
                            lits_w.addr.eq(lp),
                            lits_w.data.eq(
                                Cat((lit_mag - 1)[:VAR_ABITS], self.load_data < 0, clause_start)
                            ),
                            lits_w.en.eq(1),
                        ]
                        m.d.sync += [lp.eq(lp + 1), clause_start.eq(0)]
                with m.If(self.start & ~self.abort):
                    m.d.sync += [
                        nv.eq(self.nvars),
                        ci.eq(0),
                        tp.eq(0),
                        res.eq(0),
                        info.eq(0),
                    ]
                    with m.If(bad_input):
                        m.d.sync += info.eq(INFO_BAD_LITERAL)
                        m.next = "REJECT"
                    with m.Elif(empty_clause):
                        m.d.sync += [res.eq(2), info.eq(INFO_EMPTY_CLAUSE)]
                        m.next = "DONE"
                    with m.Else():
                        m.next = "CLEAR"

            # Clear every variable's assignment.
            with m.State("CLEAR"):
                with m.If(ci < nv):
                    m.d.comb += [asg_w.addr.eq(ci), asg_w.data.eq(0), asg_w.en.eq(1)]
                    m.d.sync += ci.eq(ci + 1)
                with m.Else():
                    m.next = "PASS_INIT"

            # Start a propagation pass over all clauses.
            with m.State("PASS_INIT"):
                m.d.sync += [
                    li.eq(0),
                    changed.eq(0),
                    all_sat.eq(1),
                    csat.eq(0),
                    cnt.eq(0),
                    boundary_done.eq(0),
                ]
                with m.If(lp == 0):
                    m.d.sync += res.eq(1)
                    m.next = "DONE"
                with m.Else():
                    m.next = "LIT_RD"

            with m.State("LIT_RD"):
                m.d.comb += lits_r.addr.eq(li)
                m.next = "LIT_WAIT"

            with m.State("LIT_WAIT"):
                m.d.comb += lits_r.addr.eq(li)
                m.d.sync += lit.eq(lits_r.data)
                with m.If(lits_r.data[15] & (li != 0) & ~boundary_done):
                    m.d.sync += fin_end.eq(0)
                    m.next = "FIN"
                with m.Else():
                    m.next = "ASG_RD"

            with m.State("ASG_RD"):
                m.d.comb += asg_r.addr.eq(lit_var)
                m.next = "ASG_WAIT"

            with m.State("ASG_WAIT"):
                m.d.comb += asg_r.addr.eq(lit_var)
                assigned = asg_r.data[1]
                value = asg_r.data[0]
                lit_key = Cat(lit_var, lit_neg)
                ulit_key = ulit[: VAR_ABITS + 1]
                with m.If(assigned):
                    with m.If(value != lit_neg):
                        m.d.sync += csat.eq(1)
                with m.Else():
                    with m.If(cnt == 0):
                        m.d.sync += [cnt.eq(1), ulit.eq(lit_key)]
                    with m.Elif((cnt == 1) & (lit_key != ulit_key)):
                        m.d.sync += cnt.eq(2)
                m.d.sync += [li.eq(li + 1), boundary_done.eq(0)]
                with m.If(li + 1 == lp):
                    m.d.sync += fin_end.eq(1)
                    m.next = "FIN"
                with m.Else():
                    m.next = "LIT_RD"

            # Finish the clause in (csat, cnt, ulit).
            with m.State("FIN"):
                m.d.sync += [csat.eq(0), cnt.eq(0), boundary_done.eq(1)]
                with m.If(~csat):
                    m.d.sync += all_sat.eq(0)
                conflict = ~csat & (cnt == 0)
                with m.If(conflict):
                    m.next = "BT"
                with m.Else():
                    with m.If(~csat & (cnt == 1)):
                        # Imply ulit: variable true iff the literal is positive.
                        m.d.comb += [
                            asg_w.addr.eq(ulit[:VAR_ABITS]),
                            asg_w.data.eq(Cat(~ulit[VAR_ABITS], Const(1, 1))),
                            asg_w.en.eq(1),
                            trail_w.addr.eq(tp),
                            trail_w.data.eq(Cat(ulit[:VAR_ABITS], Const(0, 2))),
                            trail_w.en.eq(1),
                        ]
                        m.d.sync += [tp.eq(tp + 1), changed.eq(1)]
                    with m.If(fin_end):
                        m.next = "PASS_END"
                    with m.Else():
                        m.next = "ASG_RD"

            with m.State("PASS_END"):
                with m.If(all_sat):
                    m.d.sync += res.eq(1)
                    m.next = "DONE"
                with m.Elif(changed):
                    m.next = "PASS_INIT"
                with m.Else():
                    m.d.sync += ci.eq(0)
                    m.next = "DEC_RD"

            # Decide the lowest unassigned variable, as false.
            with m.State("DEC_RD"):
                with m.If(ci >= nv):
                    m.d.sync += info.eq(INFO_NO_DECISION)
                    m.next = "DONE"  # result stays 0 (unknown)
                with m.Else():
                    m.d.comb += asg_r.addr.eq(ci)
                    m.next = "DEC_WAIT"

            with m.State("DEC_WAIT"):
                m.d.comb += asg_r.addr.eq(ci)
                with m.If(~asg_r.data[1]):
                    m.d.comb += [
                        asg_w.addr.eq(ci),
                        asg_w.data.eq(0b10),  # assigned, false
                        asg_w.en.eq(1),
                        trail_w.addr.eq(tp),
                        trail_w.data.eq(Cat(ci[:VAR_ABITS], Const(0, 1), Const(1, 1))),
                        trail_w.en.eq(1),
                    ]
                    m.d.sync += tp.eq(tp + 1)
                    m.next = "PASS_INIT"
                with m.Else():
                    m.d.sync += ci.eq(ci + 1)
                    m.next = "DEC_RD"

            # Backtrack to the latest unflipped decision.
            with m.State("BT"):
                with m.If(tp == 0):
                    m.d.sync += res.eq(2)
                    m.next = "DONE"
                with m.Else():
                    m.d.comb += trail_r.addr.eq(tp - 1)
                    m.next = "BT_WAIT"

            with m.State("BT_WAIT"):
                m.d.comb += trail_r.addr.eq(tp - 1)
                t_var = trail_r.data[:VAR_ABITS]
                t_flipped = trail_r.data[14]
                t_decision = trail_r.data[15]
                with m.If(t_decision & ~t_flipped):
                    m.d.comb += [
                        asg_w.addr.eq(t_var),
                        asg_w.data.eq(0b11),  # assigned, true
                        asg_w.en.eq(1),
                        trail_w.addr.eq(tp - 1),
                        trail_w.data.eq(Cat(t_var, Const(1, 1), Const(1, 1))),
                        trail_w.en.eq(1),
                    ]
                    m.next = "PASS_INIT"
                with m.Else():
                    m.d.comb += [
                        asg_w.addr.eq(t_var),
                        asg_w.data.eq(0),
                        asg_w.en.eq(1),
                    ]
                    m.d.sync += tp.eq(tp - 1)
                    m.next = "BT"

            with m.State("DONE"):
                m.d.comb += [
                    self.done.eq(1),
                    asg_r.addr.eq(self.model_addr),
                    self.model_val.eq(asg_r.data[0]),
                ]

            with m.State("REJECT"):
                m.d.comb += self.rejected.eq(1)

        # ABORT resets every register of the solver (the FSM returns to IDLE,
        # the load pointer to 0) in the cycle after it rises. Memory contents
        # are not reset; the solve state in them is rebuilt at the next START,
        # and the clause memory is overwritten by the next load.
        top = Module()
        top.submodules.core = ResetInserter(self.abort)(m)
        return top
