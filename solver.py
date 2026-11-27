"""A DPLL SAT solver with two watched literals, in Amaranth, for register map v1.

`design.py` implements the register map (docs/register_map_v1.md) and talks to
this module through the small interface documented in the template:

    in:  start, abort, nvars, nclauses, nlits, load_valid, load_data, model_addr
    out: idle, load_ready, done, rejected, result, info, model_val

Algorithm
---------
DPLL with chronological backtracking and MiniSat-style two-watched-literal
unit propagation. Every clause of two or more literals watches its literals
at positions 0 and 1. The watch lists are singly linked lists threaded
through the clause headers, so they need no allocation.

The trail is also the propagation queue: `qhead` is the next trail entry to
propagate. Propagating an entry walks the watch list of the literal it made
false. For each clause on that list:

    other watch true            -> keep the watch
    some literal at position 2+ is not false (and is not the other watch)
                                -> swap it into the watch position, unlink the
                                   clause from this list and push it on the
                                   list of the new watched literal
    otherwise, other unassigned -> imply the other watch (push it on the trail)
    otherwise                   -> conflict: backtrack

When the queue is empty the solver decides the lowest unassigned variable,
found through a monotone pointer (lowered on every unassignment), using its
saved phase (false at first, then the last value it had). On a conflict it
pops the trail back to the latest decision that has not been flipped yet and
flips it. Watches need no repair on backtrack. When no unflipped decision is
left the answer is UNSAT; when every variable is assigned with the queue
empty and no conflict, the answer is SAT.

Soundness note: a conflict found while walking a list leaves the rest of that
list unvisited. That is safe because the literal being propagated is always
undone or flipped by the backtrack (it sits at or after the latest decision).

Loading
-------
Clauses are stored as they stream in. A clause is two header words followed
by its literals. While the leading literal of a clause repeats it is not
stored again, so positions 0 and 1 always hold different literals and a
clause such as (x v x) becomes the unit (x). At a clause's terminator the
last literal is rewritten with its "last" flag, and in the following cycle
(with load_ready low) header word 0 is written with the address of the next
clause, which the start-up scan uses to step from clause to clause. At START
the solver clears the assignments and watch-list heads, then scans the clause
store twice. The first pass (MARK) finds the variables that occur in some
clause; every other variable stays assigned false for the whole solve, so it
is never decided and never flipped by a backtrack (without this, each unused
variable numbered below the used ones doubles the run time). In the second
pass, unit clauses are assigned at level 0 (a unit that contradicts an
earlier one means UNSAT), and every other clause is pushed on the watch lists
of its first two literals. An empty clause means UNSAT at once.

Memories (one read port and one write port each, block RAM)
--------
    store  98304 x 18  clause store. Word 0 is unused, so address 0 is the
                       null pointer. A clause at header address h:
                         h     next pointer of the watch at position 0
                               (before START: address of the next clause)
                         h+1   next pointer of the watch at position 1
                         h+2.. literals: [0] negative, [14:1] variable
                               (0-based), [15] last literal of the clause
                       A pointer is [16:0] header address, [17] watch slot.
    heads  32768 x 18  watch-list head pointer per literal code (2*var+neg)
    trail  16384 x 17  [13:0] variable, [14] value, [15] decision, [16] flipped
    asg    16384 x  2  [1] assigned, [0] value (kept on unassign: saved phase)

Block RAMs: store 108, heads 36, trail 17, asg 2 = 163 DP16KD (of 183).

Capacity: a clause takes 2 + (number of literals) words, plus word 0, so any
instance with at most max_clauses clauses and max_lits literals fits:
1 + 2 * 16384 + 65535 = 98304 words.

Timing
------
On the ECP5 a block RAM's read data appears about 6 ns after the clock, and
an address that fans out to a hundred block RAMs spread over the die needs
another 6-7 ns of routing. So:
  * store, heads and trail are bit-sliced (`BitSlicedMemory`, 1-bit-wide
    memories of 16384 x 1), so read data passes at most a 6:1 mux instead of
    a 96:1 mux of 1024 x 18 blocks. That costs 12 more block RAMs than the
    1024 x 18 packing (the parity bits go unused).
  * Read data never feeds the address, write data or write enable of store,
    heads or trail in the same cycle; it is registered first. Only the small
    asg memory takes an address from other read data (the trail, on
    backtrack) and the store's data reaches asg's address through a register.
Out of context, nextpnr reaches about 58 MHz; the design runs at 50 MHz.

Cycle costs (1-cycle read latency; no read in the same cycle as a write that
could hit the same address):
    keep a watch (other watch true)      2 cycles (visits overlap; the next
                                         entries are read speculatively)
    start a watch list (per trail entry) ~9 cycles to the first verdict
    each replacement candidate scanned   1 cycle (pipelined; no writes)
    move a watch                         ~10 cycles plus the scan
    imply the other watch                ~5 cycles
    pop one trail entry on backtrack     1 cycle
    start-up                             2*nvars cycles of clearing, one
                                         cycle per store word (MARK), then
                                         about 9 cycles per clause

Writing a size while idle restarts the load (spec 3.4) when the value changes;
design.py passes no write strobe, so a rewrite with identical values is not
seen. The runner writes ABORT before every load, which resets everything.

Instance isolation: every register is reset by ABORT (ResetInserter), the
assignments and watch heads are cleared at START, the trail is written before
it is read, and the clause store is rebuilt by each load. Nothing else
survives between instances.
"""

from amaranth import Cat, Const, Elaboratable, Module, Mux, ResetInserter, Signal, signed
from amaranth.lib.memory import Memory

VAR_BITS = 14  # variable index width: 16384 variables
CODE_BITS = VAR_BITS + 1  # literal code: [0] negative, [14:1] variable
SADDR = 17  # clause-store address width
SDEPTH = 6 * 16384  # clause-store words (6 block RAMs of 16384 x 1 per bit)

# Literal word fields.
LAST = 15

# Reason codes reported in INFO.
INFO_EMPTY_CLAUSE = 0x01  # an empty clause in the stream: UNSAT at once
INFO_BAD_LITERAL = 0x02  # literal outside 1..nvars, or the clause store is full
INFO_UNIT_CONFLICT = 0x04  # two unit clauses contradict: UNSAT at once


class _Port:
    def __init__(self, abits, width, write):
        self.addr = Signal(abits)
        self.data = Signal(width)
        if write:
            self.en = Signal()


class BitSlicedMemory(Elaboratable):
    """A width x depth memory with one synchronous read port (`rd`, 1-cycle
    latency, not transparent) and one write port (`wr`), built from 1-bit-wide
    memories."""

    def __init__(self, width, depth):
        self.width, self.depth = width, depth
        abits = (depth - 1).bit_length()
        self.rd = _Port(abits, width, False)
        self.wr = _Port(abits, width, True)

    def elaborate(self, platform):
        m = Module()
        for i in range(self.width):
            mem = Memory(shape=1, depth=self.depth, init=[])
            m.submodules[f"bit{i}"] = mem
            r, w = mem.read_port(), mem.write_port()
            m.d.comb += [
                r.addr.eq(self.rd.addr),
                self.rd.data[i].eq(r.data),
                w.addr.eq(self.wr.addr),
                w.data.eq(self.wr.data[i]),
                w.en.eq(self.wr.en),
            ]
        return m


class Solver(Elaboratable):
    # Largest instance this design holds (see "Capacity" above).
    max_vars = 1 << VAR_BITS  # 16384
    max_clauses = 1 << 14  # 16384
    max_lits = SDEPTH - 1 - 2 * max_clauses  # 65535

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
        assert 1 + 2 * self.max_clauses + self.max_lits <= SDEPTH
        m = Module()

        # The three large memories are bit-sliced into 1-bit memories so that
        # their read data passes at most a 6:1 mux (see "Timing" above).
        m.submodules.store = store = BitSlicedMemory(18, SDEPTH)
        m.submodules.heads = heads = BitSlicedMemory(18, 2 * self.max_vars)
        m.submodules.trail = trail = BitSlicedMemory(17, self.max_vars)
        m.submodules.asg = asg = Memory(shape=2, depth=self.max_vars, init=[])

        st_r, st_w = store.rd, store.wr
        hd_r, hd_w = heads.rd, heads.wr
        tr_r, tr_w = trail.rd, trail.wr
        as_r, as_w = asg.read_port(), asg.write_port()

        m.d.comb += [st_w.en.eq(0), hd_w.en.eq(0), as_w.en.eq(0), tr_w.en.eq(0)]

        def st_write(addr, data):
            m.d.comb += [st_w.addr.eq(addr), st_w.data.eq(data), st_w.en.eq(1)]

        def hd_write(addr, data):
            m.d.comb += [hd_w.addr.eq(addr), hd_w.data.eq(data), hd_w.en.eq(1)]

        def as_write(addr, data):
            m.d.comb += [as_w.addr.eq(addr), as_w.data.eq(data), as_w.en.eq(1)]

        def tr_write(addr, data):
            m.d.comb += [tr_w.addr.eq(addr), tr_w.data.eq(data), tr_w.en.eq(1)]

        # ---- load state (kept while idle) ----
        lp = Signal(SADDR + 1, init=1)  # next free store word (word 0 = null)
        hcur = Signal(SADDR)  # header address of the clause being loaded
        lit0 = Signal(CODE_BITS)  # its first literal
        clen2 = Signal()  # it has a second, different literal stored
        last_addr = Signal(SADDR)  # last literal stored, to set its last flag
        last_word = Signal(16)
        pend = Signal()  # header write pending after a terminator
        clause_start = Signal(init=1)  # the next literal starts a clause
        empty_clause = Signal()
        bad_input = Signal()
        # Sizes as last seen, to restart the load when one changes (spec 3.4).
        sz_seen = Signal(96)
        sz_now = Cat(self.nvars, self.nclauses, self.nlits)

        # ---- solve state ----
        nv = Signal(VAR_BITS + 1)  # number of variables (<= max_vars)
        ci = Signal(VAR_BITS + 2)  # clear index (literal codes)
        tp = Signal(VAR_BITS + 1)  # trail size
        qhead = Signal(VAR_BITS + 1)  # next trail entry to propagate
        dptr = Signal(VAR_BITS + 1)  # every variable below it is assigned
        res = Signal(2)
        info = Signal(32)

        # start-up scan
        h = Signal(SADDR)  # header of the clause being scanned
        nxtc = Signal(SADDR)  # header of the clause after it
        lit0w = Signal(16)
        lit1w = Signal(16)

        # mark pass
        ma = Signal(SADDR + 1)  # next store word to read
        m_rv = Signal()  # a word was read last cycle
        m_skip = Signal(2)  # header words left before the next literal
        mw = Signal(16)  # literal word to mark
        mw_valid = Signal()

        # watch-list walk
        fl = Signal(CODE_BITS)  # the literal that just became false
        cur = Signal(18)  # current list entry (clause header, watch slot)
        nxt = Signal(18)  # the entry after it
        nxt2 = Signal(18)  # and the one after that (speculative)
        prev = Signal(18)  # the kept entry before it ...
        prev_head = Signal()  # ... or the list head
        other = Signal(16)  # the other watched literal of cur
        oth_asg = Signal(2)  # its assignment
        c1 = Signal(16)  # replacement scan: newest word read ...
        c1_addr = Signal(SADDR)
        c1_valid = Signal()
        cand = Signal(16)  # ... and the candidate being judged
        cand_addr = Signal(SADDR)
        cand_valid = Signal()
        waddr = Signal(SADDR + 1)  # address of the store word being read
        oldhead = Signal(18)  # a list head read from `heads`

        cur_h, cur_s = cur[:SADDR], cur[SADDR]
        nxt_h, nxt_s = nxt[:SADDR], nxt[SADDR]
        prev_h, prev_s = prev[:SADDR], prev[SADDR]

        def other_addr(hh, ss):
            # The other watch: position 1 for slot 0, position 0 for slot 1.
            return Mux(ss, hh + 2, hh + 3)

        m.d.comb += [self.result.eq(res), self.info.eq(info)]

        lit_mag = Signal(32)
        m.d.comb += lit_mag.eq(Mux(self.load_data < 0, -self.load_data, self.load_data))
        ld_code = Cat(self.load_data < 0, (lit_mag - 1)[:VAR_BITS])
        ld_word = Cat(ld_code, Const(0, 1))

        def visit(p):
            """Start on list entry p (a register): read its next pointer."""
            m.d.comb += st_r.addr.eq(p[:SADDR] + p[SADDR])
            m.d.sync += cur.eq(p)
            with m.If(p[:SADDR] == 0):
                m.next = "Q0"  # end of the list
            with m.Else():
                m.next = "WB"

        def finish(result):
            m.d.sync += res.eq(result)
            m.next = "DONE"

        with m.FSM(init="IDLE"):
            # ------------------------------------------------------------ load
            with m.State("IDLE"):
                m.d.comb += [self.idle.eq(1), self.load_ready.eq(~pend)]
                m.d.sync += sz_seen.eq(sz_now)
                with m.If(sz_now != sz_seen):
                    # A size was rewritten: the stream starts over (spec 3.4).
                    # A rewrite with identical values cannot be seen here, as
                    # design.py passes no write strobe; the runner always
                    # writes ABORT before a load, which resets everything.
                    m.d.sync += [
                        lp.eq(1),
                        clause_start.eq(1),
                        clen2.eq(0),
                        pend.eq(0),
                        empty_clause.eq(0),
                        bad_input.eq(0),
                    ]
                with m.Elif(pend):
                    # Header word 0 of the clause just ended: next clause address.
                    st_write(hcur, lp)
                    m.d.sync += pend.eq(0)
                with m.Elif(self.load_valid & ~self.abort):
                    with m.If(self.load_data == 0):
                        with m.If(clause_start):
                            m.d.sync += empty_clause.eq(1)
                        with m.Else():
                            st_write(last_addr, last_word | (1 << LAST))
                            m.d.sync += pend.eq(1)
                        m.d.sync += clause_start.eq(1)
                    with m.Elif(lit_mag > self.nvars):
                        m.d.sync += bad_input.eq(1)
                    with m.Elif(clause_start):
                        with m.If(lp + 3 > SDEPTH):
                            m.d.sync += bad_input.eq(1)
                        with m.Else():
                            st_write(lp + 2, ld_word)
                            m.d.sync += [
                                hcur.eq(lp),
                                lp.eq(lp + 3),
                                lit0.eq(ld_code),
                                clen2.eq(0),
                                last_addr.eq(lp + 2),
                                last_word.eq(ld_word),
                                clause_start.eq(0),
                            ]
                    with m.Elif(~clen2 & (ld_code == lit0)):
                        pass  # repeat of the leading literal: drop it
                    with m.Elif(lp >= SDEPTH):
                        m.d.sync += bad_input.eq(1)
                    with m.Else():
                        st_write(lp, ld_word)
                        m.d.sync += [
                            lp.eq(lp + 1),
                            clen2.eq(1),
                            last_addr.eq(lp),
                            last_word.eq(ld_word),
                        ]
                with m.If(self.start & ~self.abort):
                    m.d.sync += [
                        nv.eq(self.nvars),
                        ci.eq(0),
                        tp.eq(0),
                        qhead.eq(0),
                        dptr.eq(0),
                        h.eq(1),
                        res.eq(0),
                        info.eq(0),
                    ]
                    with m.If(bad_input):
                        m.d.sync += info.eq(INFO_BAD_LITERAL)
                        m.next = "REJECT"
                    with m.Elif(empty_clause):
                        m.d.sync += info.eq(INFO_EMPTY_CLAUSE)
                        finish(2)
                    with m.Else():
                        m.next = "CLEAR"

            # Clear the watch heads of every literal, and assign every
            # variable false. The mark pass then unassigns the variables that
            # occur in some clause, so a variable that occurs nowhere stays
            # assigned for the whole solve: it is never decided, never on the
            # trail and never flipped by a backtrack.
            with m.State("CLEAR"):
                with m.If(ci < Cat(Const(0, 1), nv)):
                    hd_write(ci, 0)
                    as_write(ci[1:], 0b10)
                    m.d.sync += ci.eq(ci + 1)
                with m.Else():
                    m.d.sync += [ma.eq(1), m_rv.eq(0), m_skip.eq(2), mw_valid.eq(0)]
                    m.next = "MARK"

            # Read the clause store word by word (one per cycle) and unassign
            # the variable of every literal word. Each clause is two header
            # words, then literals up to the one with the last flag. Store data
            # reaches asg's address only through a register (mw).
            with m.State("MARK"):
                d = st_r.data
                m.d.comb += st_r.addr.eq(ma)
                m.d.sync += [ma.eq(ma + 1), m_rv.eq(ma < lp), mw.eq(d), mw_valid.eq(0)]
                with m.If(m_rv):
                    with m.If(m_skip != 0):
                        m.d.sync += m_skip.eq(m_skip - 1)
                    with m.Else():
                        m.d.sync += mw_valid.eq(1)
                        with m.If(d[LAST]):
                            m.d.sync += m_skip.eq(2)
                with m.If(mw_valid):
                    as_write(mw[1:CODE_BITS], 0)
                with m.If((ma >= lp) & ~m_rv & ~mw_valid):
                    m.next = "I0"

            # ------------------------------------------------ start-up scan
            with m.State("I0"):
                m.d.comb += st_r.addr.eq(h)
                with m.If(h >= lp):
                    m.next = "Q0"
                with m.Else():
                    m.next = "I1"

            with m.State("I1"):
                m.d.sync += nxtc.eq(st_r.data)
                m.d.comb += st_r.addr.eq(h + 2)
                m.next = "I2"

            with m.State("I2"):
                m.d.sync += lit0w.eq(st_r.data)
                m.d.comb += st_r.addr.eq(h + 3)
                m.next = "I3"

            with m.State("I3"):
                m.d.sync += lit1w.eq(st_r.data)
                m.d.comb += [
                    as_r.addr.eq(lit0w[1:CODE_BITS]),
                    hd_r.addr.eq(lit0w[:CODE_BITS]),
                ]
                with m.If(lit0w[LAST]):
                    m.next = "IU"
                with m.Else():
                    m.next = "I4"

            # Unit clause: assign it at level 0.
            with m.State("IU"):
                a = as_r.data
                with m.If(a[1] & (a[0] == lit0w[0])):
                    m.d.sync += info.eq(INFO_UNIT_CONFLICT)
                    finish(2)
                with m.Else():
                    with m.If(~a[1]):
                        as_write(lit0w[1:CODE_BITS], Cat(~lit0w[0], Const(1, 1)))
                        tr_write(tp, Cat(lit0w[1:CODE_BITS], ~lit0w[0], Const(0, 2)))
                        m.d.sync += tp.eq(tp + 1)
                    m.d.sync += h.eq(nxtc)
                    m.next = "I0"

            # Push (h, 0) on the list of position 0's literal ...
            with m.State("I4"):
                m.d.sync += oldhead.eq(hd_r.data)
                m.next = "I5"

            with m.State("I5"):
                st_write(h, oldhead)
                hd_write(lit0w[:CODE_BITS], Cat(h, Const(0, 1)))
                m.next = "I6"

            # ... and (h, 1) on the list of position 1's literal (a different
            # literal: the loader guarantees it).
            with m.State("I6"):
                m.d.comb += hd_r.addr.eq(lit1w[:CODE_BITS])
                m.next = "I7"

            with m.State("I7"):
                m.d.sync += oldhead.eq(hd_r.data)
                m.next = "I8"

            with m.State("I8"):
                st_write(h + 1, oldhead)
                hd_write(lit1w[:CODE_BITS], Cat(h, Const(1, 1)))
                m.d.sync += h.eq(nxtc)
                m.next = "I0"

            # ---------------------------------------------------- propagate
            with m.State("Q0"):
                m.d.comb += [tr_r.addr.eq(qhead), as_r.addr.eq(dptr)]
                with m.If(qhead == tp):
                    m.next = "DEC"
                with m.Else():
                    m.next = "Q1"

            with m.State("Q1"):
                e = tr_r.data
                m.d.sync += [
                    fl.eq(Cat(e[VAR_BITS], e[:VAR_BITS])),  # the literal made false
                    qhead.eq(qhead + 1),
                    prev_head.eq(1),
                ]
                m.next = "Q2"

            with m.State("Q2"):
                m.d.comb += hd_r.addr.eq(fl)
                m.next = "Q3"

            with m.State("Q3"):
                m.d.sync += nxt.eq(hd_r.data)
                m.next = "Q4"

            with m.State("Q4"):
                visit(nxt)

            # The walk. Visits overlap so that a kept watch costs two cycles
            # (WX, WY): while cur's other watch is being looked up in asg, the
            # store reads for the next two entries are already issued. These
            # reads are speculative and harmless: nothing is written in
            # WB..WY, and their data is dropped if cur's watch has to move.
            # Store data only ever reaches asg's address through a register.
            #
            # WB: cur's next pointer arrives. Read cur's other watch.
            with m.State("WB"):
                m.d.sync += nxt.eq(st_r.data)
                m.d.comb += st_r.addr.eq(other_addr(cur_h, cur_s))
                m.next = "WC"

            # WC: cur's other watch arrives. Read nxt's next pointer.
            with m.State("WC"):
                m.d.sync += other.eq(st_r.data)
                m.d.comb += st_r.addr.eq(nxt_h + nxt_s)
                m.next = "WX"

            # WX: look up cur's other watch. nxt's next pointer arrives; read
            # nxt's other watch.
            with m.State("WX"):
                m.d.sync += nxt2.eq(st_r.data)
                m.d.comb += [
                    as_r.addr.eq(other[1:CODE_BITS]),
                    st_r.addr.eq(other_addr(nxt_h, nxt_s)),
                ]
                m.next = "WY"

            # WY: cur's other watch's value and nxt's other watch arrive. Read
            # nxt2's next pointer.
            with m.State("WY"):
                a = as_r.data
                m.d.comb += st_r.addr.eq(nxt2[:SADDR] + nxt2[SADDR])
                m.d.sync += oth_asg.eq(a)
                with m.If(a[1] & (a[0] != other[0])):
                    # Other watch is true: keep this watch, go on to nxt.
                    m.d.sync += [
                        prev.eq(cur),
                        prev_head.eq(0),
                        cur.eq(nxt),
                        nxt.eq(nxt2),
                        other.eq(st_r.data),
                    ]
                    with m.If(nxt_h == 0):
                        m.next = "Q0"
                    with m.Else():
                        m.next = "WX"
                with m.Else():
                    m.next = "WE"

            # Look for a replacement watch. For slot 0 the other watch is
            # position 1, so its last flag says whether the clause is binary;
            # for slot 1, read position 1 to find out.
            with m.State("WE"):
                m.d.comb += st_r.addr.eq(Mux(cur_s, cur_h + 3, cur_h + 4))
                m.d.sync += [waddr.eq(cur_h + 4), c1_valid.eq(0), cand_valid.eq(0)]
                with m.If(cur_s):
                    m.next = "WP1"
                with m.Elif(other[LAST]):
                    m.next = "NOREP"
                with m.Else():
                    m.next = "SRCH"

            with m.State("WP1"):
                m.d.comb += st_r.addr.eq(cur_h + 4)
                with m.If(st_r.data[LAST]):
                    m.next = "NOREP"
                with m.Else():
                    m.next = "SRCH"

            # Scan positions 2.. for a literal that is not false, one per
            # cycle, in a three-stage pipeline: the store word read last cycle
            # (at waddr) arrives and is registered in c1; c1's value is
            # requested from asg; cand (the word before c1) gets its value
            # and is judged. The next word is read every cycle; words past the
            # clause's last literal are never judged. Nothing is written.
            with m.State("SRCH"):
                a = as_r.data
                cand_false = a[1] & (a[0] == cand[0])
                shift = Signal()
                m.d.comb += [as_r.addr.eq(c1[1:CODE_BITS]), st_r.addr.eq(waddr + 1)]
                with m.If(cand_valid):
                    with m.If(~cand_false & (cand[:CODE_BITS] != other[:CODE_BITS])):
                        m.next = "F1"
                    with m.Elif(cand[LAST]):
                        m.next = "NOREP"
                    with m.Else():
                        m.d.comb += shift.eq(1)
                with m.Else():
                    m.d.comb += shift.eq(1)
                with m.If(shift):
                    m.d.sync += [
                        cand.eq(c1),
                        cand_addr.eq(c1_addr),
                        cand_valid.eq(c1_valid),
                        c1.eq(st_r.data),
                        c1_addr.eq(waddr),
                        c1_valid.eq(1),
                        waddr.eq(waddr + 1),
                    ]

            # No replacement: imply the other watch, or conflict.
            with m.State("NOREP"):
                with m.If(oth_asg[1]):
                    m.next = "BT"  # other watch false: every literal is false
                with m.Else():
                    as_write(other[1:CODE_BITS], Cat(~other[0], Const(1, 1)))
                    tr_write(tp, Cat(other[1:CODE_BITS], ~other[0], Const(0, 2)))
                    m.d.sync += [tp.eq(tp + 1), prev.eq(cur), prev_head.eq(0)]
                    visit(nxt)

            # Replacement found at cand_addr: move the watch there.
            with m.State("F1"):
                # The watch position gets the new literal (positions 0 and 1
                # are never last here: the clause has at least 3 literals).
                st_write(other_addr(cur_h, ~cur_s), Cat(cand[:CODE_BITS], Const(0, 3)))
                m.d.comb += hd_r.addr.eq(cand[:CODE_BITS])  # != fl: cand is not false
                with m.If(prev_head):
                    hd_write(fl, nxt)  # unlink cur at the head
                m.next = "F2"

            with m.State("F2"):
                # The false literal goes where the candidate was, keeping that
                # position's last flag.
                st_write(cand_addr, Cat(fl, cand[LAST]))
                m.d.sync += oldhead.eq(hd_r.data)
                m.next = "F3"

            with m.State("F3"):
                # Push cur on the new literal's list. The next visit may read
                # nxt's header in this cycle: nxt is neither cur nor prev (the
                # two watches of a clause are different literals), so the read
                # and the write never share an address.
                st_write(cur_h + cur_s, oldhead)
                hd_write(cand[:CODE_BITS], cur)
                with m.If(prev_head):
                    visit(nxt)
                with m.Else():
                    m.next = "F4"

            with m.State("F4"):
                st_write(prev_h + prev_s, nxt)  # unlink cur after prev
                visit(nxt)

            # ------------------------------------------------------- decide
            # as_r holds asg[dptr]. Skip assigned variables, one per cycle.
            with m.State("DEC"):
                a = as_r.data
                m.d.comb += as_r.addr.eq(dptr + 1)
                with m.If(dptr >= nv):
                    finish(1)  # every variable assigned, no conflict: SAT
                with m.Elif(a[1]):
                    m.d.sync += dptr.eq(dptr + 1)
                with m.Else():
                    # Decide with the saved phase (false at first).
                    as_write(dptr, Cat(a[0], Const(1, 1)))
                    tr_write(tp, Cat(dptr[:VAR_BITS], a[0], Const(1, 1), Const(0, 1)))
                    m.d.sync += tp.eq(tp + 1)
                    m.next = "Q0"

            # ---------------------------------------------------- backtrack
            with m.State("BT"):
                m.d.comb += tr_r.addr.eq(tp - 1)
                with m.If(tp == 0):
                    finish(2)
                with m.Else():
                    m.next = "BT_POP"

            # tr_r holds trail[tp-1]; trail[tp-2] is read in case we pop.
            with m.State("BT_POP"):
                e = tr_r.data
                t_var = e[:VAR_BITS]
                t_val = e[VAR_BITS]
                t_decision = e[VAR_BITS + 1]
                t_flipped = e[VAR_BITS + 2]
                m.d.comb += tr_r.addr.eq(tp - 2)
                with m.If(t_decision & ~t_flipped):
                    as_write(t_var, Cat(~t_val, Const(1, 1)))
                    tr_write(tp - 1, Cat(t_var, ~t_val, Const(1, 1), Const(1, 1)))
                    m.d.sync += qhead.eq(tp - 1)
                    m.next = "Q0"
                with m.Else():
                    as_write(t_var, Cat(t_val, Const(0, 1)))  # keep the phase
                    m.d.sync += tp.eq(tp - 1)
                    with m.If(t_var < dptr):
                        m.d.sync += dptr.eq(t_var)
                    with m.If(tp == 1):
                        finish(2)

            with m.State("DONE"):
                m.d.comb += [
                    self.done.eq(1),
                    as_r.addr.eq(self.model_addr),
                    self.model_val.eq(as_r.data[0]),
                ]

            with m.State("REJECT"):
                m.d.comb += self.rejected.eq(1)

        # ABORT resets every register of the solver (the FSM returns to IDLE,
        # the load pointer to 1) in the cycle after it rises. Memory contents
        # are not reset; the solve state in them is rebuilt at the next START,
        # and the clause memory is overwritten by the next load.
        top = Module()
        top.submodules.core = ResetInserter(self.abort)(m)
        return top
