"""A CDCL SAT solver with two watched literals, in Amaranth, for register map v1.

`design.py` implements the register map (docs/register_map_v1.md) and talks to
this module through the small interface documented in the template:

    in:  start, abort, nvars, nclauses, nlits, load_valid, load_data, model_addr
    out: idle, load_ready, done, rejected, result, info, model_val

Algorithm
---------
Conflict-driven clause learning (CDCL), MiniSat style:

* Unit propagation with two watched literals. Every clause of two or more
  literals watches its literals at positions 0 and 1. The watch lists are
  singly linked lists threaded through the clause headers, so they need no
  allocation. The trail is also the propagation queue (`qhead`). For each
  clause on the list of the literal that just became false:
      other watch true            -> keep the watch
      some literal at position 2+ is not false (and is not the other watch)
                                  -> swap it into the watch position and move
                                     the clause to that literal's list
      otherwise, other unassigned -> imply the other watch (reason: clause)
      otherwise                   -> conflict
* Every assignment records its decision level and its reason (the header
  address of the implying clause + 2, 0 for decisions and level-0 facts).
* First-UIP conflict analysis: the conflicting clause and then the reasons of
  the marked current-level variables are resolved, walking the trail
  backwards with a per-variable `seen` mark and a counter of unresolved
  current-level literals. Literals of lower levels (level 0 excluded) are
  written straight into the learned-clause area of the clause store.
* Minimization (MiniSat's basic, non-recursive mode): a lower-level literal
  whose reason clause has only marked or level-0 literals is dropped.
* The UIP goes to position 0 and the literal of the highest level to
  position 1, so the clause is asserting after backjumping to that level.
  Seen marks are cleared by re-reading the learned literals and while popping
  the trail; there is no other list of marked variables.
* Non-chronological backjumping: the trail is popped down to the backjump
  level (unassigning; the value stays as the saved phase); then the UIP
  literal is asserted with the new clause as reason. A unit clause is
  asserted at level 0 without a reason and is not stored.
* Decisions: EVSIDS with a binary max-heap in block RAM (heap array, position
  per variable, activity per variable), as in MiniSat. Every variable marked
  in an analysis gets the activity increment, which grows by 2^(1/16) per
  conflict (decay 0.958); activities are 16-bit floats (6-bit exponent,
  10-bit mantissa) and are all divided by 2^32 when the increment gets
  large. Decisions pop the heap top until an unassigned variable comes out
  and give it its saved phase (false at first); variables popped or
  unassigned are re-inserted when the backjump unassigns them.
* Restarts: Luby sequence, unit 128 conflicts. Phases are kept.
* Clause database reduction, always at a restart (level 0, after full
  propagation, so no learned clause is the reason of anything but level-0
  facts, whose reasons are never read): the learned area is compacted, keeping
  "glue" clauses (all lower-level literals on one level, so LBD <= 2) and
  clauses that were used as a reason in an analysis since the last reduction
  (new clauses count as used once). Then every watch list is rebuilt from
  scratch by rescanning the store. Positions 0 and 1 of every clause are a
  valid watch pair at that point: with level 0 fully propagated, a clause
  either has a true watch or two non-false watches. A reduction runs every
  2000 + 300k conflicts, and also when the free room could not hold the next
  learned clause (that conflict is then dropped: restart, reduce, go on).
  If too little room is left after compaction, it is repeated keeping only
  glue clauses, and then nothing.
* UNSAT on a conflict at level 0. SAT when the heap is empty (every variable
  that occurs in a clause is assigned) with the propagation queue empty.

Loading
-------
Clauses are stored as they stream in, after the watch-list heads. A clause is
two header words followed by its literals. While the leading literal of a
clause repeats it is not stored again, so positions 0 and 1 always hold
different literals and (x v x) becomes the unit (x). At a clause's terminator
the last literal is rewritten with its "last" flag; the store is parsed
sequentially using these flags. At START the solver clears the watch heads,
assignments, levels, activities and seen marks, then:
  MARK   unassigns every variable that occurs in some clause; every other
         variable stays assigned false for the whole solve and is never decided
  QI     puts the used variables in the decision heap
  ISCAN  assigns unit clauses at level 0 (a contradicting unit means UNSAT)
         and links every other clause on the lists of positions 0 and 1.

Memories (one read and one write port each, block RAM)
--------
    store  81920 x 18  one pool, bit-sliced into 16384 x 1 memories (each bit
                       has its own write enable):
                         [0, 2*nv)        watch-list head per literal code
                         2*nv             unused
                         [2*nv+1, oend)   original clauses
                         [oend, lfree)    learned clauses
                       A clause at header address h:
                         h     next pointer of the watch at position 0
                         h+1   next pointer of the watch at position 1
                         h+2.. literals: [0] negative, [14:1] variable
                               (0-based), [15] last literal of the clause,
                               [17] (position 0 only) the clause is binary
                               (set when it is linked)
                       A learned clause also has a meta word at h-1:
                         [0] glue (LBD <= 2), [1] used since last reduction.
                       A pointer to the watch in slot s of clause h is
                       [16:0] h + s (the address of that watch's own next
                       pointer, so following a list needs no adder), [17] s.
                       Address 0 is the null pointer (it is a head, never a
                       clause).
    asg_a   8192 x  1  assigned
    asg_v   8192 x  1  value (kept on unassign: saved phase; the model)
    seen    8192 x  1  analysis mark
    lr      8192 x 31  [13:0] decision level, [30:14] reason: h + 2 for
                       the clause at header h (its first literal), 0 for none
    trail   8192 x 16  [13:0] variable, [14] value, [15] decision
    heap    8192 x 14  decision heap: variable at each position
    hpos    8192 x 15  [13:0] heap position of each variable, [14] in heap
    act     8192 x 16  activity
Each is a `Bram`. The competition build (Solver.bram_primitives = False)
makes it one amaranth Memory per column group of the block plan below, and
tools/gen_verilog.py deletes the zero initialisers Amaranth gives every
Memory (one Verilog line per word, which yosys elaborates very slowly, and
with tens of GB, on this design), so yosys infers exactly this tiling with
no initialisation. Explicit DP16KD instances (bram_primitives = True) give
the same tiling and behaviour. The store is 16384 x 1 blocks (per-bit write
enables), 5 banks per bit. The per-variable memories wider than one bit are
built from 1024 x 18 / 2048 x 9 blocks plus narrower ones for the remaining
bits. Block RAMs: store 90, asg 2, seen 1, lr 14, trail 8, heap 6, hpos 7,
act 8 = 136 DP16KD. The template says 183 are free, but the real SoC's
firmware ROM takes more, and the platform allows about 155 (mrg-sandbox#35);
that limit is why the variable capacity is 8192, not 16384. A Bram behaves exactly like a
non-transparent Memory read port (old data on a same-cycle write); see its
docstring for how. With bram_primitives = False every Bram is a Memory,
which the Amaranth simulator (tests) can run.

Capacity
--------
Declared: 8192 variables, 16384 clauses, 65535 literals. The pool holds
2*nvars heads + 2*nclauses headers + nlits literals + 1, and the solver needs
room for learning: at START it sets REJECTED (INFO 0x08) unless at least
2*nvars + 16 words are left. So each declared limit can be reached on its own,
but not all three at once; spec 3.9 allows this ("REJECTED after START ...
because of how the clauses are distributed"), and it is never a wrong answer.
Of the 70 public instances, all but one (16,278 variables) fit; the largest
needs 68,632 of the 81,920 words. A
learned clause takes 4 + (number of lower-level literals) <= 4 + trail size
words, and analysis starts only when that much room is free.

Timing
------
On the ECP5 a block RAM's read data appears about 6 ns after the clock, and an
address that fans out to a hundred block RAMs needs several more ns of
routing. So the store is bit-sliced (read data passes a 5:1 mux), store read
data never feeds the address, write data or write enable of the store in the
same cycle (it is registered first; reads past the end of a clause are issued
speculatively rather than steered by the last flag), the data of the packed
per-variable memories is registered before it steers control, and only the
small 1-bit memories (asg, seen) take an address straight from other read
data. Out of context nextpnr reaches 53-56 MHz (seeds 1-4); the design runs
at 50 MHz.

Cycle costs (1-cycle read latency; no read in the same cycle as a write that
could hit the same address):
    keep a watch (other watch true)      2 cycles (visits overlap)
    start a watch list (per trail entry) ~9 cycles to the first verdict
    each replacement candidate scanned   1 cycle (pipelined)
    move a watch                         ~11 cycles plus the scan
    imply the other watch                ~5 cycles
    analysis: each literal of a resolved clause 1 cycle (pipelined), each
    trail entry walked 4 cycles; minimization ~7 cycles plus the reason
    length per learned literal
    bump: ~5 cycles plus 5 per heap level climbed
    pop one trail entry on backjump      4 cycles (plus a heap insert if the
                                         variable had left the heap)
    decision: ~8 cycles plus 6 per heap level per heap pop

Writing a size while idle restarts the load (spec 3.4) when the value changes;
design.py passes no write strobe, so a rewrite with identical values is not
seen. The runner writes ABORT before every load, which resets everything.

Instance isolation: every register is reset by ABORT (ResetInserter). At START
the watch heads, assignments, levels/reasons, activities and seen marks are
cleared, the heap is rebuilt, the trail is written before it is read, and the
clause store (including the learned area) is rebuilt by each load. Nothing
else survives between instances.

INFO: the reason code for REJECTED or a give-up (RESULT 0); after SAT or
UNSAT it holds the number of conflicts (for logs only).
"""

import re

from amaranth import (Array, Cat, ClockSignal, Const, Elaboratable, Instance, Module, Mux,
                      ResetInserter, Signal, signed)
from amaranth.lib.memory import Memory

VAR_BITS = 14  # variable index width (encodings and signals)
NVAR = 1 << 13  # variables: per-variable memory depth and declared max_vars
CODE_BITS = VAR_BITS + 1  # literal code: [0] negative, [14:1] variable
SADDR = 17  # clause-store address width
SDEPTH = 5 * 16384  # clause-store words (5 block RAMs of 16384 x 1 per bit)
LEV_BITS = VAR_BITS  # stored decision level (0..nvars <= 8192 fits)
MAX_LEVEL = (1 << LEV_BITS) - 1

# Literal word fields.
LAST = 15
RMV = 16  # learned literal flagged for removal (only during minimization)
BIN = 17  # on position 0: the clause has exactly two literals
# Meta word fields (learned clauses).
M_GLUE = 0
M_USED = 1

# Activities (EVSIDS): 6-bit exponent, 10-bit mantissa.
ACT_EXP, ACT_MANT = 6, 10
ACT_BITS = ACT_EXP + ACT_MANT
RESCALE_AT = 48  # when the increment's exponent reaches this ...
RESCALE_BY = 32  # ... divide every activity by 2^32

# Search parameters (general values, not tuned to any instance).
RESTART_UNIT_LOG2 = 7  # Luby restarts, unit 128 conflicts
REDUCE_FIRST = 2000  # conflicts before the first reduction ...
REDUCE_INC = 300  # ... and the increment of that interval
MIN_ROOM_EXTRA = 16  # at START: free words >= 2 * nvars + this

# Reason codes reported in INFO.
INFO_EMPTY_CLAUSE = 0x01  # an empty clause in the stream: UNSAT at once
INFO_BAD_LITERAL = 0x02  # literal outside 1..nvars, or the clause store is full
INFO_UNIT_CONFLICT = 0x04  # two unit clauses contradict: UNSAT at once
INFO_NO_ROOM = 0x08  # the formula fits but leaves too little room to learn
INFO_LEVEL_LIMIT = 0x10  # decision level would exceed 16383 (gave up)


class _Port:
    def __init__(self, abits, width, write):
        self.addr = Signal(abits)
        self.data = Signal(width)
        if write:
            self.en = Signal()


# DP16KD aspect ratios: data width -> (depth, low address pins not used as
# address). Mirrors yosys' ecp5 brams_map.v: the word address goes on
# AD[13:k]; for x9 AD[2:0] are unused (0); for x18 AD[1:0] are the byte
# enables and AD[3:2] are unused (0).
_DP16KD_SHAPES = {1: (16384, 0), 2: (8192, 1), 4: (4096, 2), 9: (2048, 3), 18: (1024, 4)}


def _bram_plan(width, depth, bit_mask):
    """Cheapest way to tile a width x depth memory with DP16KD blocks.
    Returns a list of (first bit, bits used, block width). A masked memory
    (per-bit write enables) uses 1-bit-wide blocks only. Ties prefer fewer
    output-mux inputs (narrower, deeper blocks)."""
    shapes = [1] if bit_mask else [1, 2, 4, 9, 18]
    best = {0: (0, 0, [])}  # bits covered -> (blocks, mux inputs, plan)
    for w in range(1, width + 1):
        cands = []
        for tw in shapes:
            used = min(tw, w)
            prev = best[w - used]
            nb = -(-depth // _DP16KD_SHAPES[tw][0])
            cands.append((prev[0] + nb, prev[1] + nb * used, prev[2] + [(w - used, used, tw)]))
        best[w] = min(cands, key=lambda c: (c[0], c[1]))
    return sorted(best[width][2])


class Bram(Elaboratable):
    """A width x depth memory with one synchronous read port (`rd`: addr,
    data) and one write port (`wr`: addr, data, en; with `bit_mask`, also
    `mask`, the bits written, all by default).

    The read port is always enabled, has a 1-cycle latency and is not
    transparent, exactly like an amaranth.lib.memory.Memory read port with
    the default arguments: `rd.data` is the word at the address presented on
    the previous clock edge, as it was before a write in that same cycle.

    With `primitives` (see `Solver.bram_primitives`) it is built
    from ECP5 DP16KD block RAM instances, the way yosys maps such a memory
    (memory_libmap), but without any memory initialization in the Verilog (a
    DP16KD is zero after configuration; the solver clears what it needs at
    START):
      * port A writes, port B reads (CEB = 1, WEB = 0), both on the sync
        clock; NOREG (1-cycle latency), WRITEMODE NORMAL, no chip selects;
      * the write is registered and lands one cycle late. A read in the
        cycle of the logical write therefore gets the old data. A read of
        the word being written physically (the cycle after the logical
        write) is a cross-port collision, whose DOB is undefined on the
        device; it is replaced by the registered write data (bit by bit
        with `bit_mask`). So no DOB value from a collision is ever used, and
        the write side (address, data, enable) starts at flip-flops, which
        keeps it off the critical paths;
      * deep memories are split into banks; the bank of a read is decoded
        from a registered copy of the high address bits;
      * these registers are reset-less, like a memory, so ABORT (the
        ResetInserter around the solver) does not drop a write in flight.
    Without `primitives` it is one Memory, which the Amaranth simulator can
    run; both behave identically, cycle for cycle."""

    def __init__(self, width, depth, bit_mask=False, primitives=True):
        self.width, self.depth = width, depth
        self.bit_mask, self.primitives = bit_mask, primitives
        abits = (depth - 1).bit_length()
        self.rd = _Port(abits, width, False)
        self.wr = _Port(abits, width, True)
        if bit_mask:
            self.wr.mask = Signal(width, init=(1 << width) - 1)
        self.plan = _bram_plan(width, depth, bit_mask)

    @property
    def blocks(self):
        return sum(-(-self.depth // _DP16KD_SHAPES[tw][0]) for _, _, tw in self.plan)

    def elaborate(self, platform):
        m = Module()
        if not self.primitives:
            # One Memory per column group of the block plan (bits lo..lo+used)
            # and per bank (block depth), so yosys tiles each into exactly
            # one DP16KD of the shape the primitive build uses (for example
            # 2048x9 for a 9-bit group). Splitting by columns and banks does
            # not change behaviour. As in the primitive build below:
            #   * the write is registered and lands one cycle late, and a
            #     read of the word being written physically (the cycle after
            #     the logical write) takes the registered write data instead.
            #     So the read data of a physical collision is never used, and
            #     tools/gen_verilog.py marks every memory no_rw_check
            #     (otherwise yosys adds its own delayed write, comparator and
            #     bypass to every bank). The comparison is made in the cycle
            #     the data arrives, between registered copies of the read
            #     and write addresses, so it is off the address paths;
            #   * the banks' read data is combined with a one-hot bank select
            #     registered from the read address (an AND-OR: two LUT levels
            #     for five banks, the forwarded data included).
            width, abits = self.width, len(self.rd.addr)
            nbe = width if self.bit_mask else 1
            wa = Signal(abits, reset_less=True)
            wd = Signal(width, reset_less=True)
            wbe = Signal(nbe, reset_less=True)
            m.d.sync += [
                wa.eq(self.wr.addr),
                wd.eq(self.wr.data),
                wbe.eq(Mux(self.wr.en, self.wr.mask if self.bit_mask else 1, 0)),
            ]
            # Registered copies: the read address of the data arriving now,
            # and the write that was physically done in that read's cycle.
            ra_q = Signal(abits, reset_less=True)
            wa_q = Signal(abits, reset_less=True)
            wbe_q = Signal(nbe, reset_less=True)
            fwd_d = Signal(width, reset_less=True)
            m.d.sync += [ra_q.eq(self.rd.addr), wa_q.eq(wa), wbe_q.eq(wbe), fwd_d.eq(wd)]
            fwd = Signal(nbe)
            m.d.comb += fwd.eq(Mux(ra_q == wa_q, wbe_q, 0))
            fwd_bits = fwd if self.bit_mask else fwd.replicate(width)
            outs = []  # (bits lo.., used, [(select, data)]) per column group

            rsel = {}  # block depth -> one-hot bank of the read issued last cycle
            for lo, used, tw in self.plan:
                bdepth = _DP16KD_SHAPES[tw][0]
                bab = bdepth.bit_length() - 1
                nbanks = -(-self.depth // bdepth)
                en = wbe[lo:lo + used] if self.bit_mask else wbe[0]
                if nbanks > 1 and bdepth not in rsel:
                    rsel[bdepth] = Signal(nbanks, name=f"rsel{bdepth}", reset_less=True)
                    m.d.sync += rsel[bdepth].eq(
                        Cat(self.rd.addr[bab:] == b for b in range(nbanks)))
                terms = []
                for b in range(nbanks):
                    depth = min(bdepth, self.depth - b * bdepth) if nbanks > 1 else self.depth
                    mem = Memory(shape=used, depth=depth, init=[])
                    m.submodules[f"mem{lo}" if nbanks == 1 else f"mem{lo}_b{b}"] = mem
                    r = mem.read_port()
                    w = mem.write_port(granularity=1 if self.bit_mask else None)
                    if nbanks > 1:
                        m.d.comb += [
                            r.addr.eq(self.rd.addr[:bab]),
                            w.addr.eq(wa[:bab]),
                            w.en.eq(Mux(wa[bab:] == b, en, 0)),
                        ]
                        terms.append((rsel[bdepth][b], r.data))
                    else:
                        m.d.comb += [r.addr.eq(self.rd.addr), w.addr.eq(wa), w.en.eq(en)]
                        terms.append((1, r.data))
                    m.d.comb += w.data.eq(wd[lo:lo + used])
                outs.append((lo, used, terms))
            # Each bit: OR of (bank selected and not forwarded) & bank data,
            # and (forwarded) & write data.
            for lo, used, terms in outs:
                for i in range(lo, lo + used):
                    acc = Mux(fwd_bits[i], fwd_d[i], 0)
                    for sel, d in terms:
                        acc = acc | (sel & ~fwd_bits[i] & d[i - lo])
                    m.d.comb += self.rd.data[i].eq(acc)
            return m

        width, abits = self.width, len(self.rd.addr)
        # Write delayed by one cycle: address, data and per-bit (or whole
        # word) enables.
        nbe = width if self.bit_mask else 1
        wa = Signal(abits, reset_less=True)
        wd = Signal(width, reset_less=True)
        wbe = Signal(nbe, reset_less=True)
        m.d.sync += [
            wa.eq(self.wr.addr),
            wd.eq(self.wr.data),
            wbe.eq(Mux(self.wr.en, self.wr.mask if self.bit_mask else 1, 0)),
        ]
        # Forwarding: the read issued this cycle hits the word being written
        # now (physically); next cycle its data comes from the write register.
        fwd = Signal(nbe, reset_less=True)  # per enable bit
        fwd_d = Signal(width, reset_less=True)
        m.d.sync += [fwd.eq(Mux(self.rd.addr == wa, wbe, 0)), fwd_d.eq(wd)]
        fwd_bits = fwd if self.bit_mask else fwd.replicate(width)
        raw = Signal(width)  # data out of the block RAMs
        m.d.comb += self.rd.data.eq((raw & ~fwd_bits) | (fwd_d & fwd_bits))

        rsel = {}  # block depth -> bank of the read issued last cycle
        for lo, used, tw in self.plan:
            bdepth, k = _DP16KD_SHAPES[tw]
            bab = bdepth.bit_length() - 1  # address bits inside one block
            nbanks = -(-self.depth // bdepth)
            if nbanks > 1 and bdepth not in rsel:
                rsel[bdepth] = Signal(abits - bab, name=f"rsel{bdepth}", reset_less=True)
                m.d.sync += rsel[bdepth].eq(self.rd.addr[bab:])
            outs = []
            for b in range(nbanks):
                we = wbe[lo] if self.bit_mask else wbe[0]
                if nbanks > 1:
                    we = we & (wa[bab:] == b)
                do = Signal(tw, name=f"do_b{lo}_r{b}")
                if tw == 18:
                    low_a, low_b = Const(0b0011, 4), Const(0, 4)  # A: both byte enables
                else:
                    low_a = low_b = Const(0, k)
                ada = Cat(low_a, wa[:bab]) if k else wa[:bab]
                adb = Cat(low_b, self.rd.addr[:bab]) if k else self.rd.addr[:bab]
                dia = wd[lo:lo + used]
                kw = dict(
                    p_DATA_WIDTH_A=tw, p_DATA_WIDTH_B=tw,
                    p_REGMODE_A="NOREG", p_REGMODE_B="NOREG",
                    p_RESETMODE="SYNC", p_ASYNC_RESET_RELEASE="SYNC",
                    p_CSDECODE_A="0b000", p_CSDECODE_B="0b000",
                    p_WRITEMODE_A="NORMAL", p_WRITEMODE_B="NORMAL",
                    p_GSR="AUTO",
                    i_CLKA=ClockSignal("sync"), i_CLKB=ClockSignal("sync"),
                    i_CEA=Const(1), i_OCEA=Const(1), i_WEA=we, i_RSTA=Const(0),
                    i_CEB=Const(1), i_OCEB=Const(1), i_WEB=Const(0), i_RSTB=Const(0),
                )
                for c in range(3):
                    kw[f"i_CSA{c}"] = Const(0)
                    kw[f"i_CSB{c}"] = Const(0)
                for a in range(14):  # a shallow memory leaves high pins at 0
                    kw[f"i_ADA{a}"] = ada[a] if a < len(ada) else Const(0)
                    kw[f"i_ADB{a}"] = adb[a] if a < len(adb) else Const(0)
                for d in range(18):
                    kw[f"i_DIA{d}"] = dia[d] if d < used else Const(0)
                    kw[f"i_DIB{d}"] = Const(0)
                for d in range(tw):
                    kw[f"o_DOB{d}"] = do[d]
                m.submodules[f"b{lo}_r{b}"] = Instance("DP16KD", **kw)
                outs.append(do[:used])
            if nbanks == 1:
                m.d.comb += raw[lo:lo + used].eq(outs[0])
            else:
                # A bank past the end of the memory does not exist (a read
                # there is out of range); it reads as 0.
                with m.Switch(rsel[bdepth]):
                    for b in range(nbanks):
                        with m.Case(b):
                            m.d.comb += raw[lo:lo + used].eq(outs[b])
        return m


def parallel_switches(text):
    """Mark the Switch on the one-hot FSM state (`fsm_oh`) parallel_case in
    RTLIL text from amaranth.back.rtlil.convert. Its cases test one bit each
    and exactly one bit is set, so no two cases can match at once; with the
    mark, yosys' proc builds one parallel multiplexer per signal instead of a
    priority chain through every state. Used by tools/gen_verilog.py and
    sim/export_verilog.py."""
    out, n = [], 0
    for line in text.split("\n"):
        if re.fullmatch(r"\s*switch \\fsm_oh( \[\d+:0\])?", line):
            out.append(line[: len(line) - len(line.lstrip())] + "attribute \\parallel_case 1")
            n += 1
        out.append(line)
    assert n > 0, "no switch on fsm_oh found"
    return "\n".join(out)


class Solver(Elaboratable):
    # Largest instance this design accepts (see "Capacity" above). Each limit
    # can be reached on its own; an instance whose heads, clauses and learning
    # room do not fit together is REJECTED after START (spec 3.9).
    max_vars = NVAR  # 8192
    max_clauses = 1 << 14  # 16384
    max_lits = (1 << 16) - 1  # 65535

    # False (the competition build): plain amaranth.lib.memory.Memory, one per
    # block-plan column group; tools/gen_verilog.py deletes their zero
    # initialisers and yosys infers DP16KD. True: explicit ECP5 DP16KD
    # instances (kept for comparison runs; the platform's export runs
    # `hierarchy -check` without the ECP5 cell library, so it rejects them).
    # Both behave identically, cycle for cycle.
    bram_primitives = False

    def __init__(self, sdepth=SDEPTH, reduce_first=REDUCE_FIRST, reduce_inc=REDUCE_INC,
                 restart_log2=RESTART_UNIT_LOG2):
        # The defaults are the competition build. Tests use a smaller store
        # and shorter intervals to force reductions and restarts.
        assert sdepth <= SDEPTH
        self.sdepth = sdepth
        self.reduce_first = reduce_first
        self.reduce_inc = reduce_inc
        self.restart_log2 = restart_log2
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

        # ------------------------------------------------------- memories
        def bram(width, depth=NVAR, bit_mask=False):
            return Bram(width, depth, bit_mask=bit_mask, primitives=self.bram_primitives)

        m.submodules.store = store = bram(18, self.sdepth, bit_mask=True)
        m.submodules.asg_a = asg_a = bram(1)
        m.submodules.asg_v = asg_v = bram(1)
        m.submodules.seen = seen = bram(1)
        # Level and reason in separate memories: the level (8192 x 2
        # blocks, no bank mux) is compared as soon as it is read (Timing).
        m.submodules.lrl = lrl = bram(LEV_BITS)
        m.submodules.lrr = lrr = bram(SADDR)
        m.submodules.trail = trail = bram(16)
        m.submodules.heap = heap = bram(VAR_BITS)
        m.submodules.hpos = hpos = bram(VAR_BITS + 1)
        m.submodules.act = act = bram(ACT_BITS)
        self.brams = [store, asg_a, asg_v, seen, lrl, lrr, trail, heap, hpos, act]

        st_r, st_w = store.rd, store.wr
        aa_r, aa_w = asg_a.rd, asg_a.wr
        av_r, av_w = asg_v.rd, asg_v.wr
        sn_r, sn_w = seen.rd, seen.wr
        lrl_r, lrl_w = lrl.rd, lrl.wr
        lrr_r, lrr_w = lrr.rd, lrr.wr
        tr_r, tr_w = trail.rd, trail.wr
        hp_r, hp_w = heap.rd, heap.wr
        ps_r, ps_w = hpos.rd, hpos.wr
        ac_r, ac_w = act.rd, act.wr

        for w in (st_w, aa_w, av_w, sn_w, lrl_w, lrr_w, tr_w, hp_w, ps_w, ac_w):
            m.d.comb += w.en.eq(0)

        # Read address of both assignment memories (always the same variable).
        as_addr = Signal(VAR_BITS)
        m.d.comb += [aa_r.addr.eq(as_addr), av_r.addr.eq(as_addr)]
        as_data = Cat(av_r.data, aa_r.data)  # [0] value, [1] assigned

        # The control FSM, one-hot (Timing): fsm_oh[state_index[X]] is 1
        # exactly while in state X. The states are the cases of a Switch on
        # fsm_oh, each matching its own bit; goto(Y) in state X clears X's
        # bit and sets Y's. All other bits are 0 then and keep their value,
        # so each bit's next value depends only on the transitions into and
        # out of its own state. (An Amaranth FSM is binary, and yosys cannot
        # re-encode it: the next state then goes through a wide multiplexer
        # over all states, and every use of a state decodes seven bits.)
        # The cases never overlap, so the Switch is marked parallel_case
        # for synthesis (see parallel_switches below); without the mark it
        # behaves the same but synthesizes to priority logic.
        NSTATES = 128  # at least the number of states
        state_index = {"IDLE": 0}
        fsm_oh = Signal(NSTATES, init=1)
        oh_next = Signal(NSTATES)
        m.d.comb += oh_next.eq(fsm_oh)
        m.d.sync += fsm_oh.eq(oh_next)
        cur_state = [None]

        def sidx(name):
            if name not in state_index:
                state_index[name] = len(state_index)
            assert state_index[name] < len(fsm_oh)
            return state_index[name]

        def goto(name):
            m.d.comb += [oh_next[sidx(cur_state[0])].eq(0), oh_next[sidx(name)].eq(1)]

        class State:
            def __init__(self, name):
                self.name = name
                k = sidx(name)
                self.ctx = m.Case("-" * (NSTATES - 1 - k) + "1" + "-" * k)

            def __enter__(self):
                cur_state[0] = self.name
                sidx(self.name)
                return self.ctx.__enter__()

            def __exit__(self, *a):
                cur_state[0] = None
                return self.ctx.__exit__(*a)

        # The store read address is an AND-OR mux of registers selected by
        # fsm_oh, built after the FSM from the reads each state issues. A
        # state's read is issued whether or not the branch that asks for it
        # is taken (a read has no side effects).
        st_reads = {}  # repr of the address -> (address, [states])

        def st_read(addr):
            assert cur_state[0] is not None
            key = repr(addr)
            if key not in st_reads:
                st_reads[key] = (addr, [])
            if cur_state[0] not in st_reads[key][1]:
                st_reads[key][1].append(cur_state[0])

        # The store write address and data are AND-OR muxes too, selected
        # by fsm_oh (one write address and data per state); the enable and
        # the mask are set where the write is.
        st_writes = {}  # repr of (address, data) -> (address, data, [states])

        def st_write(addr, data, mask=None):
            assert cur_state[0] is not None
            m.d.comb += st_w.en.eq(1)
            if mask is not None:
                m.d.comb += st_w.mask.eq(mask)
            key = repr((addr, data))
            if key not in st_writes:
                st_writes[key] = (addr, data, [])
            if cur_state[0] not in st_writes[key][2]:
                st_writes[key][2].append(cur_state[0])

        def as_read(var):
            m.d.comb += as_addr.eq(var)

        def as_assign(var, value):
            m.d.comb += [
                aa_w.addr.eq(var), aa_w.data.eq(1), aa_w.en.eq(1),
                av_w.addr.eq(var), av_w.data.eq(value), av_w.en.eq(1),
            ]

        def as_unassign(var):  # the value stays: saved phase
            m.d.comb += [aa_w.addr.eq(var), aa_w.data.eq(0), aa_w.en.eq(1)]

        def sn_read(var):
            m.d.comb += sn_r.addr.eq(var)

        def sn_write(var, bit):
            m.d.comb += [sn_w.addr.eq(var), sn_w.data.eq(bit), sn_w.en.eq(1)]

        def lr_read(var):
            m.d.comb += [lrl_r.addr.eq(var), lrr_r.addr.eq(var)]

        def lr_write(var, level, reason):
            m.d.comb += [
                lrl_w.addr.eq(var), lrl_w.data.eq(level[:LEV_BITS]), lrl_w.en.eq(1),
                lrr_w.addr.eq(var), lrr_w.data.eq(reason[:SADDR]), lrr_w.en.eq(1),
            ]

        lr_level = lrl_r.data
        lr_reason = lrr_r.data

        def tr_read(pos):
            m.d.comb += tr_r.addr.eq(pos)

        def tr_write(pos, var, value, decision):
            if isinstance(decision, int):
                decision = Const(decision, 1)
            m.d.comb += [
                tr_w.addr.eq(pos),
                tr_w.data.eq(Cat(var[:VAR_BITS], value, decision)),
                tr_w.en.eq(1),
            ]

        tr_var = tr_r.data[:VAR_BITS]
        tr_val = tr_r.data[VAR_BITS]
        tr_dec = tr_r.data[VAR_BITS + 1]

        def hp_read(i):
            m.d.comb += hp_r.addr.eq(i)

        def hp_write(i, var):
            m.d.comb += [hp_w.addr.eq(i), hp_w.data.eq(var), hp_w.en.eq(1)]

        def ps_read(var):
            m.d.comb += ps_r.addr.eq(var)

        def ps_write(var, i, inheap):
            m.d.comb += [ps_w.addr.eq(var), ps_w.data.eq(Cat(i[:VAR_BITS], inheap)),
                         ps_w.en.eq(1)]

        def ac_read(var):
            m.d.comb += ac_r.addr.eq(var)

        def ac_write(var, a):
            m.d.comb += [ac_w.addr.eq(var), ac_w.data.eq(a), ac_w.en.eq(1)]

        ps_idx = ps_r.data[:VAR_BITS]
        ps_in = ps_r.data[VAR_BITS]

        def fadd(a, b):
            """Sum of two activities (6-bit exponent, 10-bit mantissa with a
            hidden 1; exponent 0 is zero). Truncating, which is fine for a
            heuristic."""
            ea, eb = a[ACT_MANT:], b[ACT_MANT:]
            a_big = ea >= eb
            ebig = Mux(a_big, ea, eb)
            d = Mux(a_big, ea - eb, eb - ea)[:ACT_EXP]
            mbig = Cat(Mux(a_big, a, b)[:ACT_MANT], Const(1, 1))
            msml = Cat(Mux(a_big, b, a)[:ACT_MANT], Const(1, 1))
            ssum = Signal(ACT_MANT + 2)
            m.d.comb += ssum.eq(mbig + Mux(d > ACT_MANT, 0, msml >> d))
            r = Mux(ssum[ACT_MANT + 1], Cat(ssum[1:ACT_MANT + 1], ebig + 1),
                    Cat(ssum[:ACT_MANT], ebig))
            return Mux(ea == 0, b, Mux(eb == 0, a, r))

        # ---- load state (kept while idle) ----
        lp = Signal(SADDR + 1, init=1)  # next free store word
        lit0 = Signal(CODE_BITS)  # first literal of the clause being loaded
        clen2 = Signal()  # it has a second, different literal stored
        last_addr = Signal(SADDR)  # last literal stored, to set its last flag
        last_word = Signal(16)
        clause_start = Signal(init=1)  # the next literal starts a clause
        empty_clause = Signal()
        bad_input = Signal()
        # Sizes as last seen, to restart the load when one changes (spec 3.4).
        sz_seen = Signal(96)
        sz_now = Cat(self.nvars, self.nclauses, self.nlits)

        # ---- solve state ----
        nv = Signal(VAR_BITS + 1)  # number of variables (<= max_vars)
        nv2p1 = Cat(Const(1, 1), nv)  # 2 * nv + 1: first clause header
        ci = Signal(VAR_BITS + 2)  # clear index
        tp = Signal(VAR_BITS + 1)  # trail size
        qhead = Signal(VAR_BITS + 1)  # next trail entry to propagate
        dl = Signal(VAR_BITS + 1)  # current decision level
        res = Signal(2)
        info = Signal(32)
        oend = Signal(SADDR + 1)  # end of the original clauses
        lfree = Signal(SADDR + 1)  # next free word of the learned area
        rt = Signal(SADDR + 1)  # reduction: minimum room after compaction

        # mark pass
        ma = Signal(SADDR + 1)
        m_rv = Signal()
        m_skip = Signal(2)
        mw = Signal(16)
        mw_valid = Signal()
        m_d = Signal(16)
        m_dv = Signal()

        # VMTF queue
        hn = Signal(VAR_BITS + 1)  # heap size
        hi = Signal(VAR_BITS + 1)  # heap position being filled (sift up / down)
        hx = Signal(VAR_BITS)  # variable being placed
        hax = Signal(ACT_BITS)  # its activity
        hp = Signal(VAR_BITS + 1)  # sift up: parent position
        hu = Signal(VAR_BITS)  # sift up: parent variable / sift down: child 1
        hu2 = Signal(VAR_BITS)  # sift down: child 2
        ha1 = Signal(ACT_BITS)
        ha2 = Signal(ACT_BITS)
        hret = Signal()  # sift up done: 0 to LB0, 1 to the pop loop
        inc_e = Signal(ACT_EXP, init=1)  # activity increment: exponent ...
        inc_k = Signal(4)  # ... and sixteenths of a doubling
        inc = Signal(ACT_BITS)
        inc_rom = Array(Const(int(round((2 ** (k / 16) - 1) * (1 << ACT_MANT))), ACT_MANT)
                        for k in range(16))
        m.d.comb += inc.eq(Cat(inc_rom[inc_k], inc_e))
        dv = Signal(VAR_BITS)  # decision candidate (heap top)
        dx = Signal(VAR_BITS)  # last heap entry
        dasg = Signal(2)  # candidate's assignment
        sc = Signal(VAR_BITS + 1)  # rescale index
        sc_rv = Signal()
        sc_var = Signal(VAR_BITS)
        sc_d = Signal(ACT_BITS)
        sc_dv = Signal()
        sc_var2 = Signal(VAR_BITS)
        qv = Signal(VAR_BITS + 1)  # queue build index
        q_rv = Signal()
        q_var = Signal(VAR_BITS)

        # store scan (start-up and rebuild) and watch linking
        h = Signal(SADDR + 1)  # header of the clause being scanned / linked
        inl = Signal()  # scanning the learned area (meta word before h)
        rebuild = Signal()  # rescan after a reduction: skip unit clauses
        sk = Signal(SADDR + 1)  # skip scan address
        # h + 1 .. h + 4 and sk + 1, kept in registers (Timing: no adder
        # between a register and the store address).
        h1 = Signal(SADDR + 1)
        h2 = Signal(SADDR + 1)
        h3 = Signal(SADDR + 1)
        h4 = Signal(SADDR + 1)
        sk1 = Signal(SADDR + 1)
        isk_last = Signal()
        isk_addr = Signal(SADDR + 1)
        isk_addr1 = isk_addr + 1
        lit0w = Signal(16)
        lit1w = Signal(16)
        lret = Signal()  # linking a learned clause (else scanning)

        # watch-list walk
        fl = Signal(CODE_BITS)  # the literal that just became false
        cur = Signal(18)  # current list entry (pointer: see "Memories")
        nxt = Signal(18)  # the entry after it
        nxt2 = Signal(18)  # and the one after that (speculative)
        prev = Signal(18)  # the kept entry before it ...
        prev_head = Signal()  # ... or the list head
        other = Signal(18)  # the other watched literal of cur (word)
        oth_asg = Signal(2)  # its assignment
        c1 = Signal(16)  # replacement scan: newest word read ...
        c1_addr = Signal(SADDR)
        c1_valid = Signal()
        cand = Signal(16)  # ... and the candidate being judged
        cand_addr = Signal(SADDR)
        fcand = Signal(16)  # the replacement found (F1..F4)
        fcand_addr = Signal(SADDR)
        cand_valid = Signal()
        waddr = Signal(SADDR + 1)
        waddr1 = Signal(SADDR + 1)  # waddr + 1
        oldhead = Signal(18)

        # A pointer p is (P = header + slot, slot): P is the address of the
        # watch's own next pointer. Addresses derived from cur are kept in
        # registers, computed when cur is set (always from nxt).
        cur_s = cur[SADDR]
        nxt_s = nxt[SADDR]
        cur_oa = Signal(SADDR + 1)  # other watched literal of cur
        cur_own = Signal(SADDR + 1)  # cur's own watched literal (header + 2 + slot)
        cur_h4 = Signal(SADDR + 1)  # header + 4: position 2
        cur_rsn = Signal(SADDR + 1)  # reason code: header + 2
        nxt_oa = Signal(SADDR + 1)  # other watched literal of nxt

        def other_addr(p):
            # The other watch: position 1 for slot 0, position 0 for slot 1.
            return Mux(p[SADDR], p[:SADDR] + 1, p[:SADDR] + 3)

        def set_cur(p):
            pp, ps = p[:SADDR], p[SADDR]
            m.d.sync += [
                cur.eq(p),
                cur_oa.eq(other_addr(p)),
                cur_own.eq(pp + 2),
                cur_h4.eq(Mux(ps, pp + 3, pp + 4)),
                cur_rsn.eq(Mux(ps, pp + 1, pp + 2)),
            ]

        def set_h(v):
            m.d.sync += [h.eq(v), h1.eq(v + 1), h2.eq(v + 2), h3.eq(v + 3), h4.eq(v + 4)]

        def set_sk(v):
            m.d.sync += [sk.eq(v), sk1.eq(v + 1)]

        # conflict analysis
        ccl = Signal(SADDR)  # clause being resolved: its first literal (header + 2)
        ra = Signal(SADDR + 1)  # its next word to read
        rv = Signal()  # a literal word was read last cycle
        w1 = Signal(16)  # literal word read (stage 2)
        v1 = Signal()
        w2 = Signal(16)  # literal word whose seen/level arrive (stage 3)
        v2 = Signal()
        w3 = Signal(16)  # literal judged in stage 4, with its registered
        v3 = Signal()  # seen mark and level tests
        s3 = Signal()
        l3nz = Signal()
        l3cur = Signal()
        vA = Signal(VAR_BITS)  # literal judged last cycle (bypass) ...
        mA = Signal()  # ... and whether it was marked
        vB = Signal(VAR_BITS)  # the same, two cycles ago
        mB = Signal()
        path_c = Signal(VAR_BITS + 1)  # unresolved current-level literals
        tidx = Signal(VAR_BITS + 1)  # trail walk position
        te = Signal(16)  # trail entry walked (finally the UIP)
        lh = Signal(SADDR + 1)  # learned clause header
        lw = Signal(SADDR + 1)  # next learned literal address
        maxlev = Signal(LEV_BITS)
        minlev = Signal(LEV_BITS)
        maxaddr = Signal(SADDR + 1)
        maxlit = Signal(CODE_BITS)
        firstlit = Signal(CODE_BITS)
        lastlit = Signal(CODE_BITS)
        la = Signal(SADDR + 1)  # pass over the learned literals: read ...
        wp = Signal(SADDR + 1)  # ... and write (compaction)
        lbw = Signal(18)
        lblev = Signal(LEV_BITS)
        mna = Signal(SADDR + 1)  # minimization: literal being checked
        mnw = Signal(18)
        mfail = Signal()
        bjl = Signal(VAR_BITS + 1)  # backjump target level
        bjk = Signal()  # 0: backjump after a conflict, 1: restart
        ureason = Signal(SADDR)  # reason of the asserted UIP literal (header + 2)

        # bump
        bv = Signal(VAR_BITS)
        bret = Signal()  # 0: back to the learned-literal pass, 1: to the pop loop
        pe = Signal(16)  # trail entry popped
        p_sn = Signal()  # its seen mark
        p_in = Signal()  # it is in the heap

        # restarts and reductions
        crst = Signal(32)  # conflicts since the last restart
        lu = Signal(24, init=1)  # Luby sequence state (u, v): limit = v * unit
        lv = Signal(24, init=1)
        rlimit = Signal(32)
        m.d.comb += rlimit.eq(lv << self.restart_log2)
        redc = Signal(32)  # conflicts since the last reduction
        rlim = Signal(32, init=self.reduce_first)
        need_reduce = Signal()
        rmode = Signal(2)  # 0 keep glue+used, 1 keep glue, 2 keep nothing
        rr = Signal(SADDR + 1)  # compaction read pointer
        rw = Signal(SADDR + 1)  # compaction write pointer
        r_rv = Signal()
        r_dv = Signal()  # r_d holds a word read (registered store data)
        r_d = Signal(18)
        rpos = Signal(2)  # word position in the clause: 0 meta, 1-2 header, 3 lit
        rkeep = Signal()
        r_wp = Signal()  # a word to write at rw
        r_wd = Signal(18)

        nconf = Signal(32)  # conflicts analysed (reported in INFO after SAT/UNSAT)
        m.d.comb += [self.result.eq(res), self.info.eq(Mux(res != 0, nconf, info))]

        lit_mag = Signal(32)
        m.d.comb += lit_mag.eq(Mux(self.load_data < 0, -self.load_data, self.load_data))
        ld_code = Cat(self.load_data < 0, (lit_mag - 1)[:VAR_BITS])
        ld_word = Cat(ld_code, Const(0, 1))
        # The load's one store write: the terminator flags the last literal;
        # a clause's first literal goes after the two header words.
        ld_waddr = Mux(self.load_data == 0, last_addr, Mux(clause_start, lp + 2, lp))
        ld_wdata = Mux(self.load_data == 0, last_word | (1 << LAST), ld_word)

        room = Signal(SADDR + 2)  # free words in the learned area
        m.d.comb += room.eq(self.sdepth - lfree)

        def visit(p):
            """Start on list entry p (a register): read its next pointer."""
            st_read(p[:SADDR])
            set_cur(p)
            with m.If(p[:SADDR] == 0):
                goto("Q0")  # end of the list
            with m.Else():
                goto("WB")

        def finish(result):
            m.d.sync += res.eq(result)
            goto("DONE")

        def pop_to(level, kind):
            m.d.sync += [bjl.eq(level), bjk.eq(kind)]
            goto("P0")

        # Handles for debugging in simulation (no hardware).
        self.dbg = dict(dl=dl, tp=tp, crst=crst, redc=redc, lfree=lfree, qhead=qhead, hn=hn,
                        path_c=path_c, lw=lw, lh=lh, bjl=bjl)

        with m.Switch(fsm_oh):  # the FSM (see State and goto)
            # ------------------------------------------------------------ load
            with State("IDLE"):
                m.d.comb += [self.idle.eq(1), self.load_ready.eq(1)]
                m.d.sync += sz_seen.eq(sz_now)
                with m.If(sz_now != sz_seen):
                    # A size was rewritten: the stream starts over (spec 3.4),
                    # after the watch heads of the new variable count.
                    m.d.sync += [
                        lp.eq(Cat(Const(1, 1), self.nvars[: VAR_BITS + 1])),
                        clause_start.eq(1),
                        clen2.eq(0),
                        empty_clause.eq(0),
                        bad_input.eq(0),
                    ]
                with m.Elif(self.load_valid & ~self.abort):
                    with m.If(self.load_data == 0):
                        with m.If(clause_start):
                            m.d.sync += empty_clause.eq(1)
                        with m.Else():
                            st_write(ld_waddr, ld_wdata)
                        m.d.sync += clause_start.eq(1)
                    with m.Elif(lit_mag > self.nvars):
                        m.d.sync += bad_input.eq(1)
                    with m.Elif(clause_start):
                        with m.If(lp + 3 > self.sdepth):
                            m.d.sync += bad_input.eq(1)
                        with m.Else():
                            st_write(ld_waddr, ld_wdata)
                            m.d.sync += [
                                lp.eq(lp + 3),
                                lit0.eq(ld_code),
                                clen2.eq(0),
                                last_addr.eq(lp + 2),
                                last_word.eq(ld_word),
                                clause_start.eq(0),
                            ]
                    with m.Elif(~clen2 & (ld_code == lit0)):
                        pass  # repeat of the leading literal: drop it
                    with m.Elif(lp >= self.sdepth):
                        m.d.sync += bad_input.eq(1)
                    with m.Else():
                        st_write(ld_waddr, ld_wdata)
                        m.d.sync += [
                            lp.eq(lp + 1),
                            clen2.eq(1),
                            last_addr.eq(lp),
                            last_word.eq(ld_word),
                        ]
                room0 = Signal(SADDR + 2)
                need0 = Signal(SADDR + 2)
                m.d.comb += [
                    room0.eq(self.sdepth - lp),
                    need0.eq(Cat(Const(0, 1), self.nvars[: VAR_BITS + 1]) + MIN_ROOM_EXTRA),
                ]
                with m.If(self.start & ~self.abort):
                    m.d.sync += [
                        nv.eq(self.nvars),
                        ci.eq(0),
                        tp.eq(0),
                        qhead.eq(0),
                        dl.eq(0),
                        res.eq(0),
                        info.eq(0),
                        nconf.eq(0),
                        oend.eq(lp),
                        lfree.eq(lp),
                        rt.eq(room0 >> 1),
                    ]
                    with m.If(bad_input):
                        m.d.sync += info.eq(INFO_BAD_LITERAL)
                        goto("REJECT")
                    with m.Elif(empty_clause):
                        m.d.sync += info.eq(INFO_EMPTY_CLAUSE)
                        finish(2)
                    with m.Elif(room0 < need0):
                        m.d.sync += info.eq(INFO_NO_ROOM)
                        goto("REJECT")
                    with m.Else():
                        goto("CLEAR")

            # Clear the watch heads; assign every variable false, clear its
            # seen mark and level/reason. The mark pass then unassigns the
            # variables that occur in some clause.
            with State("CLEAR"):
                with m.If(ci < Cat(Const(0, 1), nv)):
                    st_write(ci, 0)
                    with m.If(~ci[0]):
                        as_assign(ci[1:], 0)
                        sn_write(ci[1:], 0)
                        lr_write(ci[1:], Const(0, LEV_BITS), Const(0, SADDR))
                        ac_write(ci[1:], 0)
                    m.d.sync += ci.eq(ci + 1)
                with m.Else():
                    m.d.sync += [ma.eq(nv2p1), m_rv.eq(0), m_dv.eq(0), m_skip.eq(2),
                                 mw_valid.eq(0)]
                    goto("MARK")

            # Read the original clauses word by word and unassign the variable
            # of every literal word (two header words, then literals up to the
            # one with the last flag). Store data reaches asg only through mw.
            with State("MARK"):
                d = m_d  # the word read two cycles ago (registered: Timing)
                st_read(ma)
                m.d.sync += [ma.eq(ma + 1), m_rv.eq(ma < oend), m_d.eq(st_r.data),
                             m_dv.eq(m_rv), mw.eq(d), mw_valid.eq(0)]
                with m.If(m_dv):
                    with m.If(m_skip != 0):
                        m.d.sync += m_skip.eq(m_skip - 1)
                    with m.Else():
                        m.d.sync += mw_valid.eq(1)
                        with m.If(d[LAST]):
                            m.d.sync += m_skip.eq(2)
                with m.If(mw_valid):
                    as_unassign(mw[1:CODE_BITS])
                with m.If((ma >= oend) & ~m_rv & ~m_dv & ~mw_valid):
                    m.d.sync += [qv.eq(0), q_rv.eq(0), hn.eq(0)]
                    goto("QI")

            # Put the used (unassigned) variables in the decision heap, in
            # index order (all activities are 0, so that is a valid heap).
            with State("QI"):
                as_read(qv)
                m.d.sync += [qv.eq(qv + 1), q_rv.eq(qv < nv), q_var.eq(qv)]
                with m.If(q_rv & ~aa_r.data):
                    hp_write(hn, q_var)
                    ps_write(q_var, hn, 1)
                    m.d.sync += hn.eq(hn + 1)
                with m.If((qv >= nv) & ~q_rv):
                    set_h(nv2p1)
                    m.d.sync += [inl.eq(0), rebuild.eq(0), lret.eq(0)]
                    goto("I0")

            # ------------------------------------------ store scan
            # Clause by clause: originals from 2*nv+1 to oend, then learned
            # clauses (a meta word, then the clause) up to lfree.
            with State("I0"):
                with m.If(~inl & (h >= oend)):
                    m.d.sync += inl.eq(1)
                    set_h(oend + 1)
                with m.Elif(inl & (h > lfree)):
                    goto("Q0")
                with m.Else():
                    st_read(h2)
                    goto("I1")

            with State("I1"):
                m.d.sync += lit0w.eq(st_r.data)
                st_read(h3)  # unconditional: store data never steers its address
                goto("I2")

            # (Store data steers the FSM only after a register: Timing.)
            with State("I2"):
                m.d.sync += lit1w.eq(st_r.data)
                with m.If(lit0w[LAST]):
                    goto("IU0")
                with m.Else():
                    goto("LK0")

            # Unit clause: at start-up assign it at level 0; on a rebuild it
            # is assigned already (level-0 assignments are permanent).
            with State("IU0"):
                with m.If(rebuild):
                    set_h(h3)
                    goto("I0")
                with m.Else():
                    as_read(lit0w[1:CODE_BITS])
                    goto("IU1")

            with State("IU1"):
                a = as_data
                with m.If(a[1] & (a[0] == lit0w[0])):
                    m.d.sync += info.eq(INFO_UNIT_CONFLICT)
                    finish(2)
                with m.Else():
                    with m.If(~a[1]):
                        v = lit0w[1:CODE_BITS]
                        as_assign(v, ~lit0w[0])
                        tr_write(tp, v, ~lit0w[0], 0)
                        lr_write(v, Const(0, LEV_BITS), Const(0, SADDR))
                        m.d.sync += tp.eq(tp + 1)
                    set_h(h3)
                    goto("I0")

            # Skip the rest of a clause of three or more literals.
            with State("ISK"):
                # isk_last: the word at isk_addr (arrived last cycle) is last.
                st_read(sk1)
                set_sk(sk1)
                m.d.sync += [isk_last.eq(st_r.data[LAST] & ~isk_last), isk_addr.eq(sk)]
                with m.If(isk_last):
                    set_h(isk_addr1 + inl)
                    goto("I0")

            # Link clause h on the lists of lit0w (slot 0) and lit1w (slot 1),
            # two different literals. A head lives at the store address equal
            # to its literal code.
            with State("LK0"):
                st_read(lit0w[:CODE_BITS])
                with m.If(lit1w[LAST]):  # binary: flag position 0 (h + 2)
                    st_write(h2, Cat(lit0w[:CODE_BITS], Const(0b100, 3)))
                goto("LK1")

            with State("LK1"):
                m.d.sync += oldhead.eq(st_r.data)
                goto("LK2")

            with State("LK2"):
                st_write(h, oldhead)
                goto("LK3")

            with State("LK3"):
                st_write(lit0w[:CODE_BITS], Cat(h[:SADDR], Const(0, 1)))
                st_read(lit1w[:CODE_BITS])
                goto("LK4")

            with State("LK4"):
                m.d.sync += oldhead.eq(st_r.data)
                goto("LK5")

            with State("LK5"):
                st_write(h1, oldhead)
                goto("LK6")

            with State("LK6"):
                st_write(lit1w[:CODE_BITS], Cat(h1[:SADDR], Const(1, 1)))
                with m.If(lret):
                    m.d.sync += lret.eq(0)
                    goto("P0")
                with m.Elif(lit1w[LAST]):
                    set_h(h4 + inl)
                    goto("I0")
                with m.Else():
                    st_read(h4)
                    set_sk(h4)
                    m.d.sync += isk_last.eq(0)
                    goto("ISK")

            # ---------------------------------------------------- propagate
            with State("Q0"):
                tr_read(qhead)
                with m.If(qhead == tp):
                    goto("DEC")
                with m.Else():
                    goto("Q1")

            with State("Q1"):
                m.d.sync += [
                    fl.eq(Cat(tr_val, tr_var)),  # the literal made false
                    qhead.eq(qhead + 1),
                    prev_head.eq(1),
                ]
                goto("Q2")

            with State("Q2"):
                st_read(fl)  # its watch-list head
                goto("Q3")

            with State("Q3"):
                m.d.sync += nxt.eq(st_r.data)
                goto("Q4")

            with State("Q4"):
                visit(nxt)

            # The walk. Visits overlap so that a kept watch costs two cycles
            # (WX, WY): while cur's other watch is being looked up in asg, the
            # store reads for the next two entries are already issued. These
            # reads are speculative and harmless: nothing is written in
            # WB..WY, and their data is dropped if cur's watch has to move.
            with State("WB"):
                m.d.sync += nxt.eq(st_r.data)
                st_read(cur_oa)
                goto("WC")

            with State("WC"):
                m.d.sync += other.eq(st_r.data)
                st_read(nxt[:SADDR])
                m.d.sync += nxt_oa.eq(other_addr(nxt))
                goto("WX")

            with State("WX"):
                m.d.sync += nxt2.eq(st_r.data)
                as_read(other[1:CODE_BITS])
                st_read(nxt_oa)
                goto("WY")

            # If the other watch is true (wy_keep), keep this watch and go
            # on to nxt (Q0 at the end of the list); else WE. The decision
            # depends on asg data read last cycle, so its updates and
            # transitions are made after the Switch (see "Late decisions").
            with State("WY"):
                st_read(nxt2[:SADDR])
                m.d.sync += oth_asg.eq(as_data)

            # Look for a replacement watch. For slot 0 the other watch is
            # position 1, so its last flag says whether the clause is binary;
            # for slot 1, read position 1 to find out.
            with State("WE"):
                st_read(cur_h4)
                m.d.sync += [waddr.eq(cur_h4), waddr1.eq(cur_h4 + 1), c1_valid.eq(0),
                             cand_valid.eq(0)]
                # Binary: for slot 0 the other watch is position 1, whose
                # last flag says so; for slot 1 it is position 0, which
                # carries the BIN flag.
                with m.If(Mux(cur_s, other[BIN], other[LAST])):
                    goto("NOREP")
                with m.Else():
                    goto("SRCH")

            # Scan positions 2.. for a literal that is not false, one per
            # cycle, in a three-stage pipeline (store word -> asg lookup ->
            # verdict). Nothing is written.
            # The verdict on cand (F1 if it is not false and not the other
            # watch, NOREP if it is the last literal) depends on asg data read
            # last cycle: the transitions are made after the Switch (see
            # "Late decisions"). The pipeline shifts every cycle; F1.. use
            # fcand, the candidate judged in the last SRCH cycle.
            with State("SRCH"):
                as_read(c1[1:CODE_BITS])
                st_read(waddr1)
                m.d.sync += [
                    fcand.eq(cand),
                    fcand_addr.eq(cand_addr),
                    cand.eq(c1),
                    cand_addr.eq(c1_addr),
                    cand_valid.eq(c1_valid),
                    c1.eq(st_r.data),
                    c1_addr.eq(waddr),
                    c1_valid.eq(1),
                    waddr.eq(waddr1),
                    waddr1.eq(waddr1 + 1),
                ]

            # No replacement: imply the other watch, or conflict.
            with State("NOREP"):
                with m.If(oth_asg[1]):
                    goto("CONFL")  # other watch false: every literal is false
                with m.Else():
                    v = other[1:CODE_BITS]
                    as_assign(v, ~other[0])
                    tr_write(tp, v, ~other[0], 0)
                    lr_write(v, dl, cur_rsn)
                    m.d.sync += [tp.eq(tp + 1), prev.eq(cur), prev_head.eq(0)]
                    visit(nxt)

            # Replacement found at cand_addr: move the watch there. Five
            # store writes, one per cycle; the last overlaps the next visit.
            with State("F1"):
                # The false literal goes where the candidate was, keeping that
                # position's flags.
                st_write(fcand_addr, Cat(fl, fcand[LAST:]))
                st_read(fcand[:CODE_BITS])  # head of cand (!= fl: cand is not false)
                goto("F2")

            with State("F2"):
                # The watch position gets the candidate (positions 0 and 1 are
                # never last here: the clause has at least 3 literals).
                st_write(cur_own, Cat(fcand[:CODE_BITS], Const(0, 3)))
                m.d.sync += oldhead.eq(st_r.data)
                goto("F3")

            with State("F3"):
                st_write(cur[:SADDR], oldhead)
                goto("F4")

            with State("F4"):
                st_write(fcand[:CODE_BITS], cur)  # push cur on cand's list
                goto("F5")

            with State("F5"):
                # Unlink cur from fl's list. The visit reads nxt's header in
                # this cycle: nxt is neither cur nor prev and not a head.
                st_write(Mux(prev_head, fl, prev[:SADDR]), nxt)
                visit(nxt)

            # ------------------------------------------------------- decide
            with State("DEC"):
                with m.If((crst >= rlimit) | (redc >= rlim)):
                    pop_to(0, 1)  # restart (and maybe reduce)
                with m.Elif(inc_e >= RESCALE_AT):
                    m.d.sync += [sc.eq(0), sc_rv.eq(0), sc_dv.eq(0)]
                    goto("SC")
                with m.Else():
                    goto("D0")

            # Rescale every activity (and the increment) down by 2^32; small
            # ones become 0. Monotone, so the heap order stays valid.
            with State("SC"):
                ac_read(sc)
                m.d.sync += [sc.eq(sc + 1), sc_rv.eq(sc < nv), sc_var.eq(sc),
                             sc_d.eq(ac_r.data), sc_dv.eq(sc_rv), sc_var2.eq(sc_var)]
                # The activity read two cycles ago (registered: Timing).
                with m.If(sc_dv):
                    e = sc_d[ACT_MANT:]
                    ac_write(sc_var2, Mux(e > RESCALE_BY,
                                          Cat(sc_d[:ACT_MANT], e - RESCALE_BY), 0))
                with m.If((sc >= nv) & ~sc_rv & ~sc_dv):
                    m.d.sync += inc_e.eq(inc_e - RESCALE_BY)
                    goto("D0")

            # VSIDS: remove the heap top until it is unassigned; decide it.
            with State("D0"):
                hp_read(0)
                with m.If(hn == 0):
                    finish(1)  # every used variable assigned, no conflict: SAT
                with m.Else():
                    goto("D1")

            with State("D1"):
                m.d.sync += dv.eq(hp_r.data)
                hp_read(hn - 1)
                goto("D2")

            with State("D2"):
                m.d.sync += [dx.eq(hp_r.data), hn.eq(hn - 1)]
                ps_write(dv, Const(0, VAR_BITS), 0)
                as_read(dv)
                goto("D3")

            with State("D3"):
                m.d.sync += dasg.eq(as_data)
                ac_read(dx)
                goto("D3B")

            with State("D3B"):
                m.d.sync += [hx.eq(dx), hax.eq(ac_r.data), hi.eq(0)]
                with m.If(hn == 0):
                    goto("D4")
                with m.Else():
                    goto("SD0")

            with State("D4"):
                with m.If(dasg[1]):
                    goto("D0")
                with m.Elif(dl == MAX_LEVEL):
                    m.d.sync += info.eq(INFO_LEVEL_LIMIT)
                    finish(0)
                with m.Else():
                    # Decide with the saved phase (false at first).
                    as_assign(dv, dasg[0])
                    tr_write(tp, dv, dasg[0], 1)
                    lr_write(dv, dl + 1, Const(0, SADDR))
                    m.d.sync += [tp.eq(tp + 1), dl.eq(dl + 1)]
                    goto("Q0")

            # Sift hx (activity hax) down from position hi.
            with State("SD0"):
                c = Signal(VAR_BITS + 2)
                m.d.comb += c.eq(Cat(Const(1, 1), hi))  # 2 * hi + 1
                hp_read(c)
                with m.If(c >= hn):
                    goto("SDW")
                with m.Else():
                    goto("SD1")

            with State("SD1"):
                m.d.sync += hu.eq(hp_r.data)
                hp_read(Cat(Const(0, 1), hi) + 2)
                goto("SD2")

            with State("SD2"):
                m.d.sync += hu2.eq(hp_r.data)
                ac_read(hu)
                goto("SD3")

            with State("SD3"):
                m.d.sync += ha1.eq(ac_r.data)
                ac_read(hu2)
                goto("SD4")

            with State("SD4"):
                m.d.sync += ha2.eq(ac_r.data)
                goto("SD5")

            with State("SD5"):
                c1 = Cat(Const(1, 1), hi)
                two = (c1 + 1 < hn) & (ha2 > ha1)
                ch = Mux(two, hu2, hu)
                ca = Mux(two, ha2, ha1)
                ci2 = Mux(two, c1 + 1, c1)
                with m.If(ca > hax):
                    hp_write(hi, ch)
                    ps_write(ch, hi, 1)
                    m.d.sync += hi.eq(ci2)
                    goto("SD0")
                with m.Else():
                    goto("SDW")

            with State("SDW"):
                hp_write(hi, hx)
                ps_write(hx, hi, 1)
                goto("D4")

            # ----------------------------------------------------- conflict
            with State("CONFL"):
                with m.If(dl == 0):
                    finish(2)
                with m.Elif(room < tp + 8):
                    # The learned clause might not fit: drop this conflict,
                    # restart and reduce.
                    m.d.sync += need_reduce.eq(1)
                    pop_to(0, 1)
                with m.Else():
                    m.d.sync += [
                        crst.eq(crst + 1),
                        redc.eq(redc + 1),
                        nconf.eq(nconf + 1),
                        inc_k.eq(inc_k + 1),
                        inc_e.eq(inc_e + (inc_k == 15)),
                        lh.eq(lfree + 1),
                        lw.eq(lfree + 4),
                        path_c.eq(0),
                        tidx.eq(tp - 1),
                        ccl.eq(cur_rsn),
                    ]
                    goto("AC0")

            # Resolve clause ccl: mark it used (learned clauses) and read its
            # literals.
            with State("AC0"):
                with m.If(ccl > oend + 2):  # header > oend: a learned clause
                    st_write(ccl - 3, 1 << M_USED, mask=1 << M_USED)
                st_read(ccl)
                m.d.sync += [ra.eq(ccl + 1), rv.eq(1), v1.eq(0), v2.eq(0), v3.eq(0), mA.eq(0),
                             mB.eq(0)]
                goto("AC")

            # Three-stage pipeline, one literal per cycle:
            #   1. the literal word arrives from the store (next word read
            #      until the last flag);
            #   2. its seen mark and level are read;
            #   3. verdict: a literal not seen and not at level 0 is marked;
            #      at the current level it is counted, below it is appended to
            #      the learned clause.
            # (Stage 3 only registers the read data, for timing; the verdict
            # is in stage 4, with a bypass for the marks of the two previous
            # verdicts.)
            with State("AC"):
                st_read(ra)  # speculative past the last literal: harmless
                # Stage 1: the literal word arrives.
                with m.If(rv):
                    d = st_r.data
                    m.d.sync += [w1.eq(d), v1.eq(1)]
                    with m.If(~d[LAST]):
                        m.d.sync += [ra.eq(ra + 1), rv.eq(1)]
                    with m.Else():
                        m.d.sync += rv.eq(0)
                with m.Else():
                    m.d.sync += v1.eq(0)
                # Stage 2: read its seen mark and level.
                with m.If(v1):
                    sn_read(w1[1:CODE_BITS])
                    lr_read(w1[1:CODE_BITS])
                m.d.sync += [w2.eq(w1), v2.eq(v1)]
                # Stage 3: register them (timing).
                m.d.sync += [w3.eq(w2), v3.eq(v2), s3.eq(sn_r.data),
                             l3nz.eq(lr_level != 0), l3cur.eq(lr_level == dl)]
                # Stage 4: verdict. The marks written in the last two cycles
                # were not visible to this literal's read: bypass them.
                w3v = w3[1:CODE_BITS]
                mark = Signal()
                is_seen = s3 | (mA & (vA == w3v)) | (mB & (vB == w3v))
                with m.If(v3 & ~is_seen & l3nz):
                    m.d.comb += mark.eq(1)
                    sn_write(w3v, 1)
                    with m.If(l3cur):
                        m.d.sync += path_c.eq(path_c + 1)
                    with m.Else():
                        st_write(lw, w3[:CODE_BITS])
                        m.d.sync += lw.eq(lw + 1)
                m.d.sync += [vA.eq(w3v), mA.eq(mark), vB.eq(vA), mB.eq(mA)]

                with m.If(~rv & ~v1 & ~v2 & ~v3):
                    goto("AT0")

            # Walk the trail backwards to the next marked variable.
            with State("AT0"):
                tr_read(tidx)
                goto("AT1")

            with State("AT1"):
                m.d.sync += te.eq(tr_r.data)
                goto("AT2")

            with State("AT2"):
                sn_read(te[:VAR_BITS])
                lr_read(te[:VAR_BITS])
                goto("AT3")

            with State("AT3"):
                m.d.sync += tidx.eq(tidx - 1)
                with m.If(sn_r.data):
                    with m.If(path_c == 1):
                        m.d.sync += mna.eq(lh + 3)
                        goto("MN0")  # te is the first UIP
                    with m.Else():
                        m.d.sync += [path_c.eq(path_c - 1), ccl.eq(lr_reason)]
                        goto("AC0")
                with m.Else():
                    goto("AT0")

            # Minimization (MiniSat's basic mode): a lower-level literal whose
            # reason has only marked literals (or level-0 ones) is implied by
            # the rest of the clause; flag it (bit 16) for removal. Marks are
            # not changed here, so flagged literals still count as marked.
            with State("MN0"):
                with m.If(mna == lw):
                    m.d.sync += [la.eq(lh + 3), wp.eq(lh + 3), maxlev.eq(0),
                                 minlev.eq(MAX_LEVEL)]
                    goto("LB0")
                with m.Else():
                    st_read(mna)
                    goto("MN1")

            with State("MN1"):
                m.d.sync += mnw.eq(st_r.data)
                goto("MN2")

            with State("MN2"):
                lr_read(mnw[1:CODE_BITS])
                goto("MN3")

            with State("MN3"):
                m.d.sync += ccl.eq(lr_reason)
                goto("MN3B")

            with State("MN3B"):
                with m.If(ccl == 0):
                    m.d.sync += mna.eq(mna + 1)  # a decision: keep
                    goto("MN0")
                with m.Else():
                    goto("MN4")

            with State("MN4"):
                st_read(ccl)
                m.d.sync += [ra.eq(ccl + 1), rv.eq(1), v1.eq(0), v2.eq(0), v3.eq(0), mfail.eq(0)]
                goto("MN5")

            # Same pipeline as AC, without writes; stops at the first literal
            # that is neither marked nor at level 0.
            with State("MN5"):
                st_read(ra)
                with m.If(rv):
                    d = st_r.data
                    m.d.sync += [w1.eq(d), v1.eq(1)]
                    with m.If(~d[LAST]):
                        m.d.sync += [ra.eq(ra + 1), rv.eq(1)]
                    with m.Else():
                        m.d.sync += rv.eq(0)
                with m.Else():
                    m.d.sync += v1.eq(0)
                with m.If(v1):
                    sn_read(w1[1:CODE_BITS])
                    lr_read(w1[1:CODE_BITS])
                # Stage 3 registers the seen mark and level test (Timing),
                # stage 4 judges.
                m.d.sync += [v2.eq(v1), v3.eq(v2), s3.eq(sn_r.data), l3nz.eq(lr_level != 0)]
                with m.If(v3 & ~s3 & l3nz):
                    m.d.sync += mfail.eq(1)
                with m.If(mfail | (~rv & ~v1 & ~v2 & ~v3)):
                    goto("MN6")

            with State("MN6"):
                with m.If(~mfail):
                    st_write(mna, mnw | (1 << RMV))
                m.d.sync += mna.eq(mna + 1)
                goto("MN0")

            # Pass over the lower-level literals: clear every mark and bump
            # every variable (removed literals too), compact the kept
            # literals to lh+3 .. wp-1, and find the highest and lowest
            # levels among them.
            with State("LB0"):
                with m.If(la == lw):
                    m.d.sync += lw.eq(wp)
                    goto("AU0")
                with m.Else():
                    st_read(la)
                    goto("LB1")

            with State("LB1"):
                m.d.sync += [lbw.eq(st_r.data), la.eq(la + 1)]
                goto("LB2")

            with State("LB2"):
                lr_read(lbw[1:CODE_BITS])
                goto("LB3")

            with State("LB3"):
                m.d.sync += lblev.eq(lr_level)
                goto("LB4")

            with State("LB4"):
                code = lbw[:CODE_BITS]
                with m.If(~lbw[RMV]):
                    st_write(wp, code)
                    m.d.sync += [wp.eq(wp + 1), lastlit.eq(code)]
                    with m.If(wp == lh + 3):
                        m.d.sync += firstlit.eq(code)
                    with m.If(lblev > maxlev):
                        m.d.sync += [maxlev.eq(lblev), maxaddr.eq(wp), maxlit.eq(code)]
                    with m.If(lblev < minlev):
                        m.d.sync += minlev.eq(lblev)
                m.d.sync += [bv.eq(lbw[1:CODE_BITS]), bret.eq(0)]
                goto("BM0")

            # The learned clause: UIP at position 0 (as the false literal),
            # the lower-level literals at lh+3 .. lw-1. Swap the literal of
            # the highest level into position 1 and flag the last word.
            with State("AU0"):
                st_write(lh + 2, Cat(te[VAR_BITS], te[:VAR_BITS], Const(0, 2), lw == lh + 4))
                with m.If(lw == lh + 3):
                    # Unit clause: assert at level 0, not stored.
                    m.d.sync += [bjl.eq(0), ureason.eq(0), bjk.eq(0)]
                    goto("P0")
                with m.Else():
                    goto("AU1")

            with State("AU1"):
                st_write(lh + 3, Cat(maxlit, lw - 1 == lh + 3))
                goto("AU2")

            with State("AU2"):
                with m.If(maxaddr != lh + 3):
                    st_write(maxaddr, Cat(firstlit, maxaddr == lw - 1))
                goto("AU3")

            with State("AU3"):
                with m.If((lw - 1 != lh + 3) & (lw - 1 != maxaddr)):
                    st_write(lw - 1, Cat(lastlit, Const(1, 1)))
                goto("AU4")

            with State("AU4"):
                set_h(lh)
                # Meta word: glue if every lower-level literal has one level.
                st_write(lh - 1, Cat(minlev == maxlev, Const(1, 1)))
                m.d.sync += [
                    lit0w.eq(Cat(te[VAR_BITS], te[:VAR_BITS])),
                    lit1w.eq(maxlit),
                    lret.eq(1),
                    lfree.eq(lw),
                    bjl.eq(maxlev),
                    ureason.eq(lh + 2),
                    bjk.eq(0),
                ]
                goto("LK0")

            # Bump bv: clear its seen mark and add the increment to its
            # activity. In the heap: sift it up. Not in the heap and being
            # unassigned (pop loop): insert it.
            with State("BM0"):
                sn_write(bv, 0)
                ac_read(bv)
                ps_read(bv)
                goto("BM1")

            with State("BM1"):
                m.d.sync += [hax.eq(ac_r.data), hi.eq(ps_idx), hp.eq(ps_in)]
                goto("BM2")

            with State("BM2"):
                na = Signal(ACT_BITS)
                m.d.comb += na.eq(fadd(hax, inc))
                ac_write(bv, na)
                m.d.sync += [hax.eq(na), hx.eq(bv), hret.eq(bret)]
                with m.If(hp[0]):  # in the heap
                    goto("UP0")
                with m.Elif(bret):  # unassigned now: insert at the end
                    m.d.sync += [hi.eq(hn), hn.eq(hn + 1)]
                    goto("UP0")
                with m.Else():
                    goto("LB0")

            # Sift hx (activity hax) up from position hi.
            with State("UP0"):
                pp = Signal(VAR_BITS + 1)
                m.d.comb += pp.eq((hi - 1) >> 1)
                hp_read(pp)
                m.d.sync += hp.eq(pp)
                with m.If(hi == 0):
                    goto("UPW")
                with m.Else():
                    goto("UP1")

            with State("UP1"):
                m.d.sync += hu.eq(hp_r.data)
                goto("UP2")

            with State("UP2"):
                ac_read(hu)
                goto("UP3")

            with State("UP3"):
                m.d.sync += ha1.eq(ac_r.data)
                goto("UP4")

            with State("UP4"):
                with m.If(ha1 < hax):
                    hp_write(hi, hu)
                    ps_write(hu, hi, 1)
                    m.d.sync += hi.eq(hp)
                    goto("UP0")
                with m.Else():
                    goto("UPW")

            with State("UPW"):
                hp_write(hi, hx)
                ps_write(hx, hi, 1)
                with m.If(hret):
                    goto("P0")
                with m.Else():
                    goto("LB0")

            # ------------------------------------------- backjump / restart
            # Pop the trail down to level bjl, unassigning (the value stays as
            # the saved phase); marked variables are bumped and unmarked.
            with State("P0"):
                with m.If(dl == bjl):
                    with m.If(bjk):
                        goto("RS1")
                    with m.Else():
                        goto("ASSERT")
                with m.Else():
                    tr_read(tp - 1)
                    goto("P1")

            with State("P1"):
                as_unassign(tr_var)
                m.d.sync += [pe.eq(tr_r.data), tp.eq(tp - 1)]
                with m.If(tr_dec):
                    m.d.sync += dl.eq(dl - 1)
                goto("P2")

            with State("P2"):
                sn_read(pe[:VAR_BITS])
                ps_read(pe[:VAR_BITS])
                ac_read(pe[:VAR_BITS])
                goto("P3")

            # A marked variable is bumped (and inserted if needed); an
            # unmarked one is inserted if it is not in the heap.
            with State("P3"):
                m.d.sync += [hx.eq(pe[:VAR_BITS]), hax.eq(ac_r.data), hret.eq(1),
                             p_sn.eq(sn_r.data), p_in.eq(ps_in)]
                goto("P4")

            with State("P4"):
                with m.If(p_sn):
                    m.d.sync += [bv.eq(pe[:VAR_BITS]), bret.eq(1)]
                    goto("BM0")
                with m.Elif(~p_in):
                    m.d.sync += [hi.eq(hn), hn.eq(hn + 1)]
                    goto("UP0")
                with m.Else():
                    goto("P0")

            # Assert the UIP literal (the negation of its old value).
            with State("ASSERT"):
                v = te[:VAR_BITS]
                val = ~te[VAR_BITS]
                as_assign(v, val)
                tr_write(tp, v, val, 0)
                lr_write(v, bjl, ureason)
                m.d.sync += [qhead.eq(tp), tp.eq(tp + 1)]
                goto("Q0")

            # After a restart: next Luby limit; reduce if due.
            with State("RS1"):
                lowbit = Signal(24)
                m.d.comb += lowbit.eq(lu & (~lu + 1))
                with m.If(lowbit == lv):
                    m.d.sync += [lu.eq(lu + 1), lv.eq(1)]
                with m.Else():
                    m.d.sync += lv.eq(lv << 1)
                m.d.sync += [crst.eq(0), qhead.eq(tp)]
                with m.If(need_reduce | (redc >= rlim)):
                    m.d.sync += [
                        need_reduce.eq(0),
                        redc.eq(0),
                        rlim.eq(rlim + self.reduce_inc),
                        rmode.eq(0),
                    ]
                    goto("RD0")
                with m.Else():
                    goto("Q0")

            # ------------------------------------------------------ reduce
            # Compact the learned area in place, one word per cycle: read at
            # rr, write the kept words at rw <= rr - 1.
            with State("RD0"):
                m.d.sync += [rr.eq(oend), rw.eq(oend), rpos.eq(0), r_rv.eq(0), r_dv.eq(0),
                             r_wp.eq(0)]
                goto("RD1")

            with State("RD1"):
                st_read(rr)
                with m.If(rr < lfree):
                    m.d.sync += [rr.eq(rr + 1), r_rv.eq(1)]
                with m.Else():
                    m.d.sync += r_rv.eq(0)
                # Stage 2: the word read last cycle arrives; register it.
                m.d.sync += [r_d.eq(st_r.data), r_dv.eq(r_rv)]
                # Stage 3: decide whether the clause is kept (at its meta
                # word) and register the copy.
                d = r_d
                m.d.sync += [r_wp.eq(0), r_wd.eq(d)]
                with m.If(r_dv):
                    with m.If(rpos == 0):
                        keep = Signal()
                        m.d.comb += keep.eq(
                            Mux(rmode == 0, d[M_GLUE] | d[M_USED], (rmode == 1) & d[M_GLUE])
                        )
                        m.d.sync += [rkeep.eq(keep), rpos.eq(1), r_wp.eq(keep),
                                     r_wd.eq(Cat(d[M_GLUE], Const(0, 1)))]
                    with m.Else():
                        m.d.sync += r_wp.eq(rkeep)
                        with m.If(rpos != 3):
                            m.d.sync += rpos.eq(rpos + 1)
                        with m.Elif(d[LAST]):
                            m.d.sync += rpos.eq(0)
                # Stage 4: write the kept word (rw <= rr - 3: never a word
                # still to be read).
                with m.If(r_wp):
                    st_write(rw, r_wd)
                    m.d.sync += rw.eq(rw + 1)
                with m.If(~r_rv & ~r_dv & ~r_wp & (rr >= lfree)):
                    goto("RD2")

            with State("RD2"):
                m.d.sync += lfree.eq(rw)
                with m.If((self.sdepth - rw < rt) & (rmode != 2)):
                    m.d.sync += rmode.eq(rmode + 1)
                    goto("RD0")
                with m.Else():
                    m.d.sync += ci.eq(0)
                    goto("RCLR")

            # Rebuild every watch list from scratch.
            with State("RCLR"):
                with m.If(ci < Cat(Const(0, 1), nv)):
                    st_write(ci, 0)
                    m.d.sync += ci.eq(ci + 1)
                with m.Else():
                    set_h(nv2p1)
                    m.d.sync += [inl.eq(0), rebuild.eq(1), lret.eq(0)]
                    goto("I0")

            with State("DONE"):
                m.d.comb += [self.done.eq(1), self.model_val.eq(av_r.data)]
                as_read(self.model_addr[:VAR_BITS])

            with State("REJECT"):
                m.d.comb += self.rejected.eq(1)

        # Late decisions (Timing). These depend on asg data that arrives in
        # this cycle; written after the Switch, they override it, so the
        # decision enters the last multiplexer level of each register and
        # state bit instead of going through the whole Switch.
        def oh_move(src, dst):
            m.d.comb += [oh_next[sidx(src)].eq(0), oh_next[sidx(dst)].eq(1)]

        in_wy = fsm_oh[sidx("WY")]
        wy_keep = Signal()
        m.d.comb += wy_keep.eq(in_wy & as_data[1] & (as_data[0] != other[0]))
        with m.If(wy_keep):
            m.d.sync += [
                prev.eq(cur),
                prev_head.eq(0),
                nxt.eq(nxt2),
                nxt_oa.eq(other_addr(nxt2)),
                other.eq(st_r.data),
            ]
            set_cur(nxt)
            with m.If(nxt[:SADDR] == 0):
                oh_move("WY", "Q0")
            with m.Else():
                oh_move("WY", "WX")
        with m.Elif(in_wy):
            oh_move("WY", "WE")

        in_srch = fsm_oh[sidx("SRCH")]
        cand_false = as_data[1] & (as_data[0] == cand[0])
        with m.If(in_srch & cand_valid):
            with m.If(~cand_false & (cand[:CODE_BITS] != other[:CODE_BITS])):
                oh_move("SRCH", "F1")
            with m.Elif(cand[LAST]):
                oh_move("SRCH", "NOREP")

        terms = []
        seen_states = [n for _, states in st_reads.values() for n in states]
        assert len(seen_states) == len(set(seen_states)), "two store reads in one state"
        for addr, states in st_reads.values():
            sel = 0
            for name in states:
                sel = sel | fsm_oh[state_index[name]]
            terms.append(Mux(sel, addr, 0))
        acc = terms[0]
        for t in terms[1:]:
            acc = acc | t
        m.d.comb += st_r.addr.eq(acc)
        seen_states = [n for _, _, states in st_writes.values() for n in states]
        assert len(seen_states) == len(set(seen_states)), "two store writes in one state"
        wa = wd = 0
        for addr, data, states in st_writes.values():
            sel = 0
            for name in states:
                sel = sel | fsm_oh[state_index[name]]
            wa = wa | Mux(sel, addr, 0)
            wd = wd | Mux(sel, data, 0)
        m.d.comb += [st_w.addr.eq(wa), st_w.data.eq(wd)]
        # For tests: the state as a number (simulation only; unused, so
        # synthesis removes it) and its encoding, like an Amaranth FSM's.
        dbg_state = Signal(range(NSTATES))
        enc = 0
        for k in state_index.values():
            enc = enc | Mux(fsm_oh[k], k, 0)
        m.d.comb += dbg_state.eq(enc)

        class _FsmDebug:
            state = dbg_state
            encoding = dict(state_index)

        self.dbg["fsm"] = _FsmDebug

        # ABORT resets every register of the solver (the FSM returns to IDLE,
        # the load pointer to 1) in the cycle after it rises. Memory contents
        # are not reset; the solve state in them is rebuilt at the next START,
        # and the clause memory is overwritten by the next load.
        top = Module()
        top.submodules.core = ResetInserter(self.abort)(m)
        return top
