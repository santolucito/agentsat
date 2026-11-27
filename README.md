# Watched-literal DPLL: an AgentSAT entry

A correct SAT solver for the Lattice ECP5-85F, built from the
[AgentSAT entry template](https://github.com/ManhattanReasoning/agentsat-template).

- **Algorithm:** DPLL with chronological backtracking and MiniSat-style two-watched-literal
  unit propagation. The watch lists are linked lists threaded through the clause headers in
  block RAM, and the trail doubles as the propagation queue. Decisions take the lowest
  unassigned variable (through a monotone pointer) with a saved phase, false at first. See the
  notes at the top of `solver.py`.
- **Capacity:** 16,384 variables, 16,384 clauses, 65,535 literals. Any instance within all
  three limits fits the clause store (1 + 2 x clauses + literals <= 98,304 words).
- **Clock:** 50 MHz. An out-of-context nextpnr run reaches about 58 MHz. It uses 163 DP16KD
  (of the 183 available), about 2.8k LUTs and 900 FFs. Variables that appear in no clause are fixed to
  false and never decided.
- **Tests:** `pip install amaranth==0.5.8 pytest && pytest`. Random CNFs are checked against
  brute force through the full Wishbone shell, along with watched-literal edge cases
  (duplicate literals, tautologies, units, width-200 clauses, implication chains,
  pigeonhole) and abort and re-solve.

DPLL without clause learning is still weak on hard instances.

---

# AgentSAT entry template (Amaranth)

A starting point for an entry to AgentSAT, the Field Programmable Satisfiability Competition: a SAT solver that runs entirely in the fabric of a Lattice ECP5-85F. This template gives you the interface the competition runner expects. You write the solver.

It is a skeleton, not a working entry. As shipped, the solver gives up on every instance, and it declares a capacity of zero, so the runner skips every non-empty instance. Nothing you submit unchanged will score.

## What is here

| File | What it is | Edit? |
|---|---|---|
| `solver.py` | Your solver. The interface it must follow is described at the top of the file. | **Yes** |
| `design.py` | The competition register map (version 1), connected to `solver.py`. | No |
| `info.yaml` | Describes your entry: language, clock, source files, method disclosure. | **Yes** |
| `tests/` | Smoke tests for the register map and the solver interface. | Add your own |

You may add more source files. Import them from `solver.py` and list them under `sourcefiles` in `info.yaml`.

## Quick start

```sh
pip install amaranth pytest      # tested with Amaranth 0.5.8
pytest                           # runs the register-map smoke tests
```

Then:

1. Fill in `info.yaml`: your title, author, clock, and the method disclosure.
2. Implement `Solver` in `solver.py`. Read the interface notes at the top of that file.
3. Set `max_vars`, `max_clauses` and `max_lits` in `Solver` to the largest instance you can hold. The runner skips anything larger and counts it as unsolved. Do not declare more than you can hold, because a wrong answer is worse than a skip.
4. Test your solver. Add your own tests next to `tests/test_register_map.py`. The `FakeSolver` there shows how to drive the shell.

## How the pieces fit

The runner talks to your design through a fixed register map: it writes the instance size, streams the clauses in, writes `START`, and polls `STATUS` until your design reports SAT, UNSAT, or the time limit passes. It reads any satisfying assignment back one literal at a time, and checks it against the original clauses. `design.py` handles all of that. Your `Solver` sees a small interface instead: a start pulse, the instance size, a stream of clause words, and an abort level. It gives back done, rejected, a result, and the model one variable at a time.

The full register map, including `abort`, is in [`docs/register_map_v1.md`](docs/register_map_v1.md). The rules are on the competition site's Rules page, and the platform docs are at https://docs.manhattanreasoning.com.

## Things to know

- **Abort must work.** The runner aborts a solve when the time limit passes. While `abort` is high you must drop all instance state, and then raise `idle`. The next instance must solve exactly as it would on a freshly programmed board.
- **One bitstream solves every instance.** There is no reconfiguration between instances.
- **Your clock.** `clock_hz` in `info.yaml` is the frequency of the `sync` domain. The SoC generates it with a PLL. The PLL can land up to about 1% from your request, and time is measured on the clock that results.
- **Memory initialization files are not supported in v1.** Do not read data files at build time (for example Verilog `$readmemh`). Put initial values in the source, for example `Memory(init=[...])`.
- **Resources.** An entry has 78,292 LUTs, 80,922 FFs, 183 block RAMs, 152 DSPs and 3 PLLs left after the SoC. The register-map shell in `design.py` uses roughly 70 LUTs and 100 FFs.
- **Only one top module.** The platform finds your design as the one class in `design.py` that has the Wishbone signals. Keep `Entry` as the only such class in that file.
- **Build time limit.** A build must finish within 60 minutes.

## Before you submit

1. Run `pytest` and your own tests.
2. Fill in the method disclosure in `info.yaml`. It is required.
3. Push your solver to your team's registered, public GitHub repository, with `info.yaml` at its root.
4. Submit by pushing a tag that starts with `submission-`:

   ```sh
   git tag submission-1
   git push origin submission-1
   ```

   We build the exact commit the tag points to. A tag is read once, so moving it later does nothing; push a new tag instead. Your team gets one entry per UTC day.
5. We then run a pre-flight check in the evaluation image: build, timing, fit, register-map conformance, abort and correct answers.

Your repository must be public at submission, and your results and bitstream are published.

## Methods Award

If your entry was built with AI assistance, you may also submit a methods paper of at most 10 pages. List it under `methods_paper` in `info.yaml`. The paper must accompany a valid final entry. See the rules for the rubric.

## Benchmark harness (`sim/`)

`python sim/run_bench.py --cnf-dir DIR --answers manifest.csv --max-cycles N` exports the solver to
Verilog, builds a Verilator model, and runs each CNF with a cycle cap. It checks every SAT model and,
with the public manifest, every answer against the known result. It needs yosys and verilator on PATH.
