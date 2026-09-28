# Tables: atoms, instantiation rows, the template table

This note records the Plonky3 tables beyond the corpus's three: atoms,
and supercombinator instantiation. Both are built. Instantiation follows
`avon/DESIGN.md` §18.1 (in the `skijack` repository), with a public
roots table in place of a jet cell, and globals.

## 1. Atoms (built)

Atoms are the markers that bind an output (`Air.air_probe`), and the
Sudoku proof uses them (`src/sudoku.rs`).

- **The cell.** Tag 6 on the `mem` bus, `(addr, 6, n, 0)` for the atom `n`.
  Rust `Cell::Atom(n)`, Lean `Cell.atom n`, `X n` in table files.
- **The halting kind `HA`.** The row reads its head cell with tag 6 and
  repeats, as `Air.haltRow` accepts an atom outright. It reads no stack
  cell.
- **The output check.** When the AIR names an accepting marker
  (`CpuAir.accept`), the last row must be `HA` with first field `acc`. The
  read is range-checked below the counter like any other, so it is
  `rd M ctr hd = some (.atom acc)`, the hypothesis of `Air.air_probe` and
  `Stmt.stmt_sound`.
- **The witness table.** Each row commits one bit `b` and looks up
  `(addr, 3 − 2b, 0, 1 − b)`: `K` or `A 0 1` at a preprocessed address.
  The program table carries the public cells with their addresses. The two
  tables together pin the memory prefix to `Stmt.stmtMachine ρ`.

- **Blinding.** Plonky3 publishes each table's LogUp terminal in the
  clear. Two messages on buses of their own, each a fresh uniform 4-tuple,
  go from the witness table to the CPU and from the CPU to memory, so the
  private terminals are uniform subject to their public sum
  (`src/sudoku.rs`, *Blinding*).

A statement over other data needs its own witness table (one row per
private cell, with the cell's allowed shapes as constraints), its own
soundness theorem in the style of `Sudoku.sudoku_sound`, a statement check
like `lake exe sudoku statement`, and the same blinding.

## 2. Supercombinator instantiation (built)

Instantiation rows are built and checked against Lean. `src/jets.rs`
proves every corpus row jetted, and `lake exe jets check` accepts each
table (`Air.checkJA_sound`). This section records what was built, and
where it departs from the plan.

### What was measured first

`lake exe jetcost` runs each corpus term plain, and then jetted at every
licensed root. It counts the rows of these tables: one CPU row per
transition or instantiation, one POP row per argument, and one INSTW row
per written cell. These are transitions; the Plonky3 table below counts
states, one more. The last column counts the cells the jetted run writes,
against the plain run's; the loaded heap is the same in both and is not
counted.

| row | plain | whole bodies | globals | cells written (globals) |
|---|---|---|---|---|
| compiled_up | 1,206 | 2,699 (224%) | 340 (28%) | 14% |
| compiled_uq | 1,077 | 2,665 (247%) | 342 (32%) | 17% |
| compiled_ur | 1,296 | 3,561 (275%) | 389 (30%) | 16% |
| interpreted_up | 4,908 | 5,778 (118%) | 5,517 (112%) | 85% |
| sumto_us | 25,073 | 149,611 (597%) | 8,477 (34%) | 17% |

Two findings changed the plan:

- **Instantiation must name closed subterms as globals.** A compiled
  body inlines whole closed words. `instStep` as first proved writes
  every cell of the body, so on the compiled rows and `3 sumto` it costs
  2.2–6.0× the plain run. It also writes
  fresh copies of nested templates, whose roots are then never roots.
- **η-templates must never be roots.** `λ xs. G xs`, with `G` closed,
  compiles to `G` itself. Instantiating it rewrites `G xs` to `G xs`,
  and a jetted run loops. That is sound, as zero steps of weak
  reduction, but useless.

On the interpreted rows jets do not pay. They have about 2,000
licensed roots and instantiate 671 to 836 times, but each instantiation
there is short, and the POP rows it adds outnumber the CPU rows it
saves: 110–112% of the plain rows with globals, 114–118% with whole
bodies. The savings above are for the compiled rows and `3 sumto`.

### What the circuit proves

- **Instantiation with globals** (`Mach.instStepG`). Pop `|xs|` argument
  pointers, then write the body's cells at the counter in `ibuild` order.
  A formal becomes its argument's pointer. Any other variable becomes a
  public address, `genv x`.
- **Its licence** (`Mach.inst_sound_g`). If each global's address holds
  its meaning `γ x`, and the head holds `(absN xs body).close γ`, the
  state after reads back as a weak reduct of the state before. This is
  `absN_beta_close` with that `γ`.
- **The jetted step** (`Mach.JStep.inst`) takes such a template. The
  closed case, all variables formals, is `JStep.ofTemplate`.

### The public jet table

`JetTable.jetTable` computes the jet table from the compiler's own
templates, and `lake exe jets emit` writes it:

- **The templates:** each equation's `compDef` or `compRec`, each lifted λ
  chain (`wrapLift`), and each constructor (`ctorO`).
- **The globals:** each maximal closed subterm of a body, leaves
  included, becomes a variable pointing to a loaded cell that holds it.
- **The roots:** hash-consing the loaded heap finds each root. Each is
  kept only if `Air.rootOKB` licenses it: `termAtG` must read the jet's
  compiled form, with its globals read at their addresses.

Nothing in `JetTable` is trusted. The Lean checker recomputes the table
from the term and runs `rootsOKB`, and the template rows are `icells`
resolved (`JetTable.symCells_icells`). The Plonky3 verifier builds its
preprocessed tables from the jet files, so it first runs `lake exe jets
statement` itself, with its own corpus. For each term it will prove, the
file it will read must be exactly Lean's jet file for that term, and its
roots must pass `Air.rootsOKB` over the term's loaded heap, which gives
`Air.RootsOK`. The check is keyed by the verifier's terms, not by file
names. Unchecked, a file listing an extra root lets a forged proof
verify, and so does a made-up file for a term outside Lean's corpus;
the `doctored_jets` and `made_up_jets` tests show the check refusing
both.

This needs no jet cell, unlike Avon's `J g`. A root is an address, and
`termAt` below the first counter never changes (`Air.termAt_take`), so
`JStep.inst`'s head hypothesis holds at a root on every row. `S` copies
pointers, not cells, so a copy of a root is the root.

### The AIR, in Lean (`Ski/AirJet.lean`)

- **`instRow M J r`:**
  - pop the arguments through reads below the counter (`popR`, which is
    `popN`: `popR_popN`);
  - compute the body's cells from the counter (`icells`, which is what
    `ibuild` writes: `ibuild_icells`);
  - check the writes (`wrs`);
  - the next row is the root, the rest, and the counter past the
    writes.
- **`instRow_jstep`:** a passing row at a licensed root is a jetted
  step.
- **`AcceptsJ`:** the AIR where a row steps, instantiates at a listed
  root, or halts and repeats.
- **`air_sound_jet`:** from a loaded term with licensed roots, an
  accepted table ends on a value `v`. The term evaluates in normal order
  to a value that weakly reduces to `v` and has `v`'s head and arity.
- **`checkJA`:** decides these constraints on a table over an array, and
  checks the roots. `checkJA_sound` is proved; completeness is not.

### The tables (`src/jets.rs`)

- **ROOTS** `(addr, g)`, **HDR** `(g, k, n, root)`, **TMPL** `(g, j, tag,
  operand a, operand b)`: preprocessed from the jet file, each providing
  its rows with a committed multiplicity.
  - An operand is three flags (local, argument, global) and a value.
  - Padding rows copy a real row, so a multiplicity on padding provides
    only a genuine tuple.
- **POP** `(clk, c, i, s, x, s', uses)`. It reads `C x s'` at `s`,
  range-checked below `c`. It receives chain step `POPCH(clk, c, i, s)`
  and sends `POPCH(clk, c, i + 1, s')`. It provides `ARG(clk, i, x)` as
  often as the body and root use it; an inactive row's use count is
  forced to zero.
- **INSTW** `(clk, c, g, j, template row, a, b, argument pointers)`. It
  looks up `TMPL(g, j, …)` and resolves each operand: `c + j'` for a
  local, an `ARG` lookup for an argument, the value for a global. It
  writes `(c + j, tag, a, b)` to memory. It receives `WCH(clk, c, g, j)`
  and sends `WCH(…, j + 1)`. Flags are zero on inactive rows.
- **CPU, kind `INST`:**
  - looks up `ROOTS(hd, g)` and `HDR(g, k, n, root)`;
  - sends `POPCH(clk, ctr, 0, stk)` and receives `POPCH(clk, ctr, k, rest)`;
  - sends `WCH(clk, ctr, g, 0)` and receives `WCH(clk, ctr, g, n)`;
  - sets `hd' = root`, `stk' = rest` and `ctr' = ctr + n`;
  - reads no cell itself.

`clk` is a row counter: 0 on the first row, one more each row. The plan
keyed the chains by the counter `c`. Two instantiations that write no
cells share a counter, so the chains now carry `clk`, which is unique per
row.

### Measured, 2026-09-27, Apple M4 Max, release build

```
row             plain  jetted  insts  budget   pop  instw  prove s  verify s
compiled_up      1207     144     37     256   128    128     0.05     0.015
compiled_uq      1078     151     37     256   128    128     0.02     0.012
compiled_ur      1297     168     41     256   128    128     0.04     0.014
interpreted_up   4909    3995    676    4096  2048     64     0.14     0.019
interpreted_uq   4949    3976    671    4096  2048    128     0.16     0.019
interpreted_ur   6308    5004    836    8192  2048    128     0.18     0.021
sumto_us        25074    3678    939    4096  4096   4096     0.15     0.021
```

`plain` and `jetted` count states, one CPU row each; `budget` is the CPU
table's height. `3 sumto` proves in about 0.15 s jetted, against about
0.5 s plain.
`lake exe jets check` accepts all seven tables. It rejects the two
tampered ones, which the verifier also rejects, and the statement check
refuses two made-up jet files before any proof:

- `forged_write`: one instantiated cell's argument operand is changed,
  in the trace and in memory.
- `unlicensed_root`: jet 0 is instantiated once at an address that is
  not its root.
- `doctored_jets`: `3 sumto`'s jet file with an extra root.
- `made_up_jets`: a jet file for `K S K`, a term outside Lean's corpus,
  claiming `K x ↦ I` at the address of `K` (the audit's counterexample,
  which verified before the check was keyed by terms).

### Not yet built

- **Jets with probes.** `inst_sound` over open terms, so a jetted run from
  a statement machine binds its output as `air_probe` does. Until then
  jets and the Sudoku statement do not combine.
- **Zero knowledge for jets.** ROOTS, HDR and TMPL are public and would
  go under the public-seed commitment of `src/sudoku.rs`. POP and INSTW
  would need fixed heights and blinding messages, since each has its own
  published terminal. The jetted corpus proofs are not hiding.
- **A choice of when to jet.** The runs instantiate at every root. On
  the interpreted rows that saves CPU rows, but adds more POP rows than it
  saves.
- **Data jets and the interpreter jet** (Avon §18.2, §18.3).
