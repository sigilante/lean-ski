# Tables: atoms, instantiation rows, the template table

This note records the plan for the Plonky3 tables beyond the corpus's
three. The first part, atoms, is built. The second part, supercombinator
instantiation, is planned and not yet built. It follows
`avon/DESIGN.md` §18.1 (in the `skijack` repository), with one change
explained under *The head*.

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

## 2. Supercombinator instantiation (planned)

### What the circuit proves

`Mach.JStep` has two kinds of step: a machine transition, and
`inst g`, an instantiation of a licensed template `g = (xs, body)` whose
compiled form `absN xs body` is at the head:

```
JStep.inst : termAt m.heap _ m.hd = some (toTerm (absN g.xs g.body))
           → instStep g.xs g.body m = some m' → JStep m m'
```

`instStep` pops `|xs|` argument pointers off the stack (`popN`), then
writes the body's cells at the counter in `ibuild` order (children first,
function before argument, one cell per `S`, `K`, `I` leaf and per
application, no cell for a variable). Each variable becomes its argument's
pointer. A jetted run that halts on a weak head normal form proves
normal-order evaluation up to weak reduction of the value
(`Mach.jet_run_eval`). The value's head and arity are those of the
unjetted run's value (`jet_run_shape`). The circuit must enforce exactly
`instStep`, at a head that satisfies the first hypothesis.

### The head: a public roots table, not a jet cell

`avon/DESIGN.md` §18.1 places a jet cell `J g` at the head. That needs a
new cell kind and a change to `decode`. The plan here needs neither. It
uses the first hypothesis of `JStep.inst` as it stands:

- **ROOTS** (preprocessed, public): rows `(root, g)`. Each `root` is an
  address in the loaded heap where `termAt` reads `toTerm (absN xs_g
  body_g)`. The loader lists every occurrence. It need not share them. For
  a statement machine the check runs over its public cells, and a root's
  `termAt` must not reach an input cell, or the check would depend on the
  witness.
- The loaded heap is public, and `termAt` below the first counter never
  changes as the heap grows (`termAt_grow`). So the hypothesis holds at
  every row whose head is a listed root. Lean checks this statically: a
  checker `rootsOK (load t).heap roots templates : Bool`, with a soundness
  theorem, run when the statement is made. The verifier trusts no hash.
- The machine reaches a root by unwinding, since the loaded term applies
  `absN …` to its captures. `S` copies pointers, not cells, so a copy of a
  root is the root. At a root the prover may also unwind as usual:
  `JStep` allows either step, and both are sound.

### The tables

- **TEMPLATE** (preprocessed, public). One row per body cell,
  `(g, j, tag, a_op, a_val, b_op, b_val)`, in `ibuild` order. `tag` is
  `S`, `K`, `I` or `A`. An operand is `LOCAL j′` (the cell this
  instantiation wrote at offset `j′ < j`) or `ARG i` (the `i`-th popped
  argument). A header per template, `(g, k_g, n_g, root_op)`, gives the
  arity, the cell count and the root: `LOCAL (n_g − 1)` for an
  application body, `LOCAL 0` for a leaf, `ARG i` for a bare variable.
  Lean generates it from `ibuild` and `overrideN` themselves, so the order
  is the proved one, and `ARG i` names the argument `overrideN` gives a
  repeated formal.
- **POP** (witness). One row per popped argument, `(c, i, s, x, s′)`. It
  reads `C x s′` at `s` from memory, range-checked below `c`. Row `i + 1`
  starts where row `i` ended (`s = s′` of row `i`), row 0 starts at the
  `INST` row's stack, and the last `s′` is the rest. It sends
  `ARG(c, i, x)`. This is `popN`.
- **INSTW** (witness). One row per written cell, `(c, g, j, tag, a, b)`.
  It looks up `TEMPLATE(g, j, tag, ops)`. It resolves each operand:
  `LOCAL j′` to `c + j′`, `ARG i` to the `x` of `ARG(c, i, x)`. It writes
  `(c + j, tag, a, b)` to memory, a lookup at an address the counter
  covers, as the corpus's writes are. Rows for one `c` run `j = 0 … n_g −
  1`, chained like POP. This is `ibuild` with `overrideN`. The chains must
  define their empty cases: arity 0 (no POP rows, `rest = stk`) and a
  bare-variable body (no INSTW rows, `n_g = 0`).
- **CPU, kind `INST`.** It reads `ROOTS(hd, g)` and the header of `g`. It
  sends `POP-START(c = ctr, stk, k_g)` and receives `POP-END(c, rest)`.
  It sends `INSTW-START(c, g)` and receives `INSTW-END(c, g, n_g)`. The
  next registers are `hd′ = resolve(root_op)`, `stk′ = rest`,
  `ctr′ = ctr + n_g`.

The chains replace wide rows: any arity and any body size costs
`1 + k_g + n_g` table rows. The unjetted reduction it replaces costs up to
`3^k · vsize body` weak contractions (`absN_beta_count`), about 2.44 rows
each.

### The Lean side, before the circuit

1. `Air.instRow M roots templates r r′ : Bool`, the `INST` constraint over
   reads (`rd`) and write checks (`wrs`), in the style of `Air.stepRow`.
2. `instRow_jstep`: an `INST` row that passes is `JStep.inst` between
   `st M r` and `st M r′`, given `rootsOK`. The proof is `popN` against
   `rd`, and `ibuild` against `wrs` at the counter, as `stepRow_mstep`
   handles the corpus's writes.
3. `AcceptsJ`, the AIR with `INST` rows, and `air_sound_jet`: an accepted
   table is a `JSteps` run, so by `jet_run_eval` and `jet_run_shape` it
   proves the evaluation, up to weak reduction of the value, with the
   value's head and arity.
4. `checkJ`, deciding `AcceptsJ` on a concrete table, with soundness, for
   `lake exe aircheck` on the prover's jetted tables.
5. For probes, instantiation over open terms: `inst_sound` for `odecode`,
   so that a jetted run from a statement machine binds its output as
   `air_probe` does.

### Extensions, in order

- **Globals.** A body may name another template's root, for nested jets,
  through a third operand, `GLOBAL a`, a public address. In Lean, the
  default environment of `instStep` becomes a public map, and
  `inst_sound` takes a `γ` in place of `fun _ => K`. `absN_beta_close`
  already takes any `γ`.
- **Chained arities in one row.** This is a cost change only, with no
  soundness content.
- **Zero knowledge.** ROOTS and TEMPLATE are public and go under the
  public-seed commitment of `src/sudoku.rs`. POP and INSTW are witness
  tables with fixed heights, like the CPU's, and each needs a blinding
  message, since each has its own published terminal.

### What this does not cover

- **Data jets** (§18.2): native words and per-jet theorems.
- **The interpreter jet** (§18.3).
- **A DAG loader.** Sharing each root once would shrink ROOTS. `Stmt.pbuild`
  already builds a DAG for slots, and the same pattern applies.
