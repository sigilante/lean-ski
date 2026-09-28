# The AIR in Plonky3, checked against Lean

`src/main.rs` is the AIR of `Ski/Air.lean` in Plonky3 0.8: a batch STARK
over BabyBear with three tables joined by one LogUp bus, `mem`, whose
entries are `(address, tag, a, b)`.

- **CPU**: one row per machine transition, padded to a power-of-two budget
  with halted rows. A row holds the registers `hd`, `stk`, `ctr`, a one-hot
  selector for its kind, the fields of the cells it reads, and 24 bits per
  read that range-check the address below `ctr`. The kinds are the cases of
  `Air.stepG` and `Air.haltRow`: an unwind, `I`, `K`, `S`, and the six ways a
  combinator can lack arguments. A kind fixes the tags of its reads, so the
  lookups check exactly the cells the Lean rule reads, and the writes are
  lookups at `ctr`, `ctr + 1`, `ctr + 2`.
- **Memory**: the committed memory table, one entry per address in order
  (`addr` starts at 0 and increases by 1), with each entry's lookup count.
- **Program**: the loaded heap of the public term, a preprocessed table the
  verifier rebuilds from the term. Every loaded cell is looked up in memory,
  which pins the memory table's prefix.

The verifier builds its AIRs and the program table's preprocessed
commitment from the public term alone, reads the CPU and memory heights
from the proof, and rejects heights above `2^21` or a program height other
than the term's. It never sees the traces.

## Checked against Lean

For every table it proves, the prover writes the same table (the memory
table and the rows) in the format of `Ski/AirCheck.lean`. `lake exe aircheck`
decides the AIR's constraints on it with `Air.checkA`: it accepts exactly
the tables that satisfy `Air.Accepts` (`Air.checkA_iff`), and by
`Air.air_sound_eval` an accepted table proves the evaluation it ends on.
Four tampered tables, changed identically in the trace and in the Lean
table, must fail both: the prover must produce a proof and the verifier
must reject it, and `aircheck` must reject the table. They are a forged
memory cell, a wrong transition, an early halt, and a forged program (the
honest run of `I S` offered for the public term `I K`).

```
lake env lean --run bench/Dump.lean > corpus.txt        # from the repository root
cd bench/plonky3 && cargo build --release
./target/release/ski-air ../../corpus.txt tables         # prove, verify, tamper
cd ../.. && lake build aircheck
lake exe aircheck bench/plonky3/tables/{ik,skks,compiled_*,interpreted_*,sumto_us}.txt
lake exe aircheck bench/plonky3/tables/tampered_*.txt    # each must be REJECT
```

## Measured, 2026-09-27, Apple M4 Max, release build

```
row               contr   rows budget  memory  prove s verify s  verdict
ik                    1      3     16      16     0.01    0.005  verified
skks                  2      6     16      16     0.06    0.001  verified
compiled_up         493   1207   2048    8192     0.05    0.009  verified
compiled_uq         440   1078   2048    4096     0.04    0.007  verified
compiled_ur         530   1297   2048    8192     0.05    0.009  verified
interpreted_up     2014   4909   8192   16384     0.13    0.012  verified
interpreted_uq     2029   4949   8192   16384     0.13    0.012  verified
interpreted_ur     2589   6308   8192   16384     0.13    0.012  verified
sumto_us          10297  25074  32768   65536     0.48    0.014  verified

tampered tables (each proof must be rejected by the verifier):
forged_cell      rejected by the verifier (verify: Lookup(TerminalSumNonZero))
wrong_step       rejected by the verifier (verify: Verification(OodEvaluationMismatch ...))
early_halt       rejected by the verifier (verify: Lookup(TerminalSumNonZero))
forged_loaded    rejected by the verifier (verify: Verification(InvalidOpeningArgument(...)))
```

`lake exe aircheck` accepts all nine honest tables (in about 1.4 s) and
rejects the four tampered ones. The forged program fails at the opening
check: the verifier computes the program table's commitment from the
public term, so the proof's transcript no longer matches. Timings vary by
a few percent between runs. The `rows` column equals `lake exe aircost`'s on
every corpus row; `prove s` includes the setup.

## A Sudoku solution in zero knowledge

`src/sudoku.rs` proves that the prover knows a solution of Wikipedia's
Sudoku puzzle, with hiding commitments and blinded lookup sums. The
statement is the machine `Stmt.stmtMachine` of `Ski/Statement.lean` for
the puzzle's formula (`Sudoku.sudokuExpr`): the slot cells `K`, `I`, `K I`
at addresses 0 to 2, 729 input cells at 3 to 731, then the compiled
formula applied to the atoms labelled `ACC` = 731 and `REJ` = 732 (labels,
not addresses). Input `81r + 9c + d` says that row `r`, column `c` holds
`d + 1`. `lake exe sudoku emit` writes the statement with the input cells
blank (`public.txt`) and the solution's inputs (`witness.txt`). The
blank-input heap states the machine for every input
(`Stmt.stmtMachine_public`).

**The statement is checked on the verifier's path.** A `public.txt` with
the two markers exchanged, or cells for another puzzle, would let a
wrong grid verify. So the verifier first runs `lake exe sudoku statement
public.txt` itself, which accepts exactly the statement of the puzzle on
its first line (`publicText` in `bench/Sudoku.lean`), and refuses to go
on otherwise.

The AIR adds three things to the corpus's:

- **Atoms.** A memory cell may be the atom `n` (tag 6). A seventh halting
  kind reads an atom at the head, as `Air.haltRow` accepts.
- **The output.** The last row must read the atom `ACC` at the head.
- **A private witness table.** Each row commits one bit and looks up the
  memory cell at a preprocessed input address: `K` when the bit is 1,
  `A 0 1` (`K I`) when it is 0. So every input is a Scott Boolean. The
  program table holds the public cells with their addresses. Together the
  two tables name every address below the first counter, so the memory
  table's prefix is `stmtMachine ρ` for the inputs `ρ` the bits give.

A table the verifier accepts satisfies `Air.AcceptsFrom` from that machine
and reads `ACC` at the head of its last row. By `Sudoku.sudoku_sound`,
the inputs solve the puzzle. The prover writes each table it proves in
the format of `bench/Sudoku.lean`. `lake exe sudoku check public.txt`
decides `Sudoku.sudokuCheck` on it, for the statement's puzzle and markers,
reading the inputs off the table's memory (`Sudoku.sudokuCheck_sound`).

**Hiding.** The PCS is Plonky3's `HidingFriPcs`, with salted Merkle leaves
and four random codewords drawn from the operating system's generator.
The verifier rebuilds the preprocessed commitment, so both sides commit
the public preprocessed tables under a fixed public seed; only the traces
are committed under fresh randomness. The CPU and memory heights are
constants of prover and verifier (`2^16` each), not the run's, so they say
nothing about the witness: the run's length depends on where each digit's
bit falls.

**Blinding.** Plonky3 publishes each table's LogUp terminal, its whole
lookup sum, in the clear; the hiding PCS does not mask it. Unblinded, the
witness table's terminal is a function of the inputs under challenges any
verifier replays, which lets anyone check a guessed grid. Two buses of
their own carry one message each, a fresh uniform 4-tuple: from the witness
table to the CPU, and from the CPU to memory. Each adds a term uniform over
the extension field to one terminal and takes it from another, so the
three private terminals are uniform subject to their sum, which the
program table's public terminal fixes anyway. The guess test replays the
transcript as a verifier would and recomputes the witness terminal for the
true inputs: it must not match the published one. With the blinding flags
set to zero, it matches.

```
lake build sudoku && lake exe sudoku emit bench/plonky3/sudoku
lake exe sudoku statement bench/plonky3/sudoku/public.txt   # the verifier's statement check
cd bench/plonky3 && cargo build --release
./target/release/ski-air sudoku sudoku tables               # prove, verify, guess test, tamper
cd ../.. && P=bench/plonky3/sudoku/public.txt
lake exe sudoku check $P bench/plonky3/tables/sudoku.txt
lake exe sudoku check $P bench/plonky3/tables/tampered_sudoku_*.txt   # each must be REJECT
```

Measured, 2026-09-27, Apple M4 Max, release build, three runs:

```
statement   23,394 public cells, 729 inputs; heights 2^16 rows, 2^16 memory, 2^10 inputs
honest      45,667 rows, 52,299 memory cells; prove 3.0-3.3 s, verify 0.07-0.09 s,
            proof about 600 KiB (postcard)  verified
guess test    the true inputs against the published witness terminal: no match
swapped       ends at the atom 732 (REJ); rejected by the verifier (OodEvaluationMismatch)
forged_input  ends at the atom 731 (ACC); rejected by the verifier (Lookup(TerminalSumNonZero))
```

`lake exe sudoku check` accepts the honest table (in about 2 s) and
rejects both tampered ones, and a table whose puzzle line differs from
the statement's. `lake exe sudoku statement` rejects `public.txt` with
the markers exchanged or with a clue blanked. `swapped` is Wikipedia's solution with two
cells of row 0 exchanged, run honestly: the formula is false, and the run
ends at `REJ`. `forged_input` puts `I` in the first input cell, which is
no Boolean. That run reaches `ACC`, so without the witness table's
constraint the verifier would accept a table that proves nothing about a
grid. The lookup of the input cell fails instead. `prove` includes the
setup; the proof size varies with the random salts.

## Jets: instantiation rows

`src/jets.rs` proves every corpus row with supercombinator instantiation
rows. Five tables join the corpus's three: ROOTS, HDR and TMPL, public
and preprocessed from `lake exe jets emit`; and POP and INSTW, witness
tables chained to a CPU row of kind `INST`. `lake exe jets check` checks
each table it proves against `Air.AcceptsJ` (`Air.checkJA_sound`), with
the roots recomputed and licensed in Lean. The verifier runs `lake exe jets statement` on the jet files before it
builds anything from them. `DESIGN.md` §2 gives the
tables, the argument and the measurements: `3 sumto` takes 3,678 CPU rows
instead of 25,074, and proves in 0.15 s.

```
lake build jets && lake exe jets emit bench/plonky3/jets
lake env lean --run bench/Dump.lean > corpus.txt           # ski-air runs `lake exe jets statement` itself
cd bench/plonky3 && cargo build --release
./target/release/ski-air jets ../../corpus.txt jets tables   # prove, verify, tamper
cd ../.. && lake exe jets check bench/plonky3/tables/jet_*.txt
lake exe jets check bench/plonky3/tables/tampered_jet_*.txt  # each must be REJECT
```

`DESIGN.md` records the tables: atoms and the witness table, and the
instantiation rows and template table.

## What this is not

- **The corpus proofs are not zero knowledge.** Their PCS is not hiding,
  and the first row loads the whole term in the clear; nor do they bind an
  output. The Sudoku proof does both.
- **Plonky3's zero knowledge is statistical and unaudited.** Plonky3 marks
  its randomization of the trace as statistically hiding only, and
  `HidingFriPcs` enforces a masking budget (trace height at least
  `2 · (queries + 4 · opening points)`) that every Sudoku table meets.
- **The zero-knowledge argument is informal.** It rests on Plonky3's
  hiding PCS for everything committed and opened, and on the blinding for
  the published terminals. No simulator is written down, and the guess
  test checks one attack, not all.
- **Security is Plonky3's benchmark setting**: blowup 2, 100 queries and 16
  bits of query grinding. Plonky3's `conjectured_soundness_bits` gives 116,
  but that counts the query phase only and Plonky3 marks it as not a
  soundness bound; the composite conjectured bound (opening batching, the
  LogUp argument, DEEP, folding) is lower and was not computed here. Batch
  grinding would raise it.
- **The range checks** are sound because the verifier accepts CPU and
  memory heights only up to `2^21`: addresses stay below `2^21` and
  counters below `2^23`, so a read at or above the counter wraps to at
  least `p − 2^21`, which no 24-bit decomposition represents.
- **The link to Lean is per table.** The Lean checkers decide `Accepts`
  and `sudokuCheck` on each table the prover proves; that every table the
  verifier accepts satisfies them is argued in the headers of
  `src/main.rs` and `src/sudoku.rs`, not proved in Lean.
