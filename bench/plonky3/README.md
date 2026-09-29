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

`src/sudoku.rs` proves a solution of Wikipedia's Sudoku puzzle, with
hiding commitments and blinded lookup sums. An accepted table has a
solution in its input cells; that the proof shows the prover *knows* one
rests on the STARK's knowledge soundness, which is not proved here. The
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
on otherwise. It prints the puzzle it accepted: the check pins the
statement to that puzzle, not to Wikipedia's, so whoever reads the
verdict must compare the puzzle with the one they meant.

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
checks `Sudoku.sudokuCheck` on it (soundly), for the statement's puzzle and markers,
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
program table's public terminal fixes anyway (proved in Lean for every
challenge whose combiner matrix is invertible: `Circuit.sud_zk`). The guess test replays the
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
honest      45,667 rows, 52,299 memory cells; prove 3.0-3.5 s, verify 0.07-0.09 s,
            proof about 600 KiB (postcard)  verified
guess test    the true inputs against the published witness terminal: no match
swapped       ends at the atom 732 (REJ); rejected by the verifier (OodEvaluationMismatch)
forged_input  ends at the atom 731 (ACC); rejected by the verifier (Lookup(TerminalSumNonZero))
```

`lake exe sudoku check` accepts the honest table (in 1 to 2 s) and
rejects both tampered ones, and a table whose puzzle line differs from
the statement's. `lake exe sudoku statement` rejects `public.txt` with
the markers exchanged or with a clue blanked. `swapped` is Wikipedia's solution with two
cells of row 0 exchanged, run honestly: the formula is false, and the run
ends at `REJ`. `forged_input` puts `I` in the first input cell, which is
no Boolean. That run reaches `ACC`, so without the witness table's
constraint the verifier would accept a table that proves nothing about a
grid. The lookup of the input cell fails instead. `prove` includes the
setup; the proof size varies with the random salts.

## A hidden term in zero knowledge

`src/witness.rs` proves knowledge of a hidden *term*, not only Boolean
inputs: a realizer of an NP atom `atom V x` of Part II's logic, a term `w`
such that `V x w` evaluates to `K` (`real_atom_iff`). The statement is the
witness machine `Wit.wMachine` of `Ski/Witness.lean`: a private region of
`W` cells at addresses `0 … W - 1`, then `V x` applied to the region's
last cell, with an empty stack. `lake exe witness emit` writes each
example's `public.txt`, the machine with the region blank, and the
regions: the honest realizer's, a well-formed region holding a term that
realizes nothing, and the honest region with a cell pointing forward.
The verifier first runs `lake exe witness statement` on `public.txt`,
which accepts exactly the witness machine of the atom and region size the
file names (`Wit.wMachine_public`).

The AIR differs from the Sudoku proof's in two places:

- **The output.** The last row is the halting kind `HK1`: `K` at the head
  and a nil at the stack. So the run evaluates to `K`, which is what
  realizing an atom means.
- **The witness table.** Each row commits the cell at a region address:
  `S`, `K`, `I`, or `A a b` with both pointers below the address, each
  range-checked twice (as a 24-bit number and as `i - a - 1`). So the
  region reads back as a closed term at its last cell (`Wit.wf_termAt`).

A table the verifier accepts has, by `Wit.wit_realizes`, a realizer of the
atom in its region. `lake exe witness check` decides that
(`Wit.witCheck_realizes`) on each table proved here. The hiding is the
Sudoku proof's: a hiding PCS, fixed heights (`2^10` rows and memory,
`2^8` witness rows, the least the hiding PCS masks), and two blinding
messages. The guess test replays the transcript and recomputes the
witness terminal for the true region: it does not match, and with the
blinding off it does, so the test has the power to catch a leak.

Two examples (`Ski/WitnessExamples.lean`, each checked in the kernel). An
atom certifies exactly its verifier's evaluation, and nothing more:

- `neg`: `w` passes the two tests a negation of Scott Booleans passes,
  `(w T) F T (w F) F` evaluating to `K`. The negation `[b] b F T`
  realizes it (`neg_real`) and the identity does not (`neg_not_I`); so
  does `K (K (K (K (K K))))`, which is no negation (`neg_fake`).
- `sat`: `w ([a b c] φ)` evaluates to `K` for `φ = (a ∨ b) ∧ (¬a ∨ c) ∧
  ¬c`. The triple `F T F` realizes it (`sat_real`) and `T T T` does not
  (`sat_not_TTT`); so does `K K`, which is no triple (`sat_fake`).

A verifier applies its witness to finitely many arguments, and a term can
fake any finite behaviour, so a hidden term fits a claim about the term
itself. An assignment proved as data must come in as cells the circuit
fixes to Booleans, as the Sudoku proof's inputs do.

**What the caller must do.** The statement names its own atom: whoever
reads the verdict compares `V` and `x` with the atom they meant. Lean's
check reads the whole table, region included, so the tables are the
prover's and are not published.

```
lake build witness && lake exe witness emit bench/plonky3/witness
cd bench/plonky3 && cargo build --release
./target/release/ski-air witness witness tables   # statement check, prove, verify, guess test, tamper
cd ../.. && lake exe witness check bench/plonky3/witness/neg/public.txt bench/plonky3/tables/witness_neg.txt
lake exe witness check bench/plonky3/witness/neg/public.txt bench/plonky3/tables/tampered_witness_neg_*.txt  # REJECT
```

Measured, 2026-09-28, Apple M4 Max, release build:

```
neg      47 public cells, a region of 32; 63 rows, 145 memory cells
         prove 0.08 s, verify 0.012 s, proof 405 KiB   verified
sat      145 public cells, a region of 32; 166 rows, 367 memory cells
         prove 0.06 s, verify 0.011 s, proof 401 KiB   verified
guess    no match for either; a match for each with the blinding off
wrong    ends at K over a stack cell (F = K I): the term fails the atom; rejected
forged   ends at K over a nil, the forward pointer never read;
         rejected by the witness table's constraint
```

`lake exe witness check` accepts both honest tables and rejects the four
tampered ones and a table offered under the other example's statement;
`lake exe witness statement` rejects a `public.txt` with a region cell
exposed, another input or another region size.

## A composed statement in zero knowledge

`src/composed.rs` proves the statement of a formula of atoms under `∧` and
`∨` (`Ski/Compose.lean`): public terms, a check of the formula over
hidden bits and a guard per atom, each of which must evaluate to `K` on
the literal bits and a hidden witness. The statement is the composed
machine `CompM.cMachine` of `Ski/Composed.lean`: the slot cells, one cell
per bit, the witness region, then the bits' encoding and each term applied
to the bits and the witness, at its segment's root. `lake exe composed
emit` writes each example's `public.txt`, the machine with the bits and
region blank, and its witnesses; the verifier first runs `lake exe
composed statement`, which accepts exactly the machine of the formula and
region size the file names (`CompM.cMachine_public`).

The table runs one **segment** per term. A new CPU row, **restart**, ends a
segment and starts the next: it reads `K` at the head over a nil, as the
halting kind `HK1` does, and moves to the next root (looked up in SEGS, a
preprocessed table of the roots) over the public nil. Its selector is a
column of its own, outside the kinds, so tables without segments keep
their layout. A segment count starts at 0, grows by one on each restart,
and is `n - 1` on the last row, which is `HK1`. The witness table has a
bit mode: a bit cell is `K` or `A 0 1` (`K I`), a literal Scott Boolean;
a region cell is `S`, `K`, `I` or an application of two cells below it.
A table the verifier accepts satisfies `CompM.AcceptsC`, so each term
evaluates to `K` on the bits and witness (`CompM.composed_sound`), and
they read back as a realizer of the formula (`CompM.checkC_realizes`).
`lake exe composed check` decides it on each table proved here. Hiding
is the Sudoku proof's; where a segment ends is a private row.

Two examples, the `∨` and the `∧` of the two atoms of
`Ski/WitnessExamples.lean`:

```
lake build composed && lake exe composed emit bench/plonky3/composed
cd bench/plonky3 && cargo build --release
./target/release/ski-air composed composed tables   # statement check, prove, verify, guess test, tamper
cd ../.. && lake exe composed check bench/plonky3/composed/or/public.txt bench/plonky3/tables/composed_or.txt
lake exe composed check bench/plonky3/composed/or/public.txt bench/plonky3/tables/tampered_composed_or_*.txt  # REJECT
```

Measured, 2026-09-28, Apple M4 Max, release build (heights `2^11` rows and
memory, `2^8` witness):

```
or       2 bits, a region of 64, 3 segments; 264 rows, 712 memory cells
         prove 0.11 s, verify 0.014 s, proof 476 KiB   verified
and      2 bits, a region of 64, 3 segments; 468 rows, 947 memory cells
         prove 0.12 s, verify 0.015 s, proof 486 KiB   verified
guess    no match for either; a match for each with the blinding off
clear    every bit clear: the formula check ends at K I; rejected
wrong    a set atom's verifier rejects its component; rejected
nonbool  a bit cell I: rejected by the witness table's bit mode
forged   a region cell pointing forward, never read: rejected by the witness table
```

**The standalone verifier.** `ski-air composed-prove PUBLIC WITNESS PROOF
[TABLE]` writes a proof, and `ski-air composed-verify PUBLIC PROOF` checks
one from its file: it reads the statement once and pipes those bytes to
`lake exe composed statement -`, refuses a proof with trailing bytes, pins
the heights, and verifies against the statement alone. `release/composed`
ships the two example proofs, and `release/verify.sh` checks them and
their forgeries.

`lake exe composed check` accepts both honest tables and rejects the
eight tampered ones and a table offered under the other formula's
statement; `lake exe composed statement` rejects a `public.txt` with a
private cell exposed, another formula, another region size or another
root. The caller compares the formula the statement names with the one
meant, and the Lean tables, which hold the witness, stay the prover's.

## Jets: instantiation rows

`src/jets.rs` proves every corpus row with supercombinator instantiation
rows. Five tables join the corpus's three: ROOTS, HDR and TMPL, public
and preprocessed from `lake exe jets emit`; and POP and INSTW, witness
tables chained to a CPU row of kind `INST`. `lake exe jets check` checks
each table it proves against `Air.AcceptsJ` (`Air.checkJA_sound`), with
the roots recomputed and licensed in Lean. Before it builds anything from
the jet files, the verifier runs `lake exe jets statement` with its own
corpus: each file must be Lean's for the term the verifier will prove,
with roots that pass `Air.rootsOKB` over that term's heap. `DESIGN.md` §2 gives the
tables, the argument and the measurements: `3 sumto` takes 3,678 CPU rows
instead of 25,074, and proves in 0.15 s.

```
lake build jets && lake exe jets emit bench/plonky3/jets
lake env lean --run bench/Dump.lean > corpus.txt
cd bench/plonky3 && cargo build --release
./target/release/ski-air jets ../../corpus.txt jets tables   # statement check, prove, verify, tamper
cd ../.. && lake exe jets check bench/plonky3/tables/jet_*.txt
lake exe jets check bench/plonky3/tables/tampered_jet_*.txt  # each must be REJECT
```

## Probe segments: the output, bound

`src/probe.rs` proves what a jetted run halts to. The public plan, from
`lake exe jets plan OUTCOME` (`Air.planOf`), has one segment per
constructor of the outcome's probe tree, depth first: its markers, its
expected constructor and field count, and the earlier segment's field it
probes. The CPU gains two kinds, the first probe row and a later one, and
two tables join the jetted ten: PLAN, preprocessed from the plan, and PW,
which writes each segment's markers and their stack. A later probe row
ends the segment before: it reads that segment's marker at the head, pops
exactly its fields by the POP chain, and reads a nil. The next segment's
term is a field of its parent, looked up by the parent's end row. The
last row ends the last segment. `lake exe jets check-probe` checks each
table against `Air.AcceptsP` (`Air.checkPA_decodes`), so an accepted
table proves that its term decodes to the outcome. A table certifies its
own term, the one on its first line: `ACCEPT` names it (the corpus row it
equals), and `--row NAME` refuses a table whose term is not that row's.
`DESIGN.md` §3 gives the argument.

`3 sumto` decodes to `[6]` in 11 segments and 4,144 CPU rows, proved in
0.24 s and verified in 0.02 s. The prover refuses the plans of `[5]` and
of the error outcome (a segment ends at the wrong marker), and the
verifier rejects the proof of `[6]` offered for either. Nine tampered
traces are rejected. Four break a local constraint: a child probing
another pointer than its parent's field, a segment ending without the nil
below its fields, a forged end marker, and a skipped probe count. Five
change only a count or a chain flag, so only a bus balance refuses them:
a surplus SEGEND, PLAN row or field, a dropped marker, and a child whose
parent row is redirected to an instantiation that popped the same pointer
at the same index, with every count rebalanced.

```
lake build jets
lake env lean --run bench/Dump.lean > corpus.txt
cd bench/plonky3 && cargo build --release
./target/release/ski-air probes ../../corpus.txt jets tables  # prove [6], verify, forgeries
cd ../.. && lake exe jets check-probe --row sumto_us bench/plonky3/tables/probe_sumto_us.txt val 6   # ACCEPT
lake exe jets check-probe --row sumto_us bench/plonky3/tables/probe_sumto_us.txt val 5               # REJECT
```

`ski-air probe-prove-table TERM JETS TABLE PROOF OUTCOME…` proves a
probe table another producer wrote, in `check-probe`'s format, as
`jet-prove` does a jetted one. On lean-ski's own table for `[6]` it
reproduces `probe-prove`'s proof byte for byte.

`DESIGN.md` records the tables: atoms and the witness table, the
instantiation rows and template table, and the probe segments.

## What this is not

- **The corpus proofs, plain, jetted and probed, are not zero
  knowledge.** Their PCS is not hiding, and the first row loads the whole
  term in the clear. Only the probe proof binds an output. The Sudoku and
  hidden-term proofs are hiding, and bind their accepting output.
- **Plonky3's zero knowledge is statistical and unaudited.** Plonky3 marks
  its randomization of the trace as statistically hiding only, and
  `HidingFriPcs` enforces a masking budget (trace height at least
  `2 · (queries + 4 · opening points)`) that every Sudoku table meets.
- **The zero-knowledge argument is formal for the terminals only.**
  `Ski/ZK/Circuits.lean` proves that two balanced table sets for one
  statement publish their witness, CPU and memory terminals with the same
  distribution over the two blinding tuples (`sud_zk`, `wit_zk`,
  `comp_zk`), counted exactly over all `P^8` pairs, and within `2 P^4` of
  them on the draws where every inverse exists (`*_zk_valid`). Its gaps:
  - `Generic β` (the combiner matrix invertible) fails exactly when `β`
    lies in the subfield `F(x^2)` (`generic_iff`): `P^2` of the `P^4`
    challenges (`nongeneric_count`), about `2^-62`, which dominates the
    bound.
  - The challenge is fixed. In Plonky3 it is a Fiat–Shamir output of the
    trace commitments, which contain the blinding columns; independence
    rests on the hiding PCS in the random oracle model, unproved.
  - The composed proof's segment table is private, but for accepting
    runs its multiplicities are `1` for segments `1..n-1` and `0`
    elsewhere (`composed.rs`, `table`); `comp_zk` assumes it shared.
  - The prover aborts on a zero LogUp denominator. For the blinding
    messages that event is witness-independent; for the others it is not,
    and has probability at most about the number of messages over `P^4`.
  - Everything committed and opened rests on Plonky3's hiding PCS,
    unproved; no simulator for the whole transcript is written down.
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
- **The link to Lean is proved from the constraints.** Each verifier
  pipes the AIRs it verifies with to `lake exe circuit`, which checks them
  against Lean's `baseAirs`, `sudAirs`, `jetAirs` or `probeAirs`, and Lean
  proves that the tables those AIRs accept satisfy `Accepts`, the Sudoku
  statement, `AcceptsJ` or `AcceptsP` (`export_sound`, `sudExport_sound`,
  `jetExport_sound`, `probeExport_sound`), and that every run has tables
  they accept. Assumed: Plonky3's STARK and LogUp soundness, that an
  accepted proof has such tables (`Accepted`, `Ski/Circuit/Air.lean`).
  Trusted: the export's parser and Plonky3's symbolic builder. The Lean
  checkers also check each table the prover proves (`checkA` decides;
  `sudokuCheck` and `checkJA` are proved sound).
