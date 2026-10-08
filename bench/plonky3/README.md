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

The verifier checks each statement and its AIRs in Lean: it runs
`lake exe composed statement-p2` (or `circuit compare-…`) in the lean-ski
checkout it was built in, else in `$LEAN_SKI`. A Lean check that has not
answered within `$LEAN_TIMEOUT` seconds (default 600) fails the
verification; its stderr is reported when it prints nothing.

### The traces against Lean's honest tables

Each zero-knowledge circuit's completeness proof builds honest tables
from a run, and its zero-knowledge theorem simulates their terminals
blinded at its view's blocks. For each circuit the prover dumps the
private traces it proves, unblinded and blinded, with the run (`ski-air
*-dump`). Lean then checks that the unblinded traces are its honest tables
built from that run, and that the blinded ones are those tables blinded
exactly at the view's blocks (`Ski/ZK/Blocks.lean` lists each view's
blocks as data, proved its view's by `rfl`). Gate 5 runs every one:

```
circuit       dump                       tables                     blinding               runs
composed      ski-air composed-dump      composed check-c-tables    composed check-c-blind    or, and
hidden term   ski-air witness-dump       witness check-tables       witness check-blind       neg, sat
Sudoku        ski-air sudoku-dump        sudoku check-tables        sudoku check-blind        Wikipedia's
with jets     ski-air compj-dump         composed check-cj-tables   composed check-cj-blind   split8
Poseidon2     ski-air compp-dump         composed check-p2-tables   composed check-p2-blind   p2pre, handoff1, handoff2
```

- Every row of the witness and memory tables is compared, and of the
  jet tables (POP, INSTW, HDR, TMPL, P2IN, P2OUT, P2). A memory row's
  multiplicity is `memTableC`'s or `memTable5`'s count of the messages
  the dumped sender tables and Lean's own program table send it, counted
  in one pass and proved equal to the definition
  (`Circuit.memTableC_mult`, `memTable5_mult`). Where the CPU is compared
  on every row (the hidden term) that is the honest multiplicity; where
  it is sampled, it shows the memory consistent with the dumped CPU.
- The CPU is compared on every row where Lean's model is cheap (the
  hidden term), else on samples: every moving row of a short run, every
  16th of a long one, segment ends, jet rows, the halt, the two rows
  after it and the run's last, and every 64th row past the halt.
  With jets Lean's CPU row reads its memory as a list and costs seconds,
  so `split8`'s sample is 21 rows of every kind.
- The jet providers' counts are the run's lookups, counted over its
  instantiations listed once (`JRun.cntRoots_eq` and its kin); ROOTS is
  compared on its first 256 rows, every 64th and its last 64.
- The blinding check also requires every unblinded block column clear on
  every row, the theorems' clear-flags hypothesis, and refuses an
  all-zero tuple, which the theorems allow but a uniform draw makes
  vanishingly rare (`p^-4`).
- Each table's height must be the statement's (or the proof's fixed
  height) and its width its AIR's.
- With jets, the run read back from its table (`ski-air compj-dump-table`,
  the path `compj-prove-table` takes for Avon's tables) gives the same
  traces, byte for byte, as the run from the witness.

The comparisons found three differences, each a cell no constraint or
published sum depends on, or a choice between two valid runs, and each now
follows Lean's honest table:

- an inactive read's fields hold the cell at its address (`fieldsAt`);
- a segment's next root is on every row (`cpuColC`, `cpuColCJ`), not only
  on the restart row whose message reads it;
- with jets, an instantiation the machine's own step reproduces (a
  projection jet, which writes no cell) runs as that step, as the honest
  run's `jetOf` has it. The rows are the same either way, so Avon's
  tables are unchanged; `split8` now runs 1,952 instantiations and 8,018
  POP rows (was 2,250 and 8,614), `csplit8` 44,427 and 101,300 (was
  46,549 and 105,544). The released proofs were remade with these counts
  on 2026-10-09.

Each check takes seconds, except Sudoku (about a minute), `p2pre` (about
50 s), the hand-off's runs (about 80 s each) and `split8` with jets
(about 2½ minutes). What they leave out: the rows sampled out, and so,
where the CPU is sampled, the honesty of the memory's multiplicities
beyond the dumped CPU's; the runs themselves, which both sides read, so
that checking them is the AIRs' and the proof's job; and the tuples'
randomness.

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
and four random codewords. Every secret draw of a proof comes from one
128-bit seed, fresh from the operating system for that proof and never
reused (`src/seed.rs`): ChaCha20 expands it, with its own stream for the
blinding tuples, the leaf salts and the codewords. Splitting the seed
into its streams consumes it, so a second proof cannot reuse one. Its 128
bits bound one key search at `2^128`, and a batch search over `N` proofs
at about `2^128 / N`. The verifier rebuilds
the preprocessed commitment, so both sides commit the public preprocessed
tables under a fixed public seed; only the traces are committed under the
secret one. The Lean theorems count over uniform randomness; that ChaCha20
under the seed is indistinguishable from it is assumed
(`Ski/ZK/PRG.lean`, `transcript_prg`). The CPU and memory heights are
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
./target/release/ski-air sudoku-prove sudoku/public.txt sudoku/witness.txt sudoku.proof   # to a file
./target/release/ski-air sudoku-verify sudoku/public.txt sudoku.proof                     # VERIFIED
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

**The digest binds the CPU's constants.** The CPU's start head, stack
and counter and its acceptance flag sit in no committed table; the
statement's digest, the CPU instance's public values (`src/stmt.rs`),
carries them. `ski-air composed-digest-bound PUBLIC PROOF` checks the
proof with its own statement's digest, then, every AIR exactly as the
statement gives it, with the digest of the same statement with one of
those constants changed: each must be refused, and since only the digest
differs, the refusal is the digest's. It prints `BOUND` when all four
are. `release/verify.sh` runs it on the composed and entropy proofs.

`lake exe composed check` accepts both honest tables and rejects the
eight tampered ones and a table offered under the other formula's
statement; `lake exe composed statement` rejects a `public.txt` with a
private cell exposed, another formula, another region size or another
root. The caller compares the formula the statement names with the one
meant, and the Lean tables, which hold the witness, stay the prover's.

### `∃` and knowledge implication

A statement can also name a formula with `∃` over a hidden witness and
knowledge implication through a certified witness map (`formula X …`,
`Ski/ComposeX.lean`). Both compile to the same evaluation statement, so
the circuit, the prover and the checker are unchanged.

- **`∃`** (`E F`): `∃ y. F`, the value `y` held once in the witness, and
  every atom under the binder reads `⟨x, y⟩` as its input. Two atoms
  under one binder read the same hidden `y`; with `∧` and `∨` alone each
  atom reads only its own component, so no two atoms can be made to agree
  on a hidden value.
- **Knowledge implication** (`swap F`, `fst F`, `snd F`, `inl F G`,
  `inr F G`): the statement proves `F`; the formula concluded is its image
  under a public witness map from a library Lean certifies (`XS.cert`):
  every realizer `a` of the hypothesis makes `f a` a realizer of the
  conclusion. Zero knowledge covers the hypothesis's witness, and the
  statement names the hypothesis: `inl A B` reveals that `A` holds, and
  `fst (A ∧ B)` requires and checks `B`. The unproved side of an
  injection is read with no bound values. A hidden realizer of `A → B`
  is not checkable by finitely many evaluations.

`lake exe composed emit DIR` writes three examples next to `or` and `and`,
each proved, verified and checked end to end:

```
exists   ∃ y. y = w₁ ∧ y = ¬w₂     3 bits, 3 segments; 498 rows, 995 cells   verified, ACCEPT
fst      fst (neg ∧ sat) ⊢ neg      2 bits, 3 segments; 468 rows, 947 cells   verified, ACCEPT
inl      inl neg sat ⊢ neg ∨ sat    1 bit, 2 segments; 111 rows, 286 cells    verified, ACCEPT
```

A wrong witness is refused by the prover for each, and `composed
statement` refuses a map applied to a formula it does not fit (`fst` of
an atom). `lake exe composed check` reads an accepted table back as a
realizer of the formula concluded (`CompM.checkCX_realizes`).

### A chain of proofs over a public hand-off

Incremental composition without recursion (`Ski/Chain.lean`): each stage
is a composed statement of its own, proved by its own prover, and later
statements are computed from earlier ones and the values they publish.
`lake exe composed emit` writes a two-stage chain over the hand-off
`o = F` (`Ski/ChainExamples.lean`), proved and verified separately:

```
chain1   a satisfying assignment whose first variable is o   302 rows   verified, ACCEPT
chain2   a negation taking o to T                             153 rows   verified, ACCEPT
```

The verifier checks each proof, and that both statements name the same
`o` (the last term of each `formula X A V o` header). Each proof's
statement digest binds `o` into its transcript. Together the two prove
the conjunction (`chain_real`), and stage 1's witness does not prove it at
another hand-off (`stage₁_refuses_other`). The cost is every proof, so it
grows with the chain. A hidden hand-off puts a commitment in place of
`o`: Plonky3's compression of `o` and eight random elements, as
specified in Lean (tested against Plonky3, not proved equal). The chain's
knowledge soundness then reduces to the compression's collision
resistance (`hidden_chain`, `Ski/DataJet.lean`).

The circuit with the Poseidon2 jet computes the commitment inside each
stage's proof (`Ski/P2Commit.lean`). `lake exe composed emit-handoff DIR`
writes two `p2commit c pat` statements over one commitment and their
shared witness. Its value and randomness are fixed (`handoffValue`,
`handoffRand`), for tests, so that commitment hides nothing; `--fresh`
draws both from the system's entropy, as the release's statements do:
eight uniform elements below `p`, and a value meeting both patterns with
its undisclosed parts uniform. `--rand=FILE` reads the randomness, with
the tests' value. `lake exe composed check-handoff PUBLIC1
PUBLIC2` checks that two files are exactly the hand-off's statements for
the commitment they name, which is how the release's are checked:

```
handoff1   value element 1 is 840        13,991 rows   2.2 s   verified
handoff2   value element 0 is odd        13,156 rows   2.2 s   verified
```

`ski-air compp-chain PUBLIC1 PROOF1 PUBLIC2 PROOF2` asks Lean whether the
two statements form a chain (`composed chain-p2`: one commitment, both
patterns fixing value bits only and bit 30 of each value element to 0),
then verifies each proof against its own statement. It reads each
statement file once and hands the same text to both checks. From
two accepted proofs, the second's memory holds bits that meet both
patterns, or the two memories' openings collide (`p2commit_chainB`).

`compp.rs`'s unblinded traces agree with Lean's model of the honest
tables (`Ski/Circuit/CompPHonest.lean`, whose balance and clear flags
`P2Run.honest_zkP` proves) on every cell compared. `ski-air compp-dump
PUBLIC WITNESS DIR` writes the run and the unblinded traces. `lake exe
composed check-p2-tables PUBLIC DIR` rebuilds the model from the run and
first checks the dump's shape: each table's height is the statement's,
the run's is the CPU's, and the Poseidon2 tables are at least as wide as
Lean's rows. It
then compares:

- every row of P2IN, P2OUT, the Poseidon2 table (its padding the zero
  input's inactive trace) and the witness table;
- of the memory, every row: its address, tag and fields, and its
  multiplicity, `memTable5`'s count of the messages the dumped sender
  tables and Lean's program table send it, counted in one pass
  (`Circuit.memTable5_mult`);
- of the CPU, every moving row of a run of at most 2048 (every 16th of a
  longer one), its jet rows, ends and halt, and every 64th row after it.

Gate 5 runs it on `p2pre`'s run and on the hand-off's two runs with the
tests' value and randomness (the release's hand-off witness is
discarded), each with 0 cells differing (rows and times from runs by
hand):

```
p2pre      1,543 of 16,384 CPU rows   about 50 s
handoff1     918 of 16,384 CPU rows   about 90 s
handoff2     879 of 16,384 CPU rows   about 80 s
```

Its limits:

- it compares the run both sides read, so it does not check the run;
  the AIRs and the proof do;
- it skips the CPU rows between samples, and so checks the memory's
  multiplicities only against the dumped CPU's messages;
  the blinded traces the proofs commit to `check-p2-blind` compares
  (below).

The comparison made the CPU trace fill an inactive read's fields as Lean's
honest row does (`fieldsAt`), with the cell at the read's address where
the trace held zeros. Every circuit's CPU shares the trace (`cpu_trace`),
so its private columns now hold memory contents there. That keeps zero
knowledge:

- every message that carries a read's fields has a count that is 0 when
  the read is inactive: the read's own message counts the read's
  activity, and the writes and the jet's messages that reuse fields count
  kinds whose rows make those reads active; so no published sum depends
  on an inactive read's fields;
- the CPU table is committed like every private column, its openings
  masked by random rows (`masks_hide`);
- for this circuit, Lean's honest model is these tables, and
  `P2Run.honest_zkP` proves its balance and clear flags, the hypotheses of
  `compP_transcript`; `compPG_complete_log` proves the circuit accepts
  them.

`ski-air compp-guess PUBLIC WITNESS` tests the published terminals of all
six private tables: CPU, MEM, WIT, P2IN, P2OUT and the Poseidon2 table. A
guess from the true witness, recomputed under the proof's own challenges,
matches none of them, and matches each when the proof is unblinded. It
passes on `p2pre` and on the hand-off with the tests' witness, and gate 5
runs it.

**The blinded traces are the theorem's.** `compP_transcript` simulates
the terminals of `Circuit.compPViewN`'s tables: the honest tables, each
blinded by `Table.setBlind c (t k)`, which writes edge `k`'s tuple and the
flag 1 into row 0 at column `c`, at ten blocks on the tree's five edges.
`ski-air compp-dump` also writes the traces a proof commits to, blinded
under a fresh seed (`DIR/NAME.blind.txt`), and `lake exe composed
check-p2-blind DIR` checks that they are its unblinded traces blinded
exactly so; `check-p2-tables` compares those unblinded traces with Lean's
model, as far as it reaches (above):

- every cell agrees but row 0's block cells, at the columns
  `compPViewN` names (CPU at `BLA`, `BLB`, `P2SEL + 1`; MEM at 5; WIT at
  `WT_BLIND`; P2IN and P2OUT at their widths and widths + 5; P2 at its
  width);
- each block holds a tuple, not all zero, and the flag 1; the unblinded
  table's block columns are zero on every row, its flags clear
  (`UnblindedCP`), CPU and memory rows included that `check-p2-tables`
  does not reach;
- the two blocks of each edge hold one tuple.

It takes about 1.5 s, passes on the three runs, and refuses a tuple
changed at one end of an edge, a flag cleared, a cell changed outside the
blocks or beside one, a block moved to row 1, a zeroed tuple, and a flag
set on a later row of both traces. Gate 5
runs it. What it cannot see is the tuples' randomness, which rests on the
prover's fresh seed and ChaCha20 (`transcript_prg`).

The permutation's specification (`Ski/ZK/Poseidon2.lean`) uses Plonky3's
own constants and test vectors, which `ski-air poseidon2-lean` prints as
Lean:

```
ski-air poseidon2-lean > Ski/ZK/Poseidon2Data.lean
```

The kernel checks the specification against those three vectors
(`Poseidon2.permute_matches`), a test on three inputs.

### Poseidon2 in SKI, run by Avon

The data jet's contract has a proved SKI implementation, `P`
(`Ski/ZK/Poseidon2SKI.lean`, `poseidon2_implements`). `lake exe p2run K
DIR` writes `P` applied to Plonky3's test vector `K` in Avon's DAG form,
each distinct subterm once, and the normal form `P_spec` proves it
reaches, Plonky3's output, in Avon's printed form:

```
lake exe p2run 1 DIR
avon reduce --fuel=8000000000 --max-nodes=100000000 DIR/p2.dag | tail -n +2 | cmp - DIR/p2.expected
```

At Avon `188f7f2`, `share` mode (graph reduction), on an M4 Max:

```
vector   contractions   time      peak RSS
0        968,992,246    10.40 s   67 MB
1        962,192,547    10.15 s   66 MB
2        980,820,715    10.35 s   68 MB
```

Each reaches the expected normal form byte for byte. A full round costs
about 94 million contractions and a partial round about 15 million; one
S-box, about 5 million. Without sharing (`--strategy=copy`), vector 1
passes 8 × 10⁹ contractions in 33.6 s without finishing. The circuit's
write-once heap shares no work either, and its largest tables hold about
400,000 contractions (`PLAN.md` §5), so the hash runs in the circuit only
as a jet.

### The Poseidon2 table

`src/p2air.rs` is the precompile's table, one row per permutation; Lean's
`Ski/Circuit/P2Air.lean` is the same table as data, with `p2_sound_row`:
every row of a table that satisfies the AIR computes `Poseidon2.permute`.
The constraints use Plonky3's generic linear layers, and the export
matches Lean's:

```
ski-air export-p2 | lake exe circuit compare-p2 -    # MATCH p2: 634 constraints, 1 interactions
ski-air p2-bench 4096                                # prove and verify 4,096 permutations
ski-air p2-bench 256 tamper                          # one output off by one: rejected
```

```
permutations   rows    prove     verify    proof
256            256     0.02 s    0.007 s   325 KB
4,096          4,096   0.16 s    0.011 s   410 KB
```

`src/compp.rs` joins the table to the CPU through P2IN and P2OUT, on the
buses `p2v` and `p2w` (`Ski/Circuit/CompPAir.lean`).

## A SKIlark predicate in zero knowledge

A SKIlark (Joy) program is the verifier of a **predicate statement over
literal bits** (`Ski/Predicate.lean`), which the composed circuit proves.
A predicate `V x` over `n` bits has the shape of `n` bits and one term,
`[ρ w] V x ρ`: the verifier reads the bits and never the hidden witness
term. The bits are the machine's slot cells, which the witness table
constrains to `K` or `K I`, so the verifier runs on a list of Scott
Booleans a prover cannot shape. **`Circuit.predExport_sound`**: an
accepted proof's memory holds `n` Booleans `bs` with `V x (boolsT bs)`
evaluating to `K`. Completeness is `Circuit.comp_completeG_log`, and the
zero knowledge of the published sums `comp_zk`, both for any evaluation
statement; the circuit is `Circuit.compAirsG`, of which the formula
circuit is an instance.

**Why not the witness term.** A formula's atom hands its verifier a
component of the hidden term, and a term answers the verifier's case
analysis however it likes: over a hidden term, SKIlark's `vsplit` accepts
`K (K (RVal R))`, `R` a stack of `2k - 1` zeros, which is no stack at all,
at `x` = 0 and 1 (pinned in SKIlark's `tests/test_zk.py`). A claim about data needs the
data as literal bits.

**The predicate `split`** (`skilark.zk`, in the SKIlark repository):
`vsplitB x r` decodes `r`, `2k` literal bits, into the bits of two numbers
`a` and `b` (interleaved, least significant first), runs a Joy predicate
on the stack `x` above them, and returns Scott true, `K` itself, when it
leaves a nonzero numeral. `x` is one quotation of its bits, least
significant outermost. Each of the `k` unrolled steps unpacks `x_i` and
branches on `x_i`, the carry, `a_i` and `b_i`; a wrong sum bit or a carry
out fails. That `vsplitB` accepts exactly the bits of two numbers adding
up to `x` is tested, not proved: every bit pattern at `k` = 2 and 3 in
the tests, all 4,096 cases at `k = 4` in a one-off run, and a few samples
at `k = 8`.

**What it proves, and what it does not.** Some `a, b < 2^k` add up to
every `x < 2^k` (`a = x`, `b = 0`), so an accepted proof shows only that
`x < 2^k`: the pipeline is sound, the statement is weak. A range proof
needs a commitment binding the hidden number to something public.

- **The source, not the Python.** `lake exe skilark statement SRC K X
  PUBLIC` compiles the SKIjack source in Lean (`Front.compileFile`, which
  gives the term `skijack` gives) and checks that the statement is the
  predicate `vsplitB x` over `2K` bits, with `x < 2^K`. That the source is
  `skilark.zk`'s `split` for width `K` is the producer's word; `python -m
  skilark.zk 8` regenerates it byte for byte.
- **The heights are the statement's.** `public.txt` may name the CPU and
  memory log heights, `log R M` with each in `[8, 20]`; without the line
  they are `2^11`, so earlier statements are unchanged.

```
~/SKIlark/.venv/bin/python -m skilark.zk 8 > bench/plonky3/skilark/split8/source.ski
lake build skilark && lake exe skilark emit bench/plonky3/skilark/split8/source.ski 8 200 123 77 17 18 bench/plonky3/skilark/split8
lake exe skilark statement bench/plonky3/skilark/split8/source.ski 8 200 bench/plonky3/skilark/split8/public.txt
bench/plonky3/target/release/ski-air composed bench/plonky3/skilark bench/plonky3/tables   # prove, verify, guess test, tamper
lake exe composed check bench/plonky3/skilark/split8/public.txt bench/plonky3/tables/composed_split8.txt   # the predicate accepts its 16 bits
```

Measured, 2026-09-29, Apple M4 Max, release build, `k = 8`, `x = 200`
(heights `2^17` rows, `2^18` memory, `2^8` witness), `ski-air composed`,
under a load average of about 5 (proving varied from 12.7 to 23.8 s over
five runs):

```
split8   51,824 public cells, 16 bits, a region of 1, 1 segment
         129,965 rows, 215,400 memory cells; 53,450 host contractions
         prove 12.7 s, verify 14.0 s, proof 793 KiB, peak memory 2.0 GB   verified
guess    no match; a match with the blinding off
clear    every bit clear: rejected
wrong    the bits of b + 1 for b: rejected
nonbool  a bit cell I: rejected
forged   a region cell pointing forward: rejected
```

`lake exe composed check` accepts the honest table (`checkPred_sound`) and
rejects the four tampered ones. The standalone `composed-verify` takes
14 to 19 s, of which Lean's statement check is about 6 s and its
comparison of the circuit most of the rest. The cost is the SKIlark
program's: about 6,700 host contractions per bit of `x` (3,300 per
literal bit), on unary numerals and the compiled
kernel's case dispatch. At these heights the proof has under `2^21` LogUp
messages, so a zero denominator aborts it with probability below `2^-102`
(`abort_count`).

### A committed split

`csplit` (`skilark.zk`) commits the hidden number, in a toy commitment:
the verifier `vcsplitB` reads `a`, `b` (8 bits each) and `r` (8 bits) as
literal bits, and accepts when `a + b = x` and `c = Σ a_i A_i + Σ r_j B_j`,
a knapsack (subset-sum) commitment to `a` with randomness `r` under public
weights `A`, `B`. The weights are in `x`, with `c`, so each ripple step
runs the same Joy tree (the kernel's dispatch grows with the program's
distinct quotations); the step also adds `a_i`'s weight to a running sum,
`r`'s weights follow, and the wrapper compares the sum with `c`. `lake exe
skilark cstatement SRC K M SEED X C PUBLIC` checks a statement against the
source, the weights regenerated from the seed.

**It is the shape of a committed range proof, not a secure one.** A
knapsack commitment binds under subset-sum hardness and hides when the
weights and `r` are large; here the `2^16` openings map to 430 sums, none
above 437, and `c = 255` alone opens to 157 values of `a`: the commitment
neither binds nor hides, and a search finds openings at once. Real parameters need a far cheaper kernel, which is what
jets under the hiding would give. That `vcsplitB` accepts exactly the bits
with `a + b = x` and the commitment `c` is tested, not proved: at
`k = m = 2`, every `a`, `b`, `r` and `x` against the right `c`, the next,
and `0` (752 cases), and samples at `k = m = 8`.

```
~/SKIlark/.venv/bin/python -m skilark.zk csplit 8 8 > bench/plonky3/skilark/csplit8/source.ski
lake exe skilark cemit bench/plonky3/skilark/csplit8/source.ski 8 8 1 200 123 77 181 19 20 bench/plonky3/skilark/csplit8
lake exe skilark cstatement bench/plonky3/skilark/csplit8/source.ski 8 8 1 200 255 bench/plonky3/skilark/csplit8/public.txt
bench/plonky3/target/release/ski-air composed bench/plonky3/skilark bench/plonky3/tables
```

Measured, 2026-09-29, Apple M4 Max, release build, `a = 123`, `b = 77`,
`r = 181`, weights from seed 1, `c = 255` (heights `2^19` rows, `2^20`
memory):

```
csplit8  137,792 public cells, 24 bits, a region of 1, 1 segment
         471,888 rows, 672,985 memory cells; 200,884 host contractions
         prove 42.4 s, verify 52.0 s, proof 928 KiB, peak memory 6.5 GB   verified
guess    no match; a match with the blinding off
clear, wrong (another r), nonbool, forged: each rejected
```

`lake exe composed check` accepts the honest table and rejects the
tampered one. At these heights the proof has under `2^23` LogUp messages,
so a zero denominator aborts it with probability below `2^-100`.

### Jets on a SKIlark predicate, in the clear

**Jets cut `split8`'s run to under a tenth.** The closed term `vsplitB x
(boolsT bits)`, the predicate's verifier applied to its public `x = 200`
and the bits of `a = 123`, `b = 77`, run plain and with supercombinator
jets whose table comes from the SKIjack source's own templates
(`JetTable.fileTemplates`): 178 templates give 130 jets and 21,049
licensed roots in the 51,842-cell loaded heap.

```
lake exe skilark jets release/skilark/split8/source.ski 8 200 123 77 DIR   # DIR/split.term, DIR/split.jets
bench/plonky3/target/release/ski-air jets-measure DIR/split.term DIR/split.jets DIR/jet_split.txt
lake exe jets check-src release/skilark/split8/source.ski DIR/jet_split.txt  # ACCEPT: Air.checkJA_sound
```

Measured, 2026-09-29:

```
plain    129,957 rows, 215,393 cells                      (padded CPU 2^17)
jetted    11,483 rows,  74,116 cells, 2,237 instantiations (padded CPU, POP, INSTW 2^14)
          8.8% of the plain rows; the run ends at K over the empty stack
```

Lean accepts the jetted table (`jets check-src`: `checkJA` with the
source's jets, sound by `Air.checkJA_sound` whichever templates proposed
the roots). The plain count is the composed proof's 129,965 rows less the
segment's setup. `jets-measure` does not prove: the prover's check of its
AIRs recomputes the jet tables from the corpus's templates, not a
source's.

`skilark jets` also applies the closure rule of Avon's `ZK-JETS.md` §4
with the bits' cells `[51646, 51839)` private (`split_pub.jets`): it drops
the 104 roots that reach them, and no global, and the run (`JetRun.runJ`,
the counts `ski-air jets-measure` makes) is 11,570 CPU rows and the halt
row, 11,571, still 8.9%; `Air.checkJA` accepts both runs. This is a
measurement in the clear, over the heap of these bits, not the
verifier's table, which `cjets` computes over the blank composed heap
(below).

### Jets on a composed statement, under the closure rule

**The composed heap has private cells, and the jet table must avoid
them.** A predicate statement's heap (`CompM.cHeap`) holds the bit slots
and the witness region at addresses `[3, 3 + N + W)`, and public cells
point into them. Lean computes the statement's jet table over the blank
heap, the verifier's, with the closure rule: a root or a global is a cell
whose every cell below, by application, is public
(`Air.jetTableC`, `JetTable.pubCells`). The verifier's check
(`Air.jetStmtC`) recomputes that table, and checks its roots licensed
(`rootsOKB`) and their closures public (`publicB`) over the blank heap;
accepted, the roots are licensed over the heap of every witness
(`Air.jetStmtC_sound`, from `termAt_public` and `rootsOK_filled`).

```
lake exe skilark cjets SRC PUBLIC OUT [--no-rule]      # the table, over the blank heap
lake exe skilark cjets-statement SRC PUBLIC OUT        # ACCEPT: Air.jetStmtC_sound
lake exe skilark cjets-measure SRC PUBLIC WITNESS      # runs over the filled heap
```

Measured, 2026-09-30, on `bench/plonky3/skilark/{split8,csplit8}`:

```
split8   blank heap 51,841 cells, private [3, 20)
         without the rule 21,043 roots: 47 roots and 3 globals reach a private cell
         the rule  20,996 roots, 129 jets; cjets-statement ACCEPT
         plain     129,964 CPU rows
         the rule   11,598 CPU (8.9%), 8,614 POP, 12,363 INSTW; halts at K over the nil; checkJA ACCEPT
csplit8  blank heap 137,817 cells, private [3, 28)
         without the rule 57,245 roots: 71 roots and 5 globals reach a private cell
         the rule  57,174 roots, 182 jets; cjets-statement ACCEPT
         plain     471,887 CPU rows
         the rule  157,680 CPU (33.4%), 105,544 POP, 76,037 INSTW; halts at K over the nil; checkJA ACCEPT
```

**The hazard is real.** The table without the rule passes `rootsOKB`
over the blank heap and fails it over the honest filled heap, for both
statements: a root or a global it licenses reads a different term once
the bits are in (on `split8`, the global `G 25` is `K ⬝ slot₀`, `K (K I)`
blank and `K K` with bit 0 set; the rule moves it to a public
`K (K I)`). That table fails `publicB` (`cjets` reports it). The
statement check refuses it (`--no-rule`), and a hand-edited table, by
text: Lean's recomputed table is the only one accepted, and `rootsOKB`
and `publicB` re-check it, since the table generator is not trusted.
`cjets-measure` measures; it does not check the witness. `checkJA` checks each run from the filled machine,
which also checks the statement's table licensed there. The saving on
`csplit8` is a third, against `split8`'s tenth. On `csplit8`, `cjets`
takes 151 s (it computes the table with the rule and without) and
`cjets-statement` 70 s, each in under 80 MB.

### The composed circuit with jets, in zero knowledge

**A composed statement proves with jets under hiding** (`src/compj.rs`,
Avon's `ZK-JETS.md` milestone 4). Ten tables: the composed circuit's
five and the jet circuit's five. The CPU is both CPUs at once: the jet
columns at 121–130, three blinding blocks at 131–145, the restart columns
at 146–148, so `INST` (selector 11) and the restart are distinct columns.
Seven blinding tuples span the eight private tables as a tree,
`WIT —a— CPU —b— MEM` and `CPU —c— POP —d— INSTW —e— TMPL —f— HDR —g—
ROOTS`. The provider tables are padded to `2^8` rows, as the hiding PCS
needs.

The verifier holds the statement, its jet table (`skilark cjets`) and
the SKIjack source the templates come from. The statement fixes all four
free heights before the run: its line `log R M Lp Li` names the CPU's,
the memory's, POP's and INSTW's, each in `[8, 20]` (`composed budget`
writes it from a composed statement). A composed statement and one with
jets are distinct: each checker refuses the other's. Lean checks the
statement (`composed statement-jets`), then the jet table and the AIRs in
one call (`lake exe circuit compare-compJ SRC -`):
`Air.jetStmtC` on the table's bytes, `jetFitB`, and the ten AIRs against
`Circuit.compJAirs`, constraint for constraint. The verifier pins all ten
heights.

```
lake exe composed budget PUBLIC LP LI JPUBLIC                             # the statement with jets
lake exe skilark cjets SRC JPUBLIC JETS
ski-air export-compj JPUBLIC JETS | lake exe circuit compare-compJ SRC -  # MATCH, ten AIRs
ski-air compj-prove JPUBLIC JETS SRC WITNESS PROOF                        # proves, then verifies
ski-air compj-verify JPUBLIC JETS SRC PROOF                               # VERIFIED
ski-air compj-tamper JPUBLIC JETS SRC WITNESS                             # an unbalanced tree: REJECTED
ski-air compj-prove-table JPUBLIC JETS SRC TABLE PROOF                    # proves a table another producer wrote
```

Avon writes the witness table (`avon witness --statement=JPUBLIC
--jet-table=JETS WITNESS`, Avon's `docs/ZK-JETS.md` milestone 8), byte for
byte the one `compj-prove … TABLE` writes; `compj-prove-table` proves it,
reading each instantiation row from the table as `jet-prove` does. Avon's
`make zk-jet-witness-check` runs `and`, `or` and `split8` through both.

Measured, `and` and `or` 2026-09-30, `split8` and `csplit8` 2026-10-09:

```
statement             CPU rows (INST)   POP      INSTW    memory    heights CPU mem POP INSTW   prove     proof
split8                 11,599 (1,952)    8,018   12,363    74,246   2^17 2^18 2^14 2^14       11.9 s    1.11 MB
csplit8 at log 18 19  157,681 (44,427) 101,300   76,037   330,512   2^18 2^19 2^17 2^17       29.2 s    1.17 MB
and (3 segments)          404 (69)         116       17       889   2^11 2^11 2^8  2^8         0.14 s   0.78 MB
or (3 segments)           220 (41)          67       10       673   2^11 2^11 2^8  2^8         0.16 s   0.78 MB
```

The prover runs a projection jet's instantiation as the machine's step,
as Lean's honest run does ("The traces against Lean's honest tables",
above). Avon's witness table still counts it an instantiation (2,250 for
`split8`, 46,549 for `csplit8`); the rows are the same.

`and` and `or` take `split8`'s source's templates, so their segments
restart between instantiations. Without jets `csplit8` needs `2^19` rows
and `2^20` memory and proves in 42 s; with them it fits `2^18` and
`2^19`. Verifying takes 17 s on `split8` and 112 s on `csplit8`, nearly
all of it Lean's check of the jet table. On `split8`, `and` and `or`
the wrong, clear and non-Boolean witnesses are refused (a segment does not
end at `K` over the nil) and the forged region is rejected (the witness
table). A proof checked against a statement with another budget is
rejected (the heights), and an unbalanced blinding tree fails LogUp's
terminal sum.

**What an accepted proof shows is proved** (milestone 5,
`Circuit.compJExport_sound`): for the jet table Lean checked and AIRs
with `compJAirs`' normal forms, the memory holds bits and a region whose
witness makes every term evaluate to `K`; for a predicate, `V x` accepts
the bits (`predJExport_sound`). An instantiation is weak reduction, so a
jetted run proves evaluation up to weak reduction of the value; a value
with `K`'s head and arity is `K` (`CompM.chead_K`), so the statement is
proved exactly. `compj-prove … TABLE` writes the run as a table, and
`lake exe composed check-cj SRC PUBLIC TABLE` decides it (`CompM.checkCJ`):
ACCEPT on `split8`, `and` and `or`, REJECT on a table with one row's head
or one segment's end changed.

**The honest tables are accepted** (milestone 6,
`Circuit.compJ_complete_log`): a jetted run within `2^R` rows, `2^Lm`
memory cells and `2^Lp`, `2^Li` POP and INSTW rows, all at most `2^20`,
gives tables that AIRs with `compJAirs`' normal forms accept at those
heights. The program and segment tables are the public ones, and the
tables decode back to the memory and the run. `compJStmt_complete_log`
takes the jet table Lean checks (`jetStmtC`).

**The transcript hides the witness** (milestone 7,
`Circuit.compJ_transcript`, `Ski/ZK/CompJ.lean`): over a hiding PCS, a
simulator that holds only the statement matches the real transcript on
every event, up to the non-generic challenges, the aborts and the PCS's
distance. It is `transcript_zkN` for the tree of eight private tables
and seven tuples that `compj.rs` blinds. The published terminals are the
tree's view of the unblinded ones (`compJ_chain`), which sum to minus the
public program and segment tables' (`compJ_sum`, by LogUp over balanced
tables). The honest tables meet the hypotheses (`CRun.honest_zk`). Every
height is the statement's, so the transcript's shape is fixed before the
witness.

What the theorem rests on:
- **The statement comes first.** The verifier fixes the statement, its
  budgets included, and the source `SRC` before the witness exists. A
  prover who wrote its own statement per witness could choose `R`, `M`,
  `Lp` and `Li` and so publish the sizes of its run; one who chose `SRC`
  would publish which templates it used.
- **The model is honest-verifier zero knowledge.** It draws the
  challenges uniformly, and the simulator's `psim` must be fixed by the
  statement alone. The real challenges are Fiat–Shamir outputs, a step
  taken in the random-oracle model and not formalized.
- **`PCSCloseN` carries the committed traces' hiding**: the main and
  permutation traces, the quotient, FRI and the openings. The theorem's
  own content is the eight terminals' tree argument, with its error terms
  for non-generic challenges and aborts.
- **The `2^8` floor has a margin of 48 values, 40 by Plonky3's count.**
  With 100 FRI queries at arity 2 a table opens 200 base-field points and
  two out-of-domain points, `|S| + 4 |Z| = 208`, against its 256 random
  rows (`masks_hide`); Plonky3's `HidingFriPcs` asks `2 (100 + 8) = 216`.
  The witness table and the providers sit at `2^8`, and POP and INSTW do
  too at a budget of 8. `ski-air mask-margin PROOF…` prints each proof's
  margin from its heights, and `release/verify.sh` (step 14) checks every
  released zero-knowledge proof; `ski-air fs-budget` prints it after each
  hiding verification. More queries or a wider fold would need a higher
  floor.

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

## Fiat–Shamir, round by round

Plonky3 draws every challenge by hashing the transcript, so a cheating
prover can retry each round as often as it can hash. A proof is as strong
as its weakest round: at `λ` bits each attempt at that round succeeds with
probability at most `2^-λ`, and a round's proof of work multiplies an
attempt's cost by `2^b`. Lean proves the counting step: over `q` adaptive
hash calls, a round whose bad answers are a fraction `ε` of all answers is
hit with probability at most `q ε`, and `b` bits of grinding divide that by
`2^b` (`fs_attempts`, `grind_count`, `Ski/ZK/FSRound.lean`). That an
accepted false proof must contain such a call, round-by-round soundness,
is assumed; with the verifier's own `k` hash calls the bound is
`(q + k) · max ε`. For the LogUp
round Lean proves `ε` itself: `q` calls pass the check with unbalanced
tables, which the prover may change at every call, with probability at
most `q · M (W + 2) / (P^4 · 2^b)` (`logup_fs`).

`ski-air fs-budget` prefixes any verifier command and prints the proof's
rounds after it verifies:

```sh
ski-air fs-budget compj-verify JPUBLIC JETS SRC PROOF
ski-air fs-budget composed-verify PUBLIC PROOF
ski-air fs-budget sudoku-verify PUBLIC PROOF
ski-air fs-budget jet-verify CORPUS JETS NAME PROOF
```

The witness and corpus test runs (`ski-air witness …`, `ski-air`) print
one for each proof they verify; a command that prints none says so.

The rounds of a batch proof (`src/fsbudget.rs`): the constraint
combination (`ali`), at the batch's total constraint count; the
out-of-domain point (`deep-ali`), a union over the AIRs, each at its own
trace length; the low-degree test, its opening batch and the hash's
collision cap, from Plonky3's `p3-security` for one instance at the longest
trace batching every column; and LogUp, from Lean's `logup_accept`, in a
list-decoding regime once for each of the list's candidate traces. The
proven figures rest on the published proximity-gap bounds, the conjectured
ones on the random-words conjecture, all on the hash behaving as a random
oracle.

Every released proof uses Plonky3's benchmark FRI parameters (rate `1/2`,
100 queries, 16 bits of query grinding) and grinds 10 bits before the
opening batch, 5 before the lookup and 3 before the out-of-domain point
(`GRIND_*`):

| proof | proven (unique / list decoding) | conjectured | binding round | LogUp |
|---|---|---|---|---|
| `3 sumto`, jetted | 57.5 / 65.9 | 107.9 | LogUp | 107.9 |
| Sudoku | 57.5 / 65.9 | 105.0 | FRI commit | 106.4 |
| composed `and`, `or` | 57.5 / 65.9 | 110.0 | FRI commit | 111.3 |
| `split8` | 57.5 / 65.9 | 103.0 | FRI commit | 105.1 |
| `csplit8` | 57.5 / 65.9 | 101.0 | FRI commit | 103.1 |
| `split8` with jets | 57.5 / 65.9 | 102.2 | batch | 103.2 |
| `csplit8` with jets | 57.5 / 65.9 | 101.2 | batch | 101.9 |

The proven figures are bound by the low-degree test, which only more
queries move. Before the grinding the conjectured figures were 91 to 100,
bound by the opening batch. 128 bits is out of reach with this field and
hash: the constraint combination has no grinding site and stops at 114 to
116 bits (`|EF| ≈ 2^123.6` over 162 to 381 constraints), and a digest of
eight BabyBear elements caps collisions at 123 bits.

**What the transcript binds.** Before its first challenge the transcript
absorbs the batch's shape, every instance's degree bits, the main
commitment, the public values and the preprocessed commitment. Plonky3
absorbs nothing of the constants inside the AIRs (the CPU's start head,
stack and counter, the Sudoku accept marker, the probe and restart
parameters), so a prover that named its statement after the challenges
could solve for one. Every proof therefore carries, as the CPU
instance's public values, a Poseidon2 digest of all the AIRs hold, which
the verifier recomputes from the AIRs it builds from the statement
(`src/stmt.rs`): a proof checks against one statement only. The encoding
destructures every AIR exhaustively, so a new field fails to compile until
it is encoded, and it is injective (tagged, length-prefixed, 16-bit
halves). No constraint reads the digest, so the Lean circuits are
unchanged.

**Grinding.** Every configuration grinds 10 bits before the opening
batch, 5 before the lookup challenges and 3 before the out-of-domain point
(`GRIND_*`, `src/main.rs`), with the benchmark FRI parameters otherwise.
That brings every round of every released proof to 100 conjectured bits.
The proven figures stay where the low-degree test holds them.

**Proven 100 bits, a future option.** 203 queries at rate `1/2` reach it
for every released proof, with the same grinding. Two costs follow. The
query part, most of a proof, roughly doubles. And the hiding PCS's masking
budget, `2 (queries + 4 · opening points)` random rows a table, which
`masks_hide` also needs, rises from 216 to 422: the tables of `2^8` rows
(the composed and hidden-term circuits' witness and minimum heights) must
grow to `2^9`, which changes their statements' heights. Rate `1/4` (124
queries) or `1/8` (102) shortens proofs but doubles or quadruples the
low-degree extension, and does not reach 100 bits for `csplit8`. 128 bits
needs a larger extension field and a wider digest, a change to every Lean
theorem over `EF`.

## What this is not

- **The corpus proofs, plain, jetted and probed, are not zero
  knowledge.** Their PCS is not hiding, and the first row loads the whole
  term in the clear. Only the probe proof binds an output. The Sudoku and
  hidden-term proofs are hiding, and bind their accepting output.
- **Plonky3's zero knowledge is statistical and unaudited.** Plonky3 marks
  its randomization of the trace as statistically hiding only, and
  `HidingFriPcs` enforces a masking budget (trace height at least
  `2 · (queries + 4 · opening points)`) that every Sudoku table meets.
- **The zero-knowledge argument is formal, over a hiding PCS.**
  `Ski/ZK/Transcript.lean` and `TranscriptN.lean` give a simulator for
  the whole transcript (`transcript_zk`, the three-table instance of the
  tree's `transcript_zkN`; per circuit `sud_transcript`, `wit_transcript`,
  `comp_transcript`): from public data it matches the real transcript on
  every event within a fraction `P^2 / P^4 + M / P^4 + ε / NR` of the
  draws, `M` the LogUp messages. The model: public-coin challenges `α`
  and `β`, uniform and independent of the prover's randomness
  (honest-verifier zero knowledge; Fiat–Shamir in the random oracle model
  makes it non-interactive, a standard step not proved here); and one
  assumption, `PCSClose ε`, that what the PCS commits and opens matches a
  simulator's output from the challenges and the published terminals,
  each event's count over the `NR` draws of the PCS's randomness within
  `ε` (`PCSHides`, the exact case, gives `ε = 0`).
  The simulator is fixed by the statement before the witness, and the
  theorem holds for every witness. A PCS that shows nothing satisfies the
  assumption (`pcsHides_unit`), so the part published in the clear is
  simulated with no assumption. The composed proof's segment table has
  private multiplicities, but the honest prover's are fixed by the
  statement, one restart into each segment after the first
  (`segs_honest`); the completeness theorems return exactly the public
  program and segment tables the simulator reads. Its core, for the terminals,
  is that `Ski/ZK/Circuits.lean` proves that two balanced table sets for one
  statement publish their witness, CPU and memory terminals with the same
  distribution over the two blinding tuples (`sud_zk`, `wit_zk`,
  `comp_zk`), counted exactly over all `P^8` pairs, and within `2 P^4` of
  them on the draws where every inverse exists (`*_zk_valid`). Its gaps:
  - `Generic β` (the combiner matrix invertible) fails exactly when `β`
    lies in the subfield `F(x^2)` (`generic_iff`): `P^2` of the `P^4`
    challenges (`nongeneric_count`), about `2^-62`, which dominates the
    bound.
  - The challenges are the verifier's, uniform and independent. In
    Plonky3 they are Fiat–Shamir outputs of the trace commitments, which
    contain the blinding columns; that step rests on the hiding PCS in the
    random oracle model, unproved.
  - The composed proof's segment table is private, but for accepting
    runs its multiplicities are `1` for segments `1..n-1` and `0`
    elsewhere: proved (`segs_honest`), and what `composed.rs` writes.
  - The prover aborts on a zero LogUp denominator, and whether it does
    depends on the witness. Every bus prefix is `α` plus an offset free
    of `α`, so for any tables, `β` and blinding at most one `α` per
    message aborts (`abort_count`, `Ski/ZK/Abort.lean`): at most `2^-103`
    for Sudoku (under `2^20` messages), `2^-109` for the hidden term and
    `2^-108` for the composed statement.
  - Everything committed and opened rests on Plonky3's hiding PCS,
    assumed (`PCSClose ε`), statistical and unaudited.
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
