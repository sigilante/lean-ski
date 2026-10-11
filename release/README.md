# Release: `3 sumto`, proved, and its output `[6]`; statements in zero knowledge

This directory holds two proofs about the SKIlark program `3 sumto`,
compiled to SKI:

- **It halts.** A proof of the jetted run: the term evaluates to weak
  head normal form.
- **It decodes to `[6]`.** A proof of the probe segments:
  applied to marker atoms, the term reads, constructor by constructor, as
  the result `RVal [6]` (`Decodes sumto_us (.val [.num 6])`).

Anyone with a lean-ski checkout can check both:

```
release/verify.sh
```

It needs elan (Lean) and cargo (Rust), and nothing from Avon. The first
run builds Lean's checkers and the verifier, which takes minutes. After
that it runs in about two minutes on an Apple M4 Max; `QUICK=1
release/verify.sh` skips `csplit8`'s proof with jets, about 8 seconds of
them. It prints one `ok` line
per check, then `VERIFIED: …`, and exits nonzero if any check fails. A
refusal counts only with its expected reason: a forgery meant for the proof
check that the statement check refuses instead is a failure. It is not
part of CI.

## Each claim and its check

Each released claim, where it lives, the step of `verify.sh` that checks
it, and the theorem an accepted check yields. The steps also refuse the
forgeries the sections below list.

| Claim | Release files | Step | Lean |
|---|---|---|---|
| `3 sumto` halts, its jets licensed | `sumto/`, `sumto/jets/` | 1–4 | `jetExport_sound`, `Air.checkJA_sound` |
| `3 sumto` decodes to `[6]` | `sumto/` | 5 | `probeExport_sound`, `Air.checkPA_decodes` |
| A forged jet table proves nothing | `forgeries/omega/` | 3 | the statement check refuses it |
| The ∨ and the ∧ of two atoms, hidden | `composed/` | 6 | `compExportG_sound` |
| Each proof binds its CPU constants (start registers, acceptance), which no committed table holds | `composed/`, `entropy/` | 6, 13 | none: the statement digest, tested by `ski-air composed-digest-bound` |
| Some 16 bits make `split` accept `x = 200` | `skilark/split8/` | 7 | `predExport_sound` |
| The same, with a toy commitment | `skilark/csplit8/` | 8 | `predExport_sound` |
| Wikipedia's Sudoku has a hidden solution | `sudoku/` | 9 | `sudExport_sound` |
| `split` and `csplit` with jets, hidden | `skilark/*/jets/` | 10–11 | `compJExport_sound`, `Air.jetStmtC_sound` |
| A Poseidon2 preimage of `h` | `p2/` | 12 | `p2preExport_sound` |
| A hidden hand-off over one commitment | `p2/` | 12 | `p2commitExport_sound`, `p2commit_chainB` |
| A kernel's poke with a private entropy reply | `entropy/` | 13 | `entropyExport_sound` |
| Every zero-knowledge proof has the random rows its hiding needs | all but `sumto/` | 14 | `masks_hide`'s hypothesis, `\|S\| + 4\|Z\| ≤ n`, 48 to spare |

The theorems are in namespace `Circuit` unless prefixed.

## What is verified

1. **The term.** `sumto/corpus.txt` holds lean-ski's corpus row `sumto_us`:
   `3 sumto`, compiled with its own quotation table (`Ski/Corpus.lean`;
   `Ski/Table.lean` pins the term to the kernel's compilation of the
   program, `SumTable.sumto_us_eq`). The line's middle field, the
   contraction count skijack's reducer reports, is informational: the
   proof claims nothing about it, and only step 1's comparison checks it. `verify.sh` checks the file against what
   `bench/Dump.lean` prints.
2. **The jet table.** `sumto/jets/sumto_us.jets` lists 759 licensed
   roots and 76 jets. The verifier reads the corpus line and the jet file
   once and pipes those bytes to Lean's `lake exe jets statement-stdin`,
   which reads no file. It confirms that the jet file is exactly the jet
   table of the term, and that every root passes `Air.rootsOKB` over the
   term's loaded heap. That gives `Air.RootsOK` (`Air.rootsOKB_sound`).
   The verifier then uses those same bytes, so what Lean checked is what
   it proves over. Corpus lines are split as Lean splits them, on spaces.
3. **The halting proof.** `sumto/sumto_us.proof` is a Plonky3 batch STARK
   over BabyBear, 376,024 bytes, over the eight tables of
   `bench/plonky3/src/jets.rs`. `ski-air jet-verify` checks it against the
   term and the jet table alone.
4. **Forgeries are refused:**
   - the proof with one byte changed;
   - the proof offered for another term (`compiled_up`);
   - the proof with a byte appended (a proof is one byte string);
   - a name that is a path (names are identifiers, on both sides);
   - a proof that Ω, which diverges, halts, made over a forged jet table
     (`forgeries/omega`). It is offered once with the forged table, and
     once through a FIFO that answers the first read with the honest table
     and the second with the forged one. The honest table licenses
     nothing, since Ω's only templates are bare combinators, and ski-air
     refuses a table with no rows. So `verify.sh` also checks that the
     verifier read the honest table and never the forged one.

   An independent check from a clean clone found these holes. First, an
   absolute name let Lean check one file while the verifier read another.
   After names became identifiers, the FIFO let them read different
   bytes. Each let the Ω forgery verify. So did one more: a copy of the
   bytes in a temporary directory, which a process able to rename entries
   in a shared `$TMPDIR` replaced before Lean read it. Reading once and
   piping the bytes to Lean closes all three. The standing forgeries fail
   on the vulnerable builds (`a8ec55f`, `0b2fbcf`) and pass on this one,
   checked with the Ω proof made for their CPU layout. The CPU has since
   gained the probe kinds, and the Ω proof was remade for it: the old
   builds now reject it for its layout, so they no longer show the holes.
5. **Lean's own check of the witness.** `lake exe jets check` accepts
   the witness table, `sumto/sumto_us.table` (`Air.checkJA_sound`). A table
   certifies its own term, on its first line. `verify.sh` binds it to the
   corpus row twice: it compares that line with the row's term, and runs
   Lean's checks with `--row sumto_us`, which refuse any other term.
6. **The output proof.** `sumto/sumto_us.probe.proof`, 430,334 bytes, is
   over the same eight tables and two more, PLAN and PW
   (`bench/plonky3/src/probe.rs`). `ski-air probe-verify … val 6` checks
   the jet file as in item 2, takes the plan of `[6]` from Lean (`lake exe
   jets plan val 6`, `Air.planOf`), and checks the proof against the term,
   the jet table and the plan. Offered for `[5]`, for the error outcome or
   for `[6, 0]`, spelled `06`, with one byte changed, or in place of the
   halting proof, it is refused (an outcome has one spelling: plain
   decimal). A number `n` takes `n + 1` probes, so Lean gives no plan
   past 65,536 segments. `lake exe jets check-probe` accepts its table,
   `sumto/sumto_us.probe.table`, for `[6]` (`Air.checkPA_decodes`),
   rejects it for `[5]`, and refuses it as row `compiled_up`, which also
   decodes to `[6]`.

7. **Composed statements in zero knowledge.** `composed/or` and
   `composed/and` each hold a statement, `public.txt`, and a proof: that
   the prover holds bits and a witness realizing the `∨`, or the `∧`, of
   two atoms of Part II's logic (`Ski/WitnessExamples.lean`), the witness
   hidden. `verify.sh` first checks that each `public.txt` is Lean's
   statement of its formula (`lake exe composed emit`). `ski-air
   composed-verify PUBLIC PROOF` then pipes the statement's bytes to Lean's
   check (`lake exe composed statement -`) and verifies the proof, read
   from its file as one byte string, against the statement alone. A proof
   with one byte changed or a byte appended, a statement with a hidden cell
   exposed, and the `∨` proof offered for the `∧` statement are refused.
8. **A SKIlark statement in zero knowledge.** `skilark/split8` holds the
   SKIjack source of a SKIlark predicate (`source.ski`), a statement and a
   proof. `lake exe skilark statement` compiles the source in Lean and
   checks that the statement is its predicate for `x = 200` over 16
   literal bits; offered
   as `x = 201`, or as `x = 712`, which 8 bits cannot hold, it refuses.
   `ski-air composed-verify` checks the proof; with one byte changed, it
   is refused.
9. **A committed split.** `skilark/csplit8` holds the source of `csplit`,
   a statement and a proof. `lake exe skilark cstatement` compiles the
   source and checks that the statement is its predicate for `x = 200`
   and the commitment `c = 255`, the weights regenerated from seed 1;
   offered as `c = 256`, it refuses. `ski-air composed-verify` checks the
   proof; with one byte changed, it is refused.

10. **A Sudoku in zero knowledge.** `sudoku` holds the statement of
    Wikipedia's puzzle and a proof that the prover holds its solution, the
    grid hidden. `verify.sh` checks that `public.txt` is Lean's statement
    (`lake exe sudoku emit`); `ski-air sudoku-verify PUBLIC PROOF` pipes it
    to Lean's check (`lake exe sudoku statement -`), has Lean compare its
    AIRs with `Circuit.sudAirs`, and verifies the proof. With one byte
    changed, a byte appended, or a statement with its last cell removed, it
    is refused.
11. **`split8` with jets, under hiding.** `skilark/split8/jets` holds the
    statement with jets (`public.txt`: the predicate's statement whose line
    `log 17 18 14 14` fixes the CPU's, the memory's, POP's and INSTW's
    heights), its jet table (`split8.jets`) and a proof. `lake exe skilark
    statement` checks that the statement is `vsplitB`'s for `x = 200`, and
    names its budgets. `ski-air compj-verify` pipes the statement to Lean
    (`composed statement-jets`), has Lean check the jet table
    (`Air.jetStmtC`: it is the table Lean computes from the source's
    templates over the statement's blank heap, every root licensed and its
    closure public, so licensed over every filled heap) and compare the ten
    AIRs with `Circuit.compJAirs`, and verifies the proof. With one byte
    changed, offered for the plain statement, for a statement with POP's
    budget `2^15`, or with the jet table Lean computes without the closure
    rule, it is refused.
12. **`csplit8` with jets, under hiding.** `skilark/csplit8/jets`, the
    same at `log 18 19 17 17`, a height below the plain proof's.
13. **The Poseidon2 jet.** `p2` holds three statements and their proofs.
    `verify.sh` checks that each statement is Lean's: `p2pre`'s by
    re-emitting it (`lake exe composed emit-p2`); the hand-off's, which
    commit to a fresh secret value with fresh randomness Lean does not
    know, by `lake exe
    composed check-handoff`, which takes the commitment from the files and
    fixes everything else, the two documented patterns and the heights. It
    also checks that the commitment is not the fixed test randomness's.
    - `p2pre.public.txt` is `p2pre h`, a preimage of `h` under the
      permutation. `ski-air compp-verify` pipes it to Lean (`composed
      statement-p2`), has Lean compare the nine AIRs with
      `Circuit.compPAirsG`, and verifies the proof. With one byte changed, a
      byte appended, a bit cell exposed in the statement, or offered for
      another statement, it is refused. Offered for Lean's statement of
      another `h` (test vector 0) at the same heights, it passes the
      statement check and the heights, and the proof check refuses it: the
      proof binds its statement.
    - `handoff1.public.txt` and `handoff2.public.txt` are `p2commit c pat`
      for one commitment `c` and two patterns: the value's element 1 is 840,
      and its element 0 is odd. `ski-air compp-chain` reads each statement
      once, has Lean check that the two form a chain (`composed chain-p2`,
      `P2Commit.chainB`), verifies both proofs against those bytes, and
      prints `CHAIN OK`. It refuses the chain with the proofs swapped, paired
      with `p2pre`, or through FIFOs that answer Lean's read with the
      hand-off and the verifier's with `p2pre`.
14. **A poke whose event is an entropy reply.** `entropy` holds two
    statements and their proofs. `source.ski` is Avon's entropy kernel
    (avon `tests/kernel/entropy.ascii.ski`, which Lean's front end and
    SKIjack's compile to the same term) with two checks. `verify.sh`
    compiles it in Lean and checks that each statement is the predicate
    `entropyV 128` on `[kernel [0 check]]` (`lake exe entropy statement`):
    some 128 literal bits, given to the kernel as the reply `[0 [0 bits]]`,
    make the check accept the poke. `ski-air composed-verify` checks each
    proof. Each statement is refused read as the other's, and each proof
    offered for the other's statement; each proof is refused with one byte
    changed.
    - `bootok.public.txt`: the poke emits no effects and the new kernel's
      peek 0 counts one reply. It reads no bit.
    - `firstset.public.txt`: the same, and the new kernel's peek 3, the
      reply's first bit, is 1. Its proof discloses that bit.

## What the proofs mean, and what they do not

**The halting proof.** An accepted table satisfies `Air.AcceptsJ` from
the loaded term with licensed roots. By `Air.air_sound_jet`, the term
then evaluates in normal order to a value that weakly reduces to the
table's final value, with the same head combinator and arity. So
`3 sumto` **halts**, and the proof fixes the head and arity of its value.

**The composed proofs.** A formula of atoms under `∧` and `∨` compiles
to a list of terms, each of which must evaluate to `K` on literal bits and
a hidden witness (`Ski/Compose.lean`). An accepted table runs one segment
per term (`Ski/Composed.lean`), and its bits and witness read back as a
realizer of the formula (`CompM.checkC_realizes`). The proofs hide the
bits and the witness: a hiding PCS, heights each statement fixes, and blinded
lookup sums, as in the Sudoku proof. Lean proves that the published lookup sums
hide the witness (`Circuit.comp_zk`, `Ski/ZK/`); the hiding PCS is
assumed. They are
randomized, so they do not regenerate byte for byte. That the prover
*knows* a realizer rests on the STARK's knowledge soundness, assumed. The
verdict names the formula: whoever reads it compares that formula with the
one they meant.

**The SKIlark proof** (`skilark/split8`). A predicate statement over
literal bits: the SKIlark verifier `vsplitB`, compiled from `source.ski`,
reads 16 hidden bits, which the circuit constrains to `K` or `K I`, and
never a hidden term. An accepted proof holds 16 Booleans on which
`vsplitB` accepts `x = 200` (`Circuit.predExport_sound`). On such bits
`vsplitB` accepts exactly two 8-bit numbers adding up to 200, as tested,
not proved: every bit pattern for numbers of 2 and 3 bits, all 4,096
cases for 4 bits once, and samples for 8 bits. The
claim is weak: some pair of 8-bit numbers adds up to any 8-bit `x`, so the
proof shows only that `200 < 2^8`. It demonstrates a SKIlark program
proving over hidden data; a range proof needs a commitment binding the
hidden number to something public. The proof runs at `2^17` CPU rows and
`2^18` memory cells, heights the statement names.

**The committed split** (`skilark/csplit8`). The same over 24 literal
bits: `a` and `b` add up to 200, and `a`'s bits with 8 random bits `r`
sum, under public weights, to the commitment `c = 255`: a knapsack
commitment to `a`. The proof holds 24 Booleans on which `vcsplitB`
accepts (`Circuit.predExport_sound`); that it accepts exactly these
conditions is tested, not proved. At these sizes the commitment neither
binds nor hides: `2^16` openings map to sums of at most 437, and a search finds
one at once. It is the shape of a committed range proof; real parameters
need a cheaper kernel. It runs at `2^19` rows and `2^20` memory cells.

**The Sudoku proof** (`sudoku`). The statement is the formula of
Wikipedia's puzzle (`Sudoku.sudokuExpr`) over 729 hidden Boolean cells,
one per digit and square. An accepted proof holds a grid on which the
formula's run reaches the accepting marker: a solution of the puzzle
(`Sudoku.sudoku_sound`). The grid is hidden as in the composed proofs
(`Circuit.sud_zk`, `Circuit.sud_transcript`). It runs at `2^16` rows,
`2^16` memory cells and `2^10` inputs.

**The proofs with jets** (`skilark/*/jets`). The same predicates, proved
with the composed circuit with jets: a licensed template's instantiation
takes one CPU row where the machine took many. `split8` runs in 11,167 CPU
rows (1,520 instantiations, 7,154 POP and 11,931 INSTW rows) against
129,964 without jets. `csplit8` runs in 118,222 (4,968 instantiations,
22,382 POP and 36,578 INSTW rows) against 471,887, and fits `2^17` rows
and `2^18` memory cells against the plain proof's `2^19` and `2^20`.
Avon wrote each witness table (`avon witness --statement`, Avon's
`docs/ZK-JETS.md` milestone 8), byte for byte the table lean-ski's prover
writes, and ski-air proved it (`compj-prove-table`). What an accepted
proof shows is
the plain proof's: some literal bits on which the predicate accepts
(`Circuit.predJExport_sound`, for the jet table Lean checked). An
instantiation is weak reduction, so a jetted run proves evaluation up to
weak reduction of the value; a value with `K`'s head and arity is `K`
(`CompM.chead_K`), so the claim is exact. The honest tables are accepted
(`Circuit.compJ_complete_log`). The transcript hides the bits
(`Circuit.compJ_transcript`), under the conditions the plain proofs share
-- a hiding PCS, Fiat–Shamir in the random-oracle model, a simulator fixed
by the statement -- and one of its own: the verifier fixes the statement,
its budgets included, and the source before the witness. The jet table is
public; which templates the run used, and how often, is not.

**The output proof.** A result is read by probing: the term, applied to
three fresh marker atoms, must head-reduce to the marker of `RVal`
applied to one field; that field, applied to two fresh markers, to the
marker of a stack cell applied to its two fields; and so on down the
value, one probe per constructor. That is `Decodes` (`Ski/Decode.lean`),
the reading the compiler's contracts use. `[6]` takes 11 probes, the
plan's segments. An accepted table runs them in one table: each segment
starts with a probe row that writes its markers and applies its term to
them, runs by machine transitions and jet instantiations, and ends where
the head is the expected marker with exactly the expected fields on the
stack. By `Air.air_probe_decodes`, an accepted table proves that the
term decodes to the outcome. Lean proves the same outcome about the term
by its derivation (`SumTable.us_six`); this proof reaches it from the
run.

The limits:

- **The link from Plonky3 to Lean is proved from the constraints, and
  assumes the STARK.** The verifier checks the AIRs it verifies with
  against Lean's `jetAirs` and `probeAirs` (`lake exe circuit
  compare-jets`, `compare-probe`), and Lean proves that every table they
  accept satisfies `Air.AcceptsJ`, or with probe segments `Air.AcceptsP`
  (`jetExport_sound`, `probeExport_sound`). That an accepted proof has
  such tables is Plonky3's STARK and LogUp soundness, assumed. Lean also
  checks the tables these proofs cover (items 5 and 6), though nothing
  links a table to a proof's bytes. The tables and proofs regenerate,
  byte for byte.
- **The verifier trusts its build.** The statement check runs the Lean
  project of the checkout the verifier binary was built in, with `lake`
  from `PATH`; `$LEAN_SKI` is consulted only when that is absent.
- **The proof is not zero knowledge**, and has nothing to hide: the term
  is public.
- **Security is Plonky3's benchmark FRI setting, with grinding**: 10 bits
  before the opening batch, 5 before the lookup and 3 before the
  out-of-domain point, so every round reaches at least 101 conjectured
  bits; proven, 57.5 to 65.9 (`ski-air fs-budget`, `bench/plonky3/README.md`,
  "Fiat–Shamir, round by round").
- **Each proof binds its whole statement**: a digest of every AIR's
  constants is a public value the transcript absorbs (`bench/plonky3/src/stmt.rs`).

**The Poseidon2 jet's proofs.** An accepted proof of `p2pre h` holds in
its memory 496 bits whose sixteen 31-bit elements permute to a state
beginning with `h` (`Circuit.p2preExport_sound`). An accepted proof of
`p2commit c pat` holds bits whose compression is `c` and which meet `pat`
(`Circuit.p2commitExport_sound`). Two accepted proofs that `compp-chain`
accepts give one value meeting both patterns, or a collision of the
compression read from the two proofs' tables (`Circuit.p2commit_chainB`).
These rest on the stated assumptions:
- Plonky3's acceptance is as modelled (`AcceptedP`);
- the compression is collision resistant;
- the Lean specification of Poseidon2 is Plonky3's, which is tested, not
  proved.

Each proof publishes one jet call, the same for every witness
(`Circuit.p2pre_once`, `P2Run.honest_zk_p2pre`). The honest tables of every
run within `2^20` rows are accepted, with the published level table
(`Circuit.compP_complete_log`, `Circuit.compPC_complete_log`); that an
evaluation yields such a run is tested, not proved.

**The entropy proofs.** An accepted proof of either entropy statement
holds in its memory 128 Booleans `bs` for which the check accepts the
kernel's poke with the reply `[0 [0 (listT bs)]]`, Avon's encoding of the
event its pier logs (`Circuit.entropyExport_sound`, `Ski/Entropy.lean`).
The bits are the composed circuit's slot cells, hidden as every composed
witness is: the transcript is simulated given a hiding PCS
(`Circuit.comp_transcript`), Fiat–Shamir assumed. The proof binds the
bits to nothing else: not to a pier, a log, or the kernel the poke
leaves. `bootok` holds for every 128 bits, so a reader can decide it by
running the public kernel; it shows the shape of a proved poke, and a
commitment to the new kernel, as in the hand-off, would bind the hidden
state. `produce.sh` took them
from fresh Avon piers' boot replies, drawn from `getentropy`, and kept
neither pier nor witness; Lean checked first that the piers' pill is `K`
applied to the kernel it compiles (`lake exe entropy pill`). For
`firstset` it booted piers until one's first bit was set, which that
statement discloses anyway; the other 127 bits are as drawn. What the statements disclose is the check's
verdict: nothing about the bits for `bootok`, the first bit for
`firstset`. The proof does not show that the bits came from a pier; a
prover may choose them. It shows what the kernel does with some bits it
cannot see into, which is what a proved poke of a reply needs.

**The hand-off's commitment hides the value.** `produce.sh` drew the
value and the randomness fresh from the system's entropy (`emit-handoff
--fresh`; Lean's runtime reads `/dev/urandom`): the randomness eight
uniform elements below `p`; the value element 1 = 840 and the rest
uniform, element 0 odd, all below `2^30`. The witness, the value and the
randomness, stayed in a temporary directory that the script removed;
nothing in the repository holds it, and nobody, the producer included,
can open `c` or prove a third stage over it. So `c` reveals the value only
as far as Poseidon2's compression does on a uniform randomness input, an
assumption about Poseidon2, as collision resistance is. What the
statements disclose is public by design: stage 1 that element 1 is 840,
stage 2 that element 0 is odd, and both that every value element is below
`2^30` (bit 30 clear, which keeps the value canonical); the rest of the
value is hidden. Tests and Avon's check use the fixed value and
randomness in `bench/Composed.lean`, whose commitment hides nothing.

## Cost

The plain run is the machine alone (`bench/plonky3`); the jetted run is
the one proved here.

| | plain | jetted |
|---|---|---|
| contractions | 10,297 | 567, plus 482 instantiations |
| CPU rows (states) | 25,074 | 3,304 |
| CPU rows per plain contraction | 2.44 | 0.32 |
| all table rows (CPU, POP, INSTW) | 25,074 | 6,816 |
| rows per plain contraction | 2.44 | 0.66 |
| cells written | 30,244 | 4,494 |
| padded heights (CPU / memory) | 32,768 / 65,536 | 4,096 / 16,384 |
| prove, setup included (Apple M4 Max) | about 0.5 s | about 0.17 s |
| verify | about 0.015 s | about 0.02 s |
| proof | — | 376,024 bytes |

The output proof runs 11 probe segments in 3,746 CPU rows: 518
instantiations, 11 probe rows, and the machine's transitions. It writes
5,080 cells past the loaded heap, and one PW row per marker, 23 in all.
The first segment, the term applied to its three markers, takes 3,300
rows; the other ten, which read the value, take 446. It proves in about
0.18 s and verifies in about 0.02 s; the proof is 430,334 bytes.

**The jet table** has 76 jets with 234 body cells in all, averaging 3.4
formals, and 759 roots in a 7,062-cell loaded heap. A jet is one
supercombinator the compiler lifted: an equation, a λ chain or a
constructor. Its body names its closed subterms as globals, so an
instantiation writes only the cells that depend on its arguments
(`bench/plonky3/DESIGN.md` §2). A template that compiles to a bare `S`,
`K` or `I` makes no jet (`JetTable.isComb`): the machine's step for that
combinator takes one CPU row, and the jet takes one too, then a POP row
per formal, an INSTW row per cell, and CPU rows to unwind those cells.
Dropping them took the table from 2,768 roots to 759 and the run from
3,678 CPU rows to 3,304.

## How it was produced

`release/produce.sh` regenerates everything here:

1. Lean emits the term and its jet table.
2. Avon (`avon witness --jet-table`, in the separate Avon repository)
   runs the term, instantiating at the table's roots, and writes the
   witness table.
3. Lean checks that table.
4. `ski-air jet-prove` proves it, and `ski-air jet-verify` checks the
   proof.
5. Lean writes the plan of `[6]` (`lake exe jets plan val 6`). Avon
   (`avon witness --jet-table --plan`) runs the term's probe segments for
   it and writes their table, which `lake exe jets check-probe --row
   sumto_us` checks. `ski-air probe-prove-table` proves it, and `ski-air
   probe-verify` checks the proof.
6. The Ω forgery's hand-written table (`forgeries/omega/omega.table`,
   which `lake exe jets check` rejects) is proved over the forged jet
   table.
7. The composed proofs: Lean emits each statement and witness, and
   `ski-air composed-prove` proves it; the witness stays in a temporary
   directory.
8. The SKIlark proof: SKIlark writes `skilark/split8/source.ski`
   (`python -m skilark.zk 8`), Lean emits the statement and witness from
   it, and `ski-air composed-prove` proves it.
9. The committed split: likewise, from `python -m skilark.zk csplit 8 8`
   and `lake exe skilark cemit`.
10. The Sudoku proof: Lean emits the statement and witness (`lake exe
    sudoku emit`), and `ski-air sudoku-prove` proves it.
11. The proofs with jets: Lean writes the statement with jets (`lake exe
    composed budget`) and its jet table (`lake exe skilark cjets`); Avon
    (`avon witness --statement --jet-table`) writes the witness table,
    which `lake exe composed check-cj` accepts; `ski-air compj-prove-table`
    proves it, and `ski-air compj-verify` checks the proof.
12. The Poseidon2 proofs: Lean emits the statements and witnesses (`lake
    exe composed emit-p2`, `emit-handoff --fresh`, the hand-off's value
    and randomness fresh from the system's entropy and its witness
    discarded);
    `ski-air compp-prove` proves each, and `ski-air compp-chain` checks the
    hand-off.
13. The entropy proofs: Avon boots fresh piers of its entropy kernel with
    `--entropy`, and Lean emits each statement and its witness from a
    pier's logged boot reply (`lake exe entropy emit`); `ski-air
    composed-prove` proves each, at heights 2^11 and 2^14: `bootok` in
    1,831 CPU rows and 13,450 memory cells, `firstset` in 1,921 and
    13,602, each in about 0.55 s (Apple M4 Max, 2026-10-05), proofs of
    about 617 KB. The piers and the
    witnesses stay in a temporary directory.

`release/produce.sh STAGE…` runs some of these: `sumto`, `composed`,
`split8`, `csplit8`, `sudoku`, `jets`, `p2`, `entropy`.

`WITNESS=ski-air release/produce.sh STAGE…` has ski-air write the
jetted witness tables in Avon's place, for when Avon cannot run. Avon
(`e2905bb`) wrote the released ones, and `produce.sh` checks each of
the four against ski-air's, byte for byte. Avon's witnesses are
byte-identical to the tables lean-ski's own prover writes for the same
term, jet table and plan (Avon's `make
jet-witness-check` and `make probe-witness-check`, over the corpus), and
`produce.sh` compares the probe table and its proof with ski-air's own;
with `WITNESS=ski-air` the table comparison holds trivially. The
verifier does not depend on Avon: it checks
the proof, not the producer.
