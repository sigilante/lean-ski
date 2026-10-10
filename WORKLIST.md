# Worklist

What remains, in the order we mean to take it. `PLAN.md` records the design and what
is built; this file records what is next. Last revised 2026-10-10.

## Done since the last revision

- **Every zero-knowledge prover's traces against Lean's honest tables** (#9): all five
  circuits, memory multiplicities by a count proved equal to Lean's, blinding blocks read
  from Lean. The checks found two prover faults, both fixed.
- **A proved poke whose event is an entropy reply** (#11, #12): `Ski/Entropy.lean`,
  `release/entropy`. Some 128 private bits, given to a kernel as Avon's reply
  `[0 [id bits]]`, make a public check accept the poke (`entropyExport_sound`).
- **The statement digest binds the CPU's constants, tested end to end** (#13):
  `ski-air composed-digest-bound`, `verify.sh` steps 6 and 13.
- **The masking margin, checked**: `ski-air mask-margin`, `verify.sh` step 14. Every
  released hiding proof has 48 random rows to spare over `masks_hide`'s `|S| + 4|Z| ≤ n`.
- **The Poseidon2 circuit is complete** (#15): `compPG_complete_log`, and for `p2pre h`
  and `p2commit c pat` with the published level table `idxPub 1`
  (`compP_complete_log`, `compPC_complete_log`). Every table's constraints hold on its
  honest table (`Ski/Circuit/CompPSat.lean`, `CompPCpuSat.lean`). The paper, the trust
  table and the READMEs cite it.
- **`split8` and `csplit8` with jets, re-released**: proved again with the prover that
  declines projection jets as Lean's `jetOf` does, 1,952 and 44,427 instantiations
  (were 2,250 and 46,549). Statements and jet tables are unchanged, byte for byte;
  `verify.sh` passes.
- **Every CPU row compared**: the trace checks read the memory from an array, through
  copies of each CPU model proved equal to the list models (`Ski/Circuit/CpuFast.lean`),
  so the memory's multiplicities are checked against the full CPU. `split8` with jets
  compares all 131,072 CPU rows in about 2 minutes, Sudoku 65,536 in 25 s.
- **The paper's sources**: the third-party reproduction cited by its commits; the
  repositories and commits in the data statement, at the tag `paper-v1`; the
  differential test committed (`scripts/differential.py`, `lake exe front`), 1,260
  programs with no disagreement.
- **The verifier's jet check in under a second**: `cjets-statement` on `csplit8` in
  0.4 s (was 70 s), `cjets` in 0.5 s (was 151 s); the check is unchanged. The heap
  builders (`buildA`, `obuildA`, `pbuildA`) read the size before the push, so the array
  stays unshared and each push writes in place; `rootsOKB`, `publicB` and `jetTable`
  read the fuel as the array's size, not the list's length at every root.
- **The paper, reviewed by wizard, chevalier and angel**, its findings fixed; a table
  from each released claim to its check, in the paper and in `release/README.md`.

## Next

Nothing queued. For the final version, the paper cites a Zenodo DOI in place of the tag,
and its claim table moves to the docs, where `release/README.md` already holds it.

## Later

- The jets' saving on `csplit8`: a third of the plain rows, against `split8`'s tenth.
  Count the jetted run's CPU rows by the term at the stack's head, and see which hot
  subterms no template covers. A measurement; it may change SKIlark's templates or how
  `jetTable` picks them, and nothing in the proofs.
- `bench/plonky3/README.md`, "Jets on a SKIlark predicate, in the clear": say in one
  sentence that its "104 roots" measure the loaded heap of one choice of bits, where the
  next section measures the verifier's table over the blank composed heap.
- The closure rule counts a pointer that is not backward as private (`pubCells`), so a
  heap with forward pointers would lose jets it could keep. Today's heaps lose none to
  it. Worth doing only if a heap builder starts sharing cells; then `rootsOKB` and
  `publicB`, which walk each root's tree (`termAtG`, `pubAtG`), would also want one pass
  over the heap, as `pubCells` makes.
- Bind the entropy poke's hidden state: commit to the kernel the poke leaves, `c =
  P(state, r)`, so a later proof picks up from `c` as `p2commit_chainB`'s stages do. One
  commitment at boot fits today's circuit if the kernel is public code applied to a
  state of at most 248 bits (SPEC §4.1, a peek path). A chain of pokes needs two jet
  calls per proof over computed bits: a P2IN that walks a list, as P2OUT writes one.
  Arvo binds nothing here; it replays its log. Needed only to prove a kernel's history
  to someone who lacks the log.
- Proven 100-bit parameters: 203 queries at rate 1/2, and the `2^8` tables grown to
  `2^9`, which changes statements' heights (`bench/plonky3/README.md`).
- FRI, the quotient's hiding and round-by-round soundness, proved rather than assumed;
  Fiat–Shamir.
- Probe segments under the hiding; ∀ over public inputs; aggregation.
- Remote CI for lean-ski: waits on the public release.

## Handed to Avon

- [avon#22](https://github.com/sigilante/avon/issues/22): replay with less fuel deletes
  the log's last record, entropy replies included.
