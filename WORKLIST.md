# Worklist

What remains, in the order we mean to take it. `PLAN.md` records the design and what
is built; this file records what is next. Last revised 2026-10-05.

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
- **The paper, reviewed by wizard, chevalier and angel**, its findings fixed; a table
  from each released claim to its check, in the paper and in `release/README.md`.

## Next

### 1. Bind the entropy poke's hidden state

Today's proof shows that some bits pass a check on the public boot kernel, bound to
nothing else. Committing to the kernel the poke leaves, `c = P(state, r)` with `c`
public, would let a later proof pick up from `c`, as the hidden hand-off's two stages do
(`p2commit_chainB`). It touches:

- lean-ski: the statement moves to the circuit with the Poseidon2 precompile; a new
  statement form, its soundness, and a chain theorem;
- the state as committed bits: kernel-specific first (the kernel exposes its state as
  data, through a peek path), a generic structural hash later, if ever;
- SKIjack: a SPEC §4.1 convention for the state as data, opt-in;
- Avon: the pier writes the witness, the state's encoding and the commitment's
  randomness, as secret as the bits; lean-ski's prover proves it, since Avon's witness
  mode refuses `--p2`;
- the paper and the release.

Start with Avon's entropy test kernel, whose state is data already.

### 2. Re-release `split8` and `csplit8` with jets

The released proofs predate the prover's fix that declines projection jets as Lean's
`jetOf` does (1,952 instantiations against 2,250 for `split8`; 44,427 against 46,549 for
`csplit8`). They verify, and the paper flags them. `release/produce.sh`'s jets stage
builds and runs Avon, so this waits until Avon's active work allows it.

### 3. Every CPU row compared

The trace checks compare sampled CPU rows, because Lean's CPU model reads memory as a
list. An array-backed model, proved equal to the list one, would compare every row and
make the memory's multiplicities checked against the full CPU.

### 4. The paper's remaining sourcing

A pointer for the third-party reproduction; repository URLs or commits in the data
statement; a source for the "629 programs" differential test. In the final version the
claim table moves to the docs, where `release/README.md` already holds it.

## Later

- Proven 100-bit parameters: 203 queries at rate 1/2, and the `2^8` tables grown to
  `2^9`, which changes statements' heights (`bench/plonky3/README.md`).
- FRI, the quotient's hiding and round-by-round soundness, proved rather than assumed;
  Fiat–Shamir.
- Probe segments under the hiding; ∀ over public inputs; aggregation.
- Remote CI for lean-ski: waits on the public release.

## Handed to Avon

- [avon#22](https://github.com/sigilante/avon/issues/22): replay with less fuel deletes
  the log's last record, entropy replies included.
