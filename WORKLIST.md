# Worklist

What remains, in the order we mean to take it. `PLAN.md` records the design and what
is built; this file records what is next. Last revised 2026-10-13.

## Done since the last revision

- **The challenges' conditions, counted** (`Ski/ZK/MaskGen.lean`): the independence that
  `pcsCloseN_fri` asks of `αb` and the chunks of `ζ` is `Generic`, which fails for `P²` of
  the `P⁴` challenges (`mz_det_eq`, `nongeneric_count`); `pcsCloseN_fri_generic`.
- **FRI's view hides** (`Ski/ZK/MaskFri.lean`): FRI's input is each committed matrix's
  batched polynomial; a joint shift of masks, chunk randomness and random codewords keeps
  every opening and every batched polynomial, four codewords cancelling any change of a
  matrix's columns when `1, αb, αb², αb³` are independent (`mat_cancel`, `cw_rows`). The
  composed PCS with every chunk, codeword and FRI's view meets `PCSCloseN` exactly
  (`pcsCloseN_fri`, `pcsCloseN_friR` with the randomization polynomial,
  `*_transcriptG_fri`), with one group a committed matrix.
- **The random columns' openings hide** (`Ski/ZK/MaskRand.lean`): independent randomness
  beside a PCS keeps `PCSCloseN` exact (`PCSCloseN.indep`); with the random codeword and
  randomization columns' openings, `pcsCloseN_rand`.
- **The quotient's chunks hide** (`Ski/ZK/MaskChunk.lean`, `Ski/ZK/Solve4.lean`): Plonky3's
  chunk randomization, `q_i + v_i r_i` with the last chunk's `r` cancelling the others',
  hides all but what the verifier sees: a chunk on its own domain (a query point can lie
  there) and the normalized recombination elsewhere (`chunks_hide`, `chunks_sim`). The PCS
  with every quotient column's opened chunks meets `PCSCloseN` exactly
  (`pcsCloseN_chunks`, `*_transcriptG_chunks`), when `|S| + 4 ≤ n`, `ζ` generates the
  extension (`solve_spec`, `mz_gen_det`; a uniform `ζ` fails with probability about
  `2^-62`), and the honest chunks show the quotient (`RecOK`, read from Plonky3's source).
- **Honest chunks meet `RecOK`** (`Ski/ZK/MaskRec.lean`): chunks that equal the quotient
  `Qp` on their own disjoint domains, below the degree bound, with normalized selectors,
  recombine to `Qp` itself (`rpoly_quot`). They show `Qp / (κ ∏_j v_j)` off every domain
  (`shows_of_quot`), so `RecOK` holds for every column (`recOK_of_honest`). Left as
  hypotheses: the verifier's targets equal these values of `Qp`, and the selectors are
  normalized. On cosets of one subgroup the normalization follows from each domain's first
  point, as `get_zp_cis` computes it (`Ski/ZK/MaskCoset.lean`, `sel_of_coset`,
  `quotOK_of_coset`). With each chunk the quotient interpolated on its domain (`chunkOf`),
  `quotOK_honest` discharges the interpolation, the chunks' degrees and the disjointness. On
  Plonky3's split domains over BabyBear the domains are cosets of one subgroup without
  repeated points (`Ski/ZK/MaskSplit.lean`, `quotOK_split`, `bb_split`); left are the
  quotient's degree and the selectors at each first point. Plonky3's weights, `μ_k = cis_k /
  κ`, meet the first-point condition (`Ski/ZK/MaskCis.lean`, `first_of_cis`). The honest
  quotient of an AIR has the defining identity, its size `|C| - |H|`, and targets that read
  the columns at `gᵒ x` (`Ski/ZK/QuotPoly.lean`, `air_quot`, `shows_air`); the selectors'
  products are Plonky3's `xⁿ - 1` formulas (`Ski/ZK/VanishPow.lean`); the vanishing follows
  from `Sat` for guarded constraints, and for a table that meets `Sat` its honest chunks
  show the AIR's targets (`Ski/ZK/QuotSat.lean`, `hvan_of_sat`, `shows_sat`). The quotient
  fits Plonky3's ZK chunk count, in Plonky3's degree (`quot_fits`). The targets read from
  the openings are the honest ones, and an opened table that meets `Sat` shows them
  (`Ski/ZK/QuotOpen.lean`, `shows_open`). An AIR's quotient table enters `pcsCloseN_fri`
  with `TabsHonest` discharged (`Ski/ZK/QuotInst.lean`, `tabsHonest_air`,
  `pcsCloseN_fri_air`). `hsatT` asks `Sat` at every tuple assignment, more than completeness
  gives. The coordinates fold back to the verifier's fold times the model's chunk
  normalization, and extension constraints, folded by coordinates, agree with Plonky3's fold
  in the extension (`Ski/ZK/QuotFold.lean`, `airTgE_back`, `airTgE_mixed`). The folding
  challenge, drawn and published with the view, is simulated exactly
  (`pcsCloseN_fri_air_draw`). Plonky3's chunks are built and their hypotheses proved, and
  over BabyBear the trace domain's order and the masks' distinctness (`Ski/ZK/QuotP3.lean`,
  `p3_static`, `bb_trace`, `bb_masks`, `pcsCloseN_fri_bb`); the group's trace and mask
  points on them, `hT` and `hRq`, are Plonky3's interleaved rows (`Ski/ZK/Interleave.lean`,
  `bb_ileave_mcol`). For the corpus circuit the kernel checks the AIR facts for every term,
  and the composed theorem is specialized to it (`Ski/ZK/QuotBase.lean`,
  `pcsCloseN_fri_base`). Several AIRs enter with one table each, each folding its AIR's own
  constraints (`pcsCloseN_fri_tabs`), and the corpus LogUp interactions' degree is checked
  by the kernel (`base_lup`). A table can read several groups and take constraints that
  depend on the challenges and the transcript's values, as LogUp's do
  (`Ski/ZK/QuotTwo.lean`, `tabsHonest_gen`, `pcsCloseN_fri_gen`). LogUp's constraints are
  written as constraints, complete row by row on the honest permutation trace, and of the
  shape `tabsHonest_gen` asks, for the corpus too, each lookup with its bus's prefix as its
  `α`, so multi-bus AIRs are covered (`Ski/ZK/LogUpAir.lean`, `lup_sat`;
  `Ski/ZK/LogUpBase.lean`, `corpus_withLup_shape`). The honest total is the transcript's
  terminal, so completeness holds at the transcript's terminal of any table meeting `Sat`
  (`accV_terminal`, `lup_sat_terminal`). The committed main and permutation groups are that
  table's columns, so a corpus AIR's table with its LogUp constraints is honest from the
  builder's facts (`cols_withPerm`, `hsatT_lup`, `tabsHonest_corpus`). For the corpus the
  LogUp part is asked only where `goodLup` holds, no message of nonzero count with a
  vanishing denominator at the builder's table; elsewhere Plonky3's prover aborts and the
  model sends the canonical chunks, honest at every challenge (`goodLup`,
  `tabsHonest_canon`, `pcsCloseN_fri_gen`, whose `good` is a parameter). Where the proof
  does not abort `goodLup` holds (`goodLup_of_noAbort`), and `pcsCloseN_fri_corpus` sends
  the honest chunks wherever the transcript's `Aborts` is false; the transcript theorems
  show nothing on an abort and charge it by `abort_count`. These theorems take any AIR
  meeting `AirP3`, which the kernel checks for every AIR of the Sudoku, hidden-term and
  composed circuits (`Ski/ZK/HideP3.lean`). Blinding keeps `Sat` for every blinding block of
  these circuits (`sat_setBlind`, `blind_ok`). For each hiding circuit the blinded private
  tables meet `Sat` and the view publishes their terminals at 0, 1, 2
  (`Ski/ZK/HideWire.lean`). The preprocessed columns interpolate on the trace domain
  (`preInterp_spec`), and a private table meeting `hb` and the domain facts gives
  `tabsHonest_corpus_ite`, which `pcsCloseN_fri_tabs` combines into a transcript theorem's
  `hpcs`. Over BabyBear one private table's every domain, chunk and group fact is discharged
  (`Ski/ZK/BbGroup.lean`, `tabsHonest_bb`). One Sudoku run gives `Balanced`, `Unblinded` and
  `Sat` for the same tables, their blinded copies' `Sat` and the view's terminals
  (`Ski/ZK/SudRun.lean`). The Sudoku proof is zero knowledge over its composed hiding PCS,
  end to end, its PCS term zero, the public program table's groups and quotient included
  (`Ski/ZK/SudInst.lean`, `sud_pcs`, `sud_hiding`), with each height opened at its own query
  points (`S16`, `S10`, `SP`) and the program table's height derived from the statement
  (`sud_prog_height`). Fixed, not sampled: `ζ`, the FRI challenge, the blinding blocks, the
  quotient values, the weights `ws` and the query points; the four chunks per table follow
  from Plonky3's `2^(log2_ceil 2 + 1)` at degree 2. The hidden-term proof is too, by the
  same construction (`Ski/ZK/WitInst.lean`, `wit_pcs`, `wit_hiding`, its run's `Sat` from
  `wit_run_sats`). So is the composed proof, its public program and segments tables included
  (`Ski/ZK/CompInst.lean`, `comp_pcs`, `comp_hiding`, its run's `Sat` from `comp_run_sats`),
  for a CPU table of `2^R` and a memory of `2^Lm` rows, `R, Lm ≥ 3`. Each simulator reads
  the tables' preprocessed columns only (`sudPsim_pre`, `wPsim_pre`, `cPsim_pre`); the
  preprocessed columns and the randomization polynomial, matrices without witness, join
  FRI's input and the view, and each transcript theorem holds over that PCS
  (`Ski/ZK/PreOpen.lean`, `*_hidingX`). The challenges `ζ` and `αb` may be any `Generic`
  draws, all but `P²` of the `P⁴` (`*_hidingXG`, `nongeneric_count`). Under Fiat–Shamir, in
  the programmable random-oracle model, each transcript keeps its simulation error against a
  distinguisher with the oracle's table, its LogUp challenges hashed from a commitment of
  the first message (`Ski/ZK/FSInst.lean`, `sud_fs`, `wit_fs`, `comp_fs`), for an idealized
  proof: the commitment is never opened in the view and `Com` is a perfect primitive apart
  from the oracle. With the commitment opened, the view's opened values being the committed
  main matrices' (masked columns and random codewords) and the opening proof being in the
  output, the simulator committing interpolants through its own openings, the same holds
  under hiding given the openings (`Ski/ZK/FSOpenInst.lean`, `*_fs_open`). Over two rounds,
  `ζ` hashed from both commitments, each proof keeps its simulation error, summed over
  generic `ζ` (`Ski/ZK/FSRound2.lean`, `Ski/ZK/FSRound2Inst.lean`, `*_fs2`), both
  commitments unopened, the permutation and quotient commitments fused, the
  constraint-folding challenge fixed, the non-generic `ζ` excluded. With both commitments
  opened, the second of the permutation groups' and quotient chunks' matrices with their
  codewords, every proof keeps it too (`Ski/ZK/FSOpen2Inst.lean`,
  `Ski/ZK/FSOpen2Inst2.lean`, `*_fs_open2`). Over three rounds, the permutation and quotient
  commitments apart and the constraint-folding challenge hashed from the transcript with the
  permutation commitment, every commitment opened, every proof keeps it too
  (`Ski/ZK/FSOpen3.lean`, `Ski/ZK/FSOpen3Inst.lean`, `*_fs_open3`), unguarded, the non-generic
  `β` and `ζ` (at most `2/P²`) in the bound (`fs_open3U`). Open: the FRI layers hashed; `Com` from the same
  oracle (bounded queries, a ROM-hiding term); several proofs per oracle (a hybrid and a
  collision term); the later rounds under the oracle (the FRI challenge, the query points);
  the lookup proof-of-work nonce. The groups' trace and mask points (`hT`, `hRq`) are tied
  to the committed matrices: the masked column is the interpolant of Plonky3's interleaved
  column over the `2n`-point domain (`Ski/ZK/Interleave.lean`, `bb_ileave_mcol`); that
  Plonky3 interleaves, trace rows even and random rows odd, is read from its source.
- **The quotient's recombined values hide** (`Ski/ZK/MaskQuot.lean`): the chunks sit at the
  committed trace's height, so a query opens them at the trace's point `s`, where they
  recombine to a function of the terminals and the masked columns at `s` and `g s`. Masks
  covering `S ++ g S` and `Z`, `2|S| + 4|Z| ≤ n`, hide it with the column openings
  (`pcsCloseN_quot`, `PCSCloseN.post`), and every hiding circuit's transcript theorem holds
  over that view with no PCS term (`*_transcriptG_quot`). At `q` queries that is `2q + 8`,
  which `mask-margin` checks. The chunks' own values, their split and randomization were
  assumed here; later modules build them (`MaskChunk`, `MaskSplit`, `QuotP3`, `PreOpen`).
- **Every hiding table has at least `2^9` rows**: `HidingFriPcs` asks `2(q + 8) = 216`
  mask points and the quotient `2q + 8 = 208`; the `2^9` floor leaves 296 to spare and
  meets 203 queries (422). An earlier count, `3q + 8 = 308` (#30 and 77c36cf), took
  the quotient chunks for twice the trace's height; they are the same height (the batch
  verifier's chunk domains), so `2^8` had met the need. The statement checks (`logOK`,
  `plogsOK`, the Rust's `LOG_BOUNDS`) take heights `2^9` to `2^20`; the witness and
  provider tables pad to `2^9`; bits and region stay capped at `2^8`. `ski-air
  mask-margin` tests both counts, and `verify.sh` step 6 refuses a statement at height `2^8`. The
  release is remade at the new floor. `lake exe entropy` reads Avon's record checksum.
- **Every zero-knowledge prover's traces against Lean's honest tables** (#9): all five
  circuits, memory multiplicities by a count proved equal to Lean's, blinding blocks read
  from Lean. The checks found two prover faults, both fixed.
- **A proved poke whose event is an entropy reply** (#11, #12): `Ski/Entropy.lean`,
  `release/entropy`. Some 128 private bits, given to a kernel as Avon's reply
  `[0 [id bits]]`, make a public check accept the poke (`entropyExport_sound`).
- **The statement digest binds the CPU's constants, tested end to end** (#13):
  `ski-air composed-digest-bound`, `verify.sh` steps 6 and 13.
- **The masking margin, checked**: `ski-air mask-margin`, `verify.sh` step 14. Every
  released hiding proof has 296 random rows to spare over `HidingFriPcs`'s 216, at
  tables of at least `2^9` rows.
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
- **Only the jets that help**: a template whose compiled root is `S`, `K` or `I` makes
  no jet (`JetTable.isComb`). Each such jet took a POP row per formal, an INSTW row per
  cell and CPU rows to unwind them, for a step the machine takes in one CPU row. `seq`'s handler `λg t. g t`
  compiles to `I`, with 39,459 instantiations on `csplit8`. An ablation of every other
  frequent jet on `csplit8` found each one saving rows, or neutral. `csplit8` now runs
  in 118,222 CPU rows (was 157,681), 22,382 POP (101,300) and 36,578 INSTW (76,037),
  proved at `2^17 2^18 2^15 2^16` (was `2^18 2^19 2^17 2^17`) in 16 s (29 s); `split8`
  in 11,167; `3 sumto` in 3,304 (3,678). The interpreted corpus rows went from 110–112%
  of the plain rows to 86–87%. Every released jet table, witness table and proof with
  jets was remade; ski-air wrote the witness tables (`WITNESS=ski-air`).
- **Avon writes the released witnesses again**: Avon at `e2905bb` (`origin/master`,
  built in a clean worktree) writes `3 sumto`'s jetted and probe tables and the
  `split8` and `csplit8` jetted tables byte for byte as ski-air does, and
  `release/produce.sh sumto jets` remade the release from them; only the two
  randomized proofs with jets changed. Its counts equal the prover's (1,520 and 4,968
  instantiations), since no projection jet remains. Tagged `paper-v2` at PR #21's
  merge, `79c7026`.
- **The paper at PR #21's figures**: `3 sumto` in 3,304 CPU rows, `split8` and
  `csplit8` with jets at their new counts and heights, verify times after the fast jet
  check (2.4 s and 3.2 s; `release/verify.sh` in about two minutes, built), and who
  wrote which witness tables; fact-checked against the artifacts by angel.
- **The paper, reviewed by wizard, chevalier and angel**, its findings fixed; a table
  from each released claim to its check, in the paper and in `release/README.md`.

## Next

For the final version, the paper cites a Zenodo DOI in place of the tag,
and its claim table moves to the docs, where `release/README.md` already holds it.

## Later

- `csplit8` still takes a quarter of its plain rows, against `split8`'s twelfth. The
  cost is `acceptEq`'s comparison of the commitment, `eqN` on unary numerals under `Y`:
  256 levels of recursion at about 128 `I` steps each (32,896), plus the unwinds the `S`
  steps build; `wAdd` adds 5,498 more. Comparing in binary, or a jet that covers the
  `Y` unfolding, would cut it; either changes `csplit8`'s statement and proofs.
- η-lifting, measured and shelved (draft reference PRs #24 here and SKIjack #9): a λ
  chain that η-reduces whole compiles as what it reduces to, so `seq`'s `λt. g t` is
  `g`, not `I ⬝ g`. Both compilers agree (the differential test with `--eta`, 1,490
  programs, 0 disagreements), but it saves 1%: `csplit8` 118,221 → 117,115 jetted CPU
  rows, `split8` 11,166 → 10,896.
- `bench/plonky3/README.md`, "Jets on a SKIlark predicate, in the clear": say in one
  sentence that its "37 roots" measure the loaded heap of one choice of bits, where the
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
- Proven 100-bit parameters: 203 queries at rate 1/2; the masks then need 422 points,
  within the `2^9` floor (`bench/plonky3/README.md`).
- FRI's soundness and round-by-round soundness, proved rather than assumed;
  Fiat–Shamir.
- Probe segments under the hiding; ∀ over public inputs; aggregation.
- Remote CI for lean-ski: waits on the public release.

## Handed to Avon

- [avon#22](https://github.com/sigilante/avon/issues/22): replay with less fuel deletes
  the log's last record, entropy replies included.
