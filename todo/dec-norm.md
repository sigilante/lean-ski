# The `dec` jet through thunks: what remains (route B)

Done (branch `dec-norm`, no `sorry`, audited `propext`, `Quot.sound`):

- `Ski/DecInd.lean`: `readInd`, `readBitsI`, `ktAt`, `readCellI`, `readNnI`,
  `headAtom`, `readSubjI`, `decRowI`; `decRowI_step` (the row reads back as
  `J ⬝ u ⬝ R`, `u ↠ encNn s`, next state `v ⬝ R`, `v ↠ encO (decSpec s)`,
  `ORed` = `K`-contraction anywhere), `decRowI_jstep`, `JStepsI.close_K`
  (a run of `JStepI` to `K` closes to `WSteps … K` with any implementation of
  `decContract`), `decRow_decRowI`.
- skinock `Nock2Ski/DecNorm.lean`: `normT`, `norm_enc`, `normJ_impl`,
  `normDec_enc`; `bench/NockNorm.lean` runs the loop on the heap machine with
  `decRowI` as the jet (`release/nock/decloop/results-norm.txt`).

Open, in order:

1. **DEC reads through thunks** (`Ski/Circuit/DecAir.lean`, `decair.rs`).
   - A fifth row kind `KIND` (indirection). It reads three cells through
     three slots: `p = app f w` (tag 3), `f = app k R` (tag 3), `k = K`
     (tag 1); it receives a need `decn (key, p, ρ)` and sends `decn (key, R,
     ρ)`, or receives `decb (key, p, mode, lvl, bw, wc)` and sends the same
     tuple at `R` (a selector bit picks the bus). No range checks beyond the
     slots' `addr < key`: the read-back's fuel bounds a chain.
   - The `Cell` row's tail slot (slot 23, `F2 14`, tag 3) through one thunk:
     a selector `IKT`, three more slots (`F2 14` as `app f w`, `f` as `app k
     kt`, `k` as `K`), slot 23's address `(1 - IKT)·F2 14 + IKT·f2(f's slot)`.
     `NSLOT` 25 → 28. The output's cells keep `f2 14`, the slot as the
     wrapper holds it (`CellSk.kt`).
   - `compare-compd` (Lean data against the Rust export) after both edits.
2. **Soundness** (`Ski/Circuit/CompD*.lean`): `CompDOK.need_nn` and
   `chain_bits` (CompDTree) gain the indirection case (`readInd_peel`: two
   fuels down); `head_pc`/`subj_pc` become "the role's rows read the pointer
   after its chain"; `CompDOK.jetRow` concludes `decRowI`; `NormRowD` takes
   `decRowI`; `DecPre.HSteps` becomes `JStepI` (`decRowI_jstep`) and
   `HSteps.close`/`first_jet` become `JStepsI.close_K` and its analogue;
   then `decpreExport_sound` and `dectermExport_close` as stated.
3. **Completeness** (`CompDTrace*`, `CompDCompleteDec`): the honest DEC rows
   of a call add one indirection row per thunk on the need tree and bit
   chains and fill `IKT`; `decpre_complete_log` re-proved.
4. **Release**: every `compDAirsG` proof changes (lean-ski `release/dec`,
   skinock `release/nock/decloop`); re-produce and re-verify.
5. **The Nock claim with the normaliser** (skinock): the compiled loop with
   every occurrence of the word replaced by `normJ (nockToSki decF)` (the
   statement's verifier `abstJ` with `normJ JD` in place of `JD`) needs the
   compiler's correctness with that replacement, Forms' code fields
   included, and its converse (`nock_of_eqn_K`). `normDec_enc` is the
   per-call fact: on any encoding, the normalised word reaches what the word
   reaches on `encNoun s`.
6. Prove and verify `loop_1`, `loop_3`, `loop_10`, `loop_20` jetted; the
   machine runs predict 17,348 / 34,805 / 97,843 / 190,465 CPU rows plus DEC
   rows (unjetted 20,757 / 57,785 / 336,681 / 1,152,824 on the same machine
   for the same check).
