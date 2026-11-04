# The `dec` jet through thunks: what remains (route B)

Done (branch `dec-thunk`, no `sorry`, audited `propext`, `Quot.sound`):

- **DEC reads through thunks** (`Ski/Circuit/DecAir.lean`, `decair.rs`,
  `compare-compd` MATCH): a fifth row kind `KIND` (an indirection `K R w`:
  three slots, a need or a chain step received at the thunk and sent at its
  target, `IB` picks the bus); the `Cell` row's tail slot through one thunk
  (`IKT`, `CKT`, slots 23–25 gated, slot 26's address `(1-IKT)·F2 14 +
  IKT·F2 24`, the tail `F2 26`), `NSLOT` 28.  A design change from the plan:
  the `Cons` row no longer peeks at its tail (a normalised list ends in the
  thunk `K K k`, not `K`).  A last `Cons` says so (`ISLAST`, the prover's
  claim), marks its step to the tail (mode field `MODE + 2`), and the chain
  must end, through any thunks, at a nil with `TERM = 1`; an unmarked nil
  (`TERM = 0`) is at level `0` (`KNIL·(1-TERM)·LVL = 0`), so an unmarked
  step above level `0` reads a non-empty list.  Every `Cons` sends
  (`CSEND = KCONS`), `DONE1 = KNIL·(1-MODE)·(1-TERM)`.
- **Soundness** (`CompDDec` … `CompDJetRow`, `ComposedD`, `DecPreSound`,
  `DecTerm`): `CompDBack` (thunk runs end: `pigeon`, `iterI_bound`; chains
  and needs traced back to non-thunk senders, `chain_back'`, `need_back'`),
  `chain_bits`/`need_nn` through thunks (`readBitsI`, `readNnI`), the head
  chain walked step by step (`walkS`, `on_walk`, `walkS_end`),
  `CompDOK.jetRow` concludes `decRowI`; `NormRowD` takes `decRowI`,
  `HSteps`'s jet step is up to `K`-contraction (`HSteps.close_K`).
  `decpreExport_sound` now gives a cell whose read-back `ORed`-reduces to
  `encNn s`; `dectermExport_close` is as stated.
- skinock `Nock2Ski/DecLoopNorm.lean`: `nockLoopV`, `nockloop_close` (an
  accepted proof of the normalised loop's statement makes M4c's check, every
  occurrence of the word replaced by `normJ (nockToSki decF)`, reach `K`);
  `nockdec emit-loop`/`check-loop`.

Open:

1. **Completeness with the new DEC** (`decProvides_exists`,
   `decpre_complete_log`).  The old proofs are in `todo/dec-complete/*.txt`
   (`CompDTrace*`, `CompDCompleteDec`), out of the build.  To port: `DecT.DR`
   gains `ib`, `ikt`, `term`; `DR.col` the columns 36–42 (`KIND`, `IB`,
   `INN`, `INB`, `IKT`, `CKT`, `TERM`), `CSEND = KCONS`, `DONE1` with
   `TERM`; `patOf 5 = indSlots`, the `KT` source, the `Cell` row's gated
   slots 23–25 (`act`); `bitsRows` gains the terminal nil after the last
   `Cons` (at level `|bs|`, `TERM = 1`, its borrow `0`), so `callB`
   telescopes the marked step; `consReads` loses slot 16.  For `decpre`'s
   runs (no thunks: `DRun.Honest` keeps `decRow`, `decRow_decRowI`) no
   indirection row is needed; with thunks, `callRows` follows `readSubjI`
   (an indirection row per thunk on the need tree and the chains, `IKT`
   from `ktAt`), as `decair.rs`'s `Reader` does.  `compDG_complete_dec`
   (given a DEC table that provides the calls) and `compDG_complete_nojet`
   are proved.
2. **The Nock claim with the normaliser** (skinock): from `nockloop_close`
   to `*[s f] = p`, the compiler's correctness with every occurrence of the
   word replaced by `normJ (nockToSki decF)`, Forms' code fields included,
   and its converse (`nock_of_eqn_K`); `normDec_enc` is the per-call fact.
