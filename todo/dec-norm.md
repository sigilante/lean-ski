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
- Releases re-produced and verified on the new DEC: lean-ski `release/dec`
  (`QUICK=1 VERIFY_ALL=1 release/verify.sh`), skinock
  `release/nock/decloop` `dec_N` (`verify.sh`), one DEC row more per bit
  list (its end).
- **Completeness with the new DEC** (`Ski/Circuit/CompDTrace*.lean`,
  `CompDCompleteDec.lean`): `DRun.Honest`'s jet rows are `decRowI`'s; the
  honest rows follow `readSubjI` (an indirection row per thunk on the need
  tree and the bit chains, the `Cell` row's `IKT` from `iktOf`, a last
  `Cons` marked and the chain ended at a `TERM` nil); `decProvides_exists`,
  `decpre_complete_log` re-proved and audited.
- skinock `Nock2Ski/DecLoopNorm.lean`: `nockLoopV`, `nockloop_close` (an
  accepted proof of the normalised loop's statement makes M4c's check, every
  occurrence of the word replaced by `normJ (nockToSki decF)`, reach `K`);
  `nockdec emit-loop`/`check-loop`.

Open:

1. **The Nock claim with the normaliser** (skinock): from `nockloop_close`
   to `*[s f] = p`, the compiler's correctness with every occurrence of the
   word replaced by `normJ (nockToSki decF)`, Forms' code fields included,
   and its converse (`nock_of_eqn_K`); `normDec_enc` is the per-call fact.
2. **The loops jetted, proved** (`loop_1`, `loop_3`, `loop_10`, `loop_20`).
   The statement exists (skinock `nockdec emit-loop`, `nockLoopV`, one
   shared copy of `normT`) and the jet fires at every call on the circuit:
   17,544 / 35,165 / 98,777 / 192,219 CPU rows and 20 / 64 / 238 / 508 DEC
   rows (`ski-air compd-measure`; unjetted 20,757 / 57,785 / 336,681 /
   1,152,824).  But the statement's heap is the compiled program as a tree,
   2.35 million cells: memory log 22 (`dlogsOK` now allows 22).  A first
   form of `loop_1` (13 copies of `normT`) proved in 129 s and verified in
   37 s, a 1.56 MB proof, at a 13.5 GB peak, past the 4 GB budget.  Needed:
   a statement heap that shares subterms (a DAG layout of the public
   program in `cHeapO`), or a prover whose memory table is cheaper.
