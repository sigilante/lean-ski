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
   37 s, a 1.56 MB proof, at a 13.5 GB peak, past the 4 GB budget.

   **The shared statement heap (branch `shared-heap`).**  `obuildS`
   (`Ski/HeapShared.lean`) writes a statement hash-consed, its memo a table
   of association lists (`Memo.find_add`, `propext` only); `cHeapOS`
   (`Ski/ComposedOS.lean`) meets the three facts the `dec` circuit reads
   off `cHeapO` (`cMachineOS_decode`, `_public`, `_fitsB`).  The circuit and
   its soundness and completeness are proved once over a `Layout`
   (`Ski/Layout.lean`; `compDAirsGL`, `compDExportG_soundL`,
   `dectermExport_closeL`, `compDG_complete_ofL`/`_decL`/`_nojetL`), the
   audited tree names their `treeL` instances, statements unchanged.  A
   shared statement has the header `dectermS` (`publicTextDGS`,
   `statementOfTextDGS`, `dectermSExport_close`); `composed reshare-dec`
   writes one from a `decterm` text.  Sharing is safe as no composed run
   writes a cell in place (`Air.st`, `AcceptsCD.heap0`, `normRowD_spec`).
   The loops' heaps fall from 2,329,975–2,330,037 cells to 2,300–2,313;
   proved and verified under 4 GB (`compd-prove`, `compd-verify`, Lean's
   `check-dec-run`):

   | loop | CPU rows | memory cells | heights | prove | verify | proof | peak |
   |--:|--:|--:|--:|--:|--:|--:|--:|
   | 1 | 17,544 | 23,429 | 15 15 9 | 1.73 s | 1.6 s | 1.13 MB | 0.69 GB |
   | 3 | 35,165 | 44,514 | 16 16 9 | 3.34 s | 1.6 s | 1.17 MB | 0.87 GB |
   | 10 | 98,777 | 120,437 | 17 17 9 | 6.52 s | 1.6 s | 1.22 MB | 1.39 GB |
   | 20 | 192,219 | 231,457 | 18 18 9 | 12.94 s | 2.0 s | 1.28 MB | 2.77 GB |

   Open: skinock's `emit-loop`/`check-loop` writing `dectermS` and
   `nockloop_close` through `dectermSExport_close`, and the proofs released
   under `skinock/release/nock/`.
