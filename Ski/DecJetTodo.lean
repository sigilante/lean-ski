import Ski.DecPreSound
import Ski.Circuit.DecAir
import Ski.Circuit.Selectors

/-!
# The `dec` jet: what is not yet proved

**Not imported by `Ski.lean` or `Ski/Audit.lean`.**  This file states what
the `dec` jet still owes, each with `sorry`; nothing in the build depends
on it.  It typechecks with `lake env lean Ski/DecJetTodo.lean`.

What is proved (`Ski/DecJet.lean`, `Ski/Circuit/DecAir.lean`,
`Ski/DecPreSound.lean`, audited in `Ski/Audit.lean`):

- the contract `DecJet.decContract`, skinock's `nounContract decC` over
  `Dom`, the well-formed subjects whose head atom has at most 32 bits, and
  `decContract_respects`;
- the row's semantics `DecJet.decRow` and `decRow_cstep`: a row the Lean
  machine takes at `J` reads back as one `DataJet.JStep decContract J`
  (the analogue of `P2Jet.p2Row_cstep`);
- DEC as data, `Circuit.compDAirs`, which `lake exe circuit compare-compd`
  matches against the Rust verifier's AIRs; `Circuit.dec_sound_row`: every
  row of a table satisfying DEC has one kind, a role, takes the borrow
  step on a `Cons`, and in the head's mode keeps its level below 32;
- the verifier's meaning (`DecPre.decpre_meaning`) and its converse
  (`DecPre.decpre_complete`).

What is open is the circuit's half, the analogue of `Ski/Circuit/CompP*.lean`
(about 8000 lines for Poseidon2).  The route, mirroring P2's:

1. `CompDOK` (as `CompPOK`, `Ski/Circuit/CompPStep.lean`): an accepted
   proof's six tables; the memory, segment tables provide, every other
   table sends with counts `0`/`1`; a CPU row off `DECSEL` is the composed
   CPU's (`CompPOK.read`, `step`, `halt`, reused verbatim).
2. Keys (`CompPOK.jet_key_unique`): the CPU's counter grows strictly, so
   each jet row's counter keys its own messages on `decn`, `decb`, `decd`,
   `decx`.
3. **The need tree.**  On `decn` at one key, the rows of kinds CELL and
   ATOM that receive form a tree rooted at the CPU's send (role `0`): each
   CELL row sends its halves' needs.  The tree is finite because the heap
   is acyclic: a cell's fields point below its address or forward within
   the block its step wrote, and a read lies below the key (DEC's range
   checks), so the read-back `DecJet.readNn` at fuel `H.length` succeeds.
   This is the new argument; P2's tables have no recursion.
4. **The bit chains** (`Edges.path`, as P2IN's): on `decb` each ATOM row
   starts a chain of CONS rows ending at a NIL row or a last `Cons`;
   mode `0` only from the head's ATOM row (role `1`), so the head has one
   chain, of at most 32 rows (`dec_level`), each the borrow step
   (`decStep_sound`), and its writes are `DecJet.bitCells`.
5. **The verdict and the result**: one `decd` message (the chain's end, or
   a cell head), one `decx` message to the CPU, so the CPU's `DROOT`,
   `DCTR` and the memory at `[ctr, DCTR)` are `DecJet.outCells`; so the
   CPU row is `DecJet.decRow` (`CompDOK.jetRow`, as `CompPOK.jetRow`).
6. `compDExportG_sound`, as `compPExportG_sound`: the run decodes to
   `JSteps decContract JD` from the verifier on its witness to `K`; closing
   `J` to an implementation (`DataJet.JSteps.close`) and
   `DecPre.decpre_meaning_eval` give `decpreExport_sound` below.
7. Completeness, as `compP_complete_log`: the honest tables
   (`bench/plonky3/src/decair.rs`'s `dec_row_values`, modelled in Lean)
   satisfy each AIR and balance every bus.

`lake exe composed check-dec-run` replays a released run through
`DecJet.decRow` and `Air.stepRow`, which tests the honest prover's step
against the row's semantics on that run; it proves nothing about other
runs.
-/

namespace Circuit

open Air

/-- **Soundness of `decpre p`** (open): an accepted proof of the statement,
    for AIRs with the normal forms of `compDAirs p W`, holds in its memory
    a subject in the jet's domain whose decrement, under any implementation
    of the contract (skinock's `jetT decF`), is a cell headed by the atom
    `p`. -/
theorem decpreExport_sound {p W : Nat} {P : Term} (_hP : DataJet.Implements DecJet.decContract P)
    {Rs : List AirD} {ts : List Table}
    (_hs : sameAirsB Rs (compDAirs p W) = true) (_hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧
      ∃ (s : DecJet.Dom) (root : Nat), Mach.otermAt (memOf Mm) (memOf Mm).length root = some (DecJet.encNn s.1).toO ∧
        ∃ d r, DecJet.decSpec s.1 = some (.cell (.atom d) r) ∧ BitArith.val d = p := by
  sorry

end Circuit
