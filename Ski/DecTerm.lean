import Ski.DecPreSound
import Ski.DecTermText

/-!
# A composed statement with the `dec` jet for any public verifier term

`decpre p` (`Ski/ComposedDText.lean`) is one verifier, `λ β w. CHECK_p ⬝ (J ⬝
w)`.  The circuit `Circuit.compDAirsG Vs W` and its soundness
`Circuit.compDExportG_sound` already take any list of open verifiers whose
only free variable is the jet's atom `JD`.  This module gives that family a
text and a meaning:

- **`publicTextDG Vs W lg`**: the statement's text, `publicTextD`'s layout
  with the header `decterm J` (no parameter: the verifiers are the heap's
  cells after the region, each segment's root `V ⬝ β ⬝ w` as
  `cMachineO` lays it out).
- **`statementOfTextDG`**: the text parsed back.  The verifiers are read off
  the heap (`decodeDG`: every cell an `S`, `K`, `I`, an atom `x` read as the
  variable `x`, or an application of earlier cells), and the text is
  accepted only when it is exactly `publicTextDG` of what was read, every
  verifier's variables are `JD` (`occOK`), there is at least one, and the
  region and heights are in range (`checkDG`).  So a statement names its
  terms by their cells, as the composed circuit's statements do, and a
  consumer recomputes the terms it means and compares (skinock's `nockdec
  check`).
- **`dectermExport_sound`**: an accepted proof for verifiers that are
  `vsOK` (at least one, each open only in `JD`; an accepted text's
  verifiers are, `statementOfTextDG_vsOK`) has, in its memory, a bit and a
  region whose witness makes every verifier head-reduce with the jet to
  `K` (`compDExportG_sound`).
- **`dectermExport_close`**: for a verifier `λ β w. C` that ignores its
  arguments (`verT C`), any implementation `P` of the `dec` contract closed
  in for the jet makes `C` reach `K` by weak reduction (`HSteps.close_K`,
  β, Church–Rosser).  With `C` a public program whose every occurrence of
  some term `P₀` is replaced by `J` (`P₀` implementing the contract), the
  closed `C` is the program itself: an accepted proof shows the program
  reaches `K`.

What the jet can fire on: the row reads its subject from the memory cell by
cell (`DecJet.readNn`), so the subject must be an `encNn` laid out in the
memory: the statement's heap or the witness region.  A value computed during
the run is not: a Scott cell's fields come out of elimination as thunks `K h
c`, and head reduction never reduces an argument.  So the jet fires on
literal subjects (one row each) and not on its own output.
-/


namespace Circuit

open B Air Compose CompM Stmt Mach Wit ComposedDText DecTerm

/-- **Soundness of a `decterm` statement**: tables accepted for the AIRs of
    verifiers open only in the jet's atom (`vsOK`, which an accepted text's
    verifiers are: `statementOfTextDG_vsOK`) carry, in their memory, a bit
    and a region whose witness makes every verifier head-reduce with the
    `dec` jet to `K`, every subject the jet takes held in the memory. -/
theorem dectermExport_soundL (L : Layout) {Vs : List OTerm} {W : Nat} (hV : vsOK Vs = true)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirsGL L Vs W) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) 1 (regionM (memOf Mm) 1 W) = some w ∧
      ∀ V ∈ Vs, HSteps (InMem (memOf Mm)) JD (V ⬝ₒ (fillB shpD (bitsM (memOf Mm)) 0).enc.toO ⬝ₒ w.toO) .K :=
  compDExportG_soundL L (vsOK_sound hV).1 (vsOK_sound hV).2 hs hacc

/-- `dectermExport_soundL` for the statement as a tree. -/
theorem dectermExport_sound {Vs : List OTerm} {W : Nat} (hV : vsOK Vs = true)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirsG Vs W) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) 1 (regionM (memOf Mm) 1 W) = some w ∧
      ∀ V ∈ Vs, HSteps (InMem (memOf Mm)) JD (V ⬝ₒ (fillB shpD (bitsM (memOf Mm)) 0).enc.toO ⬝ₒ w.toO) .K :=
  dectermExport_soundL treeL hV hs hacc

/-- **A verifier that ignores its arguments**: its check term, with any
    implementation of the `dec` contract closed in for the jet, reaches
    `K` by weak reduction. -/
theorem verT_close {C : OTerm} (hocc : ∀ x, Occ x C → x = JD) {A : OTerm → Prop} {b w : Term}
    {P : Term} (hP : DataJet.Implements DecJet.decContract P)
    (h : HSteps A JD (verT C ⬝ₒ b.toO ⬝ₒ w.toO) .K) : WSteps (C.close (DecPre.envD P)) Term.K := by
  have hσ : DataJet.Implements DecJet.decContract (DecPre.envD P JD) := by
    show DataJet.Implements DecJet.decContract (if JD = JD then P else Term.K)
    rw [if_pos rfl]; exact hP
  have hk := DecPre.HSteps.close_K (DecPre.envD P) hσ h
  have e : (verT C ⬝ₒ b.toO ⬝ₒ w.toO).close (DecPre.envD P) = appT ((verT C).close (DecPre.envD P)) [b, w] := by
    show (verT C).close _ ⬝ b.toO.close _ ⬝ w.toO.close _ = _
    rw [close_toO, close_toO]; rfl
  rw [e] at hk
  have hb := absN_beta_close [0, 1] C (DecPre.envD P) [b, w] rfl
  have e2 : C.close (overrideC (DecPre.envD P) [0, 1] [b, w]) = C.close (DecPre.envD P) :=
    close_agree fun i hi => by
      have := hocc i hi
      subst this
      exact Mach.overrideC_notin _ _ _ _ (by decide)
  rw [e2] at hb
  exact (wsteps_K_iff hb).1 hk

/-- **`dectermExport_close`**: an accepted proof for verifiers `Vs`
    (`vsOK`) one of which is `verT C`, `C` open only in the jet's atom,
    shows `C` reaches `K` with any implementation of the `dec` contract in
    the jet's place. -/
theorem dectermExport_closeL (L : Layout) {Vs : List OTerm} {W : Nat} (hV : vsOK Vs = true) {C : OTerm}
    (hC : verT C ∈ Vs) (hocc : ∀ x, Occ x C → x = JD)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirsGL L Vs W) = true) (hacc : AcceptedP Rs ts)
    {P : Term} (hP : DataJet.Implements DecJet.decContract P) :
    WSteps (C.close (DecPre.envD P)) Term.K := by
  obtain ⟨_, _, _, _, _, _, _, w, _, hrun⟩ := dectermExport_soundL L hV hs hacc
  exact verT_close hocc hP (hrun _ hC)

/-- `dectermExport_closeL` for the statement as a tree. -/
theorem dectermExport_close {Vs : List OTerm} {W : Nat} (hV : vsOK Vs = true) {C : OTerm} (hC : verT C ∈ Vs)
    (hocc : ∀ x, Occ x C → x = JD)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirsG Vs W) = true) (hacc : AcceptedP Rs ts)
    {P : Term} (hP : DataJet.Implements DecJet.decContract P) :
    WSteps (C.close (DecPre.envD P)) Term.K :=
  dectermExport_closeL treeL hV hC hocc hs hacc hP

/-- **Soundness of a shared `decterm` statement** (header `dectermS`): as
    `dectermExport_sound`, the statement laid out by `sharedL`. -/
theorem dectermSExport_sound {Vs : List OTerm} {W : Nat} (hV : vsOK Vs = true)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirsGL sharedL Vs W) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) 1 (regionM (memOf Mm) 1 W) = some w ∧
      ∀ V ∈ Vs, HSteps (InMem (memOf Mm)) JD (V ⬝ₒ (fillB shpD (bitsM (memOf Mm)) 0).enc.toO ⬝ₒ w.toO) .K :=
  dectermExport_soundL sharedL hV hs hacc

/-- **`dectermSExport_close`**: as `dectermExport_close`, the statement
    shared. -/
theorem dectermSExport_close {Vs : List OTerm} {W : Nat} (hV : vsOK Vs = true) {C : OTerm} (hC : verT C ∈ Vs)
    (hocc : ∀ x, Occ x C → x = JD)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirsGL sharedL Vs W) = true) (hacc : AcceptedP Rs ts)
    {P : Term} (hP : DataJet.Implements DecJet.decContract P) :
    WSteps (C.close (DecPre.envD P)) Term.K :=
  dectermExport_closeL sharedL hV hC hocc hs hacc hP

end Circuit
