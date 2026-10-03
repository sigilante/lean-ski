import Ski.ComposedJ

set_option linter.unusedSimpArgs false

open Term

/-!
# Composed statements as open terms

A statement may leave variables free: each is an atom in the heap
(`addStmtsO`, the open terms built by `obuild`).  On closed terms the heap
is the one `Ski/Composed.lean` builds (`cHeap_eq`), so nothing changes for
closed statements.  The open machine's roots read back as the verifiers
applied to the bits and the witness (`cMachineO_decode`).
-/

namespace CompM

open Mach Stmt Compose Wit BExpr

-- ---------------------------------------------------------------------------
-- Open statements in the heap
-- ---------------------------------------------------------------------------

/-- `addStmts` over open terms: a variable is an atom. -/
def addStmtsO (pe wr : Nat) : List Cell → List OTerm → List Cell × List Nat
  | h, [] => (h, [])
  | h, P :: Ps =>
    let h2 := (obuild h P).1
    let pp := (obuild h P).2
    let h3 := h2 ++ [.app pp pe, .app h2.length wr]
    ((addStmtsO pe wr h3 Ps).1, (h2.length + 1) :: (addStmtsO pe wr h3 Ps).2)

theorem build_obuild : ∀ (t : Term) (h : List Cell), build h t = obuild h t.toO
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .app f a, h => by
    show (let (h1, pf) := build h f; let (h2, pa) := build h1 a; alloc h2 (.app pf pa)) =
      (let (h1, pf) := obuild h f.toO; let (h2, pa) := obuild h1 a.toO; alloc h2 (.app pf pa))
    rw [build_obuild f h]
    simp only [build_obuild a]

theorem addStmts_eq (pe wr : Nat) : ∀ (h : List Cell) (Ps : List Term),
    addStmts pe wr h Ps = addStmtsO pe wr h (Ps.map Term.toO)
  | _, [] => rfl
  | h, P :: Ps => by
    show (_, _) = (_, _)
    simp only [build_obuild P h, addStmts_eq pe wr _ Ps]

theorem addStmtsO_spec (pe wr : Nat) (E Wt : OTerm) : ∀ (Ps : List OTerm) (h : List Cell),
    otermAt h (h.length + 1) pe = some E → otermAt h (h.length + 1) wr = some Wt →
    ∃ cs, (addStmtsO pe wr h Ps).1 = h ++ cs ∧ (addStmtsO pe wr h Ps).2.length = Ps.length ∧
      ∀ j (P : OTerm), Ps[j]? = some P →
        otermAt (addStmtsO pe wr h Ps).1 ((addStmtsO pe wr h Ps).1.length + 1)
          ((addStmtsO pe wr h Ps).2.getD j 0) = some (P ⬝ₒ E ⬝ₒ Wt)
  | [], h, _, _ => ⟨[], by simp [addStmtsO], rfl, fun j P hP => by simp at hP⟩
  | P :: Ps, h, hE, hW => by
    obtain ⟨c1, e1, lp, tp⟩ := obuild_spec P h
    have hl2 : (obuild h P).1.length = h.length + c1.length := by rw [e1]; simp
    let h3 := (obuild h P).1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr]
    have hl3 : h3.length = (obuild h P).1.length + 2 := by simp [h3]
    have hEg : ∀ F, h.length + 1 ≤ F → otermAt h3 F pe = some E := fun F hF => by
      have : h3 = h ++ (c1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr]) := by
        simp [h3, e1]
      rw [this]
      exact otermAt_grow hE hF
    have hWg : ∀ F, h.length + 1 ≤ F → otermAt h3 F wr = some Wt := fun F hF => by
      have : h3 = h ++ (c1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr]) := by
        simp [h3, e1]
      rw [this]
      exact otermAt_grow hW hF
    have hPg : ∀ F, (obuild h P).2 + 1 ≤ F → otermAt h3 F (obuild h P).2 = some P := fun F hF =>
      otermAt_grow tp hF
    have h1 : h3[(obuild h P).1.length]? = some (Cell.app (obuild h P).2 pe) := by
      simp [h3]
    have h2 : h3[(obuild h P).1.length + 1]? = some (Cell.app (obuild h P).1.length wr) := by
      simp [h3]
    have r1 : ∀ F, (obuild h P).1.length + 1 ≤ F →
        otermAt h3 (F + 1) (obuild h P).1.length = some (P ⬝ₒ E) := fun F hF => by
      unfold otermAt
      rw [h1]
      dsimp only
      rw [hPg F (by omega), hEg F (by omega)]
    have r2 : ∀ F, (obuild h P).1.length + 1 ≤ F →
        otermAt h3 (F + 2) ((obuild h P).1.length + 1) = some (P ⬝ₒ E ⬝ₒ Wt) := fun F hF => by
      unfold otermAt
      rw [h2]
      dsimp only
      rw [r1 F hF, hWg (F + 1) (by omega)]
    obtain ⟨cs, e, hlen, hj⟩ := addStmtsO_spec pe wr E Wt Ps h3
      (hEg _ (by omega)) (hWg _ (by omega))
    refine ⟨c1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr] ++ cs, ?_, ?_, ?_⟩
    · show (addStmtsO pe wr h3 Ps).1 = _
      rw [e]; simp [h3, e1]
    · show (((obuild h P).1.length + 1) :: (addStmtsO pe wr h3 Ps).2).length = _
      simp [hlen]
    · intro j Q hQ
      cases j with
      | zero =>
        simp at hQ
        subst hQ
        show otermAt (addStmtsO pe wr h3 Ps).1 _ ((obuild h P).1.length + 1) = _
        rw [e]
        refine otermAt_grow (cs := cs) (r2 ((obuild h P).1.length + 1) (Nat.le_refl _)) ?_
        show _ ≤ (addStmtsO pe wr h3 Ps).1.length + 1
        rw [e, List.length_append, hl3]; omega
      | succ j =>
        simp at hQ
        exact hj j Q hQ

/-- The composed heap of an open statement. -/
def cHeapO (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm) : List Cell × List Nat :=
  let h0 := slotHeap ρ (BT.nleaves shp) ++ region
  let e1 := pbuild (BT.nleaves shp + 2) h0 (encO shp 0)
  addStmtsO e1.2 (h0.length - 1) e1.1 Vs

/-- The root of the bits' encoding in the composed heap. -/
def combRoot (ρ : Nat → Bool) (shp : BT) (region : List Cell) : Nat :=
  (pbuild (BT.nleaves shp + 2) (slotHeap ρ (BT.nleaves shp) ++ region) (encO shp 0)).2

/-- The composed machine of an open statement. -/
def cMachineO (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm) : Mach :=
  ⟨(cHeapO ρ shp region Vs).1 ++ [.nil], (cHeapO ρ shp region Vs).2.getD 0 0,
    (cHeapO ρ shp region Vs).1.length⟩

/-- **On a closed statement, the same heap.** -/
theorem cHeap_eq (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) :
    cHeap ρ shp region Ps = cHeapO ρ shp region (Ps.map Term.toO) :=
  addStmts_eq _ _ _ Ps

theorem cMachine_eq (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) :
    cMachine ρ shp region Ps = cMachineO ρ shp region (Ps.map Term.toO) := by
  unfold cMachine cMachineO; rw [cHeap_eq]

/-- The open composed machine's roots read back as the verifiers applied to
    the bits and the witness. -/
theorem cMachineO_decode {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Vs : List OTerm}
    {w : Term} (hw : cWitness ρ (BT.nleaves shp) region = some w) :
    (cHeapO ρ shp region Vs).2.length = Vs.length ∧
    ∀ j V, Vs[j]? = some V →
      otermAt (cMachineO ρ shp region Vs).heap ((cMachineO ρ shp region Vs).heap.length + 1)
        ((cHeapO ρ shp region Vs).2.getD j 0) =
        some (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) := by
  let N := BT.nleaves shp
  let h0 := slotHeap ρ N ++ region
  have hW : otermAt h0 (h0.length + 1) (h0.length - 1) = some w.toO := by
    have := otermAt_of_termAt (heap := h0) hw
    exact otermAt_mono this (Nat.le_succ _)
  have henv : ∀ x, Occ x (encO shp 0) → x < N + 2 →
      otermAt h0 (h0.length + 1) (slotPtr x) = some (slotVal ρ x) := by
    intro x _ hx
    exact otermAt_grow (cs := region) (k := h0.length + 1) (slot_reads ρ N x hx)
      (by simp [h0, slotHeap_length])
  obtain ⟨cs1, e1, t1⟩ := pbuild_spec ρ (N + 2) (encO shp 0) h0 henv
  rw [encO_fill ρ N shp 0 (by simp [N])] at t1
  have hW1 : otermAt (pbuild (N + 2) h0 (encO shp 0)).1
      ((pbuild (N + 2) h0 (encO shp 0)).1.length + 1) (h0.length - 1) = some w.toO := by
    rw [e1]; exact otermAt_grow hW (by simp)
  obtain ⟨cs, e, hlen, hj⟩ := addStmtsO_spec (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1)
    _ _ Vs (pbuild (N + 2) h0 (encO shp 0)).1 t1 hW1
  refine ⟨hlen, fun j V hV => ?_⟩
  have := hj j V hV
  show otermAt ((cHeapO ρ shp region Vs).1 ++ [Cell.nil]) _ _ = _
  refine otermAt_grow this ?_
  show _ ≤ ((cHeapO ρ shp region Vs).1 ++ [Cell.nil]).length + 1
  simp only [List.length_append, List.length_singleton]
  show _ ≤ (addStmtsO (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1)
    (pbuild (N + 2) h0 (encO shp 0)).1 Vs).1.length + 1 + 1
  omega

end CompM
