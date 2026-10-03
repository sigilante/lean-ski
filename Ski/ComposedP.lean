import Ski.ComposedJ
import Ski.P2Jet

set_option linter.unusedSimpArgs false

open Term

/-!
# Composed statements with the Poseidon2 jet

A statement whose verifiers use the Poseidon2 jet is a list of open terms:
the jet is the variable `J`, an atom in the heap (`addStmtsO`, the open
terms built by `obuild`).  On closed terms the heap is the one
`Ski/Composed.lean` builds (`cHeap_eq`), so nothing changes for statements
without the jet.

**`AcceptsCP`** is `AcceptsCJ` with one more kind of row: the jet's
(`P2Jet.p2Row`).  **`composedP_sound`**: a table it accepts from the
composed machine of the open statement proves the closed statement, the
jet closed to its SKI implementation `Poseidon2SKI.Pbits`: every verifier,
applied to the bits and the region's witness, evaluates to `K`.
-/

namespace CompM

open Mach Stmt Compose Wit BExpr Poseidon2SKI

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

-- ---------------------------------------------------------------------------
-- The AIR with the Poseidon2 jet
-- ---------------------------------------------------------------------------

/-- A row: a step, an instantiation at a listed root, a halted row repeated
    (`Air.NormRow`), or the Poseidon2 jet at the atom `J`. -/
def NormRowP (M : List Cell) (jroots : List (Nat × Nat)) (jets : List Air.Jet) (J : Nat)
    (r r' : Air.Row) : Prop :=
  Air.NormRow M jroots jets r r' ∨ P2Jet.p2Row M J r = some r'

/-- **The AIR with jets, segments and the Poseidon2 jet accepts**: as
    `AcceptsCJ`, each row within a segment a `NormRowP`. -/
structure AcceptsCP (M : List Cell) (m0 : Mach) (jroots : List (Nat × Nat)) (jets : List Air.Jet)
    (J : Nat) (roots : List Nat) (nilA n : Nat) (e : Nat → Nat) (row : Nat → Air.Row) : Prop where
  npos : 0 < n
  heap0 : M.take (row 0).ctr = m0.heap
  hd0 : (row 0).hd = roots.getD 0 0
  stk0 : (row 0).stk = nilA
  ctr0 : (row 0).ctr = m0.heap.length
  emono : ∀ j, j + 1 < n → e j < e (j + 1)
  restart : ∀ j, j + 1 < n → row (e j + 1) = ⟨roots.getD (j + 1) 0, nilA, (row (e j)).ctr⟩
  trans : ∀ i, i < e (n - 1) → (∀ j, j + 1 < n → i ≠ e j) → NormRowP M jroots jets J (row i) (row (i + 1))
  ends : ∀ j, j < n → Air.rd M (row (e j)).ctr (row (e j)).hd = some .K ∧
    Air.rd M (row (e j)).ctr (row (e j)).stk = some .nil

theorem owstep_cstep {α β : Type} {cc : DataJet.CContract α β} {j : Nat} {t u : OTerm} (h : OWStep t u) :
    DataJet.CStep cc j t u := by
  induction h with
  | S f g x => exact .S f g x
  | K x y => exact .K x y
  | I x => exact .I x
  | left x _ ih => exact .left x ih
  | right f _ ih => exact .right f ih

theorem CSteps.trans {α β : Type} {cc : DataJet.CContract α β} {j : Nat} {t u v : OTerm}
    (h₁ : DataJet.CSteps cc j t u) (h₂ : DataJet.CSteps cc j u v) : DataJet.CSteps cc j t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem owsteps_csteps {α β : Type} {cc : DataJet.CContract α β} {j : Nat} {t u : OTerm} (h : OWSteps t u) :
    DataJet.CSteps cc j t u := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (owstep_cstep h) ih

/-- **A row, read back**: the counter moves forward within the table, and
    the state's open term reduces by the jet's reduction. -/
theorem normRowP_spec {M : List Cell} {jroots : List (Nat × Nat)} {jets : List Air.Jet} {J c0 : Nat}
    (hroots : Air.RootsOK (M.take c0) jroots jets) {r r' : Air.Row} (hc0 : c0 ≤ r.ctr)
    (hc : r.ctr ≤ M.length) (h : NormRowP M jroots jets J r r') {t : OTerm}
    (hdec : odecode (Air.st M r) = some t) :
    r.ctr ≤ r'.ctr ∧ r'.ctr ≤ M.length ∧
      ∃ u, odecode (Air.st M r') = some u ∧ DataJet.CSteps poseidon2B J t u := by
  rcases h with hn | hp
  · obtain ⟨h1, h2, hJ, _⟩ := Air.normRow_spec hroots hc0 hc hn
    obtain ⟨u, hu, hw⟩ := ojsteps_owsteps hdec hJ
    exact ⟨h1, h2, u, hu, owsteps_csteps hw⟩
  · obtain ⟨h2, u, hu, hs⟩ := P2Jet.p2Row_cstep hp hc hdec
    exact ⟨P2Jet.p2Row_ctr hp, h2, u, hu, .step hs (.refl _)⟩

section

variable {M : List Cell} {m0 : Mach} {jroots : List (Nat × Nat)} {jets : List Air.Jet} {J : Nat}
  {roots : List Nat} {nilA n : Nat} {e : Nat → Nat} {row : Nat → Air.Row}

/-- **Within a segment, the run reads back as the jet's reduction.** -/
theorem AcceptsCP.within (h : AcceptsCP M m0 jroots jets J roots nilA n e row)
    (hroots : Air.RootsOK m0.heap jroots jets) {j : Nat} (hj : j < n)
    (hc : (row (segStart e j)).ctr ≤ M.length) (hc0 : (row 0).ctr ≤ (row (segStart e j)).ctr)
    {t0 : OTerm} (hdec : odecode (Air.st M (row (segStart e j))) = some t0) :
    ∀ b, segStart e j ≤ b → b ≤ e j →
      (row b).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row b).ctr ∧
      ∃ t, odecode (Air.st M (row b)) = some t ∧ DataJet.CSteps poseidon2B J t0 t := by
  have hr0 : Air.RootsOK (M.take (row 0).ctr) jroots jets := by rw [h.heap0]; exact hroots
  have hen : e j ≤ e (n - 1) := emono_le h.emono (by omega) (by omega)
  intro b hb1 hb2
  induction b with
  | zero =>
    have hs0 : segStart e j = 0 := by omega
    rw [hs0] at hdec ⊢
    exact ⟨by rw [← hs0]; exact hc, Nat.le_refl _, t0, hdec, .refl _⟩
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hb1 with hl | hl
    · obtain ⟨hcb, hsb, t, ht, hst⟩ := ih (by omega) (by omega)
      have hn := h.trans b (by omega) (not_end h.emono hj (by omega) (by omega))
      obtain ⟨h1, h2, u, hu, hsu⟩ := normRowP_spec hr0 (Nat.le_trans hc0 hsb) hcb hn ht
      exact ⟨h2, Nat.le_trans hsb h1, u, hu, CSteps.trans hst hsu⟩
    · rw [← hl]
      exact ⟨hc, Nat.le_refl _, t0, hdec, .refl _⟩

/-- The counters of a segment's rows, without reading back. -/
theorem AcceptsCP.within_ctr (h : AcceptsCP M m0 jroots jets J roots nilA n e row)
    (hroots : Air.RootsOK m0.heap jroots jets) {j : Nat} (hj : j < n)
    (hc : (row (segStart e j)).ctr ≤ M.length) (hc0 : (row 0).ctr ≤ (row (segStart e j)).ctr) :
    ∀ b, segStart e j ≤ b → b ≤ e j → (row b).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row b).ctr := by
  have hr0 : Air.RootsOK (M.take (row 0).ctr) jroots jets := by rw [h.heap0]; exact hroots
  have hen : e j ≤ e (n - 1) := emono_le h.emono (by omega) (by omega)
  intro b hb1 hb2
  induction b with
  | zero =>
    have hs0 : segStart e j = 0 := by omega
    rw [hs0]
    exact ⟨by rw [← hs0]; exact hc, Nat.le_refl _⟩
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hb1 with hl | hl
    · obtain ⟨hcb, hsb⟩ := ih (by omega) (by omega)
      have hn := h.trans b (by omega) (not_end h.emono hj (by omega) (by omega))
      rcases hn with hn | hp
      · obtain ⟨h1, h2, _, _⟩ := Air.normRow_spec hr0 (Nat.le_trans hc0 hsb) hcb hn
        exact ⟨h2, Nat.le_trans hsb h1⟩
      · exact ⟨P2Jet.p2Row_len hp hcb, Nat.le_trans hsb (P2Jet.p2Row_ctr hp)⟩
    · rw [← hl]
      exact ⟨hc, Nat.le_refl _⟩

/-- **Every segment's counters**: its first row's lies between the
    machine's and the table's length, and its last row's within the table. -/
theorem AcceptsCP.runs (h : AcceptsCP M m0 jroots jets J roots nilA n e row)
    (hroots : Air.RootsOK m0.heap jroots jets) :
    ∀ j, j < n → (row (segStart e j)).ctr ≤ M.length ∧
      m0.heap.length ≤ (row (segStart e j)).ctr ∧ (row (e j)).ctr ≤ M.length ∧
      (row (segStart e j)).ctr ≤ (row (e j)).ctr := by
  have hc0 : (row 0).ctr ≤ M.length := by
    have := congrArg List.length h.heap0
    rw [List.length_take, ← h.ctr0] at this
    omega
  have seg : ∀ j, j < n → (row (segStart e j)).ctr ≤ M.length →
      (row 0).ctr ≤ (row (segStart e j)).ctr →
      (row (e j)).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row (e j)).ctr := fun j hj hc hc0' =>
    h.within_ctr hroots hj hc hc0' (e j) (segStart_le h.emono j hj) (Nat.le_refl _)
  intro j
  induction j with
  | zero =>
    intro hn
    obtain ⟨a, b⟩ := seg 0 hn hc0 (Nat.le_refl _)
    exact ⟨hc0, by rw [show segStart e 0 = 0 from rfl, h.ctr0]; exact Nat.le_refl _, a, b⟩
  | succ j ih =>
    intro hn
    obtain ⟨_, hm, he, hse⟩ := ih (by omega)
    have hr := h.restart j hn
    have hc : (row (segStart e (j + 1))).ctr = (row (e j)).ctr := by
      show (row (e j + 1)).ctr = _
      rw [hr]
    obtain ⟨a, b⟩ := seg (j + 1) hn (by rw [hc]; exact he) (by rw [hc, h.ctr0]; omega)
    exact ⟨by rw [hc]; exact he, by rw [hc]; omega, a, b⟩

end

/-- The jet's variable closed to `Pbits`, any other to `K`. -/
def jetEnv (J : Nat) : Nat → Term := fun i => if i = J then Pbits else K

/-- **A table the AIR with the Poseidon2 jet accepts from the composed
    machine of an open statement proves the closed statement**, the jet's
    variable closed to any implementation of the contract: with a
    well-formed region and the template jets licensed over the filled heap,
    its bits and the region's witness make every verifier evaluate to `K`. -/
theorem composedP_sound_of {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Vs : List OTerm} {J : Nat}
    (σ : Nat → Term) (himpl : DataJet.CImplements poseidon2B (σ J))
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {jroots : List (Nat × Nat)} {jets : List Air.Jet}
    (hroots : Air.RootsOK (cMachineO ρ shp region Vs).heap jroots jets)
    {M : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (h : AcceptsCP M (cMachineO ρ shp region Vs) jroots jets J (cHeapO ρ shp region Vs).2
      (cHeapO ρ shp region Vs).1.length Vs.length e row) :
    ∃ w, cWitness ρ (BT.nleaves shp) region = some w ∧
      EvalRel (Vs.map (·.close σ), SameShape shp) (fillB shp ρ 0) w := by
  let N := BT.nleaves shp
  obtain ⟨w, hw⟩ := witnessOf_some (slots_wf ρ N hr) (by simp [slotHeap_length]; omega)
  refine ⟨w, hw, fillB_shape shp ρ 0, fun P hP => ?_⟩
  obtain ⟨V, hV, rfl⟩ := List.mem_map.1 hP
  obtain ⟨j, hj, hVj⟩ := List.getElem_of_mem hV
  have hj' : Vs[j]? = some V := by rw [List.getElem?_eq_getElem hj, hVj]
  obtain ⟨_, hdec⟩ := cMachineO_decode (Vs := Vs) hw
  have hroot := hdec j V hj'
  obtain ⟨hc, hm, _, _⟩ := h.runs hroots j hj
  let m0 := cMachineO ρ shp region Vs
  have hregs : (row (segStart e j)).hd = (cHeapO ρ shp region Vs).2.getD j 0 ∧
      (row (segStart e j)).stk = (cHeapO ρ shp region Vs).1.length := by
    cases j with
    | zero => exact ⟨h.hd0, h.stk0⟩
    | succ j =>
      have := h.restart j hj
      show (row (e j + 1)).hd = _ ∧ (row (e j + 1)).stk = _
      rw [this]
      exact ⟨rfl, rfl⟩
  have hm0 : m0.heap = M.take (row 0).ctr := h.heap0.symm
  have hc0 : (row 0).ctr = m0.heap.length := h.ctr0
  have hle : (row 0).ctr ≤ (row (segStart e j)).ctr := by rw [hc0]; exact hm
  have hlen : (Air.st M (row (segStart e j))).heap.length = (row (segStart e j)).ctr := by
    simp [Air.st, Air.take_length hc]
  have hstart : odecode (Air.st M (row (segStart e j))) =
      some (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) := by
    have e1 : V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO = appL (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) [] := rfl
    rw [e1]
    apply odecode_of
    · show otermAt (M.take (row (segStart e j)).ctr) (_ + 1) (row (segStart e j)).hd = _
      rw [hregs.1]
      rw [hm0] at hroot
      refine Air.otermAt_take hle ?_ hroot
      rw [← hm0, hlen]
      show m0.heap.length + 1 ≤ _
      omega
    · show ostackAt (M.take (row (segStart e j)).ctr) (_ + 1) (row (segStart e j)).stk = _
      rw [hregs.2]
      have hn : (M.take (row (segStart e j)).ctr)[(cHeapO ρ shp region Vs).1.length]? = some .nil := by
        have h1 : m0.heap[(cHeapO ρ shp region Vs).1.length]? = some .nil := by simp [m0, cMachineO]
        rw [hm0, List.getElem?_take] at h1
        rw [List.getElem?_take]
        split at h1
        · rw [if_pos (by omega)]; exact h1
        · cases h1
      unfold ostackAt
      rw [hn]
  obtain ⟨_, _, v, hv, hsteps⟩ := h.within hroots hj hc (by rw [hc0]; exact hm) hstart (e j)
    (segStart_le h.emono j hj) (Nat.le_refl _)
  have hK : v = .K := by
    refine odecode_K hv ?_ ?_
    · rw [← (h.ends j hj).1, Air.rd_eq]; rfl
    · rw [← (h.ends j hj).2, Air.rd_eq]; rfl
  rw [hK] at hsteps
  have hw' : WSteps (V.close σ ⬝ (fillB shp ρ 0).enc ⬝ w) K := by
    have := hsteps.close σ himpl
    change WSteps (V.close σ ⬝ (fillB shp ρ 0).enc.toO.close σ ⬝ w.toO.close σ) K at this
    rw [close_toO, close_toO] at this
    exact this
  obtain ⟨v', hev, hv'⟩ := eval_of_wsteps hw' .K
  obtain ⟨_, hhd⟩ := small_lemma_whnf hev.2 hv'
  rw [chead_K hhd.symm] at hev
  exact hev

/-- **The same with the jet closed to `Pbits`**, every other variable to
    `K`. -/
theorem composedP_sound {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Vs : List OTerm} {J : Nat}
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {jroots : List (Nat × Nat)} {jets : List Air.Jet}
    (hroots : Air.RootsOK (cMachineO ρ shp region Vs).heap jroots jets)
    {M : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (h : AcceptsCP M (cMachineO ρ shp region Vs) jroots jets J (cHeapO ρ shp region Vs).2
      (cHeapO ρ shp region Vs).1.length Vs.length e row) :
    ∃ w, cWitness ρ (BT.nleaves shp) region = some w ∧
      EvalRel (Vs.map (·.close (jetEnv J)), SameShape shp) (fillB shp ρ 0) w := by
  refine composedP_sound_of (jetEnv J) ?_ hr hroots h
  show DataJet.CImplements poseidon2B (if J = J then Pbits else K)
  rw [if_pos rfl]
  exact Pbits_implements

end CompM
