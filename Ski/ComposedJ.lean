import Ski.Composed
import Ski.JetPublic
import Ski.Transfer

open Term

/-!
# The composed machine with jets

The composed machine (`CompM.cMachine`, `CompM.AcceptsC`) runs one segment
per term, each from its root over the public nil to `K` over the nil.
With jets (Avon's `docs/ZK-JETS.md`), a row within a segment may also
instantiate a jet at a licensed root (`Air.NormRow`), which is weak
reduction (`Mach.inst_sound_g`), not head reduction.  A jetted run proves
evaluation only up to weak reduction of the value, keeping its head and
arity (`small_lemma_whnf`); a segment ending at `K` over the empty stack
has value `K`, of arity `0`, and a weak head normal form with `K`'s head
and arity is `K` (`chead_K`).  So the composed statement is proved exactly
as without jets (`composedJ_sound`), given the jet table's roots licensed
over the filled heap (`Air.rootsOK_filled`).

`checkCJ` decides it on a table, as `checkC` does without jets
(`checkCJ_sound`).
-/

namespace CompM

open Mach Stmt Compose Wit BExpr

/-- **A head and arity of `K`'s is `K`.** -/
theorem chead_K : ∀ {v : Term}, chead v = chead K → v = K
  | .S, h => by simp [chead] at h
  | .K, _ => rfl
  | .I, h => by simp [chead] at h
  | .app _ _, h => by simp [chead] at h

/-- **The AIR with jets and segments accepts** a table over `M` from the
    composed state `m0`, for the public jet roots and jets: as `AcceptsC`,
    each row within a segment a step, an instantiation at a listed root,
    or a halted row repeated (`Air.NormRow`). -/
structure AcceptsCJ (M : List Cell) (m0 : Mach) (jroots : List (Nat × Nat)) (jets : List Air.Jet)
    (roots : List Nat) (nilA n : Nat) (e : Nat → Nat) (row : Nat → Air.Row) : Prop where
  npos : 0 < n
  heap0 : M.take (row 0).ctr = m0.heap
  hd0 : (row 0).hd = roots.getD 0 0
  stk0 : (row 0).stk = nilA
  ctr0 : (row 0).ctr = m0.heap.length
  emono : ∀ j, j + 1 < n → e j < e (j + 1)
  restart : ∀ j, j + 1 < n → row (e j + 1) = ⟨roots.getD (j + 1) 0, nilA, (row (e j)).ctr⟩
  trans : ∀ i, i < e (n - 1) → (∀ j, j + 1 < n → i ≠ e j) →
    Air.NormRow M jroots jets (row i) (row (i + 1))
  ends : ∀ j, j < n → Air.rd M (row (e j)).ctr (row (e j)).hd = some .K ∧
    Air.rd M (row (e j)).ctr (row (e j)).stk = some .nil

section

variable {M : List Cell} {m0 : Mach} {jroots : List (Nat × Nat)} {jets : List Air.Jet}
  {roots : List Nat} {nilA n : Nat} {e : Nat → Nat} {row : Nat → Air.Row}

/-- **Within a segment, the run is jetted**: from the segment's first row,
    each row's counter stays within the table and the run reaches it by
    jetted steps. -/
theorem AcceptsCJ.within (h : AcceptsCJ M m0 jroots jets roots nilA n e row)
    (hroots : Air.RootsOK m0.heap jroots jets) {j : Nat} (hj : j < n)
    (hc : (row (segStart e j)).ctr ≤ M.length) (hc0 : (row 0).ctr ≤ (row (segStart e j)).ctr) :
    ∀ b, segStart e j ≤ b → b ≤ e j →
      (row b).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row b).ctr ∧
      JSteps (Air.st M (row (segStart e j))) (Air.st M (row b)) := by
  have hr0 : Air.RootsOK (M.take (row 0).ctr) jroots jets := by rw [h.heap0]; exact hroots
  have hen : e j ≤ e (n - 1) := emono_le h.emono (by omega) (by omega)
  intro b hb1 hb2
  induction b with
  | zero =>
    have hs0 : segStart e j = 0 := by omega
    rw [hs0]
    exact ⟨by rw [← hs0]; exact hc, Nat.le_refl _, .refl _⟩
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hb1 with hl | hl
    · obtain ⟨hcb, hsb, hJ⟩ := ih (by omega) (by omega)
      have hn := h.trans b (by omega) (not_end h.emono hj (by omega) (by omega))
      obtain ⟨h1, h2, hJ1, _⟩ := Air.normRow_spec hr0 (Nat.le_trans hc0 hsb) hcb hn
      exact ⟨h2, Nat.le_trans hsb h1, JSteps.snoc_all hJ hJ1⟩
    · rw [← hl]
      exact ⟨hc, Nat.le_refl _, .refl _⟩

/-- **Every segment runs, jetted**: its first row's counter lies between
    the machine's and the table's length, and its first row reaches its last
    by jetted steps. -/
theorem AcceptsCJ.runs (h : AcceptsCJ M m0 jroots jets roots nilA n e row)
    (hroots : Air.RootsOK m0.heap jroots jets) :
    ∀ j, j < n → (row (segStart e j)).ctr ≤ M.length ∧
      m0.heap.length ≤ (row (segStart e j)).ctr ∧ (row (e j)).ctr ≤ M.length ∧
      (row (segStart e j)).ctr ≤ (row (e j)).ctr ∧
      JSteps (Air.st M (row (segStart e j))) (Air.st M (row (e j))) := by
  have hc0 : (row 0).ctr ≤ M.length := by
    have := congrArg List.length h.heap0
    rw [List.length_take, ← h.ctr0] at this
    omega
  have seg : ∀ j, j < n → (row (segStart e j)).ctr ≤ M.length →
      (row 0).ctr ≤ (row (segStart e j)).ctr →
      (row (e j)).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row (e j)).ctr ∧
      JSteps (Air.st M (row (segStart e j))) (Air.st M (row (e j))) := fun j hj hc hc0' =>
    h.within hroots hj hc hc0' (e j) (segStart_le h.emono j hj) (Nat.le_refl _)
  intro j
  induction j with
  | zero =>
    intro hn
    obtain ⟨a, b, c⟩ := seg 0 hn hc0 (Nat.le_refl _)
    exact ⟨hc0, by rw [show segStart e 0 = 0 from rfl, h.ctr0]; exact Nat.le_refl _, a, b, c⟩
  | succ j ih =>
    intro hn
    obtain ⟨_, hm, he, hse, _⟩ := ih (by omega)
    have hr := h.restart j hn
    have hc : (row (segStart e (j + 1))).ctr = (row (e j)).ctr := by
      show (row (e j + 1)).ctr = _
      rw [hr]
    obtain ⟨a, b, c⟩ := seg (j + 1) hn (by rw [hc]; exact he) (by rw [hc, h.ctr0]; omega)
    exact ⟨by rw [hc]; exact he, by rw [hc]; omega, a, b, c⟩

end

/-- **A table the AIR with jets accepts from the composed machine proves the
    composed statement**: with a well-formed region and the jet roots
    licensed over the filled heap, its bits and the region's witness make
    every term evaluate to `K`. -/
theorem composedJ_sound {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Ps : List Term}
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {jroots : List (Nat × Nat)} {jets : List Air.Jet}
    (hroots : Air.RootsOK (cMachine ρ shp region Ps).heap jroots jets)
    {M : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (h : AcceptsCJ M (cMachine ρ shp region Ps) jroots jets (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row) :
    ∃ w, cWitness ρ (BT.nleaves shp) region = some w ∧
      EvalRel (Ps, SameShape shp) (fillB shp ρ 0) w := by
  let N := BT.nleaves shp
  obtain ⟨w, hw⟩ := witnessOf_some (slots_wf ρ N hr) (by simp [slotHeap_length]; omega)
  refine ⟨w, hw, fillB_shape shp ρ 0, fun P hP => ?_⟩
  obtain ⟨j, hj, hPj⟩ := List.getElem_of_mem hP
  have hj' : Ps[j]? = some P := by rw [List.getElem?_eq_getElem hj, hPj]
  obtain ⟨_, hdec⟩ := cMachine_decode (Ps := Ps) hw
  have hroot := hdec j P hj'
  obtain ⟨hc, hm, _, _, hrun⟩ := h.runs hroots j hj
  let m0 := cMachine ρ shp region Ps
  -- The segment's first row: the root over the nil.
  have hregs : (row (segStart e j)).hd = (cHeap ρ shp region Ps).2.getD j 0 ∧
      (row (segStart e j)).stk = (cHeap ρ shp region Ps).1.length := by
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
  have hstart : odecode (Air.st M (row (segStart e j))) = some (P ⬝ (fillB shp ρ 0).enc ⬝ w).toO := by
    have e1 : (P ⬝ (fillB shp ρ 0).enc ⬝ w).toO = appL (P.toO ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) [] := rfl
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
      have hn : (M.take (row (segStart e j)).ctr)[(cHeap ρ shp region Ps).1.length]? = some .nil := by
        have h1 : m0.heap[(cHeap ρ shp region Ps).1.length]? = some .nil := by simp [m0, cMachine]
        rw [hm0, List.getElem?_take] at h1
        rw [List.getElem?_take]
        split at h1
        · rw [if_pos (by omega)]; exact h1
        · cases h1
      unfold ostackAt
      rw [hn]
  obtain ⟨v, hv, hsteps⟩ := ojsteps_owsteps hstart hrun
  have hK : v = .K := by
    refine odecode_K hv ?_ ?_
    · rw [← (h.ends j hj).1, Air.rd_eq]; rfl
    · rw [← (h.ends j hj).2, Air.rd_eq]; rfl
  rw [hK] at hsteps
  -- Weak reduction to `K`: the evaluation's value has `K`'s head and arity.
  have hw : WSteps (P ⬝ (fillB shp ρ 0).enc ⬝ w) K := by
    have := hsteps.close (fun _ => K)
    rw [close_toO] at this
    exact this
  obtain ⟨v', hev, hv'⟩ := eval_of_wsteps hw .K
  obtain ⟨_, hhd⟩ := small_lemma_whnf hev.2 hv'
  rw [chead_K hhd.symm] at hev
  exact hev

-- ---------------------------------------------------------------------------
-- The checker
-- ---------------------------------------------------------------------------

/-- **The composed checker with jets**: `checkC`'s checks, each row within a
    segment a step, an instantiation at a listed root, or a halted row
    repeated (`Air.normB`), and the jet roots licensed over the filled
    heap (`Air.rootsOKB`). -/
def checkCJ (shp : BT) (W : Nat) (Ps : List Term) (jroots : List (Nat × Nat)) (jets : List Air.Jet)
    (A : Array Cell) (ends : Array Nat) (R : Array Air.Row) : Bool :=
  let N := BT.nleaves shp
  let region := regionOf A N W
  let m0 := cMachine (bitsOf A) shp region Ps
  let roots := (cHeap (bitsOf A) shp region Ps).2
  let nilA := (cHeap (bitsOf A) shp region Ps).1.length
  let n := Ps.length
  let g := fun a => A[a]?
  let row := fun i => R.getD i ⟨0, 0, 0⟩
  let e := fun j => ends.getD j 0
  decide (0 < n) && decide (region.length = W) &&
    (List.range W).all (fun i =>
      match region[i]? with
      | some c => cellOK (N + 3 + i) c
      | none => false) &&
    Air.rootsOKB m0.heap jroots jets &&
    decide (A.toList.take (row 0).ctr = m0.heap) && decide ((row 0).hd = roots.getD 0 0) &&
    decide ((row 0).stk = nilA) && decide ((row 0).ctr = m0.heap.length) &&
    (List.range (n - 1)).all (fun j => decide (e j < e (j + 1)) &&
      decide (row (e j + 1) = ⟨roots.getD (j + 1) 0, nilA, (row (e j)).ctr⟩)) &&
    (List.range (e (n - 1))).all (fun i => (List.range (n - 1)).any (fun j => e j == i) ||
      Air.normB g jroots jets (row i) (row (i + 1))) &&
    (List.range n).all (fun j => Air.rdG g (row (e j)).ctr (row (e j)).hd == some .K &&
      Air.rdG g (row (e j)).ctr (row (e j)).stk == some .nil)

/-- **`checkCJ` is sound**: a table it accepts proves the composed
    statement, for the bits its memory sets and the witness its region
    holds. -/
theorem checkCJ_sound {shp : BT} {W : Nat} {Ps : List Term} {jroots : List (Nat × Nat)}
    {jets : List Air.Jet} {A : Array Cell} {ends : Array Nat} {R : Array Air.Row}
    (h : checkCJ shp W Ps jroots jets A ends R = true) :
    ∃ w, cWitness (bitsOf A) (BT.nleaves shp) (regionOf A (BT.nleaves shp) W) = some w ∧
      EvalRel (Ps, SameShape shp) (fillB shp (bitsOf A) 0) w := by
  unfold checkCJ at h
  dsimp only at h
  rw [Air.getElem?_fun] at h
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hW⟩, hwf⟩, hro⟩, h0⟩, h1⟩, h2⟩, h3⟩, hmono⟩, htr⟩, hends⟩ := h
  refine composedJ_sound (fun i c hc => ?_) (Air.rootsOKB_sound hro) (e := fun j => ends.getD j 0)
    (row := fun i => R.getD i ⟨0, 0, 0⟩) (M := A.toList) ⟨hn, h0, h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · have hi : i < W := by
      rcases Nat.lt_or_ge i W with hl | hl
      · exact hl
      · rw [List.getElem?_eq_none (by rw [hW]; exact hl)] at hc; cases hc
    have := List.all_eq_true.1 hwf i (List.mem_range.2 hi)
    rw [hc] at this
    exact this
  · intro j hj
    have := List.all_eq_true.1 hmono j (List.mem_range.2 (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_iff] at this
    exact this.1
  · intro j hj
    have := List.all_eq_true.1 hmono j (List.mem_range.2 (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_iff] at this
    exact this.2
  · intro i hi hne
    have := List.all_eq_true.1 htr i (List.mem_range.2 hi)
    simp only [Bool.or_eq_true] at this
    rcases this with ha | hs
    · obtain ⟨j, hj, e⟩ := List.any_eq_true.1 ha
      rw [beq_iff_eq] at e
      exact absurd e.symm (hne j (by have := List.mem_range.1 hj; omega))
    · exact Air.normB_sound (M := A.toList) (by simpa only [Array.getElem?_toList] using hs)
  · intro j hj
    have := List.all_eq_true.1 hends j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨by rw [Air.rd_G]; exact this.1, by rw [Air.rd_G]; exact this.2⟩

end CompM
