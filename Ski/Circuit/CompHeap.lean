import Ski.Circuit.CompStep

/-!
# The composed machine's cells point into its heap

Its slots, a blank region, the bits' encoding (`pbuild`) and the
statements (`addStmts`) each point only below their own address, so every
public cell's fields, and every root, lie below the heap's length
(`cMachine_fits`).
-/

namespace Circuit

open Compose CompM Stmt Mach Wit

theorem pbuild_fits (bound : Nat) : ∀ (t : OTerm) (h : List Cell), Fits h →
    (∀ x, Occ x t → x < bound ∧ slotPtr x < h.length) →
    Fits (pbuild bound h t).1 ∧ (pbuild bound h t).2 < (pbuild bound h t).1.length ∧
      h.length ≤ (pbuild bound h t).1.length
  | .S, h, hf, _ => ⟨fits_push hf ⟨Nat.succ_pos _, Nat.succ_pos _⟩, by simp [pbuild, alloc], by simp [pbuild, alloc]⟩
  | .K, h, hf, _ => ⟨fits_push hf ⟨Nat.succ_pos _, Nat.succ_pos _⟩, by simp [pbuild, alloc], by simp [pbuild, alloc]⟩
  | .I, h, hf, _ => ⟨fits_push hf ⟨Nat.succ_pos _, Nat.succ_pos _⟩, by simp [pbuild, alloc], by simp [pbuild, alloc]⟩
  | .var x, h, hf, hv => by
    have := hv x (.var x)
    simp only [pbuild, if_pos this.1]
    exact ⟨hf, this.2, Nat.le_refl _⟩
  | .app f a, h, hf, hv => by
    obtain ⟨f1, p1, l1⟩ := pbuild_fits bound f h hf (fun x hx => hv x (.left _ hx))
    obtain ⟨f2, p2, l2⟩ := pbuild_fits bound a (pbuild bound h f).1 f1
      (fun x hx => ⟨(hv x (.right _ hx)).1, Nat.lt_of_lt_of_le (hv x (.right _ hx)).2 l1⟩)
    show Fits ((pbuild bound (pbuild bound h f).1 a).1 ++ [.app (pbuild bound h f).2 (pbuild bound (pbuild bound h f).1 a).2]) ∧
      (pbuild bound (pbuild bound h f).1 a).1.length <
        ((pbuild bound (pbuild bound h f).1 a).1 ++ [_]).length ∧
      h.length ≤ ((pbuild bound (pbuild bound h f).1 a).1 ++ [_]).length
    rw [List.length_append, List.length_singleton]
    refine ⟨fits_push f2 ⟨?_, ?_⟩, Nat.lt_succ_self _, ?_⟩
    · show (pbuild bound h f).2 < _; omega
    · show (pbuild bound (pbuild bound h f).1 a).2 < _; omega
    · omega

theorem addStmts_fits (pe wr : Nat) : ∀ (Ps : List Term) (h : List Cell), Fits h → pe < h.length → wr < h.length →
    Fits (addStmts pe wr h Ps).1 ∧ (∀ r ∈ (addStmts pe wr h Ps).2, r < (addStmts pe wr h Ps).1.length) ∧
      h.length ≤ (addStmts pe wr h Ps).1.length
  | [], h, hf, _, _ => by
    simp only [addStmts]
    exact ⟨hf, (fun _ h' => nomatch h'), Nat.le_refl _⟩
  | P :: Ps, h, hf, hpe, hwr => by
    obtain ⟨f2, p2, l2⟩ := build_fits P h hf
    have a1 : (cellFields (Cell.app (build h P).2 pe)).1 < (build h P).1.length + 1 ∧
        (cellFields (Cell.app (build h P).2 pe)).2 < (build h P).1.length + 1 := by
      simp only [cellFields]; exact ⟨by omega, by omega⟩
    have g1 := fits_push f2 a1
    have a2 : (cellFields (Cell.app (build h P).1.length wr)).1 < ((build h P).1 ++ [Cell.app (build h P).2 pe]).length + 1 ∧
        (cellFields (Cell.app (build h P).1.length wr)).2 < ((build h P).1 ++ [Cell.app (build h P).2 pe]).length + 1 := by
      simp only [cellFields, List.length_append, List.length_singleton]; exact ⟨by omega, by omega⟩
    have g2 := fits_push g1 a2
    have hl : ((build h P).1 ++ [Cell.app (build h P).2 pe] ++ [Cell.app (build h P).1.length wr]).length = (build h P).1.length + 2 := by
      simp
    obtain ⟨i1, i2, i3⟩ := addStmts_fits pe wr Ps _ g2 (by rw [hl]; omega) (by rw [hl]; omega)
    have e : (build h P).1 ++ [Cell.app (build h P).2 pe, Cell.app (build h P).1.length wr] =
        (build h P).1 ++ [Cell.app (build h P).2 pe] ++ [Cell.app (build h P).1.length wr] := by simp
    show Fits (addStmts pe wr ((build h P).1 ++ [.app (build h P).2 pe, .app (build h P).1.length wr]) Ps).1 ∧
      (∀ r ∈ ((build h P).1.length + 1) :: (addStmts pe wr ((build h P).1 ++ [.app (build h P).2 pe, .app (build h P).1.length wr]) Ps).2,
        r < (addStmts pe wr ((build h P).1 ++ [.app (build h P).2 pe, .app (build h P).1.length wr]) Ps).1.length) ∧
      h.length ≤ (addStmts pe wr ((build h P).1 ++ [.app (build h P).2 pe, .app (build h P).1.length wr]) Ps).1.length
    rw [e]
    refine ⟨i1, fun r hr => ?_, by rw [hl] at i3; omega⟩
    rcases List.mem_cons.1 hr with rfl | hr
    · rw [hl] at i3; omega
    · exact i2 r hr

theorem occ_pair {x : Nat} {a b : OTerm} (h : Occ x (pairO a b)) : Occ x a ∨ Occ x b := by
  unfold pairO at h
  cases h with
  | left _ h1 =>
    cases h1 with
    | left _ h2 => cases h2
    | right _ h2 =>
      cases h2 with
      | left _ h3 =>
        cases h3 with
        | left _ h4 => cases h4
        | right _ h4 => cases h4
      | right _ h3 =>
        cases h3 with
        | left _ h4 => cases h4
        | right _ h4 => exact .inl h4
  | right _ h1 =>
    cases h1 with
    | left _ h2 => cases h2
    | right _ h2 => exact .inr h2

/-- The encoding's variables are its leaves' slots. -/
theorem encO_occ : ∀ (t : BT) (off x : Nat), Occ x (encO t off) → off + 2 ≤ x ∧ x < off + 2 + BT.nleaves t
  | .leaf _, off, x, hx => by
    cases hx
    exact ⟨Nat.le_refl _, by simp only [BT.nleaves]; omega⟩
  | .node l r, off, x, hx => by
    simp only [BT.nleaves]
    rcases occ_pair hx with h | h
    · have := encO_occ l off x h; exact ⟨by omega, by omega⟩
    · have := encO_occ r (off + BT.nleaves l) x h; exact ⟨by omega, by omega⟩

/-- **The composed machine points into its heap**: its cells, and its roots. -/
theorem cMachine_fits (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true) :
    Fits (cMachine ρ shp region Ps).heap ∧
      ∀ r ∈ (cHeap ρ shp region Ps).2, r < (cMachine ρ shp region Ps).heap.length := by
  let N := BT.nleaves shp
  let h0 := slotHeap ρ N ++ region
  have hwf := slots_wf ρ N hr
  have hl0 : N + 3 ≤ h0.length := by simp [h0, slotHeap_length]
  have f0 : Fits h0 := by
    intro c hc
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hc
    have := hwf i c (by rw [List.getElem?_eq_getElem hi, e])
    cases c with
    | app a b =>
      simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨by simp only [cellFields]; omega, by simp only [cellFields]; omega⟩
    | S | K | I => exact ⟨by simp only [cellFields]; omega, by simp only [cellFields]; omega⟩
    | nil | cons _ _ | atom _ => simp [cellOK] at this
  have hv : ∀ x, Occ x (encO shp 0) → x < N + 2 ∧ slotPtr x < h0.length := by
    intro x hx
    have := encO_occ shp 0 x hx
    have hN : BT.nleaves shp = N := rfl
    rw [hN] at this
    refine ⟨by omega, ?_⟩
    rcases x with _ | _ | x
    · omega
    · omega
    · show x + 3 < h0.length; omega
  obtain ⟨f1, p1, l1⟩ := pbuild_fits (N + 2) (encO shp 0) h0 f0 hv
  obtain ⟨f2, rts, l2⟩ := addStmts_fits (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1) Ps _ f1 p1
    (by omega)
  refine ⟨fits_push f2 ⟨by simp only [cellFields]; omega, by simp only [cellFields]; omega⟩, fun r hr => ?_⟩
  have := rts r hr
  show r < ((cHeap ρ shp region Ps).1 ++ [Cell.nil]).length
  rw [List.length_append, List.length_singleton]
  exact Nat.lt_succ_of_lt this

end Circuit
