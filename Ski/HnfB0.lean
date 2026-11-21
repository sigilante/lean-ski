import Ski.HnfProd
open Term

/-!
# A term with an hnf-less subterm is not productive (lemma B0)

`BotAt n t` says that a subterm without a head normal form (fold `36`) sits within spine-
nesting depth `n` of `t`: either `t` itself has fold `36`, or some item of `t`'s frame satisfies
`BotAt (n-1)`.  Head steps preserve `BotAt n` (the window's items stay items, `y z` keeps the
items of `y`, and a fold-`36` head makes the whole term fold `36`).  At the head normal form, which
has fold `≠ 36`, the witness is inside an item, one level down.  Hence `¬ Pk (n+1) t`.
-/

namespace HnfB0
open HnfS HnfSound HnfProd

/-- `t` has a subterm without a head normal form at spine-nesting depth at most `n`. -/
inductive BotAt : Nat → Term → Prop
  | here {n : Nat} {t : Term} (h : fold t = 36) : BotAt n t
  | item {n : Nat} {t u : Term} (hu : u ∈ spine t) (h : BotAt n u) : BotAt (n + 1) t

/-- One more level of depth is always allowed (no `omega`: it would pull in choice). -/
theorem BotAt.succ {n : Nat} {t : Term} (h : BotAt n t) : BotAt (n + 1) t := by
  induction h with
  | here h => exact .here h
  | item hu _ ih => exact .item hu ih

/-- A fold-`36` head absorbs any pure arguments. -/
theorem foldl_bot {h : Term} (w : List Term) (hw : ∀ u ∈ w, PureS u) (hb : fold h = 36) :
    fold (w.foldl Term.app h) = 36 := by
  induction w generalizing h with
  | nil => exact hb
  | cons x w ih =>
    simp only [List.foldl]
    apply ih (fun u hu => hw u (by simp [hu]))
    simp only [fold, hb]
    exact absorb (fold_lt (hw x (by simp)))

/-- `BotAt` passes from the function to an application. -/
theorem app_left {m : Nat} {f x : Term} (hx : PureS x) (h : BotAt m f) : BotAt m (f ⬝ x) := by
  cases h with
  | here hb =>
    refine .here ?_
    simp only [fold, hb]
    exact absorb (fold_lt hx)
  | item hu h' => exact .item (by simp [spine, hu]) h'

/-- One head step preserves `BotAt n`. -/
theorem step {n : Nat} {t u₁ u₂ u₃ : Term} {rest : List Term} (ht : PureS t)
    (hs : spine t = u₁ :: u₂ :: u₃ :: rest) (h : BotAt n t) :
    BotAt n (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := by
  have hp := spine_pure ht
  rw [hs] at hp
  have p₁ := hp u₁ (by simp); have p₂ := hp u₂ (by simp); have p₃ := hp u₃ (by simp)
  have hrest : ∀ u ∈ rest, PureS u := fun u hu => hp u (by simp [hu])
  have hsp : spine (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) =
      spine u₁ ++ u₃ :: (u₂ ⬝ u₃) :: rest := by
    rw [spine_foldl]; simp [spine]
  have hS : t = rest.foldl Term.app (S ⬝ u₁ ⬝ u₂ ⬝ u₃) := by
    have h0 := pure_eq_foldl ht
    rw [hs] at h0
    simpa only [List.foldl] using h0
  have hw : WStep t (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := by
    rw [hS]; exact wstep_foldl (.S u₁ u₂ u₃) rest
  have hfold := (HnfS.wstep_pure hw ht).2
  cases h with
  | here hb => exact .here (by rw [hfold]; exact hb)
  | @item m _ v hv hb =>
    rw [hs] at hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | rfl | rfl | hv
    · -- the head item u₁
      cases hb with
      | here hb1 =>
        refine .here (foldl_bot rest hrest ?_)
        simp only [fold, hb1]
        rw [absorb (fold_lt p₃)]
        exact absorb (fold_lt (PureS.app p₂ p₃))
      | item hw' hb' =>
        exact (BotAt.item (by rw [hsp]; simp [hw']) hb').succ
    · -- the y-seat: u₂ u₃ keeps the witness
      exact .item (by rw [hsp]; simp) (app_left p₃ hb)
    · -- the z-seat: u₃ stays an item
      exact .item (by rw [hsp]; simp) hb
    · -- an item of the rest
      exact .item (by rw [hsp]; simp [hv]) hb

/-- Head reduction preserves `BotAt n`. -/
theorem chain {n : Nat} {t u : Term} (hc : HeadChain t u) (ht : PureS t) (h : BotAt n t) :
    BotAt n u := by
  induction hc with
  | refl => exact h
  | @step t' v u₁ u₂ u₃ rest hs hS _ ih =>
    have hw : WStep t' (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := by
      rw [hS]; exact wstep_foldl (.S u₁ u₂ u₃) rest
    exact ih (HnfS.wstep_pure hw ht).1 (step ht hs h)

/-- A witness within depth `n` stops the Böhm tree by depth `n + 1`. -/
theorem not_Pk : ∀ (n : Nat) {t : Term}, PureS t → BotAt n t → ¬ Pk (n + 1) t := by
  intro n
  induction n with
  | zero =>
    intro t ht h ⟨u, hc, hl, _⟩
    have hu := (HnfS.fold_wsteps (headChain_wsteps hc ht) ht).1
    cases chain hc ht h with
    | here hb => exact fold_hnf hu (isHnf_of_short hu hl) hb
  | succ n ih =>
    intro t ht h ⟨u, hc, hl, hall⟩
    have hu := (HnfS.fold_wsteps (headChain_wsteps hc ht) ht).1
    cases chain hc ht h with
    | here hb => exact fold_hnf hu (isHnf_of_short hu hl) hb
    | item hw hb => exact ih (spine_pure hu _ hw) hb (hall _ hw)

/-- `s` is a subterm of `t`. -/
inductive Sub : Term → Term → Prop
  | refl (t : Term) : Sub t t
  | left {s f : Term} (x : Term) (h : Sub s f) : Sub s (f ⬝ x)
  | right {s x : Term} (f : Term) (h : Sub s x) : Sub s (f ⬝ x)

theorem botAt_of_sub {s t : Term} (h : Sub s t) (ht : PureS t) (hs : fold s = 36) :
    ∃ n, BotAt n t := by
  induction h with
  | refl => exact ⟨0, .here hs⟩
  | left x _ ih =>
    obtain ⟨n, hn⟩ := ih ht.app_inv.1
    exact ⟨n, app_left ht.app_inv.2 hn⟩
  | right f _ ih =>
    obtain ⟨n, hn⟩ := ih ht.app_inv.2
    exact ⟨n + 1, .item (by simp [spine]) hn⟩

/-- **Lemma B0.**  A closed pure-S term with a subterm that has no head normal form
(fold `36`, equivalently no reduct in head normal form: `HnfS.no_hnf_of_bot`, `HnfSound.sound`)
is not productive: its Böhm tree is undefined at some finite depth. -/
theorem B0 {s t : Term} (ht : PureS t) (h : Sub s t) (hs : fold s = 36) : ∃ k, ¬ Pk k t := by
  obtain ⟨n, hn⟩ := botAt_of_sub h ht hs
  exact ⟨n + 1, not_Pk n ht hn⟩

end HnfB0
