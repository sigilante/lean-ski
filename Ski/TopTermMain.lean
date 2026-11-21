import Ski.TopTermQ
open Term

/-!
# Top-termination of pure S

Waldmann's §7.3 in a short form, then the theorem.

* `last2_step`, `inv_steps` (7.3.1): along head reduction from `S B C D`, the last two arguments
  `F, G` keep `D ⊴ F` and `C D ⊴ G`.
* `seg` (7.3.2): if `X Z ↠ S F G` by head reduction, then either the reduction is empty
  (`X = S F`, `Z = G`), or `Z ⊴ F` and `c Z ⊴ G` for some `c`.
* `root_next`: from a root redex `S X Y Z`, the next root redex is `S X' Y' (Y Z)`, related as
  in `seg`; if there is none, the head path makes no further root step.
* Levels, by structural induction on `X`: any root redex (`reach_L1`), one with `Y ≠ S`
  (`reach_L2`), one with `Z ∈ Q` (`reach_L3`); the next root redex after that has all three parts in
  `Q`, and `reach_qqq` (Waldmann 7.5.10) finishes.
* `reach_all`: every closed S-term makes boundedly many root steps on its head path;
  `top_termination`: no reduction sequence of closed S-terms is perpetual.
-/

namespace TopTerm
open HnfS HnfSound HnfB0

theorem qt_sub {s t : Term} (h : Sub s t) (ht : PureS t) (hs : Qt s) : Qt t := by
  induction h with
  | refl => exact hs
  | left x _ ih => exact qt_app_left ht.app_inv.1 ht.app_inv.2 (ih ht.app_inv.1)
  | right f _ ih => exact qt_app_right ht.app_inv.1 ht.app_inv.2 (ih ht.app_inv.2)

theorem ne_S_of_sub_app {c Z Y : Term} (h : Sub (c ⬝ Z) Y) : Y ≠ S := by
  rintro rfl; cases h

/-- One head step from a term with two or more arguments: the last two arguments either rotate
(`S ★ F G → ★ G (F G)`) or the second-to-last grows and the last stays. -/
theorem last2_step {u F G w : Term} (hp : PureS (u ⬝ F ⬝ G)) (s : Step (u ⬝ F ⬝ G) w) :
    ∃ u' F' G', w = u' ⬝ F' ⬝ G' ∧ ((F' = G ∧ G' = F ⬝ G) ∨ (Sub F F' ∧ G' = G)) := by
  have hu := hp.app_inv.1.app_inv.1
  cases s with
  | S => exact ⟨_, _, _, rfl, .inl ⟨rfl, rfl⟩⟩
  | K => cases hu
  | left _ s =>
    cases s with
    | S f g => exact ⟨_, _, G, rfl, .inr ⟨.right g (.refl F), rfl⟩⟩
    | K => cases hu with | app h _ => cases h
    | I => cases hu
    | left _ s' => exact ⟨_, F, G, rfl, .inr ⟨.refl F, rfl⟩⟩

/-- 7.3.1: the invariant `D ⊴ F ∧ C D ⊴ G` on the last two arguments. -/
theorem inv_steps {D CD : Term} (hD : Sub D CD) : ∀ {t w : Term}, Steps t w →
    ∀ {u F G : Term}, t = u ⬝ F ⬝ G → PureS t → Sub D F → Sub CD G →
    ∃ u' F' G', w = u' ⬝ F' ⬝ G' ∧ Sub D F' ∧ Sub CD G' := by
  intro t w h
  induction h with
  | refl => intro u F G e _ h1 h2; exact ⟨u, F, G, e, h1, h2⟩
  | step s _ ih =>
    intro u F G e hp h1 h2
    subst e
    obtain ⟨u', F', G', rfl, hr⟩ := last2_step hp s
    have hp' := (HnfS.wstep_pure s.weak hp).1
    rcases hr with ⟨rfl, rfl⟩ | ⟨hF, rfl⟩
    · exact ih rfl hp' (hD.trans h2) (.right F h2)
    · exact ih rfl hp' (h1.trans hF) h2

/-- 7.3.2, as used here. -/
theorem seg {Z F G : Term} : ∀ {t w : Term}, Steps t w → ∀ {X : Term}, t = X ⬝ Z → PureS t →
    w = S ⬝ F ⬝ G → (X = S ⬝ F ∧ Z = G) ∨ (Sub Z F ∧ ∃ c, Sub (c ⬝ Z) G) := by
  intro t w h
  induction h with
  | refl =>
    intro X e _ ew
    subst e
    injection ew with e1 e2
    exact .inl ⟨e1, e2⟩
  | @step t t' w s rest ih =>
    intro X e hp ew
    subst e
    have hX := hp.app_inv.1
    cases s with
    | S f g x =>
      -- X Z = S f g Z → f Z (g Z): the invariant from here on
      obtain ⟨u', F', G', e', h1, h2⟩ :=
        inv_steps (.right g (.refl Z)) rest rfl (HnfS.wstep_pure (Step.S f g Z).weak hp).1
          (.refl Z) (.refl (g ⬝ Z))
      rw [ew] at e'
      injection e' with e1 e3
      injection e1 with _ e4
      subst e4 e3
      exact .inr ⟨h1, g, h2⟩
    | K => cases hX with | app h _ => cases h
    | I => cases hX
    | left _ s' =>
      rcases ih rfl (HnfS.wstep_pure (Step.left Z s').weak hp).1 ew with ⟨rfl, rfl⟩ | h
      · obtain ⟨a, b, c, e⟩ := step_two hX s'
        cases e
      · exact .inr h

theorem isHnf_S1 (a : Term) : IsHnf (S ⬝ a) := .inr (.inl ⟨a, rfl⟩)

/-- From a root redex `S X Y Z`: either no further root step, or the next root redex
`S X' Y' (Y Z)`, trivially (`X = S X'`, `Y' = Z`) or with `Z ⊴ X'` and `c Z ⊴ Y'`. -/
theorem root_next {X Y Z : Term} (hX : PureS X) (hY : PureS Y) (hZ : PureS Z)
    (triv : ∀ {X'}, X = S ⬝ X' → Reach (S ⬝ X' ⬝ Z ⬝ (Y ⬝ Z)))
    (nontriv : ∀ {X' Y'}, PureS X' → PureS Y' → Sub Z X' → (∃ c, Sub (c ⬝ Z) Y') →
      Reach (S ⬝ X' ⬝ Y' ⬝ (Y ⬝ Z))) :
    Reach (S ⬝ X ⬝ Y ⬝ Z) := by
  refine reach_of_step (.S X Y Z) ?_
  have hXZ : PureS (X ⬝ Z) := .app hX hZ
  if hb : fold (X ⬝ Z) = 36 then exact reach_of_bot_fun hXZ hb
  else
    obtain ⟨Kh, hs, hK, hKp, _⟩ := hnf_of hXZ hb
    refine reach_of_steps (Steps.left (Y ⬝ Z) hs) ?_
    rcases hK with rfl | ⟨h, rfl⟩ | ⟨X', Y', rfl⟩
    · exact reach_of_hnf (isHnf_S1 _)
    · exact reach_of_hnf (.inr (.inr ⟨h, Y ⬝ Z, rfl⟩))
    · rcases seg hs rfl hXZ rfl with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
      · exact triv rfl
      · exact nontriv hKp.app_inv.1.app_inv.2 hKp.app_inv.2 h1 h2

/-- Level 4: all three parts in `Q`. -/
theorem reach_L4 {X Y Z : Term} (hX : PureS X) (hY : PureS Y) (hZ : PureS Z)
    (qx : Qt X) (qy : Qt Y) (qz : Qt Z) : Reach (S ⬝ X ⬝ Y ⬝ Z) :=
  reach_of_step (.S X Y Z) (reach_qqq hX qx hZ (.app hY hZ) qz (qt_app_left hY hZ qy))

/-- Level 3: `Z ∈ Q`. -/
theorem reach_L3 : ∀ {X : Term}, PureS X → ∀ {Y Z : Term}, PureS Y → PureS Z → Qt Z →
    Reach (S ⬝ X ⬝ Y ⬝ Z) := by
  intro X hX
  induction hX with
  | S =>
    intro Y Z hY hZ qz
    exact root_next .S hY hZ (fun e => by cases e)
      (fun hX' hY' h1 ⟨c, h2⟩ => reach_L4 hX' hY' (.app hY hZ) (qt_sub h1 hX' qz)
        (qt_sub (Sub.trans (.right c (.refl Z)) h2) hY' qz) (qt_app_right hY hZ qz))
  | @app f x hf hx _ ihx =>
    intro Y Z hY hZ qz
    refine root_next (.app hf hx) hY hZ ?_ ?_
    · intro X' e
      injection e with ef ex
      subst ef ex
      exact ihx hZ (.app hY hZ) (qt_app_right hY hZ qz)
    · intro X' Y' hX' hY' h1 ⟨c, h2⟩
      exact reach_L4 hX' hY' (.app hY hZ) (qt_sub h1 hX' qz)
        (qt_sub (Sub.trans (.right c (.refl Z)) h2) hY' qz) (qt_app_right hY hZ qz)

/-- Level 2: `Y ≠ S`. -/
theorem reach_L2 : ∀ {X : Term}, PureS X → ∀ {Y Z : Term}, PureS Y → PureS Z → Y ≠ S →
    Reach (S ⬝ X ⬝ Y ⬝ Z) := by
  intro X hX Y Z hY hZ ny
  have qyz : Qt (Y ⬝ Z) := qt_app_ne hY hZ ny
  refine root_next hX hY hZ ?_ ?_
  · intro X' e
    subst e
    exact reach_L3 hX.app_inv.2 hZ (.app hY hZ) qyz
  · intro X' Y' hX' hY' _ _
    exact reach_L3 hX' hY' (.app hY hZ) qyz

/-- Level 1: any root redex. -/
theorem reach_L1 : ∀ {X : Term}, PureS X → ∀ {Y Z : Term}, PureS Y → PureS Z →
    Reach (S ⬝ X ⬝ Y ⬝ Z) := by
  intro X hX
  induction hX with
  | S =>
    intro Y Z hY hZ
    exact root_next .S hY hZ (fun e => by cases e)
      (fun hX' hY' _ ⟨_, h2⟩ => reach_L2 hX' hY' (.app hY hZ) (ne_S_of_sub_app h2))
  | @app f x hf hx _ ihx =>
    intro Y Z hY hZ
    refine root_next (.app hf hx) hY hZ ?_ ?_
    · intro X' e
      injection e with ef ex
      subst ef ex
      exact ihx hZ (.app hY hZ)
    · intro X' Y' hX' hY' _ ⟨_, h2⟩
      exact reach_L2 hX' hY' (.app hY hZ) (ne_S_of_sub_app h2)

/-- The head path of every closed S-term does not make arbitrarily many root steps. -/
theorem reach_all {t : Term} (ht : PureS t) : Reach t := by
  cases ht with
  | S => exact reach_of_hnf (.inl rfl)
  | @app f w hf hw =>
    if hb : fold f = 36 then exact reach_of_bot_fun hf hb
    else
      obtain ⟨Kh, hs, hK, hKp, _⟩ := hnf_of hf hb
      refine reach_of_steps (Steps.left w hs) ?_
      rcases hK with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
      · exact reach_of_hnf (isHnf_S1 w)
      · exact reach_of_hnf (.inr (.inr ⟨a, w, rfl⟩))
      · exact reach_L1 hKp.app_inv.1.app_inv.2 hKp.app_inv.2 hw

/-- **Top-termination of CL(S)** (Waldmann, 1998, thesis ch. 7).  No reduction sequence of
closed S-terms rewrites the root at unboundedly late positions. -/
theorem top_termination {σ : Nat → Term} (h0 : PureS (σ 0)) : ¬ Perpetual σ :=
  not_perpetual (fin_of_reach (reach_all h0))

end TopTerm
