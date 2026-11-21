import Ski.TopTermMain
open Term

/-!
# The infinitary normal form of a closed S-term, by its finite prefixes

`NF d t P`: `P` is the infinitary normal form `t^∞` cut at depth `d` (holes below).  The rules
are S2's Prop. 8: if head reduction reaches `f w` with a *stable* root (`f` has no head normal
form, or `f w` is one), then `t^∞ = f^∞ w^∞`; and `S^∞ = S`.

* `nf_exists` (from `TopTerm.reach_all`), `nf_unique`: every prefix exists and is unique;
* `nf_redexFree`: the prefixes contain no redex, so `t^∞` is a normal form;
* `nf_approx`: `t` reduces to a finite term with the same depth-`d` prefix;
* `nf_coherent`: each prefix is the next one truncated, so the prefixes form one tree;
* `nf_wsteps`, `nf_wsteps_back`: reduction does not change the prefixes (`t ↠ u` gives
  `u^∞ = t^∞`), because a stable root stays stable under every weak reduction (`stable_wsteps`);
* `nf_finite_iff`: `t^∞` is finite iff `t` normalizes;
* `leftInf_iff`: the root of `t^∞` has an infinite left spine iff `t` has no head normal form;
* `prod_iff_nodes`: `t` is productive iff no node of `t^∞` has an infinite left spine.

That every strongly convergent reduction of `t` to a normal form ends in `t^∞` (unique normal
forms for orthogonal systems) is not proved here; S2 cites it.
-/

namespace InfNF
open HnfS HnfSound HnfB0 HnfProd TopTerm

/-- Finite prefixes of possibly infinite S-trees. -/
inductive PT
  | S
  | hole
  | app (l r : PT)
  deriving DecidableEq

/-- The depth-`d` cut of a finite term. -/
def cut : Nat → Term → PT
  | 0, _ => .hole
  | _ + 1, .S => .S
  | d + 1, .app l r => .app (cut d l) (cut d r)
  | _ + 1, _ => .hole

/-- A root `f w` that no later head step changes. -/
def Stable (f w : Term) : Prop := fold f = 36 ∨ IsHnf (f ⬝ w)

inductive NF : Nat → Term → PT → Prop
  | zero (t : Term) : NF 0 t .hole
  | leaf (d : Nat) : NF (d + 1) S .S
  | node {d : Nat} {t f w : Term} {Pf Pw : PT} : Steps t (f ⬝ w) → Stable f w →
      NF d f Pf → NF d w Pw → NF (d + 1) t (.app Pf Pw)

/-! ## Head paths -/

theorem steps_pure {t u : Term} (ht : PureS t) (h : Steps t u) : PureS u := by
  induction h with
  | refl => exact ht
  | step s _ ih => exact ih (HnfS.wstep_pure s.weak ht).1

theorem steps_fold {t u : Term} (ht : PureS t) (h : Steps t u) : fold u = fold t := by
  have := HnfS.fold_wsteps (Steps.weak h) ht
  exact this.2

theorem steps_cmp {t u v : Term} (hu : Steps t u) (hv : Steps t v) : Steps u v ∨ Steps v u := by
  induction hu generalizing v with
  | refl => exact .inl hv
  | step s _ ih =>
    cases hv with
    | refl => exact .inr (.step s ‹_›)
    | step s' rest => rw [Step.det s s'] at ih; exact ih rest

theorem steps_from_S {u : Term} (h : Steps S u) : u = S := by
  cases h with
  | refl => rfl
  | step s _ => cases s

theorem steps_from_hnf {u v : Term} (hu : IsHnf u) (h : Steps u v) : v = u := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (fun s => no_step_hnf hu s)

/-- Head steps from `f w` with `f` hnf-less stay inside `f`. -/
theorem steps_bot_fun {f w v : Term} (hf : PureS f) (hb : fold f = 36) (h : Steps (f ⬝ w) v) :
    ∃ g, v = g ⬝ w ∧ Steps f g ∧ PureS g ∧ fold g = 36 := by
  generalize ht : f ⬝ w = t at h
  induction h generalizing f with
  | refl => subst ht; exact ⟨f, rfl, .refl _, hf, hb⟩
  | step s _ ih =>
    subst ht
    cases s with
    | S a b c => exact absurd hb (fold_hnf hf (.inr (.inr ⟨a, b, rfl⟩)))
    | K => cases hf with | app h _ => cases h
    | I => cases hf
    | left _ s =>
      have hw := HnfS.wstep_pure s.weak hf
      obtain ⟨g, rfl, hs, hg, hgb⟩ := ih hw.1 (hw.2 ▸ hb) rfl
      exact ⟨g, rfl, .step s hs, hg, hgb⟩

theorem stable_pure_bot {f w : Term} (hf : PureS f) (hw : PureS w) (st : Stable f w)
    (hb : fold (f ⬝ w) = 36) : fold f = 36 := by
  rcases st with h | h
  · exact h
  · exact absurd hb (fold_hnf (.app hf hw) h)

/-! ## Existence and uniqueness -/

theorem nf_bwd : ∀ {d : Nat} {t u : Term} {P : PT}, PureS t → Steps t u → NF d u P → NF d t P := by
  intro d t u P ht hs hn
  cases hn with
  | zero => exact .zero t
  | leaf d =>
    rcases steps_two ht hs with rfl | ⟨a, b, c, e⟩
    · exact .leaf d
    · cases e
  | node h st hf hw => exact .node (hs.trans h) st hf hw

theorem nf_exists : ∀ (d : Nat) {t : Term}, PureS t → ∃ P, NF d t P := by
  intro d
  induction d with
  | zero => intro t _; exact ⟨_, .zero t⟩
  | succ d ih =>
    intro t ht
    have hr := reach_all ht
    induction hr with
    | @hnf u hu =>
      rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
      · exact ⟨_, .leaf d⟩
      · obtain ⟨Pf, hf⟩ := ih (t := S) .S
        obtain ⟨Pw, hw⟩ := ih ht.app_inv.2
        exact ⟨_, .node (.refl _) (.inr (.inr (.inl ⟨a, rfl⟩))) hf hw⟩
      · obtain ⟨Pf, hf⟩ := ih ht.app_inv.1
        obtain ⟨Pw, hw⟩ := ih ht.app_inv.2
        exact ⟨_, .node (.refl _) (.inr (.inr (.inr ⟨a, b, rfl⟩))) hf hw⟩
    | @bot f w hf hb =>
      obtain ⟨Pf, h1⟩ := ih hf
      obtain ⟨Pw, h2⟩ := ih ht.app_inv.2
      exact ⟨_, .node (.refl _) (.inl hb) h1 h2⟩
    | @step t t' s _ ih' =>
      obtain ⟨P, hP⟩ := ih' (HnfS.wstep_pure s.weak ht).1
      exact ⟨P, nf_bwd ht (.single s) hP⟩

theorem nf_unique : ∀ {d : Nat} {t : Term} {P P' : PT}, PureS t → NF d t P → NF d t P' → P = P' := by
  intro d
  induction d with
  | zero => intro t P P' _ h h'; cases h; cases h'; rfl
  | succ d ih =>
    intro t P P' ht h h'
    cases h with
    | leaf =>
      cases h' with
      | leaf => rfl
      | node hs _ _ _ => have := steps_from_S hs; cases this
    | @node _ _ f w Pf Pw hs st hf hw =>
      cases h' with
      | leaf => have := steps_from_S hs; cases this
      | @node _ _ f' w' Pf' Pw' hs' st' hf' hw' =>
        have hfw := steps_pure ht hs
        have hfw' := steps_pure ht hs'
        -- the later of the two stable roots is reached from the earlier one inside `f`
        have key : ∀ {f w f' w' : Term} {Pf Pw Pf' Pw' : PT}, PureS (f ⬝ w) → Stable f w →
            Steps (f ⬝ w) (f' ⬝ w') → NF d f Pf → NF d w Pw → NF d f' Pf' → NF d w' Pw' →
            PT.app Pf Pw = PT.app Pf' Pw' := by
          intro f w f' w' Pf Pw Pf' Pw' hp st hs hf hw hf' hw'
          rcases st with hb | hh
          · obtain ⟨g, e, hg, _, _⟩ := steps_bot_fun hp.app_inv.1 hb hs
            injection e with e1 e2
            subst e1 e2
            rw [ih hp.app_inv.1 hf (nf_bwd hp.app_inv.1 hg hf'), ih hp.app_inv.2 hw hw']
          · have e := steps_from_hnf hh hs
            injection e with e1 e2
            subst e1 e2
            rw [ih hp.app_inv.1 hf hf', ih hp.app_inv.2 hw hw']
        rcases steps_cmp hs hs' with h1 | h1
        · exact key hfw st h1 hf hw hf' hw'
        · exact (key hfw' st' h1 hf' hw' hf hw).symm

/-! ## The prefixes are normal and approximated by reducts -/

/-- Is the prefix `S x y` at its root? -/
def PT.isS2 : PT → Bool
  | .app l _ => match l with
    | .app .S _ => true
    | _ => false
  | _ => false

/-- No redex pattern `S x y z` inside the prefix. -/
def PT.redexFree : PT → Bool
  | .app l r => !l.isS2 && l.redexFree && r.redexFree
  | _ => true

theorem PT.isS2_true : ∀ {P : PT}, P.isS2 = true → ∃ X Y, P = .app (.app .S X) Y
  | .app (.app .S X) Y, _ => ⟨X, Y, rfl⟩
  | .S, h => by simp [PT.isS2] at h
  | .hole, h => by simp [PT.isS2] at h
  | .app .S _, h => by simp [PT.isS2] at h
  | .app .hole _, h => by simp [PT.isS2] at h
  | .app (.app .hole _) _, h => by simp [PT.isS2] at h
  | .app (.app (.app _ _) _) _, h => by simp [PT.isS2] at h

/-- If the prefix of `f^∞` shows `S x y` at its root, `f` head-reduces to `S x y`. -/
theorem nf_shape {d : Nat} {f : Term} {X Y : PT}
    (h : NF d f (.app (.app .S X) Y)) : ∃ x y, Steps f (S ⬝ x ⬝ y) := by
  cases h with
  | @node _ _ g y _ _ hs _ hg _ =>
    cases hg with
    | @node _ _ s x _ _ hs2 _ hS _ =>
      cases hS with
      | leaf => exact ⟨x, y, hs.trans (Steps.left y hs2)⟩

/-- The root of a stable `f w` is not a redex of the prefix. -/
theorem root_not_redex {d : Nat} {f w : Term} {Pf : PT} (hf : PureS f) (st : Stable f w)
    (h : NF d f Pf) : Pf.isS2 = false := by
  cases hs2 : Pf.isS2 with
  | false => rfl
  | true =>
    obtain ⟨X, Y, rfl⟩ := PT.isS2_true hs2
    obtain ⟨x, y, hxy⟩ := nf_shape h
    rcases st with hb | hh
    · have := steps_fold hf hxy
      rw [hb] at this
      exact absurd this (fold_hnf (steps_pure hf hxy) (.inr (.inr ⟨x, y, rfl⟩)))
    · -- `f w` is an hnf, so `f` is `S` or `S a`, and neither head-reduces to `S x y`
      rcases hh with e | ⟨a, e⟩ | ⟨a, b, e⟩
      · cases e
      · injection e with e1 _
        subst e1
        have := steps_from_S hxy
        cases this
      · injection e with e1 _
        subst e1
        have := steps_from_hnf (.inr (.inl ⟨a, rfl⟩)) hxy
        injection this with e3 _
        cases e3

theorem nf_redexFree : ∀ {d : Nat} {t : Term} {P : PT}, PureS t → NF d t P → P.redexFree = true := by
  intro d
  induction d with
  | zero => intro t P _ h; cases h; rfl
  | succ d ih =>
    intro t P ht h
    cases h with
    | leaf => rfl
    | @node _ _ f w Pf Pw hs st hf hw =>
      have hp := steps_pure ht hs
      simp only [PT.redexFree, root_not_redex hp.app_inv.1 st hf, ih hp.app_inv.1 hf,
        ih hp.app_inv.2 hw, Bool.not_false, Bool.true_and]

theorem nf_approx : ∀ {d : Nat} {t : Term} {P : PT}, NF d t P → ∃ u, WSteps t u ∧ cut d u = P := by
  intro d
  induction d with
  | zero => intro t P h; cases h; exact ⟨t, .refl t, rfl⟩
  | succ d ih =>
    intro t P h
    cases h with
    | leaf => exact ⟨S, .refl _, rfl⟩
    | node hs _ hf hw =>
      obtain ⟨u1, h1, c1⟩ := ih hf
      obtain ⟨u2, h2, c2⟩ := ih hw
      exact ⟨u1 ⬝ u2, hs.weak.trans (WSteps.app h1 h2), by simp [cut, c1, c2]⟩


/-! ## The prefixes form one tree, invariant under reduction -/

def PT.trunc : Nat → PT → PT
  | 0, _ => .hole
  | _ + 1, .S => .S
  | _ + 1, .hole => .hole
  | d + 1, .app l r => .app (PT.trunc d l) (PT.trunc d r)

/-- **Coherence.**  The depth-`d` prefix is the depth-`(d+1)` prefix truncated. -/
theorem nf_coherent : ∀ {d : Nat} {t : Term} {P : PT}, NF (d + 1) t P → NF d t (P.trunc d) := by
  intro d
  induction d with
  | zero => intro t P _; exact .zero t
  | succ d ih =>
    intro t P h
    cases h with
    | leaf => exact .leaf d
    | node hs st hf hw => exact .node hs st (ih hf) (ih hw)

theorem wstep_from_S {u : Term} (h : WStep S u) : False := by cases h

theorem wsteps_from_S {u : Term} (h : WSteps S u) : u = S := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (fun s => wstep_from_S s)

theorem wstep_app_result {t u : Term} (ht : PureS t) (h : WStep t u) : ∃ a b, u = a ⬝ b := by
  cases h with
  | S f g x => exact ⟨_, _, rfl⟩
  | K => cases ht with | app h _ => cases h with | app h _ => cases h
  | I => cases ht with | app h _ => cases h
  | left x _ => exact ⟨_, _, rfl⟩
  | right f _ => exact ⟨_, _, rfl⟩

theorem wsteps_app {a b v : Term} (hp : PureS (a ⬝ b)) (h : WSteps (a ⬝ b) v) : ∃ c d, v = c ⬝ d := by
  generalize ht : a ⬝ b = t at h
  induction h generalizing a b with
  | refl => exact ⟨a, b, ht.symm⟩
  | step s _ ih =>
    subst ht
    obtain ⟨c, d, rfl⟩ := wstep_app_result hp s
    exact ih (HnfS.wstep_pure s hp).1 rfl

theorem wsteps_to_S {t : Term} (ht : PureS t) (h : WSteps t S) : t = S := by
  cases ht with
  | S => rfl
  | app hf hx =>
    obtain ⟨c, d, e⟩ := wsteps_app (.app hf hx) h
    cases e

/-- One weak step from a stable root keeps it stable, and steps only inside its two parts. -/
theorem stable_wstep {f w v : Term} (hp : PureS (f ⬝ w)) (st : Stable f w) (h : WStep (f ⬝ w) v) :
    ∃ f' w', v = f' ⬝ w' ∧ WSteps f f' ∧ WSteps w w' ∧ Stable f' w' := by
  have hf := hp.app_inv.1
  cases h with
  | S a b c =>
    rcases st with hb | hh
    · exact absurd hb (fold_hnf hf (.inr (.inr ⟨a, b, rfl⟩)))
    · rcases hh with e | ⟨_, e⟩ | ⟨_, _, e⟩ <;> cases e
  | K => cases hf with | app h _ => cases h
  | I => cases hf
  | @left _ f' _ s =>
    refine ⟨f', w, rfl, .single s, .refl _, ?_⟩
    rcases st with hb | hh
    · exact .inl ((HnfS.wstep_pure s hf).2 ▸ hb)
    · rcases hh with e | ⟨x, e⟩ | ⟨x, y, e⟩
      · cases e
      · injection e with e1 _; subst e1; cases s
      · injection e with e1 _; subst e1
        cases s with
        | left _ s' => cases s'
        | right _ s' => exact .inr (.inr (.inr ⟨_, w, rfl⟩))
  | @right _ _ w' s =>
    refine ⟨f, w', rfl, .refl _, .single s, ?_⟩
    rcases st with hb | hh
    · exact .inl hb
    · rcases hh with e | ⟨x, e⟩ | ⟨x, y, e⟩
      · cases e
      · injection e with e1 _; subst e1; exact .inr (.inr (.inl ⟨w', rfl⟩))
      · injection e with e1 _; subst e1; exact .inr (.inr (.inr ⟨x, w', rfl⟩))

theorem stable_wsteps {f w v : Term} (hp : PureS (f ⬝ w)) (st : Stable f w) (h : WSteps (f ⬝ w) v) :
    ∃ f' w', v = f' ⬝ w' ∧ WSteps f f' ∧ WSteps w w' ∧ Stable f' w' := by
  generalize ht : f ⬝ w = t at h
  induction h generalizing f w with
  | refl => subst ht; exact ⟨f, w, rfl, .refl _, .refl _, st⟩
  | step s _ ih =>
    subst ht
    obtain ⟨f1, w1, rfl, h1, h2, st1⟩ := stable_wstep hp st s
    have hp1 := (HnfS.wstep_pure s hp).1
    obtain ⟨f', w', rfl, h3, h4, st'⟩ := ih hp1 st1 rfl
    exact ⟨f', w', rfl, h1.trans h3, h2.trans h4, st'⟩

/-- **Invariance.**  A reduct has the same prefixes: `t ↠ u` implies `u^∞ = t^∞`. -/
theorem nf_wsteps : ∀ {d : Nat} {t u : Term} {P : PT}, PureS t → NF d t P → WSteps t u → NF d u P := by
  intro d
  induction d with
  | zero => intro t u P _ h _; cases h; exact .zero u
  | succ d ih =>
    intro t u P ht h hu
    have hup := (HnfS.fold_wsteps hu ht).1
    cases h with
    | leaf => rw [wsteps_from_S hu]; exact .leaf d
    | @node _ _ f w Pf Pw hs st hf hw =>
      obtain ⟨Q, hQ⟩ := nf_exists (d + 1) hup
      cases hQ with
      | leaf =>
        have := wsteps_to_S ht hu
        subst this
        have := steps_from_S hs
        cases this
      | @node _ _ g x Qg Qx hs' st' hg hx =>
        have hfw := steps_pure ht hs
        have hgx := steps_pure hup hs'
        obtain ⟨v, h1, h2⟩ := church_rosser hs.weak (hu.trans hs'.weak)
        obtain ⟨f', w', rfl, hff, hww, _⟩ := stable_wsteps hfw st h1
        obtain ⟨g', x', e, hgg, hxx, _⟩ := stable_wsteps hgx st' h2
        injection e with e1 e2
        subst e1 e2
        have a1 := ih hfw.app_inv.1 hf hff
        have a2 := ih hgx.app_inv.1 hg hgg
        have a3 := ih hfw.app_inv.2 hw hww
        have a4 := ih hgx.app_inv.2 hx hxx
        have p1 := (HnfS.fold_wsteps hff hfw.app_inv.1).1
        have p2 := (HnfS.fold_wsteps hww hfw.app_inv.2).1
        rw [nf_unique p1 a1 a2, nf_unique p2 a3 a4]
        exact .node hs' st' hg hx

/-- Invariance backward: a term has the prefixes of its reducts. -/
theorem nf_wsteps_back {d : Nat} {t u : Term} {P : PT} (ht : PureS t) (hu : WSteps t u)
    (h : NF d u P) : NF d t P := by
  obtain ⟨Q, hQ⟩ := nf_exists d ht
  have := nf_wsteps ht hQ hu
  rw [nf_unique (HnfS.fold_wsteps hu ht).1 h this]
  exact hQ

/-! ## Finite normal forms -/

def Normal (t : Term) : Prop := ∀ u, ¬ WStep t u

def PT.full : PT → Bool
  | .S => true
  | .hole => false
  | .app l r => l.full && r.full

def height : Term → Nat
  | .app l r => max (height l) (height r) + 1
  | _ => 1

theorem normal_left {a b : Term} (h : Normal (a ⬝ b)) : Normal a := fun u s => h _ (.left b s)
theorem normal_right {a b : Term} (h : Normal (a ⬝ b)) : Normal b := fun u s => h _ (.right a s)

theorem normal_fold : ∀ {n : Term}, PureS n → Normal n → fold n ≠ 36 := by
  intro n hn
  induction hn with
  | S => intro _; decide
  | @app a b ha hb iha _ =>
    intro hN hbot
    have r := reach_all (PureS.app ha hb)
    cases r with
    | hnf hu => exact fold_hnf (.app ha hb) hu hbot
    | bot _ hb' => exact iha (normal_left hN) hb'
    | step s _ => exact hN _ s.weak

theorem normal_hnf {n : Term} (hn : PureS n) (hN : Normal n) : IsHnf n := by
  obtain ⟨u, hc, _, hu⟩ := sound_head n hn (normal_fold hn hN)
  cases headChain_steps hc with
  | refl => exact hu
  | step s _ => exact absurd s.weak (hN _)

theorem nf_normal : ∀ (d : Nat) {n : Term}, PureS n → Normal n → NF d n (cut d n) := by
  intro d
  induction d with
  | zero => intro n _ _; exact .zero n
  | succ d ih =>
    intro n hn hN
    cases hn with
    | S => exact .leaf d
    | @app a b ha hb =>
      exact .node (.refl _) (.inr (normal_hnf (.app ha hb) hN)) (ih ha (normal_left hN))
        (ih hb (normal_right hN))

theorem cut_full : ∀ {n : Term}, PureS n → ∀ d, height n ≤ d → (cut d n).full = true := by
  intro n hn
  induction hn with
  | S => intro d hd; cases d with | zero => exact absurd hd (by decide) | succ d => rfl
  | @app a b _ _ iha ihb =>
    intro d hd
    cases d with
    | zero => exact absurd hd (Nat.not_succ_le_zero _)
    | succ d =>
      have hd' : max (height a) (height b) ≤ d := Nat.le_of_succ_le_succ hd
      have h1 := iha d (Nat.le_trans (Nat.le_max_left _ _) hd')
      have h2 := ihb d (Nat.le_trans (Nat.le_max_right _ _) hd')
      show ((cut d a).full && (cut d b).full) = true
      rw [h1, h2]; rfl

theorem normal_of_cut : ∀ {d : Nat} {u : Term}, PureS u → (cut d u).full = true →
    (cut d u).redexFree = true → Normal u := by
  intro d
  induction d with
  | zero => intro u _ h; simp [cut, PT.full] at h
  | succ d ih =>
    intro u hu hf hr
    cases hu with
    | S => exact fun v s => wstep_from_S s
    | @app a b ha hb =>
      simp only [cut, PT.full, Bool.and_eq_true] at hf
      simp only [cut, PT.redexFree, Bool.and_eq_true, Bool.not_eq_true'] at hr
      obtain ⟨⟨hs2, hra⟩, hrb⟩ := hr
      intro v s
      cases s with
      | S x y z =>
        -- `a = S x y`, whose full cut shows `S x y` at its root
        cases d with
        | zero => simp [cut, PT.full] at hf
        | succ d =>
          cases d with
          | zero => simp [cut, PT.full] at hf
          | succ d =>
            cases d with
            | zero => simp [cut, PT.full] at hf
            | succ d => simp [cut, PT.isS2] at hs2
      | K => cases ha with | app h _ => cases h
      | I => cases ha
      | left _ s => exact ih ha hf.1 hra _ s
      | right _ s => exact ih hb hf.2 hrb _ s

/-- **`t^∞` is finite iff `t` normalizes.** -/
theorem nf_finite_iff {t : Term} (ht : PureS t) :
    (∃ n, WSteps t n ∧ Normal n) ↔ ∃ d P, NF d t P ∧ P.full = true := by
  constructor
  · rintro ⟨n, hn, hN⟩
    have hnp := (HnfS.fold_wsteps hn ht).1
    exact ⟨height n, _, nf_wsteps_back ht hn (nf_normal _ hnp hN), cut_full hnp _ (Nat.le_refl _)⟩
  · rintro ⟨d, P, hP, hfull⟩
    obtain ⟨u, hu, hc⟩ := nf_approx hP
    have hup := (HnfS.fold_wsteps hu ht).1
    have hr := nf_redexFree hup (nf_wsteps ht hP hu)
    rw [← hc] at hfull hr
    exact ⟨u, hu, normal_of_cut hup hfull hr⟩

/-! ## Left spines -/

/-- Number of application nodes along the left path of a prefix. -/
def PT.leftLen : PT → Nat
  | .app l _ => l.leftLen + 1
  | _ => 0

/-- Along `t^∞`'s left spine from the root, every node is an application down to depth `d`. -/
def LeftInf (t : Term) : Prop := ∀ d P, NF d t P → P.leftLen = d

theorem leftInf_of_bot : ∀ {d : Nat} {t : Term} {P : PT}, PureS t → fold t = 36 → NF d t P →
    P.leftLen = d := by
  intro d
  induction d with
  | zero => intro t P _ _ h; cases h; rfl
  | succ d ih =>
    intro t P ht hb h
    cases h with
    | leaf => exact absurd hb (by decide)
    | node hs st hf _ =>
      have hp := steps_pure ht hs
      have hb' : fold _ = 36 := (steps_fold ht hs).trans hb
      have := stable_pure_bot hp.app_inv.1 hp.app_inv.2 st hb'
      simp only [PT.leftLen]
      rw [ih hp.app_inv.1 this hf]

/-- Depth-4 prefix of a term with a head normal form: its left spine ends at `S` within two
applications. -/
theorem left_short {t : Term} (ht : PureS t) (hb : fold t ≠ 36) :
    ∃ P, NF 4 t P ∧ P.leftLen ≤ 2 := by
  obtain ⟨u, hc, _, hu⟩ := sound_head t ht hb
  have hs := headChain_steps hc
  have hup := steps_pure ht hs
  rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · exact ⟨_, nf_bwd ht hs (.leaf 3), by decide⟩
  · obtain ⟨Pa, ha⟩ := nf_exists 3 hup.app_inv.2
    exact ⟨_, nf_bwd ht hs (.node (.refl _) (.inr (.inr (.inl ⟨a, rfl⟩))) (.leaf 2) ha), by
      simp [PT.leftLen]⟩
  · obtain ⟨Pa, ha⟩ := nf_exists 2 hup.app_inv.1.app_inv.2
    obtain ⟨Pb, hb'⟩ := nf_exists 3 hup.app_inv.2
    refine ⟨_, nf_bwd ht hs (.node (.refl _) (.inr (.inr (.inr ⟨a, b, rfl⟩)))
      (.node (.refl _) (.inr (.inr (.inl ⟨a, rfl⟩))) (.leaf 1) ha) hb'), ?_⟩
    simp [PT.leftLen]

/-- **The root of `t^∞` has an infinite left spine iff `t` has no head normal form.** -/
theorem leftInf_iff {t : Term} (ht : PureS t) : LeftInf t ↔ fold t = 36 := by
  constructor
  · intro h
    if hb : fold t = 36 then exact hb
    else
      obtain ⟨P, hP, hl⟩ := left_short ht hb
      have := h 4 P hP
      omega
  · intro hb d P hP; exact leftInf_of_bot ht hb hP

/-! ## Nodes of `t^∞` and productivity -/

/-- `u` represents a node of `t^∞`: `t` itself, or a node of `f^∞` or `w^∞` for a stable root
`f w` on `t`'s head path. -/
inductive Node : Term → Term → Prop
  | self (t : Term) : Node t t
  | fn {t f w u : Term} : Steps t (f ⬝ w) → Stable f w → Node f u → Node t u
  | arg {t f w u : Term} : Steps t (f ⬝ w) → Stable f w → Node w u → Node t u

theorem node_pure {t u : Term} (ht : PureS t) (h : Node t u) : PureS u := by
  induction h with
  | self => exact ht
  | fn hs _ _ ih => exact ih (steps_pure ht hs).app_inv.1
  | arg hs _ _ ih => exact ih (steps_pure ht hs).app_inv.2

theorem node_trans {t u v : Term} (h1 : Node t u) (h2 : Node u v) : Node t v := by
  induction h1 with
  | self => exact h2
  | fn hs st _ ih => exact .fn hs st (ih h2)
  | arg hs st _ ih => exact .arg hs st (ih h2)

/-- Nodes of a productive term are productive. -/
theorem node_prod {t u : Term} (ht : PureS t) (hp : ∀ k, Pk k t) (h : Node t u) : ∀ k, Pk k u := by
  induction h with
  | self => exact hp
  | @fn t f w u hs _ _ ih =>
    have hfw := steps_pure ht hs
    have hp' : ∀ k, Pk k (f ⬝ w) := fun k => (HnfQ5.pk_wsteps k ht hs.weak).mp (hp k)
    exact ih hfw.app_inv.1 fun k => HnfQ5.prod_sub k hfw (.left w (.refl f)) hp'
  | @arg t f w u hs _ _ ih =>
    have hfw := steps_pure ht hs
    have hp' : ∀ k, Pk k (f ⬝ w) := fun k => (HnfQ5.pk_wsteps k ht hs.weak).mp (hp k)
    exact ih hfw.app_inv.2 fun k => HnfQ5.prod_sub k hfw (.right f (.refl w)) hp'

/-- **Productivity.**  `t` is productive iff no node of `t^∞` has an infinite left spine. -/
theorem prod_iff_nodes {t : Term} (ht : PureS t) :
    (∀ k, Pk k t) ↔ ∀ u, Node t u → ¬ LeftInf u := by
  constructor
  · intro hp u hn hl
    have hu := node_pure ht hn
    have hb := (leftInf_iff hu).mp hl
    obtain ⟨v, hc, hlen, _⟩ := (node_prod ht hp hn 1)
    exact HnfQ5.fold_ne_of_chain hu hc hlen hb
  · intro h k
    induction k generalizing t with
    | zero => trivial
    | succ k ih =>
      have hb : fold t ≠ 36 := fun hb => h t (.self t) ((leftInf_iff ht).mpr hb)
      obtain ⟨u, hc, hlen, hu⟩ := sound_head t ht hb
      have hs := headChain_steps hc
      have hup := steps_pure ht hs
      refine ⟨u, hc, hlen, fun a ha => ?_⟩
      -- every item of the hnf is a node of `t`
      have hna : Node t a := by
        rcases hu with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
        · simp [spine] at ha
        · simp [spine] at ha; subst ha
          exact .arg hs (.inr (.inr (.inl ⟨a, rfl⟩))) (.self a)
        · simp [spine] at ha
          rcases ha with rfl | rfl
          · exact .fn hs (.inr (.inr (.inr ⟨a, y, rfl⟩)))
              (.arg (.refl _) (.inr (.inr (.inl ⟨a, rfl⟩))) (.self a))
          · exact .arg hs (.inr (.inr (.inr ⟨x, a, rfl⟩))) (.self a)
      exact ih (node_pure ht hna) fun v hv => h v (node_trans hna hv)

end InfNF
