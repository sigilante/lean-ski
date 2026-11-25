import Ski.S11Base
import Ski.Ncfp

open Term

/-!
# S11: teeth and rests as functions; Lemmas 3, 4, 5, 7

Paper S11, *An S-Term Determined by Its Teeth Among Terms Without a Head Normal Form*, §2.
Milestone M0 of the plan `notes/S11-MECH-PLAN.md`.

* **Decidability of having an hnf** on closed S-terms (`decHasHnf`, `hasHnfB`), from S1's fold:
  `t` has an hnf iff `fold t ≠ 36` (`HnfSound.sound`, `HnfS.no_hnf_of_bot`).  Case splits on
  hnf existence go through this instance, so they need no choice.
* **Teeth and rests as functions.**  `runEnd t` is `Full.headEnd` (the hnf, or the *first*
  stable frame) for a closed S-term `t` (purity decided by `isPureB`), and `t` otherwise.
  `rest1 t`, `tooth1 t` are the two parts of the end frame; `restN n t = rest^n(t)`;
  `tooth (n+1) t = τ₁ (rest^n t)` is the paper's `τ_{n+1}` (`tooth 0` is junk, `S`).
  `first_stable_spec` links them to `Conv.FirstStable`: for a closed S-term without an hnf,
  `rest1 t ⬝ tooth1 t` is the first stable frame.  The first stable frame is unique
  (`first_stable_unique`).
* **Lemma 3** (head runs): (a) `head_step_items`, `step_to_S2`, `run_to_S2`; (b) `steps_left`,
  `nohnf_three`, `nohnf_frames_three`; (c) `lemma3c`, `nohnf_of_steps`; (d) `nohnf_app`,
  `nohnf_wsteps`; (e) `wsteps_app`, `conv_S`.
* **Lemma 4** (the Moves): `moves_A`; (B) as an inductive chain `Chain a₀ b₀ u k a b w`
  (`a_i w_i ↠_h S a_{i+1} b_{i+1}`, `w_{i+1} = b_i w_i`), with `moves_B`: the chain ends at the
  first stable frame, `rest1 f = a_k w_k`, `τ₁ f = b_k w_k`.  The existence of `k` is
  well-founded recursion on the length of the head run to the first stable frame
  (`moves_loop`, strong induction on `Ncfp.StepsK`), not a classical "the construction stops".
  `lemma4` packages the case split, decided by `decHasHnf`.
* **Lemma 5** (invariance, cf. S6 Lemma 4): (a) `inv_hnf0/1/2`, through `Conv.obs_conv` with the
  valuation into the quotient of `Term` by convertibility (`cls`, `Quot.sound`); (b)
  `inv_first` (from `Ncfp.lemma_T`), `inv_restN`, `inv_tooth`.
* **Lemma 6** (finite agreement, `lem:finite`): `run_unfold : p ↠_h rest^n(p) τ_n ⋯ τ₁` and
  `lemma6`.
* **Lemma 7** (right suffixes, `lem:suffix`): `RSuf d e t` (`e` is a right suffix of `t` at depth
  `d`); (a) `rsuf_wsteps`; (b) `lemma7b` for the chain `t_{i+1} = τ₁(t_i)` (`tIter`), through the
  reduct `r₀ = rr J t`; (c) `lemma7c`; (d) `lemma7d`.
* **Congruence** of `Conv.Convertible`: `conv_appL`, `conv_appR`, `conv_app`.
-/

namespace S11
open HnfS Conv

/-! ## Congruence of convertibility -/

theorem conv_appL {f f' : Term} (x : Term) (h : Convertible f f') :
    Convertible (f ⬝ x) (f' ⬝ x) := by
  induction h with
  | refl => exact .refl _
  | fwd s _ ih => exact .fwd (.left x s) ih
  | bwd s _ ih => exact .bwd (.left x s) ih

theorem conv_appR (f : Term) {x x' : Term} (h : Convertible x x') :
    Convertible (f ⬝ x) (f ⬝ x') := by
  induction h with
  | refl => exact .refl _
  | fwd s _ ih => exact .fwd (.right f s) ih
  | bwd s _ ih => exact .bwd (.right f s) ih

theorem conv_app {f f' x x' : Term} (hf : Convertible f f') (hx : Convertible x x') :
    Convertible (f ⬝ x) (f' ⬝ x') :=
  (conv_appL x hf).trans (conv_appR f' hx)

/-! ## Deciding hnf existence -/

/-- Having an hnf is decidable on closed S-terms, through the block `fold t` (S1). -/
def decHasHnf {t : Term} (ht : PureS t) : Decidable (HasHnf t) :=
  if h : fold t = 36 then isFalse (no_hnf_of_bot ht h) else isTrue (HnfSound.sound t ht h)

/-- The Boolean test: `fold t ≠ 36`. -/
def hasHnfB (t : Term) : Bool := !(fold t == 36)

theorem hasHnfB_iff {t : Term} (ht : PureS t) : hasHnfB t = true ↔ HasHnf t := by
  unfold hasHnfB
  constructor
  · intro h
    refine HnfSound.sound t ht (fun e => ?_)
    rw [e] at h
    exact Bool.noConfusion h
  · intro h
    cases hb : (fold t == 36) with
    | false => rfl
    | true => exact absurd h (no_hnf_of_bot ht (beq_iff_eq.1 hb))

/-! ## Purity, decided -/

/-- Purity as a Boolean. -/
def isPureB : Term → Bool
  | .S => true
  | .app f x => isPureB f && isPureB x
  | _ => false

theorem isPureB_iff {t : Term} : isPureB t = true ↔ PureS t := by
  induction t with
  | S => exact ⟨fun _ => .S, fun _ => rfl⟩
  | K => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h PureS.not_K⟩
  | I => exact ⟨fun h => Bool.noConfusion h, fun h => absurd h PureS.not_I⟩
  | app f x ihf ihx =>
    constructor
    · intro h
      have h' : (isPureB f && isPureB x) = true := h
      rw [Bool.and_eq_true] at h'
      exact .app (ihf.1 h'.1) (ihx.1 h'.2)
    · intro h
      obtain ⟨hf, hx⟩ := h.app_inv
      show (isPureB f && isPureB x) = true
      rw [ihf.2 hf, ihx.2 hx]; rfl

/-! ## Teeth and rests -/

/-- The end of the head run: `Full.headEnd` for closed S-terms, `t` otherwise. -/
def runEnd (t : Term) : Term :=
  if h : isPureB t = true then (Full.headEnd ⟨t, isPureB_iff.1 h⟩).1 else t

/-- `rest(t)`: the function part of the first stable frame (junk for terms with an hnf). -/
def rest1 (t : Term) : Term :=
  match runEnd t with
  | .app f _ => f
  | _ => S

/-- `τ₁(t)`: the argument of the first stable frame (junk for terms with an hnf). -/
def tooth1 (t : Term) : Term :=
  match runEnd t with
  | .app _ w => w
  | _ => S

/-- `rest^n(t)`, the states of `t`. -/
def restN : Nat → Term → Term
  | 0, t => t
  | n + 1, t => rest1 (restN n t)

/-- The teeth: `tooth (n+1) t = τ_{n+1}(t) = τ₁(rest^n t)`; `tooth 0 t = S` is junk (the paper
indexes teeth from `1`). -/
def tooth : Nat → Term → Term
  | 0, _ => S
  | n + 1, t => tooth1 (restN n t)

theorem restN_zero (t : Term) : restN 0 t = t := rfl
theorem restN_succ (n : Nat) (t : Term) : restN (n + 1) t = rest1 (restN n t) := rfl
theorem tooth_succ (n : Nat) (t : Term) : tooth (n + 1) t = tooth1 (restN n t) := rfl

theorem runEnd_pure {t : Term} (ht : PureS t) : runEnd t = (Full.headEnd ⟨t, ht⟩).1 := by
  unfold runEnd
  rw [dif_pos (isPureB_iff.2 ht)]

/-- `Full.headEnd` is at or before every hnf and every stable frame of the head run. -/
theorem headEnd_first (x : Full.PT) : ∀ u, Steps x.1 u →
    (IsHnf u ∨ ∃ g y, u = g ⬝ y ∧ fold g = 36) → Steps (Full.headEnd x).1 u := by
  refine Full.nxt_wf.induction (C := fun x => ∀ u, Steps x.1 u →
    (IsHnf u ∨ ∃ g y, u = g ⬝ y ∧ fold g = 36) → Steps (Full.headEnd x).1 u) x ?_
  intro x ih u hu hT
  rw [Full.headEnd]
  by_cases hs : Full.stableB x.1 = false
  · rw [dif_pos hs]
    by_cases hn : (Full.nextOf x.1).isSome = true
    · rw [dif_pos hn]
      have s := Full.nextOf_step x.2 (Full.get_spec hn)
      cases hu with
      | refl =>
        exfalso
        rcases hT with hh | ⟨g, y, e, hg⟩
        · exact Phi.no_step_hnf hh s
        · have hb : Full.stableB (g ⬝ y) = true := beq_iff_eq.2 hg
          rw [e] at hs
          exact Bool.noConfusion (hb.symm.trans hs)
      | step s' r =>
        have e := Step.det s' s
        subst e
        exact ih ⟨_, (wstep_pure s.weak x.2).1⟩ ⟨hs, s⟩ u r hT
    · rw [dif_neg hn]; exact hu
  · rw [dif_neg hs]; exact hu

/-- **The link to `Conv.FirstStable`.**  For a closed S-term without an hnf,
`rest1 t ⬝ tooth1 t` is the first stable frame of its head run. -/
theorem first_stable_spec {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) :
    FirstStable t (rest1 t) (tooth1 t) := by
  obtain ⟨f, w, he, hb, hs⟩ := Full.headEnd_stable ht hn
  have hr : runEnd t = f ⬝ w := (runEnd_pure ht).trans he
  have e1 : rest1 t = f := by unfold rest1; rw [hr]
  have e2 : tooth1 t = w := by unfold tooth1; rw [hr]
  rw [e1, e2]
  refine ⟨hs, hb, fun g x hgx hg => ?_⟩
  have h := headEnd_first ⟨t, ht⟩ _ hgx (.inr ⟨g, x, rfl, hg⟩)
  rw [he] at h
  exact h

/-- The first stable frame is unique. -/
theorem first_stable_unique {t f w f' w' : Term} (ht : PureS t) (h : FirstStable t f w)
    (h' : FirstStable t f' w') : f = f' ∧ w = w' := by
  have e := Ncfp.steps_antisymm (InfNF.steps_pure ht h.1) (h.2.2 f' w' h'.1 h'.2.1)
    (h'.2.2 f w h.1 h.2.1)
  injection e with e1 e2
  exact ⟨e1, e2⟩

/-- `FirstStable` determines `rest1` and `tooth1`. -/
theorem rest_tooth_of_first {t f w : Term} (ht : PureS t) (hn : ¬ HasHnf t)
    (h : FirstStable t f w) : rest1 t = f ∧ tooth1 t = w :=
  first_stable_unique ht (first_stable_spec ht hn) h

theorem rest1_pure {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) : PureS (rest1 t) :=
  (InfNF.steps_pure ht (first_stable_spec ht hn).1).app_inv.1

theorem tooth1_pure {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) : PureS (tooth1 t) :=
  (InfNF.steps_pure ht (first_stable_spec ht hn).1).app_inv.2

/-- `rest(t)` again has no hnf. -/
theorem rest1_nohnf {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) : ¬ HasHnf (rest1 t) :=
  no_hnf_of_bot (rest1_pure ht hn) (first_stable_spec ht hn).2.1

theorem restN_pure_nohnf {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) :
    ∀ n, PureS (restN n t) ∧ ¬ HasHnf (restN n t)
  | 0 => ⟨ht, hn⟩
  | n + 1 =>
    have ih := restN_pure_nohnf ht hn n
    ⟨rest1_pure ih.1 ih.2, rest1_nohnf ih.1 ih.2⟩

theorem restN_pure {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) (n : Nat) : PureS (restN n t) :=
  (restN_pure_nohnf ht hn n).1

theorem restN_nohnf {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) (n : Nat) :
    ¬ HasHnf (restN n t) :=
  (restN_pure_nohnf ht hn n).2

theorem tooth_pure {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) : ∀ n, PureS (tooth n t)
  | 0 => .S
  | n + 1 => tooth1_pure (restN_pure ht hn n) (restN_nohnf ht hn n)

/-- Move `n + 1`: the first stable frame of `rest^n(t)` is `rest^{n+1}(t) τ_{n+1}(t)`. -/
theorem move_spec {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) (n : Nat) :
    FirstStable (restN n t) (restN (n + 1) t) (tooth (n + 1) t) :=
  first_stable_spec (restN_pure ht hn n) (restN_nohnf ht hn n)

/-! ## Lemma 3 -/

/-- Head steps act on the function part. -/
theorem steps_left {f f' : Term} (h : Steps f f') (w : Term) : Steps (f ⬝ w) (f' ⬝ w) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.left w s) ih

/-- **Lemma 3(a)**, first half: the items after a head step from `S u₁ u₂ u₃ ⋯` are those of
`u₁`, then `u₃, u₂ u₃, u₄, …`. -/
theorem head_step_items {t t' : Term} (ht : PureS t) (s : Step t t') :
    ∃ u₁ u₂ u₃ rest, HnfSound.spine t = u₁ :: u₂ :: u₃ :: rest ∧
      HnfSound.spine t' = HnfSound.spine u₁ ++ u₃ :: (u₂ ⬝ u₃) :: rest := by
  obtain ⟨u₁, u₂, u₃, rest, hs, rfl⟩ := Phi.step_spine ht s
  refine ⟨u₁, u₂, u₃, rest, hs, ?_⟩
  rw [HnfSound.spine_foldl]
  simp [HnfSound.spine]

/-- **Lemma 3(a)**, one step: a head step to a two-item hnf `S a b` is from `S S y a`, with
`b = y a`. -/
theorem step_to_S2 {t a b : Term} (ht : PureS t) (s : Step t (S ⬝ a ⬝ b)) :
    ∃ y, t = S ⬝ S ⬝ y ⬝ a ∧ b = y ⬝ a := by
  cases s with
  | S f g x => exact ⟨g, rfl, rfl⟩
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | left x s' =>
    exfalso
    cases s' with
    | K x y => exact PureS.not_K ht.app_inv.1.app_inv.1.app_inv.1
    | left x s'' =>
      cases s'' with
      | K x y => exact PureS.not_K ht.app_inv.1.app_inv.1.app_inv.1.app_inv.1
      | I x => exact PureS.not_I ht.app_inv.1.app_inv.1.app_inv.1
    | I x => exact PureS.not_I ht.app_inv.1.app_inv.1
  | I x => exact absurd ht.app_inv.1 PureS.not_I

/-- **Lemma 3(a)**, run form: if a head run takes at least one step to the hnf `S a b`, its last
frame is `S S y a` and `b = y a`. -/
theorem run_to_S2 {t t₁ a b : Term} (ht : PureS t) (s : Step t t₁)
    (h : Steps t₁ (S ⬝ a ⬝ b)) : ∃ y, Steps t (S ⬝ S ⬝ y ⬝ a) ∧ b = y ⬝ a := by
  generalize e : S ⬝ a ⬝ b = T at h
  induction h generalizing t with
  | refl =>
    subst e
    obtain ⟨y, rfl, rfl⟩ := step_to_S2 ht s
    exact ⟨y, .refl _, rfl⟩
  | step s' _ ih =>
    obtain ⟨y, h1, h2⟩ := ih (wstep_pure s.weak ht).1 s' e
    exact ⟨y, .step s h1, h2⟩

/-- **Lemma 3(c)**: a closed S-term has an hnf iff its head run reaches one. -/
theorem lemma3c {t : Term} (ht : PureS t) : HasHnf t ↔ ∃ v, Steps t v ∧ IsHnf v :=
  Phi.hasHnf_iff_head ht

/-- **Lemma 3(c)**, second half (and its weak-reduction form): a term without an hnf has no
reduct with one.  Stated for head reduction, as in the paper. -/
theorem nohnf_of_steps {t u : Term} (hn : ¬ HasHnf t) (h : Steps t u) : ¬ HasHnf u :=
  fun ⟨v, hv, hh⟩ => hn ⟨v, h.weak.trans hv, hh⟩

/-- **Lemma 3(d)**: if `f` has no hnf, then `f w` has none. -/
theorem nohnf_app {f w : Term} (hf : PureS f) (hw : PureS w) (hn : ¬ HasHnf f) :
    ¬ HasHnf (f ⬝ w) :=
  no_hnf_of_bot (.app hf hw) (Full.fold_frame hw ((Conv.stable_iff hf).2 hn))

/-- **Lemma 3(d)**: no reduct of an hnf-less closed S-term has an hnf. -/
theorem nohnf_wsteps {f f' : Term} (hf : PureS f) (hn : ¬ HasHnf f) (h : WSteps f f') :
    ¬ HasHnf f' := by
  obtain ⟨hp, hb⟩ := fold_wsteps h hf
  exact no_hnf_of_bot hp (hb.trans ((Conv.stable_iff hf).2 hn))

/-- **Lemma 3(b)**: a closed S-term without an hnf has at least three items. -/
theorem nohnf_three {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) :
    3 ≤ (HnfSound.spine t).length := by
  rcases Nat.lt_or_ge (HnfSound.spine t).length 3 with h | h
  · exact (hn ⟨t, .refl t, HnfSound.isHnf_of_short ht (Nat.le_of_lt_succ h)⟩).elim
  · exact h

/-- **Lemma 3(b)**: every frame of a term without an hnf has at least three items. -/
theorem nohnf_frames_three {t u : Term} (ht : PureS t) (hn : ¬ HasHnf t) (h : Steps t u) :
    3 ≤ (HnfSound.spine u).length :=
  nohnf_three (InfNF.steps_pure ht h) (nohnf_of_steps hn h)

theorem wstep_app {f x t' : Term} (hp : PureS (f ⬝ x)) (s : WStep (f ⬝ x) t') :
    ∃ g y, t' = g ⬝ y := by
  cases s with
  | S f g x => exact ⟨_, _, rfl⟩
  | K x y => exact absurd hp.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd hp.app_inv.1 PureS.not_I
  | left x _ => exact ⟨_, _, rfl⟩
  | right f _ => exact ⟨_, _, rfl⟩

/-- **Lemma 3(e)**: every reduct of a closed S-application is an application. -/
theorem wsteps_app {t u : Term} (h : WSteps t u) : PureS t → (∃ f x, t = f ⬝ x) →
    ∃ g y, u = g ⬝ y := by
  induction h with
  | refl => intro _ hx; exact hx
  | step s _ ih =>
    intro hp ⟨f, x, e⟩
    subst e
    exact ih (wstep_pure s hp).1 (wstep_app hp s)

/-- **Lemma 3(e)**: `t =β S` implies `t = S`, for closed S-terms. -/
theorem conv_S {t : Term} (ht : PureS t) (h : Convertible t S) : t = S := by
  obtain ⟨w, h1, h2⟩ := conv_iff_join.mp h
  have e := InfNF.wsteps_from_S h2
  subst e
  cases ht with
  | S => rfl
  | @app f x hf hx =>
    obtain ⟨g, y, e⟩ := wsteps_app h1 (.app hf hx) ⟨f, x, rfl⟩
    cases e

/-! ## Lemma 4: the Moves -/

/-- The chain of Lemma 4(B): from `(a, b, w)` with `a w ↠_h S a₁ b₁`, the next triple is
`(a₁, b₁, b w)`; `Chain a₀ b₀ w₀ k a b w` records `k` links ending at `(a, b, w)`. -/
inductive Chain : Term → Term → Term → Nat → Term → Term → Term → Prop
  | zero (a b w : Term) : Chain a b w 0 a b w
  | succ {a b w a₁ b₁ a' b' w' : Term} {k : Nat} :
      Steps (a ⬝ w) (S ⬝ a₁ ⬝ b₁) → Chain a₁ b₁ (b ⬝ w) k a' b' w' →
      Chain a b w (k + 1) a' b' w'

/-- The head run follows the chain: `S a b w ↠_h S a' b' w'`. -/
theorem chain_steps {a b w a' b' w' : Term} {k : Nat} (h : Chain a b w k a' b' w') :
    Steps (S ⬝ a ⬝ b ⬝ w) (S ⬝ a' ⬝ b' ⬝ w') := by
  induction h with
  | zero => exact .refl _
  | succ h _ ih => exact .step (.S _ _ _) ((steps_left h _).trans ih)

/-- After at least one link, the last argument `w_k = b_{k-1} w_{k-1}` is an application. -/
theorem chain_last {a b w a' b' w' : Term} {k : Nat} (h : Chain a b w k a' b' w') :
    (k = 0 ∧ w' = w) ∨ ∃ x y, w' = x ⬝ y := by
  induction h with
  | zero => exact .inl ⟨rfl, rfl⟩
  | @succ a b w _ _ _ _ _ _ _ _ ih =>
    rcases ih with ⟨_, e⟩ | h
    · exact .inr ⟨b, w, e⟩
    · exact .inr h

/-- If `g` has an hnf but `g x` has none, the hnf of `g` has two items. -/
theorem two_item {g x : Term} (hg : PureS g) (hh : HasHnf g) (hn : ¬ HasHnf (g ⬝ x)) :
    ∃ a b, Steps g (S ⬝ a ⬝ b) := by
  obtain ⟨v, hs, hv⟩ := (Phi.hasHnf_iff_head hg).1 hh
  rcases hv with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · exact (hn ⟨S ⬝ x, (steps_left hs x).weak, .inr (.inl ⟨x, rfl⟩)⟩).elim
  · exact (hn ⟨S ⬝ a ⬝ x, (steps_left hs x).weak, .inr (.inr ⟨a, x, rfl⟩)⟩).elim
  · exact ⟨a, b, hs⟩

/-- A root frame `S a b w` on the head run lies at or before the first stable frame. -/
theorem root_before {t r τ a b w : Term} (ht : PureS t) (hF : FirstStable t r τ)
    (hX : Steps t (S ⬝ a ⬝ b ⬝ w)) : Steps (S ⬝ a ⬝ b ⬝ w) (r ⬝ τ) := by
  rcases InfNF.steps_cmp hX hF.1 with h | h
  · exact h
  · exfalso
    obtain ⟨g, e, _, hg, hgb⟩ :=
      InfNF.steps_bot_fun (InfNF.steps_pure ht hF.1).app_inv.1 hF.2.1 h
    injection e with e1 _
    subst e1
    exact fold_hnf hg (.inr (.inr ⟨a, b, rfl⟩)) hgb

/-- The iteration of Lemma 4(B), by strong induction on the number of head steps from the root
frame `S a b w` to the first stable frame `r τ`. -/
theorem moves_loop {t r τ : Term} (ht : PureS t) (hn : ¬ HasHnf t) (hF : FirstStable t r τ) :
    ∀ (n : Nat) (a b w : Term), Steps t (S ⬝ a ⬝ b ⬝ w) →
      Ncfp.StepsK n (S ⬝ a ⬝ b ⬝ w) (r ⬝ τ) →
      ∃ k a' b' w', Chain a b w k a' b' w' ∧ ¬ HasHnf (a' ⬝ w') ∧ r = a' ⬝ w' ∧
        τ = b' ⬝ w' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b w hX hK
    have hpX := InfNF.steps_pure ht hX
    have hnext : Steps t (a ⬝ w ⬝ (b ⬝ w)) := hX.trans (.single (.S a b w))
    have hpaw : PureS (a ⬝ w) := (InfNF.steps_pure ht hnext).app_inv.1
    have hn' : ¬ HasHnf (a ⬝ w ⬝ (b ⬝ w)) := nohnf_of_steps hn hnext
    cases decHasHnf hpaw with
    | isFalse h0 =>
      have hb0 : fold (a ⬝ w) = 36 := (Conv.stable_iff hpaw).2 h0
      have h1 : Steps (r ⬝ τ) (a ⬝ w ⬝ (b ⬝ w)) := hF.2.2 _ _ hnext hb0
      have h2 : Steps (a ⬝ w ⬝ (b ⬝ w)) (r ⬝ τ) := Ncfp.past_root ht hF.1 hF.2.1 hX
      have e := Ncfp.steps_antisymm (InfNF.steps_pure ht hF.1) h1 h2
      injection e with e1 e2
      exact ⟨0, a, b, w, .zero a b w, h0, e1, e2⟩
    | isTrue h0 =>
      obtain ⟨a₁, b₁, h3⟩ := two_item hpaw h0 hn'
      have hX' : Steps t (S ⬝ a₁ ⬝ b₁ ⬝ (b ⬝ w)) := hnext.trans (steps_left h3 _)
      have hplus : HeadRec.Plus (S ⬝ a ⬝ b ⬝ w) (S ⬝ a₁ ⬝ b₁ ⬝ (b ⬝ w)) :=
        ⟨_, .S a b w, steps_left h3 _⟩
      obtain ⟨n', hlt, hK'⟩ := Ncfp.stepsK_plus hpX hK hplus (root_before ht hF hX')
      obtain ⟨k, a', b', w', hc, h4, h5, h6⟩ := ih n' hlt a₁ b₁ (b ⬝ w) hX' hK'
      exact ⟨k + 1, a', b', w', .succ h3 hc, h4, h5, h6⟩

/-- **Lemma 4(A).**  If `f⁻` has no hnf, then `f⁻ u` is stable, `τ₁(f⁻ u) = u` and
`rest(f⁻ u) = f⁻`. -/
theorem moves_A {fm u : Term} (hf : PureS fm) (hu : PureS u) (hn : ¬ HasHnf fm) :
    rest1 (fm ⬝ u) = fm ∧ tooth1 (fm ⬝ u) = u :=
  rest_tooth_of_first (.app hf hu) (nohnf_app hf hu hn)
    (Ncfp.lemma_A ((Conv.stable_iff hf).2 hn) u)

/-- **Lemma 4(B).**  If `f⁻ u` has no hnf and `f⁻ ↠_h S a₀ b₀`, then there is `k` with a chain
`a_i w_i ↠_h S a_{i+1} b_{i+1}` (`w₀ = u`, `w_{i+1} = b_i w_i`, `i < k`), `a_k w_k` has no hnf,
`rest(f⁻ u) = a_k w_k` and `τ₁(f⁻ u) = b_k w_k`. -/
theorem moves_B {fm u a₀ b₀ : Term} (hf : PureS fm) (hu : PureS u) (hn : ¬ HasHnf (fm ⬝ u))
    (h0 : Steps fm (S ⬝ a₀ ⬝ b₀)) :
    ∃ k a b w, Chain a₀ b₀ u k a b w ∧ ¬ HasHnf (a ⬝ w) ∧
      rest1 (fm ⬝ u) = a ⬝ w ∧ tooth1 (fm ⬝ u) = b ⬝ w := by
  have ht : PureS (fm ⬝ u) := .app hf hu
  have hF := first_stable_spec ht hn
  have hX : Steps (fm ⬝ u) (S ⬝ a₀ ⬝ b₀ ⬝ u) := steps_left h0 u
  obtain ⟨n, hK⟩ := Ncfp.stepsK_of_steps (root_before ht hF hX)
  obtain ⟨k, a, b, w, hc, h1, h2, h3⟩ := moves_loop ht hn hF n a₀ b₀ u hX hK
  exact ⟨k, a, b, w, hc, h1, h2, h3⟩

/-- **Lemma 4**, both cases, split by the decidable `HasHnf f⁻`. -/
theorem lemma4 {fm u : Term} (hf : PureS fm) (hu : PureS u) (hn : ¬ HasHnf (fm ⬝ u)) :
    (¬ HasHnf fm ∧ rest1 (fm ⬝ u) = fm ∧ tooth1 (fm ⬝ u) = u) ∨
    (∃ a₀ b₀, Steps fm (S ⬝ a₀ ⬝ b₀) ∧ ∃ k a b w, Chain a₀ b₀ u k a b w ∧
      ¬ HasHnf (a ⬝ w) ∧ rest1 (fm ⬝ u) = a ⬝ w ∧ tooth1 (fm ⬝ u) = b ⬝ w) := by
  cases decHasHnf hf with
  | isFalse h => exact .inl ⟨h, moves_A hf hu h⟩
  | isTrue h =>
    obtain ⟨a₀, b₀, h0⟩ := two_item hf h hn
    exact .inr ⟨a₀, b₀, h0, moves_B hf hu hn h0⟩

/-! ## Lemma 5: invariance -/

/-- Convertibility as a setoid on `Term`. -/
def convSetoid : Setoid Term :=
  ⟨Convertible, ⟨Convertible.refl, Convertible.symm, Convertible.trans⟩⟩

/-- The valuation into the quotient by convertibility. -/
def cls (t : Term) : Quotient convSetoid := Quotient.mk convSetoid t

theorem cls_inv : Inv cls := fun _ s => Quotient.sound (Convertible.bwd s (.refl _))

theorem cls_eq {t u : Term} (h : cls t = cls u) : Convertible t u := Quotient.exact h

/-- **Lemma 5(a)**, no items. -/
theorem inv_hnf0 {t t' : Term} (ht : PureS t) (ht' : PureS t') (hc : Convertible t t')
    (h : Steps t S) : Steps t' S := by
  have ho := (obs_conv cls_inv ht ht' hc).1 (HasObs.s0 (v := cls) h)
  generalize hoo : (Obs.s0 : Obs (Quotient convSetoid)) = o at ho
  cases ho with
  | s0 h' => exact h'
  | s1 => cases hoo
  | s2 => cases hoo
  | bot => cases hoo

/-- **Lemma 5(a)**, one item. -/
theorem inv_hnf1 {t t' a : Term} (ht : PureS t) (ht' : PureS t') (hc : Convertible t t')
    (h : Steps t (S ⬝ a)) : ∃ a', Steps t' (S ⬝ a') ∧ Convertible a a' := by
  have ho := (obs_conv cls_inv ht ht' hc).1 (HasObs.s1 (v := cls) h)
  generalize hoo : Obs.s1 (cls a) = o at ho
  cases ho with
  | s0 => cases hoo
  | s1 h' =>
    injection hoo with e1
    exact ⟨_, h', cls_eq e1⟩
  | s2 => cases hoo
  | bot => cases hoo

/-- **Lemma 5(a)**, two items. -/
theorem inv_hnf2 {t t' a b : Term} (ht : PureS t) (ht' : PureS t') (hc : Convertible t t')
    (h : Steps t (S ⬝ a ⬝ b)) :
    ∃ a' b', Steps t' (S ⬝ a' ⬝ b') ∧ Convertible a a' ∧ Convertible b b' := by
  have ho := (obs_conv cls_inv ht ht' hc).1 (HasObs.s2 (v := cls) h)
  generalize hoo : Obs.s2 (cls a) (cls b) = o at ho
  cases ho with
  | s0 => cases hoo
  | s1 => cases hoo
  | s2 h' =>
    injection hoo with e1 e2
    exact ⟨_, _, h', cls_eq e1, cls_eq e2⟩
  | bot => cases hoo

/-- Convertible closed S-terms agree on having an hnf. -/
theorem inv_nohnf {t t' : Term} (ht : PureS t) (ht' : PureS t') (hc : Convertible t t')
    (hn : ¬ HasHnf t) : ¬ HasHnf t' :=
  (Conv.stable_iff ht').1 ((Ncfp.fold_conv ht ht' hc).symm.trans ((Conv.stable_iff ht).2 hn))

/-- **Lemma 5(b)**: convertible hnf-less closed S-terms have convertible `τ₁` and `rest`. -/
theorem inv_first {t t' : Term} (ht : PureS t) (ht' : PureS t') (hc : Convertible t t')
    (hn : ¬ HasHnf t) :
    ¬ HasHnf t' ∧ Convertible (tooth1 t) (tooth1 t') ∧ Convertible (rest1 t) (rest1 t') := by
  have hn' := inv_nohnf ht ht' hc hn
  have hF := first_stable_spec ht hn
  have hF' := first_stable_spec ht' hn'
  exact ⟨hn', Ncfp.lemma_T ht ht' hc hF.1 hF.2.1 hF'.1 hF'.2.1⟩

/-- **Lemma 5(b)**, states: `rest^n(t) =β rest^n(t')`. -/
theorem inv_restN {t t' : Term} (ht : PureS t) (ht' : PureS t') (hc : Convertible t t')
    (hn : ¬ HasHnf t) : ∀ n, Convertible (restN n t) (restN n t')
  | 0 => hc
  | n + 1 =>
    (inv_first (restN_pure ht hn n)
      (restN_pure ht' (inv_nohnf ht ht' hc hn) n) (inv_restN ht ht' hc hn n)
      (restN_nohnf ht hn n)).2.2

/-- **Lemma 5(b)**, teeth: `τ_n(t) =β τ_n(t')`. -/
theorem inv_tooth {t t' : Term} (ht : PureS t) (ht' : PureS t') (hc : Convertible t t')
    (hn : ¬ HasHnf t) : ∀ n, Convertible (tooth n t) (tooth n t')
  | 0 => .refl _
  | n + 1 =>
    (inv_first (restN_pure ht hn n)
      (restN_pure ht' (inv_nohnf ht ht' hc hn) n) (inv_restN ht ht' hc hn n)
      (restN_nohnf ht hn n)).2.1

/-! ## Lemma 6: finite agreement -/

/-- The teeth `τ_n, …, τ₁`, in spine order. -/
def teethRev : Nat → Term → List Term
  | 0, _ => []
  | n + 1, t => tooth (n + 1) t :: teethRev n t

/-- `p ↠_h rest^n(p) τ_n(p) ⋯ τ₁(p)`. -/
theorem run_unfold {p : Term} (hp : PureS p) (hn : ¬ HasHnf p) :
    ∀ n, Steps p (apps (restN n p) (teethRev n p))
  | 0 => .refl _
  | n + 1 =>
    (run_unfold hp hn n).trans (steps_apps (move_spec hp hn n).1 (teethRev n p))

theorem conv_apps_teeth {p q : Term} :
    ∀ n, (∀ i, 1 ≤ i → i ≤ n → Convertible (tooth i p) (tooth i q)) →
      ∀ T T', Convertible T T' → Convertible (apps T (teethRev n p)) (apps T' (teethRev n q))
  | 0, _, _, _, h => h
  | n + 1, hi, _, _, h =>
    conv_apps_teeth n (fun i h1 h2 => hi i h1 (Nat.le_succ_of_le h2)) _ _
      (conv_app h (hi (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)))

/-- **Lemma 6** (the paper's `lem:finite`).  If `p`, `q` have no hnf, `rest^n(p) =β rest^n(q)` and `τ_i(p) =β τ_i(q)` for
`1 ≤ i ≤ n`, then `p =β q`. -/
theorem lemma6 {p q : Term} (hp : PureS p) (hq : PureS q) (hnp : ¬ HasHnf p)
    (hnq : ¬ HasHnf q) (n : Nat) (hr : Convertible (restN n p) (restN n q))
    (hi : ∀ i, 1 ≤ i → i ≤ n → Convertible (tooth i p) (tooth i q)) : Convertible p q :=
  (Convertible.of_wsteps (run_unfold hp hnp n).weak).trans
    ((conv_apps_teeth n hi _ _ hr).trans (Convertible.of_wsteps (run_unfold hq hnq n).weak).symm)

/-! ## Lemma 7: right suffixes -/

/-- `RSuf d e t`: `t = x₁ (x₂ (⋯ (x_d e)))`, i.e. `e` is a right suffix of `t` at depth `d`. -/
inductive RSuf : Nat → Term → Term → Prop
  | zero (e : Term) : RSuf 0 e e
  | app {d : Nat} {e t : Term} (x : Term) : RSuf d e t → RSuf (d + 1) e (x ⬝ t)

theorem RSuf.pure {d : Nat} {e t : Term} (h : RSuf d e t) (ht : PureS t) : PureS e := by
  induction h with
  | zero => exact ht
  | app _ _ ih => exact ih ht.app_inv.2

/-- **Lemma 7(a)**, one step. -/
theorem rsuf_wstep {d : Nat} {e t : Term} (h : RSuf d e t) : PureS t → ∀ {t' : Term},
    WStep t t' → ∃ d' e', d ≤ d' ∧ WSteps e e' ∧ RSuf d' e' t' := by
  induction h with
  | zero e => intro _ t' s; exact ⟨0, t', Nat.le_refl 0, .single s, .zero t'⟩
  | @app d e t₀ x h₀ ih =>
    intro ht t' s
    cases s with
    | S f g _ => exact ⟨d + 2, e, Nat.le_succ _, .refl e, .app _ (.app g h₀)⟩
    | K _ _ => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
    | I _ => exact absurd ht.app_inv.1 PureS.not_I
    | left _ _ => exact ⟨d + 1, e, Nat.le_refl _, .refl e, .app _ h₀⟩
    | right _ s₀ =>
      obtain ⟨d', e', hd, he, h'⟩ := ih ht.app_inv.2 s₀
      exact ⟨d' + 1, e', Nat.succ_le_succ hd, he, .app x h'⟩

/-- **Lemma 7(a).**  If `t ↠ t'` and `e` is a right suffix of `t` at depth `d`, then `t'` has a
right suffix `e'` at a depth `≥ d` with `e ↠ e'`. -/
theorem rsuf_wsteps {t t' : Term} (hs : WSteps t t') : ∀ {d : Nat} {e : Term}, PureS t →
    RSuf d e t → ∃ d' e', d ≤ d' ∧ WSteps e e' ∧ RSuf d' e' t' := by
  induction hs with
  | refl t => intro d e _ h; exact ⟨d, e, Nat.le_refl d, .refl e, h⟩
  | step s _ ih =>
    intro d e ht h
    obtain ⟨d₁, e₁, hd₁, he₁, h₁⟩ := rsuf_wstep h ht s
    obtain ⟨d₂, e₂, hd₂, he₂, h₂⟩ := ih (wstep_pure s ht).1 h₁
    exact ⟨d₂, e₂, Nat.le_trans hd₁ hd₂, he₁.trans he₂, h₂⟩

/-- The chain `t₀ = t`, `t_{i+1} = τ₁(t_i)`. -/
def tIter : Nat → Term → Term
  | 0, t => t
  | i + 1, t => tIter i (tooth1 t)

theorem tIter_add (i : Nat) : ∀ (j : Nat) (t : Term), tIter (i + j) t = tIter i (tIter j t)
  | 0, _ => rfl
  | j + 1, t => tIter_add i j (tooth1 t)

theorem tIter_succ' (i : Nat) (t : Term) : tIter (i + 1) t = tooth1 (tIter i t) := by
  rw [Nat.add_comm]; exact tIter_add 1 i t

theorem tIter_pure {t : Term} (ht : PureS t) {J : Nat} (hn : ∀ i, i < J → ¬ HasHnf (tIter i t)) :
    ∀ i, i ≤ J → PureS (tIter i t)
  | 0, _ => ht
  | i + 1, hi => by
    rw [tIter_succ']
    exact tooth1_pure (tIter_pure ht hn i (Nat.le_of_succ_le hi)) (hn i hi)

theorem wsteps_appR (f : Term) {x x' : Term} (h : WSteps x x') : WSteps (f ⬝ x) (f ⬝ x') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.right f s) ih

/-- The reduct `r_i` of the paper: `rr 0 u = u`, `rr (m+1) u = rest(u) (rr m (τ₁ u))`. -/
def rr : Nat → Term → Term
  | 0, u => u
  | m + 1, u => rest1 u ⬝ rr m (tooth1 u)

/-- `u ↠ rr m u` while `u, τ₁ u, …` (the first `m`) have no hnf. -/
theorem wsteps_rr : ∀ (m : Nat) (u : Term), PureS u → (∀ i, i < m → ¬ HasHnf (tIter i u)) →
    WSteps u (rr m u)
  | 0, u, _, _ => .refl u
  | m + 1, u, hu, hn => by
    have hn0 : ¬ HasHnf u := hn 0 (Nat.succ_pos m)
    have h1 := (first_stable_spec hu hn0).1.weak
    have h2 := wsteps_rr m (tooth1 u) (tooth1_pure hu hn0)
      (fun i hi => hn (i + 1) (Nat.succ_lt_succ hi))
    exact h1.trans (wsteps_appR (rest1 u) h2)

/-- The right suffixes of `rr m u`, when `τ`-chain reaches `S` at `m`. -/
theorem rsuf_rr : ∀ (m : Nat) (u : Term) {d : Nat} {e : Term}, tIter m u = S →
    RSuf d e (rr m u) → d ≤ m ∧ e = rr (m - d) (tIter d u)
  | 0, u, d, e, hS, h => by
    have hu : u = S := hS
    subst hu
    cases h with
    | zero => exact ⟨Nat.le_refl 0, rfl⟩
  | m + 1, u, d, e, hS, h => by
    cases h with
    | zero => exact ⟨Nat.zero_le _, rfl⟩
    | @app d₀ _ _ _ h₀ =>
      obtain ⟨hd, he⟩ := rsuf_rr m (tooth1 u) hS h₀
      refine ⟨Nat.succ_le_succ hd, ?_⟩
      rw [he, Nat.add_sub_add_right]
      rfl

/-- **Lemma 7(b).**  Let `t₀ = t`, `t_{i+1} = τ₁(t_i)`, with `t₀, …, t_{J−1}` hnf-less and
`t_J = S`.  Every right suffix of `t` at depth `d` is `S` or convertible with `t_i` for some
`d ≤ i < J`. -/
theorem lemma7b {t : Term} (ht : PureS t) {J : Nat} (hn : ∀ i, i < J → ¬ HasHnf (tIter i t))
    (hJ : tIter J t = S) {d : Nat} {e : Term} (h : RSuf d e t) :
    e = S ∨ ∃ i, d ≤ i ∧ i < J ∧ Convertible e (tIter i t) := by
  obtain ⟨d', e', hd, he, h'⟩ := rsuf_wsteps (wsteps_rr J t ht hn) ht h
  obtain ⟨hdJ, rfl⟩ := rsuf_rr J t hJ h'
  rcases Nat.lt_or_ge d' J with hlt | hge
  · refine .inr ⟨d', hd, hlt, ?_⟩
    have hpi : PureS (tIter d' t) := tIter_pure ht hn d' (Nat.le_of_lt hlt)
    have hr := wsteps_rr (J - d') (tIter d' t) hpi (fun i hi => by
      rw [← tIter_add]; exact hn (i + d') (by omega))
    exact (Convertible.of_wsteps he).trans (Convertible.of_wsteps hr).symm
  · have e1 : d' = J := Nat.le_antisymm hdJ hge
    subst e1
    have he' : WSteps e S := by
      rw [Nat.sub_self] at he
      rw [← hJ]
      exact he
    exact .inl (conv_S (h.pure ht) (Convertible.of_wsteps he'))

/-- **Lemma 7(c).**  If `t =β Z`, `Z` has no hnf and `τ₁(Z) = S`, then every right suffix of `t`
at depth `≥ 1` is `S`. -/
theorem lemma7c {t Z : Term} (ht : PureS t) (hZ : PureS Z) (hc : Convertible t Z)
    (hn : ¬ HasHnf Z) (h1 : tooth1 Z = S) {d : Nat} {e : Term} (h : RSuf d e t) (hd : 1 ≤ d) :
    e = S := by
  have hnt : ¬ HasHnf t := inv_nohnf hZ ht hc.symm hn
  have hτ : tooth1 t = S := by
    have := (inv_first ht hZ hc hnt).2.1
    rw [h1] at this
    exact conv_S (tooth1_pure ht hnt) this
  rcases lemma7b (J := 1) ht (fun i hi => by
      cases i with
      | zero => exact hnt
      | succ i => exact absurd hi (by omega)) hτ h with he | ⟨i, hi1, hi2, _⟩
  · exact he
  · exact absurd (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi2 hd) hi1) (Nat.lt_irrefl i)

/-- **Lemma 7(d).**  If `t =β Y`, `Y` and `τ₁(Y)` have no hnf and `τ₁(τ₁(Y)) = S`, then every
right suffix of `t` at depth `1` is `S` or convertible with `τ₁(Y)`, and every one at depth `≥ 2`
is `S`. -/
theorem lemma7d {t Y : Term} (ht : PureS t) (hY : PureS Y) (hc : Convertible t Y)
    (hn : ¬ HasHnf Y) (hn1 : ¬ HasHnf (tooth1 Y)) (h2 : tooth1 (tooth1 Y) = S) {d : Nat}
    {e : Term} (h : RSuf d e t) (hd : 1 ≤ d) :
    e = S ∨ (d = 1 ∧ Convertible e (tooth1 Y)) := by
  have hnt : ¬ HasHnf t := inv_nohnf hY ht hc.symm hn
  obtain ⟨_, hc1, _⟩ := inv_first ht hY hc hnt
  have hp1 := tooth1_pure ht hnt
  have hn1t : ¬ HasHnf (tooth1 t) := inv_nohnf (tooth1_pure hY hn) hp1 hc1.symm hn1
  have hτ : tooth1 (tooth1 t) = S := by
    have := (inv_first hp1 (tooth1_pure hY hn) hc1 hn1t).2.1
    rw [h2] at this
    exact conv_S (tooth1_pure hp1 hn1t) this
  rcases lemma7b (J := 2) ht (fun i hi => by
      match i, hi with
      | 0, _ => exact hnt
      | 1, _ => exact hn1t
      | _ + 2, hi => exact absurd hi (by omega)) hτ h with he | ⟨i, hi1, hi2, hce⟩
  · exact .inl he
  · match i, hi1, hi2, hce with
    | 0, hi1, _, _ => exact absurd (Nat.lt_of_lt_of_le Nat.zero_lt_one hd) (Nat.not_lt_of_le hi1)
    | 1, hi1, _, hce => exact .inr ⟨Nat.le_antisymm hi1 hd, hce.trans hc1⟩
    | _ + 2, _, hi2, _ => exact absurd hi2 (by omega)

end S11
