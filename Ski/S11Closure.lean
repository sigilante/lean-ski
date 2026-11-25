import Ski.S11Grammar
import Ski.Conv
import Ski.HeadRec
open Term HnfS

/-!
# S11: closure of Red(𝔅) under subterms (Lemma 15) and persistence (Lemma 10(c))

Paper S11, §5.  Both lemmas are proved over parallel reduction `Par` (`Ski/Weak.lean`), never
over redex positions: a one-step reduct `t → t'` is a `Par t t'` (`WStep.par`), and "a subterm
of `t'`" is a structural case split on the `Par` derivation, with `HeadRec.Sub` for subterms.
The only non-structural case is `Par.S3` (the contracted redex `S x y z`), where the paper uses
(Std); here (Std) is `wsteps_split` together with `Conv.parIs_app` and `Conv.parIs_S`.

* **Lemma 15** (`lem:closure`) is proved for an arbitrary set `B` satisfying its two
  hypotheses (`closure`), then instantiated to `𝔅` with Lemma 16 (`lemma15`).
* **Lemma 10(c)** (`lem:persist`) is proved for an arbitrary *spine predicate* `P : ℕ → Term →
  Prop` (`Spine P`: every `s` with `P j s` head-reduces to a two-item hnf `S s' t'` with
  `P (j+1) s'`).  A solution `s` in the sense of Definition 14 gives one, with `P j s_j`; the
  equations `t_{j+1} ≍ b_{k+j+1}` are not used.  Like the paper, it assumes that `t` is a pure
  S-term (`K`/`I` redexes could erase the occurrence).
-/

namespace S11
open HeadRec (Sub)

/-! ## Lemma 15 -/

/-- `Red B`: the reducts of members of `B`. -/
def Red (B : Term → Prop) (t : Term) : Prop := ∃ β, B β ∧ WSteps β t

/-- `Red(𝔅)`. -/
abbrev RedB : Term → Prop := Red InB

theorem Red.wsteps {B : Term → Prop} {t u : Term} (h : Red B t) (hu : WSteps t u) : Red B u :=
  let ⟨β, hb, hr⟩ := h
  ⟨β, hb, hr.trans hu⟩

theorem Red.of_mem {B : Term → Prop} {t : Term} (h : B t) : Red B t := ⟨t, h, .refl t⟩

/-- Hypothesis (i) of Lemma 15, lifted to subterms. -/
theorem mem_sub {B : Term → Prop} (h1 : ∀ f x, B (f ⬝ x) → B f ∧ B x) {u t : Term}
    (hs : Sub u t) : B t → B u := by
  induction hs with
  | refl => exact id
  | left x _ ih => exact fun h => ih (h1 _ x h).1
  | right f _ ih => exact fun h => ih (h1 f _ h).2

/-- The `S3` case of Lemma 15 (the paper's `x z`, `y z` case): if `S x y z ∈ Red B`, then
(Std) gives `β ↠_h S x₀ y₀ z₀` by head steps and then `S x y z` by internal steps, so `x z` and
`y z` are reducts of `x₀ z₀`, `y₀ z₀ ∈ B` (hypothesis (ii)). -/
theorem red_S3 {B : Term → Prop}
    (h2 : ∀ β x y z, B β → Steps β (S ⬝ x ⬝ y ⬝ z) → B (x ⬝ z) ∧ B (y ⬝ z))
    {f g x : Term} (h : Red B (S ⬝ f ⬝ g ⬝ x)) : Red B (f ⬝ x) ∧ Red B (g ⬝ x) := by
  obtain ⟨β, hb, hr⟩ := h
  obtain ⟨T, h1, hT⟩ := wsteps_split hr
  obtain ⟨T2, x0, rfl, h3, hx⟩ := Conv.parIs_app hT
  obtain ⟨T1, g0, rfl, h4, hg⟩ := Conv.parIs_app h3
  obtain ⟨T0, f0, rfl, h5, hf⟩ := Conv.parIs_app h4
  have e := Conv.parIs_S h5
  subst e
  obtain ⟨hfx, hgx⟩ := h2 β f0 g0 x0 hb h1
  exact ⟨⟨_, hfx, WSteps.app hf hx⟩, ⟨_, hgx, WSteps.app hg hx⟩⟩

/-- One parallel step keeps "every subterm is in `Red B`". -/
theorem subRed_par {B : Term → Prop}
    (h2 : ∀ β x y z, B β → Steps β (S ⬝ x ⬝ y ⬝ z) → B (x ⬝ z) ∧ B (y ⬝ z))
    {t t' : Term} (hp : Par t t') :
    (∀ u, Sub u t → Red B u) → ∀ u, Sub u t' → Red B u := by
  induction hp with
  | S => exact id
  | K => exact id
  | I => exact id
  | @app f f' x x' hf hx ihf ihx =>
    intro h u hu
    cases hu with
    | refl => exact (h _ .refl).wsteps (Par.app hf hx).wsteps
    | left _ hu => exact ihf (fun v hv => h v (.left x hv)) u hu
    | right _ hu => exact ihx (fun v hv => h v (.right f hv)) u hu
  | @K2 x x' y _ ihx =>
    intro h
    exact ihx (fun v hv => h v (.left y (.right K hv)))
  | @I1 x x' _ ihx =>
    intro h
    exact ihx (fun v hv => h v (.right I hv))
  | @S3 f f' g g' x x' hf hg hx ihf ihg ihx =>
    intro h u hu
    have hf' : ∀ v, Sub v f → Red B v := fun v hv => h v (.left x (.left g (.right S hv)))
    have hg' : ∀ v, Sub v g → Red B v := fun v hv => h v (.left x (.right (S ⬝ f) hv))
    have hx' : ∀ v, Sub v x → Red B v := fun v hv => h v (.right (S ⬝ f ⬝ g) hv)
    obtain ⟨hfx, hgx⟩ := red_S3 h2 (h _ .refl)
    cases hu with
    | refl => exact (h _ .refl).wsteps (Par.S3 hf hg hx).wsteps
    | left _ hu =>
      cases hu with
      | refl => exact hfx.wsteps (Par.app hf hx).wsteps
      | left _ hu => exact ihf hf' u hu
      | right _ hu => exact ihx hx' u hu
    | right _ hu =>
      cases hu with
      | refl => exact hgx.wsteps (Par.app hg hx).wsteps
      | left _ hu => exact ihg hg' u hu
      | right _ hu => exact ihx hx' u hu

/-- Reduction keeps "every subterm is in `Red B`". -/
theorem subRed_wsteps {B : Term → Prop}
    (h2 : ∀ β x y z, B β → Steps β (S ⬝ x ⬝ y ⬝ z) → B (x ⬝ z) ∧ B (y ⬝ z))
    {t t' : Term} (hr : WSteps t t') :
    (∀ u, Sub u t → Red B u) → ∀ u, Sub u t' → Red B u := by
  induction hr with
  | refl => exact id
  | step s _ ih => exact fun h => ih (subRed_par h2 s.par h)

/-- **Lemma 15** (`lem:closure`), for any set `B`.  Suppose that (i) the function part and the
argument of every member of `B` that is an application are in `B`, and (ii) for every `β ∈ B`
and every frame `S x₀ y₀ z₀` with exactly three items on the head run of `β`, the terms
`x₀ z₀` and `y₀ z₀` are in `B`.  Then `Red B` is closed under subterms. -/
theorem closure {B : Term → Prop} (h1 : ∀ f x, B (f ⬝ x) → B f ∧ B x)
    (h2 : ∀ β x y z, B β → Steps β (S ⬝ x ⬝ y ⬝ z) → B (x ⬝ z) ∧ B (y ⬝ z))
    {t u : Term} (ht : Red B t) (hu : Sub u t) : Red B u := by
  obtain ⟨β, hb, hr⟩ := ht
  exact subRed_wsteps h2 hr (fun v hv => .of_mem (mem_sub h1 hv hb)) u hu

/-- **Lemma 15** for `𝔅` (with Lemma 16): `Red(𝔅)` is closed under subterms. -/
theorem lemma15 {t u : Term} (ht : RedB t) (hu : Sub u t) : RedB u :=
  closure (fun _ _ h => lemma16_i h) (fun _ _ _ _ hb hr => lemma16_ii hb hr) ht hu

/-! ## Lemma 10(c) -/

/-- Two head normal forms on one head run are equal. -/
theorem hnf_eq {s a b : Term} (ha : Steps s a) (hA : IsHnf a) (hb : Steps s b)
    (hB : IsHnf b) : a = b := by
  rcases InfNF.steps_cmp ha hb with h | h
  · exact (InfNF.steps_from_hnf hA h).symm
  · exact InfNF.steps_from_hnf hB h

theorem isHnf_S2 (x y : Term) : IsHnf (S ⬝ x ⬝ y) := .inr (.inr ⟨x, y, rfl⟩)

/-- A term with the two-item hnf `S s' t'` does not reduce to `S` (the paper: `r ≍ s_j` has a
two-item hnf). -/
theorem reduct_ne_S {s s' t' : Term} (hs : Steps s (S ⬝ s' ⬝ t')) (h : WSteps s S) : False := by
  obtain ⟨T, h1, hT⟩ := wsteps_split h
  have e := Conv.parIs_S hT
  subst e
  have e := hnf_eq h1 (.inl rfl) hs (isHnf_S2 s' t')
  cases e

/-- A term with the two-item hnf `S s' t'` does not reduce to `S x`. -/
theorem reduct_ne_S1 {s s' t' x : Term} (hs : Steps s (S ⬝ s' ⬝ t')) (h : WSteps s (S ⬝ x)) :
    False := by
  obtain ⟨T, h1, hT⟩ := wsteps_split h
  obtain ⟨T0, x0, rfl, h3, _⟩ := Conv.parIs_app hT
  have e := Conv.parIs_S h3
  subst e
  have e := hnf_eq h1 (.inr (.inl ⟨x0, rfl⟩)) hs (isHnf_S2 s' t')
  cases e

/-- If a term with the two-item hnf `S s' t'` reduces to `S x y`, then `x` is a reduct of `s'`
(the paper: (Std) gives `s_j ↠_h S s_{j+1} t_{j+1} ↠ S x y` by internal steps). -/
theorem reduct_S2 {s s' t' x y : Term} (hs : Steps s (S ⬝ s' ⬝ t'))
    (h : WSteps s (S ⬝ x ⬝ y)) : WSteps s' x := by
  obtain ⟨T, h1, hT⟩ := wsteps_split h
  obtain ⟨T1, y0, rfl, h3, _⟩ := Conv.parIs_app hT
  obtain ⟨T0, x0, rfl, h4, hx⟩ := Conv.parIs_app h3
  have e := Conv.parIs_S h4
  subst e
  have e := hnf_eq h1 (isHnf_S2 x0 y0) hs (isHnf_S2 s' t')
  cases e
  exact hx

/-- A *spine predicate*: `P j s` says that `s` plays the role of `s_j` of a solution.  Every such
`s` head-reduces to a two-item hnf `S s' t'` whose first item satisfies `P (j+1)`.  For a
solution `s₀` from `k` (Definition 14), `P j s := (s = s_j)` is one, and so is
`P j s := "s is a solution from k + j"`. -/
def Spine (P : Nat → Term → Prop) : Prop :=
  ∀ j s, P j s → ∃ s' t', Steps s (S ⬝ s' ⬝ t') ∧ P (j + 1) s'

/-- `t` contains a reduct of some `s_{j'}` with `j' ≥ j`. -/
def Contains (P : Nat → Term → Prop) (j : Nat) (t : Term) : Prop :=
  ∃ j', j ≤ j' ∧ ∃ s u, P j' s ∧ WSteps s u ∧ Sub u t

theorem Contains.sub {P : Nat → Term → Prop} {j : Nat} {t t' : Term} (h : Contains P j t)
    (hs : Sub t t') : Contains P j t' :=
  let ⟨j', hj, s, u, hP, hsu, hu⟩ := h
  ⟨j', hj, s, u, hP, hsu, hu.trans hs⟩

/-- One parallel step of a pure S-term keeps `Contains P j`. -/
theorem contains_par {P : Nat → Term → Prop} (hP : Spine P) {j : Nat} {t t' : Term}
    (hp : Par t t') : PureS t → Contains P j t → Contains P j t' := by
  induction hp with
  | S => exact fun _ h => h
  | K => exact fun _ h => h
  | I => exact fun _ h => h
  | @app f f' x x' hf hx ihf ihx =>
    intro ht h
    obtain ⟨j', hj, s, u, hs, hsu, hu⟩ := h
    have hpf := ht.app_inv.1
    have hpx := ht.app_inv.2
    cases hu with
    | refl => exact ⟨j', hj, s, _, hs, hsu.trans (Par.app hf hx).wsteps, .refl⟩
    | left _ hu => exact (ihf hpf ⟨j', hj, s, u, hs, hsu, hu⟩).sub (.left x' .refl)
    | right _ hu => exact (ihx hpx ⟨j', hj, s, u, hs, hsu, hu⟩).sub (.right f' .refl)
  | K2 y _ _ =>
    intro ht
    exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I1 _ _ =>
    intro ht
    exact absurd ht.app_inv.1 PureS.not_I
  | @S3 f f' g g' x x' hf hg hx ihf ihg ihx =>
    intro ht h
    obtain ⟨j', hj, s, u, hs, hsu, hu⟩ := h
    have hpx := ht.app_inv.2
    have hpg := ht.app_inv.1.app_inv.2
    have hpf := ht.app_inv.1.app_inv.1.app_inv.2
    obtain ⟨s1, t1, hst, hP1⟩ := hP j' s hs
    cases hu with
    | refl => exact ⟨j', hj, s, _, hs, hsu.trans (Par.S3 hf hg hx).wsteps, .refl⟩
    | left _ hu =>
      cases hu with
      | refl =>
        exact ⟨j' + 1, Nat.le_succ_of_le hj, s1, f', hP1, (reduct_S2 hst hsu).trans hf.wsteps,
          .left _ (.left _ .refl)⟩
      | left _ hu =>
        cases hu with
        | refl => exact (reduct_ne_S1 hst hsu).elim
        | left _ hu =>
          cases hu
          exact (reduct_ne_S hst hsu).elim
        | right _ hu =>
          exact (ihf hpf ⟨j', hj, s, u, hs, hsu, hu⟩).sub (.left _ (.left _ .refl))
      | right _ hu =>
        exact (ihg hpg ⟨j', hj, s, u, hs, hsu, hu⟩).sub (.right _ (.left _ .refl))
    | right _ hu =>
      exact (ihx hpx ⟨j', hj, s, u, hs, hsu, hu⟩).sub (.left _ (.right _ .refl))

/-- Reduction of a pure S-term keeps `Contains P j`. -/
theorem contains_wsteps {P : Nat → Term → Prop} (hP : Spine P) {j : Nat} {t t' : Term}
    (hr : WSteps t t') : PureS t → Contains P j t → Contains P j t' := by
  induction hr with
  | refl => exact fun _ h => h
  | step s _ ih => exact fun ht h => ih (wstep_pure s ht).1 (contains_par hP s.par ht h)

/-- **Lemma 10(c)** (`lem:persist`).  Let `P` be a spine predicate (a solution).  If the pure
S-term `t` contains a reduct of `s_j`, then every reduct of `t` contains a reduct of some
`s_{j'}` with `j' ≥ j`. -/
theorem lemma10c {P : Nat → Term → Prop} (hP : Spine P) {j : Nat} {s u t t' : Term}
    (ht : PureS t) (hs : P j s) (hsu : WSteps s u) (hut : Sub u t) (hr : WSteps t t') :
    ∃ j', j ≤ j' ∧ ∃ s' u', P j' s' ∧ WSteps s' u' ∧ Sub u' t' :=
  contains_wsteps hP hr ht ⟨j, Nat.le_refl j, s, u, hs, hsu, hut⟩

end S11
