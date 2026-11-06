import Ski.CantorLift

open Term

/-!
# A behavioural lift at Nat → Bool, for m-local functions

`NoLift.no_lift_conv`: no closed term lifts every function *total on the
numerals*.  This module shows that the obstruction is the hypothesis, not the
type: under a modulus as strong as the one `CantorLift` assumes at Cantor
space, Nat → Bool has a lift.

- `AtLeast m n`: `n` weakly reduces to at least `m` successor layers, the last
  tail arbitrary (it may diverge).  The infinite numeral satisfies it for every
  `m` (`omega_atLeast`).
- `NLocal m φ f`: `f` gives `φ c` on the numeral `c` for `c < m`, and `φ m` on
  every term with at least `m` successor layers.  So `f` forces at most `m`
  layers of its argument, and it extends continuously to the one-point
  compactification ℕ∞ (Escardó), with value `φ m` at ∞.
- `srchT p = p 0 0 (succ (srch (p ∘ succ)))`: if `p 0` then `0`, else the
  successor of the search for `p ∘ succ`.  It builds a lazy numeral, infinite
  when `p` is never true.  For an `m`-local `p`, `p (srch p)` forces at most `m`
  layers, so it reduces to a boolean, true exactly when `p` is true at some
  numeral (`search_nat`): the naturals are searchable *for m-local
  predicates*, as ℕ∞ is.
- Then, as at Cantor space, constancy is decided (`constN_spec`), `f`
  tabulates into a finite tree whose nodes hold the value at `0` and the tree of
  `f ∘ succ` (`treeN_spec`), the tree lifts to its code, and
  **`natL f = App ⟨evalN⟩ (liftTreeN (treeN f))`** is a lift (`nat_lift`,
  `nat_canonical`).

Where the impossibility sits.
- `G (num k)` is `(k+1)`-local (`G_num_nlocal`).
- The witness of `no_lift`, `G ω`, is `m`-local for no `m` (`G_omega_not_local`). It is
  constantly false, but it walks its argument all the way down, so it has no value at the
  infinite numeral.
- No closed term lifts the `m`-local functions together with `G ω` (`no_lift_local_plus_one`).

So the line among the functions total on the numerals is *totality at ∞* (on ℕ∞, not just ℕ).
It is not continuity: `G ω` is extensionally constant. The obstruction is intensional, since
m-local functions are, extensionally, exactly the eventually constant ones.

Conjectured, not proved: totality on the numerals and at `ω` implies `m`-locality, by a
generalization of `NoLift.sim` (the fan step at ℕ∞).
-/

namespace NatLift

open NoLift LiftBool Search CantorLift

-- ---------------------------------------------------------------------------
-- Numerals with at least m successor layers
-- ---------------------------------------------------------------------------

/-- `n` has at least `m` successor layers. -/
def AtLeast : Nat → Term → Prop
  | 0, _ => True
  | m + 1, n => ∃ n', WSteps n (succS ⬝ n') ∧ AtLeast m n'

theorem AtLeast.back {m : Nat} {n n'' : Term} (h : WSteps n'' n) (hn : AtLeast m n) : AtLeast m n'' := by
  cases m with
  | zero => trivial
  | succ m => obtain ⟨n', h1, h2⟩ := hn; exact ⟨n', h.trans h1, h2⟩

theorem num_atLeast : ∀ (m c : Nat), m ≤ c → AtLeast m (num c)
  | 0, _, _ => trivial
  | m + 1, c + 1, h => ⟨num c, .refl _, num_atLeast m c (by omega)⟩

theorem omega_atLeast : ∀ (m : Nat) {z : Term}, Steps z (fixB succS) → AtLeast m (omegaT z)
  | 0, _, _ => trivial
  | m + 1, z, hz => ⟨omegaT (I ⬝ z), (fixSelf_unroll (F := succS) hz).weak,
      omega_atLeast m (.step (.I _) hz)⟩

/-- `f` is `m`-local with values `φ 0, …, φ (m−1)` at the first numerals and
    `φ m` from `m` on. -/
def NLocal (m : Nat) (φ : Nat → Bool) (f : Term) : Prop :=
  (∀ c, c < m → WSteps (f ⬝ num c) (boolT (φ c))) ∧
  (∀ n, AtLeast m n → WSteps (f ⬝ n) (boolT (φ m)))

/-- An `m`-local function is total on the numerals. -/
theorem nlocal_value {m : Nat} {φ : Nat → Bool} {f : Term} (hf : NLocal m φ f) (c : Nat) :
    WSteps (f ⬝ num c) (boolT (φ (min c m))) := by
  by_cases h : c < m
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]; exact hf.1 c h
  · rw [Nat.min_eq_right (by omega)]; exact hf.2 _ (num_atLeast m c (by omega))

/-- `f ∘ succ`. -/
def shiftN (f : Term) : Term := S ⬝ (K ⬝ f) ⬝ succS

theorem shiftN_wsteps (f x : Term) : WSteps (shiftN f ⬝ x) (f ⬝ (succS ⬝ x)) :=
  (WSteps.single (WStep.S _ _ _)).trans (WSteps.left _ (.single (.K _ _)))

theorem nlocal_shift {m : Nat} {φ : Nat → Bool} {f : Term} (hf : NLocal (m + 1) φ f) :
    NLocal m (fun k => φ (k + 1)) (shiftN f) :=
  ⟨fun c hc => (shiftN_wsteps f _).trans (hf.1 (c + 1) (by omega)),
   fun n hn => (shiftN_wsteps f n).trans (hf.2 _ ⟨n, .refl _, hn⟩)⟩

theorem nlocal_zero {φ : Nat → Bool} {f : Term} (hf : NLocal 0 φ f) (n : Term) :
    WSteps (f ⬝ n) (boolT (φ 0)) := hf.2 n trivial

theorem nlocal_comp {m : Nat} {φ : Nat → Bool} {f : Term} (g : Term) (ψ : Bool → Bool)
    (hg : ∀ b, WSteps (g ⬝ boolT b) (boolT (ψ b))) (hf : NLocal m φ f) :
    NLocal m (fun k => ψ (φ k)) (comp g f) :=
  ⟨fun c hc => (comp_wsteps _ _ _).trans ((WSteps.right _ (hf.1 c hc)).trans (hg _)),
   fun n hn => (comp_wsteps _ _ _).trans ((WSteps.right _ (hf.2 n hn)).trans (hg _))⟩

-- ---------------------------------------------------------------------------
-- The search over the naturals, for m-local predicates
-- ---------------------------------------------------------------------------

/-- `srch p = p 0 0 (succ (srch (p ∘ succ)))`, over `r` (0), `p` (1). -/
def srchBody : OTerm :=
  .var 1 ⬝ₒ (num 0).toO ⬝ₒ (num 0).toO ⬝ₒ
    (succS.toO ⬝ₒ (.var 0 ⬝ₒ (S.toO ⬝ₒ (K.toO ⬝ₒ .var 1) ⬝ₒ succS.toO)))

def srchStep : Term := toTerm (absN [0, 1] srchBody)

/-- **The search**, the fixpoint of `srchStep`. -/
def srchT : Term := fixSelf srchStep (fixB srchStep)

theorem srch_unroll : WSteps srchT (srchStep ⬝ srchT) := by
  have h := (fixSelf_unroll (F := srchStep) (Steps.refl (fixB srchStep))).weak
  have hI : WSteps (fixSelf srchStep (I ⬝ fixB srchStep)) srchT := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem srch_unfold (p : Term) :
    WSteps (srchT ⬝ p) (p ⬝ num 0 ⬝ num 0 ⬝ (succS ⬝ (srchT ⬝ shiftN p))) := by
  have h := absN_beta_close [0, 1] srchBody (fun _ => K) [srchT, p] rfl
  simp only [srchBody, OTerm.close, close_toO, appT] at h
  exact (WSteps.left _ srch_unroll).trans h

/-- Is `φ` true at some `k ≤ m`? -/
def anyTo : Nat → (Nat → Bool) → Bool
  | 0, φ => φ 0
  | m + 1, φ => φ 0 || anyTo m (fun k => φ (k + 1))

/-- **The search decides**: for an `m`-local `p`, `p (srch p)` reduces to
    whether `p` is true anywhere, that is at some `k ≤ m`. -/
theorem search_nat : ∀ (m : Nat) (φ : Nat → Bool) (p : Term), NLocal m φ p →
    WSteps (p ⬝ (srchT ⬝ p)) (boolT (anyTo m φ))
  | 0, φ, p, hp => nlocal_zero hp _
  | m + 1, φ, p, hp => by
    have h0 : WSteps (p ⬝ num 0) (boolT (φ 0)) := hp.1 0 (by omega)
    have hu := srch_unfold p
    cases hv : φ 0 with
    | true =>
      rw [hv] at h0
      have hs : WSteps (srchT ⬝ p) (num 0) :=
        hu.trans ((WSteps.left _ (WSteps.left _ h0)).trans (sel true _ _))
      simpa [anyTo, hv] using (WSteps.right p hs).trans h0
    | false =>
      rw [hv] at h0
      have hs : WSteps (srchT ⬝ p) (succS ⬝ (srchT ⬝ shiftN p)) :=
        hu.trans ((WSteps.left _ (WSteps.left _ h0)).trans (sel false _ _))
      have ih := search_nat m _ (shiftN p) (nlocal_shift hp)
      have hj := to_bool_of_join ih (shiftN_wsteps p _)
      simpa [anyTo, hv] using (WSteps.right p hs).trans hj

theorem anyTo_iff : ∀ (m : Nat) (φ : Nat → Bool), anyTo m φ = true ↔ ∃ k, k ≤ m ∧ φ k = true
  | 0, φ => by simp [anyTo]
  | m + 1, φ => by
    rw [anyTo, Bool.or_eq_true, anyTo_iff m]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨0, by omega, h⟩
      · exact ⟨k + 1, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      cases k with
      | zero => exact .inl h
      | succ k => exact .inr ⟨k, by omega, h⟩

-- ---------------------------------------------------------------------------
-- every, const
-- ---------------------------------------------------------------------------

/-- Is `φ` true at every `k ≤ m`? -/
def allTo (m : Nat) (φ : Nat → Bool) : Bool := !anyTo m (fun k => !φ k)

theorem allTo_iff (m : Nat) (φ : Nat → Bool) : allTo m φ = true ↔ ∀ k, k ≤ m → φ k = true := by
  rw [allTo, Bool.not_eq_true', ← Bool.not_eq_true, anyTo_iff]
  constructor
  · intro h k hk
    cases hφ : φ k with
    | true => rfl
    | false => exact absurd ⟨k, hk, by simp [hφ]⟩ h
  · rintro h ⟨k, hk, hk'⟩
    simp [h k hk] at hk'

/-- `every p = not (p' (srch p'))`, `p' = not ∘ p`. -/
def everyN (p : Term) : Term := notT ⬝ (comp notT p ⬝ (srchT ⬝ comp notT p))

theorem everyN_spec {m : Nat} {φ : Nat → Bool} {p : Term} (hp : NLocal m φ p) :
    WSteps (everyN p) (boolT (allTo m φ)) :=
  (WSteps.right _ (search_nat m _ _ (nlocal_comp notT (fun b => !b) not_spec hp))).trans
    (not_spec _)

/-- `const f = every (λ n. eqB (f n) (f ω))`. -/
def constN (f : Term) : Term := everyN (eqWith f (f ⬝ omega0))

theorem constN_spec {m : Nat} {φ : Nat → Bool} {f : Term} (hf : NLocal m φ f) :
    WSteps (constN f) (boolT (allTo m (fun k => φ k == φ m))) := by
  have hω : WSteps (f ⬝ omega0) (boolT (φ m)) := hf.2 _ (omega_atLeast m (.refl _))
  have hl : NLocal m (fun k => φ k == φ m) (eqWith f (f ⬝ omega0)) := by
    have key : ∀ x b, WSteps (f ⬝ x) (boolT b) → WSteps (eqWith f (f ⬝ omega0) ⬝ x) (boolT (b == φ m)) := by
      intro x b hx
      have h0 : WSteps (eqWith f (f ⬝ omega0) ⬝ x) (eqBT ⬝ (f ⬝ x) ⬝ (f ⬝ omega0)) :=
        (iter_sound (k := 3) rfl :
            Steps (eqWith f (f ⬝ omega0) ⬝ x) (eqBT ⬝ (f ⬝ x) ⬝ (K ⬝ (f ⬝ omega0) ⬝ x))).weak.trans
          (WSteps.right _ (.single (.K _ x)))
      exact h0.trans ((WSteps.app (WSteps.right _ hx) hω).trans (eqB_spec _ _))
    exact ⟨fun c hc => key _ _ (hf.1 c hc), fun n hn => by simpa using key _ _ (hf.2 n hn)⟩
  exact everyN_spec hl

-- ---------------------------------------------------------------------------
-- The tree
-- ---------------------------------------------------------------------------

/-- **The datum** an `m`-local function tabulates to: a leaf when it is
    constant, else a node of its value at `0` and the tree of `f ∘ succ`. -/
def DN : Nat → (Nat → Bool) → Term
  | 0, φ => leafT ⬝ boolT (φ 0)
  | m + 1, φ =>
    if allTo (m + 1) (fun k => φ k == φ (m + 1)) then leafT ⬝ boolT (φ (m + 1))
    else nodeT ⬝ boolT (φ 0) ⬝ DN m (fun k => φ (k + 1))

theorem DN_congr : ∀ (m : Nat) (φ ψ : Nat → Bool), (∀ k, k ≤ m → φ k = ψ k) → DN m φ = DN m ψ
  | 0, φ, ψ, h => by simp [DN, h 0 (Nat.le_refl _)]
  | m + 1, φ, ψ, h => by
    have hc : allTo (m + 1) (fun k => φ k == φ (m + 1)) = allTo (m + 1) (fun k => ψ k == ψ (m + 1)) := by
      apply Bool.eq_iff_iff.2
      rw [allTo_iff, allTo_iff]
      constructor
      · intro H k hk; have := H k hk; rw [h k hk, h (m + 1) (Nat.le_refl _)] at this; exact this
      · intro H k hk; have := H k hk; rw [← h k hk, ← h (m + 1) (Nat.le_refl _)] at this; exact this
    have hr := DN_congr m (fun k => φ (k + 1)) (fun k => ψ (k + 1)) fun k hk => h _ (by omega)
    unfold DN
    rw [hc, hr, h 0 (by omega), h (m + 1) (Nat.le_refl _)]

def everyNO (p : OTerm) : OTerm := notT.toO ⬝ₒ (compO notT.toO p ⬝ₒ (srchT.toO ⬝ₒ compO notT.toO p))
def constNO (f : OTerm) : OTerm := everyNO (eqWithO f (f ⬝ₒ omega0.toO))

theorem close_constNO (σ : Nat → Term) (x : Nat) : (constNO (.var x)).close σ = constN (σ x) := by
  simp [constNO, everyNO, eqWithO, compO, OTerm.close, close_toO, constN, everyN, eqWith, CantorLift.comp]

/-- `tree f = const f (Leaf (f ω)) (Node (f 0) (tree (f ∘ succ)))`, over `r` (0), `f` (1). -/
def treeNBody : OTerm :=
  constNO (.var 1) ⬝ₒ (leafT.toO ⬝ₒ (.var 1 ⬝ₒ omega0.toO)) ⬝ₒ
    (nodeT.toO ⬝ₒ (.var 1 ⬝ₒ (num 0).toO) ⬝ₒ (.var 0 ⬝ₒ (S.toO ⬝ₒ (K.toO ⬝ₒ .var 1) ⬝ₒ succS.toO)))

def treeNStep : Term := toTerm (absN [0, 1] treeNBody)

/-- **`treeN`**, the fixpoint of `treeNStep`. -/
def treeNT : Term := fixSelf treeNStep (fixB treeNStep)

theorem treeN_unroll : WSteps treeNT (treeNStep ⬝ treeNT) := by
  have h := (fixSelf_unroll (F := treeNStep) (Steps.refl (fixB treeNStep))).weak
  have hI : WSteps (fixSelf treeNStep (I ⬝ fixB treeNStep)) treeNT := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem treeN_unfold (f : Term) :
    WSteps (treeNT ⬝ f) (constN f ⬝ (leafT ⬝ (f ⬝ omega0)) ⬝
      (nodeT ⬝ (f ⬝ num 0) ⬝ (treeNT ⬝ shiftN f))) := by
  have h := absN_beta_close [0, 1] treeNBody (fun _ => K) [treeNT, f] rfl
  simp only [treeNBody, OTerm.close, close_toO, appT] at h
  rw [close_constNO] at h
  exact (WSteps.left _ treeN_unroll).trans h

theorem allTo_zero_self (φ : Nat → Bool) : allTo 0 (fun k => φ k == φ 0) = true :=
  (allTo_iff 0 _).2 fun k hk => by rw [Nat.le_zero.1 hk]; simp

/-- **Tabulation.** -/
theorem treeN_spec : ∀ (m : Nat) (φ : Nat → Bool) (f : Term), NLocal m φ f →
    WSteps (treeNT ⬝ f) (DN m φ)
  | m, φ, f, hf => by
    have hu := treeN_unfold f
    have hc := constN_spec hf
    have hω : WSteps (f ⬝ omega0) (boolT (φ m)) := hf.2 _ (omega_atLeast m (.refl _))
    have hsel := (hu.trans (WSteps.left _ (WSteps.left _ hc))).trans (sel _ _ _)
    cases m with
    | zero =>
      rw [allTo_zero_self] at hsel
      simpa [DN] using hsel.trans (WSteps.right _ hω)
    | succ m =>
      cases h : allTo (m + 1) (fun k => φ k == φ (m + 1)) with
      | true =>
        rw [h] at hsel
        simpa [DN, h] using hsel.trans (WSteps.right _ hω)
      | false =>
        rw [h] at hsel
        have h0 : WSteps (f ⬝ num 0) (boolT (φ 0)) := hf.1 0 (by omega)
        have hr := treeN_spec m _ _ (nlocal_shift hf)
        simpa [DN, h] using hsel.trans (WSteps.app (WSteps.right _ h0) hr)

-- ---------------------------------------------------------------------------
-- Evaluation
-- ---------------------------------------------------------------------------

/-- `evalN d n = d (λ b. b) (λ b t. n b (λ n'. evalN t n'))`,
    over `ev` (0), `d` (1), `n` (2), `b` (3), `t` (4), `n'` (5). -/
def evalNIn : OTerm := absN [3, 4] (.var 2 ⬝ₒ .var 3 ⬝ₒ absN [5] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 5))
def evalNBody : OTerm := .var 1 ⬝ₒ I.toO ⬝ₒ evalNIn
def evalNStep : Term := toTerm (absN [0, 1, 2] evalNBody)

/-- **`evalN`**, the fixpoint of `evalNStep`. -/
def evalNT : Term := fixSelf evalNStep (fixB evalNStep)

theorem evalN_unroll : WSteps evalNT (evalNStep ⬝ evalNT) := by
  have h := (fixSelf_unroll (F := evalNStep) (Steps.refl (fixB evalNStep))).weak
  have hI : WSteps (fixSelf evalNStep (I ⬝ fixB evalNStep)) evalNT := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem evalN_unfold (d n : Term) : ∃ X, WSteps (evalNT ⬝ d ⬝ n) (d ⬝ I ⬝ X) ∧
    ∀ b t, ∃ Y, WSteps (X ⬝ b ⬝ t) (n ⬝ b ⬝ Y) ∧ ∀ n', WSteps (Y ⬝ n') (evalNT ⬝ t ⬝ n') := by
  have h := absN_beta_close [0, 1, 2] evalNBody (fun _ => K) [evalNT, d, n] rfl
  simp only [evalNBody, OTerm.close, close_toO, appT] at h
  refine ⟨_, (WSteps.left _ (WSteps.left _ evalN_unroll)).trans h, fun b t => ?_⟩
  let σ := overrideC (fun _ => K) [0, 1, 2] [evalNT, d, n]
  have h2 := absN_beta_close [3, 4] (.var 2 ⬝ₒ .var 3 ⬝ₒ absN [5] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 5)) σ [b, t] rfl
  simp only [OTerm.close, appT] at h2
  refine ⟨_, h2, fun n' => ?_⟩
  have h3 := absN_beta_close [5] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 5) (overrideC σ [3, 4] [b, t]) [n'] rfl
  simp only [OTerm.close, appT] at h3
  exact h3

/-- **Evaluation**: the datum gives `φ c` at the numerals below `m`, and `φ m`
    on every term with at least `m` successor layers. -/
theorem evalN_spec : ∀ (m : Nat) (φ : Nat → Bool),
    (∀ c, c < m → WSteps (evalNT ⬝ DN m φ ⬝ num c) (boolT (φ c))) ∧
    (∀ n, AtLeast m n → WSteps (evalNT ⬝ DN m φ ⬝ n) (boolT (φ m))) := by
  have leaf : ∀ (b : Bool) (n : Term), WSteps (evalNT ⬝ (leafT ⬝ boolT b) ⬝ n) (boolT b) := by
    intro b n
    obtain ⟨X, hX, _⟩ := evalN_unfold (leafT ⬝ boolT b) n
    exact (hX.trans (leaf_sel _ _ _)).trans (.single (.I _))
  intro m
  induction m with
  | zero => intro φ; exact ⟨fun c hc => absurd hc (Nat.not_lt_zero _), fun n _ => leaf _ _⟩
  | succ m ih =>
    intro φ
    cases h : allTo (m + 1) (fun k => φ k == φ (m + 1)) with
    | true =>
      have hall := (allTo_iff _ _).1 h
      have hD : DN (m + 1) φ = leafT ⬝ boolT (φ (m + 1)) := by simp [DN, h]
      rw [hD]
      refine ⟨fun c hc => ?_, fun n _ => leaf _ _⟩
      have := hall c (by omega)
      simp only [beq_iff_eq] at this
      rw [this]; exact leaf _ _
    | false =>
      have hD : DN (m + 1) φ = nodeT ⬝ boolT (φ 0) ⬝ DN m (fun k => φ (k + 1)) := by simp [DN, h]
      rw [hD]
      have node : ∀ n, ∃ Y, WSteps (evalNT ⬝ (nodeT ⬝ boolT (φ 0) ⬝ DN m (fun k => φ (k + 1))) ⬝ n)
          (n ⬝ boolT (φ 0) ⬝ Y) ∧ ∀ n', WSteps (Y ⬝ n') (evalNT ⬝ DN m (fun k => φ (k + 1)) ⬝ n') := by
        intro n
        obtain ⟨X, hX, hnode⟩ := evalN_unfold (nodeT ⬝ boolT (φ 0) ⬝ DN m (fun k => φ (k + 1))) n
        obtain ⟨Y, hY, hrec⟩ := hnode (boolT (φ 0)) (DN m (fun k => φ (k + 1)))
        exact ⟨Y, (hX.trans (node_sel _ _ _ _)).trans hY, hrec⟩
      refine ⟨fun c hc => ?_, fun n hn => ?_⟩
      · cases c with
        | zero =>
          obtain ⟨Y, hY, _⟩ := node (num 0)
          exact hY.trans (.single (.K _ _))
        | succ c =>
          obtain ⟨Y, hY, hrec⟩ := node (num (c + 1))
          exact (hY.trans (succS_wsteps (num c) _ Y)).trans
            ((hrec _).trans ((ih (fun k => φ (k + 1))).1 c (by omega)))
      · obtain ⟨n', h1, h2⟩ := hn
        obtain ⟨Y, hY, hrec⟩ := node n
        exact ((hY.trans (WSteps.left _ (WSteps.left _ h1))).trans (succS_wsteps n' _ Y)).trans
          ((hrec _).trans ((ih (fun k => φ (k + 1))).2 n' h2))

-- ---------------------------------------------------------------------------
-- Lifting the datum
-- ---------------------------------------------------------------------------

/-- `lt d = d (λ b. App ⟨Leaf⟩ (b ⟨K⟩ ⟨K I⟩))
                (λ b t. App (App ⟨Node⟩ (b ⟨K⟩ ⟨K I⟩)) (lt t))`,
    over `lt` (0), `d` (1), `b` (2), and `b` (3), `t` (4). -/
def ltNLeaf : OTerm :=
  absN [2] (Requote.appC.toO ⬝ₒ (quoteT leafT).toO ⬝ₒ (.var 2 ⬝ₒ (quoteT K).toO ⬝ₒ (quoteT (K ⬝ I)).toO))
def ltNNode : OTerm :=
  absN [3, 4] (Requote.appC.toO ⬝ₒ
    (Requote.appC.toO ⬝ₒ (quoteT nodeT).toO ⬝ₒ (.var 3 ⬝ₒ (quoteT K).toO ⬝ₒ (quoteT (K ⬝ I)).toO)) ⬝ₒ
    (.var 0 ⬝ₒ .var 4))
def ltNBody : OTerm := .var 1 ⬝ₒ ltNLeaf ⬝ₒ ltNNode
def ltNStep : Term := toTerm (absN [0, 1] ltNBody)

/-- **`liftTreeN`**. -/
def liftTreeNT : Term := fixSelf ltNStep (fixB ltNStep)

theorem ltN_unroll : WSteps liftTreeNT (ltNStep ⬝ liftTreeNT) := by
  have h := (fixSelf_unroll (F := ltNStep) (Steps.refl (fixB ltNStep))).weak
  have hI : WSteps (fixSelf ltNStep (I ⬝ fixB ltNStep)) liftTreeNT := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem ltN_case (d : Term) : WSteps (liftTreeNT ⬝ d)
    (d ⬝ ltNLeaf.close (overrideC (fun _ => K) [0, 1] [liftTreeNT, d])
       ⬝ ltNNode.close (overrideC (fun _ => K) [0, 1] [liftTreeNT, d])) := by
  have h := absN_beta_close [0, 1] ltNBody (fun _ => K) [liftTreeNT, d] rfl
  simp only [ltNBody, OTerm.close, appT] at h
  exact (WSteps.left _ ltN_unroll).trans h

theorem liftTreeN_spec : ∀ (m : Nat) (φ : Nat → Bool),
    WSteps (liftTreeNT ⬝ DN m φ) (quoteT (DN m φ)) := by
  have leaf : ∀ b : Bool, WSteps (liftTreeNT ⬝ (leafT ⬝ boolT b)) (quoteT (leafT ⬝ boolT b)) := by
    intro b
    refine (ltN_case _).trans ((leaf_sel _ _ _).trans ?_)
    have h := absN_beta_close [2]
      (Requote.appC.toO ⬝ₒ (quoteT leafT).toO ⬝ₒ (.var 2 ⬝ₒ (quoteT K).toO ⬝ₒ (quoteT (K ⬝ I)).toO))
      (overrideC (fun _ => K) [0, 1] [liftTreeNT, leafT ⬝ boolT b]) [boolT b] rfl
    simp only [OTerm.close, close_toO, appT] at h
    exact h.trans (WSteps.right _ (quote_bool b))
  intro m
  induction m with
  | zero => intro φ; exact leaf _
  | succ m ih =>
    intro φ
    cases h : allTo (m + 1) (fun k => φ k == φ (m + 1)) with
    | true => simp only [DN, h, if_true]; exact leaf _
    | false =>
      simp only [DN, h]
      refine (ltN_case _).trans ((node_sel _ _ _ _).trans ?_)
      have h2 := absN_beta_close [3, 4]
        (Requote.appC.toO ⬝ₒ
          (Requote.appC.toO ⬝ₒ (quoteT nodeT).toO ⬝ₒ (.var 3 ⬝ₒ (quoteT K).toO ⬝ₒ (quoteT (K ⬝ I)).toO)) ⬝ₒ
          (.var 0 ⬝ₒ .var 4))
        (overrideC (fun _ => K) [0, 1] [liftTreeNT, nodeT ⬝ boolT (φ 0) ⬝ DN m (fun k => φ (k + 1))])
        [boolT (φ 0), DN m (fun k => φ (k + 1))] rfl
      simp only [OTerm.close, close_toO, appT] at h2
      exact h2.trans (WSteps.app (WSteps.right _ (WSteps.right _ (quote_bool _))) (ih _))

-- ---------------------------------------------------------------------------
-- The lift
-- ---------------------------------------------------------------------------

/-- **The lift at Nat → Bool**: `natL f = App ⟨evalN⟩ (liftTreeN (treeN f))`. -/
def natL : Term :=
  toTerm (absN [0] (Requote.appC.toO ⬝ₒ (quoteT evalNT).toO ⬝ₒ (liftTreeNT.toO ⬝ₒ (treeNT.toO ⬝ₒ .var 0))))

/-- **The lift at Nat → Bool for m-local functions.**  `natL f` reduces to a
    code whose term agrees with `f` on every numeral (`evalN_spec` gives it on
    every term with at least `m` successor layers too). -/
theorem nat_lift {m : Nat} {φ : Nat → Bool} {f : Term} (hf : NLocal m φ f) :
    WSteps (natL ⬝ f) (quoteT (evalNT ⬝ DN m φ)) ∧
    ∀ (c : Nat) (r : Bool), WSteps (f ⬝ num c) (boolT r) →
      WSteps (evalNT ⬝ DN m φ ⬝ num c) (boolT r) := by
  refine ⟨?_, fun c r hr => ?_⟩
  · have h := absN_beta_close [0]
      (Requote.appC.toO ⬝ₒ (quoteT evalNT).toO ⬝ₒ (liftTreeNT.toO ⬝ₒ (treeNT.toO ⬝ₒ .var 0)))
      (fun _ => K) [f] rfl
    simp only [OTerm.close, close_toO, appT] at h
    exact h.trans (WSteps.right _ ((WSteps.right _ (treeN_spec m φ f hf)).trans (liftTreeN_spec m φ)))
  · by_cases hc : c < m
    · rw [bool_unique hr (hf.1 c hc)]; exact (evalN_spec m φ).1 c hc
    · have ha := num_atLeast m c (by omega)
      rw [bool_unique hr (hf.2 _ ha)]; exact (evalN_spec m φ).2 _ ha

/-- **Canonicality.** -/
theorem nat_canonical {m : Nat} {φ ψ : Nat → Bool} {f g : Term}
    (hf : NLocal m φ f) (hg : NLocal m ψ g) (h : ∀ k, k ≤ m → φ k = ψ k) :
    ∃ c, WSteps (natL ⬝ f) (quoteT c) ∧ WSteps (natL ⬝ g) (quoteT c) :=
  ⟨_, (nat_lift hf).1, by rw [DN_congr m φ ψ h]; exact (nat_lift hg).1⟩

/-- An m-local function is total on the numerals (`NoLift.Total`), so
    `natL` lifts, uniformly, the m-local part of the class that
    `NoLift.no_lift_conv` shows no closed term lifts entirely. -/
theorem nlocal_total {m : Nat} {φ : Nat → Bool} {f : Term} (hf : NLocal m φ f) : Total f :=
  fun c => ⟨_, nlocal_value hf c⟩

-- ---------------------------------------------------------------------------
-- Where the impossibility sits
-- ---------------------------------------------------------------------------

/-- `G (num k)`, which decides `n > k`, is `(k+1)`-local: the hypothesis is met
    by the very functions `NoLift.no_lift_core` uses. -/
theorem G_num_nlocal (k : Nat) : NLocal (k + 1) (fun c => decide (k < c)) (G ⬝ num k) := by
  refine ⟨fun c _ => G_num c k, ?_⟩
  suffices h : ∀ k n, AtLeast (k + 1) n → WSteps (G ⬝ num k ⬝ n) (boolT true) by
    intro n hn; simpa using h k n hn
  intro k
  induction k with
  | zero =>
    intro n hn
    obtain ⟨n', h1, _⟩ := hn
    obtain ⟨X, hX, _⟩ := G_succ' (num 0) h1
    exact hX.trans (.single (.K _ _))
  | succ k ih =>
    intro n hn
    obtain ⟨n', h1, h2⟩ := hn
    obtain ⟨X, hX, hrec⟩ := G_succ' (num (k + 1)) h1
    exact (hX.trans (succS_wsteps (num k) K X)).trans ((hrec _).trans (ih n' h2))

theorem liftsAt_of_nlocal {m : Nat} {φ : Nat → Bool} {f : Term} (hf : NLocal m φ f) :
    LiftsAt natL f :=
  ⟨_, _, (nat_lift hf).1, .refl _, (nat_lift hf).2⟩

/-- **`G ω` is m-local for no m**: else `natL` would lift it together with every
    `G (num k)`, which `no_lift_core` forbids. -/
theorem G_omega_not_local (m : Nat) (φ : Nat → Bool) : ¬ NLocal m φ (G ⬝ omega0) := fun h =>
  no_lift_core natL (liftsAt_of_nlocal h) fun k => liftsAt_of_nlocal (G_num_nlocal k)

/-- **The sharp statement**: no closed term lifts every m-local function and
    also the one function `G ω`, which is total on the numerals and diverges
    only at the infinite numeral. -/
theorem no_lift_local_plus_one (L : Term)
    (hL : ∀ (m : Nat) (φ : Nat → Bool) (f : Term), NLocal m φ f → LiftsAt L f) :
    ¬ LiftsAt L (G ⬝ omega0) := fun h0 =>
  no_lift_core L h0 fun k => hL _ _ _ (G_num_nlocal k)

end NatLift
