import Ski.BExp
open Term

/-!
# Theorem Φ: a syntactic congruence of finite index for the Φ observable (S4)

Mechanization of Theorem Φ of `notes/S4-bounded-exposure.md`, section R1 (statement) and R2
(proof).  Setting: closed terms over the single combinator `S`.

* `SModel`: an applicative structure `M` with an element `s`, the S-law, and a homomorphism `φ`
  to S1's 38-block table (`HnfS.β`).  Finiteness of `M` and surjectivity of `φ` are **not**
  assumed: R1 uses finiteness only to obtain the constants `N`, `p`, which are hypotheses here
  (`Periodic`).
* `Periodic 𝔐 N p`: `N ≥ 10`, `p ≥ 1`, and for `k, k' ≥ N − 1` with `k ≡ k' (mod p)`: the
  Fibonacci map of `M` agrees at times `k`, `k'` from every start, and the towers `S^k (S S)`,
  `S^k' (S S)` have the same value.  (`Periodic.of_sIter`: R1's condition on `m ↦ s·m` implies
  the tower condition.)
* `Base` (R1's `≈_b`), `Sim g` (R1's `≃_g`), `Obs` (the observable `O_Φ`), `Ctx` (contexts, with
  any number of holes).
* `theorem_phi`: `t ≃₁₀ t'` implies `O_Φ(C[t]) = O_Φ(C[t'])` for every context `C`.
* `s1Model`, `s1_periodic`: S1 itself satisfies the hypotheses with `N = 10`, `p = 1`.

Proof (R2, with two changes of bookkeeping; see `Rel`, `HR`, `core`).  (1) R2's four kinds of
pair are one constructor `Rel.grad` carrying a level `Lvl n`, `n ≥ r`.  (2) R2's `ρ(P)` (the
number of non-exempt head steps to come) is replaced by a bound `r ≥ r₁ P` on `HnfSound`'s
weight, which drops at every non-exempt step (`HnfSound.root_step`) and is at most 10
(`BExp.r1_le`); these are the two halves of `BExp.skeleton`.  The S-law of the model
(`SModel.law`) is not used by the proof: equal values of replaced pairs are propagated
structurally, and blocks through `φ`.  Arities agree by the `Items` clause, not `arity_blocks`.

"Has no hnf" is `¬ HnfS.HasHnf`; "the hnf" is the head normal form reached by head reduction
(`Steps`), which is unique (`hnf_unique`); for pure terms the two notions agree
(`hasHnf_iff_head`).
-/

namespace Phi
open HnfS HnfSound BExp

/-! ## Models -/

/-- An S-model with a homomorphism to S1's 38-block model.  `law` is the S-law
`s·a·b·c = a·c·(b·c)`; `φ` maps to block numbers and commutes with application. -/
structure SModel where
  M : Type
  app : M → M → M
  s : M
  law : ∀ a b c : M, app (app (app s a) b) c = app (app a c) (app b c)
  φ : M → Nat
  φ_s : φ s = 0
  φ_app : ∀ a b : M, φ (app a b) = β (φ a) (φ b)

/-- The value of a closed S-term in the model (`K`, `I` are not pure-S terms; they get `s`). -/
def SModel.val (𝔐 : SModel) : Term → 𝔐.M
  | .app f x => 𝔐.app (𝔐.val f) (𝔐.val x)
  | _ => 𝔐.s

/-- `k` steps of the Fibonacci map `(a, b) ↦ (b, a·b)` of the model. -/
def SModel.fibM (𝔐 : SModel) : Nat → 𝔐.M × 𝔐.M → 𝔐.M × 𝔐.M
  | 0, q => q
  | k + 1, q => 𝔐.fibM k (q.2, 𝔐.app q.1 q.2)

/-- `k` iterations of `m ↦ s·m`. -/
def SModel.sIter (𝔐 : SModel) : Nat → 𝔐.M → 𝔐.M
  | 0, m => m
  | k + 1, m => 𝔐.app 𝔐.s (𝔐.sIter k m)

/-- The constants of R1: `N ≥ 10`, `p ≥ 1`; for `k, k' ≥ N − 1` congruent mod `p`, the Fibonacci
map agrees at times `k`, `k'` from every start, and `M(S^k (S S)) = M(S^k' (S S))`. -/
structure Periodic (𝔐 : SModel) (N p : Nat) : Prop where
  hN : 10 ≤ N
  hp : 1 ≤ p
  fib : ∀ k k' : Nat, N - 1 ≤ k → N - 1 ≤ k' → k % p = k' % p → ∀ q, 𝔐.fibM k q = 𝔐.fibM k' q
  tow : ∀ k k' : Nat, N - 1 ≤ k → N - 1 ≤ k' → k % p = k' % p →
    𝔐.val (tower k) = 𝔐.val (tower k')

/-! ## The relations of R1 -/

/-- Pairwise relation of two lists (of equal length). -/
inductive All₂ {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | nil : All₂ R [] []
  | cons {a b : α} {l m : List α} : R a b → All₂ R l m → All₂ R (a :: l) (b :: m)

/-- Tower indices related as in R1: equal, or both at least `N` and congruent mod `p`. -/
def TowRel (N p k k' : Nat) : Prop := k = k' ∨ (N ≤ k ∧ N ≤ k' ∧ k % p = k' % p)

/-- **The base relation `≈_b`.**  Equal `M`-values and, if the terms are towers `S^k (S S)`,
`S^k' (S S)`, then `k = k'` or (`k, k' ≥ N` and `k ≡ k' mod p`).  (Equal values give equal
blocks, so one is a tower iff the other is: `tower_of_fold`, `fold_tower`.) -/
def Base (𝔐 : SModel) (N p : Nat) (u u' : Term) : Prop :=
  𝔐.val u = 𝔐.val u' ∧ ∀ k k' : Nat, u = tower k → u' = tower k' → TowRel N p k k'

/-- The items of the head normal forms of `u`, `u'` are pairwise `R`-related (in particular the
arities agree).  The head normal form of a term is unique (`hnf_unique`); the condition is
vacuous if `u` or `u'` has none. -/
def Items (R : Term → Term → Prop) (u u' : Term) : Prop :=
  ∀ v v' : Term, Steps u v → IsHnf v → Steps u' v' → IsHnf v' → All₂ R (spine v) (spine v')

/-- `Lvl n`: the unfoldings agree under `≈_b` at depths `0..n`.  `Lvl 0 = ≈_b`. -/
def Lvl (𝔐 : SModel) (N p : Nat) : Nat → Term → Term → Prop
  | 0 => Base 𝔐 N p
  | n + 1 => fun u u' => Base 𝔐 N p u u' ∧ Items (Lvl 𝔐 N p n) u u'

/-- **The relation `≃_g` of R1** (`sim_zero`, `sim_succ`): it compares the unfolding at depths
`0..g+1` by `≈_b`. -/
def Sim (𝔐 : SModel) (N p g : Nat) : Term → Term → Prop := Lvl 𝔐 N p (g + 1)

/-- `u ≃₀ u'` iff `u ≈_b u'` and the items are pairwise `≈_b`. -/
theorem sim_zero (𝔐 : SModel) (N p : Nat) (u u' : Term) :
    Sim 𝔐 N p 0 u u' ↔ Base 𝔐 N p u u' ∧ Items (Base 𝔐 N p) u u' := Iff.rfl

/-- `u ≃_{g+1} u'` iff `u ≈_b u'` and the items are pairwise `≃_g`. -/
theorem sim_succ (𝔐 : SModel) (N p g : Nat) (u u' : Term) :
    Sim 𝔐 N p (g + 1) u u' ↔ Base 𝔐 N p u u' ∧ Items (Sim 𝔐 N p g) u u' := Iff.rfl

/-! ## Contexts and the observable -/

/-- Contexts over `S`, with any number of holes (one-hole contexts are a special case). -/
inductive Ctx
  | hole : Ctx
  | s : Ctx
  | app : Ctx → Ctx → Ctx

/-- `C[t]`: every hole filled with `t`. -/
def Ctx.plug : Ctx → Term → Term
  | .hole, t => t
  | .s, _ => S
  | .app c d, t => c.plug t ⬝ d.plug t

/-- **The observable `O_Φ`**, as a relation: `none` (⊥) if `t` has no hnf; `some [M a₁, …, M a_j]`
if the hnf of `t` is `S a₁ … a_j`.  (The list carries the arity `j`.)  It is a total function
on pure terms: `obs_total`, `obs_unique`. -/
def Obs (𝔐 : SModel) (t : Term) : Option (List 𝔐.M) → Prop
  | none => ¬ HasHnf t
  | some l => ∃ v, Steps t v ∧ IsHnf v ∧ l = (spine v).map 𝔐.val

/-! ## Lists, values, head reduction -/

theorem All₂.append {α : Type} {R : α → α → Prop} {l m l' m' : List α} (h : All₂ R l m)
    (h' : All₂ R l' m') : All₂ R (l ++ l') (m ++ m') := by
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact .cons hab ih

theorem All₂.mono_mem {α : Type} {R R' : α → α → Prop} {l m : List α} (h : All₂ R l m) :
    (∀ a b, a ∈ l → b ∈ m → R a b → R' a b) → All₂ R' l m := by
  induction h with
  | nil => intro _; exact .nil
  | cons hab _ ih =>
    intro f
    exact .cons (f _ _ (by simp) (by simp) hab)
      (ih fun a b ha hb => f a b (by simp [ha]) (by simp [hb]))

theorem All₂.mono {α : Type} {R R' : α → α → Prop} {l m : List α} (h : All₂ R l m)
    (f : ∀ a b, R a b → R' a b) : All₂ R' l m :=
  h.mono_mem fun a b _ _ => f a b

theorem All₂.forall_left {α : Type} {R : α → α → Prop} {Q : α → Prop} {l m : List α}
    (h : All₂ R l m) (f : ∀ a b, R a b → Q a) : ∀ a ∈ l, Q a := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hab _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with e | ha'
    · rw [e]; exact f _ _ hab
    · exact ih a ha'

theorem All₂.forall_right {α : Type} {R : α → α → Prop} {Q : α → Prop} {l m : List α}
    (h : All₂ R l m) (f : ∀ a b, R a b → Q b) : ∀ b ∈ m, Q b := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hab _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with e | ha'
    · rw [e]; exact f _ _ hab
    · exact ih a ha'

theorem All₂.map_eq {α β : Type} {f : α → β} {l m : List α}
    (h : All₂ (fun a b => f a = f b) l m) : l.map f = m.map f := by
  induction h with
  | nil => rfl
  | @cons a b l m hab _ ih => show f a :: l.map f = f b :: m.map f; rw [hab, ih]

/-- The homomorphism sends the value of a pure term to its block. -/
theorem fold_val (𝔐 : SModel) : ∀ {t : Term}, PureS t → 𝔐.φ (𝔐.val t) = fold t := by
  intro t ht
  induction ht with
  | S => exact 𝔐.φ_s
  | app _ _ ihf ihx =>
    show 𝔐.φ (𝔐.app _ _) = β _ _
    rw [𝔐.φ_app, ihf, ihx]

theorem fold_eq_of_val (𝔐 : SModel) {u u' : Term} (hu : PureS u) (hu' : PureS u')
    (h : 𝔐.val u = 𝔐.val u') : fold u = fold u' := by
  rw [← fold_val 𝔐 hu, ← fold_val 𝔐 hu', h]

theorem val_fibT (𝔐 : SModel) : ∀ (k : Nat) (x y : Term),
    (𝔐.val (fibT k (x, y)).1, 𝔐.val (fibT k (x, y)).2) = 𝔐.fibM k (𝔐.val x, 𝔐.val y) := by
  intro k
  induction k with
  | zero => intro x y; rfl
  | succ k ih => intro x y; exact ih y (x ⬝ y)

theorem val_tower (𝔐 : SModel) : ∀ k : Nat,
    𝔐.val (tower k) = 𝔐.sIter k (𝔐.val (S ⬝ S)) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => show 𝔐.app 𝔐.s (𝔐.val (tower k)) = 𝔐.app 𝔐.s _; rw [ih]

/-- R1's condition "`m ↦ s·m` agrees at iterates `j, j' ≥ N − 1`, `j ≡ j' (mod p)`, on all of
`M`" implies the tower condition of `Periodic`. -/
theorem Periodic.of_sIter {𝔐 : SModel} {N p : Nat} (hN : 10 ≤ N) (hp : 1 ≤ p)
    (fib : ∀ k k' : Nat, N - 1 ≤ k → N - 1 ≤ k' → k % p = k' % p →
      ∀ q, 𝔐.fibM k q = 𝔐.fibM k' q)
    (sit : ∀ k k' : Nat, N - 1 ≤ k → N - 1 ≤ k' → k % p = k' % p →
      ∀ m, 𝔐.sIter k m = 𝔐.sIter k' m) : Periodic 𝔐 N p :=
  ⟨hN, hp, fib, fun k k' h h' e => by rw [val_tower, val_tower]; exact sit k k' h h' e _⟩

theorem step_foldl {a b : Term} (h : Step a b) : ∀ (rest : List Term),
    Step (rest.foldl Term.app a) (rest.foldl Term.app b) := by
  intro rest
  induction rest generalizing a b with
  | nil => exact h
  | cons r rest ih => exact ih (.left r h)

theorem steps_foldl {a b : Term} (h : Steps a b) : ∀ (rest : List Term),
    Steps (rest.foldl Term.app a) (rest.foldl Term.app b) := by
  intro rest
  induction rest generalizing a b with
  | nil => exact h
  | cons r rest ih => exact ih (Steps.left r h)

theorem headChain_steps {t u : Term} (h : HeadChain t u) : Steps t u := by
  induction h with
  | refl => exact .refl _
  | step _ hS _ ih => rw [hS]; exact .step (step_foldl (.S _ _ _) _) ih

theorem no_step_hnf {u u' : Term} (hu : IsHnf u) (s : Step u u') : False := by
  rcases hu with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · cases s
  · cases s with | left _ s => cases s
  · cases s with | left _ s => cases s with | left _ s => cases s

/-- The head normal form reached by head reduction is unique. -/
theorem hnf_unique {t v v' : Term} (h : Steps t v) (hv : IsHnf v) (h' : Steps t v')
    (hv' : IsHnf v') : v = v' := by
  induction h generalizing v' with
  | refl t =>
    cases h' with
    | refl => rfl
    | step s _ => exact (no_step_hnf hv s).elim
  | step s _ ih =>
    cases h' with
    | refl => exact (no_step_hnf hv' s).elim
    | step s' hs' =>
      have e := Step.det s s'
      subst e
      exact ih hv hs' hv'

theorem steps_pure {t u : Term} (ht : PureS t) (h : Steps t u) : PureS u :=
  (fold_wsteps h.weak ht).1

theorem steps_fold {t u : Term} (ht : PureS t) (h : Steps t u) : fold u = fold t :=
  (fold_wsteps h.weak ht).2

/-- A pure term with an hnf reaches it by head reduction (`HnfSound.sound_head`). -/
theorem head_hnf {t : Term} (ht : PureS t) (hb : fold t ≠ 36) : ∃ v, Steps t v ∧ IsHnf v := by
  obtain ⟨u, hc, _, hu⟩ := sound_head t ht hb
  exact ⟨u, headChain_steps hc, hu⟩

/-- For pure terms, "some reduct is an hnf" and "head reduction reaches an hnf" agree. -/
theorem hasHnf_iff_head {t : Term} (ht : PureS t) : HasHnf t ↔ ∃ v, Steps t v ∧ IsHnf v := by
  constructor
  · intro h
    by_cases hb : fold t = 36
    · exact (no_hnf_of_bot ht hb h).elim
    · exact head_hnf ht hb
  · rintro ⟨v, hs, hv⟩
    exact ⟨v, hs.weak, hv⟩

theorem pure_foldl : ∀ (as : List Term) {h : Term}, PureS h → (∀ a ∈ as, PureS a) →
    PureS (as.foldl Term.app h) := by
  intro as
  induction as with
  | nil => intro h hh _; exact hh
  | cons a as ih =>
    intro h hh ha
    exact ih (.app hh (ha a (by simp))) (fun b hb => ha b (by simp [hb]))

theorem fold_foldl_bot : ∀ (as : List Term) {h : Term}, fold h = 36 → (∀ a ∈ as, PureS a) →
    fold (as.foldl Term.app h) = 36 := by
  intro as
  induction as with
  | nil => intro h hh _; exact hh
  | cons a as ih =>
    intro h hh ha
    refine ih ?_ (fun b hb => ha b (by simp [hb]))
    show β (fold h) (fold a) = 36
    rw [hh]; exact absorb (fold_lt (ha a (by simp)))

/-- A head step of a pure term is the root step of its frame. -/
theorem step_spine {t t' : Term} (ht : PureS t) (s : Step t t') : ∃ u₁ u₂ u₃ rest,
    spine t = u₁ :: u₂ :: u₃ :: rest ∧ t' = rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃)) := by
  match hs : spine t with
  | u₁ :: u₂ :: u₃ :: rest =>
    refine ⟨u₁, u₂, u₃, rest, rfl, ?_⟩
    have h0 := pure_eq_foldl ht
    rw [hs] at h0
    have s' : Step t (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := by
      have h1 := step_foldl (Step.S u₁ u₂ u₃) rest
      rw [h0]; exact h1
    exact Step.det s s'
  | [] => exact (no_step_hnf (isHnf_of_short ht (by simp [hs])) s).elim
  | [_] => exact (no_step_hnf (isHnf_of_short ht (by simp [hs])) s).elim
  | [_, _] => exact (no_step_hnf (isHnf_of_short ht (by simp [hs])) s).elim

/-- The weight `r₁` of `HnfSound` does not grow along head reduction. -/
theorem r1_steps {t q : Term} (h : Steps t q) : PureS t → fold t ≠ 36 → r₁ q ≤ r₁ t := by
  induction h with
  | refl => intro _ _; exact Nat.le_refl _
  | step s _ ih =>
    intro ht hb
    obtain ⟨u₁, u₂, u₃, rest, hs, rfl⟩ := step_spine ht s
    obtain ⟨hstep, _, hr, _, _⟩ := root_step ht hb hs
    obtain ⟨hp', he⟩ := wstep_pure hstep ht
    have := ih hp' (by rw [he]; exact hb)
    omega

/-- `Run ℓ t`: head reduction from `t` reaches an hnf in exactly `ℓ` steps. -/
inductive Run : Nat → Term → Prop
  | done {t : Term} : IsHnf t → Run 0 t
  | step {ℓ : Nat} {t t' : Term} : Step t t' → Run ℓ t' → Run (ℓ + 1) t

theorem run_of_steps {t v : Term} (h : Steps t v) (hv : IsHnf v) : ∃ ℓ, Run ℓ t := by
  induction h with
  | refl => exact ⟨0, .done hv⟩
  | step s _ ih => obtain ⟨ℓ, hℓ⟩ := ih hv; exact ⟨ℓ + 1, .step s hℓ⟩

theorem run_step {ℓ : Nat} {t t' : Term} (h : Run ℓ t) (s : Step t t') :
    ∃ ℓ', ℓ = ℓ' + 1 ∧ Run ℓ' t' := by
  cases h with
  | done hv => exact (no_step_hnf hv s).elim
  | step s' h' =>
    have e := Step.det s' s
    subst e
    exact ⟨_, rfl, h'⟩

theorem run_steps {t q : Term} (h : Steps t q) : ∀ {ℓ : Nat}, Run ℓ t →
    ∃ ℓ', ℓ' ≤ ℓ ∧ Run ℓ' q := by
  induction h with
  | refl => intro ℓ h; exact ⟨ℓ, Nat.le_refl _, h⟩
  | step s _ ih =>
    intro ℓ h
    obtain ⟨ℓ₁, e, h1⟩ := run_step h s
    obtain ⟨ℓ', hle, h'⟩ := ih h1
    exact ⟨ℓ', by omega, h'⟩

/-! ## Towers and congruences -/

theorem tower_ne_S (k : Nat) : tower k ≠ S := by
  cases k with
  | zero => intro e; exact Term.noConfusion e
  | succ k => intro e; exact Term.noConfusion e

theorem tower_inj : ∀ {k k' : Nat}, tower k = tower k' → k = k' := by
  intro k
  induction k with
  | zero =>
    intro k' e
    cases k' with
    | zero => rfl
    | succ k' =>
      have e' : S ⬝ S = S ⬝ tower k' := e
      injection e' with _ e2
      exact (tower_ne_S k' e2.symm).elim
  | succ k ih =>
    intro k' e
    cases k' with
    | zero =>
      have e' : S ⬝ tower k = S ⬝ S := e
      injection e' with _ e2
      exact (tower_ne_S k e2).elim
    | succ k' =>
      have e' : S ⬝ tower k = S ⬝ tower k' := e
      injection e' with _ e2
      rw [ih e2]

theorem towRel_succ {N p k k' : Nat} (h : TowRel N p k k') : TowRel N p (k + 1) (k' + 1) := by
  rcases h with e | ⟨a, b, c⟩
  · exact .inl (by rw [e])
  · exact .inr ⟨by omega, by omega, by rw [Nat.add_mod k 1 p, Nat.add_mod k' 1 p, c]⟩

/-- Congruence mod `p` passes to predecessors. -/
theorem mod_pred {p a b : Nat} (hp : 1 ≤ p) (h : (a + 1) % p = (b + 1) % p) : a % p = b % p := by
  have e : ∀ c : Nat, c % p = ((c + 1) % p + (p - 1) % p) % p := by
    intro c
    rw [← Nat.add_mod, show c + 1 + (p - 1) = c + p by omega, Nat.add_mod_right]
  rw [e a, e b, h]

/-! ## The replacement relation of R2 -/

/-- `Lvl n` implies the base relation. -/
theorem lvl_base {𝔐 : SModel} {N p : Nat} : ∀ {n : Nat} {u u' : Term},
    Lvl 𝔐 N p n u u' → Base 𝔐 N p u u'
  | 0, _, _, h => h
  | _ + 1, _, _, h => h.1

/-- Hnf-less terms of equal value are related at every level (R2's pairs of kind (i)). -/
theorem lvl_dead {𝔐 : SModel} {N p : Nat} (n : Nat) {u u' : Term} (hu : PureS u)
    (hb : fold u = 36) (hv : 𝔐.val u = 𝔐.val u') : Lvl 𝔐 N p n u u' := by
  have base : Base 𝔐 N p u u' := by
    refine ⟨hv, fun k k' e _ => ?_⟩
    subst e
    have h := fold_tower k
    rw [hb] at h
    exact absurd h (by decide)
  cases n with
  | zero => exact base
  | succ n =>
    refine ⟨base, fun v v' hs hn _ _ => ?_⟩
    exact absurd ((steps_fold hu hs).trans hb) (fold_hnf (steps_pure hu hs) hn)

/-- **Configurations of R2**, as a relation on pairs of terms: `P'` arises from `P` by replacing
disjoint subterm occurrences `u` by `u'` with `Lvl n u u'` for some `n ≥ r`.  Here `r` bounds
the weight `r₁ P`, hence the number of non-exempt head steps still to come.  This one kind covers
R2's kinds (i) (hnf-less, equal value: every level, `lvl_dead`), (ii) and identical towers (the
tower clause of `≈_b`, `rel_tower`), (iii) (graded: `n = g + 1`) and (iv) (frozen: `n = 0`, which
forces `r = 0`). -/
inductive Rel (𝔐 : SModel) (N p r : Nat) : Term → Term → Prop
  | atom : Rel 𝔐 N p r Term.S Term.S
  | app {f f' x x' : Term} : Rel 𝔐 N p r f f' → Rel 𝔐 N p r x x' →
      Rel 𝔐 N p r (f ⬝ x) (f' ⬝ x')
  | grad {n : Nat} {u u' : Term} : PureS u → PureS u' → r ≤ n → Lvl 𝔐 N p n u u' →
      Rel 𝔐 N p r u u'

section
variable {𝔐 : SModel} {N p : Nat}

theorem Rel.pure {r : Nat} {u u' : Term} (h : Rel 𝔐 N p r u u') : PureS u ∧ PureS u' := by
  induction h with
  | atom => exact ⟨.S, .S⟩
  | app _ _ ihf ihx => exact ⟨.app ihf.1 ihx.1, .app ihf.2 ihx.2⟩
  | grad hu hu' _ _ => exact ⟨hu, hu'⟩

/-- Related terms have equal values (hence equal blocks). -/
theorem Rel.val_eq {r : Nat} {u u' : Term} (h : Rel 𝔐 N p r u u') : 𝔐.val u = 𝔐.val u' := by
  induction h with
  | atom => rfl
  | app _ _ ihf ihx => show 𝔐.app _ _ = 𝔐.app _ _; rw [ihf, ihx]
  | grad _ _ _ hl => exact (lvl_base hl).1

theorem Rel.mono {r r' : Nat} {u u' : Term} (hr : r' ≤ r) (h : Rel 𝔐 N p r u u') :
    Rel 𝔐 N p r' u u' := by
  induction h with
  | atom => exact .atom
  | app _ _ ihf ihx => exact .app ihf ihx
  | grad hu hu' hn hl => exact .grad hu hu' (Nat.le_trans hr hn) hl

theorem Rel.refl {r : Nat} {t : Term} (ht : PureS t) : Rel 𝔐 N p r t t := by
  induction ht with
  | S => exact .atom
  | app _ _ ihf ihx => exact .app ihf ihx

/-- Only `S` is related to `S` (block 0 forces `S`). -/
theorem rel_S {r : Nat} {u u' : Term} (h : Rel 𝔐 N p r u u') : u = S → u' = S := by
  induction h with
  | atom => intro _; rfl
  | app _ _ _ _ => intro e; exact Term.noConfusion e
  | grad hu hu' _ hl =>
    intro e
    subst e
    exact fold_eq_zero hu' (fold_eq_of_val 𝔐 hu hu' (lvl_base hl).1).symm

/-- A term `≈_b`-related to a tower is a tower with a related index. -/
theorem base_tower {k : Nat} {u' : Term} (hu' : PureS u') (h : Base 𝔐 N p (tower k) u') :
    ∃ k', u' = tower k' ∧ TowRel N p k k' := by
  have e := fold_eq_of_val 𝔐 (tower_pure k) hu' h.1
  obtain ⟨k', rfl⟩ := tower_of_fold hu' (by rw [← e]; exact fold_tower k)
  exact ⟨k', rfl, h.2 k k' rfl rfl⟩

/-- A term related to a tower is a tower with a related index. -/
theorem rel_tower {r : Nat} {u u' : Term} (h : Rel 𝔐 N p r u u') : ∀ k : Nat, u = tower k →
    ∃ k', u' = tower k' ∧ TowRel N p k k' := by
  induction h with
  | atom => intro k e; exact (tower_ne_S k e.symm).elim
  | @app f f' x x' hf hx _ ihx =>
    intro k e
    cases k with
    | zero =>
      have e' : f ⬝ x = S ⬝ S := e
      injection e' with e1 e2
      rw [rel_S hf e1, rel_S hx e2]
      exact ⟨0, rfl, .inl rfl⟩
    | succ k =>
      have e' : f ⬝ x = S ⬝ tower k := e
      injection e' with e1 e2
      obtain ⟨k', ek, hk⟩ := ihx k e2
      rw [rel_S hf e1, ek]
      exact ⟨k' + 1, rfl, towRel_succ hk⟩
  | grad _ hu' _ hl =>
    intro k e
    subst e
    exact base_tower hu' (lvl_base hl)

end

/-- The head of a configuration: both heads are `S`; or a pair of towers with indices `≥ N`,
congruent mod `p`; or a pair that can still be unfolded once (`Lvl (n + 1)`, `n ≥ r`: R2's
invariant I1). -/
def HeadPair (𝔐 : SModel) (N p r : Nat) (h h' : Term) : Prop :=
  (h = S ∧ h' = S) ∨
  (∃ k k', h = tower k ∧ h' = tower k' ∧ N ≤ k ∧ N ≤ k' ∧ k % p = k' % p) ∨
  (∃ n, PureS h ∧ PureS h' ∧ r ≤ n ∧ Lvl 𝔐 N p (n + 1) h h')

/-- A configuration in spine form: related heads applied to pairwise related arguments
(R2's invariant I, with `r ≥ r₁ P` in place of `ρ(P)`). -/
def HR (𝔐 : SModel) (N p r : Nat) (P P' : Term) : Prop :=
  ∃ h h' as as', P = List.foldl Term.app h as ∧ P' = List.foldl Term.app h' as' ∧
    HeadPair 𝔐 N p r h h' ∧ All₂ (Rel 𝔐 N p r) as as'

/-- The conclusion for a configuration: both sides head-reduce to head normal forms of the same
arity whose items have pairwise equal values. -/
def Good (𝔐 : SModel) (P P' : Term) : Prop :=
  ∃ v v', Steps P v ∧ IsHnf v ∧ Steps P' v' ∧ IsHnf v' ∧
    All₂ (fun a a' => 𝔐.val a = 𝔐.val a') (spine v) (spine v')

section
variable {𝔐 : SModel} {N p : Nat}

theorem Good.of_steps {P P' Q Q' : Term} (h : Good 𝔐 Q Q') (s : Steps P Q) (s' : Steps P' Q') :
    Good 𝔐 P P' := by
  obtain ⟨v, v', h1, h2, h3, h4, h5⟩ := h
  exact ⟨v, v', s.trans h1, h2, s'.trans h3, h4, h5⟩

theorem hr_app {r : Nat} {f f' x x' : Term} (h : HR 𝔐 N p r f f') (hx : Rel 𝔐 N p r x x') :
    HR 𝔐 N p r (f ⬝ x) (f' ⬝ x') := by
  obtain ⟨h, h', as, as', rfl, rfl, hh, ha⟩ := h
  exact ⟨h, h', as ++ [x], as' ++ [x'], by rw [List.foldl_append]; rfl,
    by rw [List.foldl_append]; rfl, hh, ha.append (.cons hx .nil)⟩

theorem hr_foldl {r : Nat} {rest rest' : List Term} (ha : All₂ (Rel 𝔐 N p r) rest rest') :
    ∀ {f f' : Term}, HR 𝔐 N p r f f' →
      HR 𝔐 N p r (rest.foldl Term.app f) (rest'.foldl Term.app f') := by
  induction ha with
  | nil => intro f f' h; exact h
  | cons hx _ ih => intro f f' h; exact ih (hr_app h hx)

/-- A related pair with one unit of level to spare may stand at the head. -/
theorem hr_of_rel {r : Nat} {u u' : Term} (h : Rel 𝔐 N p (r + 1) u u') : HR 𝔐 N p r u u' := by
  induction h with
  | atom => exact ⟨S, S, [], [], rfl, rfl, .inl ⟨rfl, rfl⟩, .nil⟩
  | app _ hx ihf _ => exact hr_app ihf (hx.mono (Nat.le_succ r))
  | @grad n u u' hu hu' hn hl =>
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero r)
    | succ m =>
      exact ⟨u, u', [], [], rfl, rfl, .inr (.inr ⟨m, hu, hu', Nat.le_of_succ_le_succ hn, hl⟩),
        .nil⟩

theorem hr_refl {r : Nat} {t : Term} (ht : PureS t) : HR 𝔐 N p r t t := by
  induction ht with
  | S => exact ⟨S, S, [], [], rfl, rfl, .inl ⟨rfl, rfl⟩, .nil⟩
  | app _ hx ihf _ => exact hr_app ihf (Rel.refl hx)

theorem hr_tower {r k k' : Nat} (h : TowRel N p k k') : HR 𝔐 N p r (tower k) (tower k') := by
  rcases h with e | ⟨a, b, c⟩
  · rw [e]; exact hr_refl (tower_pure k')
  · exact ⟨tower k, tower k', [], [], rfl, rfl, .inr (.inl ⟨k, k', rfl, rfl, a, b, c⟩), .nil⟩

/-- R2, case T: both sides are frames of at most two pairwise related items. -/
theorem good_short {r : Nat} {as as' : List Term} (ha : All₂ (Rel 𝔐 N p r) as as')
    (hl : as.length ≤ 2) (hl' : as'.length ≤ 2) :
    Good 𝔐 (as.foldl Term.app S) (as'.foldl Term.app S) := by
  have hP : PureS (as.foldl Term.app S) := pure_foldl as .S (ha.forall_left fun _ _ h => h.pure.1)
  have hP' : PureS (as'.foldl Term.app S) :=
    pure_foldl as' .S (ha.forall_right fun _ _ h => h.pure.2)
  have hsp : spine (as.foldl Term.app S) = as := by rw [spine_foldl]; rfl
  have hsp' : spine (as'.foldl Term.app S) = as' := by rw [spine_foldl]; rfl
  refine ⟨_, _, .refl _, isHnf_of_short hP (by rw [hsp]; exact hl), .refl _,
    isHnf_of_short hP' (by rw [hsp']; exact hl'), ?_⟩
  rw [hsp, hsp']
  exact ha.mono fun _ _ h => h.val_eq

/-- R2, cases T and A: the head is `S` on both sides.  Either the frame has at most two items,
or the head step is taken on both sides; a non-exempt step lowers the bound `r` by one, which
pays for the first item coming to the head; an exempt step brings `S` or a tower to the head. -/
theorem caseS (ℓ : Nat)
    (IH : ∀ ℓ', ℓ' < ℓ → ∀ (r : Nat) (P P' : Term), Run ℓ' P → fold P ≠ 36 → r₁ P ≤ r →
      HR 𝔐 N p r P P' → Good 𝔐 P P')
    {r ℓ₀ : Nat} {as as' : List Term} (hℓ : ℓ₀ ≤ ℓ) (hrun : Run ℓ₀ (as.foldl Term.app S))
    (hb : fold (as.foldl Term.app S) ≠ 36) (hr : r₁ (as.foldl Term.app S) ≤ r)
    (ha : All₂ (Rel 𝔐 N p r) as as') :
    Good 𝔐 (as.foldl Term.app S) (as'.foldl Term.app S) := by
  have hP : PureS (as.foldl Term.app S) := pure_foldl as .S (ha.forall_left fun _ _ h => h.pure.1)
  have hsp : spine (as.foldl Term.app S) = as := by rw [spine_foldl]; rfl
  cases ha with
  | nil => exact good_short (.nil : All₂ (Rel 𝔐 N p r) [] []) (by simp) (by simp)
  | cons h1 ha =>
    cases ha with
    | nil => exact good_short (.cons h1 .nil) (by simp) (by simp)
    | cons h2 ha =>
      cases ha with
      | nil => exact good_short (.cons h1 (.cons h2 .nil)) (by simp) (by simp)
      | @cons u₃ u₃' rest rest' h3 hrest =>
        rename_i u₁ u₁' u₂ u₂'
        obtain ⟨hstep, _, hr1, _, _⟩ := root_step hP hb hsp
        obtain ⟨_, he⟩ := wstep_pure hstep hP
        have s : Step (List.foldl Term.app S (u₁ :: u₂ :: u₃ :: rest))
            (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := step_foldl (.S u₁ u₂ u₃) rest
        have s' : Step (List.foldl Term.app S (u₁' :: u₂' :: u₃' :: rest'))
            (rest'.foldl Term.app (u₁' ⬝ u₃' ⬝ (u₂' ⬝ u₃'))) := step_foldl (.S u₁' u₂' u₃') rest'
        obtain ⟨ℓ₁, e, hrun1⟩ := run_step hrun s
        have hb1 : fold (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) ≠ 36 := by
          rw [he]; exact hb
        have key : ∃ r1, r₁ (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) ≤ r1 ∧
            HR 𝔐 N p r1 (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃)))
              (rest'.foldl Term.app (u₁' ⬝ u₃' ⬝ (u₂' ⬝ u₃'))) := by
          by_cases hex : exempt (fold u₁) = true
          · rw [if_pos hex] at hr1
            refine ⟨r, by omega, ?_⟩
            have hu : HR 𝔐 N p r u₁ u₁' := by
              rcases exempt_shape h1.pure.1 hex with e1 | ⟨k, e1⟩
              · rw [e1, rel_S h1 e1]; exact hr_refl .S
              · obtain ⟨k', e2, hk⟩ := rel_tower h1 _ e1
                rw [e1, e2]; exact hr_tower hk
            exact hr_foldl hrest (hr_app (hr_app hu h3) (.app h2 h3))
          · rw [if_neg hex] at hr1
            obtain ⟨r1, e1⟩ : ∃ r1, r = r1 + 1 := ⟨r - 1, by omega⟩
            subst e1
            refine ⟨r1, by omega, ?_⟩
            have m := Nat.le_succ r1
            exact hr_foldl (hrest.mono fun _ _ h => h.mono m)
              (hr_app (hr_app (hr_of_rel h1) (h3.mono m)) (.app (h2.mono m) (h3.mono m)))
        obtain ⟨r1, hr1', hHR⟩ := key
        exact (IH ℓ₁ (by omega) r1 _ _ hrun1 hb1 hr1' hHR).of_steps (.single s) (.single s')

/-- **The Claim of R2.**  A configuration whose left side has an hnf, with `r₁ P ≤ r`, has head
normal forms of the same arity on both sides with items of pairwise equal value.  Induction on
the length of the head run of `P`.  The cases: head `S` (`caseS`: R2's T and A); a tower pair at
the head (T with at most one argument, else C: the burst `iterS_run`, after which the two
Fibonacci terms are hnf-less, `fib_dead`, with equal values, `Periodic.fib`); an unfoldable pair
at the head (B: head-reduce it to its hnf and replace it by its items, one level lower).  R2's
case D does not arise: an hnf-less head makes `P` hnf-less. -/
theorem core (hper : Periodic 𝔐 N p) : ∀ (ℓ r : Nat) (P P' : Term), Run ℓ P → fold P ≠ 36 →
    r₁ P ≤ r → HR 𝔐 N p r P P' → Good 𝔐 P P' := by
  intro ℓ
  induction ℓ using Nat.strongRecOn with
  | _ ℓ IH =>
    intro r P P' hrun hb hr hHR
    obtain ⟨h, h', as, as', rfl, rfl, hh, ha⟩ := hHR
    have hpa : ∀ a ∈ as, PureS a := ha.forall_left fun _ _ h => h.pure.1
    rcases hh with ⟨rfl, rfl⟩ | ⟨k, k', rfl, rfl, hk, hk', hc⟩ | ⟨n, hu, hu', hn, hl⟩
    · exact caseS ℓ IH (Nat.le_refl _) hrun hb hr ha
    · -- a tower pair at the head
      have hN := hper.hN
      have hP : PureS (as.foldl Term.app (tower k)) := pure_foldl as (tower_pure k) hpa
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
      have hj : 𝔐.val (tower j) = 𝔐.val (tower j') :=
        hper.tow j j' (by omega) (by omega) (mod_pred hper.hp hc)
      cases ha with
      | nil =>
        show Good 𝔐 (S ⬝ tower j) (S ⬝ tower j')
        exact ⟨_, _, .refl _, .inr (.inl ⟨_, rfl⟩), .refl _, .inr (.inl ⟨_, rfl⟩),
          .cons hj .nil⟩
      | @cons x x' as as' hx ha =>
        cases ha with
        | nil =>
          show Good 𝔐 (S ⬝ tower j ⬝ x) (S ⬝ tower j' ⬝ x')
          exact ⟨_, _, .refl _, .inr (.inr ⟨_, _, rfl⟩), .refl _, .inr (.inr ⟨_, _, rfl⟩),
            .cons hj (.cons hx.val_eq .nil)⟩
        | @cons y y' rest rest' hy hrest =>
          have px := hx.pure; have py := hy.pure
          have st : Steps (List.foldl Term.app (tower (j + 1)) (x :: y :: rest))
              (List.foldl Term.app S
                (S :: (fibT (j + 1) (x, y)).1 :: (fibT (j + 1) (x, y)).2 :: rest)) :=
            steps_foldl (iterS_run (j + 1) (S ⬝ S) x y) rest
          have st' : Steps (List.foldl Term.app (tower (j' + 1)) (x' :: y' :: rest'))
              (List.foldl Term.app S
                (S :: (fibT (j' + 1) (x', y')).1 :: (fibT (j' + 1) (x', y')).2 :: rest')) :=
            steps_foldl (iterS_run (j' + 1) (S ⬝ S) x' y') rest'
          obtain ⟨i, ei⟩ : ∃ i, j + 1 = i + 8 := ⟨j + 1 - 8, by omega⟩
          have hdead := fib_dead i px.1 py.1
          rw [← ei] at hdead
          have pf := fibT_pure (j + 1) px.1 py.1
          have pf' := fibT_pure (j' + 1) px.2 py.2
          have ev : (𝔐.val (fibT (j + 1) (x, y)).1, 𝔐.val (fibT (j + 1) (x, y)).2) =
              (𝔐.val (fibT (j' + 1) (x', y')).1, 𝔐.val (fibT (j' + 1) (x', y')).2) := by
            rw [val_fibT, val_fibT, hx.val_eq, hy.val_eq]
            exact hper.fib (j + 1) (j' + 1) (by omega) (by omega) hc _
          have hall : All₂ (Rel 𝔐 N p r)
              (S :: (fibT (j + 1) (x, y)).1 :: (fibT (j + 1) (x, y)).2 :: rest)
              (S :: (fibT (j' + 1) (x', y')).1 :: (fibT (j' + 1) (x', y')).2 :: rest') :=
            .cons .atom
              (.cons (.grad pf.1 pf'.1 (Nat.le_refl r) (lvl_dead r pf.1 hdead.1
                  (congrArg Prod.fst ev)))
                (.cons (.grad pf.2 pf'.2 (Nat.le_refl r) (lvl_dead r pf.2 hdead.2
                  (congrArg Prod.snd ev))) hrest))
          obtain ⟨ℓ₁, hle, hrun1⟩ := run_steps st hrun
          have hr1 := Nat.le_trans (r1_steps st hP hb) hr
          have hb1 : fold (List.foldl Term.app S
              (S :: (fibT (j + 1) (x, y)).1 :: (fibT (j + 1) (x, y)).2 :: rest)) ≠ 36 := by
            rw [steps_fold hP st]; exact hb
          exact (caseS ℓ IH hle hrun1 hb1 hr1 hall).of_steps st st'
    · -- an unfoldable pair at the head
      have hP : PureS (as.foldl Term.app h) := pure_foldl as hu hpa
      have hbu : fold h ≠ 36 := fun e => hb (fold_foldl_bot as e hpa)
      have hbu' : fold h' ≠ 36 := by
        rw [← fold_eq_of_val 𝔐 hu hu' (lvl_base hl).1]; exact hbu
      obtain ⟨v, hv, hvn⟩ := head_hnf hu hbu
      obtain ⟨v', hv', hvn'⟩ := head_hnf hu' hbu'
      have hit : All₂ (Lvl 𝔐 N p n) (spine v) (spine v') := hl.2 v v' hv hvn hv' hvn'
      have pv := steps_pure hu hv
      have pv' := steps_pure hu' hv'
      have st : Steps (as.foldl Term.app h) (List.foldl Term.app S (spine v ++ as)) := by
        rw [List.foldl_append, ← pure_eq_foldl pv]; exact steps_foldl hv as
      have st' : Steps (as'.foldl Term.app h') (List.foldl Term.app S (spine v' ++ as')) := by
        rw [List.foldl_append, ← pure_eq_foldl pv']; exact steps_foldl hv' as'
      have hall : All₂ (Rel 𝔐 N p r) (spine v ++ as) (spine v' ++ as') :=
        (hit.mono_mem fun a b ha hb hab =>
          .grad (spine_pure pv a ha) (spine_pure pv' b hb) hn hab).append ha
      obtain ⟨ℓ₁, hle, hrun1⟩ := run_steps st hrun
      have hr1 := Nat.le_trans (r1_steps st hP hb) hr
      have hb1 : fold (List.foldl Term.app S (spine v ++ as)) ≠ 36 := by
        rw [steps_fold hP st]; exact hb
      exact (caseS ℓ IH hle hrun1 hb1 hr1 hall).of_steps st st'

/-- R2, start: filling the holes of a context with related terms gives a configuration. -/
theorem rel_plug {r n : Nat} {t t' : Term} (ht : PureS t) (ht' : PureS t') (hn : r ≤ n)
    (h : Lvl 𝔐 N p n t t') : ∀ C : Ctx, Rel 𝔐 N p r (C.plug t) (C.plug t') := by
  intro C
  induction C with
  | hole => exact .grad ht ht' hn h
  | s => exact .atom
  | app _ _ ihc ihd => exact .app ihc ihd

end

/-! ## The observable is a function -/

theorem obs_total (𝔐 : SModel) {t : Term} (ht : PureS t) : ∃ o, Obs 𝔐 t o := by
  by_cases hb : fold t = 36
  · exact ⟨none, no_hnf_of_bot ht hb⟩
  · obtain ⟨v, hs, hv⟩ := head_hnf ht hb
    exact ⟨some _, v, hs, hv, rfl⟩

theorem obs_unique (𝔐 : SModel) {t : Term} {o o' : Option (List 𝔐.M)} (h : Obs 𝔐 t o)
    (h' : Obs 𝔐 t o') : o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some l' =>
      obtain ⟨v, hs, hv, _⟩ := h'
      exact (h ⟨v, hs.weak, hv⟩).elim
  | some l =>
    obtain ⟨v, hs, hv, e⟩ := h
    cases o' with
    | none => exact (h' ⟨v, hs.weak, hv⟩).elim
    | some l' =>
      obtain ⟨v', hs', hv', e'⟩ := h'
      rw [e, e', hnf_unique hs hv hs' hv']

/-- One direction of the conclusion, from the Claim. -/
theorem obs_transfer (𝔐 : SModel) {P P' : Term} (hP : PureS P) (hP' : PureS P')
    (hv : 𝔐.val P = 𝔐.val P') (hg : fold P ≠ 36 → Good 𝔐 P P') (o : Option (List 𝔐.M))
    (h : Obs 𝔐 P o) : Obs 𝔐 P' o := by
  cases o with
  | none =>
    intro hh'
    have hb' : fold P' ≠ 36 := fun e => no_hnf_of_bot hP' e hh'
    exact h (sound P hP (by rw [fold_eq_of_val 𝔐 hP hP' hv]; exact hb'))
  | some l =>
    obtain ⟨v, hs, hn, e⟩ := h
    have hb : fold P ≠ 36 := by
      rw [← steps_fold hP hs]; exact fold_hnf (steps_pure hP hs) hn
    obtain ⟨w, w', h1, h2, h3, h4, h5⟩ := hg hb
    have ew := hnf_unique hs hn h1 h2
    refine ⟨w', h3, h4, ?_⟩
    rw [e, ew]
    exact h5.map_eq

/-! ## Theorem Φ -/

/-- **The invariant-preservation form** (R2's Claim at the start configuration): if `t ≃₁₀ t'`
and `C[t]` has an hnf, then `C[t]`, `C[t']` head-reduce to head normal forms of the same arity
with items of pairwise equal value. -/
theorem good_of_sim (𝔐 : SModel) {N p : Nat} (hper : Periodic 𝔐 N p) {t t' : Term}
    (ht : PureS t) (ht' : PureS t') (h : Sim 𝔐 N p 10 t t') (C : Ctx)
    (hb : fold (C.plug t) ≠ 36) : Good 𝔐 (C.plug t) (C.plug t') := by
  have hrel : Rel 𝔐 N p 11 (C.plug t) (C.plug t') := rel_plug ht ht' (Nat.le_refl 11) h C
  have hP := hrel.pure.1
  obtain ⟨v, hs, hv⟩ := head_hnf hP hb
  obtain ⟨ℓ, hrun⟩ := run_of_steps hs hv
  exact core hper ℓ 10 _ _ hrun hb (r1_le hP hb) (hr_of_rel hrel)

/-- **Theorem Φ** (R1).  If `t ≃₁₀ t'` then `O_Φ(C[t]) = O_Φ(C[t'])` for every context `C`. -/
theorem theorem_phi (𝔐 : SModel) {N p : Nat} (hper : Periodic 𝔐 N p) {t t' : Term}
    (ht : PureS t) (ht' : PureS t') (h : Sim 𝔐 N p 10 t t') (C : Ctx)
    (o : Option (List 𝔐.M)) : Obs 𝔐 (C.plug t) o ↔ Obs 𝔐 (C.plug t') o := by
  have hrel : Rel 𝔐 N p 11 (C.plug t) (C.plug t') := rel_plug ht ht' (Nat.le_refl 11) h C
  have hP := hrel.pure.1
  have hP' := hrel.pure.2
  have fwd : ∀ o, Obs 𝔐 (C.plug t) o → Obs 𝔐 (C.plug t') o :=
    obs_transfer 𝔐 hP hP' hrel.val_eq (good_of_sim 𝔐 hper ht ht' h C)
  constructor
  · exact fwd o
  · intro h'
    obtain ⟨o₂, h₂⟩ := obs_total 𝔐 hP
    rw [obs_unique 𝔐 h' (fwd o₂ h₂)]
    exact h₂

/-! ## Sanity: the hypotheses are satisfiable -/

/-- `≃_g` is reflexive on pure terms, so the hypothesis of Theorem Φ is not vacuous. -/
theorem lvl_refl (𝔐 : SModel) (N p : Nat) : ∀ (n : Nat) {t : Term}, PureS t →
    Lvl 𝔐 N p n t t := by
  intro n
  induction n with
  | zero => intro t _; exact ⟨rfl, fun k k' e e' => .inl (tower_inj (e.symm.trans e'))⟩
  | succ n ih =>
    intro t ht
    refine ⟨⟨rfl, fun k k' e e' => .inl (tower_inj (e.symm.trans e'))⟩, fun v v' hs hv hs' hv' => ?_⟩
    rw [← hnf_unique hs hv hs' hv']
    have hp := spine_pure (steps_pure ht hs)
    generalize spine v = l at hp
    induction l with
    | nil => exact .nil
    | cons a l ihl => exact .cons (ih (hp a (by simp))) (ihl fun b hb => hp b (by simp [hb]))

/-- S1 itself: the 38-block table as a model over itself. -/
def s1Model : SModel where
  M := Fin 38
  app a b := ⟨β a.1 b.1, β_lt a.2 b.2⟩
  s := ⟨0, by decide⟩
  law a b c := Fin.eq_of_val_eq (compat a.2 b.2 c.2)
  φ a := a.1
  φ_s := rfl
  φ_app _ _ := rfl

theorem fibB_dead (j : Nat) {a b : Nat} (ha : a < 38) (hb : b < 38) :
    fibB (j + 8) (a, b) = (36, 36) := by
  have h8 := fib8B_eq
  simp only [fib8B, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h8
  rw [Nat.add_comm, fibB_add, h8 _ ha _ hb, fibB_bot]

theorem s1_fib : ∀ (k : Nat) (q : Fin 38 × Fin 38),
    ((s1Model.fibM k q).1.1, (s1Model.fibM k q).2.1) = fibB k (q.1.1, q.2.1) := by
  intro k
  induction k with
  | zero => intro q; rfl
  | succ k ih => intro q; exact ih (q.2, s1Model.app q.1 q.2)

def tower4B : Bool := fold (tower 4) == 17 && β 0 17 == 17
theorem tower4B_eq : tower4B = true := by decide +kernel

theorem fold_tower_ge4 : ∀ j : Nat, fold (tower (j + 4)) = 17 := by
  have h := tower4B_eq
  simp only [tower4B, Bool.and_eq_true, beq_iff_eq] at h
  intro j
  induction j with
  | zero => exact h.1
  | succ j ih => show β 0 (fold (tower (j + 4))) = 17; rw [ih]; exact h.2

/-- **S1 satisfies the hypotheses with `N = 10`, `p = 1`**: its Fibonacci map is constant
`(⊥, ⊥)` from time 8 (`fib8B_eq`, by `decide +kernel`), and its towers have block 17 from
`k = 4` (`tower4B_eq`). -/
theorem s1_periodic : Periodic s1Model 10 1 := by
  have dead : ∀ (k : Nat), 9 ≤ k → ∀ q : Fin 38 × Fin 38,
      ((s1Model.fibM k q).1.1, (s1Model.fibM k q).2.1) = (36, 36) := by
    intro k hk q
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
    rw [s1_fib, fibB_dead j q.1.2 q.2.2]
  have tw : ∀ (k : Nat), 9 ≤ k → (s1Model.val (tower k)).1 = 17 := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    exact (fold_val s1Model (tower_pure (j + 4))).trans (fold_tower_ge4 j)
  refine ⟨by decide, by decide, fun k k' hk hk' _ q => ?_, fun k k' hk hk' _ => ?_⟩
  · have e := dead k hk q
    have e' := dead k' hk' q
    exact Prod.ext (Fin.eq_of_val_eq ((congrArg Prod.fst e).trans (congrArg Prod.fst e').symm))
      (Fin.eq_of_val_eq ((congrArg Prod.snd e).trans (congrArg Prod.snd e').symm))
  · exact Fin.eq_of_val_eq ((tw k hk).trans (tw k' hk').symm)

/-- Theorem Φ for S1's own labels, with `N = 10`, `p = 1`. -/
theorem theorem_phi_s1 {t t' : Term} (ht : PureS t) (ht' : PureS t')
    (h : Sim s1Model 10 1 10 t t') (C : Ctx) (o : Option (List (Fin 38))) :
    Obs s1Model (C.plug t) o ↔ Obs s1Model (C.plug t') o :=
  theorem_phi s1Model s1_periodic ht ht' h C o

end Phi
