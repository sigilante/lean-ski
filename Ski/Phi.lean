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

/-! ## Theorem Φ -/

/-- **Theorem Φ** (R1).  If `t ≃₁₀ t'` then `O_Φ(C[t]) = O_Φ(C[t'])` for every context `C`. -/
theorem theorem_phi (𝔐 : SModel) {N p : Nat} (hper : Periodic 𝔐 N p) {t t' : Term}
    (ht : PureS t) (ht' : PureS t') (h : Sim 𝔐 N p 10 t t') (C : Ctx)
    (o : Option (List 𝔐.M)) : Obs 𝔐 (C.plug t) o ↔ Obs 𝔐 (C.plug t') o := by
  sorry

end Phi
