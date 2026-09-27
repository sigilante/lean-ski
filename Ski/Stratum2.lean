import Ski.Stratum
import Ski.Bridge

/-!
# Stratum 2: contraction normalizes, with no elementary bound

The paper's second stratum is typed realizers with contraction, in which a
binder may occur twice under the additive count.  They are strongly
normalizing (`strong_normalization`, `Ski/Tait.lean`), and a closed one
compiles to a converging `SKI` term (`compiled_converges`,
`Ski/Bridge.lean`).  This file proves the rest of the claim: no elementary
function of a realizer's size bounds its evaluation.

**The family.**  `two = λ f x. f (f x)` uses `f` twice: it is contraction.
The tower `towerT k = two two ⋯ two`, with `k + 1` copies associated to the
left, is the Church numeral `2↑↑(k+1)` at a type that falls one level per
copy.  Applied to a Boolean toggle and a Boolean, it computes the toggle's
`2↑↑(k+1)`-fold iterate.  Its additive size is linear in `k` (`asz_evalT`),
and it is typed (`evalT_typed`).

**The lower bound** (`evalT_lower`): every call-by-name reduction of
`evalT k` to an injection takes at least `2↑↑(k+1)` steps.  The proof is a
lower-bound logical relation `LB`, indexed by descriptors: a number at
`Bool`, a function on descriptors at an arrow.  It is closed under backward
steps, because call-by-name reduction is deterministic (`WH.det`).  The
toggle costs one case per use (`LB_tog`), and `two` composes its argument's
descriptor with itself (`LB_two`).  So the tower's descriptor is the
`2↑↑(k+1)`-fold iterate (`LB_towerT`).

**The bound is not vacuous** (`evalT_terminates`).  `evalT k` does reduce to
an injection, by strong normalization and canonical forms.

**No elementary bound** (`no_elementary_bound`): for every height `j` of
exponentials and every constant `c`, some member of the family takes more
steps than `exp_j (c · size)`.
-/

namespace Rz

open Tm

variable {γ : Type}

-- ---------------------------------------------------------------------------
-- Call-by-name reduction is deterministic
-- ---------------------------------------------------------------------------

theorem WH.no_lam {b u : Tm γ} (h : WH (.lam b) u) : False := by cases h
theorem WH.no_pair {a b u : Tm γ} (h : WH (.pair a b) u) : False := by cases h
theorem WH.no_inl {a u : Tm γ} (h : WH (.inl a) u) : False := by cases h
theorem WH.no_inr {b u : Tm γ} (h : WH (.inr b) u) : False := by cases h

/-- **Call-by-name reduction is deterministic.** -/
theorem WH.det {t u v : Tm γ} (h₁ : WH t u) (h₂ : WH t v) : u = v := by
  induction h₁ generalizing v with
  | beta b a =>
    cases h₂ with
    | beta => rfl
    | appL _ h => exact (h.no_lam).elim
  | fstβ a b =>
    cases h₂ with
    | fstβ => rfl
    | fst h => exact (h.no_pair).elim
  | sndβ a b =>
    cases h₂ with
    | sndβ => rfl
    | snd h => exact (h.no_pair).elim
  | inlβ a f g =>
    cases h₂ with
    | inlβ => rfl
    | caseS _ _ h => exact (h.no_inl).elim
  | inrβ b f g =>
    cases h₂ with
    | inrβ => rfl
    | caseS _ _ h => exact (h.no_inr).elim
  | appL a h ih =>
    cases h₂ with
    | beta => exact (h.no_lam).elim
    | appL _ h' => rw [ih h']
  | fst h ih =>
    cases h₂ with
    | fstβ => exact (h.no_pair).elim
    | fst h' => rw [ih h']
  | snd h ih =>
    cases h₂ with
    | sndβ => exact (h.no_pair).elim
    | snd h' => rw [ih h']
  | caseS f g h ih =>
    cases h₂ with
    | inlβ => exact (h.no_inl).elim
    | inrβ => exact (h.no_inr).elim
    | caseS _ _ h' => rw [ih h']

/-- An injection. -/
def IsInj (v : Tm γ) : Prop := ∃ a, v = .inl a ∨ v = .inr a

theorem IsInj.no_step {v u : Tm γ} (hv : IsInj v) (h : WH v u) : False := by
  cases hv with
  | intro a ha =>
    cases ha with
    | inl e => rw [e] at h; exact h.no_inl
    | inr e => rw [e] at h; exact h.no_inr

/-- To reach an injection, a case first brings its scrutinee to one. -/
theorem case_dec : ∀ {n : Nat} {s f g v : Tm γ}, WHN n (.case s f g) v → IsInj v →
    ∃ n₁ s', n₁ < n ∧ WHN n₁ s s' ∧ IsInj s'
  | 0, s, f, g, v, h, hv => by
    cases h
    cases hv with
    | intro a ha => cases ha with
      | inl e => cases e
      | inr e => cases e
  | n + 1, s, f, g, v, h, hv => by
    cases h with
    | step s1 rest =>
      cases s1 with
      | inlβ a _ _ => exact ⟨0, .inl a, Nat.zero_lt_succ n, .refl _, a, .inl rfl⟩
      | inrβ b _ _ => exact ⟨0, .inr b, Nat.zero_lt_succ n, .refl _, b, .inr rfl⟩
      | caseS _ _ hs =>
        cases case_dec rest hv with
        | intro n₁ h' => cases h' with
          | intro s' h' => exact ⟨n₁ + 1, s', by omega, .step hs h'.2.1, h'.2.2⟩

-- ---------------------------------------------------------------------------
-- The lower-bound relation
-- ---------------------------------------------------------------------------

/-- Types built from `Bool`. -/
inductive BT where
  | bool
  | arr (A B : BT)

/-- Descriptors: a step count at `Bool`, a function on descriptors at an arrow. -/
@[reducible] def Desc : BT → Type
  | .bool => Nat
  | .arr A B => Desc A → Desc B

/-- `LB A u d`: `u` behaves at `A` at least as slowly as `d`.  At `Bool`,
    every reduction to an injection takes at least `d` steps. -/
def LB : (A : BT) → Tm γ → Desc A → Prop
  | .bool, u, m => ∀ n v, WHN n u v → IsInj v → m ≤ n
  | .arr A B, F, E => ∀ u d, LB A u d → LB B (.app F u) (E d)

/-- **Backward closure**: a step before a slow term keeps it slow. -/
theorem LB.back : ∀ (A : BT) {t t' : Tm γ} {d : Desc A}, WH t t' → LB A t' d → LB A t d
  | .bool, t, t', m, s, h => by
    intro n v hn hv
    cases hn with
    | refl => exact (hv.no_step s).elim
    | step s1 rest =>
      rw [WH.det s1 s] at rest
      exact Nat.le_succ_of_le (h _ v rest hv)
  | .arr _ B, _, _, _, s, h => fun u d hu => LB.back B (.appL u s) (h u d hu)

theorem LB.backN (A : BT) {t t' : Tm γ} {d : Desc A} {k : Nat} (s : WHN k t t') (h : LB A t' d) :
    LB A t d := by
  induction s with
  | refl => exact h
  | step s1 _ ih => exact LB.back A s1 (ih h)

/-- A case is slower than its scrutinee by one step. -/
theorem LB_case {s f g : Tm γ} {m : Nat} (h : LB .bool s m) : LB .bool (.case s f g) (m + 1) := by
  intro n v hn hv
  cases case_dec hn hv with
  | intro n₁ h' => cases h' with
    | intro s' h' => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (h n₁ s' h'.2.1 h'.2.2) h'.1)

-- ---------------------------------------------------------------------------
-- The toggle and the numeral two
-- ---------------------------------------------------------------------------

/-- The toggle `λ b. case b (λ a. inr a) (λ a. inl a)`. -/
def togT : Tm γ := .lam (.case (.var 0) (.lam (.inr (.var 0))) (.lam (.inl (.var 0))))

/-- Each use of the toggle takes a case. -/
theorem LB_tog : LB (γ := γ) (.arr .bool .bool) togT (fun m => m + 1) := by
  intro u m hu
  exact LB.back .bool (.beta _ u) (LB_case hu)

/-- `two = λ f x. f (f x)`: the variable `f` occurs twice. -/
def twoT : Tm γ := .lam (.lam (.app (.var 1) (.app (.var 1) (.var 0))))

theorem sub_beta1_shift (u h : Tm γ) : sub (beta1 u) (ren Nat.succ h) = h := by
  rw [sub_ren]
  exact sub_var h

/-- `two` composes its argument's descriptor with itself. -/
theorem LB_two (A : BT) :
    LB (γ := γ) (.arr (.arr A A) (.arr A A)) twoT (fun f d => f (f d)) := by
  intro h f hh u d hu
  have s1 : WH (Tm.app (Tm.app twoT h) u)
      (.app (.lam (.app (ren Nat.succ h) (.app (ren Nat.succ h) (.var 0)))) u) :=
    .appL u (.beta _ h)
  have s2 : WH (Tm.app (.lam (.app (ren Nat.succ h) (.app (ren Nat.succ h) (.var 0)))) u)
      (.app h (.app h u)) := by
    have := WH.beta (.app (ren Nat.succ h) (.app (ren Nat.succ h) (.var 0))) u
    simp only [sub, sub_beta1_shift] at this
    exact this
  exact LB.back A s1 (LB.back A s2 (hh _ _ (hh u d hu)))

-- ---------------------------------------------------------------------------
-- The tower
-- ---------------------------------------------------------------------------

/-- `f` iterated `n` times. -/
def iterN {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => f (iterN f n a)

theorem iterN_succ' {α : Type} (f : α → α) : ∀ (m : Nat) (x : α), iterN f m (f x) = f (iterN f m x)
  | 0, _ => rfl
  | m + 1, x => by show f (iterN f m (f x)) = f (f (iterN f m x)); rw [iterN_succ' f m x]

theorem iterN_add {α : Type} (f : α → α) (m : Nat) : ∀ n a, iterN f (m + n) a = iterN f m (iterN f n a)
  | 0, _ => rfl
  | n + 1, a => by
    show f (iterN f (m + n) a) = iterN f m (f (iterN f n a))
    rw [iterN_add f m n a, iterN_succ']

/-- Squaring a function iterates it `2^n` times after `n` squarings. -/
theorem iterN_sq {α : Type} : ∀ (n : Nat) (f : α → α) (a : α),
    iterN (fun (g : α → α) (x : α) => g (g x)) n f a = iterN f (2 ^ n) a
  | 0, f, a => rfl
  | n + 1, f, a => by
    show (fun x => iterN (fun (g : α → α) (x : α) => g (g x)) n f
      (iterN (fun (g : α → α) (x : α) => g (g x)) n f x)) a = _
    simp only [iterN_sq n f]
    rw [← iterN_add, Nat.pow_succ, Nat.mul_two]

/-- The tower `2↑↑k`: `tw 0 = 1`, `tw (k + 1) = 2 ^ tw k`. -/
def tw : Nat → Nat
  | 0 => 1
  | k + 1 => 2 ^ tw k

/-- `two two ⋯ two`, `k + 1` copies, associated to the left. -/
def towerT : Nat → Tm γ
  | 0 => twoT
  | k + 1 => .app (towerT k) twoT

/-- The Church type `(A ⇒ A) ⇒ A ⇒ A`. -/
def NT (A : BT) : BT := .arr (.arr A A) (.arr A A)

/-- **The tower's descriptor** is the `2↑↑(k+1)`-fold iterate. -/
theorem LB_towerT : ∀ (k : Nat) (A : BT),
    LB (γ := γ) (NT A) (towerT k) (fun f => iterN f (tw (k + 1)))
  | 0, A => by
    have e : (fun (f : Desc (.arr A A)) => iterN f (tw 1)) = fun f d => f (f d) := by
      funext f d; rfl
    show LB (NT A) twoT (fun f => iterN f (tw 1))
    rw [e]
    exact LB_two A
  | k + 1, A => by
    have ih := LB_towerT k (.arr A A)
    have h := ih twoT (fun f d => f (f d)) (LB_two A)
    have e : (fun (f : Desc (.arr A A)) => iterN f (tw (k + 2))) =
        iterN (fun (g : Desc (.arr A A)) (x : Desc A) => g (g x)) (tw (k + 1)) := by
      funext f d
      rw [iterN_sq]
      rfl
    show LB (NT A) (.app (towerT k) twoT) _
    rw [e]
    exact h

theorem iterN_succ_zero : ∀ n : Nat, iterN (fun m => m + 1) n 0 = n
  | 0 => rfl
  | n + 1 => by show iterN (fun m => m + 1) n 0 + 1 = n + 1; rw [iterN_succ_zero n]

/-- The tower applied to the toggle and a Boolean. -/
def evalT (k : Nat) (b : Tm γ) : Tm γ := .app (.app (towerT k) togT) b

/-- **The lower bound**: every call-by-name reduction of the tower, applied
    to the toggle and an injection, to an injection takes at least
    `2↑↑(k+1)` steps. -/
theorem evalT_lower (k : Nat) (a : Tm γ) {n : Nat} {v : Tm γ}
    (h : WHN n (evalT k (.inl a)) v) (hv : IsInj v) : tw (k + 1) ≤ n := by
  have hb : LB (γ := γ) .bool (.inl a) 0 := fun _ _ _ _ => Nat.zero_le _
  have := LB_towerT (γ := γ) k .bool togT (fun m => m + 1) LB_tog (.inl a) 0 hb n v h hv
  dsimp only at this
  rw [iterN_succ_zero] at this
  exact this

-- ---------------------------------------------------------------------------
-- The family is typed, and linear in size
-- ---------------------------------------------------------------------------

/-- `Bool`, as `W + W` over one base type. -/
def boolTy : Ty Unit := .sum (.base ()) (.base ())

/-- The realizer type of a `Bool`-type. -/
def BT.ty : BT → Ty Unit
  | .bool => boolTy
  | .arr A B => .arr A.ty B.ty

/-- The one constant, a witness of the base type. -/
def sigU : Unit → Ty Unit := fun _ => .base ()

theorem twoT_typed (Γ : Nat → Ty Unit) (A : BT) :
    Typed sigU Γ (twoT : Tm Unit) (NT A).ty :=
  .lam (.lam (.app (.var _ 1) (.app (.var _ 1) (.var _ 0))))

theorem togT_typed (Γ : Nat → Ty Unit) : Typed sigU Γ (togT : Tm Unit) (BT.arr .bool .bool).ty :=
  .lam (.case (.var _ 0) (.lam (.inr (.var _ 0))) (.lam (.inl (.var _ 0))))

theorem towerT_typed (Γ : Nat → Ty Unit) : ∀ (k : Nat) (A : BT),
    Typed sigU Γ (towerT k : Tm Unit) (NT A).ty
  | 0, A => twoT_typed Γ A
  | k + 1, A => .app (towerT_typed Γ k (.arr A A)) (twoT_typed Γ A)

/-- `inl c`, a Boolean. -/
def trueT : Tm Unit := .inl (.const ())

/-- **The family is typed**: `evalT k trueT : Bool`. -/
theorem evalT_typed (Γ : Nat → Ty Unit) (k : Nat) : Typed sigU Γ (evalT k trueT) boolTy :=
  .app (.app (towerT_typed Γ k .bool) (togT_typed Γ)) (.inl (.const _ ()))

theorem asz_towerT : ∀ k : Nat, asz (towerT k : Tm γ) = 8 * k + 7
  | 0 => rfl
  | k + 1 => by show asz (towerT k : Tm γ) + 7 + 1 = _; rw [asz_towerT k]; omega

/-- **The family is linear in size**: additive size `8k + 17`. -/
theorem asz_evalT (k : Nat) : asz (evalT k trueT) = 8 * k + 17 := by
  show asz (towerT k : Tm Unit) + 6 + 1 + 2 + 1 = _
  rw [asz_towerT]

-- ---------------------------------------------------------------------------
-- The family terminates: subject reduction, canonical forms, strong normalization
-- ---------------------------------------------------------------------------

section Termination

variable {β : Type} {sig : γ → Ty β}

theorem Typed.ren {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β} (h : Typed sig Γ t A) :
    ∀ {Δ : Nat → Ty β} {ξ : Nat → Nat}, (∀ i, Δ (ξ i) = Γ i) → Typed sig Δ (ren ξ t) A := by
  induction h with
  | var Γ n => intro Δ ξ hξ; rw [← hξ n]; exact .var _ _
  | const Γ c => intro Δ ξ _; exact .const _ _
  | lam _ ih =>
    intro Δ ξ hξ
    refine .lam (ih fun i => ?_)
    cases i with
    | zero => rfl
    | succ i => exact hξ i
  | app _ _ ihf iha => intro Δ ξ hξ; exact .app (ihf hξ) (iha hξ)
  | pair _ _ iha ihb => intro Δ ξ hξ; exact .pair (iha hξ) (ihb hξ)
  | fst _ ih => intro Δ ξ hξ; exact .fst (ih hξ)
  | snd _ ih => intro Δ ξ hξ; exact .snd (ih hξ)
  | inl _ ih => intro Δ ξ hξ; exact .inl (ih hξ)
  | inr _ ih => intro Δ ξ hξ; exact .inr (ih hξ)
  | case _ _ _ ihs ihf ihg => intro Δ ξ hξ; exact .case (ihs hξ) (ihf hξ) (ihg hξ)

theorem Typed.sub {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β} (h : Typed sig Γ t A) :
    ∀ {Δ : Nat → Ty β} {σ : Nat → Tm γ}, (∀ i, Typed sig Δ (σ i) (Γ i)) →
      Typed sig Δ (Tm.sub σ t) A := by
  induction h with
  | var Γ n => intro Δ σ hσ; exact hσ n
  | const Γ c => intro Δ σ _; exact .const _ _
  | @lam Γ A B b _ ih =>
    intro Δ σ hσ
    refine .lam (ih fun i => ?_)
    cases i with
    | zero => exact .var _ 0
    | succ i => exact (hσ i).ren (fun _ => rfl)
  | app _ _ ihf iha => intro Δ σ hσ; exact .app (ihf hσ) (iha hσ)
  | pair _ _ iha ihb => intro Δ σ hσ; exact .pair (iha hσ) (ihb hσ)
  | fst _ ih => intro Δ σ hσ; exact .fst (ih hσ)
  | snd _ ih => intro Δ σ hσ; exact .snd (ih hσ)
  | inl _ ih => intro Δ σ hσ; exact .inl (ih hσ)
  | inr _ ih => intro Δ σ hσ; exact .inr (ih hσ)
  | case _ _ _ ihs ihf ihg => intro Δ σ hσ; exact .case (ihs hσ) (ihf hσ) (ihg hσ)

/-- **Subject reduction.** -/
theorem WH.typed {t t' : Tm γ} (s : WH t t') :
    ∀ {Γ : Nat → Ty β} {A : Ty β}, Typed sig Γ t A → Typed sig Γ t' A := by
  induction s with
  | beta b a =>
    intro Γ A h
    cases h with
    | app hf ha =>
      cases hf with
      | lam hb =>
        refine hb.sub fun i => ?_
        cases i with
        | zero => exact ha
        | succ i => exact .var _ i
  | fstβ a b => intro Γ A h; cases h with | fst hp => cases hp with | pair ha _ => exact ha
  | sndβ a b => intro Γ A h; cases h with | snd hp => cases hp with | pair _ hb => exact hb
  | inlβ a f g =>
    intro Γ A h
    cases h with
    | case hs hf _ => cases hs with | inl ha => exact .app hf ha
  | inrβ b f g =>
    intro Γ A h
    cases h with
    | case hs _ hg => cases hs with | inr hb => exact .app hg hb
  | appL a _ ih => intro Γ A h; cases h with | app hf ha => exact .app (ih hf) ha
  | fst _ ih => intro Γ A h; cases h with | fst ht => exact .fst (ih ht)
  | snd _ ih => intro Γ A h; cases h with | snd ht => exact .snd (ih ht)
  | caseS f g _ ih => intro Γ A h; cases h with | case hs hf hg => exact .case (ih hs) hf hg

theorem closedAt_ren : ∀ (t : Tm γ) (d e : Nat) (ξ : Nat → Nat), closedAt d t →
    (∀ i, i < d → ξ i < e) → closedAt e (ren ξ t)
  | .var i, _, _, _, h, hξ => hξ i h
  | .const _, _, _, _, _, _ => trivial
  | .app f a, d, e, ξ, h, hξ => ⟨closedAt_ren f d e ξ h.1 hξ, closedAt_ren a d e ξ h.2 hξ⟩
  | .lam b, d, e, ξ, h, hξ => by
    refine closedAt_ren b (d + 1) (e + 1) (upr ξ) h fun i hi => ?_
    cases i with
    | zero => exact Nat.zero_lt_succ e
    | succ i => show ξ i + 1 < e + 1; have := hξ i (by omega); omega
  | .pair a b, d, e, ξ, h, hξ => ⟨closedAt_ren a d e ξ h.1 hξ, closedAt_ren b d e ξ h.2 hξ⟩
  | .fst t, d, e, ξ, h, hξ => closedAt_ren t d e ξ h hξ
  | .snd t, d, e, ξ, h, hξ => closedAt_ren t d e ξ h hξ
  | .inl a, d, e, ξ, h, hξ => closedAt_ren a d e ξ h hξ
  | .inr b, d, e, ξ, h, hξ => closedAt_ren b d e ξ h hξ
  | .case s f g, d, e, ξ, h, hξ =>
    ⟨closedAt_ren s d e ξ h.1 hξ, closedAt_ren f d e ξ h.2.1 hξ, closedAt_ren g d e ξ h.2.2 hξ⟩

theorem closedAt_sub : ∀ (t : Tm γ) (d e : Nat) (σ : Nat → Tm γ), closedAt d t →
    (∀ i, i < d → closedAt e (σ i)) → closedAt e (Tm.sub σ t)
  | .var i, _, _, _, h, hσ => hσ i h
  | .const _, _, _, _, _, _ => trivial
  | .app f a, d, e, σ, h, hσ => ⟨closedAt_sub f d e σ h.1 hσ, closedAt_sub a d e σ h.2 hσ⟩
  | .lam b, d, e, σ, h, hσ => by
    refine closedAt_sub b (d + 1) (e + 1) (up σ) h fun i hi => ?_
    cases i with
    | zero => exact Nat.zero_lt_succ e
    | succ i =>
      exact closedAt_ren (σ i) e (e + 1) Nat.succ (hσ i (by omega)) fun j hj => by omega
  | .pair a b, d, e, σ, h, hσ => ⟨closedAt_sub a d e σ h.1 hσ, closedAt_sub b d e σ h.2 hσ⟩
  | .fst t, d, e, σ, h, hσ => closedAt_sub t d e σ h hσ
  | .snd t, d, e, σ, h, hσ => closedAt_sub t d e σ h hσ
  | .inl a, d, e, σ, h, hσ => closedAt_sub a d e σ h hσ
  | .inr b, d, e, σ, h, hσ => closedAt_sub b d e σ h hσ
  | .case s f g, d, e, σ, h, hσ =>
    ⟨closedAt_sub s d e σ h.1 hσ, closedAt_sub f d e σ h.2.1 hσ, closedAt_sub g d e σ h.2.2 hσ⟩

/-- Reduction keeps a term closed. -/
theorem WH.closed {t t' : Tm γ} (s : WH t t') (h : closedAt 0 t) : closedAt 0 t' := by
  induction s with
  | beta b a =>
    refine closedAt_sub b 1 0 (beta1 a) h.1 fun i hi => ?_
    cases i with
    | zero => exact h.2
    | succ i => exact absurd hi (by omega)
  | fstβ a b => exact h.1
  | sndβ a b => exact h.2
  | inlβ a f g => exact ⟨h.2.1, h.1⟩
  | inrβ b f g => exact ⟨h.2.2, h.1⟩
  | appL a _ ih => exact ⟨ih h.1, h.2⟩
  | fst _ ih => exact ih h
  | snd _ ih => exact ih h
  | caseS f g _ ih => exact ⟨ih h.1, h.2.1, h.2.2⟩

/-- A call-by-name step is a step. -/
theorem WH.step {t t' : Tm γ} (s : WH t t') : Step t t' := by
  induction s with
  | beta b a => exact .beta b a
  | fstβ a b => exact .fstβ a b
  | sndβ a b => exact .sndβ a b
  | inlβ a f g => exact .inlβ a f g
  | inrβ b f g => exact .inrβ b f g
  | appL a _ ih => exact .appL a ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | caseS f g _ ih => exact .caseS f g ih

/-- The computable call-by-name step. -/
def wh? : Tm γ → Option (Tm γ)
  | .app (.lam b) a => some (Tm.sub (beta1 a) b)
  | .app f a => (wh? f).map fun f' => .app f' a
  | .fst (.pair a _) => some a
  | .fst t => (wh? t).map .fst
  | .snd (.pair _ b) => some b
  | .snd t => (wh? t).map .snd
  | .case (.inl a) f _ => some (.app f a)
  | .case (.inr b) _ g => some (.app g b)
  | .case s f g => (wh? s).map fun s' => .case s' f g
  | _ => none

/-- Every call-by-name step is the one `wh?` computes. -/
theorem WH.wh? {t u : Tm γ} (s : WH t u) : wh? t = some u := by
  induction s with
  | beta b a => rfl
  | fstβ a b => rfl
  | sndβ a b => rfl
  | inlβ a f g => rfl
  | inrβ b f g => rfl
  | @appL f f' a h ih =>
    cases f with
    | lam b => exact (h.no_lam).elim
    | var _ => cases h
    | const _ => cases h
    | pair _ _ => cases h
    | inl _ => cases h
    | inr _ => cases h
    | _ => simp only [Rz.wh?, ih, Option.map_some]
  | @fst t t' h ih =>
    cases t with
    | pair a b => exact (h.no_pair).elim
    | var _ => cases h
    | const _ => cases h
    | lam _ => cases h
    | inl _ => cases h
    | inr _ => cases h
    | _ => simp only [Rz.wh?, ih, Option.map_some]
  | @snd t t' h ih =>
    cases t with
    | pair a b => exact (h.no_pair).elim
    | var _ => cases h
    | const _ => cases h
    | lam _ => cases h
    | inl _ => cases h
    | inr _ => cases h
    | _ => simp only [Rz.wh?, ih, Option.map_some]
  | @caseS s s' f g h ih =>
    cases s with
    | inl a => exact (h.no_inl).elim
    | inr b => exact (h.no_inr).elim
    | var _ => cases h
    | const _ => cases h
    | lam _ => cases h
    | pair _ _ => cases h
    | _ => simp only [Rz.wh?, ih, Option.map_some]

/-- What `wh?` computes is a call-by-name step. -/
theorem wh?_sound : ∀ {t u : Tm γ}, wh? t = some u → WH t u
  | .app f a, u, h => by
    cases f with
    | lam b => cases h; exact .beta _ _
    | _ =>
      simp only [Rz.wh?, Option.map_eq_some_iff] at h
      cases h with
      | intro f' h => rw [← h.2]; exact .appL a (wh?_sound h.1)
  | .fst t, u, h => by
    cases t with
    | pair a b => cases h; exact .fstβ _ _
    | _ =>
      simp only [Rz.wh?, Option.map_eq_some_iff] at h
      cases h with
      | intro t' h => rw [← h.2]; exact .fst (wh?_sound h.1)
  | .snd t, u, h => by
    cases t with
    | pair a b => cases h; exact .sndβ _ _
    | _ =>
      simp only [Rz.wh?, Option.map_eq_some_iff] at h
      cases h with
      | intro t' h => rw [← h.2]; exact .snd (wh?_sound h.1)
  | .case s f g, u, h => by
    cases s with
    | inl a => cases h; exact .inlβ _ _ _
    | inr b => cases h; exact .inrβ _ _ _
    | _ =>
      simp only [Rz.wh?, Option.map_eq_some_iff] at h
      cases h with
      | intro s' h => rw [← h.2]; exact .caseS f g (wh?_sound h.1)
  | .var _, _, h => by cases h
  | .const _, _, h => by cases h
  | .lam _, _, h => by cases h
  | .pair _ _, _, h => by cases h
  | .inl _, _, h => by cases h
  | .inr _, _, h => by cases h

/-- **A strongly normalizing term reaches a call-by-name normal form.** -/
theorem Tm.SN.wh_normal {t : Tm γ} (h : SN t) : ∃ n u, WHN n t u ∧ ∀ u', ¬ WH u u' := by
  induction h with
  | @intro t _ ih =>
    cases hw : wh? t with
    | none => exact ⟨0, t, .refl t, fun u' s => by rw [s.wh?] at hw; cases hw⟩
    | some t' =>
      have s := wh?_sound hw
      cases ih t' s.step with
      | intro n h => cases h with
        | intro u h => exact ⟨n + 1, u, .step s h.1, h.2⟩

theorem Typed.const_inv {Γ : Nat → Ty β} {c : γ} {T : Ty β} (h : Typed sig Γ (.const c) T) :
    T = sig c := by
  cases h; rfl

/-- An introduction form, or a constant. -/
def Intro : Tm γ → Prop
  | .lam _ => True
  | .pair _ _ => True
  | .inl _ => True
  | .inr _ => True
  | .const _ => True
  | _ => False

/-- **Canonical forms**: a closed, typed term with no call-by-name step is an
    introduction form or a constant, when constants have base types. -/
theorem canonical (hsig : ∀ c, ∃ b, sig c = .base b) {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β}
    (h : Typed sig Γ t A) (hc : closedAt 0 t) (hn : ∀ u, ¬ WH t u) : Intro t := by
  induction h with
  | var Γ n => exact absurd hc (Nat.not_lt_zero n)
  | const Γ c => trivial
  | lam _ _ => trivial
  | pair _ _ _ _ => trivial
  | inl _ _ => trivial
  | inr _ _ => trivial
  | @app Γ A B f a hf _ ihf _ =>
    have hi := ihf hc.1 fun u s => hn _ (.appL a s)
    cases f with
    | lam b => exact (hn _ (.beta b a)).elim
    | const c =>
      cases hsig c with
      | intro b hb => have e := hf.const_inv.trans hb; cases e
    | var _ => exact hi.elim
    | app _ _ => exact hi.elim
    | fst _ => exact hi.elim
    | snd _ => exact hi.elim
    | case _ _ _ => exact hi.elim
    | pair _ _ => cases hf
    | inl _ => cases hf
    | inr _ => cases hf
  | @fst Γ A B t ht ih =>
    have hi := ih hc fun u s => hn _ (.fst s)
    cases t with
    | pair a b => exact (hn _ (.fstβ a b)).elim
    | const c => cases hsig c with | intro b hb => have e := ht.const_inv.trans hb; cases e
    | lam _ => cases ht
    | inl _ => cases ht
    | inr _ => cases ht
    | var _ => exact hi.elim
    | app _ _ => exact hi.elim
    | fst _ => exact hi.elim
    | snd _ => exact hi.elim
    | case _ _ _ => exact hi.elim
  | @snd Γ A B t ht ih =>
    have hi := ih hc fun u s => hn _ (.snd s)
    cases t with
    | pair a b => exact (hn _ (.sndβ a b)).elim
    | const c => cases hsig c with | intro b hb => have e := ht.const_inv.trans hb; cases e
    | lam _ => cases ht
    | inl _ => cases ht
    | inr _ => cases ht
    | var _ => exact hi.elim
    | app _ _ => exact hi.elim
    | fst _ => exact hi.elim
    | snd _ => exact hi.elim
    | case _ _ _ => exact hi.elim
  | @case Γ A B C s f g hs _ _ ihs _ _ =>
    have hi := ihs hc.1 fun u st => hn _ (.caseS f g st)
    cases s with
    | inl a => exact (hn _ (.inlβ a f g)).elim
    | inr b => exact (hn _ (.inrβ b f g)).elim
    | const c => cases hsig c with | intro b hb => have e := hs.const_inv.trans hb; cases e
    | lam _ => cases hs
    | pair _ _ => cases hs
    | var _ => exact hi.elim
    | app _ _ => exact hi.elim
    | fst _ => exact hi.elim
    | snd _ => exact hi.elim
    | case _ _ _ => exact hi.elim

theorem WHN.typed {n : Nat} {t u : Tm γ} (s : WHN n t u) {Γ : Nat → Ty β} {A : Ty β}
    (h : Typed sig Γ t A) : Typed sig Γ u A := by
  induction s with
  | refl => exact h
  | step s1 _ ih => exact ih (s1.typed h)

theorem WHN.closed {n : Nat} {t u : Tm γ} (s : WHN n t u) (h : closedAt 0 t) : closedAt 0 u := by
  induction s with
  | refl => exact h
  | step s1 _ ih => exact ih (s1.closed h)

/-- **Closed Booleans evaluate**: a closed term of a sum type, whose constants
    have base types, reduces by call-by-name to an injection. -/
theorem evaluates_inj (hsig : ∀ c, ∃ b, sig c = .base b) {Γ : Nat → Ty β} {t : Tm γ}
    {A B : Ty β} (h : Typed sig Γ t (.sum A B)) (hc : closedAt 0 t) :
    ∃ n v, WHN n t v ∧ IsInj v := by
  cases (strong_normalization h).wh_normal with
  | intro n h' => cases h' with
    | intro u h' =>
      have hu := h'.1.typed h
      have hi := canonical hsig hu (h'.1.closed hc) h'.2
      refine ⟨n, u, h'.1, ?_⟩
      cases u with
      | inl a => exact ⟨a, .inl rfl⟩
      | inr b => exact ⟨b, .inr rfl⟩
      | const c => cases hsig c with | intro b hb => have e := hu.const_inv.trans hb; cases e
      | lam _ => cases hu
      | pair _ _ => cases hu
      | var _ => exact hi.elim
      | app _ _ => exact hi.elim
      | fst _ => exact hi.elim
      | snd _ => exact hi.elim
      | case _ _ _ => exact hi.elim

end Termination

theorem closedAt_twoT (d : Nat) : closedAt d (twoT : Tm γ) := by
  show 1 < d + 1 + 1 ∧ 1 < d + 1 + 1 ∧ 0 < d + 1 + 1
  exact ⟨by omega, by omega, by omega⟩

theorem closedAt_togT (d : Nat) : closedAt d (togT : Tm γ) := by
  show 0 < d + 1 ∧ 0 < d + 1 + 1 ∧ 0 < d + 1 + 1
  exact ⟨by omega, by omega, by omega⟩

theorem closedAt_towerT (d : Nat) : ∀ k : Nat, closedAt d (towerT k : Tm γ)
  | 0 => closedAt_twoT d
  | k + 1 => ⟨closedAt_towerT d k, closedAt_twoT d⟩

theorem closedAt_evalT (k : Nat) : closedAt 0 (evalT k trueT) :=
  ⟨⟨closedAt_towerT 0 k, closedAt_togT 0⟩, trivial⟩

/-- **The family terminates**: `evalT k trueT` reduces to an injection, so the
    lower bound is not vacuous. -/
theorem evalT_terminates (k : Nat) : ∃ n v, WHN n (evalT k trueT) v ∧ IsInj v :=
  evaluates_inj (sig := sigU) (fun _ => ⟨(), rfl⟩) (evalT_typed (fun _ => boolTy) k)
    (closedAt_evalT k)

-- ---------------------------------------------------------------------------
-- No elementary bound
-- ---------------------------------------------------------------------------

/-- Exponentials of height `j`: `expT 0 x = x`, `expT (j + 1) x = 2 ^ expT j x`. -/
def expT : Nat → Nat → Nat
  | 0, x => x
  | j + 1, x => 2 ^ expT j x

theorem two_pow_pos' (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

theorem lt_two_pow' : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have := lt_two_pow' n
    rw [Nat.pow_succ]
    have := two_pow_pos' n
    omega

theorem two_pow_lt {m n : Nat} (h : m < n) : 2 ^ m < 2 ^ n := by
  have h1 : 2 ^ (m + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h
  rw [Nat.pow_succ] at h1
  have := two_pow_pos' m
  omega

theorem expT_lt : ∀ (j : Nat) {x y : Nat}, x < y → expT j x < expT j y
  | 0, _, _, h => h
  | j + 1, _, _, h => two_pow_lt (expT_lt j h)

/-- The tower is exponentials over a lower tower. -/
theorem tw_add (m : Nat) : ∀ j : Nat, tw (m + j) = expT j (tw m)
  | 0 => rfl
  | j + 1 => by show 2 ^ tw (m + j) = 2 ^ expT j (tw m); rw [tw_add m j]

theorem pow_le_tw : ∀ m : Nat, 2 ^ m ≤ tw m
  | 0 => Nat.le_refl 1
  | m + 1 => by
    show 2 ^ (m + 1) ≤ 2 ^ tw m
    have h1 := lt_two_pow' m
    have h2 := pow_le_tw m
    exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The tower outgrows every linear function. -/
theorem tw_beats_linear (A B : Nat) : ∃ m, 1 ≤ m ∧ A * m + B < tw m := by
  refine ⟨2 * (2 * A + B + 1), by omega, ?_⟩
  generalize hX : 2 * A + B + 1 = X
  have hX1 : 1 ≤ X := by omega
  have hXX : X * X < 2 ^ (2 * X) := by
    have := Nat.mul_self_lt_mul_self (lt_two_pow' X)
    rw [← Nat.pow_add, show X + X = 2 * X by omega] at this
    exact this
  have hle := pow_le_tw (2 * X)
  -- `X * X ≥ X * (2A + B + 1) ≥ A * (2X) + B + 1`
  have e1 : X * X = X * (2 * A) + X * B + X := by
    conv => lhs; rw [show X = 2 * A + B + 1 from hX.symm]
    rw [← hX]; rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  have e2 : A * (2 * X) = X * (2 * A) := by
    rw [Nat.mul_left_comm A 2 X, Nat.mul_left_comm X 2 A, Nat.mul_comm A X]
  have e3 : B ≤ X * B := by rw [Nat.mul_comm]; exact Nat.le_mul_of_pos_right B hX1
  generalize X * X = P at *
  generalize X * (2 * A) = Q at *
  generalize X * B = R at *
  rw [e2]
  omega

/-- **No elementary bound.**  For every height `j` of exponentials and every
    constant `c`, some member of the typed family evaluates, and every
    evaluation of it to an injection takes more than `expT j (c · size)` steps. -/
theorem no_elementary_bound (j c : Nat) : ∃ k,
    (∃ n v, WHN n (evalT k trueT) v ∧ IsInj v) ∧
    ∀ n v, WHN n (evalT k trueT) v → IsInj v → expT j (c * asz (evalT k trueT)) < n := by
  cases tw_beats_linear (c * 8) (c * (8 * j + 17)) with
  | intro m hm =>
    refine ⟨m + j - 1, evalT_terminates _, fun n v hn hv => ?_⟩
    have hlow := evalT_lower (m + j - 1) (.const ()) hn hv
    rw [show m + j - 1 + 1 = m + j by omega, tw_add] at hlow
    rw [asz_evalT]
    have hsz : c * (8 * (m + j - 1) + 17) ≤ c * 8 * m + c * (8 * j + 17) := by
      have h1 : 8 * (m + j - 1) + 17 ≤ 8 * m + (8 * j + 17) := by omega
      have h2 := Nat.mul_le_mul_left c h1
      have h3 : c * (8 * m + (8 * j + 17)) = c * 8 * m + c * (8 * j + 17) := by
        rw [Nat.mul_add, Nat.mul_assoc]
      exact Nat.le_trans h2 (Nat.le_of_eq h3)
    exact Nat.lt_of_lt_of_le (expT_lt j (Nat.lt_of_le_of_lt hsz hm.2)) hlow

end Rz
