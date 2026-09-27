import Ski.Tait

/-!
# Stratum 1 at the source: affine realizers evaluate within their additive size

The paper's first stratum: an affine realizer evaluates within its
additive size.  Affinity and size both use the additive rule.

**The additive count** (`acnt`).  A variable's occurrences across the two
branches of a case count as the larger of the two, not the sum, since only
one branch runs.  A realizer is **additively affine** (`AffA`) when every
λ's variable occurs at most once under this count.  So a variable may
appear in both branches of a case, which is what glue that carries a
context through a case needs (`orDist`, `Ski/Sigma.lean`).

**The additive size** (`asz`) of a case is one, plus its scrutinee, plus
the larger branch.  A split is two plus its parts, one for each
application its step builds, so the step still shrinks the size.

**Reduction** (`WH`) is call-by-name to weak head normal form:
- β, projection of a pair, split of a pair, and case of an injection, at
  the head;
- congruence only in function, projection, split and scrutinee position,
  so a discarded branch is never touched.

**The theorem.**  Every step strictly decreases the additive size
(`WH.asz_lt`) and preserves additive affinity (`WH.affA`).  So every
reduction sequence of an additively affine realizer is shorter than its
additive size (`wh_bound`).  Typing is not needed.

The substitution argument: a λ's variable occurs at most once under the
additive count.  So β places the argument in at most one position on
every path through the case branches, and the size grows by at most the
argument's size (`asz_sub_le`).  Substitution never changes how often a
binder's own variable occurs (`acnt_sub_self`), so additive affinity
survives any substitution of affine terms (`affA_sub`).

This bound is on the source.  The compiled term's own normal-order steps
are bounded in `Ski/Cost.lean`, for multiplicatively affine realizers, and
in `Ski/CostAdd.lean`, for additively affine ones.  There the variables a
case's branches share are threaded through its continuations.
-/

namespace Rz

variable {γ : Type}

open Tm

/-- Additive size: a case costs its larger branch. -/
def asz : Tm γ → Nat
  | .var _ => 1
  | .const _ => 1
  | .app f a => asz f + asz a + 1
  | .lam b => asz b + 1
  | .pair a b => asz a + asz b + 1
  | .fst t => asz t + 1
  | .snd t => asz t + 1
  | .inl a => asz a + 1
  | .inr b => asz b + 1
  | .case s f g => asz s + max (asz f) (asz g) + 1
  | .split t k => asz t + asz k + 2

/-- Additive occurrences of the variable of index `i`: the larger of the two
    branches of a case. -/
def acnt : Nat → Tm γ → Nat
  | i, .var j => if j = i then 1 else 0
  | _, .const _ => 0
  | i, .app f a => acnt i f + acnt i a
  | i, .lam b => acnt (i + 1) b
  | i, .pair a b => acnt i a + acnt i b
  | i, .fst t => acnt i t
  | i, .snd t => acnt i t
  | i, .inl a => acnt i a
  | i, .inr b => acnt i b
  | i, .case s f g => acnt i s + max (acnt i f) (acnt i g)
  | i, .split t k => acnt i t + acnt i k

/-- **Additively affine**: every λ's variable occurs at most once, under the
    additive count. -/
def AffA : Tm γ → Prop
  | .var _ => True
  | .const _ => True
  | .app f a => AffA f ∧ AffA a
  | .lam b => acnt 0 b ≤ 1 ∧ AffA b
  | .pair a b => AffA a ∧ AffA b
  | .fst t => AffA t
  | .snd t => AffA t
  | .inl a => AffA a
  | .inr b => AffA b
  | .case s f g => AffA s ∧ AffA f ∧ AffA g
  | .split t k => AffA t ∧ AffA k

theorem asz_pos : ∀ t : Tm γ, 1 ≤ asz t := by
  intro t; cases t <;> simp only [asz] <;> omega

-- ---------------------------------------------------------------------------
-- Renaming and substitution
-- ---------------------------------------------------------------------------

theorem asz_ren : ∀ (t : Tm γ) (ξ : Nat → Nat), asz (ren ξ t) = asz t
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .app f a, ξ => by simp only [ren, asz, asz_ren f, asz_ren a]
  | .lam b, ξ => by simp only [ren, asz, asz_ren b]
  | .pair a b, ξ => by simp only [ren, asz, asz_ren a, asz_ren b]
  | .fst t, ξ => by simp only [ren, asz, asz_ren t]
  | .snd t, ξ => by simp only [ren, asz, asz_ren t]
  | .inl a, ξ => by simp only [ren, asz, asz_ren a]
  | .inr b, ξ => by simp only [ren, asz, asz_ren b]
  | .case s f g, ξ => by simp only [ren, asz, asz_ren s, asz_ren f, asz_ren g]
  | .split t k, ξ => by simp only [ren, asz, asz_ren t, asz_ren k]

theorem upr_inj {ξ : Nat → Nat} (h : ∀ a b, ξ a = ξ b → a = b) :
    ∀ a b, upr ξ a = upr ξ b → a = b
  | 0, 0, _ => rfl
  | 0, b + 1, e => by cases e
  | a + 1, 0, e => by cases e
  | a + 1, b + 1, e => by
    have : ξ a + 1 = ξ b + 1 := e
    rw [h a b (by omega)]

/-- An injective renaming keeps occurrences, at the renamed index. -/
theorem acnt_ren_inj : ∀ (t : Tm γ) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) → ∀ k,
    acnt (ξ k) (ren ξ t) = acnt k t
  | .var j, ξ, h, k => by
    show (if ξ j = ξ k then 1 else 0) = (if j = k then 1 else 0)
    by_cases hj : j = k
    · rw [if_pos hj, if_pos (by rw [hj])]
    · rw [if_neg hj, if_neg (fun e => hj (h j k e))]
  | .const _, _, _, _ => rfl
  | .app f a, ξ, h, k => by
    show acnt _ (ren ξ f) + acnt _ (ren ξ a) = _
    rw [acnt_ren_inj f ξ h k, acnt_ren_inj a ξ h k]; rfl
  | .lam b, ξ, h, k => by
    show acnt (ξ k + 1) (ren (upr ξ) b) = acnt (k + 1) b
    exact acnt_ren_inj b (upr ξ) (upr_inj h) (k + 1)
  | .pair a b, ξ, h, k => by
    show acnt _ (ren ξ a) + acnt _ (ren ξ b) = _
    rw [acnt_ren_inj a ξ h k, acnt_ren_inj b ξ h k]; rfl
  | .fst t, ξ, h, k => acnt_ren_inj t ξ h k
  | .snd t, ξ, h, k => acnt_ren_inj t ξ h k
  | .inl a, ξ, h, k => acnt_ren_inj a ξ h k
  | .inr b, ξ, h, k => acnt_ren_inj b ξ h k
  | .case s f g, ξ, h, k => by
    show acnt _ (ren ξ s) + max (acnt _ (ren ξ f)) (acnt _ (ren ξ g)) = _
    rw [acnt_ren_inj s ξ h k, acnt_ren_inj f ξ h k, acnt_ren_inj g ξ h k]; rfl
  | .split t c, ξ, h, k => by
    show acnt _ (ren ξ t) + acnt _ (ren ξ c) = _
    rw [acnt_ren_inj t ξ h k, acnt_ren_inj c ξ h k]; rfl

theorem succ_inj : ∀ a b : Nat, Nat.succ a = Nat.succ b → a = b := fun _ _ e => Nat.succ.inj e

/-- Nothing occurs at `0` after shifting up. -/
theorem acnt_shift : ∀ (t : Tm γ) (ξ : Nat → Nat) (k : Nat), (∀ i, ξ i ≠ k) →
    acnt k (ren ξ t) = 0
  | .var j, ξ, k, h => by show (if ξ j = k then 1 else 0) = 0; rw [if_neg (h j)]
  | .const _, _, _, _ => rfl
  | .app f a, ξ, k, h => by
    show acnt k (ren ξ f) + acnt k (ren ξ a) = 0
    rw [acnt_shift f ξ k h, acnt_shift a ξ k h]
  | .lam b, ξ, k, h => by
    show acnt (k + 1) (ren (upr ξ) b) = 0
    refine acnt_shift b (upr ξ) (k + 1) ?_
    intro i
    cases i with
    | zero => show 0 ≠ k + 1; omega
    | succ i => show ξ i + 1 ≠ k + 1; have := h i; omega
  | .pair a b, ξ, k, h => by
    show acnt k (ren ξ a) + acnt k (ren ξ b) = 0
    rw [acnt_shift a ξ k h, acnt_shift b ξ k h]
  | .fst t, ξ, k, h => acnt_shift t ξ k h
  | .snd t, ξ, k, h => acnt_shift t ξ k h
  | .inl a, ξ, k, h => acnt_shift a ξ k h
  | .inr b, ξ, k, h => acnt_shift b ξ k h
  | .case s f g, ξ, k, h => by
    show acnt k (ren ξ s) + max (acnt k (ren ξ f)) (acnt k (ren ξ g)) = 0
    rw [acnt_shift s ξ k h, acnt_shift f ξ k h, acnt_shift g ξ k h]; rfl
  | .split t c, ξ, k, h => by
    show acnt k (ren ξ t) + acnt k (ren ξ c) = 0
    rw [acnt_shift t ξ k h, acnt_shift c ξ k h]

/-- A substitution that keeps `k` and puts nothing at `k` elsewhere keeps
    `k`'s occurrences. -/
theorem acnt_sub_self : ∀ (t : Tm γ) (σ : Nat → Tm γ) (k : Nat), σ k = .var k →
    (∀ i, i ≠ k → acnt k (σ i) = 0) → acnt k (sub σ t) = acnt k t
  | .var j, σ, k, h1, h2 => by
    show acnt k (σ j) = (if j = k then 1 else 0)
    by_cases hj : j = k
    · rw [hj, h1, if_pos rfl]; show (if k = k then 1 else 0) = 1; rw [if_pos rfl]
    · rw [if_neg hj]; exact h2 j hj
  | .const _, _, _, _, _ => rfl
  | .app f a, σ, k, h1, h2 => by
    show acnt k (sub σ f) + acnt k (sub σ a) = _
    rw [acnt_sub_self f σ k h1 h2, acnt_sub_self a σ k h1 h2]; rfl
  | .lam b, σ, k, h1, h2 => by
    show acnt (k + 1) (sub (up σ) b) = acnt (k + 1) b
    refine acnt_sub_self b (up σ) (k + 1) (by show ren Nat.succ (σ k) = _; rw [h1]; rfl) ?_
    intro i hi
    cases i with
    | zero => show (if 0 = k + 1 then 1 else 0) = 0; rw [if_neg (by omega)]
    | succ i =>
      show acnt (Nat.succ k) (ren Nat.succ (σ i)) = 0
      rw [acnt_ren_inj (σ i) Nat.succ succ_inj k]
      exact h2 i (by omega)
  | .pair a b, σ, k, h1, h2 => by
    show acnt k (sub σ a) + acnt k (sub σ b) = _
    rw [acnt_sub_self a σ k h1 h2, acnt_sub_self b σ k h1 h2]; rfl
  | .fst t, σ, k, h1, h2 => acnt_sub_self t σ k h1 h2
  | .snd t, σ, k, h1, h2 => acnt_sub_self t σ k h1 h2
  | .inl a, σ, k, h1, h2 => acnt_sub_self a σ k h1 h2
  | .inr b, σ, k, h1, h2 => acnt_sub_self b σ k h1 h2
  | .case s f g, σ, k, h1, h2 => by
    show acnt k (sub σ s) + max (acnt k (sub σ f)) (acnt k (sub σ g)) = _
    rw [acnt_sub_self s σ k h1 h2, acnt_sub_self f σ k h1 h2, acnt_sub_self g σ k h1 h2]; rfl
  | .split t c, σ, k, h1, h2 => by
    show acnt k (sub σ t) + acnt k (sub σ c) = _
    rw [acnt_sub_self t σ k h1 h2, acnt_sub_self c σ k h1 h2]; rfl

-- ---------------------------------------------------------------------------
-- Additive affinity survives renaming and substitution
-- ---------------------------------------------------------------------------

theorem affA_ren : ∀ (t : Tm γ) (ξ : Nat → Nat), (∀ a b, ξ a = ξ b → a = b) → AffA t →
    AffA (ren ξ t)
  | .var _, _, _, _ => trivial
  | .const _, _, _, _ => trivial
  | .app f a, ξ, h, ht => ⟨affA_ren f ξ h ht.1, affA_ren a ξ h ht.2⟩
  | .lam b, ξ, h, ht => by
    refine ⟨?_, affA_ren b (upr ξ) (upr_inj h) ht.2⟩
    show acnt (upr ξ 0) (ren (upr ξ) b) ≤ 1
    rw [acnt_ren_inj b (upr ξ) (upr_inj h) 0]
    exact ht.1
  | .pair a b, ξ, h, ht => ⟨affA_ren a ξ h ht.1, affA_ren b ξ h ht.2⟩
  | .fst t, ξ, h, ht => affA_ren t ξ h ht
  | .snd t, ξ, h, ht => affA_ren t ξ h ht
  | .inl a, ξ, h, ht => affA_ren a ξ h ht
  | .inr b, ξ, h, ht => affA_ren b ξ h ht
  | .case s f g, ξ, h, ht => ⟨affA_ren s ξ h ht.1, affA_ren f ξ h ht.2.1, affA_ren g ξ h ht.2.2⟩
  | .split t k, ξ, h, ht => ⟨affA_ren t ξ h ht.1, affA_ren k ξ h ht.2⟩

/-- **Additive affinity survives any substitution of additively affine terms.** -/
theorem affA_sub : ∀ (t : Tm γ) (σ : Nat → Tm γ), (∀ i, AffA (σ i)) → AffA t → AffA (sub σ t)
  | .var i, σ, hσ, _ => hσ i
  | .const _, _, _, _ => trivial
  | .app f a, σ, hσ, ht => ⟨affA_sub f σ hσ ht.1, affA_sub a σ hσ ht.2⟩
  | .lam b, σ, hσ, ht => by
    have hup : ∀ i, AffA (up σ i) := by
      intro i
      cases i with
      | zero => trivial
      | succ i => exact affA_ren (σ i) Nat.succ succ_inj (hσ i)
    refine ⟨?_, affA_sub b (up σ) hup ht.2⟩
    show acnt 0 (sub (up σ) b) ≤ 1
    rw [acnt_sub_self b (up σ) 0 rfl ?_]
    · exact ht.1
    · intro i hi
      cases i with
      | zero => exact absurd rfl hi
      | succ i => exact acnt_shift (σ i) Nat.succ 0 (fun j => Nat.succ_ne_zero j)
  | .pair a b, σ, hσ, ht => ⟨affA_sub a σ hσ ht.1, affA_sub b σ hσ ht.2⟩
  | .fst t, σ, hσ, ht => affA_sub t σ hσ ht
  | .snd t, σ, hσ, ht => affA_sub t σ hσ ht
  | .inl a, σ, hσ, ht => affA_sub a σ hσ ht
  | .inr b, σ, hσ, ht => affA_sub b σ hσ ht
  | .case s f g, σ, hσ, ht => ⟨affA_sub s σ hσ ht.1, affA_sub f σ hσ ht.2.1, affA_sub g σ hσ ht.2.2⟩
  | .split t k, σ, hσ, ht => ⟨affA_sub t σ hσ ht.1, affA_sub k σ hσ ht.2⟩

-- ---------------------------------------------------------------------------
-- Substitution and additive size
-- ---------------------------------------------------------------------------

/-- `σ` sends every index but `k` to a variable. -/
def VarsBut (σ : Nat → Tm γ) (k : Nat) : Prop := ∀ i, i ≠ k → ∃ j, σ i = .var j

theorem VarsBut.up {σ : Nat → Tm γ} {k : Nat} (h : VarsBut σ k) : VarsBut (up σ) (k + 1) := by
  intro i hi
  cases i with
  | zero => exact ⟨0, rfl⟩
  | succ i =>
    cases h i (by omega) with
    | intro j hj => exact ⟨j + 1, by show ren Nat.succ (σ i) = _; rw [hj]; rfl⟩

/-- Substituting at an index that does not occur keeps the size. -/
theorem asz_sub_zero : ∀ (t : Tm γ) (σ : Nat → Tm γ) (k : Nat), VarsBut σ k →
    acnt k t = 0 → asz (sub σ t) = asz t
  | .var i, σ, k, hσ, h => by
    have hi : i ≠ k := fun e => by rw [e] at h; simp [acnt] at h
    cases hσ i hi with
    | intro j hj => show asz (σ i) = 1; rw [hj]; rfl
  | .const _, _, _, _, _ => rfl
  | .app f a, σ, k, hσ, h => by
    have h' : acnt k f + acnt k a = 0 := h
    show asz (sub σ f) + asz (sub σ a) + 1 = _
    rw [asz_sub_zero f σ k hσ (by omega), asz_sub_zero a σ k hσ (by omega)]; rfl
  | .lam b, σ, k, hσ, h => by
    show asz (sub (up σ) b) + 1 = _
    rw [asz_sub_zero b (up σ) (k + 1) hσ.up h]; rfl
  | .pair a b, σ, k, hσ, h => by
    have h' : acnt k a + acnt k b = 0 := h
    show asz (sub σ a) + asz (sub σ b) + 1 = _
    rw [asz_sub_zero a σ k hσ (by omega), asz_sub_zero b σ k hσ (by omega)]; rfl
  | .fst t, σ, k, hσ, h => by
    show asz (sub σ t) + 1 = _; rw [asz_sub_zero t σ k hσ h]; rfl
  | .snd t, σ, k, hσ, h => by
    show asz (sub σ t) + 1 = _; rw [asz_sub_zero t σ k hσ h]; rfl
  | .inl a, σ, k, hσ, h => by
    show asz (sub σ a) + 1 = _; rw [asz_sub_zero a σ k hσ h]; rfl
  | .inr b, σ, k, hσ, h => by
    show asz (sub σ b) + 1 = _; rw [asz_sub_zero b σ k hσ h]; rfl
  | .case s f g, σ, k, hσ, h => by
    have h' : acnt k s + max (acnt k f) (acnt k g) = 0 := h
    have hs : acnt k s = 0 := by omega
    have hf : acnt k f = 0 := by omega
    have hg : acnt k g = 0 := by omega
    show asz (sub σ s) + max (asz (sub σ f)) (asz (sub σ g)) + 1 = _
    rw [asz_sub_zero s σ k hσ hs, asz_sub_zero f σ k hσ hf, asz_sub_zero g σ k hσ hg]; rfl
  | .split t c, σ, k, hσ, h => by
    have h' : acnt k t + acnt k c = 0 := h
    show asz (sub σ t) + asz (sub σ c) + 2 = _
    rw [asz_sub_zero t σ k hσ (by omega), asz_sub_zero c σ k hσ (by omega)]; rfl

/-- **Substitution at an affine index grows the size by at most the
    argument's size**, counting a case's branches additively. -/
theorem asz_sub_le : ∀ (t : Tm γ) (σ : Nat → Tm γ) (k : Nat), VarsBut σ k →
    acnt k t ≤ 1 → asz (sub σ t) + 1 ≤ asz t + asz (σ k)
  | .var i, σ, k, hσ, _ => by
    show asz (σ i) + 1 ≤ 1 + asz (σ k)
    by_cases hi : i = k
    · rw [hi]; omega
    · cases hσ i hi with
      | intro j hj => rw [hj]; have := asz_pos (σ k); show 1 + 1 ≤ 1 + asz (σ k); omega
  | .const _, σ, k, _, _ => by show 1 + 1 ≤ 1 + asz (σ k); have := asz_pos (σ k); omega
  | .app f a, σ, k, hσ, h => by
    have h' : acnt k f + acnt k a ≤ 1 := h
    show asz (sub σ f) + asz (sub σ a) + 1 + 1 ≤ asz f + asz a + 1 + asz (σ k)
    by_cases hf : acnt k f = 0
    · rw [asz_sub_zero f σ k hσ hf]
      have := asz_sub_le a σ k hσ (by omega); omega
    · rw [asz_sub_zero a σ k hσ (by omega)]
      have := asz_sub_le f σ k hσ (by omega); omega
  | .lam b, σ, k, hσ, h => by
    show asz (sub (up σ) b) + 1 + 1 ≤ asz b + 1 + asz (σ k)
    have := asz_sub_le b (up σ) (k + 1) hσ.up h
    have e : asz (up σ (k + 1)) = asz (σ k) := asz_ren (σ k) Nat.succ
    omega
  | .pair a b, σ, k, hσ, h => by
    have h' : acnt k a + acnt k b ≤ 1 := h
    show asz (sub σ a) + asz (sub σ b) + 1 + 1 ≤ asz a + asz b + 1 + asz (σ k)
    by_cases ha : acnt k a = 0
    · rw [asz_sub_zero a σ k hσ ha]
      have := asz_sub_le b σ k hσ (by omega); omega
    · rw [asz_sub_zero b σ k hσ (by omega)]
      have := asz_sub_le a σ k hσ (by omega); omega
  | .fst t, σ, k, hσ, h => by
    show asz (sub σ t) + 1 + 1 ≤ asz t + 1 + asz (σ k)
    have := asz_sub_le t σ k hσ h; omega
  | .snd t, σ, k, hσ, h => by
    show asz (sub σ t) + 1 + 1 ≤ asz t + 1 + asz (σ k)
    have := asz_sub_le t σ k hσ h; omega
  | .inl a, σ, k, hσ, h => by
    show asz (sub σ a) + 1 + 1 ≤ asz a + 1 + asz (σ k)
    have := asz_sub_le a σ k hσ h; omega
  | .inr b, σ, k, hσ, h => by
    show asz (sub σ b) + 1 + 1 ≤ asz b + 1 + asz (σ k)
    have := asz_sub_le b σ k hσ h; omega
  | .case s f g, σ, k, hσ, h => by
    have h' : acnt k s + max (acnt k f) (acnt k g) ≤ 1 := h
    show asz (sub σ s) + max (asz (sub σ f)) (asz (sub σ g)) + 1 + 1 ≤
      asz s + max (asz f) (asz g) + 1 + asz (σ k)
    by_cases hs : acnt k s = 0
    · rw [asz_sub_zero s σ k hσ hs]
      have hf := asz_sub_le f σ k hσ (by omega)
      have hg := asz_sub_le g σ k hσ (by omega)
      omega
    · rw [asz_sub_zero f σ k hσ (by omega), asz_sub_zero g σ k hσ (by omega)]
      have := asz_sub_le s σ k hσ (by omega); omega
  | .split t c, σ, k, hσ, h => by
    have h' : acnt k t + acnt k c ≤ 1 := h
    show asz (sub σ t) + asz (sub σ c) + 2 + 1 ≤ asz t + asz c + 2 + asz (σ k)
    by_cases ht : acnt k t = 0
    · rw [asz_sub_zero t σ k hσ ht]
      have := asz_sub_le c σ k hσ (by omega); omega
    · rw [asz_sub_zero c σ k hσ (by omega)]
      have := asz_sub_le t σ k hσ (by omega); omega

-- ---------------------------------------------------------------------------
-- Call-by-name reduction to weak head normal form
-- ---------------------------------------------------------------------------

/-- One call-by-name step: a redex at the head, or a step in function,
    projection or scrutinee position.  Branches and arguments are never
    reduced. -/
inductive WH : Tm γ → Tm γ → Prop
  | beta (b a : Tm γ) : WH (.app (.lam b) a) (sub (beta1 a) b)
  | fstβ (a b : Tm γ) : WH (.fst (.pair a b)) a
  | sndβ (a b : Tm γ) : WH (.snd (.pair a b)) b
  | inlβ (a f g : Tm γ) : WH (.case (.inl a) f g) (.app f a)
  | inrβ (b f g : Tm γ) : WH (.case (.inr b) f g) (.app g b)
  | appL {f f' : Tm γ} (a : Tm γ) : WH f f' → WH (.app f a) (.app f' a)
  | fst {t t' : Tm γ} : WH t t' → WH (.fst t) (.fst t')
  | snd {t t' : Tm γ} : WH t t' → WH (.snd t) (.snd t')
  | caseS {s s' : Tm γ} (f g : Tm γ) : WH s s' → WH (.case s f g) (.case s' f g)
  | splitβ (a b k : Tm γ) : WH (.split (.pair a b) k) (.app (.app k a) b)
  | splitT {t t' : Tm γ} (k : Tm γ) : WH t t' → WH (.split t k) (.split t' k)

theorem beta1_varsBut (a : Tm γ) : VarsBut (beta1 a) 0 := by
  intro i hi
  cases i with
  | zero => exact absurd rfl hi
  | succ i => exact ⟨i, rfl⟩

theorem beta1_affA {a : Tm γ} (ha : AffA a) : ∀ i, AffA (beta1 a i)
  | 0 => ha
  | _ + 1 => trivial

/-- **Each step preserves additive affinity.** -/
theorem WH.affA {t t' : Tm γ} (h : WH t t') (ht : AffA t) : AffA t' := by
  induction h with
  | beta b a => exact affA_sub b (beta1 a) (beta1_affA ht.2) ht.1.2
  | fstβ a b => exact ht.1
  | sndβ a b => exact ht.2
  | inlβ a f g => exact ⟨ht.2.1, ht.1⟩
  | inrβ b f g => exact ⟨ht.2.2, ht.1⟩
  | appL a _ ih => exact ⟨ih ht.1, ht.2⟩
  | fst _ ih => exact ih ht
  | snd _ ih => exact ih ht
  | caseS f g _ ih => exact ⟨ih ht.1, ht.2.1, ht.2.2⟩
  | splitβ a b k => exact ⟨⟨ht.2, ht.1.1⟩, ht.1.2⟩
  | splitT k _ ih => exact ⟨ih ht.1, ht.2⟩

/-- **Each step strictly decreases the additive size.** -/
theorem WH.asz_lt {t t' : Tm γ} (h : WH t t') (ht : AffA t) : asz t' < asz t := by
  induction h with
  | beta b a =>
    have := asz_sub_le b (beta1 a) 0 (beta1_varsBut a) ht.1.1
    show asz (sub (beta1 a) b) < asz b + 1 + asz a + 1
    have e : asz (beta1 a 0) = asz a := rfl
    omega
  | fstβ a b => show asz a < asz a + asz b + 1 + 1; omega
  | sndβ a b => show asz b < asz a + asz b + 1 + 1; omega
  | inlβ a f g =>
    show asz f + asz a + 1 < asz a + 1 + max (asz f) (asz g) + 1
    omega
  | inrβ b f g =>
    show asz g + asz b + 1 < asz b + 1 + max (asz f) (asz g) + 1
    omega
  | appL a _ ih =>
    show asz _ + asz a + 1 < asz _ + asz a + 1
    have := ih ht.1; omega
  | fst _ ih => show asz _ + 1 < asz _ + 1; have := ih ht; omega
  | snd _ ih => show asz _ + 1 < asz _ + 1; have := ih ht; omega
  | caseS f g _ ih =>
    show asz _ + max (asz f) (asz g) + 1 < asz _ + max (asz f) (asz g) + 1
    have := ih ht.1; omega
  | splitβ a b k => show asz k + asz a + 1 + asz b + 1 < asz a + asz b + 1 + asz k + 2; omega
  | splitT k _ ih =>
    show asz _ + asz k + 2 < asz _ + asz k + 2
    have := ih ht.1; omega

/-- Exactly `n` call-by-name steps. -/
inductive WHN : Nat → Tm γ → Tm γ → Prop
  | refl (t : Tm γ) : WHN 0 t t
  | step {n : Nat} {t t' u : Tm γ} : WH t t' → WHN n t' u → WHN (n + 1) t u

/-- **Stratum 1, at the source**: a reduction of `n` call-by-name steps
    from an additively affine term leaves at most its additive size minus
    `n`, so `n` is below the additive size. -/
theorem wh_bound {n : Nat} {t u : Tm γ} (h : WHN n t u) (ht : AffA t) : n + asz u ≤ asz t := by
  induction h with
  | refl => omega
  | step s _ ih =>
    have h1 := s.asz_lt ht
    have h2 := ih (s.affA ht)
    omega

theorem wh_steps_lt {n : Nat} {t u : Tm γ} (h : WHN n t u) (ht : AffA t) : n < asz t := by
  have := wh_bound h ht
  have := asz_pos u
  omega

end Rz
