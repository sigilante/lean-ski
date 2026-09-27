import Nock.Fingerprint
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime
import SkiZk.Memory

/-!
# Fingerprints of terms, over BabyBear

Pure Nock fingerprints a noun as three field elements (`NPR.fnHorner`) and
bounds collisions between distinct field-nouns by univariate
Schwartz–Zippel.  A field-noun is the noun with its leaves cast into the
field, so two distinct nouns can share a fingerprint for every `r` when
their leaves collide mod `p`.  Stored terms have leaves 0, 1, 2, and these
stay distinct in any field where `2 ≠ 0`; so distinct terms are distinct
field-nouns (`toNoun_fieldNoun_ne`) and collide for at most `2Λ − 1` of the
field's elements (`term_collision_card_le`).

BabyBear is the prime `p = 15 · 2^27 + 1 = 2013265921`.  Over `ZMod p`
the bound is `(2Λ − 1) / p`, about `Λ · 2^-30`, which is too weak for a
proof system; provers draw `r` from the degree-4 extension, where the bound
is `(2Λ − 1) / p^4` (`babyBear4_collision_card_le`).  Any field of
characteristic `p` qualifies.
-/

open Term Nock

namespace SkiZk

/-- The leaf array of a stored term: every leaf is 0, 1 or 2. -/
theorem leafList_toNoun_le (t : Term) : ∀ k ∈ (toNoun t).leafList, k ≤ 2 := by
  induction t with
  | S => intro k hk; simp [toNoun, Noun.leafList] at hk; omega
  | K => intro k hk; simp [toNoun, Noun.leafList] at hk; omega
  | I => intro k hk; simp [toNoun, Noun.leafList] at hk; omega
  | app f x ihf ihx =>
    intro k hk
    simp only [toNoun, Noun.leafList, List.mem_append] at hk
    cases hk with
    | inl h => exact ihf k h
    | inr h => exact ihx k h

section Field

variable {K : Type*} [Field K]

theorem cast_inj_le_two (h2 : (2 : K) ≠ 0) :
    ∀ {a b : ℕ}, a ≤ 2 → b ≤ 2 → (a : K) = (b : K) → a = b := by
  intro a b ha hb h
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  have h21 : (2 : K) ≠ 1 := by
    intro e
    apply h1
    have : (2 : K) - 1 = 0 := by rw [e, sub_self]
    rw [← this]; norm_num
  interval_cases a <;> interval_cases b <;> simp_all [eq_comm]

theorem map_cast_inj (h2 : (2 : K) ≠ 0) :
    ∀ {l₁ l₂ : List ℕ}, (∀ k ∈ l₁, k ≤ 2) → (∀ k ∈ l₂, k ≤ 2) →
      l₁.map (fun k : ℕ => (k : K)) = l₂.map (fun k : ℕ => (k : K)) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [cast_inj_le_two h2 (h₁ a (by simp)) (h₂ b (by simp)) h.1,
      map_cast_inj h2 (fun k hk => h₁ k (by simp [hk])) (fun k hk => h₂ k (by simp [hk])) h.2]

theorem dyckBits_inj {n₁ n₂ : Noun}
    (h : NPR.dyckBits (K := K) n₁ = NPR.dyckBits (K := K) n₂) : n₁.dyckWord = n₂.dyckWord := by
  unfold NPR.dyckBits at h
  refine List.map_injective_iff.2 ?_ h
  intro a b hab
  cases a <;> cases b <;> simp_all

/-- Distinct terms are distinct field-nouns wherever `2 ≠ 0`. -/
theorem toNoun_fieldNoun_ne (h2 : (2 : K) ≠ 0) {t₁ t₂ : Term} (hne : t₁ ≠ t₂) :
    (NPR.leafF (K := K) (toNoun t₁), NPR.dyckBits (K := K) (toNoun t₁))
      ≠ (NPR.leafF (K := K) (toNoun t₂), NPR.dyckBits (K := K) (toNoun t₂)) := by
  intro h
  simp only [Prod.mk.injEq] at h
  apply hne
  apply toNoun_injective
  apply Noun.noun_dyck_leaf_injective
  simp only [Prod.mk.injEq]
  exact ⟨dyckBits_inj h.2,
    map_cast_inj h2 (leafList_toNoun_le t₁) (leafList_toNoun_le t₂) h.1⟩

variable [Fintype K] [DecidableEq K]

/-- **Term collisions.**  Distinct terms of at most `Λ` leaves share a
    fingerprint for at most `2Λ − 1` values of `r`. -/
theorem term_collision_card_le (h2 : (2 : K) ≠ 0) (Λ : ℕ) {t₁ t₂ : Term} (hne : t₁ ≠ t₂)
    (h₁ : (toNoun t₁).leaves ≤ Λ) (h₂ : (toNoun t₂).leaves ≤ Λ) :
    (Finset.univ.filter (fun r : K =>
        NPR.fnHorner r (toNoun t₁) = NPR.fnHorner r (toNoun t₂))).card ≤ 2 * Λ - 1 := by
  simp only [NPR.fnHorner_eq_fn]
  exact NPR.collision_card_le_tight Λ _ _ h₁ h₂ (toNoun_fieldNoun_ne h2 hne)

end Field

/-- The BabyBear prime, `15 · 2^27 + 1`. -/
def babyBear : ℕ := 2013265921

theorem babyBear_eq : babyBear = 15 * 2 ^ 27 + 1 := rfl

instance babyBear_prime : Fact (Nat.Prime babyBear) := ⟨by unfold babyBear; norm_num⟩

theorem two_ne_zero_of_charP {K : Type*} [Field K] [CharP K babyBear] : (2 : K) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff K babyBear 2).1 (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) this
  unfold babyBear at this
  omega

/-- Over any field of characteristic BabyBear. -/
theorem babyBear_collision_card_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [CharP K babyBear] (Λ : ℕ) {t₁ t₂ : Term} (hne : t₁ ≠ t₂)
    (h₁ : (toNoun t₁).leaves ≤ Λ) (h₂ : (toNoun t₂).leaves ≤ Λ) :
    (Finset.univ.filter (fun r : K =>
        NPR.fnHorner r (toNoun t₁) = NPR.fnHorner r (toNoun t₂))).card ≤ 2 * Λ - 1 :=
  term_collision_card_le two_ne_zero_of_charP Λ hne h₁ h₂

/-- The degree-4 extension of BabyBear has `p^4` elements. -/
theorem babyBear4_card : Nat.card (GaloisField babyBear 4) = babyBear ^ 4 :=
  GaloisField.card babyBear 4 (by norm_num)

/-- **Over the degree-4 extension**: distinct terms collide for at most
    `2Λ − 1` of its `p^4` elements. -/
theorem babyBear4_collision_card_le (Λ : ℕ) {t₁ t₂ : Term} (hne : t₁ ≠ t₂)
    (h₁ : (toNoun t₁).leaves ≤ Λ) (h₂ : (toNoun t₂).leaves ≤ Λ) :
    ∃ _ : Fintype (GaloisField babyBear 4), ∃ _ : DecidableEq (GaloisField babyBear 4),
      Fintype.card (GaloisField babyBear 4) = babyBear ^ 4 ∧
      (Finset.univ.filter (fun r : GaloisField babyBear 4 =>
        NPR.fnHorner r (toNoun t₁) = NPR.fnHorner r (toNoun t₂))).card ≤ 2 * Λ - 1 := by
  classical
  letI : Fintype (GaloisField babyBear 4) := Fintype.ofFinite _
  refine ⟨inferInstance, inferInstance, ?_, babyBear_collision_card_le Λ hne h₁ h₂⟩
  rw [← Nat.card_eq_fintype_card, babyBear4_card]

end SkiZk
