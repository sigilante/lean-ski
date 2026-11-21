import Ski.HnfQ5
open Term

/-!
# Size laws for head reduction of S-terms

`HeadChain` is head reduction (`HnfSound`).  The laws used by the certificate checker:

* `chain_factor` (F′): a head chain to `w₀ ⬝ L` either keeps `L` as the original last argument,
  or creates it at an arity-3 step `S x y z → x z (y z)` with `L = y z`;
* `chain_spine` / `L0`: after a step the spine has at least two items, so `S a` is reached only
  from itself;
* `L1`: if `t` head-reduces to `S S y` then `|y| + 2 = |t|`;
* `LA`: if `t` head-reduces to `S (S S) y` then `|y| + 2 ≤ |t|`.
-/

namespace HnfCertLaws
open HnfS HnfSound

/-- Number of atoms. -/
def tsz : Term → Nat
  | .app f x => tsz f + tsz x
  | _ => 1

theorem tsz_pos (t : Term) : 0 < tsz t := by
  induction t with
  | app f x ihf _ => simp only [tsz]; omega
  | _ => simp [tsz]

theorem foldl_append_one (rest : List Term) (r a : Term) :
    (rest ++ [r]).foldl Term.app a = (rest.foldl Term.app a) ⬝ r := by
  simp [List.foldl_append]

/-- **F′.** Factoring a head chain at the last argument of its end. -/
theorem chain_factor {t w : Term} (h : HeadChain t w) :
    ∀ {w₀ L : Term}, w = w₀ ⬝ L →
      (∃ t₀, t = t₀ ⬝ L ∧ HeadChain t₀ w₀) ∨
      (∃ x y z, HeadChain t (S ⬝ x ⬝ y ⬝ z) ∧ y ⬝ z = L ∧ HeadChain (x ⬝ z) w₀) := by
  induction h with
  | refl t => intro w₀ L hw; exact .inl ⟨w₀, hw, .refl _⟩
  | @step t v u₁ u₂ u₃ rest hs hS hc ih =>
    intro w₀ L hw
    rcases ih hw with ⟨t'₀, ht', hc'⟩ | ⟨x, y, z, hc', hyz, hxz⟩
    · rcases List.eq_nil_or_concat rest with rfl | ⟨rest₀, r, rfl⟩
      all_goals try simp only [List.concat_eq_append] at *
      · -- arity 3: the new last argument is u₂ u₃
        simp only [List.foldl] at ht' hS
        injection ht' with h1 h2
        refine .inr ⟨u₁, u₂, u₃, ?_, h2, ?_⟩
        · rw [hS]; exact .refl _
        · exact h1 ▸ hc'
      · -- arity ≥ 4: the last argument is untouched
        rw [foldl_append_one] at ht' hS
        injection ht' with h1 h2
        subst h2
        refine .inl ⟨rest₀.foldl Term.app (S ⬝ u₁ ⬝ u₂ ⬝ u₃), hS, ?_⟩
        have hs₀ : spine (rest₀.foldl Term.app (S ⬝ u₁ ⬝ u₂ ⬝ u₃)) = u₁ :: u₂ :: u₃ :: rest₀ := by
          rw [spine_foldl]; simp [spine]
        exact .step hs₀ rfl (h1 ▸ hc')
    · exact .inr ⟨x, y, z, .step hs hS hc', hyz, hxz⟩

/-- After at least one step the spine has two or more items. -/
theorem chain_spine {t u : Term} (h : HeadChain t u) : t = u ∨ 2 ≤ (spine u).length := by
  induction h with
  | refl => exact .inl rfl
  | @step t v u₁ u₂ u₃ rest hs hS hc ih =>
    right
    rcases ih with rfl | h2
    · rw [spine_foldl]; simp [spine]; omega
    · exact h2

/-- **L0.**  A head chain ending in a frame of one item is trivial. -/
theorem L0 {t u : Term} (h : HeadChain t u) (hl : (spine u).length ≤ 1) : t = u := by
  rcases chain_spine h with h | h
  · exact h
  · omega

theorem spine_S_app (a : Term) : spine (S ⬝ a) = [a] := by simp [spine]
theorem spine_S (t : Term) (h : t = S) : spine t = [] := by subst h; rfl

/-- **L1** (by strong induction on the size of `t`). -/
theorem L1aux : ∀ (n : Nat) (t y : Term), tsz t = n → HeadChain t (S ⬝ S ⬝ y) → tsz y + 2 = tsz t := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih t y hn h
  rcases chain_factor h rfl with ⟨t₀, rfl, h₀⟩ | ⟨x, y', z, hc, hyz, hxz⟩
  · -- t = t₀ y with t₀ ->* S S: a one-item frame, so t₀ = S S
    have := L0 h₀ (by simp [spine])
    subst this; simp [tsz]; omega
  · -- x z ->* S S forces x z = S S, so x = S, z = S, and y = y' S
    have hxz' := L0 hxz (by simp [spine])
    injection hxz' with hx hz
    subst hx hz hyz
    -- t ->* S S y' S, whose last argument S is an atom: factor it off
    rcases chain_factor hc rfl with ⟨t₁, rfl, h₁⟩ | ⟨_, y₂, z₂, _, hyz₂, _⟩
    · have := ih (tsz t₁) (by simp [tsz] at hn ⊢; omega) t₁ y' rfl h₁
      simp [tsz] at this ⊢; omega
    · exact absurd hyz₂ (by intro h; cases h)

/-- **L1.**  If `t` head-reduces to `S S y` then `|y| + 2 = |t|`. -/
theorem L1 {t y : Term} (h : HeadChain t (S ⬝ S ⬝ y)) : tsz y + 2 = tsz t := L1aux _ t y rfl h

/-- **LA.**  If `t` head-reduces to `S (S S) y` then `|y| + 2 ≤ |t|`. -/
theorem LA {t y : Term} (h : HeadChain t (S ⬝ (S ⬝ S) ⬝ y)) : tsz y + 2 ≤ tsz t := by
  rcases chain_factor h rfl with ⟨t₀, rfl, h₀⟩ | ⟨x, y', z, hc, hyz, hxz⟩
  · -- t = t₀ y with t₀ ->* S (S S): a one-item frame, so t₀ = S (S S)
    have := L0 h₀ (by simp [spine])
    subst this; simp [tsz]; omega
  · -- the last step was S x y' z -> x z (y' z) with x z ->* S (S S), so x z = S (S S)
    have hxz' := L0 hxz (by simp [spine])
    injection hxz' with hx hz
    subst hx hz hyz
    -- t ->* S S y' (S S); factor at the last argument S S
    rcases chain_factor hc rfl with ⟨t₁, rfl, h₁⟩ | ⟨x₂, y₂, z₂, hc₂, hyz₂, hxz₂⟩
    · -- t = t₁ (S S), t₁ ->* S S y': L1
      have := L1 h₁
      simp [tsz] at this ⊢; omega
    · -- S S was created: y₂ = S, z₂ = S, and x₂ S ->* S S y'
      injection hyz₂ with hy₂ hz₂
      subst hy₂ hz₂
      have h1 := L1 hxz₂
      -- t ->* S x₂ S S: peel the two atomic last arguments, then L0
      rcases chain_factor hc₂ rfl with ⟨t₃, rfl, h₃⟩ | ⟨_, y₃, z₃, _, hyz₃, _⟩
      · rcases chain_factor h₃ rfl with ⟨t₄, rfl, h₄⟩ | ⟨_, y₄, z₄, _, hyz₄, _⟩
        · have := L0 h₄ (by simp [spine])
          subst this; simp [tsz] at h1 ⊢; omega
        · exact absurd hyz₄ (by intro h; cases h)
      · exact absurd hyz₃ (by intro h; cases h)

end HnfCertLaws
