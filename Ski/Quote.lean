import Ski.Weak
import Ski.Compile
import Ski.Lambda

open Term Lam

/-!
# No combinator quotes live terms

Proposition 3.1 of the metacircular paper: no closed `Q` over `{S, K, I}`
satisfies `Q M ↠ ⟨M⟩` for every closed `M`, where `⟨M⟩` is `M` encoded as
data over the object type `S | K | I | App`.  So quotation, entering the
representation, is a host function, and a program cannot reify a run-time
parameter from inside: the statement/witness line of a proof is where the
compiler puts it.

The paper proves it by reduction to Jay and Given-Wilson's Theorem 3.2
(factorisation is not representable in `SK`).  The argument here is the
λ-calculus one the paper sketches, made exact.  Translate combinators into
λ-terms (`tr`); weak reduction becomes β-reduction (`tr_wsteps`); and
`S K X` reduces to the identity for every `X` (`tr_SK`).  So `Q (S K S)`
and `Q (S K K)` reduce to one term, and by Church–Rosser any normal forms of
their quotations coincide (`no_quote_of_separated`).  The quotations of
`S K S` and `S K K` have different normal forms, computed by the kernel
(`quote_separated`), so no `Q` exists (`no_quote`).
-/

/-- The combinators as λ-terms. -/
def trS : Lam := lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))
def trK : Lam := lam (lam (var 1))
def trI : Lam := lam (var 0)

def tr : Term → Lam
  | .S => trS
  | .K => trK
  | .I => trI
  | .app f a => app (tr f) (tr a)

/-- A translated term is closed: substitution and renaming leave it alone. -/
theorem tr_sub : ∀ (t : Term) (σ : Nat → Lam), Lam.sub σ (tr t) = tr t
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .app f a, σ => by
    show app (Lam.sub σ (tr f)) (Lam.sub σ (tr a)) = app (tr f) (tr a)
    rw [tr_sub f, tr_sub a]

theorem tr_ren : ∀ (t : Term) (ξ : Nat → Nat), Lam.ren ξ (tr t) = tr t
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .app f a, ξ => by
    show app (Lam.ren ξ (tr f)) (Lam.ren ξ (tr a)) = app (tr f) (tr a)
    rw [tr_ren f, tr_ren a]

theorem tr_S (x y z : Term) :
    LSteps (tr (.S ⬝ x ⬝ y ⬝ z)) (tr (x ⬝ z ⬝ (y ⬝ z))) := by
  -- three β-steps, the arguments closed
  have s1 : LStep (app (app (app trS (tr x)) (tr y)) (tr z))
      (app (app (lam (lam (app (app (tr x) (var 0)) (app (var 1) (var 0))))) (tr y)) (tr z)) := by
    have e : Lam.sub (beta1 (tr x)) (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))
        = lam (lam (app (app (tr x) (var 0)) (app (var 1) (var 0)))) := by
      show lam (lam (app (app (Lam.ren Nat.succ (Lam.ren Nat.succ (tr x))) (var 0))
        (app (var 1) (var 0)))) = _
      rw [tr_ren, tr_ren]
    have h := LStep.beta (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0))))) (tr x)
    rw [e] at h
    exact .appL _ (.appL _ h)
  have s2 : LStep (app (app (lam (lam (app (app (tr x) (var 0)) (app (var 1) (var 0))))) (tr y)) (tr z))
      (app (lam (app (app (tr x) (var 0)) (app (tr y) (var 0)))) (tr z)) := by
    have e : Lam.sub (beta1 (tr y)) (lam (app (app (tr x) (var 0)) (app (var 1) (var 0))))
        = lam (app (app (tr x) (var 0)) (app (tr y) (var 0))) := by
      show lam (app (app (Lam.sub (Lam.up (beta1 (tr y))) (tr x)) (var 0))
        (app (Lam.ren Nat.succ (tr y)) (var 0))) = _
      rw [tr_sub, tr_ren]
    have h := LStep.beta (lam (app (app (tr x) (var 0)) (app (var 1) (var 0)))) (tr y)
    rw [e] at h
    exact .appL _ h
  have s3 : LStep (app (lam (app (app (tr x) (var 0)) (app (tr y) (var 0)))) (tr z))
      (app (app (tr x) (tr z)) (app (tr y) (tr z))) := by
    have e : Lam.sub (beta1 (tr z)) (app (app (tr x) (var 0)) (app (tr y) (var 0)))
        = app (app (tr x) (tr z)) (app (tr y) (tr z)) := by
      show app (app (Lam.sub (beta1 (tr z)) (tr x)) (tr z))
        (app (Lam.sub (beta1 (tr z)) (tr y)) (tr z)) = _
      rw [tr_sub, tr_sub]
    have h := LStep.beta (app (app (tr x) (var 0)) (app (tr y) (var 0))) (tr z)
    rw [e] at h
    exact h
  exact .step s1 (.step s2 (.single s3))

theorem tr_K (x y : Term) : LSteps (tr (.K ⬝ x ⬝ y)) (tr x) := by
  have s1 : LStep (app (app trK (tr x)) (tr y)) (app (lam (tr x)) (tr y)) := by
    have e : Lam.sub (beta1 (tr x)) (lam (var 1)) = lam (tr x) := by
      show lam (Lam.ren Nat.succ (tr x)) = _
      rw [tr_ren]
    have h := LStep.beta (lam (var 1)) (tr x)
    rw [e] at h
    exact .appL _ h
  have s2 : LStep (app (lam (tr x)) (tr y)) (tr x) := by
    have h := LStep.beta (tr x) (tr y)
    rw [tr_sub] at h
    exact h
  exact .step s1 (.single s2)

theorem tr_I (x : Term) : LSteps (tr (.I ⬝ x)) (tr x) :=
  .single (LStep.beta (var 0) (tr x))

/-- **Weak reduction is β-reduction of the translation.** -/
theorem tr_wstep {t u : Term} (h : WStep t u) : LSteps (tr t) (tr u) := by
  induction h with
  | S f g x => exact tr_S f g x
  | K x y => exact tr_K x y
  | I x => exact tr_I x
  | left x _ ih => exact LSteps.appL (tr x) ih
  | right f _ ih => exact LSteps.appR (tr f) ih

theorem tr_wsteps {t u : Term} (h : WSteps t u) : LSteps (tr t) (tr u) := by
  induction h with
  | refl t => exact .refl _
  | step h _ ih => exact (tr_wstep h).trans ih

/-- **`S K X` is the identity**, whatever `X` is. -/
theorem tr_SK (x : Term) : LSteps (tr (.S ⬝ .K ⬝ x)) (lam (var 0)) := by
  have s1 : LStep (app (app trS trK) (tr x))
      (app (lam (lam (app (app trK (var 0)) (app (var 1) (var 0))))) (tr x)) := by
    have e : Lam.sub (beta1 trK) (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))
        = lam (lam (app (app trK (var 0)) (app (var 1) (var 0)))) := rfl
    have h := LStep.beta (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0))))) trK
    rw [e] at h
    exact .appL _ h
  have s2 : LStep (app (lam (lam (app (app trK (var 0)) (app (var 1) (var 0))))) (tr x))
      (lam (app (app trK (var 0)) (app (tr x) (var 0)))) := by
    have e : Lam.sub (beta1 (tr x)) (lam (app (app trK (var 0)) (app (var 1) (var 0))))
        = lam (app (app trK (var 0)) (app (tr x) (var 0))) := by
      show lam (app (app trK (var 0)) (app (Lam.ren Nat.succ (tr x)) (var 0))) = _
      rw [tr_ren]
    have h := LStep.beta (lam (app (app trK (var 0)) (app (var 1) (var 0)))) (tr x)
    rw [e] at h
    exact h
  -- under the binder: `K 0 (X 0)` to `0`
  have s3 : LStep (app (app trK (var 0)) (app (tr x) (var 0)))
      (app (lam (var 1)) (app (tr x) (var 0))) :=
    .appL _ (LStep.beta (lam (var 1)) (var 0))
  have s4 : LStep (app (lam (var 1)) (app (tr x) (var 0))) (var 0) :=
    LStep.beta (var 1) (app (tr x) (var 0))
  exact .step s1 (.step s2 (.step (.lam s3) (.single (.lam s4))))

/-- **No quoter, for any encoding that separates `S K S` from `S K K`.**
    If the translations of their encodings have different β-normal forms, no
    closed `Q` reduces `Q M` to the encoding of `M` for every `M`. -/
theorem no_quote_of_separated (enc : Term → Term) {n₁ n₂ : Lam}
    (h₁ : LSteps (tr (enc (.S ⬝ .K ⬝ .S))) n₁) (w₁ : LNormal n₁)
    (h₂ : LSteps (tr (enc (.S ⬝ .K ⬝ .K))) n₂) (w₂ : LNormal n₂) (hne : n₁ ≠ n₂) :
    ¬ ∃ Q : Term, ∀ M : Term, WSteps (Q ⬝ M) (enc M) := by
  intro ⟨Q, hQ⟩
  -- both applications reach `Q (λz.z)`, and their quotations' normal forms
  have z₁ : LSteps (tr (Q ⬝ (.S ⬝ .K ⬝ .S))) (app (tr Q) (lam (var 0))) :=
    LSteps.appR (tr Q) (tr_SK .S)
  have z₂ : LSteps (tr (Q ⬝ (.S ⬝ .K ⬝ .K))) (app (tr Q) (lam (var 0))) :=
    LSteps.appR (tr Q) (tr_SK .K)
  have q₁ : LSteps (tr (Q ⬝ (.S ⬝ .K ⬝ .S))) n₁ := (tr_wsteps (hQ _)).trans h₁
  have q₂ : LSteps (tr (Q ⬝ (.S ⬝ .K ⬝ .K))) n₂ := (tr_wsteps (hQ _)).trans h₂
  obtain ⟨v₁, a₁, b₁⟩ := lsteps_confluent q₁ z₁
  obtain ⟨v₂, a₂, b₂⟩ := lsteps_confluent q₂ z₂
  have e₁ : v₁ = n₁ := w₁.steps_eq a₁
  have e₂ : v₂ = n₂ := w₂.steps_eq a₂
  rw [e₁] at b₁
  rw [e₂] at b₂
  exact hne (normal_unique b₁ b₂ w₁ w₂)

/-- The encoding of the metacircular paper: the object type
    `S | K | I | App term term`, each leaf its Scott constructor and an
    application the constructor `App` applied to the two encodings. -/
def quoteT : Term → Term
  | .S => toTerm (ctorO 0 0 4)
  | .K => toTerm (ctorO 0 1 4)
  | .I => toTerm (ctorO 0 2 4)
  | .app f a => toTerm (ctorO 2 3 4) ⬝ quoteT f ⬝ quoteT a

/-- The encodings of `S K S` and `S K K` have different β-normal forms,
    computed by the kernel. -/
theorem quote_separated :
    (match lnf 200 (tr (quoteT (.S ⬝ .K ⬝ .S))), lnf 200 (tr (quoteT (.S ⬝ .K ⬝ .K))) with
      | some a, some b => a != b
      | _, _ => false) = true := by
  decide +kernel

/-- **Proposition 3.1.**  No closed term over `{S, K, I}` quotes every closed
    term: none satisfies `Q M ↠ ⟨M⟩` for every `M`. -/
theorem no_quote : ¬ ∃ Q : Term, ∀ M : Term, WSteps (Q ⬝ M) (quoteT M) := by
  have h := quote_separated
  cases e₁ : lnf 200 (tr (quoteT (.S ⬝ .K ⬝ .S))) with
  | none => rw [e₁] at h; cases h
  | some a =>
    cases e₂ : lnf 200 (tr (quoteT (.S ⬝ .K ⬝ .K))) with
    | none => rw [e₁, e₂] at h; cases h
    | some b =>
      rw [e₁, e₂] at h
      have hne : a ≠ b := fun hab => by rw [hab] at h; simp at h
      obtain ⟨ha, wa⟩ := lnf_sound e₁
      obtain ⟨hb, wb⟩ := lnf_sound e₂
      exact no_quote_of_separated quoteT ha wa hb wb hne
