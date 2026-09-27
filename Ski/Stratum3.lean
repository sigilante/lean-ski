import Ski.Stratum2
import Ski.Cost
open Term

/-!
# Stratum 3: the fixed point, where fuel begins

The paper's third stratum extends the realizer language with a typed fixed
point, `fix : (A ⇒ A) ⇒ A`.  This is how `Y` enters a typed language, and
where strong normalization fails.  It is the only stratum in which the
glue's own redexes need fuel, and in which the third outcome, divergence,
arises in the glue.

**The extension.**  Constants are labels `FixLab`: a fixed point at each
type, or an atom.  Call-by-name reduction (`WHF`) is `WH` plus
`fix f ⇒ f (fix f)`.  The fixed point compiles to SKIjack's `Y`
(`Ycomb`), the combinator the compiler emits for recursion.

**Strong normalization fails** (`omegaF_diverges`).  `fix (λ x. x)` is typed
at every type (`omegaF_typed`) and has no call-by-name normal form.  So
fuel cannot be dispensed with: some typed realizer evaluates for ever.

**The fixed point is not always divergent** (`fixConst_evaluates`).
`fix (λ x. inl c)` reaches `inl c` in two steps.  So whether a `fix`
realizer halts depends on the realizer, and a fuel bound is the only
uniform treatment.

**Divergence, compiled** (`compiled_omegaF_diverges`).  The compiled term of
`fix (λ x. x)` is `Y ⬝ I` (`compiled_omegaF`), and it diverges in normal
order.  So it times out at every fuel (`compiled_omegaF_timeout`): the
third outcome, in the glue.  The proof follows a chain.  With
`B = S (S (K S) K) (K (S I I))`, `Y ⬝ I` reaches `B ⬝ I ⬝ (I ⬝ (B ⬝ I))`, and
each `B ⬝ I ⬝ (Iⁿ (B ⬝ I))` reaches the next with one more `I`.  Normal order
is deterministic, so a normal form would be reached from every member in
strictly fewer steps than from the one before.

**Without the fixed point, no fuel** (`fixfree_evaluates`,
`glue_converges`).  A closed, typed realizer without `fix` whose constants
have base types reduces to an injection at a sum type.  Glue without
constants compiles to a converging term.  Fuel comes from `fix`, and from
atoms, whose verifiers are opaque terms and may use `Y` themselves.
-/

-- ---------------------------------------------------------------------------
-- `Y ⬝ I` diverges
-- ---------------------------------------------------------------------------

/-- The second half of SKIjack's `Y`: `S (S (K S) K) (K (S I I))`. -/
def Bterm : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I))

theorem Ycomb_eq : Ycomb = S ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ Bterm := rfl

/-- `n` applications of `I`. -/
def iI : Nat → Term → Term
  | 0, t => t
  | n + 1, t => I ⬝ iI n t

theorem iI_steps (a : Term) : ∀ (n : Nat) (t : Term), StepsN n (iI n t ⬝ a) (t ⬝ a)
  | 0, _ => .refl _
  | n + 1, t => .step (.left a (.I _)) (iI_steps a n t)

/-- `B ⬝ I ⬝ x` reaches `x ⬝ (I ⬝ x)` in nine head steps, for every `x`. -/
theorem Bterm_steps (x : Term) : StepsN 9 (Bterm ⬝ I ⬝ x) (x ⬝ (I ⬝ x)) := by
  have hr : oiter 9 (Bterm.toO ⬝ₒ .I ⬝ₒ .var 0) = some (.var 0 ⬝ₒ (.I ⬝ₒ .var 0)) := by decide
  have h := Rz.oiter_stepsN 9 hr (fun _ => x)
  simp only [OTerm.close, close_toO] at h
  exact h

/-- The chain: `B ⬝ I ⬝ (Iⁿ⁺¹ (B ⬝ I))`. -/
def chainT (n : Nat) : Term := Bterm ⬝ I ⬝ iI (n + 1) (Bterm ⬝ I)

theorem chainT_step (n : Nat) : StepsN (9 + (n + 1)) (chainT n) (chainT (n + 1)) :=
  (Bterm_steps _).trans' (iI_steps (iI (n + 2) (Bterm ⬝ I)) (n + 1) (Bterm ⬝ I))

theorem Y_I_chain : Steps (Ycomb ⬝ I) (chainT 0) := iter_sound (k := 4) (by decide)

/-- No member of the chain reaches a weak head normal form. -/
theorem chainT_no_whnf : ∀ (m k : Nat) {v : Term}, StepsN m (chainT k) v → ¬ Whnf v := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro k v hm hv
    cases hs : chainT_step k with
    | step s rest =>
      cases StepsN.tail_lt s rest.steps hm hv with
      | intro m' h => exact ih m' h.1 (k + 1) h.2 hv

/-- **`Y ⬝ I` diverges.** -/
theorem Y_I_diverges : Diverges (Ycomb ⬝ I) := by
  intro v hv
  cases Steps.counted hv.1 with
  | intro n hn =>
    cases StepsN.tail Y_I_chain hn hv.2 with
    | intro m hm => exact chainT_no_whnf m 0 hm.2 hv.2

namespace Rz

open Tm

variable {β γ : Type}

-- ---------------------------------------------------------------------------
-- The realizer language with a fixed point
-- ---------------------------------------------------------------------------

/-- Constants: a fixed point at each type, or an atom. -/
inductive FixLab (β γ : Type) where
  | fix (A : Ty β)
  | atom (c : γ)

/-- The signature: `fix A : (A ⇒ A) ⇒ A`. -/
def sigF (sig : γ → Ty β) : FixLab β γ → Ty β
  | .fix A => .arr (.arr A A) A
  | .atom c => sig c

/-- The interpretation: `fix` is SKIjack's `Y`. -/
def ιF (ι : γ → Term) : FixLab β γ → Term
  | .fix _ => Ycomb
  | .atom c => ι c

/-- Call-by-name reduction with the fixed point. -/
inductive WHF : Tm (FixLab β γ) → Tm (FixLab β γ) → Prop
  | fixβ (A : Ty β) (f : Tm (FixLab β γ)) :
      WHF (.app (.const (.fix A)) f) (.app f (.app (.const (.fix A)) f))
  | beta (b a : Tm (FixLab β γ)) : WHF (.app (.lam b) a) (Tm.sub (beta1 a) b)
  | fstβ (a b : Tm (FixLab β γ)) : WHF (.fst (.pair a b)) a
  | sndβ (a b : Tm (FixLab β γ)) : WHF (.snd (.pair a b)) b
  | inlβ (a f g : Tm (FixLab β γ)) : WHF (.case (.inl a) f g) (.app f a)
  | inrβ (b f g : Tm (FixLab β γ)) : WHF (.case (.inr b) f g) (.app g b)
  | appL {f f' : Tm (FixLab β γ)} (a : Tm (FixLab β γ)) : WHF f f' → WHF (.app f a) (.app f' a)
  | fst {t t' : Tm (FixLab β γ)} : WHF t t' → WHF (.fst t) (.fst t')
  | snd {t t' : Tm (FixLab β γ)} : WHF t t' → WHF (.snd t) (.snd t')
  | caseS {s s' : Tm (FixLab β γ)} (f g : Tm (FixLab β γ)) :
      WHF s s' → WHF (.case s f g) (.case s' f g)

/-- Exactly `n` steps. -/
inductive WHFN : Nat → Tm (FixLab β γ) → Tm (FixLab β γ) → Prop
  | refl (t : Tm (FixLab β γ)) : WHFN 0 t t
  | step {n : Nat} {t t' u : Tm (FixLab β γ)} : WHF t t' → WHFN n t' u → WHFN (n + 1) t u

/-- `fix (λ x. x)`. -/
def omegaF (A : Ty β) : Tm (FixLab β γ) := .app (.const (.fix A)) (.lam (.var 0))

/-- `fix (λ x. x)` is typed, at every type. -/
theorem omegaF_typed (sig : γ → Ty β) (Γ : Nat → Ty β) (A : Ty β) :
    Typed (sigF sig) Γ (omegaF A : Tm (FixLab β γ)) A :=
  .app (.const _ (FixLab.fix A)) (.lam (.var _ 0))

theorem WHF.no_lam {b u : Tm (FixLab β γ)} (h : WHF (.lam b) u) : False := by cases h
theorem WHF.no_const {c : FixLab β γ} {u : Tm (FixLab β γ)} (h : WHF (.const c) u) : False := by
  cases h

/-- The reducts of `fix (λ x. x)` are itself and `(λ x. x) (fix (λ x. x))`. -/
theorem omegaF_reducts (A : Ty β) : ∀ {n : Nat} {u : Tm (FixLab β γ)}, WHFN n (omegaF A) u →
    u = omegaF A ∨ u = .app (.lam (.var 0)) (omegaF A) := by
  intro n
  induction n with
  | zero => intro u h; cases h; exact .inl rfl
  | succ n ih =>
    intro u h
    cases h with
    | step s rest =>
      -- one step from `omegaF A` or from its reduct returns into the pair
      have key : ∀ {t t' : Tm (FixLab β γ)}, (t = omegaF A ∨ t = .app (.lam (.var 0)) (omegaF A)) →
          WHF t t' → (t' = omegaF A ∨ t' = .app (.lam (.var 0)) (omegaF A)) := by
        intro t t' ht st
        cases ht with
        | inl e =>
          subst e
          cases st with
          | fixβ => exact .inr rfl
          | appL _ h => exact (h.no_const).elim
        | inr e =>
          subst e
          cases st with
          | beta => exact .inl rfl
          | appL _ h => exact (h.no_lam).elim
      have h1 := key (.inl rfl) s
      -- continue from the reduct, which is again in the pair
      have gen : ∀ {m : Nat} {t w : Tm (FixLab β γ)},
          (t = omegaF A ∨ t = .app (.lam (.var 0)) (omegaF A)) → WHFN m t w →
          (w = omegaF A ∨ w = .app (.lam (.var 0)) (omegaF A)) := by
        intro m t w ht hw
        induction hw with
        | refl => exact ht
        | step st _ ihw => exact ihw (key ht st)
      exact gen h1 rest

/-- **Strong normalization fails with the fixed point**: `fix (λ x. x)` has no
    call-by-name normal form; every reduct takes another step. -/
theorem omegaF_diverges (A : Ty β) {n : Nat} {u : Tm (FixLab β γ)} (h : WHFN n (omegaF A) u) :
    ∃ u', WHF u u' := by
  cases omegaF_reducts A h with
  | inl e => rw [e]; exact ⟨_, .fixβ A _⟩
  | inr e => rw [e]; exact ⟨_, .beta _ _⟩

/-- `fix (λ x. inl c)`. -/
def fixConst (A : Ty β) (c : γ) : Tm (FixLab β γ) :=
  .app (.const (.fix (.sum A A))) (.lam (.inl (.const (.atom c))))

/-- **The fixed point does not always diverge**: `fix (λ x. inl c)` reaches
    `inl c` in two steps. -/
theorem fixConst_evaluates (A : Ty β) (c : γ) :
    WHFN 2 (fixConst A c) (.inl (.const (.atom c))) :=
  .step (.fixβ _ _) (.step (.beta _ _) (.refl _))

-- ---------------------------------------------------------------------------
-- Compiled: the third outcome
-- ---------------------------------------------------------------------------

/-- The compiled term of `fix (λ x. x)` is `Y ⬝ I`. -/
theorem compiled_omegaF (ι : γ → Term) (A : Ty β) :
    compiled (ιF ι) (omegaF A : Tm (FixLab β γ)) = Ycomb ⬝ I := rfl

/-- **Divergence, compiled**: the compiled term of `fix (λ x. x)` diverges in
    normal order. -/
theorem compiled_omegaF_diverges (ι : γ → Term) (A : Ty β) :
    Diverges (compiled (ιF ι) (omegaF A : Tm (FixLab β γ))) := by
  rw [compiled_omegaF]
  exact Y_I_diverges

/-- **The third outcome**: it times out at every fuel. -/
theorem compiled_omegaF_timeout (ι : γ → Term) (A : Ty β) (k : Nat) :
    evalF k (compiled (ιF ι) (omegaF A : Tm (FixLab β γ))) = none :=
  (diverges_iff_fuel _).1 (compiled_omegaF_diverges ι A) k

/-- The productive fixed point, compiled, converges: `Y` unrolls once and the
    body returns the compiled `inl c` without using the recursive argument,
    in 12 contractions. -/
theorem compiled_fixConst_converges :
    runF 13 (compiled (ιF (fun (_ : Unit) => K))
      (fixConst (β := Unit) (.base ()) () : Tm (FixLab Unit Unit))) =
      some (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K ⬝ K), 12) := by
  decide

-- ---------------------------------------------------------------------------
-- Without the fixed point, no fuel
-- ---------------------------------------------------------------------------

/-- **Without the fixed point, evaluation needs no fuel**: a closed, typed
    realizer without `fix`, whose constants have base types, reduces by
    call-by-name to an injection at a sum type. -/
theorem fixfree_evaluates {sig : γ → Ty β} (hsig : ∀ c, ∃ b, sig c = .base b)
    {Γ : Nat → Ty β} {t : Tm γ} {A B : Ty β} (h : Typed sig Γ t (.sum A B))
    (hc : closedAt 0 t) : ∃ n v, WHN n t v ∧ IsInj v :=
  evaluates_inj hsig h hc

end Rz
