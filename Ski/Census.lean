import Ski.Stratum3
import Ski.Sigma

/-!
# The census: stratifying realizers by the additive count

The paper's census sorts realizers into three strata by the additive
occurrence count: across an application occurrences add, and across the
branches of a case they take the larger.  The census is on the source,
because bracket abstraction duplicates a variable shared by a case's
branches into both continuations, so raw counts on compiled terms depend on
the compiler's conventions.

**The census** (`census`) is computable:
- stratum 3 if a fixed point occurs (`hasFix`);
- stratum 1 if every λ's variable occurs at most once under the additive
  count (`affB`, which decides `AffA`: `affB_iff`);
- stratum 2 otherwise.

It is exact (`census_one_iff`, `census_two_iff`, `census_three_iff`).

**Each stratum has its theorem**, for the realizer language with the fixed
point (`WHF`):
- Stratum 1 evaluates in fewer call-by-name steps than its additive size
  (`census_one_bound`).
- Strata 1 and 2, typed, closed and at a sum type, evaluate to an injection
  (`census_le_two_evaluates`), without fuel.  A term without `fix` reduces
  under `WHF` exactly as under `WH` (`WHF.of_fixFree`).
- Stratum 2 has no elementary bound (`no_elementary_bound`,
  `Ski/Stratum2.lean`).
- Stratum 3 contains a typed term that diverges (`census_three_diverges`).

**The additive rule is needed** (`additive_rule_needed`).  `sharedT` shares
a variable across a case's branches.  The raw count scores it as
contraction, but it is additively affine, so the census puts it in stratum
1, where its bound holds.

**The census, computed** (`census_table`): the glue of the Σ-algebra is in
stratum 1, and so is the prover's composition of a 2-of-3 threshold plan.
Swapping a pair's halves and the tower of twos are in stratum 2.
`fix (λ x. x)` is in stratum 3.
-/

namespace Rz

open Tm

variable {β γ : Type}

-- ---------------------------------------------------------------------------
-- The census
-- ---------------------------------------------------------------------------

/-- A fixed point occurs, for a given test of which constants are fixed points. -/
def hasFix (isFix : γ → Bool) : Tm γ → Bool
  | .var _ => false
  | .const c => isFix c
  | .app f a => hasFix isFix f || hasFix isFix a
  | .lam b => hasFix isFix b
  | .pair a b => hasFix isFix a || hasFix isFix b
  | .fst t => hasFix isFix t
  | .snd t => hasFix isFix t
  | .inl a => hasFix isFix a
  | .inr b => hasFix isFix b
  | .case s f g => hasFix isFix s || hasFix isFix f || hasFix isFix g

/-- The decision procedure for additive affinity. -/
def affB : Tm γ → Bool
  | .var _ => true
  | .const _ => true
  | .app f a => affB f && affB a
  | .lam b => decide (acnt 0 b ≤ 1) && affB b
  | .pair a b => affB a && affB b
  | .fst t => affB t
  | .snd t => affB t
  | .inl a => affB a
  | .inr b => affB b
  | .case s f g => affB s && affB f && affB g

/-- **`affB` decides additive affinity.** -/
theorem affB_iff : ∀ t : Tm γ, affB t = true ↔ AffA t
  | .var _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | .const _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | .app f a => by
    show (affB f && affB a) = true ↔ AffA f ∧ AffA a
    rw [Bool.and_eq_true, affB_iff f, affB_iff a]
  | .lam b => by
    show (decide (acnt 0 b ≤ 1) && affB b) = true ↔ acnt 0 b ≤ 1 ∧ AffA b
    rw [Bool.and_eq_true, decide_eq_true_iff, affB_iff b]
  | .pair a b => by
    show (affB a && affB b) = true ↔ AffA a ∧ AffA b
    rw [Bool.and_eq_true, affB_iff a, affB_iff b]
  | .fst t => affB_iff t
  | .snd t => affB_iff t
  | .inl a => affB_iff a
  | .inr b => affB_iff b
  | .case s f g => by
    show (affB s && affB f && affB g) = true ↔ AffA s ∧ AffA f ∧ AffA g
    rw [Bool.and_eq_true, Bool.and_eq_true, affB_iff s, affB_iff f, affB_iff g, and_assoc]

/-- **The census**: stratum 3 if a fixed point occurs, 1 if additively
    affine, 2 otherwise. -/
def census (isFix : γ → Bool) (t : Tm γ) : Nat :=
  if hasFix isFix t then 3 else if affB t then 1 else 2

theorem census_one_iff (isFix : γ → Bool) (t : Tm γ) :
    census isFix t = 1 ↔ hasFix isFix t = false ∧ AffA t := by
  unfold census
  cases hf : hasFix isFix t with
  | true =>
    rw [if_pos rfl]
    exact ⟨fun h => absurd h (by decide), fun h => by cases h.1⟩
  | false =>
    rw [if_neg Bool.false_ne_true]
    cases ha : affB t with
    | true =>
      rw [if_pos rfl]
      exact ⟨fun _ => ⟨rfl, (affB_iff t).1 ha⟩, fun _ => rfl⟩
    | false =>
      rw [if_neg Bool.false_ne_true]
      exact ⟨fun h => absurd h (by decide), fun h => by rw [(affB_iff t).2 h.2] at ha; cases ha⟩

theorem census_two_iff (isFix : γ → Bool) (t : Tm γ) :
    census isFix t = 2 ↔ hasFix isFix t = false ∧ ¬ AffA t := by
  unfold census
  cases hf : hasFix isFix t with
  | true =>
    rw [if_pos rfl]
    exact ⟨fun h => absurd h (by decide), fun h => by cases h.1⟩
  | false =>
    rw [if_neg Bool.false_ne_true]
    cases ha : affB t with
    | true =>
      rw [if_pos rfl]
      exact ⟨fun h => absurd h (by decide), fun h => absurd ((affB_iff t).1 ha) h.2⟩
    | false =>
      rw [if_neg Bool.false_ne_true]
      exact ⟨fun _ => ⟨rfl, fun h => by rw [(affB_iff t).2 h] at ha; cases ha⟩, fun _ => rfl⟩

theorem census_three_iff (isFix : γ → Bool) (t : Tm γ) :
    census isFix t = 3 ↔ hasFix isFix t = true := by
  unfold census
  cases hasFix isFix t with
  | true => rw [if_pos rfl]; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | false =>
    rw [if_neg Bool.false_ne_true]
    constructor
    · intro h
      cases ha : affB t with
      | true => rw [ha, if_pos rfl] at h; exact absurd h (by decide)
      | false => rw [ha, if_neg Bool.false_ne_true] at h; exact absurd h (by decide)
    · intro h; cases h

-- ---------------------------------------------------------------------------
-- Each stratum's theorem, with the fixed point
-- ---------------------------------------------------------------------------

/-- The fixed points among the constants of the language with `fix`. -/
def isFixF : FixLab β γ → Bool
  | .fix _ => true
  | .atom _ => false

theorem hasFix_ren (isFix : γ → Bool) : ∀ (t : Tm γ) (ξ : Nat → Nat),
    hasFix isFix (ren ξ t) = hasFix isFix t
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .app f a, ξ => by simp only [ren, hasFix, hasFix_ren isFix f, hasFix_ren isFix a]
  | .lam b, ξ => by simp only [ren, hasFix, hasFix_ren isFix b]
  | .pair a b, ξ => by simp only [ren, hasFix, hasFix_ren isFix a, hasFix_ren isFix b]
  | .fst t, ξ => by simp only [ren, hasFix, hasFix_ren isFix t]
  | .snd t, ξ => by simp only [ren, hasFix, hasFix_ren isFix t]
  | .inl a, ξ => by simp only [ren, hasFix, hasFix_ren isFix a]
  | .inr b, ξ => by simp only [ren, hasFix, hasFix_ren isFix b]
  | .case s f g, ξ => by
    simp only [ren, hasFix, hasFix_ren isFix s, hasFix_ren isFix f, hasFix_ren isFix g]

theorem hasFix_sub (isFix : γ → Bool) : ∀ (t : Tm γ) (σ : Nat → Tm γ),
    hasFix isFix t = false → (∀ i, hasFix isFix (σ i) = false) → hasFix isFix (Tm.sub σ t) = false
  | .var i, _, _, hσ => hσ i
  | .const _, _, h, _ => h
  | .app f a, σ, h, hσ => by
    have h' := Bool.or_eq_false_iff.1 h
    show (hasFix isFix (Tm.sub σ f) || hasFix isFix (Tm.sub σ a)) = false
    rw [hasFix_sub isFix f σ h'.1 hσ, hasFix_sub isFix a σ h'.2 hσ]; rfl
  | .lam b, σ, h, hσ => by
    refine hasFix_sub isFix b (up σ) h fun i => ?_
    cases i with
    | zero => rfl
    | succ i => show hasFix isFix (ren Nat.succ (σ i)) = false; rw [hasFix_ren]; exact hσ i
  | .pair a b, σ, h, hσ => by
    have h' := Bool.or_eq_false_iff.1 h
    show (hasFix isFix (Tm.sub σ a) || hasFix isFix (Tm.sub σ b)) = false
    rw [hasFix_sub isFix a σ h'.1 hσ, hasFix_sub isFix b σ h'.2 hσ]; rfl
  | .fst t, σ, h, hσ => hasFix_sub isFix t σ h hσ
  | .snd t, σ, h, hσ => hasFix_sub isFix t σ h hσ
  | .inl a, σ, h, hσ => hasFix_sub isFix a σ h hσ
  | .inr b, σ, h, hσ => hasFix_sub isFix b σ h hσ
  | .case s f g, σ, h, hσ => by
    have h' := Bool.or_eq_false_iff.1 h
    have h'' := Bool.or_eq_false_iff.1 h'.1
    show (hasFix isFix (Tm.sub σ s) || hasFix isFix (Tm.sub σ f) || hasFix isFix (Tm.sub σ g)) = false
    rw [hasFix_sub isFix s σ h''.1 hσ, hasFix_sub isFix f σ h''.2 hσ, hasFix_sub isFix g σ h'.2 hσ]
    rfl

/-- **Without a fixed point, the fixed point's reduction is plain call-by-name.** -/
theorem WHF.of_fixFree {t u : Tm (FixLab β γ)} (h : WHF t u) (ht : hasFix isFixF t = false) :
    WH t u ∧ hasFix isFixF u = false := by
  induction h with
  | fixβ A f => cases ht
  | beta b a =>
    have h' := Bool.or_eq_false_iff.1 ht
    refine ⟨.beta b a, hasFix_sub isFixF b (beta1 a) h'.1 fun i => ?_⟩
    cases i with
    | zero => exact h'.2
    | succ i => rfl
  | fstβ a b => exact ⟨.fstβ a b, (Bool.or_eq_false_iff.1 ht).1⟩
  | sndβ a b => exact ⟨.sndβ a b, (Bool.or_eq_false_iff.1 ht).2⟩
  | inlβ a f g =>
    have h' := Bool.or_eq_false_iff.1 ht
    have h'' := Bool.or_eq_false_iff.1 h'.1
    refine ⟨.inlβ a f g, ?_⟩
    show (hasFix isFixF f || hasFix isFixF a) = false
    rw [h''.2, show hasFix isFixF a = false from h''.1]; rfl
  | inrβ b f g =>
    have h' := Bool.or_eq_false_iff.1 ht
    have h'' := Bool.or_eq_false_iff.1 h'.1
    refine ⟨.inrβ b f g, ?_⟩
    show (hasFix isFixF g || hasFix isFixF b) = false
    rw [h'.2, show hasFix isFixF b = false from h''.1]; rfl
  | appL a _ ih =>
    have h' := Bool.or_eq_false_iff.1 ht
    have r := ih h'.1
    refine ⟨.appL a r.1, ?_⟩
    show (hasFix isFixF _ || hasFix isFixF a) = false
    rw [r.2, h'.2]; rfl
  | fst _ ih => have r := ih ht; exact ⟨.fst r.1, r.2⟩
  | snd _ ih => have r := ih ht; exact ⟨.snd r.1, r.2⟩
  | caseS f g _ ih =>
    have h' := Bool.or_eq_false_iff.1 ht
    have h'' := Bool.or_eq_false_iff.1 h'.1
    have r := ih h''.1
    refine ⟨.caseS f g r.1, ?_⟩
    show (hasFix isFixF _ || hasFix isFixF f || hasFix isFixF g) = false
    rw [r.2, h''.2, h'.2]; rfl

theorem WHFN.of_fixFree {n : Nat} {t u : Tm (FixLab β γ)} (h : WHFN n t u)
    (ht : hasFix isFixF t = false) : WHN n t u := by
  induction h with
  | refl => exact .refl _
  | step s _ ih =>
    have r := s.of_fixFree ht
    exact .step r.1 (ih r.2)

theorem WH.toWHF {t u : Tm (FixLab β γ)} (h : WH t u) : WHF t u := by
  induction h with
  | beta b a => exact .beta b a
  | fstβ a b => exact .fstβ a b
  | sndβ a b => exact .sndβ a b
  | inlβ a f g => exact .inlβ a f g
  | inrβ b f g => exact .inrβ b f g
  | appL a _ ih => exact .appL a ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | caseS f g _ ih => exact .caseS f g ih

theorem WHN.toWHFN {n : Nat} {t u : Tm (FixLab β γ)} (h : WHN n t u) : WHFN n t u := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step s.toWHF ih

theorem census_hasFix {isFix : γ → Bool} {t : Tm γ} (h : census isFix t ≤ 2) :
    hasFix isFix t = false := by
  cases hf : hasFix isFix t with
  | false => rfl
  | true => unfold census at h; rw [hf, if_pos rfl] at h; exact absurd h (by decide)

/-- **Stratum 1's theorem**: fewer call-by-name steps than the additive size,
    in the language with the fixed point. -/
theorem census_one_bound {t u : Tm (FixLab β γ)} {n : Nat} (h : census isFixF t = 1)
    (hn : WHFN n t u) : n < asz t := by
  have hc := (census_one_iff isFixF t).1 h
  exact wh_steps_lt (hn.of_fixFree hc.1) hc.2

/-- A signature for a term without fixed points: every fixed point at a base
    type, so that canonical forms apply. -/
def sigB (sig : γ → Ty β) (b0 : β) : FixLab β γ → Ty β
  | .fix _ => .base b0
  | .atom c => sig c

theorem Typed.unfix {sig : γ → Ty β} (b0 : β) {Γ : Nat → Ty β} {t : Tm (FixLab β γ)} {A : Ty β}
    (h : Typed (sigF sig) Γ t A) (ht : hasFix isFixF t = false) : Typed (sigB sig b0) Γ t A := by
  induction h with
  | var Γ n => exact .var Γ n
  | const Γ c =>
    cases c with
    | fix _ => cases ht
    | atom c => exact .const Γ (FixLab.atom c)
  | lam _ ih => exact .lam (ih ht)
  | app _ _ ihf iha =>
    have h' := Bool.or_eq_false_iff.1 ht
    exact .app (ihf h'.1) (iha h'.2)
  | pair _ _ iha ihb =>
    have h' := Bool.or_eq_false_iff.1 ht
    exact .pair (iha h'.1) (ihb h'.2)
  | fst _ ih => exact .fst (ih ht)
  | snd _ ih => exact .snd (ih ht)
  | inl _ ih => exact .inl (ih ht)
  | inr _ ih => exact .inr (ih ht)
  | case _ _ _ ihs ihf ihg =>
    have h' := Bool.or_eq_false_iff.1 ht
    have h'' := Bool.or_eq_false_iff.1 h'.1
    exact .case (ihs h''.1) (ihf h''.2) (ihg h'.2)

/-- **Strata 1 and 2 need no fuel**: a closed, typed realizer of census at
    most 2, at a sum type, whose atoms have base types, evaluates to an
    injection. -/
theorem census_le_two_evaluates {sig : γ → Ty β} (hsig : ∀ c, ∃ b, sig c = .base b) (b0 : β)
    {Γ : Nat → Ty β} {t : Tm (FixLab β γ)} {A B : Ty β} (hcen : census isFixF t ≤ 2)
    (h : Typed (sigF sig) Γ t (.sum A B)) (hc : closedAt 0 t) :
    ∃ n v, WHFN n t v ∧ IsInj v := by
  have hf := census_hasFix hcen
  have hsigB : ∀ c, ∃ b, sigB sig b0 c = .base b := by
    intro c
    cases c with
    | fix _ => exact ⟨b0, rfl⟩
    | atom c => exact hsig c
  cases evaluates_inj hsigB (h.unfix b0 hf) hc with
  | intro n h' => cases h' with
    | intro v h' => exact ⟨n, v, h'.1.toWHFN, h'.2⟩

/-- **Stratum 3 contains divergence**: `fix (λ x. x)` is in stratum 3, typed,
    and every reduct takes another step. -/
theorem census_three_diverges (A : Ty β) :
    census isFixF (omegaF A : Tm (FixLab β γ)) = 3 ∧
    ∀ {n : Nat} {u : Tm (FixLab β γ)}, WHFN n (omegaF A) u → ∃ u', WHF u u' :=
  ⟨rfl, fun h => omegaF_diverges A h⟩

-- ---------------------------------------------------------------------------
-- The additive rule, and the census computed
-- ---------------------------------------------------------------------------

/-- **The additive rule is needed**: `sharedT` shares a variable across a
    case's branches.  The raw count scores it as contraction; the additive
    count, and so the census, puts it in stratum 1. -/
theorem additive_rule_needed :
    ¬ Tm.Aff sharedT ∧ AffA sharedT ∧ census (fun e : Empty => e.elim) sharedT = 1 :=
  ⟨sharedT_not_aff, sharedT_affA, (census_one_iff _ _).2 ⟨rfl, sharedT_affA⟩⟩

/-- The tower of twos is in stratum 2 at every height: `two` uses its
    function twice. -/
theorem census_evalT (k : Nat) : census (fun _ : Unit => false) (evalT k trueT) = 2 := by
  refine (census_two_iff _ _).2 ⟨?_, fun h => ?_⟩
  · show (hasFix _ (towerT k) || hasFix _ togT || hasFix _ trueT) = false
    have : ∀ k, hasFix (fun _ : Unit => false) (towerT k : Tm Unit) = false := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => show (hasFix _ (towerT k) || _) = false; rw [ih]; rfl
    rw [this]; rfl
  · have ht : ∀ k, AffA (towerT k : Tm Unit) → False := by
      intro k
      induction k with
      | zero => intro h; exact absurd h.1 (by decide)
      | succ k ih => intro h; exact ih h.1
    exact ht k h.1.1

/-- The 2-of-3 threshold plan proving components 0 and 2. -/
def plan2of3 : Plan (thrF 2 [.atom 0, .atom 1, .atom 2]) :=
  .inl (.and (.atom 0) (.inr (.inl (.and (.atom 2) .top))))

/-- **The census, computed.** -/
theorem census_table :
    census (fun e : Empty => e.elim) idT = 1 ∧
    census (fun e : Empty => e.elim) andI = 1 ∧
    census (fun e : Empty => e.elim) fstE = 1 ∧
    census (fun e : Empty => e.elim) caseE = 1 ∧
    census (fun e : Empty => e.elim) orComm = 1 ∧
    census (fun e : Empty => e.elim) thrTake = 1 ∧
    census (fun e : Empty => e.elim) thrSkip = 1 ∧
    census (fun e : Empty => e.elim) (thrWeaken 2 [.atom 0, .atom 1, .atom 2]) = 1 ∧
    census (fun e : Empty => e.elim) plan2of3.compose = 1 ∧
    census (fun e : Empty => e.elim) swapT = 2 ∧
    census (fun _ : Unit => false) (evalT 3 trueT) = 2 ∧
    census isFixF (omegaF (.base ()) : Tm (FixLab Unit Unit)) = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, census_evalT 3, rfl⟩ <;> decide

end Rz
