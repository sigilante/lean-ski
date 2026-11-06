import Ski.NoLift

open Term

/-!
# A behavioural lift at `Bool → Bool`

The other side of `NoLift.no_lift`.  At `Nat → Bool` no closed term lifts a
total function to an agreeing code.  At `Bool → Bool` one does: probe the
function at both booleans and emit the code of one of the four functions
`Bool → Bool`,

    liftBB f = f true (f false ⟨K K⟩ ⟨I⟩) (f false ⟨not⟩ ⟨K (K I)⟩)

(`f true` selects the outer pair, `f false` the inner).  The quotations are
of four fixed closed terms, written at compile time; no live term is quoted.
The lift canonicalizes: two functions with the same values get the same code.

`lift_bool : LiftBB liftBB` is stated exactly as `NoLift.LiftNB`, with the
booleans for the numerals, so the two theorems put the staging line between
these two types.

The booleans here are `K` (true) and `K I` (false), SKI's.  Nock's are
loobeans: the atom `0` is yes and `1` is no.  A lift transported to Nock
reads them through the atom encoding, so `0` must map to `K`.
-/

namespace LiftBool

open NoLift

/-- `not = λ b. b false true`. -/
def notT : Term := S ⬝ (S ⬝ I ⬝ (K ⬝ (K ⬝ I))) ⬝ (K ⬝ K)

/-- The canonical function with values `t` at `true` and `e` at `false`. -/
def canon : Bool → Bool → Term
  | true, true => K ⬝ K
  | true, false => I
  | false, true => notT
  | false, false => K ⬝ (K ⬝ I)

theorem canon_spec : ∀ (t e b : Bool), WSteps (canon t e ⬝ boolT b) (boolT (if b then t else e))
  | true, true, b => by cases b <;> exact .single (.K _ _)
  | true, false, true => .single (.I _)
  | true, false, false => .single (.I _)
  | false, true, true => (iter_sound (k := 5) rfl : Steps (notT ⬝ K) (K ⬝ I)).weak
  | false, true, false => (iter_sound (k := 6) rfl : Steps (notT ⬝ (K ⬝ I)) K).weak
  | false, false, b => by cases b <;> exact .single (.K _ _)

/-- The body of the lift, over `f` (0). -/
def liftBody : OTerm :=
  .var 0 ⬝ₒ K.toO ⬝ₒ
    (.var 0 ⬝ₒ (K ⬝ I).toO ⬝ₒ (quoteT (canon true true)).toO ⬝ₒ (quoteT (canon true false)).toO) ⬝ₒ
    (.var 0 ⬝ₒ (K ⬝ I).toO ⬝ₒ (quoteT (canon false true)).toO ⬝ₒ (quoteT (canon false false)).toO)

/-- **The lift.** -/
def liftBB : Term := toTerm (absN [0] liftBody)

/-- `f` is total on the booleans. -/
def TotalB (f : Term) : Prop := ∀ b, ∃ r : Bool, WSteps (f ⬝ boolT b) (boolT r)

/-- `L` lifts at `Bool → Bool`: as `NoLift.LiftNB`, the booleans for the
    numerals. -/
def LiftBB (L : Term) : Prop :=
  ∀ f, TotalB f → ∃ c, WSteps (L ⬝ f) (quoteT c) ∧
    ∀ (b r : Bool), WSteps (f ⬝ boolT b) (boolT r) → WSteps (c ⬝ boolT b) (boolT r)

/-- A boolean selects. -/
theorem sel (r : Bool) (x y : Term) : WSteps (boolT r ⬝ x ⬝ y) (if r then x else y) := by
  cases r with
  | true => exact .single (.K _ _)
  | false => exact (WSteps.left _ (.single (.K _ _))).trans (.single (.I _))

/-- A term reaches at most one boolean. -/
theorem bool_unique {t : Term} {r r' : Bool} (h : WSteps t (boolT r)) (h' : WSteps t (boolT r')) :
    r = r' := by
  cases r <;> cases r'
  · rfl
  · exact (bool_disjoint h h').elim
  · exact (bool_disjoint h' h).elim
  · rfl

/-- **`lift_bool`**: `liftBB` lifts every total `f : Bool → Bool` to the code
    of the canonical function with its values. -/
theorem lift_bool : LiftBB liftBB := by
  intro f hf
  obtain ⟨t, ht⟩ := hf true
  obtain ⟨e, he⟩ := hf false
  refine ⟨canon t e, ?_, ?_⟩
  · have h := absN_beta_close [0] liftBody (fun _ => K) [f] rfl
    simp only [liftBody, OTerm.close, close_toO, overrideC, updC, if_pos] at h
    have hF (a b : Term) : WSteps (f ⬝ (K ⬝ I) ⬝ a ⬝ b) (if e then a else b) :=
      (WSteps.left _ (WSteps.left _ he)).trans (sel e a b)
    have hT (a b : Term) : WSteps (f ⬝ K ⬝ a ⬝ b) (if t then a else b) :=
      (WSteps.left _ (WSteps.left _ ht)).trans (sel t a b)
    refine h.trans ((hT _ _).trans ?_)
    cases t <;> cases e <;> simpa using hF _ _
  · intro b r hr
    have hc := canon_spec t e b
    cases b with
    | true => rw [bool_unique hr ht]; simpa using hc
    | false => rw [bool_unique hr he]; simpa using hc

/-- The lift canonicalizes: functions with the same values get one code. -/
theorem lift_canonical {f g : Term} {t e : Bool}
    (hft : WSteps (f ⬝ K) (boolT t)) (hfe : WSteps (f ⬝ (K ⬝ I)) (boolT e))
    (hgt : WSteps (g ⬝ K) (boolT t)) (hge : WSteps (g ⬝ (K ⬝ I)) (boolT e)) :
    ∃ c, WSteps (liftBB ⬝ f) (quoteT c) ∧ WSteps (liftBB ⬝ g) (quoteT c) := by
  have key : ∀ h : Term, WSteps (h ⬝ K) (boolT t) → WSteps (h ⬝ (K ⬝ I)) (boolT e) →
      WSteps (liftBB ⬝ h) (quoteT (canon t e)) := by
    intro h h1 h0
    have hb := absN_beta_close [0] liftBody (fun _ => K) [h] rfl
    simp only [liftBody, OTerm.close, close_toO, overrideC, updC, if_pos] at hb
    have hF (a b : Term) : WSteps (h ⬝ (K ⬝ I) ⬝ a ⬝ b) (if e then a else b) :=
      (WSteps.left _ (WSteps.left _ h0)).trans (sel e a b)
    have hT (a b : Term) : WSteps (h ⬝ K ⬝ a ⬝ b) (if t then a else b) :=
      (WSteps.left _ (WSteps.left _ h1)).trans (sel t a b)
    refine hb.trans ((hT _ _).trans ?_)
    cases t <;> cases e <;> simpa using hF _ _
  exact ⟨canon t e, key f hft hfe, key g hgt hge⟩

end LiftBool
