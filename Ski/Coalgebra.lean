import Ski.NatLift

open Term

/-!
# Kavvos's second coalgebra law for the behavioural lifts

A behavioural lift `α : A → □A` is a Q-coalgebra in Kavvos's sense (*On the
Semantics of Intensionality and Intensional Recursion*, Def. 33) when
`ε ∘ α ∼ id` (our agreement clause) and `δ ∘ α ∼ □α ∘ α`.  Here `δ` is
re-encoding (`Requote.R`) and `□α` acts on a code `⟨t⟩` as the code of `α t`,
`App ⟨α⟩ ⟨t⟩`.  For a lift with `α f ↠ ⟨c⟩`:

    δ (α f)     ↠ R ⟨c⟩             ↠ ⟨⟨c⟩⟩
    □α (α f)    = App ⟨α⟩ (α f)     ↠ App ⟨α⟩ ⟨c⟩  =  ⟨α c⟩

So the law holds, *under the box*, exactly when `α c ↠ ⟨c⟩`: the lift is
idempotent on its own outputs.  Each of the three lifts is: its output term meets
its own hypothesis with the same table, and canonicality returns the same code.

- `bool_idem`, `nat_idem`, `cantor_idem`: idempotence.
- `bool_coalg2`, `nat_coalg2`, `cantor_coalg2`: the second law, as
  `δ (α f) ↠ ⟨⟨c⟩⟩` and `□α (α f) ↠ ⟨α c⟩` with `α c ↠ ⟨c⟩`: the two sides
  are codes of convertible terms.
-/

namespace Coalgebra

open NoLift LiftBool Search CantorLift NatLift

-- ---------------------------------------------------------------------------
-- Idempotence
-- ---------------------------------------------------------------------------

/-- A term reaching a boolean at both inputs is total. -/
theorem canon_total (t e : Bool) : TotalB (canon t e) := fun b =>
  ⟨_, canon_spec t e b⟩

/-- `liftBB` sends any `f` with values `t, e` to the code of `canon t e`. -/
theorem lift_code {f : Term} {t e : Bool} (hT : WSteps (f ⬝ K) (boolT t))
    (hF : WSteps (f ⬝ (K ⬝ I)) (boolT e)) : WSteps (liftBB ⬝ f) (quoteT (canon t e)) := by
  have h := absN_beta_close [0] liftBody (fun _ => K) [f] rfl
  simp only [liftBody, OTerm.close, close_toO, overrideC, updC, if_pos, appT] at h
  have hsF (a b : Term) : WSteps (f ⬝ (K ⬝ I) ⬝ a ⬝ b) (if e then a else b) :=
    (WSteps.left _ (WSteps.left _ hF)).trans (sel e a b)
  have hsT (a b : Term) : WSteps (f ⬝ K ⬝ a ⬝ b) (if t then a else b) :=
    (WSteps.left _ (WSteps.left _ hT)).trans (sel t a b)
  refine h.trans ((hsT _ _).trans ?_)
  cases t <;> cases e <;> simpa [canon] using hsF _ _

/-- `liftBB` is idempotent on its outputs. -/
theorem bool_idem (t e : Bool) : WSteps (liftBB ⬝ canon t e) (quoteT (canon t e)) :=
  lift_code (canon_spec t e true) (canon_spec t e false)

/-- `natL`'s output term is local with the same table, so `natL` is
    idempotent on its outputs. -/
theorem nat_idem (m : Nat) (φ : Nat → Bool) :
    WSteps (natL ⬝ (evalNT ⬝ DN m φ)) (quoteT (evalNT ⬝ DN m φ)) :=
  (nat_lift (evalN_spec m φ)).1

/-- `cantorL`'s output term is local with the same table, so `cantorL` is
    idempotent on its outputs. -/
theorem cantor_idem (m : Nat) (φ : List Bool → Bool) :
    WSteps (cantorL ⬝ (evalT ⬝ D m φ)) (quoteT (evalT ⬝ D m φ)) :=
  (cantor_lift (fun w hw s hs => eval_spec m φ w s hw hs)).1

-- ---------------------------------------------------------------------------
-- The second law
-- ---------------------------------------------------------------------------

/-- `□α`, on a code: `App ⟨α⟩`. -/
def boxMap (α x : Term) : Term := Requote.appC ⬝ quoteT α ⬝ x

/-- **The second law, generically**: if `α f ↠ ⟨c⟩` and `α c ↠ ⟨c⟩`, then
    `δ (α f) ↠ ⟨⟨c⟩⟩` and `□α (α f) ↠ ⟨α c⟩`, codes of the convertible terms
    `⟨c⟩` and `α c`. -/
theorem coalg2 {α f c : Term} (hf : WSteps (α ⬝ f) (quoteT c)) (hc : WSteps (α ⬝ c) (quoteT c)) :
    WSteps (Requote.R ⬝ (α ⬝ f)) (quoteT (quoteT c)) ∧
    WSteps (boxMap α (α ⬝ f)) (quoteT (α ⬝ c)) ∧
    WSteps (α ⬝ c) (quoteT c) :=
  ⟨(WSteps.right _ hf).trans (Requote.requote c), WSteps.right _ hf, hc⟩

theorem bool_coalg2 {f : Term} {t e : Bool} (ht : WSteps (f ⬝ K) (boolT t))
    (he : WSteps (f ⬝ (K ⬝ I)) (boolT e)) :
    WSteps (Requote.R ⬝ (liftBB ⬝ f)) (quoteT (quoteT (canon t e))) ∧
    WSteps (boxMap liftBB (liftBB ⬝ f)) (quoteT (liftBB ⬝ canon t e)) ∧
    WSteps (liftBB ⬝ canon t e) (quoteT (canon t e)) :=
  coalg2 (lift_code ht he) (bool_idem t e)

theorem nat_coalg2 {m : Nat} {φ : Nat → Bool} {f : Term} (hf : NLocal m φ f) :
    WSteps (Requote.R ⬝ (natL ⬝ f)) (quoteT (quoteT (evalNT ⬝ DN m φ))) ∧
    WSteps (boxMap natL (natL ⬝ f)) (quoteT (natL ⬝ (evalNT ⬝ DN m φ))) ∧
    WSteps (natL ⬝ (evalNT ⬝ DN m φ)) (quoteT (evalNT ⬝ DN m φ)) :=
  coalg2 (nat_lift hf).1 (nat_idem m φ)

theorem cantor_coalg2 {m : Nat} {φ : List Bool → Bool} {q : Term} (hq : Local m φ q) :
    WSteps (Requote.R ⬝ (cantorL ⬝ q)) (quoteT (quoteT (evalT ⬝ D m φ))) ∧
    WSteps (boxMap cantorL (cantorL ⬝ q)) (quoteT (cantorL ⬝ (evalT ⬝ D m φ))) ∧
    WSteps (cantorL ⬝ (evalT ⬝ D m φ)) (quoteT (evalT ⬝ D m φ)) :=
  coalg2 (cantor_lift hq).1 (cantor_idem m φ)

end Coalgebra
