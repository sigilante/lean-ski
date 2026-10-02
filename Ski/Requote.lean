import Ski.Quote
import Ski.Simulation

open Term

/-!
# Re-encoding is definable

`no_quote` shows that no combinator takes a live term `M` to its encoding
`⟨M⟩`.  Re-encoding is different: it takes the encoding `⟨t⟩` to the
encoding of the encoding, `⟨⟨t⟩⟩`.  Its input is data, a Scott tree over
`S | K | I | App`, so a program can fold over it.  `requote` gives one
closed term `R` with `R ⟨t⟩ ↠ ⟨⟨t⟩⟩` for every `t`, under weak reduction.
Under L1's head reduction `R ⟨t⟩` evaluates lazily, its recursive calls
left under the constructor, so its weak head normal form can differ from
`⟨⟨t⟩⟩`'s (they differ at `t = S ⬝ K`); the two are joined by weak
reduction.

`R` is the fixpoint of `λ r q. q ⟨⟨S⟩⟩ ⟨⟨K⟩⟩ ⟨⟨I⟩⟩ (λ f a. App' (r f) (r a))`.
Here `App` is the constructor term `appC`, `⟨App⟩` its encoding, and
`App' u v` is `App ⬝ (App ⬝ ⟨App⟩ ⬝ u) ⬝ v`: the encoding of `App ⬝ u₀ ⬝ v₀`
given encodings `u` of `u₀` and `v` of `v₀`.  The leaves re-encode to
constants; an application re-encodes to the encoding of the constructor
applied to the re-encoded children.  The proof is induction on `t`.  Weak
reduction reduces under the constructor, where the recursive calls sit.
-/

namespace Requote

/-- The object type's `App` constructor. -/
def appC : Term := toTerm (ctorO 2 3 4)

theorem quoteT_app (f a : Term) : quoteT (f ⬝ a) = appC ⬝ quoteT f ⬝ quoteT a := rfl

/-- A leaf encoding selects its continuation: `⟨S⟩ a b c d ↠ a`. -/
theorem quoteS_elim (a b c d : Term) : WSteps (quoteT .S ⬝ a ⬝ b ⬝ c ⬝ d) a :=
  absN_beta_close [0, 1, 2, 3] (.var 0) (fun _ => K) [a, b, c, d] rfl

theorem quoteK_elim (a b c d : Term) : WSteps (quoteT .K ⬝ a ⬝ b ⬝ c ⬝ d) b :=
  absN_beta_close [0, 1, 2, 3] (.var 1) (fun _ => K) [a, b, c, d] rfl

theorem quoteI_elim (a b c d : Term) : WSteps (quoteT .I ⬝ a ⬝ b ⬝ c ⬝ d) c :=
  absN_beta_close [0, 1, 2, 3] (.var 2) (fun _ => K) [a, b, c, d] rfl

/-- An application's encoding passes its children to the fourth
    continuation: `⟨f a⟩ k₀ k₁ k₂ k₃ ↠ k₃ ⟨f⟩ ⟨a⟩`. -/
theorem quoteApp_elim (f x a b c d : Term) :
    WSteps (quoteT (f ⬝ x) ⬝ a ⬝ b ⬝ c ⬝ d) (d ⬝ quoteT f ⬝ quoteT x) :=
  absN_beta_close [0, 1, 2, 3, 4, 5] (.var 5 ⬝ₒ .var 0 ⬝ₒ .var 1) (fun _ => K)
    [quoteT f, quoteT x, a, b, c, d] rfl

/-- The application case's body, over `r` (0), `f` (2) and `a` (3):
    `⟨App⟩ ⬝ (⟨App⟩ ⬝ ⟨appC⟩ ⬝ r f) ⬝ r a`. -/
def appBody : OTerm :=
  appC.toO ⬝ₒ (appC.toO ⬝ₒ (quoteT appC).toO ⬝ₒ (.var 0 ⬝ₒ .var 2)) ⬝ₒ (.var 0 ⬝ₒ .var 3)

/-- The step function's body, over `r` (0) and `q` (1). -/
def stepBody : OTerm :=
  .var 1 ⬝ₒ (quoteT (quoteT .S)).toO ⬝ₒ (quoteT (quoteT .K)).toO ⬝ₒ (quoteT (quoteT .I)).toO
    ⬝ₒ absN [2, 3] appBody

/-- `λ r q. q ⟨⟨S⟩⟩ ⟨⟨K⟩⟩ ⟨⟨I⟩⟩ (λ f a. App' (r f) (r a))`. -/
def stepF : Term := toTerm (absN [0, 1] stepBody)

/-- **The re-encoder**, the fixpoint of `stepF`. -/
def R : Term := fixSelf stepF (fixB stepF)

/-- `R` unrolls once. -/
theorem R_unroll : WSteps R (stepF ⬝ R) := by
  have h := (fixSelf_unroll (F := stepF) (Steps.refl (fixB stepF))).weak
  -- the unrolled self-reference is `R` with an `I` in front of its argument
  have hI : WSteps (fixSelf stepF (I ⬝ fixB stepF)) R :=
    WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

/-- One unrolling and the step function's β: `R q` cases on `q`. -/
theorem R_case (q : Term) :
    WSteps (R ⬝ q) (q ⬝ quoteT (quoteT .S) ⬝ quoteT (quoteT .K) ⬝ quoteT (quoteT .I)
      ⬝ (absN [2, 3] appBody).close (overrideC (fun _ => K) [0, 1] [R, q])) := by
  have h := absN_beta_close [0, 1] stepBody (fun _ => K) [R, q] rfl
  simp only [stepBody, OTerm.close, close_toO] at h
  exact (WSteps.left q R_unroll).trans h

/-- The application case's function, applied to two encodings. -/
theorem appCase (q f x : Term) :
    WSteps ((absN [2, 3] appBody).close (overrideC (fun _ => K) [0, 1] [R, q]) ⬝ f ⬝ x)
      (appC ⬝ (appC ⬝ quoteT appC ⬝ (R ⬝ f)) ⬝ (R ⬝ x)) := by
  have h := absN_beta_close [2, 3] appBody (overrideC (fun _ => K) [0, 1] [R, q]) [f, x] rfl
  simp only [appBody, OTerm.close, close_toO] at h
  exact h

/-- **Re-encoding is definable**: one closed term `R` takes the encoding of
    every term to the encoding of that encoding, `R ⟨t⟩ ↠ ⟨⟨t⟩⟩`. -/
theorem requote : ∀ t : Term, WSteps (R ⬝ quoteT t) (quoteT (quoteT t))
  | .S => (R_case _).trans (quoteS_elim _ _ _ _)
  | .K => (R_case _).trans (quoteK_elim _ _ _ _)
  | .I => (R_case _).trans (quoteI_elim _ _ _ _)
  | .app f x => by
    rw [quoteT_app f x, quoteT_app, quoteT_app]
    have h1 := (R_case (appC ⬝ quoteT f ⬝ quoteT x)).trans
      (quoteApp_elim f x _ _ _ _)
    exact (h1.trans (appCase _ _ _)).trans
      (WSteps.app (WSteps.right _ (WSteps.right _ (requote f))) (requote x))

/-- Iterated: `Rⁿ ⟨t⟩ ↠ ⟨…⟨t⟩…⟩`, the encoding `n + 1` deep. -/
theorem requote_iter (t : Term) : ∀ n : Nat,
    WSteps (Nat.repeat (R ⬝ ·) n (quoteT t)) (Nat.repeat quoteT (n + 1) t)
  | 0 => .refl _
  | n + 1 => (WSteps.right R (requote_iter t n)).trans (requote _)

end Requote
