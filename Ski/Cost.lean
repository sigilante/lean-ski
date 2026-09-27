import Ski.Bridge
open Term

/-!
# Normal-order cost of compiled affine realizers

Counted standardization is false (`counted_standardization_false`), so a
step bound on the trace cannot come from a count of weak steps.  This file
bounds normal-order head reduction of compiled terms directly.

**The obstacle is duplication.**  `S f g x` copies `x`.  In code compiled
from an affine source, every copy but one goes where it is never forced:
bracket abstraction sends a variable to one side of an application and a
`K` discards the copy on the other.  So every combinator occurrence fires
at most once.  A logical relation that counts steps (`Q`) captures this
through graded arrows:
- `A ⊸ B` uses its argument at most once, and charges its cost once;
- `A ⊸⁰ B` discards its argument.

`S`, `K` and `I` are typed at graded types (`Q_S1`, `Q_S2`, `Q_K`, `Q_I`),
each firing once.  Bracket abstraction over a variable that occurs at most
once yields a graded arrow (`abs_OG`), because abstraction never duplicates
a variable.  The fundamental lemma (`OG.sound`) charges a typed term its
number of combinator leaves, plus its variables' costs.

**The theorem** (`glue_head_bound`).  Let a closed, typed, affine glue
realizer be written as SKIjack source and compiled by `comp`.  Its compiled
term, applied to witnesses that head-normalize within `mᵢ` steps each,
head-normalizes within `leaves + Σ mᵢ` steps, where `leaves` counts the
combinators of the compiled term.

Here affine means multiplicative: no variable occurs twice in a λ's scope,
including across the two branches of a case.  `Ski/CostAdd.lean` lifts the
restriction, for realizers compiled with shared variables threaded through
each case's continuations.
-/

theorem StepsN.left' {n : Nat} {f f' : Term} (x : Term) (h : StepsN n f f') :
    StepsN n (f ⬝ x) (f' ⬝ x) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.left x s) ih

theorem StepsN.trans' {a b : Nat} {t u v : Term} (h₁ : StepsN a t u) (h₂ : StepsN b u v) :
    StepsN (a + b) t v := by
  induction h₁ with
  | refl => rw [Nat.zero_add]; exact h₂
  | step s _ ih => rw [Nat.add_right_comm]; exact .step s (ih h₂)

namespace Rz

variable {β : Type}

-- ---------------------------------------------------------------------------
-- Counted head reduction
-- ---------------------------------------------------------------------------

/-- `u` head-normalizes within `n` steps. -/
def HNB (u : Term) (n : Nat) : Prop := ∃ i v, i ≤ n ∧ StepsN i u v ∧ Whnf v

/-- At most `j` head steps from `u` to `v`. -/
def StepsLe (j : Nat) (u v : Term) : Prop := ∃ i, i ≤ j ∧ StepsN i u v

-- ---------------------------------------------------------------------------
-- Graded types and the counting relation
-- ---------------------------------------------------------------------------

/-- Graded types: `lin A B` is `A ⊸ B`, `dis A B` is `A ⊸⁰ B`. -/
inductive GTy (β : Type) where
  | base (b : β)
  | lin (A B : GTy β)
  | dis (A B : GTy β)
  | prod (A B : GTy β)
  | sum (A B : GTy β)

/-- `Q A u n`: `u` behaves at `A` within cost `n`. -/
def Q : GTy β → Term → Nat → Prop
  | .base _, u, n => HNB u n
  | .lin A B, u, n => ∀ a m, Q A a m → Q B (u ⬝ a) (n + m)
  | .dis A B, u, n => ∀ a m, Q A a m → Q B (u ⬝ a) n
  | .prod A B, u, n => ∃ j na nb, j + na + nb ≤ n ∧
      ∀ k, ∃ a b, StepsLe j (u ⬝ k) (k ⬝ a ⬝ b) ∧ Q A a na ∧ Q B b nb
  | .sum A B, u, n => ∃ j na, j + na ≤ n ∧
      ((∀ f g, ∃ a, StepsLe j (u ⬝ f ⬝ g) (f ⬝ a) ∧ Q A a na) ∨
       (∀ f g, ∃ b, StepsLe j (u ⬝ f ⬝ g) (g ⬝ b) ∧ Q B b na))

theorem Q.mono : ∀ (A : GTy β) {u : Term} {n n' : Nat}, Q A u n → n ≤ n' → Q A u n'
  | .base _, _, _, _, h, hn => by
    cases h with
    | intro i h => cases h with
      | intro v h => exact ⟨i, v, Nat.le_trans h.1 hn, h.2⟩
  | .lin _ B, _, _, _, h, hn => fun a m ha => Q.mono B (h a m ha) (Nat.add_le_add_right hn m)
  | .dis _ B, _, _, _, h, hn => fun a m ha => Q.mono B (h a m ha) hn
  | .prod _ _, _, _, _, h, hn => by
    cases h with
    | intro j h => cases h with
      | intro na h => cases h with
        | intro nb h => exact ⟨j, na, nb, Nat.le_trans h.1 hn, h.2⟩
  | .sum _ _, _, _, _, h, hn => by
    cases h with
    | intro j h => cases h with
      | intro na h => exact ⟨j, na, Nat.le_trans h.1 hn, h.2⟩

/-- **Backward closure under counted head steps.** -/
theorem Q.backN : ∀ (A : GTy β) {u u' : Term} {i n : Nat}, StepsN i u u' → Q A u' n →
    Q A u (n + i)
  | .base _, _, _, i, _, s, h => by
    cases h with
    | intro i' h => cases h with
      | intro v h =>
        refine ⟨i + i', v, by omega, s.trans' h.2.1, h.2.2⟩
  | .lin _ B, _, _, i, n, s, h => fun a m ha => by
    have := Q.backN B (s.left' a) (h a m ha)
    rw [show n + i + m = n + m + i by omega]
    exact this
  | .dis _ B, _, _, _, _, s, h => fun a m ha => Q.backN B (s.left' a) (h a m ha)
  | .prod _ _, _, _, i, _, s, h => by
    cases h with
    | intro j h => cases h with
      | intro na h => cases h with
        | intro nb h =>
          refine ⟨i + j, na, nb, by omega, fun k => ?_⟩
          cases h.2 k with
          | intro a h' => cases h' with
            | intro b h' =>
              cases h'.1 with
              | intro i' hi =>
                exact ⟨a, b, ⟨i + i', by omega, (s.left' k).trans' hi.2⟩, h'.2⟩
  | .sum _ _, _, _, i, _, s, h => by
    cases h with
    | intro j h => cases h with
      | intro na h =>
        refine ⟨i + j, na, by omega, ?_⟩
        cases h.2 with
        | inl hl =>
          refine .inl fun f g => ?_
          cases hl f g with
          | intro a ha =>
            cases ha.1 with
            | intro i' hi =>
              exact ⟨a, ⟨i + i', by omega, ((s.left' f).left' g).trans' hi.2⟩, ha.2⟩
        | inr hr =>
          refine .inr fun f g => ?_
          cases hr f g with
          | intro b hb =>
            cases hb.1 with
            | intro i' hi =>
              exact ⟨b, ⟨i + i', by omega, ((s.left' f).left' g).trans' hi.2⟩, hb.2⟩

theorem Q.back {A : GTy β} {u u' : Term} {n : Nat} (s : Step u u') (h : Q A u' n) :
    Q A u (n + 1) :=
  Q.backN A (.step s (.refl _)) h

-- ---------------------------------------------------------------------------
-- Subtyping
-- ---------------------------------------------------------------------------

/-- Subtyping: a discarding arrow is a linear one; arrows are contravariant
    in the argument and covariant in the result; a pair is its eliminator, and
    so is an injection. -/
inductive Sub : GTy β → GTy β → Prop
  | refl (A : GTy β) : Sub A A
  | trans {A B C : GTy β} : Sub A B → Sub B C → Sub A C
  | disLin (A B : GTy β) : Sub (.dis A B) (.lin A B)
  | lin {A A' B B' : GTy β} : Sub A' A → Sub B B' → Sub (.lin A B) (.lin A' B')
  | dis {A A' B B' : GTy β} : Sub A' A → Sub B B' → Sub (.dis A B) (.dis A' B')
  | prodE (A B C : GTy β) : Sub (.prod A B) (.lin (.lin A (.lin B C)) C)
  | sumE (A B C : GTy β) : Sub (.sum A B) (.lin (.lin A C) (.lin (.lin B C) C))

/-- A pair, eliminated by a continuation. -/
theorem Q_prodE {A B C : GTy β} {p : Term} {n : Nat} (h : Q (.prod A B) p n) :
    Q (.lin (.lin A (.lin B C)) C) p n := by
  intro k nk hk
  cases h with
  | intro j h => cases h with
    | intro na h => cases h with
      | intro nb h =>
        cases h.2 k with
        | intro a h' => cases h' with
          | intro b h' =>
            cases h'.1 with
            | intro i hi =>
              have h1 := hk a na h'.2.1 b nb h'.2.2
              exact Q.mono C (Q.backN C hi.2 h1) (by omega)

/-- An injection, eliminated by two continuations; only one runs. -/
theorem Q_sumE {A B C : GTy β} {s : Term} {n : Nat} (h : Q (.sum A B) s n) :
    Q (.lin (.lin A C) (.lin (.lin B C) C)) s n := by
  intro f nf hf g ng hg
  cases h with
  | intro j h => cases h with
    | intro na h =>
      cases h.2 with
      | inl hl =>
        cases hl f g with
        | intro a ha =>
          cases ha.1 with
          | intro i hi => exact Q.mono C (Q.backN C hi.2 (hf a na ha.2)) (by omega)
      | inr hr =>
        cases hr f g with
        | intro b hb =>
          cases hb.1 with
          | intro i hi => exact Q.mono C (Q.backN C hi.2 (hg b na hb.2)) (by omega)

theorem Sub.sound {A B : GTy β} (h : Sub A B) : ∀ {u : Term} {n : Nat}, Q A u n → Q B u n := by
  induction h with
  | refl => exact id
  | trans _ _ ih1 ih2 => exact fun hq => ih2 (ih1 hq)
  | disLin A B => intro u n hq a m ha; exact Q.mono B (hq a m ha) (Nat.le_add_right n m)
  | lin _ _ iha ihb => intro u n hq a m ha; exact ihb (hq a m (iha ha))
  | dis _ _ iha ihb => intro u n hq a m ha; exact ihb (hq a m (iha ha))
  | prodE => exact Q_prodE
  | sumE => exact Q_sumE

-- ---------------------------------------------------------------------------
-- The combinators, each firing once
-- ---------------------------------------------------------------------------

/-- `g Y Z` for a grade: linear (`true`) or discarding (`false`). -/
def garr (g : Bool) (Y Z : GTy β) : GTy β := if g then .lin Y Z else .dis Y Z

theorem Q.garr_app {g : Bool} {Y Z : GTy β} {f a : Term} {nf na : Nat}
    (hf : Q (garr g Y Z) f nf) (ha : Q Y a na) : Q Z (f ⬝ a) (nf + na) := by
  cases g with
  | true => exact hf a na ha
  | false => exact Q.mono Z (hf a na ha) (Nat.le_add_right nf na)

/-- `K : T ⊸ X ⊸⁰ T`. -/
theorem Q_K (T X : GTy β) : Q (.lin T (.dis X T)) K 1 := by
  intro a na ha N m _
  have := Q.back (.K a N) ha
  rw [Nat.add_comm] at this
  exact this

/-- `I : X ⊸ X`. -/
theorem Q_I (X : GTy β) : Q (.lin X X) I 1 := by
  intro N m hN
  have := Q.back (.I N) hN
  rw [Nat.add_comm] at this
  exact this

/-- `S : (X ⊸ Y ⊸g Z) ⊸ (X ⊸⁰ Y) ⊸ X ⊸ Z`: the argument goes to the left
    side only. -/
theorem Q_S1 (g : Bool) (X Y Z : GTy β) :
    Q (.lin (.lin X (garr g Y Z)) (.lin (.dis X Y) (.lin X Z))) S 1 := by
  intro P nP hP F nF hF N m hN
  have h1 := Q.garr_app (hP N m hN) (hF N m hN)
  have h2 := Q.back (.S P F N) h1
  exact Q.mono Z h2 (by omega)

/-- `S : (X ⊸⁰ Y ⊸g Z) ⊸ (X ⊸ Y) ⊸ X ⊸ Z`: the argument goes to the right
    side only. -/
theorem Q_S2 (g : Bool) (X Y Z : GTy β) :
    Q (.lin (.dis X (garr g Y Z)) (.lin (.lin X Y) (.lin X Z))) S 1 := by
  intro P nP hP F nF hF N m hN
  have h1 := Q.garr_app (hP N m hN) (hF N m hN)
  have h2 := Q.back (.S P F N) h1
  exact Q.mono Z h2 (by omega)

end Rz

-- ---------------------------------------------------------------------------
-- Leaves, costs of variables, occurrences
-- ---------------------------------------------------------------------------

/-- Combinator occurrences. -/
def Term.leaves : Term → Nat
  | .app f a => f.leaves + a.leaves
  | _ => 1

/-- Combinator occurrences of an open term. -/
def OTerm.leaves : OTerm → Nat
  | .var _ => 0
  | .app f a => f.leaves + a.leaves
  | _ => 1

/-- The costs of a term's variable occurrences, one per occurrence. -/
def envsum (μ : Nat → Nat) : OTerm → Nat
  | .var x => μ x
  | .app f a => envsum μ f + envsum μ a
  | _ => 0

/-- Occurrences of a variable. -/
def OTerm.count (x : Nat) : OTerm → Nat
  | .var y => if y = x then 1 else 0
  | .app f a => f.count x + a.count x
  | _ => 0

theorem leaves_toO : ∀ t : Term, t.toO.leaves = t.leaves
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app f a => by
    show f.toO.leaves + a.toO.leaves = f.leaves + a.leaves
    rw [leaves_toO f, leaves_toO a]

theorem envsum_toO (μ : Nat → Nat) : ∀ t : Term, envsum μ t.toO = 0
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app f a => by
    show envsum μ f.toO + envsum μ a.toO = 0
    rw [envsum_toO μ f, envsum_toO μ a]

theorem count_eq_zero {x : Nat} : ∀ {M : OTerm}, M.mem x = false → M.count x = 0
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var y, h => by
    have : y ≠ x := fun e => by rw [e, mem_var.2 rfl] at h; cases h
    show (if y = x then 1 else 0) = 0
    rw [if_neg this]
  | .app f a, h => by
    rw [mem_app, Bool.or_eq_false_iff] at h
    show f.count x + a.count x = 0
    rw [count_eq_zero h.1, count_eq_zero h.2]

theorem mem_of_count {x : Nat} : ∀ {M : OTerm}, 0 < M.count x → M.mem x = true
  | .S, h => by cases h
  | .K, h => by cases h
  | .I, h => by cases h
  | .var y, h => by
    by_cases hy : y = x
    · exact mem_var.2 hy
    · simp [OTerm.count, hy] at h
  | .app f a, h => by
    rw [mem_app]
    by_cases hf : 0 < f.count x
    · rw [mem_of_count hf]; rfl
    · have : 0 < a.count x := by simp only [OTerm.count] at h; omega
      rw [mem_of_count this, Bool.or_true]

theorem count_pos {x : Nat} : ∀ {M : OTerm}, M.mem x = true → 0 < M.count x
  | .S, h => by cases h
  | .K, h => by cases h
  | .I, h => by cases h
  | .var y, h => by
    have : y = x := mem_var.1 h
    show 0 < (if y = x then 1 else 0)
    rw [if_pos this]; exact Nat.one_pos
  | .app f a, h => by
    rw [mem_app] at h
    show 0 < f.count x + a.count x
    cases hf : f.mem x with
    | true => have := count_pos hf; omega
    | false =>
      rw [hf, Bool.false_or] at h
      have := count_pos h; omega

theorem mem_false_of_count {x : Nat} {M : OTerm} (h : M.count x = 0) : M.mem x = false := by
  cases hm : M.mem x with
  | false => rfl
  | true => have := count_pos hm; omega

namespace Rz

variable {β : Type}

-- ---------------------------------------------------------------------------
-- Graded typing of open combinator terms
-- ---------------------------------------------------------------------------

/-- Graded typing: variables typed by `Γ`, closed terms by their behaviour
    at their own leaf count, the two applications, and subtyping. -/
inductive OG (Γ : Nat → GTy β) : OTerm → GTy β → Prop
  | var (x : Nat) : OG Γ (.var x) (Γ x)
  | const {t : Term} {A : GTy β} : Q A t t.leaves → OG Γ t.toO A
  | appL {e f : OTerm} {A B : GTy β} : OG Γ e (.lin A B) → OG Γ f A → OG Γ (e ⬝ₒ f) B
  | appD {e f : OTerm} {A B : GTy β} : OG Γ e (.dis A B) → OG Γ f A → OG Γ (e ⬝ₒ f) B
  | sub {M : OTerm} {A B : GTy β} : OG Γ M A → Sub A B → OG Γ M B

/-- **The fundamental lemma**: a typed term, closed by terms that behave at
    their types within the costs `μ`, behaves at its type within its leaf
    count plus the costs of its variable occurrences. -/
theorem OG.sound {Γ : Nat → GTy β} {M : OTerm} {A : GTy β} (h : OG Γ M A) :
    ∀ {γ : Nat → Term} {μ : Nat → Nat}, (∀ x, M.mem x = true → Q (Γ x) (γ x) (μ x)) →
      Q A (M.close γ) (M.leaves + envsum μ M) := by
  induction h with
  | var x =>
    intro γ μ hγ
    show Q _ (γ x) (0 + μ x)
    rw [Nat.zero_add]
    exact hγ x (mem_var.2 rfl)
  | @const t A hq =>
    intro γ μ _
    rw [close_toO, leaves_toO, envsum_toO, Nat.add_zero]
    exact hq
  | @appL e f A B _ _ ihe ihf =>
    intro γ μ hγ
    have he := ihe (γ := γ) (μ := μ) fun x hx => hγ x (by rw [mem_app, hx]; rfl)
    have hf := ihf (γ := γ) (μ := μ) fun x hx => hγ x (by rw [mem_app, hx, Bool.or_true])
    have := he _ _ hf
    show Q B (e.close γ ⬝ f.close γ) (e.leaves + f.leaves + (envsum μ e + envsum μ f))
    exact Q.mono B this (by omega)
  | @appD e f A B _ _ ihe ihf =>
    intro γ μ hγ
    have he := ihe (γ := γ) (μ := μ) fun x hx => hγ x (by rw [mem_app, hx]; rfl)
    have hf := ihf (γ := γ) (μ := μ) fun x hx => hγ x (by rw [mem_app, hx, Bool.or_true])
    have := he _ _ hf
    show Q B (e.close γ ⬝ f.close γ) (e.leaves + f.leaves + (envsum μ e + envsum μ f))
    exact Q.mono B this (by omega)
  | sub _ hs ih => intro γ μ hγ; exact hs.sound (ih hγ)

/-- Typing depends on the context only at the variables that occur. -/
theorem OG.congr {Γ Γ' : Nat → GTy β} {M : OTerm} {A : GTy β} (h : OG Γ M A)
    (hc : ∀ y, M.mem y = true → Γ y = Γ' y) : OG Γ' M A := by
  induction h with
  | var x => rw [hc x (mem_var.2 rfl)]; exact .var x
  | const hq => exact .const hq
  | appL _ _ ihe ihf =>
    exact .appL (ihe fun y hy => hc y (by rw [mem_app, hy]; rfl))
      (ihf fun y hy => hc y (by rw [mem_app, hy, Bool.or_true]))
  | appD _ _ ihe ihf =>
    exact .appD (ihe fun y hy => hc y (by rw [mem_app, hy]; rfl))
      (ihf fun y hy => hc y (by rw [mem_app, hy, Bool.or_true]))
  | sub _ hs ih => exact .sub (ih hc) hs

theorem toO_ne_var' (t : Term) (y : Nat) : t.toO ≠ .var y := by
  cases t <;> intro e <;> cases e

theorem OG.var_inv {Γ : Nat → GTy β} {M : OTerm} {T : GTy β} (h : OG Γ M T) :
    ∀ {y}, M = .var y → Sub (Γ y) T := by
  induction h with
  | var x => intro y e; cases e; exact .refl _
  | const _ => intro y e; exact absurd e (toO_ne_var' _ _)
  | appL _ _ => intro y e; cases e
  | appD _ _ => intro y e; cases e
  | sub _ hs ih => intro y e; exact .trans (ih e) hs

theorem OG.app_inv {Γ : Nat → GTy β} {M : OTerm} {T : GTy β} (h : OG Γ M T) :
    ∀ {e f}, M = e ⬝ₒ f → (∃ t : Term, M = t.toO) ∨
      ∃ (g : Bool) (A T' : GTy β), Sub T' T ∧ OG Γ f A ∧ OG Γ e (garr g A T') := by
  induction h with
  | var x => intro e f h; cases h
  | @const t _ _ => intro e f _; exact .inl ⟨t, rfl⟩
  | @appL e f A B he hf => intro e' f' h; cases h; exact .inr ⟨true, A, B, .refl _, hf, he⟩
  | @appD e f A B he hf => intro e' f' h; cases h; exact .inr ⟨false, A, B, .refl _, hf, he⟩
  | sub _ hs ih =>
    intro e f h
    cases ih h with
    | inl hc => exact .inl hc
    | inr hr =>
      cases hr with
      | intro g hr => cases hr with
        | intro A hr => cases hr with
          | intro T' hr => exact .inr ⟨g, A, T', .trans hr.1 hs, hr.2.1, hr.2.2⟩

theorem Sub.garr_lin {g : Bool} {A B : GTy β} : Sub (garr g A B) (.lin A B) := by
  cases g with
  | true => exact .refl _
  | false => exact .disLin A B

/-- `Γ` with `X` for `x`. -/
def extG (Γ : Nat → GTy β) (x : Nat) (X : GTy β) : Nat → GTy β :=
  fun y => if y = x then X else Γ y

/-- **Abstraction yields a graded arrow**: if `M : T` with `x : X`, and `x`
    occurs at most once in `M`, then `[x] M : X ⊸ T`.  Abstraction sends the
    variable to one side of each application and discards on the other. -/
theorem abs_OG {Γ : Nat → GTy β} {x : Nat} {X : GTy β} :
    ∀ (M : OTerm) {T : GTy β}, OG (extG Γ x X) M T → M.count x ≤ 1 →
      OG Γ (abs x M) (.lin X T)
  | M, T, h, hc => by
    have ext_ne : ∀ {N : OTerm}, N.mem x = false → ∀ y, N.mem y = true → extG Γ x X y = Γ y :=
      fun hN y hy => if_neg fun e => by rw [e, hN] at hy; cases hy
    cases hm : M.mem x with
    | false =>
      rw [abs_of_not_mem hm]
      exact .sub (.appL (.const (t := K) (Q_K T X)) (h.congr (ext_ne hm))) (.disLin X T)
    | true =>
      match M, h, hm, hc with
      | .var y, h, hm, _ =>
        have hyx : y = x := mem_var.1 hm
        subst hyx
        have hs : Sub X T := by
          have := h.var_inv rfl
          unfold extG at this
          rw [if_pos rfl] at this
          exact this
        rw [abs_var, if_pos rfl]
        exact .sub (.const (t := I) (Q_I X)) (.lin (.refl X) hs)
      | .app e f, h, hm, hc =>
        cases h.app_inv rfl with
        | inl hk =>
          cases hk with
          | intro t ht => rw [ht, mem_toO] at hm; cases hm
        | inr hr =>
          cases hr with
          | intro g hr => cases hr with
            | intro A hr => cases hr with
              | intro T' hr =>
                have hce : e.count x + f.count x ≤ 1 := hc
                by_cases he : f = .var x ∧ e.mem x = false
                · -- η: `[x] (e x) = e`
                  rw [abs_app, if_neg (by rw [hm]; decide), if_pos he]
                  have hXA : Sub X A := by
                    have := hr.2.1.var_inv he.1
                    unfold extG at this
                    rw [if_pos rfl] at this
                    exact this
                  exact .sub (hr.2.2.congr (ext_ne he.2))
                    (.trans Sub.garr_lin (.lin hXA hr.1))
                · rw [abs_app, if_neg (by rw [hm]; decide), if_neg he]
                  cases hfm : f.mem x with
                  | false =>
                    -- the variable is on the left: `S ([x] e) (K f)`
                    have hem : e.mem x = true := by
                      rw [mem_app, hfm, Bool.or_false] at hm; exact hm
                    have hfc : f.count x = 0 := count_eq_zero hfm
                    rw [abs_of_not_mem hfm]
                    have hE := abs_OG e hr.2.2 (by omega)
                    have hF : OG Γ (.K ⬝ₒ f) (.dis X A) :=
                      .appL (.const (t := K) (Q_K A X)) (hr.2.1.congr (ext_ne hfm))
                    exact .sub (.appL (.appL (.const (t := S) (Q_S1 g X A T')) hE) hF)
                      (.lin (.refl X) hr.1)
                  | true =>
                    -- the variable is on the right: `S (K e) ([x] f)`
                    have hfc : 0 < f.count x := count_pos hfm
                    have hem : e.mem x = false := mem_false_of_count (by omega)
                    rw [abs_of_not_mem hem]
                    have hF := abs_OG f hr.2.1 (by omega)
                    have hE : OG Γ (.K ⬝ₒ e) (.dis X (garr g A T')) :=
                      .appL (.const (t := K) (Q_K _ X)) (hr.2.2.congr (ext_ne hem))
                    exact .sub (.appL (.appL (.const (t := S) (Q_S2 g X A T')) hE) hF)
                      (.lin (.refl X) hr.1)

-- ---------------------------------------------------------------------------
-- Abstraction over several formals
-- ---------------------------------------------------------------------------

/-- `Γ` with `Xs` for `xs`, first to last. -/
def overrideG (Γ : Nat → GTy β) : List Nat → List (GTy β) → Nat → GTy β
  | x :: xs, X :: Xs => overrideG (extG Γ x X) xs Xs
  | _, _ => Γ

/-- `X₁ ⊸ … ⊸ Xₖ ⊸ T`. -/
def arrowsG : List (GTy β) → GTy β → GTy β
  | [], T => T
  | X :: Xs, T => .lin X (arrowsG Xs T)

/-- Abstraction keeps the other variables' occurrences. -/
theorem count_abs_ne {x y : Nat} (h : y ≠ x) : ∀ M : OTerm, (abs y M).count x = M.count x
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var z => by
    rw [abs_var]
    by_cases hz : z = y
    · rw [if_pos hz]
      show 0 = (if z = x then 1 else 0)
      rw [if_neg (fun e => h (hz ▸ e))]
    · rw [if_neg hz]; show 0 + _ = _; rw [Nat.zero_add]
  | .app e f => by
    rw [abs_app]
    by_cases hm : (OTerm.app e f).mem y = false
    · rw [if_pos hm]; show 0 + (e.count x + f.count x) = _; rw [Nat.zero_add]; rfl
    · rw [if_neg hm]
      by_cases he : f = .var y ∧ e.mem y = false
      · rw [if_pos he, he.1]
        show e.count x = e.count x + (if y = x then 1 else 0)
        rw [if_neg h, Nat.add_zero]
      · rw [if_neg he]
        show 0 + (abs y e).count x + (abs y f).count x = e.count x + f.count x
        rw [count_abs_ne h e, count_abs_ne h f, Nat.zero_add]

theorem count_absN {x : Nat} : ∀ (xs : List Nat) (M : OTerm), x ∉ xs →
    (absN xs M).count x = M.count x
  | [], _, _ => rfl
  | y :: ys, M, h => by
    show (abs y (absN ys M)).count x = _
    rw [count_abs_ne (fun e => h (by rw [e]; exact .head _)),
      count_absN ys M (fun hx => h (.tail _ hx))]

/-- **Abstraction over several formals**, each occurring at most once. -/
theorem absN_OG : ∀ (xs : List Nat) (Xs : List (GTy β)) (Γ : Nat → GTy β) (M : OTerm)
    (T : GTy β), xs.length = Xs.length → Distinct xs → OG (overrideG Γ xs Xs) M T →
      (∀ x ∈ xs, M.count x ≤ 1) → OG Γ (absN xs M) (arrowsG Xs T)
  | [], [], _, _, _, _, _, h, _ => h
  | x :: xs, X :: Xs, Γ, M, T, hl, hd, h, hc => by
    have ih := absN_OG xs Xs (extG Γ x X) M T (Nat.succ.inj hl) hd.2 h
      (fun y hy => hc y (.tail _ hy))
    exact abs_OG (absN xs M) ih (by rw [count_absN xs M hd.1]; exact hc x (.head _))
  | [], _ :: _, _, _, _, hl, _, _, _ => by cases hl
  | _ :: _, [], _, _, _, hl, _, _, _ => by cases hl

-- ---------------------------------------------------------------------------
-- The Scott constructors, by symbolic head reduction
-- ---------------------------------------------------------------------------

theorem oiter_stepsN : ∀ (k : Nat) {t u : OTerm}, oiter k t = some u →
    ∀ σ : Nat → Term, StepsN k (t.close σ) (u.close σ)
  | 0, t, u, h, σ => by cases h; exact .refl _
  | k + 1, t, u, h, σ => by
    simp only [oiter] at h
    cases hs : ostep? t with
    | none => rw [hs] at h; cases h
    | some t' =>
      rw [hs] at h
      exact .step ((ostep?_sound hs).close σ) (oiter_stepsN k h σ)

/-- Three closed terms as an environment. -/
def env3 (a b c : Term) : Nat → Term
  | 0 => a
  | 1 => b
  | _ => c

/-- `Pair : A ⊸ B ⊸ A × B`, firing each of its 17 combinators once. -/
theorem Q_pairG (A B : GTy β) : Q (.lin A (.lin B (.prod A B))) pairG pairG.leaves := by
  have hl : pairG.leaves = 17 := by decide
  have hr : oiter 14 (pairG.toO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2) =
      some (.var 2 ⬝ₒ (.K ⬝ₒ .var 0 ⬝ₒ .var 2) ⬝ₒ (.K ⬝ₒ .K ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2)) := by
    decide
  rw [hl]
  intro a na ha b nb hb
  refine ⟨14, na + 1, nb + 2, by omega, fun k => ⟨K ⬝ a ⬝ k, K ⬝ K ⬝ a ⬝ b ⬝ k, ?_, ?_, ?_⟩⟩
  · have h := oiter_stepsN 14 hr (env3 a b k)
    simp only [OTerm.close, close_toO, env3] at h
    exact ⟨14, Nat.le_refl _, h⟩
  · exact Q.back (.K a k) ha
  · have s : StepsN 2 (K ⬝ K ⬝ a ⬝ b ⬝ k) b :=
      .step (.left k (.left b (.K K a))) (.step (.K b k) (.refl b))
    exact Q.backN B s hb

/-- `Inl : A ⊸ A + B`, firing each of its 10 combinators once. -/
theorem Q_inlG (A B : GTy β) : Q (.lin A (.sum A B)) inlG inlG.leaves := by
  have hl : inlG.leaves = 10 := by decide
  have hr : oiter 9 (inlG.toO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2) =
      some (.var 1 ⬝ₒ (.K ⬝ₒ .var 0 ⬝ₒ .var 1)) := by decide
  rw [hl]
  intro a na ha
  refine ⟨9, na + 1, by omega, .inl fun f g => ⟨K ⬝ a ⬝ f, ?_, Q.back (.K a f) ha⟩⟩
  have h := oiter_stepsN 9 hr (env3 a f g)
  simp only [OTerm.close, close_toO, env3] at h
  exact ⟨9, Nat.le_refl _, h⟩

/-- `Inr : B ⊸ A + B`, firing each of its 8 combinators once. -/
theorem Q_inrG (A B : GTy β) : Q (.lin B (.sum A B)) inrG inrG.leaves := by
  have hl : inrG.leaves = 8 := by decide
  have hr : oiter 7 (inrG.toO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2) =
      some (.var 2 ⬝ₒ (.K ⬝ₒ .var 0 ⬝ₒ .var 2)) := by decide
  rw [hl]
  intro b nb hb
  refine ⟨7, nb + 1, by omega, .inr fun f g => ⟨K ⬝ b ⬝ g, ?_, Q.back (.K b g) hb⟩⟩
  have h := oiter_stepsN 7 hr (env3 b f g)
  simp only [OTerm.close, close_toO, env3] at h
  exact ⟨7, Nat.le_refl _, h⟩

end Rz

-- ---------------------------------------------------------------------------
-- Occurrences in SKIjack source, and what `comp` does to them
-- ---------------------------------------------------------------------------

/-- Free occurrences of a name in source. -/
def Src.cnt (x : Nat) : Src → Nat
  | .glob _ => 0
  | .var y => if y = x then 1 else 0
  | .app f a => f.cnt x + a.cnt x
  | .lam y b => if y = x then 0 else b.cnt x

theorem Src.cnt_peel (x : Nat) : ∀ e : Src, x ∉ e.peel.1 → e.peel.2.cnt x = e.cnt x
  | .glob _, _ => rfl
  | .var _, _ => rfl
  | .app _ _, _ => rfl
  | .lam y b, h => by
    have hy : y ≠ x := fun e => h (by rw [e]; exact .head _)
    have hb : x ∉ b.peel.1 := fun hx => h (.tail _ hx)
    show b.peel.2.cnt x = (if y = x then 0 else b.cnt x)
    rw [if_neg hy, Src.cnt_peel x b hb]

theorem Src.cnt_pos_of_occurs {x : Nat} : ∀ {e : Src}, e.occurs x = true → 0 < e.cnt x
  | .glob _, h => by cases h
  | .var y, h => by
    have : y = x := by simpa [Src.occurs] using h
    show 0 < (if y = x then 1 else 0)
    rw [if_pos this]; exact Nat.one_pos
  | .app f a, h => by
    show 0 < f.cnt x + a.cnt x
    simp only [Src.occurs, Bool.or_eq_true] at h
    cases h with
    | inl h => have := Src.cnt_pos_of_occurs h; omega
    | inr h => have := Src.cnt_pos_of_occurs h; omega
  | .lam y b, h => by
    simp only [Src.occurs, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    show 0 < (if y = x then 0 else b.cnt x)
    rw [if_neg h.1]
    exact Src.cnt_pos_of_occurs h.2

theorem Src.sizeOf_peel : ∀ e : Src, sizeOf e.peel.2 ≤ sizeOf e
  | .glob _ => Nat.le_refl _
  | .var _ => Nat.le_refl _
  | .app _ _ => Nat.le_refl _
  | .lam y b => by
    show sizeOf b.peel.2 ≤ sizeOf (Src.lam y b)
    have := Src.sizeOf_peel b
    simp only [Src.lam.sizeOf_spec]
    omega

theorem count_toO (x : Nat) : ∀ t : Term, t.toO.count x = 0
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app f a => by
    show f.toO.count x + a.toO.count x = 0
    rw [count_toO x f, count_toO x a]

theorem count_absN_mem {x : Nat} : ∀ (xs : List Nat) (M : OTerm), x ∈ xs → (absN xs M).count x = 0
  | [], _, h => by cases h
  | y :: ys, M, h => by
    show (abs y (absN ys M)).count x = 0
    by_cases hy : y = x
    · subst hy
      exact count_eq_zero (by rw [mem_abs, bne_self_eq_false, Bool.and_false])
    · rw [Rz.count_abs_ne hy]
      cases h with
      | head => exact absurd rfl hy
      | tail _ h => exact count_absN_mem ys M h

theorem count_appL (x : Nat) : ∀ (xs : List Nat) (F : OTerm),
    (appL F (xs.map .var)).count x = F.count x + xs.count x
  | [], F => by
    show F.count x = F.count x + List.count x []
    rw [List.count_nil]; exact (Nat.add_zero _).symm
  | y :: ys, F => by
    show (appL (F ⬝ₒ .var y) (ys.map .var)).count x = _
    rw [count_appL x ys]
    show F.count x + (if y = x then 1 else 0) + ys.count x = F.count x + (y :: ys).count x
    by_cases hy : y = x
    · subst hy
      rw [if_pos rfl, List.count_cons_self]
      omega
    · rw [if_neg hy, List.count_cons_of_ne hy]
      omega

/-- **Compilation does not add occurrences**: a name occurs in a compiled
    term at most as often as in its source, if the scope names it at most
    once.  A λ captures an occurring name once. -/
theorem count_comp_aux (x : Nat) : ∀ (n : Nat) (e : Src) (sc : List Nat), sizeOf e ≤ n →
    sc.count x ≤ 1 → (comp sc e).count x ≤ e.cnt x
  | 0, e, _, hs, _ => by
    have : 0 < sizeOf e := by cases e <;> simp <;> omega
    omega
  | n + 1, e, sc, hs, hsc => by
    cases e with
    | glob t => show t.toO.count x ≤ 0; rw [count_toO]; exact Nat.le_refl 0
    | var y => exact Nat.le_refl _
    | app f a =>
      show (comp sc f).count x + (comp sc a).count x ≤ f.cnt x + a.cnt x
      have hf : sizeOf f ≤ n := by simp only [Src.app.sizeOf_spec] at hs; omega
      have ha : sizeOf a ≤ n := by simp only [Src.app.sizeOf_spec] at hs; omega
      exact Nat.add_le_add (count_comp_aux x n f sc hf hsc) (count_comp_aux x n a sc ha hsc)
    | lam y b =>
      show (compLam (sc.filter fun s => (Src.lam y b).occurs s) [y] b).count x ≤ _
      rw [compLam_chain]
      unfold wrapLift
      rw [count_appL]
      have hL : [y] ++ b.peel.1 = (Src.lam y b).peel.1 := rfl
      rw [hL]
      generalize hcaps : sc.filter (fun s => (Src.lam y b).occurs s) = caps
      have hcc : caps.count x ≤ 1 := by
        rw [← hcaps]
        exact Nat.le_trans (List.Sublist.count_le _ (List.filter_sublist)) hsc
      by_cases hx : x ∈ caps ++ (Src.lam y b).peel.1
      · rw [count_absN_mem _ _ hx, Nat.zero_add]
        by_cases hxc : x ∈ caps
        · have hocc : (Src.lam y b).occurs x = true := by
            rw [← hcaps] at hxc
            exact (List.mem_filter.1 hxc).2
          have := Src.cnt_pos_of_occurs hocc
          omega
        · rw [List.count_eq_zero_of_not_mem hxc]; exact Nat.zero_le _
      · rw [Rz.count_absN _ _ hx]
        have hxc : x ∉ caps := fun h => hx (List.mem_append_left _ h)
        have hxL : x ∉ (Src.lam y b).peel.1 := fun h => hx (List.mem_append_right _ h)
        rw [List.count_eq_zero_of_not_mem hxc, Nat.add_zero]
        have hsz : sizeOf b.peel.2 ≤ n := by
          have := Src.sizeOf_peel b
          simp only [Src.lam.sizeOf_spec] at hs
          omega
        have ih := count_comp_aux x n b.peel.2 (caps ++ (Src.lam y b).peel.1) hsz
          (by rw [List.count_eq_zero_of_not_mem hx]; exact Nat.zero_le _)
        have e2 : (Src.lam y b).peel.2 = b.peel.2 := rfl
        rw [← Src.cnt_peel x (.lam y b) hxL, e2]
        exact ih

theorem count_comp (x : Nat) (e : Src) (sc : List Nat) (hsc : sc.count x ≤ 1) :
    (comp sc e).count x ≤ e.cnt x :=
  count_comp_aux x (sizeOf e) e sc (Nat.le_refl _) hsc

theorem Src.occurs_peel {x : Nat} : ∀ {e : Src}, x ∈ e.peel.1 → e.occurs x = false
  | .glob _, h => by cases h
  | .var _, h => by cases h
  | .app _ _, h => by cases h
  | .lam y b, h => by
    show (y != x && b.occurs x) = false
    cases h with
    | head => simp
    | tail _ h => rw [Src.occurs_peel h, Bool.and_false]

namespace Rz

variable {β γ : Type} (ι : γ → Term)

open Tm

-- ---------------------------------------------------------------------------
-- Affine realizers
-- ---------------------------------------------------------------------------

/-- Occurrences of the variable of index `i`. -/
def Tm.cnt : Nat → Tm γ → Nat
  | i, .var j => if j = i then 1 else 0
  | _, .const _ => 0
  | i, .app f a => f.cnt i + a.cnt i
  | i, .lam b => b.cnt (i + 1)
  | i, .pair a b => a.cnt i + b.cnt i
  | i, .fst t => t.cnt i
  | i, .snd t => t.cnt i
  | i, .inl a => a.cnt i
  | i, .inr b => b.cnt i
  | i, .case s f g => s.cnt i + f.cnt i + g.cnt i

/-- **Affine**: every λ's variable occurs at most once in its body, counting
    both branches of a case. -/
def Tm.Aff : Tm γ → Prop
  | .var _ => True
  | .const _ => True
  | .app f a => f.Aff ∧ a.Aff
  | .lam b => b.cnt 0 ≤ 1 ∧ b.Aff
  | .pair a b => a.Aff ∧ b.Aff
  | .fst t => t.Aff
  | .snd t => t.Aff
  | .inl a => a.Aff
  | .inr b => b.Aff
  | .case s f g => s.Aff ∧ f.Aff ∧ g.Aff

/-- The free variables below `d` occur at most once. -/
def AffAt (d : Nat) (t : Tm γ) : Prop := ∀ i, i < d → t.cnt i ≤ 1

theorem Src.cnt_projS (n d : Nat) (first : Bool) : (projS d first).cnt n = 0 := by
  unfold projS
  show (if d = n then 0 else (if d + 1 = n then 0 else
    (if (if first then d else d + 1) = n then 1 else 0))) = 0
  by_cases h1 : d = n
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : d + 1 = n
    · rw [if_pos h2]
    · rw [if_neg h2]
      cases first with
      | true => show (if d = n then 1 else 0) = 0; rw [if_neg h1]
      | false => show (if d + 1 = n then 1 else 0) = 0; rw [if_neg h2]

/-- A name's occurrences in the source are its variable's occurrences in the
    realizer, if it is bound outside; none, if it is bound inside. -/
theorem Src.cnt_trS : ∀ (t : Tm γ) (d n : Nat), closedAt d t →
    (trS ι d t).cnt n = if n < d then t.cnt (d - 1 - n) else 0
  | .var j, d, n, h => by
    show (if d - 1 - j = n then 1 else 0) = if n < d then (if j = d - 1 - n then 1 else 0) else 0
    have hj : j < d := h
    by_cases hn : n < d
    · rw [if_pos hn]
      by_cases e : d - 1 - j = n
      · rw [if_pos e, if_pos (by omega)]
      · rw [if_neg e, if_neg (by omega)]
    · rw [if_neg hn, if_neg (by omega)]
  | .const _, d, n, _ => by
    show 0 = if n < d then 0 else 0
    split <;> rfl
  | .app f a, d, n, h => by
    show (trS ι d f).cnt n + (trS ι d a).cnt n = _
    rw [Src.cnt_trS f d n h.1, Src.cnt_trS a d n h.2]
    by_cases hn : n < d
    · rw [if_pos hn, if_pos hn, if_pos hn]; rfl
    · rw [if_neg hn, if_neg hn, if_neg hn]
  | .lam b, d, n, h => by
    show (if d = n then 0 else (trS ι (d + 1) b).cnt n) = if n < d then b.cnt (d - 1 - n + 1) else 0
    rw [Src.cnt_trS b (d + 1) n h]
    by_cases e : d = n
    · rw [if_pos e, if_neg (by omega)]
    · rw [if_neg e]
      by_cases hn : n < d
      · rw [if_pos (by omega), if_pos hn, show d + 1 - 1 - n = d - 1 - n + 1 by omega]
      · rw [if_neg (by omega), if_neg hn]
  | .pair a b, d, n, h => by
    show 0 + (trS ι d a).cnt n + (trS ι d b).cnt n = _
    rw [Src.cnt_trS a d n h.1, Src.cnt_trS b d n h.2]
    by_cases hn : n < d
    · rw [if_pos hn, if_pos hn, if_pos hn, Nat.zero_add]; rfl
    · rw [if_neg hn, if_neg hn, if_neg hn]
  | .fst t, d, n, h => by
    show (trS ι d t).cnt n + (projS d true).cnt n = _
    rw [Src.cnt_trS t d n h, Src.cnt_projS, Nat.add_zero]
    rfl
  | .snd t, d, n, h => by
    show (trS ι d t).cnt n + (projS d false).cnt n = _
    rw [Src.cnt_trS t d n h, Src.cnt_projS, Nat.add_zero]
    rfl
  | .inl a, d, n, h => by
    show 0 + (trS ι d a).cnt n = _
    rw [Src.cnt_trS a d n h, Nat.zero_add]
    rfl
  | .inr b, d, n, h => by
    show 0 + (trS ι d b).cnt n = _
    rw [Src.cnt_trS b d n h, Nat.zero_add]
    rfl
  | .case s f g, d, n, h => by
    show (trS ι d s).cnt n + (trS ι d f).cnt n + (trS ι d g).cnt n = _
    rw [Src.cnt_trS s d n h.1, Src.cnt_trS f d n h.2.1, Src.cnt_trS g d n h.2.2]
    by_cases hn : n < d
    · rw [if_pos hn, if_pos hn, if_pos hn, if_pos hn]; rfl
    · rw [if_neg hn, if_neg hn, if_neg hn, if_neg hn]

/-- The parameters of the λ-chain at the top of `trS d t` are distinct names
    from `d` up. -/
theorem trS_peel : ∀ (t : Tm γ) (d : Nat),
    Distinct (trS ι d t).peel.1 ∧ ∀ n ∈ (trS ι d t).peel.1, d ≤ n
  | .lam b, d => by
    have ih := trS_peel b (d + 1)
    refine ⟨⟨fun h => by have := ih.2 d h; omega, ih.1⟩, fun n hn => ?_⟩
    cases hn with
    | head => exact Nat.le_refl d
    | tail _ h => have := ih.2 n h; omega
  | .var _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .const _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .app _ _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .pair _ _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .fst _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .snd _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .inl _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .inr _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .case _ _ _, _ => ⟨trivial, fun _ h => by cases h⟩

theorem distinct_of_nodup : ∀ {xs : List Nat}, xs.Nodup → Distinct xs
  | [], _ => trivial
  | _ :: _, h => ⟨(List.nodup_cons.1 h).1, distinct_of_nodup (List.nodup_cons.1 h).2⟩

theorem nodup_of_distinct : ∀ {xs : List Nat}, Distinct xs → xs.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => List.nodup_cons.2 ⟨h.1, nodup_of_distinct h.2⟩

-- ---------------------------------------------------------------------------
-- Compiled affine realizers are typed
-- ---------------------------------------------------------------------------

/-- The graded type of a realizer type: every arrow is linear. -/
def gty : Ty β → GTy β
  | .base b => .base b
  | .arr A B => .lin (gty A) (gty B)
  | .prod A B => .prod (gty A) (gty B)
  | .sum A B => .sum (gty A) (gty B)

/-- The context names the variable of index `i` at depth `d` `d - 1 - i`. -/
def CtxOK (d : Nat) (Γ : Nat → Ty β) (Γc : Nat → GTy β) : Prop :=
  ∀ i, i < d → Γc (d - 1 - i) = gty (Γ i)

theorem CtxOK.cons {d : Nat} {Γ : Nat → Ty β} {Γc : Nat → GTy β} (h : CtxOK d Γ Γc)
    (A : Ty β) : CtxOK (d + 1) (Ty.cons A Γ) (extG Γc d (gty A)) := by
  intro i hi
  cases i with
  | zero =>
    show extG Γc d (gty A) (d + 1 - 1 - 0) = gty A
    unfold extG; rw [if_pos (by omega)]
  | succ i =>
    show extG Γc d (gty A) (d + 1 - 1 - (i + 1)) = gty (Γ i)
    unfold extG
    rw [if_neg (by omega), show d + 1 - 1 - (i + 1) = d - 1 - i by omega]
    exact h i (by omega)

theorem overrideG_self (Γ : Nat → GTy β) : ∀ xs : List Nat, overrideG Γ xs (xs.map Γ) = Γ
  | [] => rfl
  | x :: xs => by
    show overrideG (extG Γ x (Γ x)) xs (xs.map Γ) = Γ
    have : extG Γ x (Γ x) = Γ := by
      funext y; unfold extG; by_cases h : y = x
      · rw [if_pos h, h]
      · rw [if_neg h]
    rw [this]
    exact overrideG_self Γ xs

theorem OG.var' {Γ : Nat → GTy β} {x : Nat} {A : GTy β} (h : Γ x = A) : OG Γ (.var x) A := by
  rw [← h]; exact .var x

theorem OG.appL_vars {Γ : Nat → GTy β} : ∀ (xs : List Nat) {F : OTerm} {T : GTy β},
    OG Γ F (arrowsG (xs.map Γ) T) → OG Γ (_root_.appL F (xs.map OTerm.var)) T
  | [], _, _, h => h
  | x :: xs, _, _, h => OG.appL_vars xs (.appL h (.var x))

theorem filter_false_nil {p : Nat → Bool} (h : ∀ a, p a = false) : ∀ l : List Nat, l.filter p = []
  | [] => rfl
  | a :: l => by
    unfold List.filter
    rw [h a]
    exact filter_false_nil h l

theorem projS_occurs (d : Nat) (first : Bool) (s : Nat) : (projS d first).occurs s = false := by
  show (d != s && ((d + 1) != s && ((if first then d else d + 1) == s))) = false
  by_cases h1 : d = s
  · rw [h1, bne_self_eq_false, Bool.false_and]
  · by_cases h2 : d + 1 = s
    · rw [h2, bne_self_eq_false, Bool.false_and, Bool.and_false]
    · cases first with
      | true => rw [show (if true = true then d else d + 1) = d from rfl, beq_false_of_ne h1,
          Bool.and_false, Bool.and_false]
      | false => rw [show (if false = true then d else d + 1) = d + 1 from rfl,
          beq_false_of_ne h2, Bool.and_false, Bool.and_false]

/-- The case continuation `λ a b. a` (or `λ a b. b`), compiled: `A ⊸ B ⊸ A`. -/
theorem projS_OG (sc : List Nat) (d : Nat) (first : Bool) (Γc : Nat → GTy β) (A B : GTy β) :
    OG Γc (comp sc (projS d first)) (.lin A (.lin B (if first then A else B))) := by
  have hcaps : (sc.filter fun s => (projS d first).occurs s) = [] := by
    exact filter_false_nil (fun s => projS_occurs d first s) sc
  show OG Γc (compLam (sc.filter fun s => (projS d first).occurs s) [d]
    (.lam (d + 1) (.var (if first then d else d + 1)))) _
  rw [hcaps, compLam_chain]
  show OG Γc (appL (absN ([] ++ [d, d + 1]) (comp ([] ++ [d, d + 1]) (.var _))) []) _
  have hdist : Distinct [d, d + 1] := by
    show d ∉ [d + 1] ∧ (d + 1 ∉ ([] : List Nat) ∧ True)
    exact ⟨fun h => by have := List.mem_singleton.1 h; omega, List.not_mem_nil, trivial⟩
  refine absN_OG [d, d + 1] [A, B] Γc _ _ rfl hdist ?_ ?_
  · show OG _ (.var (if first then d else d + 1)) _
    cases first with
    | true =>
      show OG (overrideG Γc [d, d + 1] [A, B]) (.var d) A
      refine OG.var' ?_
      show extG (extG Γc d A) (d + 1) B d = A
      unfold extG; rw [if_neg (by omega), if_pos rfl]
    | false =>
      show OG (overrideG Γc [d, d + 1] [A, B]) (.var (d + 1)) B
      refine OG.var' ?_
      show extG (extG Γc d A) (d + 1) B (d + 1) = B
      unfold extG; rw [if_pos rfl]
  · intro x _
    show (if (if first then d else d + 1) = x then 1 else 0) ≤ 1
    by_cases h : (if first then d else d + 1) = x
    · exact Nat.le_of_eq (if_pos h)
    · rw [if_neg h]; exact Nat.zero_le 1

/-- The fundamental statement, for the body of the λ-chain `comp` lifts. -/
def SemOG (Γ : Nat → Ty β) (t : Tm γ) (A : Ty β) : Prop :=
  ∀ d (Γc : Nat → GTy β) (sc : List Nat), CtxOK d Γ Γc → closedAt d t → AffAt d t → t.Aff →
    sc.Nodup → OG Γc (absN (trS ι d t).peel.1 (comp sc (trS ι d t).peel.2)) (gty A)

/-- From the chain form to the compiled term itself, in any scope. -/
theorem og_usual {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β} (hs : SemOG ι Γ t A) :
    ∀ d (Γc : Nat → GTy β) (sc : List Nat), CtxOK d Γ Γc → closedAt d t → AffAt d t →
      t.Aff → sc.Nodup → OG Γc (comp sc (trS ι d t)) (gty A) := by
  intro d Γc sc hΓ hd ha haff hsc
  cases t with
  | lam b =>
    show OG Γc (compLam (sc.filter fun s => (Src.lam d (trS ι (d + 1) b)).occurs s) [d]
      (trS ι (d + 1) b)) _
    rw [compLam_chain]
    generalize hcaps : sc.filter (fun s => (Src.lam d (trS ι (d + 1) b)).occurs s) = caps
    have hL : [d] ++ (trS ι (d + 1) b).peel.1 = (trS ι d (.lam b)).peel.1 := rfl
    have hB : (trS ι (d + 1) b).peel.2 = (trS ι d (.lam b)).peel.2 := rfl
    rw [hL, hB]
    generalize hLL : (trS ι d (.lam b)).peel.1 = L
    have hcn : caps.Nodup := by rw [← hcaps]; exact List.Pairwise.sublist List.filter_sublist hsc
    have hLn : L.Nodup := by rw [← hLL]; exact nodup_of_distinct (trS_peel ι _ d).1
    have hdisj : ∀ c ∈ caps, c ∉ L := by
      intro c hc hcL
      rw [← hcaps] at hc
      have h1 := (List.mem_filter.1 hc).2
      rw [← hLL] at hcL
      have hcL' : c ∈ (Src.lam d (trS ι (d + 1) b)).peel.1 := hcL
      rw [Src.occurs_peel hcL'] at h1
      cases h1
    have hnd : (caps ++ L).Nodup := List.nodup_append.2 ⟨hcn, hLn, fun a ha b hb e => hdisj a ha (e ▸ hb)⟩
    have hsem := hs d Γc (caps ++ L) hΓ hd ha haff hnd
    rw [hLL] at hsem
    unfold wrapLift
    rw [absN_append]
    refine OG.appL_vars caps (absN_OG caps (caps.map Γc) Γc _ _ (List.length_map _).symm
      (distinct_of_nodup hcn) (by rw [overrideG_self]; exact hsem) ?_)
    intro c hc
    rw [count_absN L _ (hdisj c hc)]
    refine Nat.le_trans (count_comp c _ (caps ++ L) (List.nodup_iff_count.1 hnd c)) ?_
    have hcL : c ∉ (trS ι d (.lam b)).peel.1 := by rw [hLL]; exact hdisj c hc
    rw [Src.cnt_peel c _ hcL, Src.cnt_trS ι (.lam b) d c hd]
    split
    · exact ha _ (by omega)
    · exact Nat.zero_le 1
  | var _ => exact hs d Γc sc hΓ hd ha haff hsc
  | const _ => exact hs d Γc sc hΓ hd ha haff hsc
  | app _ _ => exact hs d Γc sc hΓ hd ha haff hsc
  | pair _ _ => exact hs d Γc sc hΓ hd ha haff hsc
  | fst _ => exact hs d Γc sc hΓ hd ha haff hsc
  | snd _ => exact hs d Γc sc hΓ hd ha haff hsc
  | inl _ => exact hs d Γc sc hΓ hd ha haff hsc
  | inr _ => exact hs d Γc sc hΓ hd ha haff hsc
  | case _ _ _ => exact hs d Γc sc hΓ hd ha haff hsc

/-- **Compiled affine realizers are typed**: under the chain form, by
    induction on the typing derivation. -/
theorem ogsem {sig : γ → Ty β} (hq : ∀ c, Q (gty (sig c)) (ι c) (ι c).leaves)
    {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β} (h : Typed sig Γ t A) : SemOG ι Γ t A := by
  induction h with
  | var Γ n =>
    intro d Γc sc hΓ hd _ _ _
    exact OG.var' (hΓ n hd)
  | const Γ c =>
    intro d Γc sc _ _ _ _ _
    exact .const (hq c)
  | @lam Γ A B b _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    show OG Γc (abs d (absN (trS ι (d + 1) b).peel.1 (comp sc (trS ι (d + 1) b).peel.2)))
      (.lin (gty A) (gty B))
    have ha' : AffAt (d + 1) b := by
      intro i hi
      cases i with
      | zero => exact haff.1
      | succ i => exact ha i (by omega)
    have hog := ih (d + 1) (extG Γc d (gty A)) sc (hΓ.cons A) hd ha' haff.2 hsc
    refine abs_OG _ hog ?_
    have hdp : d ∉ (trS ι (d + 1) b).peel.1 := fun h => by
      have := (trS_peel ι b (d + 1)).2 d h; omega
    rw [count_absN _ _ hdp]
    refine Nat.le_trans (count_comp d _ sc (List.nodup_iff_count.1 hsc d)) ?_
    rw [Src.cnt_peel d _ hdp, Src.cnt_trS ι b (d + 1) d hd, if_pos (by omega),
      show d + 1 - 1 - d = 0 by omega]
    exact haff.1
  | @app Γ A B f a _ _ ihf iha =>
    intro d Γc sc hΓ hd ha haff hsc
    have haf : AffAt d f := fun i hi => by have := ha i hi; simp only [Tm.cnt] at this; omega
    have haa : AffAt d a := fun i hi => by have := ha i hi; simp only [Tm.cnt] at this; omega
    exact .appL (og_usual ι ihf d Γc sc hΓ hd.1 haf haff.1 hsc)
      (og_usual ι iha d Γc sc hΓ hd.2 haa haff.2 hsc)
  | @pair Γ A B a b _ _ iha ihb =>
    intro d Γc sc hΓ hd ha haff hsc
    have haa : AffAt d a := fun i hi => by have := ha i hi; simp only [Tm.cnt] at this; omega
    have hab : AffAt d b := fun i hi => by have := ha i hi; simp only [Tm.cnt] at this; omega
    exact .appL (.appL (.const (Q_pairG _ _)) (og_usual ι iha d Γc sc hΓ hd.1 haa haff.1 hsc))
      (og_usual ι ihb d Γc sc hΓ hd.2 hab haff.2 hsc)
  | @fst Γ A B t _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    exact .appL (.sub (og_usual ι ih d Γc sc hΓ hd ha haff hsc) (.prodE _ _ _))
      (projS_OG sc d true Γc _ _)
  | @snd Γ A B t _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    exact .appL (.sub (og_usual ι ih d Γc sc hΓ hd ha haff hsc) (.prodE _ _ _))
      (projS_OG sc d false Γc _ _)
  | @inl Γ A B a _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    exact .appL (.const (Q_inlG _ _)) (og_usual ι ih d Γc sc hΓ hd ha haff hsc)
  | @inr Γ A B b _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    exact .appL (.const (Q_inrG _ _)) (og_usual ι ih d Γc sc hΓ hd ha haff hsc)
  | @case Γ A B C s f g _ _ _ ihs ihf ihg =>
    intro d Γc sc hΓ hd ha haff hsc
    have has : AffAt d s := fun i hi => by have := ha i hi; simp only [Tm.cnt] at this; omega
    have haf : AffAt d f := fun i hi => by have := ha i hi; simp only [Tm.cnt] at this; omega
    have hag : AffAt d g := fun i hi => by have := ha i hi; simp only [Tm.cnt] at this; omega
    exact .appL (.appL (.sub (og_usual ι ihs d Γc sc hΓ hd.1 has haff.1 hsc) (.sumE _ _ _))
      (og_usual ι ihf d Γc sc hΓ hd.2.1 haf haff.2.1 hsc))
      (og_usual ι ihg d Γc sc hΓ hd.2.2 hag haff.2.2 hsc)

theorem envsum_zero : ∀ M : OTerm, envsum (fun _ => 0) M = 0
  | .var _ => rfl
  | .app f a => by show envsum _ f + envsum _ a = 0; rw [envsum_zero f, envsum_zero a]
  | .S => rfl
  | .K => rfl
  | .I => rfl

theorem leaves_close {γ' : Nat → Term} : ∀ {M : OTerm}, (∀ x, M.mem x = false) →
    Term.leaves (M.close γ') = M.leaves
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var y, h => by have := h y; rw [mem_var.2 rfl] at this; cases this
  | .app f a, h => by
    show Term.leaves (f.close γ') + Term.leaves (a.close γ') = f.leaves + a.leaves
    rw [leaves_close (fun x => by have := h x; rw [mem_app, Bool.or_eq_false_iff] at this; exact this.1),
      leaves_close (fun x => by have := h x; rw [mem_app, Bool.or_eq_false_iff] at this; exact this.2)]

/-- **A compiled affine realizer behaves at its type within its leaf count.** -/
theorem compiled_Q {sig : γ → Ty β} (hq : ∀ c, Q (gty (sig c)) (ι c) (ι c).leaves)
    {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β} (h : Typed sig Γ t A) (ht : closedAt 0 t)
    (haff : t.Aff) : Q (gty A) (compiled ι t) (compiled ι t).leaves := by
  have hog := og_usual ι (ogsem ι hq h) 0 (fun _ => gty A) [] (fun _ h => absurd h (Nat.not_lt_zero _))
    ht (fun _ h => absurd h (Nat.not_lt_zero _)) haff List.nodup_nil
  have hclosed : ∀ x, (comp [] (trS ι 0 t)).mem x = false := fun x => by
    have hc := count_comp x (trS ι 0 t) [] (Nat.zero_le 1)
    rw [Src.cnt_trS ι t 0 x ht, if_neg (Nat.not_lt_zero _)] at hc
    exact mem_false_of_count (Nat.le_zero.1 hc)
  have hs := hog.sound (γ := fun _ => K) (μ := fun _ => 0) (fun x hx => by rw [hclosed x] at hx; cases hx)
  rw [envsum_zero, Nat.add_zero] at hs
  show Q (gty A) ((comp [] (trS ι 0 t)).close fun _ => K) (Term.leaves ((comp [] (trS ι 0 t)).close fun _ => K))
  rw [leaves_close hclosed]
  exact hs

/-- **The glue's normal-order bound.**  A closed, typed, affine realizer
    without constants, of type `W₁ ⇒ … ⇒ Wₖ ⇒ W` over base types, compiled by
    `comp` and applied to witnesses that head-normalize within `mᵢ` steps each,
    head-normalizes within its compiled term's leaf count plus `Σ mᵢ` steps. -/
theorem glue_head_bound {Γ : Nat → Ty β} {t : Tm Empty} {w : β} (Ws : List β)
    (h : Typed Empty.elim Γ t (Ws.foldr (fun v C => .arr (.base v) C) (.base w)))
    (ht : closedAt 0 t) (haff : t.Aff) (wm : List (Term × Nat)) (hl : wm.length = Ws.length)
    (hw : ∀ p ∈ wm, HNB p.1 p.2) :
    HNB (appT (compiled Empty.elim t) (wm.map Prod.fst))
      ((compiled Empty.elim t).leaves + (wm.map Prod.snd).sum) := by
  have hQ := compiled_Q Empty.elim (fun c => c.elim) h ht haff
  have key : ∀ (Ws : List β) (wm : List (Term × Nat)) (r : Term) (n : Nat),
      wm.length = Ws.length → (∀ p ∈ wm, HNB p.1 p.2) →
      Q (gty (Ws.foldr (fun v C => .arr (.base v) C) (.base w))) r n →
      HNB (appT r (wm.map Prod.fst)) (n + (wm.map Prod.snd).sum) := by
    intro Ws
    induction Ws with
    | nil =>
      intro wm r n hl _ hr
      cases wm with
      | nil => exact hr
      | cons _ _ => cases hl
    | cons v Ws ih =>
      intro wm r n hl hw hr
      cases wm with
      | nil => cases hl
      | cons p wm =>
        have h1 := ih wm (r ⬝ p.1) (n + p.2) (Nat.succ.inj hl) (fun q hq => hw q (.tail _ hq))
          (hr p.1 p.2 (hw p (.head _)))
        show HNB (appT (r ⬝ p.1) (wm.map Prod.fst)) (n + (p.2 + (wm.map Prod.snd).sum))
        rw [← Nat.add_assoc]
        exact h1
  exact key Ws wm _ _ hl hw hQ

/-- `λ x y. fst (y, x)`: an affine glue realizer of `W ⇒ W ⇒ W`. -/
def fstPairT : Tm Empty := .lam (.lam (.fst (.pair (.var 0) (.var 1))))

theorem fstPairT_typed (Γ : Nat → Ty β) (w : β) :
    Typed Empty.elim Γ fstPairT (.arr (.base w) (.arr (.base w) (.base w))) :=
  .lam (.lam (.fst (B := .base w) (.pair (.var _ 0) (.var _ 1))))

theorem fstPairT_leaves : (compiled Empty.elim fstPairT).leaves = 28 := by decide

/-- **The bound, instantiated**: applied to two witnesses that head-normalize
    within `m₁` and `m₂` steps, the compiled term head-normalizes within
    `28 + m₁ + m₂` steps. -/
theorem fstPairT_bound (w₁ w₂ : Term) (m₁ m₂ : Nat) (h₁ : HNB w₁ m₁) (h₂ : HNB w₂ m₂) :
    HNB (compiled Empty.elim fstPairT ⬝ w₁ ⬝ w₂) (28 + (m₁ + (m₂ + 0))) := by
  have h := glue_head_bound (Γ := fun _ => .base ()) (w := ()) [(), ()] (fstPairT_typed _ ())
    ⟨show 0 < 0 + 1 + 1 by decide, show 1 < 0 + 1 + 1 by decide⟩
    ⟨by decide, by decide, trivial, trivial⟩ [(w₁, m₁), (w₂, m₂)] rfl (by
      intro p hp
      cases hp with
      | head => exact h₁
      | tail _ hp => cases hp with
        | head => exact h₂
        | tail _ hp => cases hp)
  rw [fstPairT_leaves] at h
  exact h

end Rz
