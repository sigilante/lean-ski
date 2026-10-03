import Ski.Compose
import Ski.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Term

/-!
# Binary arithmetic in SKI

A number is a Scott list of Scott Booleans, least significant digit first
(`bl`, `val`); leading zeros are allowed.  The operations are SKI terms,
recursive through Turing's fixed point `Θ` (`theta_unfold`), each proved
for every input by weak reduction:

- `addT`: `a + b + c` with a carry, no digit for a final carry of 0
  (`add_spec`);
- `mulT`: shift and add (`mul_spec`);
- `ltT`: the Boolean `a < b + c` (`lt_spec`);
- `subT`: `a - b - c` when `b + c ≤ a` (`sub_spec`);
- `trimT`: the value kept (`trim_spec`), leading zeros dropped;
- `modT m`: long division by the constant `m`, most significant digit
  first, one comparison and at most one subtraction a digit (`mod_spec`);
- `pow7T m`: `x^7 mod m` (`RepR.pow7`).

**The proof method.**  Each operation is a generator `G` over its own
recursive call and the operations it uses, all as parameters: the
operation is `Θ ⬝ (G ⬝ deps)`.  One unfolding of `G` on digits and
symbolic tails, with the recursive call a variable, is a run of the open
term that the kernel checks (`wnf`, `run`); a variable is inert, so the
run stops at the recursive call.  Induction on the inputs closes the
variables with the operation itself and the tails.

**Cost** (not proved; the proofs are about values).  The terms are
written to run.  Addition adds no digit for a final carry of 0, and
reduction trims its partial remainder, which therefore has at most one
digit more than `m`, so each digit's comparison and subtraction run over
`m`'s length.  A value used more than once is bound once, so a reducer
that shares arguments computes it once.

`RepR t n`: `t` reduces to a number of value `n`.  The operations compose
over it without forcing their arguments first (`RepR.add`, `RepR.mul`,
`RepR.mod`).
-/

namespace BitArith

open Compose

-- ---------------------------------------------------------------------------
-- A weak normalizer for open terms, for kernel-checked symbolic runs
-- ---------------------------------------------------------------------------

/-- One contraction at the root, if the root is a redex. -/
def root? : OTerm → Option OTerm
  | .app (.app (.app .S f) g) x => some (f ⬝ₒ x ⬝ₒ (g ⬝ₒ x))
  | .app (.app .K x) _ => some x
  | .app .I x => some x
  | _ => none

theorem root?_sound {t u : OTerm} (h : root? t = some u) : OWStep t u := by
  unfold root? at h
  split at h
  · cases h; exact .S _ _ _
  · cases h; exact .K _ _
  · cases h; exact .I _
  · cases h

/-- Weak normalization with fuel: both sides of an application, then the
    root, again. -/
def wnf : Nat → OTerm → OTerm
  | 0, t => t
  | n + 1, .app f x =>
    match root? (.app (wnf n f) (wnf n x)) with
    | some u => wnf n u
    | none => .app (wnf n f) (wnf n x)
  | _ + 1, t => t

theorem wnf_sound : ∀ (n : Nat) (t : OTerm), OWSteps t (wnf n t)
  | 0, t => .refl t
  | n + 1, .app f x => by
    simp only [wnf]
    have hfx : OWSteps (f ⬝ₒ x) (wnf n f ⬝ₒ wnf n x) := OWSteps.app (wnf_sound n f) (wnf_sound n x)
    split
    · rename_i u hu
      exact hfx.trans (.step (root?_sound hu) (wnf_sound n u))
    · exact hfx
  | _ + 1, .S => .refl _
  | _ + 1, .K => .refl _
  | _ + 1, .I => .refl _
  | _ + 1, .var _ => .refl _

/-- A symbolic run, closed. -/
theorem run {n : Nat} {t u : OTerm} (h : wnf n t = u) (σ : Nat → Term) :
    WSteps (t.close σ) (u.close σ) :=
  h ▸ (wnf_sound n t).close σ


-- ---------------------------------------------------------------------------
-- Encodings
-- ---------------------------------------------------------------------------

/-- `[k] k a b`, open. -/
def pairO (a b : OTerm) : OTerm := .S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ a)) ⬝ₒ (.K ⬝ₒ b)

/-- Scott lists: `nil = [n c] n`, `cons h t = [n c] c h t`. -/
def nilT : Term := K
def consT (h t : Term) : Term := K ⬝ pairT h t
def consO (h t : OTerm) : OTerm := .K ⬝ₒ pairO h t

def ttO : OTerm := .K
def ffO : OTerm := .K ⬝ₒ .I

/-- A number, least significant bit first. -/
def bl : List Bool → Term
  | [] => nilT
  | b :: bs => consT (boolT b) (bl bs)

def val : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * val bs

theorem consT_congr {h h' t t' : Term} (hh : WSteps h h') (ht : WSteps t t') :
    WSteps (consT h t) (consT h' t') :=
  WSteps.right K (WSteps.app (WSteps.right S (WSteps.right (S ⬝ I) (WSteps.right K hh)))
    (WSteps.right K ht))

theorem close_consO (σ : Nat → Term) (h t : OTerm) :
    (consO h t).close σ = consT (h.close σ) (t.close σ) := rfl

-- ---------------------------------------------------------------------------
-- Recursion: Turing's fixed point
-- ---------------------------------------------------------------------------

/-- `[x y] y (x x y)`. -/
def thA : Term := lam [0, 1] (.var 1 ⬝ₒ (.var 0 ⬝ₒ .var 0 ⬝ₒ .var 1))

/-- `Θ = A A`. -/
def thetaT : Term := thA ⬝ thA

theorem theta_unfold (F : Term) : WSteps (thetaT ⬝ F) (F ⬝ (thetaT ⬝ F)) :=
  lam_beta [0, 1] _ [thA, F] rfl

-- ---------------------------------------------------------------------------
-- Booleans
-- ---------------------------------------------------------------------------

def notO (c : OTerm) : OTerm := c ⬝ₒ ffO ⬝ₒ ttO

/-- The sum bit of a full adder. -/
def xor3O (x y c : OTerm) : OTerm := x ⬝ₒ (y ⬝ₒ c ⬝ₒ notO c) ⬝ₒ (y ⬝ₒ notO c ⬝ₒ c)

/-- The carry of a full adder. -/
def majO (x y c : OTerm) : OTerm := x ⬝ₒ (y ⬝ₒ ttO ⬝ₒ c) ⬝ₒ (y ⬝ₒ c ⬝ₒ ffO)

def xor3 (x y c : Bool) : Bool := (x ^^ y) ^^ c
def maj (x y c : Bool) : Bool := (x && y) || (x && c) || (y && c)

theorem adder (x y c : Bool) :
    x.toNat + y.toNat + c.toNat = (xor3 x y c).toNat + 2 * (maj x y c).toNat := by
  cases x <;> cases y <;> cases c <;> rfl

-- ---------------------------------------------------------------------------
-- Addition
-- ---------------------------------------------------------------------------

section
local notation "v" n => OTerm.var n

/-- One digit of the sum and the recursive call on the tails. -/
def addStep (x xs y ys : OTerm) : OTerm :=
  consO (xor3O x y (v 1)) ((v 0) ⬝ₒ majO x y (v 1) ⬝ₒ xs ⬝ₒ ys)

/-- `add self c a b`: `a + b + c`, a missing digit read as 0; a final
    carry of 0 adds no digit, so sums gain no leading zeros. -/
def addG : Term :=
  lam [0, 1, 2, 3]
    ((v 2) ⬝ₒ ((v 3) ⬝ₒ ((v 1) ⬝ₒ consO ttO .K ⬝ₒ .K) ⬝ₒ absN [6, 7] (addStep ffO .K (v 6) (v 7)))
      ⬝ₒ absN [4, 5] ((v 3) ⬝ₒ addStep (v 4) (v 5) ffO .K ⬝ₒ absN [6, 7] (addStep (v 4) (v 5) (v 6) (v 7))))
end

def addT : Term := thetaT ⬝ addG

theorem add_nn : ∀ c : Bool,
    wnf 200 (addG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ .K ⬝ₒ .K) =
      (bl (if c then [true] else [])).toO := by
  decide

theorem add_cc : ∀ x y c : Bool,
    wnf 200 (addG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ consO (boolT x).toO (.var 11)
      ⬝ₒ consO (boolT y).toO (.var 12)) =
      consO (boolT (xor3 x y c)).toO (.var 10 ⬝ₒ (boolT (maj x y c)).toO ⬝ₒ .var 11 ⬝ₒ .var 12) := by
  decide

theorem add_nc : ∀ y c : Bool,
    wnf 200 (addG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ .K ⬝ₒ consO (boolT y).toO (.var 12)) =
      consO (boolT (xor3 false y c)).toO (.var 10 ⬝ₒ (boolT (maj false y c)).toO ⬝ₒ .K ⬝ₒ .var 12) := by
  decide

theorem add_cn : ∀ x c : Bool,
    wnf 200 (addG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ consO (boolT x).toO (.var 11) ⬝ₒ .K) =
      consO (boolT (xor3 x false c)).toO (.var 10 ⬝ₒ (boolT (maj x false c)).toO ⬝ₒ .var 11 ⬝ₒ .K) := by
  decide

theorem add_unfold (c a b : Term) : WSteps (addT ⬝ c ⬝ a ⬝ b) (addG ⬝ addT ⬝ c ⬝ a ⬝ b) :=
  WSteps.left _ (WSteps.left _ (WSteps.left _ (theta_unfold addG)))

/-- The environment of a symbolic run: the function, then two tails. -/
def env3 (f a b : Term) : Nat → Term := fun i => if i = 10 then f else if i = 11 then a else b

/-- **Addition.** -/
theorem add_spec : ∀ (n : Nat) (c : Bool) (a b : List Bool), a.length + b.length ≤ n →
    ∃ d, WSteps (addT ⬝ boolT c ⬝ bl a ⬝ bl b) (bl d) ∧ val d = c.toNat + val a + val b
  | _, c, [], [], _ => by
    refine ⟨if c then [true] else [], ?_, ?_⟩
    · have h := run (add_nn c) (env3 addT K K)
      simp only [OTerm.close, close_toO] at h
      exact (add_unfold _ _ _).trans h
    · cases c <;> rfl
  | n + 1, c, [], y :: ys, hl => by
    have h := run (add_nc y c) (env3 addT K (bl ys))
    simp only [OTerm.close, close_toO, close_consO] at h
    obtain ⟨d, hd, hv⟩ := add_spec n (maj false y c) [] ys (by simp only [List.length_cons, List.length_nil] at hl ⊢; omega)
    refine ⟨xor3 false y c :: d, (add_unfold _ _ _).trans (h.trans (consT_congr (.refl _) hd)), ?_⟩
    have := adder false y c
    simp only [val, Bool.toNat_false] at hv this ⊢; omega
  | n + 1, c, x :: xs, [], hl => by
    have h := run (add_cn x c) (env3 addT (bl xs) K)
    simp only [OTerm.close, close_toO, close_consO] at h
    obtain ⟨d, hd, hv⟩ := add_spec n (maj x false c) xs [] (by simp only [List.length_cons, List.length_nil] at hl ⊢; omega)
    refine ⟨xor3 x false c :: d, (add_unfold _ _ _).trans (h.trans (consT_congr (.refl _) hd)), ?_⟩
    have := adder x false c
    simp only [val, Bool.toNat_false] at hv this ⊢; omega
  | n + 1, c, x :: xs, y :: ys, hl => by
    have h := run (add_cc x y c) (env3 addT (bl xs) (bl ys))
    simp only [OTerm.close, close_toO, close_consO] at h
    obtain ⟨d, hd, hv⟩ := add_spec n (maj x y c) xs ys (by simp only [List.length_cons, List.length_nil] at hl ⊢; omega)
    refine ⟨xor3 x y c :: d, (add_unfold _ _ _).trans (h.trans (consT_congr (.refl _) hd)), ?_⟩
    have := adder x y c
    simp only [val, Bool.toNat_false] at hv this ⊢; omega
  | 0, _, [], _ :: _, hl => absurd hl (Nat.not_succ_le_zero _)
  | 0, _, _ :: _, _, hl => absurd (Nat.le_trans (Nat.le_add_right _ _) hl) (Nat.not_succ_le_zero _)


-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

/-- The environment of a symbolic run: variable `10 + i` is the `i`-th
    term. -/
def envL (ts : List Term) : Nat → Term := fun i => ts.getD (i - 10) K

theorem boolT_sel (b : Bool) (X Y : Term) : WSteps (boolT b ⬝ X ⬝ Y) (if b then X else Y) := by
  cases b
  · exact (WSteps.left _ (.single (.K _ _))).trans (.single (.I _))
  · exact .single (.K _ _)

theorem bl_cons (b : Bool) (bs : List Bool) : bl (b :: bs) = consT (boolT b) (bl bs) := rfl

-- ---------------------------------------------------------------------------
-- Multiplication
-- ---------------------------------------------------------------------------

section
local notation "v" n => OTerm.var n

/-- `mul add self a b`: shift and add, over the digits of `a`. -/
def mulG : Term :=
  lam [0, 1, 2, 3]
    ((v 2) ⬝ₒ .K ⬝ₒ absN [4, 5] ((v 0) ⬝ₒ ffO ⬝ₒ ((v 4) ⬝ₒ (v 3) ⬝ₒ .K) ⬝ₒ consO ffO ((v 1) ⬝ₒ (v 5) ⬝ₒ (v 3))))
end

def mulT : Term := thetaT ⬝ (mulG ⬝ addT)

theorem mul_n : wnf 200 (mulG.toO ⬝ₒ .var 10 ⬝ₒ .var 11 ⬝ₒ .K ⬝ₒ .var 12) = .K := by decide

theorem mul_c : ∀ x : Bool,
    wnf 200 (mulG.toO ⬝ₒ .var 10 ⬝ₒ .var 11 ⬝ₒ consO (boolT x).toO (.var 13) ⬝ₒ .var 12) =
      .var 10 ⬝ₒ ffO ⬝ₒ (if x then .var 12 else .K) ⬝ₒ consO ffO (.var 11 ⬝ₒ .var 13 ⬝ₒ .var 12) := by
  decide

theorem mul_unfold (a b : Term) : WSteps (mulT ⬝ a ⬝ b) (mulG ⬝ addT ⬝ mulT ⬝ a ⬝ b) :=
  WSteps.left _ (WSteps.left _ (theta_unfold _))

/-- **Multiplication.** -/
theorem mul_spec (b : List Bool) : ∀ a : List Bool,
    ∃ d, WSteps (mulT ⬝ bl a ⬝ bl b) (bl d) ∧ val d = val a * val b
  | [] => by
    refine ⟨[], ?_, by simp only [val, Nat.zero_mul]⟩
    have h := run mul_n (envL [addT, mulT, bl b])
    exact (mul_unfold _ _).trans h
  | x :: xs => by
    have h := run (mul_c x) (envL [addT, mulT, bl b, bl xs])
    simp only [OTerm.close, close_toO, close_consO] at h
    obtain ⟨d₁, h₁, v₁⟩ := mul_spec b xs
    obtain ⟨d, hd, vd⟩ := add_spec ((if x then b else []).length + (false :: d₁).length) false
      (if x then b else []) (false :: d₁) (Nat.le_refl _)
    refine ⟨d, ?_, ?_⟩
    · refine (mul_unfold _ _).trans (h.trans ?_)
      have hsel : (if x then OTerm.var 12 else OTerm.K).close (envL [addT, mulT, bl b, bl xs]) =
          bl (if x then b else []) := by cases x <;> rfl
      show WSteps (addT ⬝ boolT false ⬝ _ ⬝ consT (boolT false) (mulT ⬝ bl xs ⬝ bl b)) _
      rw [hsel]
      exact (WSteps.right _ (consT_congr (.refl _) h₁)).trans hd
    · have hx : val (if x then b else []) = x.toNat * val b := by
        cases x
        · simp only [val, Bool.toNat_false, Nat.zero_mul]; rfl
        · simp only [Bool.toNat_true, Nat.one_mul]; rfl
      rw [vd, hx]
      simp only [val, Bool.toNat_false, Nat.zero_add, v₁, Nat.add_mul, Nat.mul_assoc]

-- ---------------------------------------------------------------------------
-- Comparison and subtraction
-- ---------------------------------------------------------------------------

/-- The borrow of `x - y - c`: `x < y + c`. -/
def borrowO (x y c : OTerm) : OTerm := x ⬝ₒ (y ⬝ₒ c ⬝ₒ ffO) ⬝ₒ (y ⬝ₒ ttO ⬝ₒ c)

def borrow (x y c : Bool) : Bool := (!x && (y || c)) || (y && c)

theorem borrow_eq (x y c : Bool) : borrow x y c = decide (x.toNat < y.toNat + c.toNat) := by
  cases x <;> cases y <;> cases c <;> rfl

theorem suber (x y c : Bool) :
    x.toNat + 2 * (borrow x y c).toNat = y.toNat + c.toNat + (xor3 x y c).toNat := by
  cases x <;> cases y <;> cases c <;> rfl

section
local notation "v" n => OTerm.var n

/-- `lt self c a b`: whether `a < b + c`, from the least significant digit
    up, a missing digit read as 0. -/
def ltG : Term :=
  lam [0, 1, 2, 3]
    ((v 2) ⬝ₒ ((v 3) ⬝ₒ (v 1) ⬝ₒ absN [6, 7] ((v 0) ⬝ₒ borrowO ffO (v 6) (v 1) ⬝ₒ .K ⬝ₒ (v 7)))
      ⬝ₒ absN [4, 5] ((v 3) ⬝ₒ ((v 0) ⬝ₒ borrowO (v 4) ffO (v 1) ⬝ₒ (v 5) ⬝ₒ .K)
        ⬝ₒ absN [6, 7] ((v 0) ⬝ₒ borrowO (v 4) (v 6) (v 1) ⬝ₒ (v 5) ⬝ₒ (v 7))))

def subStep (x xs y ys : OTerm) : OTerm :=
  consO (xor3O x y (v 1)) ((v 0) ⬝ₒ borrowO x y (v 1) ⬝ₒ xs ⬝ₒ ys)

/-- `sub self c a b`: `a - b - c`, when `b + c ≤ a`. -/
def subG : Term :=
  lam [0, 1, 2, 3]
    ((v 2) ⬝ₒ ((v 3) ⬝ₒ .K ⬝ₒ absN [6, 7] (subStep ffO .K (v 6) (v 7)))
      ⬝ₒ absN [4, 5] ((v 3) ⬝ₒ subStep (v 4) (v 5) ffO .K ⬝ₒ absN [6, 7] (subStep (v 4) (v 5) (v 6) (v 7))))
end

def ltT : Term := thetaT ⬝ ltG
def subT : Term := thetaT ⬝ subG

theorem lt_nn : ∀ c : Bool,
    wnf 200 (ltG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ .K ⬝ₒ .K) = (boolT c).toO := by decide

theorem lt_nc : ∀ y c : Bool,
    wnf 200 (ltG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ .K ⬝ₒ consO (boolT y).toO (.var 12)) =
      .var 10 ⬝ₒ (boolT (borrow false y c)).toO ⬝ₒ .K ⬝ₒ .var 12 := by decide

theorem lt_cn : ∀ x c : Bool,
    wnf 200 (ltG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ consO (boolT x).toO (.var 11) ⬝ₒ .K) =
      .var 10 ⬝ₒ (boolT (borrow x false c)).toO ⬝ₒ .var 11 ⬝ₒ .K := by decide

theorem lt_cc : ∀ x y c : Bool,
    wnf 200 (ltG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ consO (boolT x).toO (.var 11)
      ⬝ₒ consO (boolT y).toO (.var 12)) =
      .var 10 ⬝ₒ (boolT (borrow x y c)).toO ⬝ₒ .var 11 ⬝ₒ .var 12 := by decide

theorem sub_nn : ∀ c : Bool,
    wnf 200 (subG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ .K ⬝ₒ .K) = .K := by decide

theorem sub_nc : ∀ y c : Bool,
    wnf 200 (subG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ .K ⬝ₒ consO (boolT y).toO (.var 12)) =
      consO (boolT (xor3 false y c)).toO (.var 10 ⬝ₒ (boolT (borrow false y c)).toO ⬝ₒ .K ⬝ₒ .var 12) := by
  decide

theorem sub_cn : ∀ x c : Bool,
    wnf 200 (subG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ consO (boolT x).toO (.var 11) ⬝ₒ .K) =
      consO (boolT (xor3 x false c)).toO (.var 10 ⬝ₒ (boolT (borrow x false c)).toO ⬝ₒ .var 11 ⬝ₒ .K) := by
  decide

theorem sub_cc : ∀ x y c : Bool,
    wnf 200 (subG.toO ⬝ₒ .var 10 ⬝ₒ (boolT c).toO ⬝ₒ consO (boolT x).toO (.var 11)
      ⬝ₒ consO (boolT y).toO (.var 12)) =
      consO (boolT (xor3 x y c)).toO (.var 10 ⬝ₒ (boolT (borrow x y c)).toO ⬝ₒ .var 11 ⬝ₒ .var 12) := by
  decide


theorem lt_unfold (c a b : Term) : WSteps (ltT ⬝ c ⬝ a ⬝ b) (ltG ⬝ ltT ⬝ c ⬝ a ⬝ b) :=
  WSteps.left _ (WSteps.left _ (WSteps.left _ (theta_unfold ltG)))

theorem sub_unfold (c a b : Term) : WSteps (subT ⬝ c ⬝ a ⬝ b) (subG ⬝ subT ⬝ c ⬝ a ⬝ b) :=
  WSteps.left _ (WSteps.left _ (WSteps.left _ (theta_unfold subG)))

theorem lt_step (x y c : Bool) (A B : Nat) :
    decide (x.toNat + 2 * A < y.toNat + 2 * B + c.toNat) = decide (A < B + (borrow x y c).toNat) := by
  have hs := suber x y c
  have hd : (xor3 x y c).toNat ≤ 1 := by cases xor3 x y c <;> decide
  apply decide_eq_decide.mpr
  constructor
  · intro h; omega
  · intro h; omega

/-- **Comparison**: `lt c a b` is the Boolean `a < b + c`. -/
theorem lt_spec : ∀ (n : Nat) (c : Bool) (a b : List Bool), a.length + b.length ≤ n →
    WSteps (ltT ⬝ boolT c ⬝ bl a ⬝ bl b) (boolT (decide (val a < val b + c.toNat)))
  | _, c, [], [], _ => by
    have h := run (lt_nn c) (envL [ltT])
    simp only [OTerm.close, close_toO] at h
    have e : c = decide (val [] < val [] + c.toNat) := by cases c <;> rfl
    rw [← e]
    exact (lt_unfold _ _ _).trans h
  | n + 1, c, [], y :: ys, hl => by
    have h := run (lt_nc y c) (envL [ltT, K, bl ys])
    simp only [OTerm.close, close_toO, close_consO] at h
    have ih := lt_spec n (borrow false y c) [] ys (by simp only [List.length_cons, List.length_nil] at hl ⊢; omega)
    have e : decide (val [] < val (y :: ys) + c.toNat) = decide (val [] < val ys + (borrow false y c).toNat) :=
      lt_step false y c (val []) (val ys)
    rw [e]
    exact (lt_unfold _ _ _).trans (h.trans ih)
  | n + 1, c, x :: xs, [], hl => by
    have h := run (lt_cn x c) (envL [ltT, bl xs])
    simp only [OTerm.close, close_toO, close_consO] at h
    have ih := lt_spec n (borrow x false c) xs [] (by simp only [List.length_cons, List.length_nil] at hl ⊢; omega)
    have e : decide (val (x :: xs) < val [] + c.toNat) = decide (val xs < val [] + (borrow x false c).toNat) :=
      lt_step x false c (val xs) (val [])
    rw [e]
    exact (lt_unfold _ _ _).trans (h.trans ih)
  | n + 1, c, x :: xs, y :: ys, hl => by
    have h := run (lt_cc x y c) (envL [ltT, bl xs, bl ys])
    simp only [OTerm.close, close_toO, close_consO] at h
    have ih := lt_spec n (borrow x y c) xs ys (by simp only [List.length_cons, List.length_nil] at hl ⊢; omega)
    have e : decide (val (x :: xs) < val (y :: ys) + c.toNat) = decide (val xs < val ys + (borrow x y c).toNat) :=
      lt_step x y c (val xs) (val ys)
    rw [e]
    exact (lt_unfold _ _ _).trans (h.trans ih)
  | 0, _, [], _ :: _, hl => absurd hl (Nat.not_succ_le_zero _)
  | 0, _, _ :: _, _, hl => absurd (Nat.le_trans (Nat.le_add_right _ _) hl) (Nat.not_succ_le_zero _)

/-- **Subtraction**: `sub c a b` is `a - b - c`, when `b + c ≤ a`. -/
theorem sub_spec : ∀ (n : Nat) (c : Bool) (a b : List Bool), a.length + b.length ≤ n →
    val b + c.toNat ≤ val a →
    ∃ d, WSteps (subT ⬝ boolT c ⬝ bl a ⬝ bl b) (bl d) ∧ val d + val b + c.toNat = val a
  | _, c, [], [], _, hv => by
    refine ⟨[], ?_, ?_⟩
    · have h := run (sub_nn c) (envL [subT])
      simp only [OTerm.close, close_toO] at h
      exact (sub_unfold _ _ _).trans h
    · simp only [val] at hv ⊢; omega
  | n + 1, c, [], y :: ys, hl, hv => by
    have h := run (sub_nc y c) (envL [subT, K, bl ys])
    simp only [OTerm.close, close_toO, close_consO] at h
    have hs := suber false y c
    have hd : (xor3 false y c).toNat ≤ 1 := by cases xor3 false y c <;> decide
    simp only [val, Bool.toNat_false] at hv hs
    obtain ⟨d, hd', vd⟩ := sub_spec n (borrow false y c) [] ys
      (by simp only [List.length_cons, List.length_nil] at hl ⊢; omega) (by simp only [val]; omega)
    refine ⟨xor3 false y c :: d, (sub_unfold _ _ _).trans (h.trans (consT_congr (.refl _) hd')), ?_⟩
    simp only [val, Bool.toNat_false] at vd ⊢; omega
  | n + 1, c, x :: xs, [], hl, hv => by
    have h := run (sub_cn x c) (envL [subT, bl xs])
    simp only [OTerm.close, close_toO, close_consO] at h
    have hs := suber x false c
    have hd : (xor3 x false c).toNat ≤ 1 := by cases xor3 x false c <;> decide
    simp only [val, Bool.toNat_false] at hv hs
    obtain ⟨d, hd', vd⟩ := sub_spec n (borrow x false c) xs []
      (by simp only [List.length_cons, List.length_nil] at hl ⊢; omega) (by simp only [val]; omega)
    refine ⟨xor3 x false c :: d, (sub_unfold _ _ _).trans (h.trans (consT_congr (.refl _) hd')), ?_⟩
    simp only [val, Bool.toNat_false] at vd ⊢; omega
  | n + 1, c, x :: xs, y :: ys, hl, hv => by
    have h := run (sub_cc x y c) (envL [subT, bl xs, bl ys])
    simp only [OTerm.close, close_toO, close_consO] at h
    have hs := suber x y c
    have hd : (xor3 x y c).toNat ≤ 1 := by cases xor3 x y c <;> decide
    simp only [val] at hv
    obtain ⟨d, hd', vd⟩ := sub_spec n (borrow x y c) xs ys
      (by simp only [List.length_cons, List.length_nil] at hl ⊢; omega) (by omega)
    refine ⟨xor3 x y c :: d, (sub_unfold _ _ _).trans (h.trans (consT_congr (.refl _) hd')), ?_⟩
    simp only [val] at vd ⊢; omega
  | 0, _, [], _ :: _, hl, _ => absurd hl (Nat.not_succ_le_zero _)
  | 0, _, _ :: _, _, hl, _ => absurd (Nat.le_trans (Nat.le_add_right _ _) hl) (Nat.not_succ_le_zero _)


-- ---------------------------------------------------------------------------
-- Leading zeros dropped
-- ---------------------------------------------------------------------------

section
local notation "v" n => OTerm.var n

/-- `[b t] t (b [1] []) ([_ _] cons b t)`: the digit `b` on a trimmed `t`,
    dropped when it would be a leading 0. -/
def tstep : Term := lam [0, 1] ((v 1) ⬝ₒ ((v 0) ⬝ₒ consO ttO .K ⬝ₒ .K) ⬝ₒ absN [2, 3] (consO (v 0) (v 1)))

/-- `trim tstep self a`: `a` without its leading zeros. -/
def trimG : Term := lam [0, 1, 2] ((v 2) ⬝ₒ .K ⬝ₒ absN [3, 4] ((v 0) ⬝ₒ (v 3) ⬝ₒ ((v 1) ⬝ₒ (v 4))))
end

def trimT : Term := thetaT ⬝ (trimG ⬝ tstep)

theorem trim_n : wnf 200 (trimG.toO ⬝ₒ .var 10 ⬝ₒ .var 11 ⬝ₒ .K) = .K := by decide

theorem trim_c : wnf 200 (trimG.toO ⬝ₒ .var 10 ⬝ₒ .var 11 ⬝ₒ consO (.var 12) (.var 13)) =
    .var 10 ⬝ₒ .var 12 ⬝ₒ (.var 11 ⬝ₒ .var 13) := by decide

theorem tstep_n : ∀ b : Bool,
    wnf 200 (tstep.toO ⬝ₒ (boolT b).toO ⬝ₒ .K) = (bl (if b then [true] else [])).toO := by decide

theorem tstep_c : ∀ b : Bool,
    wnf 200 (tstep.toO ⬝ₒ (boolT b).toO ⬝ₒ consO (.var 12) (.var 13)) =
      consO (boolT b).toO (consO (.var 12) (.var 13)) := by decide

theorem trim_unfold (a : Term) : WSteps (trimT ⬝ a) (trimG ⬝ tstep ⬝ trimT ⬝ a) :=
  WSteps.left _ (theta_unfold _)

/-- **Trimming keeps the value.** -/
theorem trim_spec : ∀ bs : List Bool, ∃ d, WSteps (trimT ⬝ bl bs) (bl d) ∧ val d = val bs
  | [] => ⟨[], (trim_unfold _).trans (run trim_n (envL [tstep, trimT])), rfl⟩
  | b :: bs => by
    have h := run trim_c (envL [tstep, trimT, boolT b, bl bs])
    simp only [OTerm.close, close_toO, close_consO] at h
    obtain ⟨d, hd, vd⟩ := trim_spec bs
    have h₁ := (trim_unfold _).trans (h.trans (WSteps.right _ hd))
    cases d with
    | nil =>
      have h₂ := run (tstep_n b) (envL [])
      simp only [OTerm.close, close_toO] at h₂
      refine ⟨if b then [true] else [], h₁.trans h₂, ?_⟩
      show _ = b.toNat + 2 * val bs
      rw [← vd]
      cases b <;> rfl
    | cons e es =>
      have h₂ := run (tstep_c b) (envL [K, K, boolT e, bl es])
      simp only [OTerm.close, close_toO, close_consO] at h₂
      refine ⟨b :: e :: es, h₁.trans h₂, ?_⟩
      show b.toNat + 2 * val (e :: es) = b.toNat + 2 * val bs
      rw [vd]

-- ---------------------------------------------------------------------------
-- Reduction modulo a constant
-- ---------------------------------------------------------------------------

section
local notation "v" n => OTerm.var n

/-- `r` if `r < m`, else `r - m`. -/
def redO (r : OTerm) : OTerm := ((v 0) ⬝ₒ ffO ⬝ₒ r ⬝ₒ (v 2)) ⬝ₒ r ⬝ₒ ((v 1) ⬝ₒ ffO ⬝ₒ r ⬝ₒ (v 2))

/-- `mod lt sub m trim self a`: from the most significant digit down,
    `a mod m = red (b + 2 (a' mod m))` for `a = b + 2 a'`.
    - The partial remainder is bound once, `[r] red r` applied to it, so a
      reducer that shares arguments computes it once; written three times
      in `red`, it would be three recursive calls, and the cost would
      double a digit.
    - `a' mod m` is trimmed, so the partial remainder has at most one digit
      more than `m`, and each digit's comparison and subtraction run over
      that many digits, not over all of `a`'s. -/
def modG : Term :=
  lam [0, 1, 2, 8, 3, 4]
    ((v 4) ⬝ₒ .K ⬝ₒ absN [5, 6] (absN [7] (redO (v 7)) ⬝ₒ consO (v 5) ((v 8) ⬝ₒ ((v 3) ⬝ₒ (v 6)))))
end

/-- Reduction modulo the number `m`. -/
def modT (m : List Bool) : Term := thetaT ⬝ (modG ⬝ ltT ⬝ subT ⬝ bl m ⬝ trimT)

theorem mod_n : wnf 200 (modG.toO ⬝ₒ .var 10 ⬝ₒ .var 11 ⬝ₒ .var 12 ⬝ₒ .var 15 ⬝ₒ .var 13 ⬝ₒ .K) = .K := by
  decide

theorem mod_c : ∀ x : Bool,
    wnf 200 (modG.toO ⬝ₒ .var 10 ⬝ₒ .var 11 ⬝ₒ .var 12 ⬝ₒ .var 15 ⬝ₒ .var 13 ⬝ₒ consO (boolT x).toO (.var 14)) =
      (.var 10 ⬝ₒ ffO ⬝ₒ consO (boolT x).toO (.var 15 ⬝ₒ (.var 13 ⬝ₒ .var 14)) ⬝ₒ .var 12)
        ⬝ₒ consO (boolT x).toO (.var 15 ⬝ₒ (.var 13 ⬝ₒ .var 14))
        ⬝ₒ (.var 11 ⬝ₒ ffO ⬝ₒ consO (boolT x).toO (.var 15 ⬝ₒ (.var 13 ⬝ₒ .var 14)) ⬝ₒ .var 12) := by
  decide

theorem mod_unfold (m : List Bool) (a : Term) :
    WSteps (modT m ⬝ a) (modG ⬝ ltT ⬝ subT ⬝ bl m ⬝ trimT ⬝ modT m ⬝ a) :=
  WSteps.left _ (theta_unfold _)

/-- One digit of long division: `R = b + 2 (n mod M)` is below `2 M` and
    congruent to `b + 2 n`. -/
theorem mod_step (b : Bool) (n M : Nat) (hM : 0 < M) :
    (b.toNat + 2 * n) % M = (b.toNat + 2 * (n % M)) % M ∧ b.toNat + 2 * (n % M) < 2 * M := by
  have hlt := Nat.mod_lt n hM
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  refine ⟨?_, by omega⟩
  have e : b.toNat + 2 * n = (b.toNat + 2 * (n % M)) + M * (2 * (n / M)) := by
    have := Nat.mod_add_div n M
    rw [Nat.mul_left_comm, Nat.add_assoc, ← Nat.mul_add, this]
  rw [e, Nat.add_mul_mod_self_left]

/-- **Reduction modulo `m`.** -/
theorem mod_spec (m : List Bool) (hm : 0 < val m) : ∀ a : List Bool,
    ∃ d, WSteps (modT m ⬝ bl a) (bl d) ∧ val d = val a % val m
  | [] => ⟨[], (mod_unfold m _).trans (run mod_n (envL [ltT, subT, bl m, modT m, K, trimT])),
      by simp only [val, Nat.zero_mod]⟩
  | x :: xs => by
    have h := run (mod_c x) (envL [ltT, subT, bl m, modT m, bl xs, trimT])
    simp only [OTerm.close, close_toO, close_consO] at h
    obtain ⟨e₀, he₀, ve₀⟩ := mod_spec m hm xs
    obtain ⟨e, he, ve⟩ := trim_spec e₀
    rw [ve₀] at ve
    have hr : WSteps (consT (boolT x) (trimT ⬝ (modT m ⬝ bl xs))) (bl (x :: e)) :=
      consT_congr (.refl _) ((WSteps.right _ he₀).trans he)
    have hlt := lt_spec ((x :: e).length + m.length) false (x :: e) m (Nat.le_refl _)
    obtain ⟨hcong, hbound⟩ := mod_step x (val xs) (val m) hm
    have hR : val (x :: e) = x.toNat + 2 * (val xs % val m) := by simp only [val, ve]
    have hsel := boolT_sel (decide (val (x :: e) < val m + (false).toNat))
      (consT (boolT x) (trimT ⬝ (modT m ⬝ bl xs))) (subT ⬝ boolT false ⬝ consT (boolT x) (trimT ⬝ (modT m ⬝ bl xs)) ⬝ bl m)
    have h1 : WSteps (ltT ⬝ boolT false ⬝ consT (boolT x) (trimT ⬝ (modT m ⬝ bl xs)) ⬝ bl m)
        (boolT (decide (val (x :: e) < val m + (false).toNat))) :=
      (WSteps.left _ (WSteps.right _ hr)).trans hlt
    have hpre := (mod_unfold m _).trans (h.trans ((WSteps.left _ (WSteps.left _ h1)).trans hsel))
    have hval : val (x :: xs) % val m = val (x :: e) % val m := by
      show (x.toNat + 2 * val xs) % val m = val (x :: e) % val m
      rw [hcong, hR]
    by_cases hc : val (x :: e) < val m + (false).toNat
    · rw [if_pos (decide_eq_true hc)] at hpre
      refine ⟨x :: e, hpre.trans hr, ?_⟩
      rw [hval, Nat.mod_eq_of_lt (by simpa using hc)]
    · rw [if_neg (by simpa using hc)] at hpre
      have hge : val m + (false).toNat ≤ val (x :: e) := Nat.le_of_not_lt hc
      obtain ⟨d, hd, vd⟩ := sub_spec ((x :: e).length + m.length) false (x :: e) m (Nat.le_refl _) hge
      refine ⟨d, hpre.trans ((WSteps.left _ (WSteps.right _ hr)).trans hd), ?_⟩
      simp only [Bool.toNat_false, Nat.add_zero] at vd hge
      rw [hval, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      omega


-- ---------------------------------------------------------------------------
-- Literals
-- ---------------------------------------------------------------------------

/-- The low `k` bits of `n`, least significant first. -/
def bitsOf : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: bitsOf k (n / 2)

theorem bit_toNat (n : Nat) : (n % 2 == 1).toNat = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> rfl

/-- `n mod 2m` from the low bit and `n / 2 mod m` (core's `Nat.mod_mul`
    depends on `Classical.choice`). -/
theorem mod_two_mul (n m : Nat) (hm : 0 < m) : n % (2 * m) = n % 2 + 2 * (n / 2 % m) := by
  have h1 := Nat.mod_add_div n 2
  have h2 := Nat.mod_add_div (n / 2) m
  have hlt1 := Nat.mod_lt n (by decide : 0 < 2)
  have hlt2 := Nat.mod_lt (n / 2) hm
  have e : n = (n % 2 + 2 * (n / 2 % m)) + 2 * m * (n / 2 / m) := by
    rw [Nat.mul_assoc]
    generalize m * (n / 2 / m) = Y at h2 ⊢
    omega
  calc n % (2 * m) = ((n % 2 + 2 * (n / 2 % m)) + 2 * m * (n / 2 / m)) % (2 * m) := congrArg (· % (2 * m)) e
    _ = (n % 2 + 2 * (n / 2 % m)) % (2 * m) := Nat.add_mul_mod_self_left _ _ _
    _ = n % 2 + 2 * (n / 2 % m) := Nat.mod_eq_of_lt (by omega)

theorem val_bitsOf : ∀ (k n : Nat), val (bitsOf k n) = n % 2 ^ k
  | 0, n => by simp only [bitsOf, val, Nat.pow_zero, Nat.mod_one]
  | k + 1, n => by
    simp only [bitsOf, val, val_bitsOf k (n / 2), bit_toNat]
    rw [Nat.pow_succ', mod_two_mul n _ (Nat.two_pow_pos k)]

/-- A literal, in as many bits as it needs. -/
def litT (n : Nat) : Term := bl (bitsOf (n.log2 + 1) n)

theorem val_lit (n : Nat) : val (bitsOf (n.log2 + 1) n) = n := by
  rw [val_bitsOf, Nat.mod_eq_of_lt Nat.lt_log2_self]

-- ---------------------------------------------------------------------------
-- Values up to reduction
-- ---------------------------------------------------------------------------

/-- `t` reduces to a number whose value is `n`. -/
def RepR (t : Term) (n : Nat) : Prop := ∃ bs, WSteps t (bl bs) ∧ val bs = n

theorem RepR.back {t t' : Term} {n : Nat} (h : WSteps t t') (r : RepR t' n) : RepR t n :=
  let ⟨bs, hb, vb⟩ := r; ⟨bs, h.trans hb, vb⟩

theorem RepR.lit (n : Nat) : RepR (litT n) n := ⟨_, .refl _, val_lit n⟩

theorem RepR.add {a b : Term} {x y : Nat} (ha : RepR a x) (hb : RepR b y) :
    RepR (addT ⬝ boolT false ⬝ a ⬝ b) (x + y) := by
  obtain ⟨as, ha, va⟩ := ha
  obtain ⟨bs, hb, vb⟩ := hb
  obtain ⟨d, hd, vd⟩ := add_spec (as.length + bs.length) false as bs (Nat.le_refl _)
  refine ⟨d, (WSteps.app (WSteps.right _ ha) hb).trans hd, ?_⟩
  rw [vd, va, vb]; simp only [Bool.toNat_false, Nat.zero_add]

theorem RepR.mul {a b : Term} {x y : Nat} (ha : RepR a x) (hb : RepR b y) :
    RepR (mulT ⬝ a ⬝ b) (x * y) := by
  obtain ⟨as, ha, va⟩ := ha
  obtain ⟨bs, hb, vb⟩ := hb
  obtain ⟨d, hd, vd⟩ := mul_spec bs as
  exact ⟨d, (WSteps.app (WSteps.right _ ha) hb).trans hd, by rw [vd, va, vb]⟩

theorem RepR.mod {m : List Bool} (hm : 0 < val m) {a : Term} {x : Nat} (ha : RepR a x) :
    RepR (modT m ⬝ a) (x % val m) := by
  obtain ⟨as, ha, va⟩ := ha
  obtain ⟨d, hd, vd⟩ := mod_spec m hm as
  exact ⟨d, (WSteps.right _ ha).trans hd, by rw [vd, va]⟩

-- ---------------------------------------------------------------------------
-- The power seven
-- ---------------------------------------------------------------------------

section
local notation "v" n => OTerm.var n

/-- `[x] (x (x (x (x (x (x x)))))) mod m`, the products by `mul`, which
    runs over the digits of its first argument: `x`, not the growing
    product. -/
def pow7T (m : List Bool) : Term :=
  lam [0] ((modT m).toO ⬝ₒ (mulT.toO ⬝ₒ (v 0) ⬝ₒ (mulT.toO ⬝ₒ (v 0) ⬝ₒ (mulT.toO ⬝ₒ (v 0) ⬝ₒ
    (mulT.toO ⬝ₒ (v 0) ⬝ₒ (mulT.toO ⬝ₒ (v 0) ⬝ₒ (mulT.toO ⬝ₒ (v 0) ⬝ₒ (v 0))))))))
end

theorem RepR.pow7 {m : List Bool} (hm : 0 < val m) {a : Term} {x : Nat} (ha : RepR a x) :
    RepR (pow7T m ⬝ a) (x ^ 7 % val m) := by
  have hb := lam_beta [0] ((modT m).toO ⬝ₒ (mulT.toO ⬝ₒ .var 0 ⬝ₒ (mulT.toO ⬝ₒ .var 0 ⬝ₒ (mulT.toO ⬝ₒ .var 0 ⬝ₒ
    (mulT.toO ⬝ₒ .var 0 ⬝ₒ (mulT.toO ⬝ₒ .var 0 ⬝ₒ (mulT.toO ⬝ₒ .var 0 ⬝ₒ .var 0)))))))
    [a] rfl
  simp only [OTerm.close, close_toO] at hb
  have e : x ^ 7 = x * (x * (x * (x * (x * (x * x))))) := by
    simp only [Nat.pow_succ', Nat.pow_zero, Nat.mul_one]
  rw [e]
  exact RepR.back hb (RepR.mod hm (ha.mul (ha.mul (ha.mul (ha.mul (ha.mul (ha.mul ha)))))))

end BitArith
