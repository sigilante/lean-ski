import Ski.Circuit.Field

/-!
# The circuit's expressions, and their normal form

Plonky3 records an AIR as symbolic expressions over its columns
(`p3_air::symbolic`).  `E` is that language: main and preprocessed columns
at a row offset, the first-row, last-row and transition selectors,
constants, `+ - ×` and negation.  `E.eval` is its meaning at a row.

**The normal form** (`E.norm`): a polynomial as a sorted list of
monomials with their coefficients, like terms merged and zeros dropped.
It is computable, and it keeps the meaning (`eval_norm`).  So two
expressions with the same normal form mean the same everywhere
(`eval_eq_of_norm`): what `lake exe circuit compare` checks between the
Rust circuit and the Lean one.
-/

namespace Circuit

open Lean.Grind

/-- A leaf: a main or preprocessed column `i` at row offset `o`, or a
    selector. -/
inductive Atom
  | main (o i : Nat)
  | pre (o i : Nat)
  | first
  | last
  | trans
  deriving DecidableEq, Repr

/-- Cantor's pairing. -/
def pairNat (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

/-- The order leaves sort by. -/
def Atom.key : Atom → Nat
  | .main o i => 5 * pairNat o i
  | .pre o i => 5 * pairNat o i + 1
  | .first => 2
  | .last => 3
  | .trans => 4

/-- An expression. -/
inductive E
  | atom (a : Atom)
  | const (c : F)
  | add (a b : E)
  | sub (a b : E)
  | mul (a b : E)
  | neg (a : E)
  deriving Repr

/-- Its meaning, given the leaves' values. -/
def E.eval (ρ : Atom → F) : E → F
  | .atom a => ρ a
  | .const c => c
  | .add a b => a.eval ρ + b.eval ρ
  | .sub a b => a.eval ρ - b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ
  | .neg a => -(a.eval ρ)

-- ---------------------------------------------------------------------------
-- Ring facts, from Lean's `CommRing (Fin P)`
-- ---------------------------------------------------------------------------

theorem add_comm' (a b : F) : a + b = b + a := AddCommMonoid.add_comm a b
theorem add_assoc' (a b c : F) : a + b + c = a + (b + c) := AddCommMonoid.add_assoc a b c
theorem zero_add' (a : F) : 0 + a = a := AddCommMonoid.zero_add a
theorem add_zero' (a : F) : a + 0 = a := AddCommMonoid.add_zero a
theorem mul_comm' (a b : F) : a * b = b * a := CommSemiring.mul_comm a b
theorem mul_assoc' (a b c : F) : a * b * c = a * (b * c) := Semiring.mul_assoc a b c
theorem one_mul' (a : F) : 1 * a = a := Semiring.one_mul a
theorem mul_one' (a : F) : a * 1 = a := Semiring.mul_one a
theorem zero_mul' (a : F) : 0 * a = 0 := Semiring.zero_mul a
theorem mul_zero' (a : F) : a * 0 = 0 := Semiring.mul_zero a
theorem left_distrib' (a b c : F) : a * (b + c) = a * b + a * c := Semiring.left_distrib a b c
theorem right_distrib' (a b c : F) : (a + b) * c = a * c + b * c := Semiring.right_distrib a b c
theorem sub_eq_add_neg' (a b : F) : a - b = a + -b := Ring.sub_eq_add_neg a b
theorem neg_add_cancel' (a : F) : -a + a = 0 := Ring.neg_add_cancel a

theorem neg_eq_neg_one_mul (a : F) : -a = -1 * a := by
  have h : -1 * a + a = 0 := by
    rw [show -1 * a + a = -1 * a + 1 * a by rw [one_mul'], ← right_distrib', neg_add_cancel',
      zero_mul']
  calc -a = -a + (-1 * a + a) := by rw [h, add_zero']
    _ = -1 * a + (-a + a) := by rw [← add_assoc', ← add_assoc', add_comm' (-a) (-1 * a)]
    _ = -1 * a := by rw [neg_add_cancel', add_zero']

theorem neg_mul' (a b : F) : -a * b = -(a * b) := by
  rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul (a * b), mul_assoc']

-- ---------------------------------------------------------------------------
-- Monomials and polynomials
-- ---------------------------------------------------------------------------

/-- A monomial: its leaves, sorted by key, with repetition. -/
abbrev Mono := List Atom

def meval (ρ : Atom → F) (m : Mono) : F := m.foldr (fun a acc => ρ a * acc) 1

/-- Insert a leaf in key order. -/
def minsert (a : Atom) : Mono → Mono
  | [] => [a]
  | b :: m => if a.key ≤ b.key then a :: b :: m else b :: minsert a m

theorem meval_insert (ρ : Atom → F) (a : Atom) : ∀ m : Mono,
    meval ρ (minsert a m) = ρ a * meval ρ m
  | [] => rfl
  | b :: m => by
    unfold minsert
    split
    · rfl
    · show ρ b * meval ρ (minsert a m) = ρ a * (ρ b * meval ρ m)
      rw [meval_insert ρ a m, ← mul_assoc', ← mul_assoc', mul_comm' (ρ b) (ρ a)]

/-- The product of two monomials. -/
def mmul (m₁ m₂ : Mono) : Mono := m₁.foldr minsert m₂

theorem meval_mul (ρ : Atom → F) : ∀ m₁ m₂ : Mono,
    meval ρ (mmul m₁ m₂) = meval ρ m₁ * meval ρ m₂
  | [], m₂ => by show meval ρ m₂ = 1 * meval ρ m₂; rw [one_mul']
  | a :: m₁, m₂ => by
    show meval ρ (minsert a (mmul m₁ m₂)) = ρ a * meval ρ m₁ * meval ρ m₂
    rw [meval_insert, meval_mul ρ m₁ m₂, mul_assoc']

/-- Lexicographic order on monomials, by keys. -/
def monoLt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: m, b :: n => if a.key < b.key then true else if b.key < a.key then false else monoLt m n

/-- A polynomial: monomials with coefficients. -/
abbrev Poly := List (Mono × F)

def peval (ρ : Atom → F) (p : Poly) : F := p.foldr (fun t acc => t.2 * meval ρ t.1 + acc) 0

/-- Insert a term, merging a like term, keeping the order. -/
def pinsert (t : Mono × F) : Poly → Poly
  | [] => [t]
  | u :: p =>
    if t.1 = u.1 then (u.1, t.2 + u.2) :: p
    else if monoLt t.1 u.1 then t :: u :: p
    else u :: pinsert t p

theorem peval_insert (ρ : Atom → F) (t : Mono × F) : ∀ p : Poly,
    peval ρ (pinsert t p) = t.2 * meval ρ t.1 + peval ρ p
  | [] => rfl
  | u :: p => by
    unfold pinsert
    split
    · next h =>
      show (t.2 + u.2) * meval ρ u.1 + peval ρ p = t.2 * meval ρ t.1 + (u.2 * meval ρ u.1 + peval ρ p)
      rw [h, right_distrib', add_assoc']
    · split
      · rfl
      · show u.2 * meval ρ u.1 + peval ρ (pinsert t p) =
          t.2 * meval ρ t.1 + (u.2 * meval ρ u.1 + peval ρ p)
        rw [peval_insert ρ t p, ← add_assoc', ← add_assoc', add_comm' (u.2 * _)]

def padd (p q : Poly) : Poly := p.foldr pinsert q

theorem peval_add (ρ : Atom → F) : ∀ p q : Poly, peval ρ (padd p q) = peval ρ p + peval ρ q
  | [], q => by show peval ρ q = 0 + peval ρ q; rw [zero_add']
  | t :: p, q => by
    show peval ρ (pinsert t (padd p q)) = t.2 * meval ρ t.1 + peval ρ p + peval ρ q
    rw [peval_insert, peval_add ρ p q, add_assoc']

def pscale (c : F) (m : Mono) (q : Poly) : Poly := q.map fun u => (mmul m u.1, c * u.2)

theorem peval_scale (ρ : Atom → F) (c : F) (m : Mono) : ∀ q : Poly,
    peval ρ (pscale c m q) = c * meval ρ m * peval ρ q
  | [] => by show (0 : F) = c * meval ρ m * 0; rw [mul_zero']
  | u :: q => by
    show c * u.2 * meval ρ (mmul m u.1) + peval ρ (pscale c m q) =
      c * meval ρ m * (u.2 * meval ρ u.1 + peval ρ q)
    rw [peval_scale ρ c m q, meval_mul, left_distrib']
    congr 1
    have e : u.2 * (meval ρ m * meval ρ u.1) = meval ρ m * (u.2 * meval ρ u.1) := by
      rw [← mul_assoc', mul_comm' u.2, mul_assoc']
    rw [mul_assoc' c u.2, e, ← mul_assoc']

def pmul (p q : Poly) : Poly := p.foldr (fun t acc => padd (pscale t.2 t.1 q) acc) []

theorem peval_mul (ρ : Atom → F) : ∀ p q : Poly, peval ρ (pmul p q) = peval ρ p * peval ρ q
  | [], q => by show (0 : F) = 0 * peval ρ q; rw [zero_mul']
  | t :: p, q => by
    show peval ρ (padd (pscale t.2 t.1 q) (pmul p q)) = (t.2 * meval ρ t.1 + peval ρ p) * peval ρ q
    rw [peval_add, peval_scale, peval_mul ρ p q, right_distrib']

def pneg (p : Poly) : Poly := p.map fun u => (u.1, -u.2)

theorem peval_neg (ρ : Atom → F) : ∀ p : Poly, peval ρ (pneg p) = -(peval ρ p)
  | [] => by
    show (0 : F) = -0
    rw [neg_eq_neg_one_mul, mul_zero']
  | u :: p => by
    show -u.2 * meval ρ u.1 + peval ρ (pneg p) = -(u.2 * meval ρ u.1 + peval ρ p)
    rw [peval_neg ρ p, neg_mul', neg_eq_neg_one_mul (_ + _), left_distrib',
      ← neg_eq_neg_one_mul, ← neg_eq_neg_one_mul]

/-- Drop the zero terms. -/
def pclean (p : Poly) : Poly := p.filter fun u => u.2 != 0

theorem peval_clean (ρ : Atom → F) : ∀ p : Poly, peval ρ (pclean p) = peval ρ p
  | [] => rfl
  | u :: p => by
    unfold pclean
    rw [List.filter_cons]
    by_cases h : u.2 = 0
    · rw [if_neg (by rw [h]; decide)]
      show peval ρ (pclean p) = u.2 * meval ρ u.1 + peval ρ p
      rw [peval_clean ρ p, h, zero_mul', zero_add']
    · rw [if_pos (by simpa using h)]
      show u.2 * meval ρ u.1 + peval ρ (pclean p) = u.2 * meval ρ u.1 + peval ρ p
      rw [peval_clean ρ p]

/-- An expression as a polynomial, before cleaning. -/
def E.poly : E → Poly
  | .atom a => [([a], 1)]
  | .const c => [([], c)]
  | .add a b => padd a.poly b.poly
  | .sub a b => padd a.poly (pneg b.poly)
  | .mul a b => pmul a.poly b.poly
  | .neg a => pneg a.poly

/-- **The normal form.** -/
def E.norm (e : E) : Poly := pclean e.poly

theorem E.eval_poly (ρ : Atom → F) : ∀ e : E, peval ρ e.poly = e.eval ρ
  | .atom a => by
    show 1 * (ρ a * 1) + 0 = ρ a
    rw [one_mul', mul_one', add_zero']
  | .const c => by
    show c * 1 + 0 = c
    rw [mul_one', add_zero']
  | .add a b => by
    show peval ρ (padd a.poly b.poly) = _
    rw [peval_add, E.eval_poly ρ a, E.eval_poly ρ b]; rfl
  | .sub a b => by
    show peval ρ (padd a.poly (pneg b.poly)) = a.eval ρ - b.eval ρ
    rw [peval_add, peval_neg, E.eval_poly ρ a, E.eval_poly ρ b, sub_eq_add_neg']
  | .mul a b => by
    show peval ρ (pmul a.poly b.poly) = _
    rw [peval_mul, E.eval_poly ρ a, E.eval_poly ρ b]; rfl
  | .neg a => by
    show peval ρ (pneg a.poly) = _
    rw [peval_neg, E.eval_poly ρ a]; rfl

/-- **The normal form keeps the meaning.** -/
theorem E.eval_norm (ρ : Atom → F) (e : E) : peval ρ e.norm = e.eval ρ := by
  unfold E.norm
  rw [peval_clean, E.eval_poly]

/-- **Expressions with the same normal form mean the same everywhere.** -/
theorem E.eval_eq_of_norm {e e' : E} (h : e.norm = e'.norm) (ρ : Atom → F) :
    e.eval ρ = e'.eval ρ := by
  rw [← E.eval_norm ρ e, ← E.eval_norm ρ e', h]

end Circuit
