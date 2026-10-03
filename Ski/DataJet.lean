import Ski.Chain
import Ski.ZK.Poseidon2

set_option linter.unusedSectionVars false

open Term

/-!
# Data jets: a contract, its translation to SKI, and a hidden hand-off

A **code jet** names an SKI term and licenses native code that
reproduces that term's reduction; its contract is the term itself
(`Ski/AirJet.lean`).  A **data jet** names no term.  Its contract is a
Lean function over encoded data:

  `J ⬝ encI x ⟶ encO (spec x)`

with `spec` the specification, `encI` and `encO` the encodings of its
input and output (`Contract`).  Weak reduction with the jet (`JStep`) is
SKI's three rules, the jet's rule at the head variable `j`, and the two
congruences.  The jet's argument must reduce to an encoding first; any
other argument leaves the jet stuck.

**What a data jet means** (`JSteps.close`).  For any SKI term `P` that
implements the contract (`Implements`: `P ⬝ encI x ↠ encO (spec x)` for
every `x`), closing the jet head to `P` turns every extended reduction
into a plain weak reduction.  So a verifier that accepts under the jet
accepts as an SKI term with `P` in the jet's place, and realizes its atom
(`real_of_jet`).  This is one direction: acceptance under the jet implies
acceptance under every implementation.

**When an implementation can exist.**  The specification must be a
function of the encoding (`Contract.Respects`): two inputs with one
encoding must have one output.  When distinct outputs encode to distinct
normal forms, this is necessary, since weak reduction is confluent
(`church_rosser`); that argument is not formalized here.  An injective
input encoding gives it (`respects_of_inj`).  The toy contract has a
proved implementation (`notP_implements`).  The Poseidon2 contract
respects its encoding (`poseidon2_respects`): its inputs are states of
sixteen canonical field elements, each in 31 bits, and the encoding is
injective (`stateT_inj`).  Its implementation is an SKI term built and
proved in `Ski/ZK/Poseidon2SKI.lean` (`Poseidon2SKI.poseidon2_implements`),
so the theorems here apply to it.

**The circuit's obligation.**  The circuit must compute `spec`: a
Poseidon2 precompile, an AIR and a bus from the CPU to it, with a proof
that its accepted rows are `Poseidon2.permute`.  That is open.  The
specification it must meet is fixed, and the kernel checks it against
Plonky3's permutation on three inputs (`Poseidon2.permute_matches`).

**A hidden hand-off** (`hidden_chain`).  The public hand-off of
`Ski/Chain.lean` becomes a commitment `c = commit o r`: Plonky3's
compression `TruncatedPermutation` as specified here (the specification
of the permutation is tested against Plonky3's, not proved equal), the
permutation of the value `o` and the randomness `r`, eight canonical
elements each, truncated to eight.  Each stage's relation is that its
witness opens `c` (`Opening`, eight and eight elements) and that the
stage's own relation holds at the opened value.  From a verified proof of
each stage, the extractors give one value that opens `c` and at which
both relations hold, or two openings of `c` with different values: two
distinct inputs on which the compression agrees (`Collision`).  Binding
is the claim that no efficient prover finds such a pair.  It is
computational and not formalized, and the theorem reduces
the chain's knowledge soundness to it.  An injectivity hypothesis would
be false (sixteen elements compress to eight), so the theorem names the
collision instead of assuming none exists.

`hidden_chain` is stated over `commit`, the Lean function.  That a
stage's verifier computes `commit` is the precompile's obligation above.
Hiding needs `r` uniform and the truncated permutation to hide its input;
that is an assumption about Poseidon2 and is not formalized either.
-/

namespace DataJet

open Compose

-- ---------------------------------------------------------------------------
-- The contract and extended reduction
-- ---------------------------------------------------------------------------

/-- **A data jet's contract**: a specification and the encodings of its
    input and output. -/
structure Contract (α β : Type) where
  encI : α → Term
  encO : β → Term
  spec : α → β

/-- **Weak reduction with a data jet** at the head variable `j`: SKI's
    rules, the jet's rule, and the congruences. -/
inductive JStep {α β : Type} (c : Contract α β) (j : Nat) : OTerm → OTerm → Prop
  | S (f g x : OTerm) : JStep c j (.S ⬝ₒ f ⬝ₒ g ⬝ₒ x) (f ⬝ₒ x ⬝ₒ (g ⬝ₒ x))
  | K (x y : OTerm) : JStep c j (.K ⬝ₒ x ⬝ₒ y) x
  | I (x : OTerm) : JStep c j (.I ⬝ₒ x) x
  | jet (x : α) : JStep c j (.var j ⬝ₒ (c.encI x).toO) (c.encO (c.spec x)).toO
  | left {f f' : OTerm} (x : OTerm) (h : JStep c j f f') : JStep c j (f ⬝ₒ x) (f' ⬝ₒ x)
  | right (f : OTerm) {x x' : OTerm} (h : JStep c j x x') : JStep c j (f ⬝ₒ x) (f ⬝ₒ x')

inductive JSteps {α β : Type} (c : Contract α β) (j : Nat) : OTerm → OTerm → Prop
  | refl (t : OTerm) : JSteps c j t t
  | step {t t' u : OTerm} (h : JStep c j t t') (hs : JSteps c j t' u) : JSteps c j t u

/-- `P` **implements** the contract: on every encoded input, it reduces to
    the encoded output of the specification. -/
def Implements {α β : Type} (c : Contract α β) (P : Term) : Prop :=
  ∀ x, WSteps (P ⬝ c.encI x) (c.encO (c.spec x))

/-- One extended step closes to a plain weak reduction, the jet head
    closed to an implementation. -/
theorem JStep.close {α β : Type} {c : Contract α β} {j : Nat} (σ : Nat → Term)
    (hj : Implements c (σ j)) {t u : OTerm} (h : JStep c j t u) :
    WSteps (t.close σ) (u.close σ) := by
  induction h with
  | S f g x => exact .single (.S _ _ _)
  | K x y => exact .single (.K _ _)
  | I x => exact .single (.I _)
  | jet x =>
    show WSteps (σ j ⬝ (c.encI x).toO.close σ) ((c.encO (c.spec x)).toO.close σ)
    rw [close_toO, close_toO]
    exact hj x
  | left x _ ih => exact WSteps.left _ ih
  | right f _ ih => exact WSteps.right _ ih

/-- **Closing to an implementation**: an extended reduction closes to a plain weak
    reduction, the jet head closed to any implementation of the
    contract. -/
theorem JSteps.close {α β : Type} {c : Contract α β} {j : Nat} (σ : Nat → Term)
    (hj : Implements c (σ j)) {t u : OTerm} (h : JSteps c j t u) :
    WSteps (t.close σ) (u.close σ) := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact (h.close σ hj).trans ih

/-- **A verifier that accepts under the jet realizes its atom** with any
    implementation in the jet's place: the open verifier `V`, applied to
    the closed statement `x` and realizer `r`, reduces to `K` under the
    jet. -/
theorem real_of_jet {α β : Type} {c : Contract α β} {j : Nat} (σ : Nat → Term)
    (hj : Implements c (σ j)) {V : OTerm} {x r : Term}
    (h : JSteps c j (V ⬝ₒ x.toO ⬝ₒ r.toO) .K) : Real (.atom (V.close σ) x) r := by
  have h' := h.close σ hj
  change WSteps (V.close σ ⬝ x.toO.close σ ⬝ r.toO.close σ) K at h'
  rw [close_toO, close_toO] at h'
  exact h'

/-- The specification is a function of the input encoding. -/
def Contract.Respects {α β : Type} (c : Contract α β) : Prop :=
  ∀ x y, c.encI x = c.encI y → c.spec x = c.spec y

/-- An injective input encoding respects any specification. -/
theorem respects_of_inj {α β : Type} {c : Contract α β}
    (h : ∀ x y, c.encI x = c.encI y → x = y) : c.Respects :=
  fun x y e => by rw [h x y e]

-- ---------------------------------------------------------------------------
-- Contracts in continuation-passing form
-- ---------------------------------------------------------------------------

/-- **A contract in continuation-passing form**: the jet takes a
    continuation `k`, then its inputs as separate arguments, encoded, and
    passes `k` its outputs, encoded:

      `J ⬝ k ⬝ a₁ ⬝ … ⬝ aₙ ⟶ k ⬝ b₁ ⬝ … ⬝ bₘ`

    with `[a₁, …, aₙ] = encI x` and `[b₁, …, bₘ] = encO (spec x)`.  A
    machine passes arguments by pointer, so separate arguments need no
    pairing; `k` keeps the jet's result an ordinary application; and with
    `k` first, a verifier can pass its witness's arguments straight on:
    `w (J k)` applies `J k` to whatever `w` supplies. -/
structure CContract (α β : Type) where
  encI : α → List Term
  encO : β → List Term
  spec : α → β

/-- Weak reduction with a continuation-passing data jet at the head
    variable `j`. -/
inductive CStep {α β : Type} (c : CContract α β) (j : Nat) : OTerm → OTerm → Prop
  | S (f g x : OTerm) : CStep c j (.S ⬝ₒ f ⬝ₒ g ⬝ₒ x) (f ⬝ₒ x ⬝ₒ (g ⬝ₒ x))
  | K (x y : OTerm) : CStep c j (.K ⬝ₒ x ⬝ₒ y) x
  | I (x : OTerm) : CStep c j (.I ⬝ₒ x) x
  | jet (x : α) (k : OTerm) :
      CStep c j (appL (.var j) (k :: (c.encI x).map Term.toO)) (appL k ((c.encO (c.spec x)).map Term.toO))
  | left {f f' : OTerm} (x : OTerm) (h : CStep c j f f') : CStep c j (f ⬝ₒ x) (f' ⬝ₒ x)
  | right (f : OTerm) {x x' : OTerm} (h : CStep c j x x') : CStep c j (f ⬝ₒ x) (f ⬝ₒ x')

inductive CSteps {α β : Type} (c : CContract α β) (j : Nat) : OTerm → OTerm → Prop
  | refl (t : OTerm) : CSteps c j t t
  | step {t t' u : OTerm} (h : CStep c j t t') (hs : CSteps c j t' u) : CSteps c j t u

/-- `P` implements the contract: for every input and every continuation. -/
def CImplements {α β : Type} (c : CContract α β) (P : Term) : Prop :=
  ∀ x (k : Term), WSteps (appT P (k :: c.encI x)) (appT k (c.encO (c.spec x)))

theorem map_close_toO (σ : Nat → Term) (ts : List Term) : (ts.map Term.toO).map (OTerm.close σ) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => show _ :: _ = _ :: _; rw [close_toO, ih]

theorem CStep.close {α β : Type} {c : CContract α β} {j : Nat} (σ : Nat → Term)
    (hj : CImplements c (σ j)) {t u : OTerm} (h : CStep c j t u) :
    WSteps (t.close σ) (u.close σ) := by
  induction h with
  | S f g x => exact .single (.S _ _ _)
  | K x y => exact .single (.K _ _)
  | I x => exact .single (.I _)
  | jet x k =>
    rw [_root_.close_appL, _root_.close_appL, List.map_cons, map_close_toO, map_close_toO]
    exact hj x (k.close σ)
  | left x _ ih => exact WSteps.left _ ih
  | right f _ ih => exact WSteps.right _ ih

/-- **Closing to an implementation**, for a continuation-passing jet. -/
theorem CSteps.close {α β : Type} {c : CContract α β} {j : Nat} (σ : Nat → Term)
    (hj : CImplements c (σ j)) {t u : OTerm} (h : CSteps c j t u) :
    WSteps (t.close σ) (u.close σ) := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact (h.close σ hj).trans ih

/-- A verifier that accepts under the continuation-passing jet realizes
    its atom with any implementation in the jet's place. -/
theorem real_of_cjet {α β : Type} {c : CContract α β} {j : Nat} (σ : Nat → Term)
    (hj : CImplements c (σ j)) {V : OTerm} {x r : Term}
    (h : CSteps c j (V ⬝ₒ x.toO ⬝ₒ r.toO) .K) : Real (.atom (V.close σ) x) r := by
  have h' := h.close σ hj
  change WSteps (V.close σ ⬝ x.toO.close σ ⬝ r.toO.close σ) K at h'
  rw [close_toO, close_toO] at h'
  exact h'

-- ---------------------------------------------------------------------------
-- A contract with an implementation
-- ---------------------------------------------------------------------------

/-- Negation of Scott Booleans, as a data jet. -/
def notC : Contract Bool Bool := ⟨boolT, boolT, not⟩

/-- `[b] b false true`. -/
def notP : Term := pairT (boolT false) (boolT true)

/-- `notP` implements `notC`, so the hypothesis of `JSteps.close` can
    hold. -/
theorem notP_implements : Implements notC notP := by
  intro x
  cases x with
  | true => exact (pairT_app _ _ _).trans (.single (.K _ _))
  | false =>
    exact (pairT_app _ _ _).trans ((WSteps.left _ (.single (.K _ _))).trans (.single (.I _)))

-- ---------------------------------------------------------------------------
-- Poseidon2 as a data jet
-- ---------------------------------------------------------------------------

/-- A canonical BabyBear element. -/
abbrev F := Fin Poseidon2.p

/-- The low `k` bits of `n`, least significant first, as a list of
    Scott-paired Booleans ending in `K`. -/
def bitsT : Nat → Nat → Term
  | 0, _ => K
  | k + 1, n => pairT (boolT (n % 2 == 1)) (bitsT k (n / 2))

/-- An output element in 31 bits. -/
def feltN (n : Nat) : Term := bitsT 31 n

/-- A canonical element in 31 bits (`p < 2^31`). -/
def feltT (x : F) : Term := bitsT 31 x.val

/-- An input state, the elements paired in order, ending in `K`. -/
def stateT : List F → Term
  | [] => K
  | x :: s => pairT (feltT x) (stateT s)

/-- An output state. -/
def stateN : List Nat → Term
  | [] => K
  | x :: s => pairT (feltN x) (stateN s)

theorem boolT_inj : ∀ {a b : Bool}, boolT a = boolT b → a = b
  | true, true, _ => rfl
  | false, false, _ => rfl
  | true, false, h => nomatch h
  | false, true, h => nomatch h

theorem pairT_inj {a b a' b' : Term} (h : pairT a b = pairT a' b') : a = a' ∧ b = b' := by
  cases h
  exact ⟨rfl, rfl⟩

theorem bitsT_inj : ∀ (k a b : Nat), a < 2 ^ k → b < 2 ^ k → bitsT k a = bitsT k b → a = b
  | 0, a, b, ha, hb, _ => (Nat.lt_one_iff.1 ha).trans (Nat.lt_one_iff.1 hb).symm
  | k + 1, a, b, ha, hb, h => by
    obtain ⟨hbit, hr⟩ := pairT_inj h
    have hbit := boolT_inj hbit
    have half : ∀ n, n < 2 ^ (k + 1) → n / 2 < 2 ^ k := fun n hn =>
      (Nat.div_lt_iff_lt_mul (by decide)).2 (by rw [← Nat.pow_succ]; exact hn)
    have hq := bitsT_inj k (a / 2) (b / 2) (half a ha) (half b hb) hr
    have hm : a % 2 = b % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> rw [h1, h2] at hbit <;> rw [h1, h2] <;>
        first | rfl | exact absurd hbit (by decide)
    calc a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
      _ = 2 * (b / 2) + b % 2 := by rw [hq, hm]
      _ = b := Nat.div_add_mod b 2

theorem feltT_inj {x y : F} (h : feltT x = feltT y) : x = y :=
  Fin.ext (bitsT_inj 31 _ _ (Nat.lt_trans x.isLt (by decide)) (Nat.lt_trans y.isLt (by decide)) h)

/-- **The input encoding is injective.** -/
theorem stateT_inj : ∀ x y : List F, stateT x = stateT y → x = y
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: x, b :: y, h => by
    obtain ⟨h1, h2⟩ := pairT_inj h
    rw [feltT_inj h1, stateT_inj x y h2]

/-- A state: sixteen canonical elements. -/
def St : Type := {x : List F // x.length = 16}

/-- **The Poseidon2 data jet**: Plonky3's width-16 permutation, from
    states of canonical elements to their images. -/
def poseidon2 : Contract St (List Nat) :=
  ⟨fun x => stateT x.1, stateN, fun x => Poseidon2.permute (x.1.map Fin.val)⟩

theorem poseidon2_encI (x : St) : poseidon2.encI x = stateT x.1 := rfl
theorem poseidon2_encO : poseidon2.encO = stateN := rfl
theorem poseidon2_spec (x : St) : poseidon2.spec x = Poseidon2.permute (x.1.map Fin.val) := by
  dsimp only [poseidon2]

/-- **The Poseidon2 contract respects its encoding.** -/
theorem poseidon2_respects : poseidon2.Respects :=
  respects_of_inj fun x y h => Subtype.ext (stateT_inj x.1 y.1 h)

-- ---------------------------------------------------------------------------
-- A hidden hand-off
-- ---------------------------------------------------------------------------

/-- **The commitment**: Plonky3's compression `TruncatedPermutation`, the
    permutation of the value and the randomness, truncated to eight. -/
def commit (o r : List F) : List Nat := (Poseidon2.permute ((o ++ r).map Fin.val)).take 8

/-- An opening: a value and randomness of eight elements each, the
    compression's input. -/
def Opening (a : List F × List F) : Prop := a.1.length = 8 ∧ a.2.length = 8

/-- Two openings with different values and one commitment: two distinct
    inputs on which the compression agrees. -/
def Collision (a b : List F × List F) : Prop :=
  Opening a ∧ Opening b ∧ a.1 ≠ b.1 ∧ commit a.1 a.2 = commit b.1 b.2

/-- A stage's relation over a committed hand-off: the witness opens the
    statement's commitment `h t`, and the stage's relation `Q` holds at the
    opened value. -/
def HRel {T W : Type} (h : T → List Nat) (Q : T → List F → W → Prop)
    (t : T) (w : (List F × List F) × W) : Prop :=
  Opening w.1 ∧ commit w.1.1 w.1.2 = h t ∧ Q t w.1.1 w.2

/-- **The hidden hand-off chain.**  Two stages carry the same commitment
    (`h₂ (link t) = h₁ t`).  From a verified proof of each, the extractors
    give one value that opens the commitment and at which both stages'
    relations hold, or a collision of the compression. -/
theorem hidden_chain {T₁ T₂ W₁ W₂ : Type} {h₁ : T₁ → List Nat} {h₂ : T₂ → List Nat}
    {Q₁ : T₁ → List F → W₁ → Prop} {Q₂ : T₂ → List F → W₂ → Prop}
    (ps₁ : Chain.PS T₁ _ (HRel h₁ Q₁)) (ps₂ : Chain.PS T₂ _ (HRel h₂ Q₂))
    (link : T₁ → T₂) (hl : ∀ t, h₂ (link t) = h₁ t) (t : T₁)
    (π₁ : ps₁.Proof) (π₂ : ps₂.Proof) (v₁ : ps₁.verify t π₁) (v₂ : ps₂.verify (link t) π₂) :
    (∃ o r, Opening (o, r) ∧ commit o r = h₁ t ∧
      Q₁ t o (ps₁.ext t π₁).2 ∧ Q₂ (link t) o (ps₂.ext (link t) π₂).2) ∨
      Collision (ps₁.ext t π₁).1 (ps₂.ext (link t) π₂).1 := by
  obtain ⟨⟨o₁, c₁, q₁⟩, ⟨o₂, c₂, q₂⟩⟩ := Chain.chain2_knowledge ps₁ ps₂ link t π₁ π₂ v₁ v₂
  match decEq (ps₁.ext t π₁).1.1 (ps₂.ext (link t) π₂).1.1 with
  | isTrue e =>
    refine .inl ⟨_, _, o₁, c₁, q₁, ?_⟩
    rw [e]
    exact q₂
  | isFalse e => exact .inr ⟨o₁, o₂, e, c₁.trans ((hl t).symm.trans c₂.symm)⟩

end DataJet
