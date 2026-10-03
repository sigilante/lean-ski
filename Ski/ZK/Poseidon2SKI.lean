import Ski.BitArith
import Ski.DataJet
import Ski.ZK.Poseidon2Ex
import Ski.DataJet

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Term

/-!
# Poseidon2 in SKI

`P`, an SKI term, computes the Poseidon2 permutation by weak reduction on
every state of sixteen canonical BabyBear elements
(`P_spec`, `poseidon2_implements`):
`P ⬝ stateT x ↠ stateN (permute (x.map Fin.val))`.
So the Poseidon2 data jet of `Ski/DataJet.lean` has an implementation,
and the jet's translation to SKI (`DataJet.JSteps.close`) applies to it.

**The construction.**  The state enters as sixteen 31-bit elements, which
`inS` turns into numbers (`Ski/BitArith.lean`).  A layer is sixteen
arithmetic expressions over the sixteen inputs (`Ex`), compiled to terms
over `BitArith`'s operations (`Ex.comp`), the inputs read by projection
from the paired state (`layerT`).  A full round is three layers (the
S-boxes, `M₄` on each block, the column mixing) and a partial round two
(the S-box on the first entry, the internal layer), so that the S-box
and `M₄` results are components of the state, computed once by a reducer
that shares.  Within a layer an expression is a tree: the internal
layer's sum is computed for each of its sixteen outputs, and each column
sum for each of its four.  The rounds run in the
specification's order (`rounds`), and `outS` turns the numbers back into
31-bit elements.  Each layer's result stays unevaluated until the next
reads it.

**The proof.**
- An expression's term reduces to its value whenever the inputs it reads
  do (`Ex.comp_spec`), so a layer maps states of values to states of its
  expressions' values (`layer_ok`).
- The specification's rounds are compositions of the sublayers by
  definition (`extRound_split`, `intRound_split`), and each sublayer, on
  sixteen inputs, equals its expressions' value (`bridge_sbox`,
  `bridge_mat4`, `bridge_mix`, `bridge_sbox0`, `bridge_intLin`).  The
  expressions mirror the specification's definitions (`mat4E`,
  `colSumE`, `intLinearE`); the bridges are checked by the kernel on
  symbolic inputs, after fixing the lists' lengths to literals.
- Layers compose (`comp_ok`).
- A chain of layers computes the fold of their rounds (`chain_ok`), and
  the rounds fold to `permute` (`rounds_fold`).

**What it costs** (`bench/P2Run.lean`).  `P` has 12,370,891 nodes as a
tree, and `P` applied to a state 12,929 distinct subterms.  Avon's graph
reduction (`share` mode, at `188f7f2`) takes each of Plonky3's three test
vectors to the normal form `P_spec` names, byte for byte, in 962 to 981
million contractions, about 10.4 s and 66 MB.  A reducer that shares no
work recomputes every input each time a later layer reads it: Avon's
`copy` mode passes 8 × 10⁹ contractions on vector 1 without finishing.
-/

namespace Poseidon2SKI

open Compose BitArith Poseidon2

-- ---------------------------------------------------------------------------
-- Expressions compiled to SKI
-- ---------------------------------------------------------------------------

/-- `p` in 31 bits. -/
def pBits : List Bool := bitsOf 31 Poseidon2.p

theorem val_pBits : val pBits = Poseidon2.p := by
  rw [pBits, val_bitsOf]; decide

theorem pBits_pos : 0 < val pBits := by rw [val_pBits]; decide

def mdT : Term := modT pBits
def sboxT : Term := pow7T pBits

/-- Every input an expression reads is below `n`. -/
def Ex.varsLt (n : Nat) : Ex → Bool
  | .var i => decide (i < n)
  | .lit _ => true
  | .add a b => a.varsLt n && b.varsLt n
  | .mul a b => a.varsLt n && b.varsLt n
  | .md a => a.varsLt n
  | .sbox a => a.varsLt n

/-- The term computing an expression, input `i` read by `f i`. -/
def Ex.comp (f : Nat → OTerm) : Ex → OTerm
  | .var i => f i
  | .lit n => (litT n).toO
  | .add a b => addT.toO ⬝ₒ (boolT false).toO ⬝ₒ a.comp f ⬝ₒ b.comp f
  | .mul a b => mulT.toO ⬝ₒ a.comp f ⬝ₒ b.comp f
  | .md a => mdT.toO ⬝ₒ a.comp f
  | .sbox a => sboxT.toO ⬝ₒ a.comp f

/-- **An expression's term computes its value**, when every input it reads
    does. -/
theorem Ex.comp_spec (f : Nat → OTerm) (σ : Nat → Term) (ρ : Nat → Nat) (n : Nat)
    (hf : ∀ i, i < n → RepR ((f i).close σ) (ρ i)) :
    ∀ e : Ex, e.varsLt n = true → RepR ((e.comp f).close σ) (e.eval ρ)
  | .var i, h => hf i (of_decide_eq_true h)
  | .lit k, _ => by
    show RepR ((litT k).toO.close σ) k
    rw [close_toO]; exact RepR.lit k
  | .add a b, h => by
    show RepR (addT.toO.close σ ⬝ (boolT false).toO.close σ ⬝ (a.comp f).close σ ⬝ (b.comp f).close σ) _
    rw [close_toO, close_toO]
    exact RepR.add (Ex.comp_spec f σ ρ n hf a (band_l h)) (Ex.comp_spec f σ ρ n hf b (band_r h))
  | .mul a b, h => by
    show RepR (mulT.toO.close σ ⬝ (a.comp f).close σ ⬝ (b.comp f).close σ) _
    rw [close_toO]
    exact RepR.mul (Ex.comp_spec f σ ρ n hf a (band_l h)) (Ex.comp_spec f σ ρ n hf b (band_r h))
  | .md a, h => by
    show RepR (mdT.toO.close σ ⬝ (a.comp f).close σ) (a.eval ρ % Poseidon2.p)
    rw [close_toO, ← val_pBits]
    exact RepR.mod pBits_pos (Ex.comp_spec f σ ρ n hf a h)
  | .sbox a, h => by
    show RepR (sboxT.toO.close σ ⬝ (a.comp f).close σ) (a.eval ρ ^ 7 % Poseidon2.p)
    rw [close_toO, ← val_pBits]
    exact RepR.pow7 pBits_pos (Ex.comp_spec f σ ρ n hf a h)

-- ---------------------------------------------------------------------------
-- States: sixteen values, paired
-- ---------------------------------------------------------------------------

def packT : List Term → Term
  | [] => K
  | t :: ts => pairT t (packT ts)

def packO : List OTerm → OTerm
  | [] => .K
  | t :: ts => pairO t (packO ts)

theorem close_packO (σ : Nat → Term) : ∀ os : List OTerm, (packO os).close σ = packT (os.map (·.close σ))
  | [] => rfl
  | o :: os => by
    show pairT (o.close σ) ((packO os).close σ) = pairT (o.close σ) (packT (os.map (·.close σ)))
    rw [close_packO σ os]

/-- The `i`-th component: `i` second projections, then the first. -/
def projO : Nat → OTerm → OTerm
  | 0, s => s ⬝ₒ ttO
  | i + 1, s => projO i (s ⬝ₒ ffO)

def projT : Nat → Term → Term
  | 0, s => s ⬝ K
  | i + 1, s => projT i (s ⬝ (K ⬝ I))

theorem close_projO (σ : Nat → Term) : ∀ (i : Nat) (s : OTerm), (projO i s).close σ = projT i (s.close σ)
  | 0, _ => rfl
  | i + 1, s => close_projO σ i (s ⬝ₒ ffO)

theorem projT_congr : ∀ (i : Nat) {s s' : Term}, WSteps s s' → WSteps (projT i s) (projT i s')
  | 0, _, _, h => WSteps.left _ h
  | i + 1, _, _, h => projT_congr i (WSteps.left _ h)

theorem proj_pack : ∀ (i : Nat) (ts : List Term), i < ts.length → WSteps (projT i (packT ts)) (ts.getD i K)
  | 0, t :: ts, _ => (pairT_app t (packT ts) K).trans (.single (.K _ _))
  | i + 1, t :: ts, h =>
    (projT_congr i ((pairT_app t (packT ts) (K ⬝ I)).trans
      ((WSteps.left _ (.single (.K _ _))).trans (.single (.I _))))).trans
      (proj_pack i ts (Nat.lt_of_succ_lt_succ h))
  | _, [], h => absurd h (Nat.not_lt_zero _)

/-- Components that compute values, pointwise. -/
inductive StR : List Term → List Nat → Prop
  | nil : StR [] []
  | cons {t : Term} {v : Nat} {ts : List Term} {vs : List Nat} : RepR t v → StR ts vs → StR (t :: ts) (v :: vs)

theorem StR.length : ∀ {ts : List Term} {vs : List Nat}, StR ts vs → ts.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => congrArg (· + 1) h.length

theorem StR.get : ∀ {ts : List Term} {vs : List Nat}, StR ts vs →
    ∀ i, i < ts.length → RepR (ts.getD i K) (vs.getD i 0)
  | _, _, .cons h _, 0, _ => h
  | _, _, .cons _ h, i + 1, hi => h.get i (Nat.lt_of_succ_lt_succ hi)
  | _, _, .nil, _, hi => absurd hi (Nat.not_lt_zero _)

-- ---------------------------------------------------------------------------
-- Layers
-- ---------------------------------------------------------------------------

/-- The input-reading of a layer: component `i` of the state in variable 0. -/
def rd : Nat → OTerm := fun i => projO i (.var 0)

/-- A layer: the state in, each expression's value out. -/
def layerT (es : List Ex) : Term := lam [0] (packO (es.map (Ex.comp rd)))

/-- `L` maps states of sixteen values `vs` to states of the values `f vs`. -/
def LayerOK (L : Term) (f : List Nat → List Nat) : Prop :=
  ∀ ts vs, StR ts vs → vs.length = 16 →
    ∃ ts', WSteps (L ⬝ packT ts) (packT ts') ∧ StR ts' (f vs) ∧ (f vs).length = 16

theorem StR_map (σ : Nat → Term) (ρ : Nat → Nat) (n : Nat)
    (hf : ∀ i, i < n → RepR ((rd i).close σ) (ρ i)) :
    ∀ es : List Ex, es.all (·.varsLt n) = true →
      StR ((es.map (Ex.comp rd)).map (·.close σ)) (es.map (Ex.eval ρ))
  | [], _ => .nil
  | e :: es, h => .cons (Ex.comp_spec rd σ ρ n hf e (band_l h)) (StR_map σ ρ n hf es (band_r h))

/-- **A layer computes its expressions.** -/
theorem layer_ok (es : List Ex) (f : List Nat → List Nat) (hv : es.all (·.varsLt 16) = true)
    (hl : es.length = 16) (hb : ∀ vs, vs.length = 16 → es.map (Ex.eval (at16 vs)) = f vs) :
    LayerOK (layerT es) f := by
  intro ts vs h hvs
  have σd : (rd 0).close (overrideC (fun _ => I) [0] [packT ts]) = projT 0 (packT ts) := rfl
  refine ⟨(es.map (Ex.comp rd)).map (·.close (overrideC (fun _ => I) [0] [packT ts])), ?_, ?_, ?_⟩
  · have := lam_beta [0] (packO (es.map (Ex.comp rd))) [packT ts] rfl
    rw [close_packO] at this
    exact this
  · rw [← hb vs hvs]
    refine StR_map _ _ 16 (fun i hi => ?_) es hv
    rw [show (rd i).close (overrideC (fun _ => I) [0] [packT ts]) = projT i (packT ts) from close_projO _ i _]
    show RepR (projT i (packT ts)) (vs.getD i 0)
    have hlen := h.length
    exact RepR.back (proj_pack i ts (by rw [hlen, hvs]; exact hi)) (h.get i (by rw [hlen, hvs]; exact hi))
  · rw [← hb vs hvs, List.length_map, hl]

-- ---------------------------------------------------------------------------
-- The rounds
-- ---------------------------------------------------------------------------

/-- Two layers in turn. -/
def compT (A B : Term) : Term := lam [0] (B.toO ⬝ₒ (A.toO ⬝ₒ .var 0))

theorem comp_ok {A B : Term} {f g : List Nat → List Nat} (ha : LayerOK A f) (hb : LayerOK B g) :
    LayerOK (compT A B) (fun s => g (f s)) := by
  intro ts vs h hl
  obtain ⟨ts₁, h₁, s₁, l₁⟩ := ha ts vs h hl
  obtain ⟨ts₂, h₂, s₂, l₂⟩ := hb ts₁ (f vs) s₁ l₁
  refine ⟨ts₂, ?_, s₂, l₂⟩
  have hb' := lam_beta [0] (B.toO ⬝ₒ (A.toO ⬝ₒ .var 0)) [packT ts] rfl
  simp only [OTerm.close, close_toO] at hb'
  exact hb'.trans ((WSteps.right B h₁).trans h₂)

theorem LayerOK.congr {L : Term} {f g : List Nat → List Nat} (h : LayerOK L f)
    (e : ∀ vs, vs.length = 16 → f vs = g vs) : LayerOK L g := by
  intro ts vs hs hl
  rw [← e vs hl]
  exact h ts vs hs hl

theorem sbox_ok (rc : List Nat) (hc : rc.length = 16) : LayerOK (layerT (sboxLE rc)) (sboxL rc) :=
  len16 (P := fun rc => LayerOK (layerT (sboxLE rc)) (sboxL rc))
    (fun c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 => layer_ok _ _ rfl rfl (fun vs hv => bridge_sbox vs [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] hv rfl)) rc hc

theorem mat4_ok : LayerOK (layerT mat4LE) mat4L := layer_ok _ _ rfl rfl bridge_mat4
theorem mix_ok : LayerOK (layerT mixLE) mixL := layer_ok _ _ rfl rfl bridge_mix
theorem sbox0_ok (c : Nat) : LayerOK (layerT (sbox0LE c)) (sbox0L c) := layer_ok _ _ rfl rfl (bridge_sbox0 · c)
theorem intLin_ok : LayerOK (layerT intLinLE) intLinear := layer_ok _ _ rfl rfl bridge_intLin

def L0 : Term := compT (layerT mat4LE) (layerT mixLE)
def extL (rc : List Nat) : Term := compT (compT (layerT (sboxLE rc)) (layerT mat4LE)) (layerT mixLE)
def intL (c : Nat) : Term := compT (layerT (sbox0LE c)) (layerT intLinLE)

theorem L0_ok : LayerOK L0 extLinear :=
  (comp_ok mat4_ok mix_ok).congr fun vs _ => (extLinear_split vs).symm

theorem extL_ok (rc : List Nat) (hc : rc.length = 16) : LayerOK (extL rc) (fun s => extRound s rc) :=
  (comp_ok (comp_ok (sbox_ok rc hc) mat4_ok) mix_ok).congr fun vs _ => (extRound_split vs rc).symm

theorem intL_ok (c : Nat) : LayerOK (intL c) (fun s => intRound s c) :=
  (comp_ok (sbox0_ok c) intLin_ok).congr fun vs _ => (intRound_split vs c).symm

-- ---------------------------------------------------------------------------
-- Field elements in, field elements out: fixed width to numbers and back
-- ---------------------------------------------------------------------------

theorem pairT_congr {a a' b b' : Term} (ha : WSteps a a') (hb : WSteps b b') :
    WSteps (pairT a b) (pairT a' b') :=
  WSteps.app (WSteps.right S (WSteps.right (S ⬝ I) (WSteps.right K ha))) (WSteps.right K hb)

theorem close_pairO (σ : Nat → Term) (a b : OTerm) : (pairO a b).close σ = pairT (a.close σ) (b.close σ) := rfl

section
local notation "v" n => OTerm.var n

/-- One bit of a fixed-width element to one digit of a number. -/
def inStep : Term := lam [0, 1] ((v 1) ⬝ₒ absN [2, 3] (consO (v 2) ((v 0) ⬝ₒ (v 3))))

/-- One digit of a number to one bit of a fixed-width element, a missing
    digit read as 0. -/
def outStep : Term := lam [0, 1] ((v 1) ⬝ₒ pairO ffO ((v 0) ⬝ₒ .K) ⬝ₒ absN [2, 3] (pairO (v 2) ((v 0) ⬝ₒ (v 3))))
end

def inK : Nat → Term
  | 0 => K ⬝ K
  | k + 1 => inStep ⬝ inK k

def outK : Nat → Term
  | 0 => K ⬝ K
  | k + 1 => outStep ⬝ outK k

theorem in_step : wnf 100 (inStep.toO ⬝ₒ .var 10 ⬝ₒ pairO (.var 11) (.var 12)) =
    consO (.var 11) (.var 10 ⬝ₒ .var 12) := by decide

theorem out_n : wnf 100 (outStep.toO ⬝ₒ .var 10 ⬝ₒ .K) = pairO ffO (.var 10 ⬝ₒ .K) := by decide

theorem out_c : wnf 100 (outStep.toO ⬝ₒ .var 10 ⬝ₒ consO (.var 11) (.var 12)) =
    pairO (.var 11) (.var 10 ⬝ₒ .var 12) := by decide

theorem inK_spec : ∀ (k n : Nat), WSteps (inK k ⬝ DataJet.bitsT k n) (bl (bitsOf k n))
  | 0, _ => .single (.K _ _)
  | k + 1, n => by
    have h := run in_step (envL [inK k, boolT (n % 2 == 1), DataJet.bitsT k (n / 2)])
    simp only [OTerm.close, close_toO, close_consO, close_pairO] at h
    exact h.trans (consT_congr (.refl _) (inK_spec k (n / 2)))

theorem outK_spec : ∀ (k : Nat) (bs : List Bool), WSteps (outK k ⬝ bl bs) (DataJet.bitsT k (val bs))
  | 0, _ => .single (.K _ _)
  | k + 1, [] => by
    have h := run out_n (envL [outK k])
    simp only [OTerm.close, close_toO, close_pairO] at h
    exact h.trans (pairT_congr (.refl _) (outK_spec k []))
  | k + 1, b :: bs => by
    have h := run out_c (envL [outK k, boolT b, bl bs])
    simp only [OTerm.close, close_toO, close_pairO] at h
    have e1 : ((b.toNat + 2 * val bs) % 2 == 1) = b := by
      rw [Nat.add_mul_mod_self_left]; cases b <;> rfl
    have e2 : (b.toNat + 2 * val bs) / 2 = val bs := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
      cases b
      · show 0 / 2 + val bs = val bs; rw [Nat.zero_div, Nat.zero_add]
      · show 1 / 2 + val bs = val bs; rw [show 1 / 2 = 0 from rfl, Nat.zero_add]
    show WSteps _ (pairT (boolT ((b.toNat + 2 * val bs) % 2 == 1)) (DataJet.bitsT k ((b.toNat + 2 * val bs) / 2)))
    rw [e1, e2]
    exact h.trans (pairT_congr (.refl _) (outK_spec k bs))

/-- The state in: each element's 31 bits to a number. -/
def inS : Term := lam [0] (packO ((List.range 16).map fun i => (inK 31).toO ⬝ₒ rd i))

/-- The state out: each number to 31 bits. -/
def outS : Term := lam [0] (packO ((List.range 16).map fun i => (outK 31).toO ⬝ₒ rd i))

theorem stateT_pack : ∀ x : List DataJet.F, DataJet.stateT x = packT (x.map DataJet.feltT)
  | [] => rfl
  | a :: x => by
    show pairT (DataJet.feltT a) (DataJet.stateT x) = pairT (DataJet.feltT a) (packT (x.map DataJet.feltT))
    rw [stateT_pack x]

theorem stateN_pack : ∀ vs : List Nat, DataJet.stateN vs = packT (vs.map DataJet.feltN)
  | [] => rfl
  | a :: vs => by
    show pairT (DataJet.feltN a) (DataJet.stateN vs) = pairT (DataJet.feltN a) (packT (vs.map DataJet.feltN))
    rw [stateN_pack vs]

theorem in_rep : ∀ (x : List DataJet.F) (i : Nat), i < x.length →
    RepR (inK 31 ⬝ (x.map DataJet.feltT).getD i K) ((x.map Fin.val).getD i 0)
  | a :: _, 0, _ => by
    refine ⟨_, inK_spec 31 a.val, ?_⟩
    show val (bitsOf 31 a.val) = a.val
    rw [val_bitsOf, Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))]
  | _ :: x, i + 1, h => in_rep x i (Nat.lt_of_succ_lt_succ h)
  | [], _, h => absurd h (Nat.not_lt_zero _)

/-- States from index lists, pointwise. -/
theorem StR_idx (F : Nat → OTerm) (σ : Nat → Term) (vals : Nat → Nat)
    (h : ∀ i, i < 16 → RepR ((F i).close σ) (vals i)) :
    ∀ l : List Nat, l.all (fun i => decide (i < 16)) = true → StR ((l.map F).map (·.close σ)) (l.map vals)
  | [], _ => .nil
  | i :: l, hl => .cons (h i (of_decide_eq_true (band_l hl))) (StR_idx F σ vals h l (band_r hl))

theorem pack_idx (F : Nat → OTerm) (σ : Nat → Term) (H : Nat → Term)
    (h : ∀ i, i < 16 → WSteps ((F i).close σ) (H i)) :
    ∀ l : List Nat, l.all (fun i => decide (i < 16)) = true →
      WSteps (packT ((l.map F).map (·.close σ))) (packT (l.map H))
  | [], _ => .refl _
  | i :: l, hl => pairT_congr (h i (of_decide_eq_true (band_l hl))) (pack_idx F σ H h l (band_r hl))

theorem range16_all : (List.range 16).all (fun i => decide (i < 16)) = true := by decide

/-- **The state in.** -/
theorem inS_spec (x : List DataJet.F) (hx : x.length = 16) :
    ∃ ts, WSteps (inS ⬝ DataJet.stateT x) (packT ts) ∧ StR ts (x.map Fin.val) := by
  let σ := overrideC (fun _ => I) [0] [DataJet.stateT x]
  have hb := lam_beta [0] (packO ((List.range 16).map fun i => (inK 31).toO ⬝ₒ rd i)) [DataJet.stateT x] rfl
  rw [close_packO] at hb
  refine ⟨_, hb, ?_⟩
  have hv := range16_map 0 (x.map Fin.val) (by rw [List.length_map, hx])
  rw [← hv]
  refine StR_idx _ σ _ (fun i hi => ?_) _ range16_all
  show RepR ((inK 31).toO.close σ ⬝ (rd i).close σ) _
  rw [close_toO, show (rd i).close σ = projT i (DataJet.stateT x) from close_projO _ i _, stateT_pack]
  have hl : i < (x.map DataJet.feltT).length := by rw [List.length_map, hx]; exact hi
  exact RepR.back (WSteps.right _ (proj_pack i _ hl)) (in_rep x i (by rw [hx]; exact hi))

/-- **The state out.** -/
theorem outS_spec (ts : List Term) (vs : List Nat) (h : StR ts vs) (hv : vs.length = 16) :
    WSteps (outS ⬝ packT ts) (DataJet.stateN vs) := by
  let σ := overrideC (fun _ => I) [0] [packT ts]
  have hb := lam_beta [0] (packO ((List.range 16).map fun i => (outK 31).toO ⬝ₒ rd i)) [packT ts] rfl
  rw [close_packO] at hb
  refine hb.trans ((pack_idx _ σ (fun i => DataJet.feltN (vs.getD i 0)) (fun i hi => ?_) _ range16_all).trans ?_)
  · show WSteps ((outK 31).toO.close σ ⬝ (rd i).close σ) _
    rw [close_toO, show (rd i).close σ = projT i (packT ts) from close_projO _ i _]
    have hlen : i < ts.length := by rw [h.length, hv]; exact hi
    obtain ⟨bs, hbs, vb⟩ := h.get i hlen
    have := (WSteps.right (outK 31) ((proj_pack i ts hlen).trans hbs)).trans (outK_spec 31 bs)
    rw [vb] at this
    exact this
  · have e : (List.range 16).map (fun i => DataJet.feltN (vs.getD i 0)) = vs.map DataJet.feltN :=
      len16 (P := fun vs => (List.range 16).map (fun i => DataJet.feltN (vs.getD i 0)) = vs.map DataJet.feltN)
        (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) vs hv
    rw [e, stateN_pack]
    exact .refl _

-- ---------------------------------------------------------------------------
-- The chain of layers
-- ---------------------------------------------------------------------------

def chainT : List Term → Term → Term
  | [], x => x
  | L :: Ls, x => chainT Ls (L ⬝ x)

def chainO : List OTerm → OTerm → OTerm
  | [], x => x
  | L :: Ls, x => chainO Ls (L ⬝ₒ x)

theorem close_chainO (σ : Nat → Term) :
    ∀ (Ls : List Term) (x : OTerm), (chainO (Ls.map Term.toO) x).close σ = chainT Ls (x.close σ)
  | [], _ => rfl
  | L :: Ls, x => by
    show (chainO (Ls.map Term.toO) (L.toO ⬝ₒ x)).close σ = chainT Ls (L ⬝ x.close σ)
    rw [close_chainO σ Ls]
    show chainT Ls (L.toO.close σ ⬝ x.close σ) = _
    rw [close_toO]

theorem chainT_congr : ∀ (Ls : List Term) {x y : Term}, WSteps x y → WSteps (chainT Ls x) (chainT Ls y)
  | [], _, _, h => h
  | L :: Ls, _, _, h => chainT_congr Ls (WSteps.right L h)

/-- Every layer of the list computes its function. -/
def AllOK : List (Term × (List Nat → List Nat)) → Prop
  | [] => True
  | p :: ps => LayerOK p.1 p.2 ∧ AllOK ps

theorem allOK_append : ∀ (a b : List (Term × (List Nat → List Nat))), AllOK a → AllOK b → AllOK (a ++ b)
  | [], _, _, hb => hb
  | _ :: a, b, ⟨hp, ha⟩, hb => ⟨hp, allOK_append a b ha hb⟩

/-- **A chain of layers computes the composition of their functions.** -/
theorem chain_ok : ∀ (Lfs : List (Term × (List Nat → List Nat))), AllOK Lfs →
    ∀ ts vs, StR ts vs → vs.length = 16 →
      ∃ ts', WSteps (chainT (Lfs.map Prod.fst) (packT ts)) (packT ts') ∧
        StR ts' (Lfs.foldl (fun v p => p.2 v) vs) ∧ (Lfs.foldl (fun v p => p.2 v) vs).length = 16
  | [], _, ts, _, h, hl => ⟨ts, .refl _, h, hl⟩
  | p :: ps, ⟨hp, hps⟩, ts, vs, h, hl => by
    obtain ⟨ts₁, h₁, s₁, l₁⟩ := hp ts vs h hl
    obtain ⟨ts₂, h₂, s₂, l₂⟩ := chain_ok ps hps ts₁ (p.2 vs) s₁ l₁
    exact ⟨ts₂, (chainT_congr _ h₁).trans h₂, s₂, l₂⟩

/-- The layers of the permutation, in order. -/
def rounds : List (Term × (List Nat → List Nat)) :=
  ((L0, extLinear) :: rcInitial.map fun rc => (extL rc, fun s => extRound s rc)) ++
    (rcInternal.map fun c => (intL c, fun s => intRound s c)) ++
    (rcTerminal.map fun rc => (extL rc, fun s => extRound s rc))

theorem allOK_ext : ∀ l : List (List Nat), l.all (fun rc => decide (rc.length = 16)) = true →
    AllOK (l.map fun rc => (extL rc, fun s => extRound s rc))
  | [], _ => trivial
  | rc :: l, h => ⟨extL_ok rc (of_decide_eq_true (band_l h)), allOK_ext l (band_r h)⟩

theorem allOK_int : ∀ l : List Nat, AllOK (l.map fun c => (intL c, fun s => intRound s c))
  | [] => trivial
  | c :: l => ⟨intL_ok c, allOK_int l⟩

theorem rounds_ok : AllOK rounds :=
  allOK_append _ _ (allOK_append _ _ ⟨L0_ok, allOK_ext rcInitial (by decide)⟩ (allOK_int rcInternal))
    (allOK_ext rcTerminal (by decide))

theorem rounds_fold (s : List Nat) : rounds.foldl (fun v p => p.2 v) s = permute s := by
  simp only [rounds, List.foldl_append, List.foldl_cons, List.foldl_map]
  rfl

-- ---------------------------------------------------------------------------
-- The permutation
-- ---------------------------------------------------------------------------

/-- **Poseidon2 in SKI**: the state in, the rounds, the state out. -/
def P : Term :=
  lam [0] (outS.toO ⬝ₒ chainO ((rounds.map Prod.fst).map Term.toO) (inS.toO ⬝ₒ .var 0))

/-- **`P` computes the permutation** on every state of sixteen canonical
    elements, by weak reduction. -/
theorem P_spec (x : List DataJet.F) (hx : x.length = 16) :
    WSteps (P ⬝ DataJet.stateT x) (DataJet.stateN (permute (x.map Fin.val))) := by
  have hb := lam_beta [0] (outS.toO ⬝ₒ chainO ((rounds.map Prod.fst).map Term.toO) (inS.toO ⬝ₒ .var 0))
    [DataJet.stateT x] rfl
  rw [show (outS.toO ⬝ₒ chainO ((rounds.map Prod.fst).map Term.toO) (inS.toO ⬝ₒ .var 0)).close
      (overrideC (fun _ => I) [0] [DataJet.stateT x]) =
      outS ⬝ chainT (rounds.map Prod.fst) (inS ⬝ DataJet.stateT x) by
    show outS.toO.close _ ⬝ (chainO _ _).close _ = _
    rw [close_toO, close_chainO]
    show outS ⬝ chainT _ (inS.toO.close _ ⬝ DataJet.stateT x) = _
    rw [close_toO]] at hb
  obtain ⟨ts₀, h₀, s₀⟩ := inS_spec x hx
  obtain ⟨ts₁, h₁, s₁, l₁⟩ := chain_ok rounds rounds_ok ts₀ (x.map Fin.val) s₀ (by rw [List.length_map, hx])
  rw [rounds_fold] at s₁ l₁
  exact hb.trans ((WSteps.right outS ((chainT_congr _ h₀).trans h₁)).trans (outS_spec ts₁ _ s₁ l₁))

/-- **`P` implements the Poseidon2 data jet.** -/
theorem poseidon2_implements : DataJet.Implements DataJet.poseidon2 P := by
  intro x
  rw [DataJet.poseidon2_encI, DataJet.poseidon2_encO, DataJet.poseidon2_spec]
  exact P_spec x.1 x.2


-- ---------------------------------------------------------------------------
-- The continuation-passing form
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Any 31-bit inputs
-- ---------------------------------------------------------------------------

theorem in_repN : ∀ (vs : List Nat) (i : Nat), i < vs.length → vs.getD i 0 < 2 ^ 31 →
    RepR (inK 31 ⬝ (vs.map DataJet.feltN).getD i K) (vs.getD i 0)
  | v :: _, 0, _, hb => ⟨_, inK_spec 31 v, by
      show val (bitsOf 31 v) = v; rw [val_bitsOf, Nat.mod_eq_of_lt (show v < 2 ^ 31 from hb)]⟩
  | _ :: vs, i + 1, h, hb => in_repN vs i (Nat.lt_of_succ_lt_succ h) hb
  | [], _, h, _ => absurd h (Nat.not_lt_zero _)

theorem inS_specN (vs : List Nat) (hv : vs.length = 16) (hb : ∀ i, i < 16 → vs.getD i 0 < 2 ^ 31) :
    ∃ ts, WSteps (inS ⬝ DataJet.stateN vs) (packT ts) ∧ StR ts vs := by
  let σ := overrideC (fun _ => I) [0] [DataJet.stateN vs]
  have hb' := lam_beta [0] (packO ((List.range 16).map fun i => (inK 31).toO ⬝ₒ rd i)) [DataJet.stateN vs] rfl
  rw [close_packO] at hb'
  refine ⟨_, hb', ?_⟩
  have hr := range16_map 0 vs hv
  have := StR_idx (fun i => (inK 31).toO ⬝ₒ rd i) σ (fun i => vs.getD i 0) (fun i hi => by
    show RepR ((inK 31).toO.close σ ⬝ (rd i).close σ) _
    rw [close_toO, show (rd i).close σ = projT i (DataJet.stateN vs) from close_projO _ i _, stateN_pack]
    have hl : i < (vs.map DataJet.feltN).length := by rw [List.length_map, hv]; exact hi
    exact RepR.back (WSteps.right _ (proj_pack i _ hl)) (in_repN vs i (by rw [hv]; exact hi) (hb i hi)))
    _ range16_all
  rw [hr] at this
  exact this

/-- **`P` computes the permutation on any sixteen 31-bit values**, canonical
    or not. -/
theorem P_specN (vs : List Nat) (hv : vs.length = 16) (hb : ∀ i, i < 16 → vs.getD i 0 < 2 ^ 31) :
    WSteps (P ⬝ DataJet.stateN vs) (DataJet.stateN (permute vs)) := by
  have h := lam_beta [0] (outS.toO ⬝ₒ chainO ((rounds.map Prod.fst).map Term.toO) (inS.toO ⬝ₒ .var 0))
    [DataJet.stateN vs] rfl
  rw [show (outS.toO ⬝ₒ chainO ((rounds.map Prod.fst).map Term.toO) (inS.toO ⬝ₒ .var 0)).close
      (overrideC (fun _ => I) [0] [DataJet.stateN vs]) =
      outS ⬝ chainT (rounds.map Prod.fst) (inS ⬝ DataJet.stateN vs) by
    show outS.toO.close _ ⬝ (chainO _ _).close _ = _
    rw [close_toO, close_chainO]
    show outS ⬝ chainT _ (inS.toO.close _ ⬝ DataJet.stateN vs) = _
    rw [close_toO]] at h
  obtain ⟨ts₀, h₀, s₀⟩ := inS_specN vs hv hb
  obtain ⟨ts₁, h₁, s₁, l₁⟩ := chain_ok rounds rounds_ok ts₀ vs s₀ hv
  rw [rounds_fold] at s₁ l₁
  exact h.trans ((WSteps.right outS ((chainT_congr _ h₀).trans h₁)).trans (outS_spec ts₁ _ s₁ l₁))

-- ---------------------------------------------------------------------------
-- The jet on bits
-- ---------------------------------------------------------------------------

/-- The `i`-th 31 bits of `bs`, least significant first. -/
def chunk (bs : List Bool) (i : Nat) : List Bool := (List.range 31).map fun j => bs.getD (31 * i + j) false

/-- Sixteen 31-bit values from 496 bits. -/
def valsB (bs : List Bool) : List Nat := (List.range 16).map fun i => val (chunk bs i)

def Bits : Type := {bs : List Bool // bs.length = 496}

/-- **The Poseidon2 jet on bits**, in continuation-passing form: a
    continuation, then the sixteen inputs' 496 bits, each a Scott Boolean;
    the continuation receives the sixteen outputs' 496 bits.  The inputs are
    any 31-bit values; the permutation of a value is the permutation of its
    residue. -/
def poseidon2B : DataJet.CContract Bits (List Nat) :=
  ⟨fun bs => bs.1.map boolT, fun ys => (ys.flatMap (bitsOf 31)).map boolT, fun bs => permute (valsB bs.1)⟩

theorem poseidon2B_encI (bs : Bits) : poseidon2B.encI bs = bs.1.map boolT := rfl
theorem poseidon2B_encO : poseidon2B.encO = fun ys => (ys.flatMap (bitsOf 31)).map boolT := rfl
theorem poseidon2B_spec (bs : Bits) : poseidon2B.spec bs = permute (valsB bs.1) := by
  dsimp only [poseidon2B]

theorem boolT_inj' {a b : Bool} (h : boolT a = boolT b) : a = b := DataJet.boolT_inj h

theorem map_boolT_inj : ∀ {a b : List Bool}, a.map boolT = b.map boolT → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    obtain ⟨h1, h2⟩ := List.cons.inj h
    rw [boolT_inj' h1, map_boolT_inj h2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- **The bit contract respects its encoding.** -/
theorem poseidon2B_respects : ∀ x y : Bits, poseidon2B.encI x = poseidon2B.encI y → x = y :=
  fun x y h => Subtype.ext (map_boolT_inj h)

theorem val_lt : ∀ l : List Bool, val l < 2 ^ l.length
  | [] => Nat.zero_lt_one
  | b :: l => by
    have := val_lt l
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    show b.toNat + 2 * val l < 2 ^ (l.length + 1)
    rw [Nat.pow_succ]; omega

theorem bitsOf_val : ∀ l : List Bool, bitsOf l.length (val l) = l
  | [] => rfl
  | b :: l => by
    show ((b.toNat + 2 * val l) % 2 == 1) :: bitsOf l.length ((b.toNat + 2 * val l) / 2) = b :: l
    have e1 : ((b.toNat + 2 * val l) % 2 == 1) = b := by
      rw [Nat.add_mul_mod_self_left]; cases b <;> rfl
    have e2 : (b.toNat + 2 * val l) / 2 = val l := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
      cases b
      · show 0 / 2 + val l = val l; rw [Nat.zero_div, Nat.zero_add]
      · show 1 / 2 + val l = val l; rw [show 1 / 2 = 0 from rfl, Nat.zero_add]
    rw [e1, e2, bitsOf_val l]

theorem bitsT_pack : ∀ (k n : Nat), DataJet.bitsT k n = packT ((bitsOf k n).map boolT)
  | 0, _ => rfl
  | k + 1, n => by
    show pairT _ (DataJet.bitsT k (n / 2)) = pairT _ (packT _)
    rw [bitsT_pack k (n / 2)]

theorem range_map_getD {α : Type} (d : α) : ∀ l : List α, (List.range l.length).map (fun i => l.getD i d) = l
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    show a :: (List.range l.length).map (fun i => (a :: l).getD (i + 1) d) = a :: l
    exact congrArg _ (range_map_getD d l)

theorem bitsOf_length : ∀ (k n : Nat), (bitsOf k n).length = k
  | 0, _ => rfl
  | k + 1, n => congrArg (· + 1) (bitsOf_length k (n / 2))

theorem chunk_length (bs : List Bool) (i : Nat) : (chunk bs i).length = 31 := by
  rw [chunk, List.length_map, List.length_range]

theorem feltN_chunk (bs : List Bool) (i : Nat) :
    DataJet.feltN (val (chunk bs i)) = packT ((List.range 31).map fun j => boolT (bs.getD (31 * i + j) false)) := by
  show DataJet.bitsT 31 _ = _
  rw [bitsT_pack, ← chunk_length bs i, bitsOf_val, chunk, List.map_map]; rfl

theorem valsB_length (bs : List Bool) : (valsB bs).length = 16 := by
  rw [valsB, List.length_map, List.length_range]

theorem valsB_lt (bs : List Bool) (i : Nat) (hi : i < 16) : (valsB bs).getD i 0 < 2 ^ 31 := by
  rw [valsB, getD_map' (fun i => val (chunk bs i)) 0 (List.range 16) i 0 (by rw [List.length_range]; exact hi),
    range_getD i hi]
  have := val_lt (chunk bs i)
  rwa [chunk_length] at this

/-- `overrideC` over the formals `[s, s + n)`. -/
theorem override_out : ∀ (n s : Nat) (γ : Nat → Term) (Ns : List Term) (i : Nat), i < s →
    overrideC γ (List.range' s n) Ns i = γ i
  | 0, _, _, _, _, _ => rfl
  | _ + 1, _, _, [], _, _ => rfl
  | n + 1, s, γ, N :: Ns, i, hi => by
    show overrideC (updC γ s N) (List.range' (s + 1) n) Ns i = γ i
    rw [override_out n (s + 1) _ Ns i (by omega)]
    exact if_neg (by omega)

theorem override_in : ∀ (n s : Nat) (γ : Nat → Term) (Ns : List Term), Ns.length = n →
    ∀ i, s ≤ i → i < s + n → overrideC γ (List.range' s n) Ns i = Ns.getD (i - s) K
  | 0, _, _, _, _, _, h1, h2 => absurd h2 (by omega)
  | n + 1, s, γ, N :: Ns, hl, i, h1, h2 => by
    show overrideC (updC γ s N) (List.range' (s + 1) n) Ns i = _
    by_cases hi : i = s
    · rw [hi, override_out n (s + 1) _ Ns s (by omega), Nat.sub_self]
      exact if_pos rfl
    · rw [override_in n (s + 1) _ Ns (Nat.succ.inj hl) i (by omega) (by omega)]
      show _ = (N :: Ns).getD (i - s) K
      rw [show i - s = (i - (s + 1)) + 1 by omega]
      rfl
  | _ + 1, _, _, [], hl, _, _, _ => nomatch hl

/-- A pointwise reduction of argument lists. -/
def Pw : List Term → List Term → Prop
  | [], [] => True
  | a :: as, b :: bs => WSteps a b ∧ Pw as bs
  | _, _ => False

theorem Pw.append : ∀ {as bs cs ds : List Term}, Pw as bs → Pw cs ds → Pw (as ++ cs) (bs ++ ds)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, ⟨h, hs⟩, h' => ⟨h, Pw.append hs h'⟩
  | [], _ :: _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, h, _ => nomatch h

theorem Pw.map {α : Type} (f g : α → Term) : ∀ l : List α, (∀ a ∈ l, WSteps (f a) (g a)) → Pw (l.map f) (l.map g)
  | [], _ => trivial
  | a :: l, h => ⟨h a (List.mem_cons_self ..), Pw.map f g l fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

theorem Pw.flatMap {α : Type} (f g : α → List Term) : ∀ l : List α, (∀ a ∈ l, Pw (f a) (g a)) →
    Pw (l.flatMap f) (l.flatMap g)
  | [], _ => trivial
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact Pw.append (h a (List.mem_cons_self ..)) (Pw.flatMap f g l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem appT_pw : ∀ (h : Term) {as bs : List Term}, Pw as bs → WSteps (appT h as) (appT h bs)
  | _, [], [], _ => .refl _
  | h, a :: as, b :: bs, ⟨hab, hs⟩ =>
    (WSteps.appT (WSteps.right h hab) as).trans (appT_pw (h ⬝ b) hs)
  | _, [], _ :: _, hs => nomatch hs
  | _, _ :: _, [], hs => nomatch hs

theorem mem_range16 {i : Nat} (h : i ∈ List.range 16) : i < 16 := List.mem_range.1 h

/-- The inputs: sixteen literals of 31 bits, from the arguments `1 … 496`. -/
def inO : OTerm := packO ((List.range 16).map fun i => packO ((List.range 31).map fun j => .var (1 + (31 * i + j))))

/-- The outputs: the bits of the sixteen outputs, from the state in `497`. -/
def outArgs : List OTerm := (List.range 16).flatMap fun i => (List.range 31).map fun j => projO j (projO i (.var 497))

/-- **Poseidon2 on bits**: `[k b₀ … b₄₉₅] (\[s] k (π₀ π₀ s) … (π₃₀ π₁₅ s))
    (P (literals of the bits))`. -/
def Pbits : Term := lam (List.range 497) (absN [497] (appL (.var 0) outArgs) ⬝ₒ (P.toO ⬝ₒ inO))

/-- **`Pbits` implements the bit contract.** -/
theorem Pbits_implements : DataJet.CImplements poseidon2B Pbits := by
  intro x k
  rw [poseidon2B_encI, poseidon2B_encO, poseidon2B_spec]
  obtain ⟨bs, hbs⟩ := x
  show WSteps (appT Pbits (k :: bs.map boolT)) (appT k (((permute (valsB bs)).flatMap (bitsOf 31)).map boolT))
  have hlen : (k :: bs.map boolT).length = (List.range 497).length := by
    rw [List.length_cons, List.length_map, hbs, List.length_range]
  have hb := lam_beta (List.range 497) (absN [497] (appL (.var 0) outArgs) ⬝ₒ (P.toO ⬝ₒ inO)) (k :: bs.map boolT) hlen
  have hσ0 : ∀ i, i < 497 → overrideC (fun _ => I) (List.range 497) (k :: bs.map boolT) i =
      (k :: bs.map boolT).getD i K := fun i hi => by
    rw [List.range_eq_range', override_in 497 0 _ _ (by rw [List.length_cons, List.length_map, hbs]) i
      (Nat.zero_le _) (by omega), Nat.sub_zero]
  generalize hg : overrideC (fun _ => I) (List.range 497) (k :: bs.map boolT) = σ at hb hσ0
  have hσ : ∀ i, i < 497 → σ i = (k :: bs.map boolT).getD i K := hσ0
  have hσb : ∀ m, m < 496 → σ (1 + m) = boolT (bs.getD m false) := fun m hm => by
    rw [hσ (1 + m) (by omega), Nat.add_comm 1 m]
    show (bs.map boolT).getD m K = _
    rw [getD_map' boolT false bs m K (by rw [hbs]; exact hm)]
  -- The input literals: the state of the bits' values.
  have hin : inO.close σ = DataJet.stateN (valsB bs) := by
    rw [stateN_pack, valsB, List.map_map, inO, close_packO, List.map_map]
    apply congrArg packT
    refine List.map_congr_left fun i hi => ?_
    have hi' := mem_range16 hi
    show (packO _).close σ = DataJet.feltN (val (chunk bs i))
    rw [close_packO, List.map_map, feltN_chunk]
    apply congrArg packT
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 31 := List.mem_range.1 hj
    exact hσb _ (by omega)
  have e1 : (absN [497] (appL (.var 0) outArgs) ⬝ₒ (P.toO ⬝ₒ inO)).close σ =
      (absN [497] (appL (.var 0) outArgs)).close σ ⬝ (P ⬝ DataJet.stateN (valsB bs)) := by
    show _ ⬝ (P.toO.close σ ⬝ inO.close σ) = _
    rw [close_toO, hin]
  rw [e1] at hb
  have hb2 := absN_beta_close [497] (appL (.var 0) outArgs) σ [P ⬝ DataJet.stateN (valsB bs)] rfl
  generalize hg' : overrideC σ [497] [P ⬝ DataJet.stateN (valsB bs)] = σ' at hb2
  have h0 : σ' 0 = k := by
    rw [← hg']
    show updC σ 497 (P ⬝ DataJet.stateN (valsB bs)) 0 = k
    unfold updC
    rw [if_neg (by decide)]
    exact hσ 0 (by decide)
  have h497 : σ' 497 = P ⬝ DataJet.stateN (valsB bs) := by
    rw [← hg']
    show updC σ 497 (P ⬝ DataJet.stateN (valsB bs)) 497 = _
    unfold updC
    exact if_pos rfl
  rw [_root_.close_appL, show (OTerm.var 0).close σ' = σ' 0 from rfl, h0, outArgs, List.map_flatMap] at hb2
  refine hb.trans (hb2.trans ?_)
  generalize hys' : permute (valsB bs) = ys
  have hys : ys.length = 16 := by rw [← hys']; exact permute_len _ (valsB_length bs)
  have hP := P_specN (valsB bs) (valsB_length bs) (valsB_lt bs)
  rw [hys'] at hP
  have hpw : Pw ((List.range 16).flatMap fun i => ((List.range 31).map fun j => projO j (projO i (.var 497))).map
        (OTerm.close σ'))
      ((List.range 16).flatMap fun i => (List.range 31).map fun j => boolT ((bitsOf 31 (ys.getD i 0)).getD j false)) := by
    refine Pw.flatMap _ _ _ fun i hi => ?_
    have hi' := mem_range16 hi
    rw [List.map_map]
    refine Pw.map _ _ _ fun j hj => ?_
    have hj' : j < 31 := List.mem_range.1 hj
    show WSteps ((projO j (projO i (.var 497))).close σ') _
    rw [close_projO, close_projO, show (OTerm.var 497).close σ' = σ' 497 from rfl, h497]
    refine (projT_congr j (projT_congr i hP)).trans ?_
    rw [stateN_pack]
    have hi2 : i < (ys.map DataJet.feltN).length := by rw [List.length_map, hys]; exact hi'
    refine (projT_congr j (proj_pack i _ hi2)).trans ?_
    rw [getD_map' DataJet.feltN 0 ys i K (by rw [hys]; exact hi'),
      show DataJet.feltN (ys.getD i 0) = DataJet.bitsT 31 (ys.getD i 0) from rfl, bitsT_pack]
    have hj2 : j < ((bitsOf 31 (ys.getD i 0)).map boolT).length := by
      rw [List.length_map, bitsOf_length]; exact hj'
    refine (proj_pack j _ hj2).trans ?_
    rw [getD_map' boolT false _ j K (by rw [bitsOf_length]; exact hj')]
    exact .refl _
  refine (appT_pw k hpw).trans ?_
  have inner : ∀ y, (List.range 31).map (fun j => boolT ((bitsOf 31 y).getD j false)) = (bitsOf 31 y).map boolT :=
    fun y => by
      have := range_map_getD false (bitsOf 31 y)
      rw [bitsOf_length] at this
      rw [show (fun j => boolT ((bitsOf 31 y).getD j false)) = boolT ∘ (fun j => (bitsOf 31 y).getD j false) from rfl,
        ← List.map_map, this]
  simp only [inner]
  rw [List.map_flatMap]
  have e : (List.range 16).flatMap (fun i => (bitsOf 31 (ys.getD i 0)).map boolT) =
      ys.flatMap (fun y => (bitsOf 31 y).map boolT) :=
    len16 (P := fun ys => (List.range 16).flatMap (fun i => (bitsOf 31 (ys.getD i 0)).map boolT) =
      ys.flatMap (fun y => (bitsOf 31 y).map boolT)) (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => rfl) ys hys
  rw [e]
  exact .refl _

-- ---------------------------------------------------------------------------
-- The jet on a comb of bits
-- ---------------------------------------------------------------------------

/-- The comb of the bits: Scott pairs, the last bit bare (`BT.enc` of a
    comb, `combBT`). -/
def combT : List Bool → Term
  | [] => boolT false
  | [b] => boolT b
  | b :: bs => pairT (boolT b) (combT bs)

/-- **The Poseidon2 jet on a comb**: a continuation, then the inputs' 496
    bits as one comb; the continuation receives the outputs' 496 bits. -/
def poseidon2Comb : DataJet.CContract Bits (List Nat) :=
  ⟨fun bs => [combT bs.1], fun ys => (ys.flatMap (bitsOf 31)).map boolT, fun bs => permute (valsB bs.1)⟩

theorem poseidon2Comb_encI (bs : Bits) : poseidon2Comb.encI bs = [combT bs.1] := rfl
theorem poseidon2Comb_encO : poseidon2Comb.encO = fun ys => (ys.flatMap (bitsOf 31)).map boolT := rfl
theorem poseidon2Comb_spec (bs : Bits) : poseidon2Comb.spec bs = permute (valsB bs.1) := by
  dsimp only [poseidon2Comb]

/-- `spread n a p`: the comb `p` of `n` bits passed to `a`, bit by bit. -/
def spreadT : Nat → Term
  | 0 => lam [0, 1] (.var 0 ⬝ₒ .var 1)
  | 1 => lam [0, 1] (.var 0 ⬝ₒ .var 1)
  | n + 2 => lam [0, 1] (.var 1 ⬝ₒ absN [2, 3] ((spreadT (n + 1)).toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ .var 3))

theorem spreadT_spec : ∀ (n : Nat) (a : Term) (bs : List Bool), bs.length = n + 1 →
    WSteps (spreadT (n + 1) ⬝ a ⬝ combT bs) (appT a (bs.map boolT))
  | 0, a, [b], _ => lam_beta [0, 1] (.var 0 ⬝ₒ .var 1) [a, boolT b] rfl
  | n + 1, a, b :: c :: bs, hl => by
    have h1 := lam_beta [0, 1] (.var 1 ⬝ₒ absN [2, 3] ((spreadT (n + 1)).toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ .var 3))
      [a, combT (b :: c :: bs)] rfl
    let σ := overrideC (fun _ => I) [0, 1] [a, combT (b :: c :: bs)]
    have e1 : (.var 1 ⬝ₒ absN [2, 3] ((spreadT (n + 1)).toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ .var 3) : OTerm).close σ =
        pairT (boolT b) (combT (c :: bs)) ⬝ (absN [2, 3] ((spreadT (n + 1)).toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ .var 3)).close σ :=
      rfl
    rw [e1] at h1
    have h2 := pairT_app (boolT b) (combT (c :: bs)) ((absN [2, 3] ((spreadT (n + 1)).toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ .var 3)).close σ)
    have h3 := absN_beta_close [2, 3] ((spreadT (n + 1)).toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ .var 3) σ
      [boolT b, combT (c :: bs)] rfl
    have e3 : ((spreadT (n + 1)).toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ .var 3).close
        (overrideC σ [2, 3] [boolT b, combT (c :: bs)]) = spreadT (n + 1) ⬝ (a ⬝ boolT b) ⬝ combT (c :: bs) := by
      show (spreadT (n + 1)).toO.close _ ⬝ _ ⬝ _ = _
      rw [close_toO]; rfl
    rw [e3] at h3
    have ih := spreadT_spec n (a ⬝ boolT b) (c :: bs) (Nat.succ.inj hl)
    exact h1.trans (h2.trans (h3.trans ih))
  | 0, _, [], hl => nomatch hl
  | 0, _, _ :: _ :: _, hl => absurd (Nat.succ.inj hl) (Nat.succ_ne_zero _)
  | _ + 1, _, [], hl => nomatch hl
  | _ + 1, _, [_], hl => absurd (Nat.succ.inj hl).symm (Nat.succ_ne_zero _)

/-- `[k β] spread₄₉₆ (Pbits k) β`. -/
def Pcomb : Term := lam [0, 1] ((spreadT 496).toO ⬝ₒ (Pbits.toO ⬝ₒ .var 0) ⬝ₒ .var 1)

theorem close_app' (σ : Nat → Term) (f x : OTerm) : (f ⬝ₒ x).close σ = f.close σ ⬝ x.close σ := rfl

/-- **`Pcomb` implements the comb contract.** -/
theorem Pcomb_implements : DataJet.CImplements poseidon2Comb Pcomb := by
  intro x k
  rw [poseidon2Comb_encI, poseidon2Comb_encO, poseidon2Comb_spec]
  obtain ⟨bs, hbs⟩ := x
  have h1 := lam_beta [0, 1] ((spreadT 496).toO ⬝ₒ (Pbits.toO ⬝ₒ .var 0) ⬝ₒ .var 1) [k, combT bs] rfl
  rw [close_app', close_app', close_app', close_toO, close_toO] at h1
  have h2 : WSteps (spreadT 496 ⬝ (Pbits ⬝ k) ⬝ combT bs) (appT (Pbits ⬝ k) (bs.map boolT)) :=
    spreadT_spec 495 (Pbits ⬝ k) bs hbs
  have h3 := Pbits_implements ⟨bs, hbs⟩ k
  rw [poseidon2B_encI, poseidon2B_encO, poseidon2B_spec, appT] at h3
  exact h1.trans (h2.trans h3)

end Poseidon2SKI
