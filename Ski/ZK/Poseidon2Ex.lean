import Ski.ZK.Poseidon2

set_option linter.unusedSimpArgs false

/-!
# Poseidon2's layers as expressions

The sublayers of Poseidon2's rounds as arithmetic expressions over sixteen
numbered inputs (`Ex`), and the bridges: on sixteen inputs, each sublayer
of the specification equals its expressions' value (`bridge_sbox`,
`bridge_mat4`, `bridge_mix`, `bridge_sbox0`, `bridge_intLin`).  Two
consumers read them: the SKI implementation compiles them to terms
(`Ski/ZK/Poseidon2SKI.lean`), and the Poseidon2 table reads them as
constraints (`Ski/Circuit/P2Air.lean`).  This file holds no terms, so a
program that imports it initializes nothing large.
-/

namespace Poseidon2SKI

open Poseidon2

-- ---------------------------------------------------------------------------
-- Expressions over the field
-- ---------------------------------------------------------------------------

/-- Arithmetic expressions over numbered inputs: the operations the
    specification uses. -/
inductive Ex
  | var (i : Nat)
  | lit (n : Nat)
  | add (a b : Ex)
  | mul (a b : Ex)
  | md (a : Ex)
  | sbox (a : Ex)
  deriving Inhabited

def Ex.eval (ρ : Nat → Nat) : Ex → Nat
  | .var i => ρ i
  | .lit n => n
  | .add a b => a.eval ρ + b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ
  | .md a => Poseidon2.md (a.eval ρ)
  | .sbox a => Poseidon2.sbox (a.eval ρ)

-- ---------------------------------------------------------------------------
-- The specification's layers over expressions
-- ---------------------------------------------------------------------------

/-- `Poseidon2.mat4`, over expressions. -/
def mat4E : List Ex → List Ex
  | [x0, x1, x2, x3] =>
    [.md (.add (.add (.add (.mul (.lit 2) x0) (.mul (.lit 3) x1)) x2) x3),
     .md (.add (.add (.add x0 (.mul (.lit 2) x1)) (.mul (.lit 3) x2)) x3),
     .md (.add (.add (.add x0 x1) (.mul (.lit 2) x2)) (.mul (.lit 3) x3)),
     .md (.add (.add (.add (.mul (.lit 3) x0) x1) x2) (.mul (.lit 2) x3))]
  | l => l

def chunks4E : List Ex → List (List Ex)
  | a :: b :: c :: d :: r => [a, b, c, d] :: chunks4E r
  | [] => []
  | l => [l]

def colSumE (s : List Ex) (k : Nat) : Ex :=
  .md (((List.range s.length).filter (fun i => i % 4 == k)).foldl (fun acc i => .add acc (s.getD i (.lit 0))) (.lit 0))

def intLinearE (s : List Ex) : List Ex :=
  let sum := Ex.md (s.foldl .add (.lit 0))
  (s.zip V).map fun (x, v) => .md (.add sum (.mul (.lit v) x))

/-- The sixteen inputs. -/
def vars16 : List Ex := (List.range 16).map Ex.var

-- ---------------------------------------------------------------------------
-- The bridges: each layer of the specification is its expressions' value
-- ---------------------------------------------------------------------------

/-- A statement about every list of sixteen, from one about sixteen
    variables. -/
theorem len16 {α : Type} {P : List α → Prop} (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : α, P [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]) :
    ∀ l : List α, l.length = 16 → P l
  | [], hl => nomatch hl
  | [_], hl => nomatch hl
  | [_, _], hl => nomatch hl
  | [_, _, _], hl => nomatch hl
  | [_, _, _, _], hl => nomatch hl
  | [_, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _, _, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _, _, _, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _, _, _, _, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _], hl => nomatch hl
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _], hl => nomatch hl
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15], _ => h a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: r, hl => absurd hl (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 17 r.length)))

/-- The value of the inputs `vs`. -/
def at16 (vs : List Nat) : Nat → Nat := fun i => vs.getD i 0

/-! The rounds split into sublayers, so that the S-box and `M₄` results
are components of the state: a full round is the S-box layer, `M₄` on
each block, and the column mixing; a partial round is the S-box on the
first entry and the internal layer.  The specification's rounds are these
compositions by definition (`extRound_split`, `intRound_split`). -/

def sboxL (rc s : List Nat) : List Nat := (s.zip rc).map fun (x, c) => sbox (x + c)
def mat4L (s : List Nat) : List Nat := (chunks4 s).flatMap mat4
def mixL (m : List Nat) : List Nat := (List.range m.length).map fun i => md (m.getD i 0 + colSum m (i % 4))
def sbox0L (c : Nat) : List Nat → List Nat
  | x :: r => sbox (x + c) :: r
  | [] => []

theorem extLinear_split (s : List Nat) : extLinear s = mixL (mat4L s) := rfl
theorem extRound_split (s rc : List Nat) : extRound s rc = mixL (mat4L (sboxL rc s)) := rfl
theorem intRound_split (s : List Nat) (c : Nat) : intRound s c = intLinear (sbox0L c s) := by
  cases s <;> rfl

def sboxLE (rc : List Nat) : List Ex := (vars16.zip rc).map fun (x, c) => .sbox (.add x (.lit c))
def mat4LE : List Ex := (chunks4E vars16).flatMap mat4E
def mixLE : List Ex := (List.range 16).map fun i => .md (.add (vars16.getD i (.lit 0)) (colSumE vars16 (i % 4)))
def sbox0LE (c : Nat) : List Ex := match vars16 with
  | x :: r => .sbox (.add x (.lit c)) :: r
  | [] => []
def intLinLE : List Ex := intLinearE vars16

theorem bridge_sbox (vs rc : List Nat) (hv : vs.length = 16) (hc : rc.length = 16) :
    (sboxLE rc).map (Ex.eval (at16 vs)) = sboxL rc vs :=
  len16 (P := fun rc => (sboxLE rc).map (Ex.eval (at16 vs)) = sboxL rc vs)
    (fun c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 => len16 (P := fun vs => (sboxLE [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15]).map (Ex.eval (at16 vs)) = sboxL [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] vs)
      (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => rfl) vs hv) rc hc

theorem bridge_mat4 (vs : List Nat) (hv : vs.length = 16) : mat4LE.map (Ex.eval (at16 vs)) = mat4L vs :=
  len16 (P := fun vs => mat4LE.map (Ex.eval (at16 vs)) = mat4L vs) (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => rfl) vs hv

theorem bridge_mix (vs : List Nat) (hv : vs.length = 16) : mixLE.map (Ex.eval (at16 vs)) = mixL vs :=
  len16 (P := fun vs => mixLE.map (Ex.eval (at16 vs)) = mixL vs) (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => by
    have h : [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15].length = 16 := rfl
    simp only [mixL, colSum, h]
    rfl) vs hv

theorem bridge_sbox0 (vs : List Nat) (c : Nat) (hv : vs.length = 16) :
    (sbox0LE c).map (Ex.eval (at16 vs)) = sbox0L c vs :=
  len16 (P := fun vs => (sbox0LE c).map (Ex.eval (at16 vs)) = sbox0L c vs) (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => rfl) vs hv

theorem bridge_intLin (vs : List Nat) (hv : vs.length = 16) : intLinLE.map (Ex.eval (at16 vs)) = intLinear vs :=
  len16 (P := fun vs => intLinLE.map (Ex.eval (at16 vs)) = intLinear vs) (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => rfl) vs hv

theorem band_l {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> first | rfl | exact nomatch h

theorem band_r {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> first | rfl | exact nomatch h

theorem sboxL_len (rc vs : List Nat) (hv : vs.length = 16) (hc : rc.length = 16) : (sboxL rc vs).length = 16 := by
  rw [← bridge_sbox vs rc hv hc, List.length_map]
  exact len16 (P := fun rc => (sboxLE rc).length = 16) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) rc hc

theorem mat4L_len (vs : List Nat) (hv : vs.length = 16) : (mat4L vs).length = 16 := by
  rw [← bridge_mat4 vs hv, List.length_map]; rfl

theorem mixL_len (vs : List Nat) (hv : vs.length = 16) : (mixL vs).length = 16 := by
  rw [← bridge_mix vs hv, List.length_map]; rfl

theorem intLinear_len (vs : List Nat) (hv : vs.length = 16) : (Poseidon2.intLinear vs).length = 16 := by
  rw [← bridge_intLin vs hv, List.length_map]; rfl

theorem sbox0L_len (c : Nat) : ∀ vs : List Nat, (sbox0L c vs).length = vs.length
  | [] => rfl
  | _ :: _ => rfl

theorem foldl_ext_len : ∀ (rcs : List (List Nat)), rcs.all (fun rc => decide (rc.length = 16)) = true →
    ∀ s : List Nat, s.length = 16 → (rcs.foldl Poseidon2.extRound s).length = 16
  | [], _, _, hs => hs
  | rc :: rcs, h, s, hs => by
    show ((rcs.foldl Poseidon2.extRound (Poseidon2.extRound s rc))).length = 16
    refine foldl_ext_len rcs (band_r h) _ ?_
    rw [extRound_split]
    exact mixL_len _ (mat4L_len _ (sboxL_len rc s hs (of_decide_eq_true (band_l h))))

theorem foldl_int_len : ∀ (cs : List Nat) (s : List Nat), s.length = 16 →
    (cs.foldl Poseidon2.intRound s).length = 16
  | [], _, hs => hs
  | c :: cs, s, hs => by
    show ((cs.foldl Poseidon2.intRound (Poseidon2.intRound s c))).length = 16
    refine foldl_int_len cs _ ?_
    rw [intRound_split]
    exact intLinear_len _ (by rw [sbox0L_len]; exact hs)

/-- The permutation keeps sixteen entries. -/
theorem permute_len (s : List Nat) (hs : s.length = 16) : (Poseidon2.permute s).length = 16 := by
  show ((Poseidon2.rcTerminal.foldl Poseidon2.extRound
    (Poseidon2.rcInternal.foldl Poseidon2.intRound
      (Poseidon2.rcInitial.foldl Poseidon2.extRound (Poseidon2.extLinear s))))).length = 16
  refine foldl_ext_len _ (by decide) _ (foldl_int_len _ _ (foldl_ext_len _ (by decide) _ ?_))
  rw [extLinear_split]
  exact mixL_len _ (mat4L_len _ hs)

theorem getD_map' {α β : Type} (f : α → β) (d : α) : ∀ (l : List α) (i : Nat) (d' : β), i < l.length →
    (l.map f).getD i d' = f (l.getD i d)
  | _ :: _, 0, _, _ => rfl
  | _ :: l, i + 1, d', h => getD_map' f d l i d' (Nat.lt_of_succ_lt_succ h)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)

theorem range_getD : ∀ i : Nat, i < 16 → (List.range 16).getD i 0 = i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | n + 16, h => absurd h (Nat.not_lt.2 (Nat.le_add_left 16 n))

theorem range16_map {α : Type} (d : α) (l : List α) (hl : l.length = 16) : (List.range 16).map (fun i => l.getD i d) = l :=
  len16 (P := fun l => (List.range 16).map (fun i => l.getD i d) = l) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) l hl

end Poseidon2SKI
