import Ski.ZK.Poseidon2Lin

/-!
# Poseidon2, generically, and Plonky3's instance

Poseidon2 as Grassi, Khovratovich and Schofnegger define it ("Poseidon2:
A Faster Version of the Poseidon Hash Function", AFRICACRYPT 2023,
eprint 2023/323), over a prime `p`, with its choices as parameters
(`Params`):

- the width `t`, the S-box `x ↦ x^d`, `R_F` full rounds split in halves
  around `R_P` partial rounds;
- the external matrix `M_E` and the internal matrix `M_I`, each a
  `t × t` matrix;
- the round constants: `t` for each full round, one for each partial
  round.

The permutation (`permute`) applies `M_E` first; then each full round adds
its `t` constants, applies the S-box to every entry, and applies `M_E`;
each partial round adds its constant to the first entry, applies the
S-box to it alone, and applies `M_I`.  The paper's matrices are
constructions: `M_E = circ(2 M₄, M₄, …, M₄)` from a `4 × 4` matrix `M₄`
for `t = 4k` with `k ≥ 2` (`circM4`), and `M_I` with `μᵢ` on the diagonal
and 1 elsewhere (`diagOnes`).

**`permute_plonky3`**: `Poseidon2.permute`, the specification the proofs
use, is the instance at `t = 16`, `R_F = 8`, `R_P = 13`, `d = 7`
(`plonky3`, whose shapes `plonky3_ok` checks), with Plonky3's matrices
and constants.  The matrices and constants are read from Plonky3's
source; Plonky3's Rust is tied to the specification only by the three
test vectors (`permute_matches`).  Plonky3's choices are
not the paper's examples: its `M₄` is `[[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]`
(`MDSMat4`), where the paper suggests another, and its `μᵢ` is `1 + Vᵢ`
for a `V` it chose for cheap multiplication.  The round constants are the
Grain LFSR's (`Grain.rc_grain`).  That these matrices meet the paper's
security conditions is Plonky3's claim, not proved here; that they are
invertible is (`Ski/ZK/Poseidon2Inv.lean`).
-/

namespace Poseidon2.Generic

open Poseidon2.Lin Poseidon2SKI

/-- Poseidon2's parameters.  The permutation runs one full round per row
    of `rcFirst` and `rcLast` and one partial round per entry of
    `rcPartial`; `Params.ok` ties those counts to `RF` and `RP`, and the
    rows' and matrices' widths to `t`. -/
structure Params where
  /-- The field's prime. -/
  p : Nat
  /-- The width. -/
  t : Nat
  /-- The S-box's exponent. -/
  d : Nat
  /-- Full rounds, half before and half after the partial ones. -/
  RF : Nat
  /-- Partial rounds. -/
  RP : Nat
  /-- The external matrix, as its rows. -/
  ME : List (List Nat)
  /-- The internal matrix, as its rows. -/
  MI : List (List Nat)
  /-- The constants of the first `RF / 2` full rounds. -/
  rcFirst : List (List Nat)
  /-- The constants of the partial rounds. -/
  rcPartial : List Nat
  /-- The constants of the last `RF / 2` full rounds. -/
  rcLast : List (List Nat)

/-- The parameters' shapes: `RF` even, `RF / 2` rows of `t` constants on
    each side, `RP` partial constants, square matrices of width `t`. -/
def Params.ok (P : Params) : Bool :=
  P.RF % 2 == 0 && P.rcFirst.length == P.RF / 2 && P.rcLast.length == P.RF / 2 &&
  P.rcPartial.length == P.RP && P.rcFirst.all (·.length == P.t) && P.rcLast.all (·.length == P.t) &&
  P.ME.length == P.t && P.ME.all (·.length == P.t) && P.MI.length == P.t && P.MI.all (·.length == P.t)

/-- The S-box. -/
def Params.sbox (P : Params) (x : Nat) : Nat := x ^ P.d % P.p

/-- A full round: every entry's constant, every entry's S-box, `M_E`. -/
def Params.fullRound (P : Params) (s rc : List Nat) : List Nat :=
  matVec P.p P.ME ((s.zip rc).map fun (x, c) => P.sbox (x + c))

/-- A partial round: the first entry's constant and S-box, `M_I`. -/
def Params.partialRound (P : Params) : List Nat → Nat → List Nat
  | x :: r, c => matVec P.p P.MI (P.sbox (x + c) :: r)
  | [], _ => []

/-- **Poseidon2**: `M_E`, the first half of the full rounds, the partial
    rounds, the second half of the full rounds. -/
def Params.permute (P : Params) (s : List Nat) : List Nat :=
  let s := P.rcFirst.foldl P.fullRound (matVec P.p P.ME s)
  let s := P.rcPartial.foldl P.partialRound s
  P.rcLast.foldl P.fullRound s

/-- The paper's external matrix for `t = 4k`: block `(I, J)` is `2 M₄` on
    the diagonal and `M₄` off it. -/
def circM4 (M4 : List (List Nat)) (k : Nat) : List (List Nat) :=
  (List.range (4 * k)).map fun i => (List.range (4 * k)).map fun j =>
    (if i / 4 = j / 4 then 2 else 1) * ((M4.getD (i % 4) []).getD (j % 4) 0)

/-- The paper's internal matrix: `μᵢ` on the diagonal, 1 elsewhere. -/
def diagOnes (μ : List Nat) : List (List Nat) :=
  (List.range μ.length).map fun i => (List.range μ.length).map fun j =>
    if i = j then μ.getD i 0 else 1

/-- Plonky3's `M₄` (`MDSMat4`). -/
def mat4M : List (List Nat) := [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]]

/-- **Plonky3's Poseidon2 over BabyBear, width 16** (Plonky3 0.8's
    `default_babybear_poseidon2_16`): `M_E = circ(2 M₄, M₄, M₄, M₄)`,
    `M_I = 1 + Diag(V)`, that is `μᵢ = 1 + Vᵢ`. -/
def plonky3 : Params where
  p := Poseidon2.p
  t := 16
  d := 7
  RF := 8
  RP := 13
  ME := circM4 mat4M 4
  MI := diagOnes (V.map fun v => (1 + v) % Poseidon2.p)
  rcFirst := rcInitial
  rcPartial := rcInternal
  rcLast := rcTerminal

theorem plonky3_ok : plonky3.ok = true := by decide +kernel

-- ---------------------------------------------------------------------------
-- The specification's layers are the matrices
-- ---------------------------------------------------------------------------

theorem getD_map_eval (ρ : Nat → Nat) : ∀ (l : List Ex) (i : Nat),
    (l.map (Ex.eval ρ)).getD i 0 = (l.getD i (.lit 0)).eval ρ
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_map_eval ρ l i

/-- The external layer's rows, from the expressions of `M₄` then the
    column mixing, the one substituted into the other. -/
theorem linRows_ext : linRows (mixLE.map (P2Air.exSubst mat4LE)) = some plonky3.ME := by decide +kernel

theorem linRows_int : linRows intLinLE = some plonky3.MI := by decide +kernel

theorem rows_len16 (M : List (List Nat)) (hM : M.all (·.length == 16) = true) (s : List Nat)
    (hs : s.length = 16) : ∀ r ∈ M, r.length ≤ s.length := by
  intro r hr
  rw [hs]
  exact Nat.le_of_eq (beq_iff_eq.mp (List.all_eq_true.mp hM r hr))

/-- **The external layer is `M_E`.** -/
theorem extLinear_eq (s : List Nat) (hs : s.length = 16) : extLinear s = matVec p plonky3.ME s := by
  rw [extLinear_split, ← bridge_mix _ (mat4L_len s hs), ← bridge_mat4 s hs]
  have hρ : at16 (mat4LE.map (Ex.eval (at16 s))) = fun i => (mat4LE.getD i (.lit 0)).eval (at16 s) :=
    funext fun i => getD_map_eval (at16 s) mat4LE i
  rw [hρ, matVec_rows _ s (rows_len16 _ (by decide +kernel) s hs)]
  have h := linRows_sound (at16 s) _ _ linRows_ext
  rw [List.map_map] at h
  show _ = List.map (fun c => dotF c 0 (at16 s) % p) plonky3.ME
  rw [← h]
  apply List.map_congr_left
  intro e _
  exact (P2Air.eval_subst (at16 s) mat4LE e).symm

/-- **The internal layer is `M_I`.** -/
theorem intLinear_eq (s : List Nat) (hs : s.length = 16) : intLinear s = matVec p plonky3.MI s := by
  rw [← bridge_intLin s hs, matVec_rows _ s (rows_len16 _ (by decide +kernel) s hs)]
  exact linRows_sound (at16 s) _ _ linRows_int

-- ---------------------------------------------------------------------------
-- The rounds and the permutation
-- ---------------------------------------------------------------------------

theorem matVec_len (q : Nat) (M : List (List Nat)) (s : List Nat) : (matVec q M s).length = M.length :=
  List.length_map _

theorem zip_len16 (s rc : List Nat) (hs : s.length = 16) (hc : rc.length = 16) :
    ((s.zip rc).map fun (x, c) => Poseidon2.sbox (x + c)).length = 16 := by
  rw [List.length_map, List.length_zip, hs, hc]; rfl

theorem foldl_full : ∀ (rcs : List (List Nat)), rcs.all (·.length == 16) = true →
    ∀ s : List Nat, s.length = 16 →
      rcs.foldl extRound s = rcs.foldl plonky3.fullRound s ∧ (rcs.foldl extRound s).length = 16
  | [], _, _, hs => ⟨rfl, hs⟩
  | rc :: rcs, h, s, hs => by
    have h' : (rc.length == 16) = true ∧ rcs.all (·.length == 16) = true := by
      rw [List.all_cons, Bool.and_eq_true] at h; exact h
    have hc : rc.length = 16 := beq_iff_eq.mp h'.1
    have hstep : extRound s rc = plonky3.fullRound s rc :=
      extLinear_eq _ (zip_len16 s rc hs hc)
    have hlen : (extRound s rc).length = 16 := by
      rw [hstep]; exact matVec_len _ _ _
    show rcs.foldl extRound (extRound s rc) = rcs.foldl plonky3.fullRound (plonky3.fullRound s rc) ∧ _
    rw [← hstep]
    exact foldl_full rcs h'.2 _ hlen

theorem foldl_partial : ∀ (cs : List Nat) (s : List Nat), s.length = 16 →
    cs.foldl intRound s = cs.foldl plonky3.partialRound s ∧ (cs.foldl intRound s).length = 16
  | [], _, hs => ⟨rfl, hs⟩
  | c :: cs, s, hs => by
    match s, hs with
    | x :: r, hs =>
      have hstep : intRound (x :: r) c = plonky3.partialRound (x :: r) c :=
        intLinear_eq _ (by show r.length + 1 = 16; exact hs)
      have hlen : (intRound (x :: r) c).length = 16 := by
        rw [hstep]; exact matVec_len _ _ _
      show cs.foldl intRound (intRound (x :: r) c) = cs.foldl plonky3.partialRound (plonky3.partialRound (x :: r) c) ∧ _
      rw [← hstep]
      exact foldl_partial cs _ hlen

/-- **The specification is Poseidon2 with Plonky3's parameters**: on every
    state of sixteen entries, `Poseidon2.permute` is `plonky3.permute`. -/
theorem permute_plonky3 (s : List Nat) (hs : s.length = 16) : Poseidon2.permute s = plonky3.permute s := by
  have h0 : extLinear s = matVec p plonky3.ME s := extLinear_eq s hs
  have h0l : (extLinear s).length = 16 := by rw [h0]; exact matVec_len _ _ _
  obtain ⟨h1, h1l⟩ := foldl_full rcInitial (by decide +kernel) _ h0l
  obtain ⟨h2, h2l⟩ := foldl_partial rcInternal _ h1l
  obtain ⟨h3, _⟩ := foldl_full rcTerminal (by decide +kernel) _ h2l
  show rcTerminal.foldl extRound (rcInternal.foldl intRound (rcInitial.foldl extRound (extLinear s))) =
    rcTerminal.foldl plonky3.fullRound (rcInternal.foldl plonky3.partialRound
      (rcInitial.foldl plonky3.fullRound (matVec p plonky3.ME s)))
  rw [h3, h2, h1, h0]

end Poseidon2.Generic
