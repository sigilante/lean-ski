import Ski.ZK.FSMultiMixSud
import Ski.ZK.FSMultiAdapt
import Ski.ZK.SudDraws

/-!
# Sudoku statements picked after seeing the tables

`FSMultiAdapt`'s picks need the `S` statements to share their draws;
`SudDraws` shows two Sudoku proofs with the same parameters do.  A family
of `n` Sudoku proofs counts the same draws whatever its puzzles, witnesses
and runs (`sudD_sm`, through `sudFS4T_sm`), so `ZKBT` bounds for `S` such
families, one per choice of puzzles, move to one draw count
(`zkbT_sm_congr`), and a distinguisher picking the family from the tables
is bounded by `zkbT_adaptive` (`sud_adaptive`).  The families share the
program tables' height `tP`; `SudDraws`'s `sud_progTp` makes it `14` for
every valid puzzle, so each family's own bound (`sud_interleave` and its
kin, through `htp`) admits the one `tP`.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **A `ZKBT` bound moves to an equal draw count.** -/
theorem zkbT_sm_congr {T X C V : Type} {ST : (T → Nat) → Nat} {K : Nat} {sm sm' : (X → Nat) → Nat}
    {SC : (C → Nat) → Nat} {rv : T → X → V} {pg : T → C → X → T} {sv : T → C → X → V} {ε : Nat}
    (e : sm = sm') (h : ZKBT ST K sm SC rv pg sv ε) : ZKBT ST K sm' SC rv pg sv ε := e ▸ h

set_option maxRecDepth 100000 in
/-- **A family of Sudoku proofs counts the same draws whatever its puzzles,
    witnesses and runs**, the other parameters shared (`sudFS4T_sm`). -/
theorem sudD_sm {V Wv P1 P2 P3 W1 W2 W3 : Type} (off : EF → String → EF) (puzzle : Nat → List Nat) (A : Nat → List Cell) (k : Nat → Nat) (row : Nat → Nat → Air.Row) (tP : Nat → Nat) (S16 : Nat → Nat → List F) (S10 : Nat → Nat → List F) (SP : Nat → Nat → List F) (qv : Nat → EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → Nat → List (EF → EF → List F)) (wc : Nat → Nat → List (EF → EF → List F)) (ww : Nat → Nat → List (EF → EF → List F)) (wp : Nat → Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat → Nat) (αd : Nat → Nat → EF) (B4 : Nat → Nat) (fri : Nat → Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat → Nat) (Rb : Nat → Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → Nat → EF → EF → Nat → Wv) (NS1 : Nat → Nat) (NS2 : Nat → Nat) (NS3 : Nat → Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : Nat → List (List (List F)) → Nat → Nat) (Com2 : Nat → List (List (List F)) → Nat → Nat) (Com3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → Nat) (kr : Nat) (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3) (puzzle' : Nat → List Nat) (A' : Nat → List Cell) (k' : Nat → Nat) (row' : Nat → Nat → Air.Row) (i m : Nat) :
    (sudD (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) (W1 := W1) (W2 := W2) (W3 := W3) off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).sm m = (sudD (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) (W1 := W1) (W2 := W2) (W3 := W3) off puzzle' A' k' row' tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).sm m := by
  rw [sudD, sudD]
  exact sudFS4T_sm off (puzzle i) (A i) (k i) (row i) (tP i) (S16 i) (S10 i) (SP i) (qv i) (wm i) (wc i) (ww i) (wp i) K2 K4 (φ i) N4 (ncw i) (αd i) (B4 i) (fri i) (NR2 i) (Rb i) (Ro i) (NS1 i) (NS2 i) (NS3 i) n1 n2 n3 (Com1 i) (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 i) (nx1 i) (G1 i)) (Com2 i) (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 i) (nx2 i) (G2 i)) (Com3 i) (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 i) (nx3 i) (G3 i)) (fun _ _ _ => false) (puzzle' i) (A' i) (k' i) (row' i) (tP i) (S16 i) (S10 i) (SP i) (qv i) (wm i) (wc i) (ww i) (wp i) K2 K4 (φ i) N4 (ncw i) (αd i) (B4 i) (fri i) (NR2 i) (Rb i) (Ro i) (NS1 i) (NS2 i) (NS3 i) n1 n2 n3 (Com1 i) (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 i) (nx1 i) (G1 i)) (Com2 i) (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 i) (nx2 i) (G2 i)) (Com3 i) (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 i) (nx3 i) (G3 i)) (fun _ _ _ => false) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl m

set_option maxRecDepth 100000 in
/-- **A Sudoku family picked from the tables**: `S` families of `n` Sudoku
    proofs, family `j` with puzzles `puzzle j`, witnesses `A j` and runs
    `k j`, `row j`, the other parameters shared, each meeting a `ZKBT`
    bound at its own draw count (as `sud_interleave` gives); the pick
    `ix H < S` read from the tables.  The draw counts agree (`sudD_sm`), so
    the picked family's real count is at most the sum of the families'
    simulations, each kept where the pick confirms it, plus the errors
    (`zkbT_adaptive`). -/
theorem sud_adaptive {V Wv P1 P2 P3 W1 W2 W3 T C U : Type} (off : EF → String → EF) (puzzle : Nat → Nat → List Nat) (A : Nat → Nat → List Cell) (k : Nat → Nat → Nat) (row : Nat → Nat → Nat → Air.Row) (tP : Nat → Nat) (S16 : Nat → Nat → List F) (S10 : Nat → Nat → List F) (SP : Nat → Nat → List F) (qv : Nat → EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → Nat → List (EF → EF → List F)) (wc : Nat → Nat → List (EF → EF → List F)) (ww : Nat → Nat → List (EF → EF → List F)) (wp : Nat → Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat → Nat) (αd : Nat → Nat → EF) (B4 : Nat → Nat) (fri : Nat → Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat → Nat) (Rb : Nat → Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → Nat → EF → EF → Nat → Wv) (NS1 : Nat → Nat) (NS2 : Nat → Nat) (NS3 : Nat → Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : Nat → List (List (List F)) → Nat → Nat) (Com2 : Nat → List (List (List F)) → Nat → Nat) (Com3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → Nat) (kr : Nat) (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3) {K S n : Nat}
    {ST : (T → Nat) → Nat} (hST : Lin ST) {SC : (C → Nat) → Nat}
    (rv : Nat → T → PowD (fun _ => Nat × Nat × Nat × (Nat → Tup)) n → U)
    (pg : Nat → T → C → PowD (fun _ => Nat × Nat × Nat × (Nat → Tup)) n → T)
    (sv : Nat → T → C → PowD (fun _ => Nat × Nat × Nat × (Nat → Tup)) n → U) (ε : Nat → Nat)
    (h : ∀ j, j < S → ZKBT ST K
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => (sudD (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) (W1 := W1) (W2 := W2) (W3 := W3) off (puzzle j) (A j) (k j) (row j) tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).sm 2) n)
      SC (rv j) (pg j) (sv j) (ε j))
    (ix : T → Nat) (hix : ∀ H, ix H < S) (E : T → Nat × U → Bool) :
    K * ST (fun H => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup))
        (fun i => (sudD (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) (W1 := W1) (W2 := W2) (W3 := W3) off (puzzle 0) (A 0) (k 0) (row 0) tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).sm 2) n (fun x => indB (E H (ix H, rv (ix H) H x)))) ≤
      sumTo S (fun j => ST (fun H => SC (fun c => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup))
        (fun i => (sudD (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) (W1 := W1) (W2 := W2) (W3 := W3) off (puzzle 0) (A 0) (k 0) (row 0) tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).sm 2) n (fun x =>
        indB (E (pg j H c x) (j, sv j H c x) && decide (ix (pg j H c x) = j)))))) + sumTo S ε := by
  have e : ∀ j, (fun i => (sudD (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) (W1 := W1) (W2 := W2) (W3 := W3) off (puzzle j) (A j) (k j) (row j) tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).sm 2) = (fun i => (sudD (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) (W1 := W1) (W2 := W2) (W3 := W3) off (puzzle 0) (A 0) (k 0) (row 0) tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).sm 2) :=
    fun j => funext fun i => sudD_sm (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) (W1 := W1) (W2 := W2) (W3 := W3) off (puzzle j) (A j) (k j) (row j) tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 (puzzle 0) (A 0) (k 0) (row 0) i 2
  exact zkbT_adaptive (sm := smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => (sudD (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) (W1 := W1) (W2 := W2) (W3 := W3) off (puzzle 0) (A 0) (k 0) (row 0) tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).sm 2) n) hST (lin_smPowD (fun _ => lin_sm _ _ _ _) n) rv pg sv ε
    (fun j hj => zkbT_sm_congr (congrArg (fun f => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) f n) (e j)) (h j hj))
    ix hix E

end Circuit
