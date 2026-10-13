import Ski.ZK.SpongeIndex
import Ski.ZK.SudChallenger

/-!
# Composites averaged over the permutation

`SpongeIndex` gives `SudChallenger`'s spread hypotheses at each
permutation table `H`, with that table's `δsP H = δ0 (1 + pairsAll H)`.
Here the composite runs under a uniform permutation.

- **Averaging.** `ZKBT` at each table `P < M`, with common draws,
  challenges and `K`, sums to `ZKBT` over the pairs `(P, H)` weighted by
  `w P`, the distinguisher reading `P`; the error is the weighted sum of
  the tables' errors (`zkbT_avg`).  `errPowD` is linear in its errors
  (`errPowD_avg`).
- **The Sudoku composite.** `sud_interleaveS`, its fourth table's index the
  overwrite sponge's state under `P` (`spongeφ`), holds at every
  permutation table with `δsP P` (`sponge_hsp`).  The draws, `NS`, `NR` and
  `ε` do not read the index, so the tables share them, and the composite
  holds averaged over the permutation tables, its error the
  permutation-weighted sum of the tables' errors (`sud_interleaveP`).
  `sponge_δs_countP` bounds the weighted sum of `δsP`.

Limits, from `SpongeIndex`: the bound on `δsP` says something only while
`n1²` and the later block lists stay well below the capacity, which
Plonky3's widths exceed; the state before the first commitment is fixed;
the first commitment fills one aligned block.  The fourth table `H4` stays
independent of the permutation, as in `SudChallenger`; Plonky3 squeezes the
challenge from the same permutation.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **Per-table bounds sum to an averaged bound**: `ZKBT` at each of the
    tables `P < M`, with common draws, challenges and `K`, gives `ZKBT` over
    the pairs `(P, H)` weighted by `w P`, the distinguisher reading `P`, its
    error the weighted sum of the tables' errors. -/
theorem zkbT_avg {T X C V : Type} {K M : Nat} (w : Nat → Nat) (ST : (T → Nat) → Nat) (sm : (X → Nat) → Nat)
    (SC : (C → Nat) → Nat) (rv : Nat → T → X → V) (pg : Nat → T → C → X → T) (sv : Nat → T → C → X → V)
    (ε : Nat → Nat) (h : ∀ P, P < M → ZKBT ST K sm SC (rv P) (pg P) (sv P) (ε P)) :
    ZKBT (fun f : Nat × T → Nat => sumTo M (fun P => w P * ST (fun H => f (P, H)))) K sm SC
      (fun PH x => rv PH.1 PH.2 x) (fun PH c x => (PH.1, pg PH.1 PH.2 c x)) (fun PH c x => sv PH.1 PH.2 c x)
      (sumTo M (fun P => w P * ε P)) := by
  intro E
  show K * sumTo M (fun P => w P * ST (fun H => sm (fun x => indB (E (P, H) (rv P H x))))) ≤
    sumTo M (fun P => w P * ST (fun H => SC (fun c => sm (fun x => indB (E (P, pg P H c x) (sv P H c x)))))) +
      sumTo M (fun P => w P * ε P)
  rw [sumTo_mul, ← sumTo_add]
  refine sumTo_mono _ (fun P hP => ?_)
  rw [Nat.mul_left_comm, ← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (h P hP (fun H v => E (P, H) v))

/-- **The interleaved error is linear in its errors**: weighted over the
    tables, `errPowD` with each table's `δ P` is `errPowD` with the
    weighted `δ` and the errors `ε` times the total weight. -/
theorem errPowD_avg {X C : Nat → Type} (Kf : Nat → Nat) (sm : (i : Nat) → (X i → Nat) → Nat)
    (sc : (i : Nat) → (C i → Nat) → Nat) (ε : Nat → Nat) (M : Nat) (w : Nat → Nat) (δ : Nat → Nat → Nat) :
    ∀ n, sumTo M (fun P => w P * errPowD Kf sm sc ε (δ P) n) =
      errPowD Kf sm sc (fun i => sumTo M w * ε i) (fun i => sumTo M (fun P => w P * δ P i)) n
  | 0 => by
    show sumTo M (fun P => w P * 0) = 0
    rw [sumTo_congr _ (fun P _ => Nat.mul_zero (w P)), sumTo_const, Nat.mul_zero]
  | n + 1 => by
    have ih := errPowD_avg Kf sm sc ε M w δ n
    show sumTo M (fun P => w P * (KPowD Kf n * (ε n * smPowD sm n (fun _ => 1)) +
        errPowD Kf sm sc ε (δ P) n * sc n (fun _ => sm n (fun _ => 1)) + KPowD Kf n * δ P n)) =
      KPowD Kf n * ((sumTo M w * ε n) * smPowD sm n (fun _ => 1)) +
        errPowD Kf sm sc (fun i => sumTo M w * ε i) (fun i => sumTo M (fun P => w P * δ P i)) n *
          sc n (fun _ => sm n (fun _ => 1)) + KPowD Kf n * sumTo M (fun P => w P * δ P n)
    generalize KPowD Kf n = A at *
    generalize smPowD sm n (fun _ => 1) = S at *
    generalize sc n (fun _ => sm n (fun _ => 1)) = B at *
    rw [← ih]
    have e : ∀ P, w P * (A * (ε n * S) + errPowD Kf sm sc ε (δ P) n * B + A * δ P n) =
        (A * (ε n * S)) * w P + B * (w P * errPowD Kf sm sc ε (δ P) n) + A * (w P * δ P n) := fun P => by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm (w P) (A * (ε n * S)), Nat.mul_left_comm (w P) A,
        Nat.mul_comm (errPowD Kf sm sc ε (δ P) n) B, Nat.mul_left_comm (w P) B]
    rw [sumTo_congr _ (fun P _ => e P), sumTo_add, sumTo_add, ← sumTo_mul, ← sumTo_mul, ← sumTo_mul]
    rw [Nat.mul_comm B, Nat.mul_assoc A, Nat.mul_comm (ε n * S), ← Nat.mul_assoc (sumTo M w)]

/-- The fourth table's index under the permutation `H`: the overwrite
    sponge's state after the first commitment `m % n1` and the later blocks
    `enc (m / n1) w`, the same for every proof `ix`. -/
def spongeφ {W : Type} (Kp : Nat) (inner : Nat → Nat → Nat) (iv n1 L : Nat) (enc : Nat → W → List Nat) (H : Nat) :
    Nat → Nat → W → Nat :=
  fun _ m w => chain1 Kp inner iv ((m % n1) :: enc (m / n1) w) H (L + 1)

/-- The spread the permutation `H` gives proof `ix`: `δ0 ix (1 + pairsAll)`. -/
def δsP (Kp : Nat) (inner : Nat → Nat → Nat) (iv n1 X L : Nat) (δ0 : Nat → Nat) (H ix : Nat) : Nat :=
  δ0 ix * (1 + pairsAll Kp inner iv n1 X L H)

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_interleaveS` averaged over a uniform permutation**: the fourth
    table's index the overwrite sponge's state under the permutation `P`
    (`spongeφ`), `P` ranging over the permutation tables and read by the
    distinguisher; the error the permutation-weighted sum of each table's
    `sud_interleaveS` error at that table's `δsP` (`sponge_hsp`,
    `zkbT_avg`). -/
theorem sud_interleaveP {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (iv : Nat) {X L : Nat} (hX : 0 < X)
    (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X) (δ0 : Nat → Nat)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n, ZKBT (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) *
        (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H))))
      (KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
      (fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x)
      (fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x))
      (fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x)
      (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsP Kp inner iv n1 X L δ0 P n))))))) n))) := by
  intro n
  exact zkbT_avg (fun P => indB (permB Kp P)) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
    (fun P => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n)) (fun P => (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n)) (fun P => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n))
    (fun P => (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (spongeφ Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsP Kp inner iv n1 X L δ0 P n))))))) n)) (fun P _ =>
    sud_interleaveS φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp
      hK2 hK4 (spongeφ Kp inner iv n1 L enc P) (fun _ _ _ => rget_lt hKp _ _) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
      Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 (δsP Kp inner iv n1 X L δ0 P)
      (fun ix => (sponge_hsp hX inner iv enc henc (Com1 ix) (hr1 ix) (hsp1 ix) P).1)
      (fun ix => (sponge_hsp hX inner iv enc henc (Com1 ix) (hr1 ix) (hsp1 ix) P).2) isQ nxtQ n)

end

end Circuit
