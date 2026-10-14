import Ski.ZK.SpongeProgramN
import Ski.ZK.SpongeAlign

/-!
# The Sudoku composite restated for a squeezed challenge

`zk_squeezeN` reads each fourth challenge at a squeeze position, the input
of the permutation's last call, and needs the fourth table's answers to be
full states.  `sud_interleaveLG` reads `H4` at the state after that call
(`loadφG`), the permutation's answer at the squeeze position.  Here the
composite is restated step by step toward `zk_squeezeN`'s hypothesis.

- **The squeeze position.** `loadφG` is the permutation's answer at
  `loadψG`, the input of the chain's last call (`loadφG_eq`).  An equal
  position gives an equal state, so `loadψG` spreads over the first salt as
  `loadφG` does (`loadGψ_hsp`), and `sud_interleaveLG` holds with `H4` read
  at the squeeze position (`sud_interleaveLGψ`).  Its `K4` is free, so
  `K4 = Kp` makes `H4`'s answers full states.

- **The chains as runs.** A chain absorbing blocks from `z` is the `runAdp`
  run whose next position is `nxtBl`: its position at time `i` is the
  chain's `i`-th input (`posT_nxtBl`), and a chain after a prefix is the
  chain over the joined blocks (`chain1_app`).  So `loadψG` is the squeeze
  position of the run over `blocksG`, the prefix and the commitment's
  blocks, after `|pre0| + 1 + L` queries (`loadψG_posT`).  With absorption
  keeping `κ`, the run meets `zk_squeezeN`'s `hκ` (`nxtBl_κ`).

A limit found on the way: the composite's index absorbs the opened values
computed with the fourth challenge set to `0` (`ozF (rvF 0 …)`), and those
depend on the challenge through its query sets.  The real view carries the
opened values at the real challenge, so a distinguisher cannot recompute
the index from it, as `zk_squeezeN` asks (`hpr`).  An instance whose
encoding `enc` absorbs the commitments alone has an index the view
determines.

Not shown yet: `H4` taken out of the other tables' count, and the view
reading `H4` through `getAt`.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The fourth table's index at the input of the chain's last call: the
    squeeze position. -/
def loadψG {W : Type} (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat)
    (G n1 L : Nat) (enc : Nat → W → List Nat) (H : Nat) : Nat → Nat → W → Nat :=
  fun _ m w => inner (chain1 K inner (ivP K inner z (pre0 ++ [blk ((m % n1) % G)]) H) (bf ((m % n1) / G) :: enc (m / n1) w) H L)
    ((bf ((m % n1) / G) :: enc (m / n1) w).getD L 0)

/-- **The state is the permutation's answer at the squeeze position.** -/
theorem loadφG_eq {W : Type} (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat)
    (G n1 L : Nat) (enc : Nat → W → List Nat) (H ix m : Nat) (w : W) :
    loadφG K inner z pre0 blk bf G n1 L enc H ix m w = rget K (loadψG K inner z pre0 blk bf G n1 L enc H ix m w) H :=
  rfl

/-- **`loadG_hsp` at the squeeze position**: an equal position gives an
    equal state, so the position spreads as the state does. -/
theorem loadGψ_hsp {D W : Type} {K NS1 n1 δs X G N0 N : Nat} (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat)
    (blk bf : Nat → Nat) (hG : 0 < G) (hN : 0 < N) (hn : n1 = G * N0) (hbf : ∀ h, h < N0 → bf h < N)
    (hinj : ∀ h h', h < N0 → h' < N0 → bf h = bf h' → h = h') (hX : 0 < X) (L t : Nat)
    (enc : Nat → W → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) {s0 : Nat} (hs0 : 2 ≤ s0) (H : Nat) :
    (∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs * loadG K inner z pre0 blk G N X L t s0 H) ∧
      (∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        (loadψG K inner z pre0 blk bf G n1 L enc H 0 (Com1 d σ1 + n1 * rest) w = v))) ≤
        δs * loadG K inner z pre0 blk G N X L t s0 H) := by
  have h := loadG_hsp (K := K) inner z pre0 blk bf hG hN hn hbf hinj hX L t enc henc Com1 hr1 hsp1 hs0 H
  refine ⟨h.1, fun d rest w v => Nat.le_trans (sumTo_mono _ (fun σ1 _ => ?_)) (h.2 d rest w (rget K v H))⟩
  by_cases e : loadψG K inner z pre0 blk bf G n1 L enc H 0 (Com1 d σ1 + n1 * rest) w = v
  · rw [decide_eq_true e, loadφG_eq, e, decide_eq_true rfl]; exact Nat.le_refl _
  · rw [decide_eq_false e]; exact Nat.zero_le _


/-! ### The chains as a run -/

theorem getD_app_left : ∀ (l l' : List Nat) (i : Nat), i < l.length → (l ++ l').getD i 0 = l.getD i 0
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: l, l', i + 1, h => getD_app_left l l' i (Nat.lt_of_succ_lt_succ h)

theorem getD_app_right : ∀ (l l' : List Nat) (j : Nat), (l ++ l').getD (l.length + j) 0 = l'.getD j 0
  | [], _, j => by rw [List.nil_append, List.length_nil, Nat.zero_add]
  | _ :: l, l', j => by
    rw [List.cons_append, List.length_cons, Nat.add_right_comm]
    exact getD_app_right l l' j

/-- A chain reads only the blocks before its step. -/
theorem chain1_app_left (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (l l' : List Nat) (H : Nat) :
    ∀ i, i ≤ l.length → chain1 K inner z (l ++ l') H i = chain1 K inner z l H i
  | 0, _ => rfl
  | i + 1, h => by
    show rget K (inner (chain1 K inner z (l ++ l') H i) ((l ++ l').getD i 0)) H =
      rget K (inner (chain1 K inner z l H i) (l.getD i 0)) H
    rw [chain1_app_left K inner z l l' H i (Nat.le_of_succ_le h), getD_app_left l l' i h]

/-- **A chain after a prefix is the chain over the joined blocks.** -/
theorem chain1_app (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (l l' : List Nat) (H : Nat) :
    ∀ j, chain1 K inner (chain1 K inner z l H l.length) l' H j = chain1 K inner z (l ++ l') H (l.length + j)
  | 0 => (chain1_app_left K inner z l l' H l.length (Nat.le_refl _)).symm
  | j + 1 => by
    show rget K (inner (chain1 K inner (chain1 K inner z l H l.length) l' H j) (l'.getD j 0)) H =
      rget K (inner (chain1 K inner z (l ++ l') H (l.length + j)) ((l ++ l').getD (l.length + j) 0)) H
    rw [chain1_app K inner z l l' H j, getD_app_right]

/-- The next position of a chain absorbing the blocks `bl` from `z`, its
    answers newest first. -/
def nxtBl (inner : Nat → Nat → Nat) (z : Nat) (bl : List Nat) (l : List Nat) : Nat :=
  inner (match l with | [] => z | a :: _ => a) (bl.getD l.length 0)

/-- **The run's position at time `i` is the chain's `i`-th input.** -/
theorem posT_nxtBl (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (bl : List Nat) (H : Nat) :
    ∀ i, posT K (nxtBl inner z bl) H i = inner (chain1 K inner z bl H i) (bl.getD i 0)
  | 0 => rfl
  | i + 1 => by
    show inner (rget K (posT K (nxtBl inner z bl) H i) H)
        (bl.getD ((runAdp K (nxtBl inner z bl) H (i + 1)).map Prod.snd).length 0) =
      inner (rget K (inner (chain1 K inner z bl H i) (bl.getD i 0)) H) (bl.getD (i + 1) 0)
    rw [posT_nxtBl K inner z bl H i, List.length_map, runAdp_length]

/-- The blocks of the first commitment's chain: the prefix, its group's
    first element, then its other elements and the transcript. -/
def blocksG {W : Type} (pre0 : List Nat) (blk bf : Nat → Nat) (G n1 : Nat) (enc : Nat → W → List Nat)
    (m : Nat) (w : W) : List Nat :=
  (pre0 ++ [blk ((m % n1) % G)]) ++ (bf ((m % n1) / G) :: enc (m / n1) w)

/-- **The squeeze position is the run's**: `loadψG` is the position after
    `|pre0| + 1 + L` queries of the chain over `blocksG`. -/
theorem loadψG_posT {W : Type} (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat)
    (G n1 L : Nat) (enc : Nat → W → List Nat) (H ix m : Nat) (w : W) :
    loadψG K inner z pre0 blk bf G n1 L enc H ix m w =
      posT K (nxtBl inner z (blocksG pre0 blk bf G n1 enc m w)) H (pre0.length + 1 + L) := by
  have hl : (pre0 ++ [blk ((m % n1) % G)]).length = pre0.length + 1 := by rw [List.length_append]; rfl
  rw [posT_nxtBl, ← hl]
  unfold blocksG
  rw [← chain1_app, getD_app_right]
  rfl

theorem nxtBl_lt {K : Nat} {inner : Nat → Nat → Nat} (hin : ∀ s x, inner s x < K) (z : Nat) (bl l : List Nat) :
    nxtBl inner z bl l < K := hin _ _

/-- With absorption keeping `κ`, the chain's next position keeps `κ` of the
    answer before it. -/
theorem nxtBl_κ {inner : Nat → Nat → Nat} {κ : Nat → Nat} (hκin : ∀ s x, κ (inner s x) = κ s) (z : Nat)
    (bl : List Nat) (a : Nat) (l : List Nat) : κ (nxtBl inner z bl (a :: l)) = κ a := hκin _ _

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_interleaveLG` with the fourth table read at the squeeze
    position** (`loadψG`), where `sud_interleaveLG` reads it at the state the
    permutation answers there; the spread as before (`loadGψ_hsp`). -/
theorem sud_interleaveLGψ {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat)
    {G N0 N : Nat} (hG : 0 < G) (hN : 0 < N) (hn : n1 = G * N0) (hbf : ∀ h, h < N0 → bf h < N)
    (hinj : ∀ h h', h < N0 → h' < N0 → bf h = bf h' → h = h')
    (hd : ∀ iv a b, a < N → b < N → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ iv s s' x c c', c < N → c' < N → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (δ0 : Nat → Nat)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n, ZKBT (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) *
        (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H))))
      (KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
      (fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x)
      (fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x))
      (fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x)
      (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsG Kp inner z pre0 blk G N X L t s0 δ0 P n))))))) n))) := by
  intro n
  exact zkbT_avgW (fun P => indB (permB Kp P)) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
    (fun P => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n)) (fun P => (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n)) (fun P => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n))
    (fun P => (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsG Kp inner z pre0 blk G N X L t s0 δ0 P n))))))) n)) (fun P _ hw =>
    sud_interleaveS φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp
      hK2 hK4 (loadψG Kp inner z pre0 blk bf G n1 L enc P) (fun _ _ _ => hin _ _) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
      Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 (δsG Kp inner z pre0 blk G N X L t s0 δ0 P)
      (fun ix => (loadGψ_hsp inner z pre0 blk bf hG hN hn hbf hinj hX L t enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).1)
      (fun ix => (loadGψ_hsp inner z pre0 blk bf hG hN hn hbf hinj hX L t enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).2) isQ nxtQ n)

end

end Circuit
