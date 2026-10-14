import Ski.ZK.SpongeProgramN
import Ski.ZK.SpongeAlign
import Ski.ZK.SudEndToEnd

/-!
# `n` Sudoku proofs with their fourth challenges squeezed from the permutation

`zk_squeezeN` reads each fourth challenge at a squeeze position, the input
of the permutation's last call, and needs the fourth table's answers to be
full states.  `sud_interleaveLG` reads `H4` at the state after that call
(`loadφG`).  Here the composite is restated and `zk_squeezeN` applied.

- **The squeeze position.** `loadφG` is the permutation's answer at
  `loadψG` (`loadφG_eq`); an equal position gives an equal state, so the
  position spreads as the state does (`loadGψ_hsp`), and the composite
  holds with `H4` read at the squeeze position (`sud_interleaveLGψ`).
- **The chains as runs.** A chain absorbing blocks from `z` is the `runAdp`
  run whose next position is `nxtBl` (`posT_nxtBl`, `chain1_app`), so
  `loadψG` is the squeeze position of the run over the prefix and the
  commitment's blocks after `|pre0| + 1 + L` queries (`loadψG_posT`).
- **The view.** With no query phases, no table-reading openings
  (`kr = 0`), the fourth table's answers full states (`K4 = Kp`) and the
  chains absorbing the commitments alone (`encC`), the composite's view
  reads the permutation only through the runs and `H4` only at their
  squeeze positions (`sud_rv_local`), and a distinguisher recovers the
  positions from it (`sud_hpr`).
- **The result.** `sud_squeezeN`: the composite's bound, through
  `hypN_of_zkbT` and `zk_squeezeN`, with each proof's fourth challenge
  read from the permutation at its run's squeeze position; the simulated
  distinguisher sees the permutation with its answers at the simulated
  positions exchanged for the programmed table's.  The error is the
  composite's plus the runs' exchanges and collisions.
  `sud_squeezeN_sat08` meets at 0.8's sponge the hypotheses this file adds
  or changes in form (`hF`, `hκin`, `henc`, `hB4`, and the openings at
  `kr = 0`), with the sponge's others.

Limits.  The composite's index absorbs the opened values computed with the
fourth challenge set to `0` (`ozF (rvF 0 …)`).  The view shows the values
at the real challenge's query sets, so it does not determine those, and
the chains here absorb the commitments alone, where Plonky3 absorbs the
opened values before the fourth challenge.  Query phases are dropped: the
distinguisher reads the whole permutation anyway.  The first three
challenges still read tables independent of the permutation.  The spread
bound still assumes absorptions only.  No witness meets every hypothesis
of `sud_interleaveLG` together; the Sudoku run's are left as the theorem
states them.  `sud_squeezeN` carries `sud_interleaveLG`'s sponge hypotheses
`hd`, `hdxC`, `hpk2`, `hκ` and `ht`, which its proof does not use.  The
simulator (`pgJ`, `sv`) reads the whole permutation table, as a
programming simulator that samples the permutation may.
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


/-! ### Views of `n` proofs, componentwise -/

/-- Component `i` of `n` draws of one type, or `d`. -/
def xAt {Xt : Type} (d : Xt) : (n : Nat) → PowD (fun _ => Xt) n → Nat → Xt
  | 0, _, _ => d
  | n + 1, x, i => if i = n then x.1 else xAt d n x.2 i

/-- **Views of `n` proofs agree when each component does.** -/
theorem rvPowD_congr {T T' Xt : Type} {V : Nat → Type} (d : Xt) (rv : (i : Nat) → T → Xt → V i)
    (rv' : (i : Nat) → T' → Xt → V i) (H : T) (H' : T') :
    ∀ (n : Nat) (x : PowD (fun _ => Xt) n), (∀ i, i < n → rv i H (xAt d n x i) = rv' i H' (xAt d n x i)) →
      rvPowD (X := fun _ => Xt) rv n H x = rvPowD (X := fun _ => Xt) rv' n H' x
  | 0, _, _ => rfl
  | n + 1, x, h => by
    show (rv n H x.1, rvPowD (X := fun _ => Xt) rv n H x.2) = (rv' n H' x.1, rvPowD (X := fun _ => Xt) rv' n H' x.2)
    have h0 := h n (Nat.lt_succ_self n)
    rw [show xAt d (n + 1) x n = x.1 from if_pos rfl] at h0
    rw [h0, rvPowD_congr d rv rv' H H' n x.2 (fun i hi => by
      have := h i (Nat.lt_succ_of_lt hi)
      rwa [show xAt d (n + 1) x i = xAt d n x.2 i from if_neg (Nat.ne_of_lt hi)] at this)]

/-- **`read4T` agrees when the fourth challenge does**: equal first three
    tables, an output that does not read the tables, and equal answers at
    the two indexes. -/
theorem read4T_congr {X O : Type} {K1 K2 K3 K4 : Nat} (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat)
    (q q' : Nat → Nat → Nat → X → Nat) (out out' : Nat × Nat × Nat × Nat → Nat → Nat → Nat → Nat → X → O)
    (H H' : Nat × Nat × Nat × Nat) (x : X) (h1 : H.1 = H'.1) (h2 : H.2.1 = H'.2.1) (h3 : H.2.2.1 = H'.2.2.1)
    (hout : out H = out' H')
    (h4 : rget K4 (q (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1)
        (rget K3 (m3 (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1) x) H.2.2.1) x) H.2.2.2 =
      rget K4 (q' (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1)
        (rget K3 (m3 (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1) x) H.2.2.1) x) H'.2.2.2) :
    read4T K1 K2 K3 K4 m1 m2 m3 q out H x = read4T K1 K2 K3 K4 m1 m2 m3 q' out' H' x := by
  unfold read4T
  rw [← h1, ← h2, ← h3, ← h4, ← hout]

/-- Proof `i`'s squeeze position read off the runs, newest first. -/
def posOf (nxt : Nat → List Nat → Nat) (c : List (List (Nat × Nat))) (i : Nat) : Nat :=
  (sqOf nxt c).getD (c.length - 1 - i) 0

theorem posOf_runsN (K : Nat) (nxt : Nat → List Nat → Nat) (k P : Nat) :
    ∀ n i, i < n → posOf nxt (runsN K nxt k P n) i = posT K (nxt i) P k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    unfold posOf
    rw [runsN_length]
    show (nxt (runsN K nxt k P n).length ((runAdp K (nxt n) P k).map Prod.snd) :: sqOf nxt (runsN K nxt k P n)).getD
      (n + 1 - 1 - i) 0 = _
    rcases Nat.lt_or_ge i n with hi | hi
    · have e : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
      rw [e]
      show (sqOf nxt (runsN K nxt k P n)).getD (n - 1 - i) 0 = _
      have := posOf_runsN K nxt k P n i hi
      unfold posOf at this; rwa [runsN_length] at this
    · have e1 : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hi
      subst e1
      rw [show i + 1 - 1 - i = 0 by omega, runsN_length]; rfl

theorem posT_mem_sqOf (K : Nat) (nxt : Nat → List Nat → Nat) (k P : Nat) :
    ∀ n i, i < n → posT K (nxt i) P k ∈ sqOf nxt (runsN K nxt k P n)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    show posT K (nxt i) P k ∈ nxt (runsN K nxt k P n).length ((runAdp K (nxt n) P k).map Prod.snd) ::
      sqOf nxt (runsN K nxt k P n)
    rcases Nat.lt_or_ge i n with hi | hi
    · exact List.mem_cons_of_mem _ (posT_mem_sqOf K nxt k P n i hi)
    · have e1 : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hi
      subst e1
      rw [runsN_length]; exact List.mem_cons_self

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



/-! ### Positions read off a view -/

/-- `f (n-1), …, f 0`. -/
def listN (f : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => f n :: listN f n

theorem listN_congr {f f' : Nat → Nat} : ∀ n, (∀ i, i < n → f i = f' i) → listN f n = listN f' n
  | 0, _ => rfl
  | n + 1, h => by
    show f n :: listN f n = f' n :: listN f' n
    rw [h n (Nat.lt_succ_self n), listN_congr n (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem sqOf_runsN (K : Nat) (nxt : Nat → List Nat → Nat) (k P : Nat) :
    ∀ n, sqOf nxt (runsN K nxt k P n) = listN (fun i => posT K (nxt i) P k) n
  | 0 => rfl
  | n + 1 => by
    show nxt (runsN K nxt k P n).length ((runAdp K (nxt n) P k).map Prod.snd) :: sqOf nxt (runsN K nxt k P n) =
      posT K (nxt n) P k :: listN (fun i => posT K (nxt i) P k) n
    rw [runsN_length, sqOf_runsN K nxt k P n]; rfl

/-- The fourth indexes a distinguisher computes from `n` proofs' views, the
    index of proof `i` from its third message `idx i m3`. -/
def posV {O : Type} (idx : Nat → Nat → Nat) : (n : Nat) → PowD (fun _ => Option (Nat × Nat × Nat × O) × List Nat) n → List Nat
  | 0, _ => []
  | n + 1, v => (match v.1.1 with | some y => idx n y.2.2.1 | none => 0) :: posV idx n v.2

theorem posV_rvPowD {T Xt O : Type} (d : Xt) (idx : Nat → Nat → Nat)
    (rv : (i : Nat) → T → Xt → Option (Nat × Nat × Nat × O) × List Nat) (H : T) :
    ∀ n (x : PowD (fun _ => Xt) n),
      posV idx n (rvPowD (X := fun _ => Xt) rv n H x) =
        listN (fun i => match (rv i H (xAt d n x i)).1 with | some y => idx i y.2.2.1 | none => 0) n
  | 0, _ => rfl
  | n + 1, x => by
    show (match (rv n H x.1).1 with | some y => idx n y.2.2.1 | none => 0) ::
        posV idx n (rvPowD (X := fun _ => Xt) rv n H x.2) = _ :: _
    rw [posV_rvPowD d idx rv H n x.2]
    congr 1
    · show _ = (match (rv n H (xAt d (n + 1) x n)).1 with | some y => idx n y.2.2.1 | none => 0)
      rw [show xAt d (n + 1) x n = x.1 from if_pos rfl]
    · exact listN_congr n (fun i hi => by rw [show xAt d (n + 1) x i = xAt d n x.2 i from if_neg (Nat.ne_of_lt hi)])

/-! ### The restated composite's view reads `H4` only at the squeeze positions -/

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

/-- The draw type of one Sudoku proof. -/
abbrev XSud : Type := Nat × Nat × Nat × (Nat → Tup)

/-- The type the fourth index's transcript argument ranges over. -/
abbrev WSud : Type := Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF)))

/-- A default draw. -/
def xSud0 : XSud := (0, 0, 0, fun _ => Tup.dec 0)

variable {V Wv P1 P2 P3 W1 W2 W3 : Type} (off : EF → String → EF) (puzzle : Nat → List Nat) (A : Nat → List Cell)
  (k : Nat → Nat) (row : Nat → Nat → Air.Row) (tP : Nat → Nat) (S16 S10 SP : Nat → Nat → List F)
  (qv : Nat → EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : Nat → Nat → List (EF → EF → List F))
  (K2 Kp : Nat) (ncw : Nat → Nat) (αd : Nat → Nat → EF) (B4 : Nat → Nat) (fri : Nat → Nat → EF → EF → List (EF → EF) → V)
  (NR2 : Nat → Nat) (Rb : Nat → Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → Nat → EF → EF → Nat → Wv)
  (NS1 NS2 NS3 : Nat → Nat) (n1 n2 n3 : Nat) (Com1 : Nat → List (List (List F)) → Nat → Nat)
  (Com2 : Nat → List (List (List F)) → Nat → Nat) (Com3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → Nat)
  (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1)
  (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat)
  (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2)
  (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3)
  (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
  (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat) (G L : Nat) (encC : Nat → List Nat)

/-- Proof `i`'s third message, from the first three tables and the draws;
    no table-reading openings (`kr = 0`), the fourth table a full state. -/
def sudM3At (n : Nat) (H : Nat × Nat × Nat) (x : PowD (fun _ => XSud) n) (i : Nat) : Nat :=
  (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
    n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m3
    (rget (Q4 * Q4) ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro
      NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m1 (xAt xSud0 n x i)) H.1)
    (rget K2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro
      NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m2
      (rget (Q4 * Q4) ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb
        Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m1 (xAt xSud0 n x i)) H.1)
      (xAt xSud0 n x i)) H.2.1)
    (xAt xSud0 n x i)

/-- Proof `i`'s sponge run: the prefix, its third message's blocks, the
    encoding of the commitments alone. -/
def sudNxtI (n : Nat) (H : Nat × Nat × Nat) (x : PowD (fun _ => XSud) n) (i : Nat) : List Nat → Nat :=
  nxtBl inner z (blocksG pre0 blk bf G n1 (fun r (_ : WSud) => encC r)
    (sudM3At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
      Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i) none)

/-- **The restated view**: the composite's view with each proof's fourth
    index its run's squeeze position and the fourth table answering `g`. -/
def sudRvS (n : Nat) (c : List (List (Nat × Nat))) (H : Nat × Nat × Nat) (x : PowD (fun _ => XSud) n) (g : Nat → Nat) :=
  rvPowD (X := fun _ => XSud) (mixRv (Q4 * Q4) K2 Q4 Kp 0 (fun _ => false) (fun _ _ => (0, 0, ()))
    (fun i => read4T (Q4 * Q4) K2 Q4 Kp
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
        (fun ix _ _ => posOf (sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1
          NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x) c ix)
        Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m1
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
        n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m2
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
        n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m3
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
        (fun ix _ _ => posOf (sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1
          NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x) c ix)
        Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).q
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
        n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).out))
    n (H.1, H.2.1, H.2.2, tab Kp g Kp) x

theorem getAt_lt {K : Nat} (hK : 0 < K) : ∀ (ps as : List Nat), (∀ a ∈ as, a < K) → ∀ v, getAt ps as v < K
  | [], _, _, _ => hK
  | _ :: _, [], _, _ => hK
  | p :: ps, a :: as, h, v => by
    show (if v = p then a else getAt ps as v) < K
    split
    · exact h a List.mem_cons_self
    · exact getAt_lt hK ps as (fun b hb => h b (List.mem_cons_of_mem _ hb)) v

/-- **The composite's view reads the permutation only through the runs and
    `H4` only at their squeeze positions**: with no query phases, no
    table-reading openings, the fourth table a full state and an encoding
    of the commitments alone, the view at `(P, H, H4)` is `sudRvS` at the
    runs and the lookup of `H4` at the distinct squeeze positions. -/
theorem sud_rv_local (hKp : 0 < Kp) (hin : ∀ s x, inner s x < Kp) (n P : Nat) (H : Nat × Nat × Nat) (H4 : Nat)
    (x : PowD (fun _ => XSud) n) :
    rvPowD (X := fun _ => XSud) (mixRv (Q4 * Q4) K2 Q4 Kp 0 (fun _ => false) (fun _ _ => (0, 0, ()))
      (fun i => read4T (Q4 * Q4) K2 Q4 Kp
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out))
      n (H.1, H.2.1, H.2.2, H4) x =
    sudRvS off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3
      φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n
      (runsN Kp (sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3
        Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x) (pre0.length + 1 + L) P n) H x
      (getAt (dedupL (sqOf (sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x)
          (runsN Kp (sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2
            n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x) (pre0.length + 1 + L) P n)))
        ((dedupL (sqOf (sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x)
          (runsN Kp (sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2
            n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x) (pre0.length + 1 + L) P n))).map
          (fun v => rget Kp v H4))) := by
  let nx := sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3
    Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x
  let kk := pre0.length + 1 + L
  let ps := dedupL (sqOf nx (runsN Kp nx kk P n))
  let g := getAt ps (ps.map (fun v => rget Kp v H4))
  refine rvPowD_congr xSud0 _ _ _ _ n x (fun i hi => ?_)
  refine congrArg (fun y => (some y, ([] : List Nat))) ?_
  refine read4T_congr _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl ?_
  -- the index is proof `i`'s squeeze position
  have hq : loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P i
      (sudM3At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
        Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i) none = posT Kp (nx i) P kk :=
    loadψG_posT Kp inner z pre0 blk bf G n1 L _ P i _ none
  have hpos : posOf nx (runsN Kp nx kk P n) i = posT Kp (nx i) P kk := posOf_runsN Kp nx kk P n i hi
  have hmem : posT Kp (nx i) P kk ∈ ps := (mem_dedupL _).2 (posT_mem_sqOf Kp nx kk P n i hi)
  have hlt : posT Kp (nx i) P kk < Kp := hin _ _
  have hg : ∀ m, m < Kp → g m < Kp := fun m _ => getAt_lt hKp ps _ (fun a ha => by
    obtain ⟨v, _, e⟩ := List.mem_map.1 ha; rw [← e]; exact rget_lt hKp _ _) m
  show rget Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P i
      (sudM3At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
        Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i) none) H4 =
    rget Kp (posOf nx (runsN Kp nx kk P n) i) (tab Kp g Kp)
  rw [hq, hpos, rget_tab hKp Kp g hg _ hlt]
  exact (getAt_map (fun v => rget Kp v H4) ps hmem).symm


/-- **The distinguisher finds the squeeze positions from the restated
    view**: each proof's third message is in its view, and its run is the
    chain over that message's blocks under `P`. -/
theorem sud_hpr (n P : Nat) (H : Nat × Nat × Nat) (x : PowD (fun _ => XSud) n) (c : List (List (Nat × Nat)))
    (g : Nat → Nat) :
    dedupL (posV (fun i m => loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P i m none) n
      (sudRvS off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
        Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n c H x g)) =
    dedupL (sqOf (sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3
        Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x)
      (runsN Kp (sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3
        Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x) (pre0.length + 1 + L) P n)) := by
  congr 1
  unfold sudRvS
  rw [posV_rvPowD xSud0, sqOf_runsN]
  exact listN_congr n (fun i _ => loadψG_posT Kp inner z pre0 blk bf G n1 L _ P i _ none)

end


/-! ### The Sudoku proofs' fourth challenges squeezed from the permutation -/

theorem lin_sum3 (A1 A2 A3 : Nat) : Lin (fun (f : Nat × Nat × Nat → Nat) =>
    sumTo A1 (fun H1 => sumTo A2 (fun H2 => sumTo A3 (fun H3 => f (H1, H2, H3))))) := fun N f => by
  show sumTo A1 (fun H1 => sumTo A2 (fun H2 => sumTo A3 (fun H3 => sumTo N (fun i => f i (H1, H2, H3))))) =
    sumTo N (fun i => sumTo A1 (fun H1 => sumTo A2 (fun H2 => sumTo A3 (fun H3 => f i (H1, H2, H3)))))
  rw [sumTo_congr A1 (fun H1 _ => sumTo_congr A2 (fun H2 _ => sumTo_exch (fun H3 i => f i (H1, H2, H3)) N A3)),
    sumTo_congr A1 (fun H1 _ => sumTo_exch (fun H2 i => sumTo A3 (fun H3 => f i (H1, H2, H3))) N A2)]
  exact sumTo_exch (fun H1 i => sumTo A2 (fun H2 => sumTo A3 (fun H3 => f i (H1, H2, H3)))) N A1

theorem lin_sum4c (A1 A2 A3 A4 : Nat) : Lin (fun (f : Nat × Nat × Nat × Nat → Nat) =>
    sumTo A4 (fun c4 => sumTo A1 (fun c1 => sumTo A2 (fun c2 => sumTo A3 (fun c3 => f (c1, c2, c3, c4)))))) := fun N f => by
  show sumTo A4 (fun c4 => sumTo A1 (fun c1 => sumTo A2 (fun c2 => sumTo A3 (fun c3 => sumTo N (fun i => f i (c1, c2, c3, c4)))))) =
    sumTo N (fun i => sumTo A4 (fun c4 => sumTo A1 (fun c1 => sumTo A2 (fun c2 => sumTo A3 (fun c3 => f i (c1, c2, c3, c4))))))
  rw [sumTo_congr A4 (fun c4 _ => sumTo_congr A1 (fun c1 _ => sumTo_congr A2 (fun c2 _ =>
      sumTo_exch (fun c3 i => f i (c1, c2, c3, c4)) N A3))),
    sumTo_congr A4 (fun c4 _ => sumTo_congr A1 (fun c1 _ =>
      sumTo_exch (fun c2 i => sumTo A3 (fun c3 => f i (c1, c2, c3, c4))) N A2)),
    sumTo_congr A4 (fun c4 _ => sumTo_exch (fun c1 i => sumTo A2 (fun c2 => sumTo A3 (fun c3 => f i (c1, c2, c3, c4)))) N A1)]
  exact sumTo_exch (fun c4 i => sumTo A1 (fun c1 => sumTo A2 (fun c2 => sumTo A3 (fun c3 => f i (c1, c2, c3, c4))))) N A4

theorem lin_scPowD {C : Nat → Type} {sc : (i : Nat) → (C i → Nat) → Nat} (h : ∀ i, Lin (sc i)) :
    ∀ n, Lin (scPowD sc n)
  | 0 => fun _ _ => rfl
  | n + 1 => fun N f => by
    show sc n (fun c => scPowD sc n (fun rest => sumTo N (fun i => f i (c, rest)))) =
      sumTo N (fun i => sc n (fun c => scPowD sc n (fun rest => f i (c, rest))))
    rw [← h n N]
    exact congrArg (sc n) (funext fun c => lin_scPowD h n N (fun i rest => f i (c, rest)))

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- **`n` interleaved Sudoku proofs with their fourth challenges squeezed
    from the permutation.**  `sud_interleaveLGψ` with no query phases, no
    table-reading openings, the fourth table's answers full states
    (`K4 = Kp`) and the chains absorbing the commitments alone (`encC`),
    through `hypN_of_zkbT` (`sud_rv_local`, `sud_hpr`) and `zk_squeezeN`:
    the real view reads each proof's fourth challenge from the permutation
    at its run's squeeze position, and the simulated distinguisher sees the
    permutation with its answers at the simulated positions exchanged for
    the programmed table's.  The error is the composite's plus the runs'
    exchanges and collisions. -/
theorem sud_squeezeN {V Wv P1 P2 P3 W1 W2 W3 : Type} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 Kp : Nat} (hK2 : 0 < K2) (hKp : 0 < Kp) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo Kp (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 Kp n1 0 (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 Kp n1 0 (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 Kp n1 0 (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat)
    {G N0 N : Nat} (hG : 0 < G) (hN : 0 < N) (hn : n1 = G * N0) (hbf : ∀ h, h < N0 → bf h < N)
    (hinj : ∀ h h', h < N0 → h' < N0 → bf h = bf h' → h = h')
    (hd : ∀ iv a b, a < N → b < N → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ iv s s' x c c', c < N → c' < N → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {X : Nat} (hX : 0 < X) (L : Nat) (encC : Nat → List Nat) (henc : ∀ r i, i < L → (encC r).getD i 0 < X)
    (δ0 : Nat → Nat)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    {Fκ : Nat} (hF : ∀ v, sumTo Kp (fun u => indB (decide (κ u = v))) ≤ Fκ)
    (hκin : ∀ s x, κ (inner s x) = κ s) (n : Nat) 
    (E : Nat → Nat × Nat × Nat →
      PowD (fun _ => Option (Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF)) × List Nat) n →
      Bool) :
    let sD := fun (Pφ : Nat → Nat → WSud → Nat) => sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp Pφ Kp ncw αd B4
      fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3
    let ψ := fun P => loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P
    let kk := pre0.length + 1 + L
    let K4w := KPowD (fun _ => Kp * (Q4 * Q4 * (K2 * Q4))) n
    let ST := fun (f : Nat × Nat × Nat → Nat) => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3))))
    let sm := smPowD (X := fun _ => XSud) (fun i => (sD (ψ 0) i).sm 2) n
    let SC := scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) =>
      sumTo Kp (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n
    let nxtI := fun H x => sudNxtI off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n H x
    let rv := fun c H x g => sudRvS off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encC n c H x g
    let pgF := fun (P : Nat) (H : Nat × Nat × Nat) (H4 : Nat) (c : PowD (fun _ => Nat × Nat × Nat × Nat) n)
        (x : PowD (fun _ => XSud) n) =>
      pgPowD (X := fun _ => XSud) (C := fun _ => Nat × Nat × Nat × Nat)
        (pgRd (Q4 * Q4) K2 Q4 Kp (fun i => !(fun _ => false) i) (fun i => (sD (ψ P) i).pts) (fun _ c => c)) n
        (H.1, H.2.1, H.2.2, H4) c x
    let pgJ := fun P H H4 c x => (((pgF P H H4 c x).1, (pgF P H H4 c x).2.1, (pgF P H H4 c x).2.2.1), (pgF P H H4 c x).2.2.2)
    let sv := fun (P : Nat) (H : Nat × Nat × Nat) (H4 : Nat) (c : PowD (fun _ => Nat × Nat × Nat × Nat) n)
        (x : PowD (fun _ => XSud) n) =>
      svPowDT (X := fun _ => XSud) (C := fun _ => Nat × Nat × Nat × Nat)
        (pgRd (Q4 * Q4) K2 Q4 Kp (fun i => !(fun _ => false) i) (fun i => (sD (ψ P) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 Kp 0 (fun _ => false) (fun _ _ => (0, 0, ())) (fun i => (sD (ψ P) i).sv)) n
        (H.1, H.2.1, H.2.2, H4) c x
    let pos := fun P (_ : Nat × Nat × Nat) v => dedupL (posV (fun i m => ψ P i m none) n v)
    let ε := (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (errPowD (fun _ => (Kp * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo Kp (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond ((fun _ => false) i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo Kp (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (Kp ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond ((fun _ => false) i) 0 (4 + 3 * 0)) n *
            cond ((fun _ => false) n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (_ : WSud) => encC r) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsG Kp inner z pre0 blk G N X L t s0 δ0 P n))))))) n)))
    (Kp - n * kk) * (K4w * (Kp ^ Kp * ST (fun H => sm (fun x => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P &&
        E P H (rv (runsN Kp (nxtI H x) kk P n) H x
          (getAt (dedupL (sqOf (nxtI H x) (runsN Kp (nxtI H x) kk P n)))
            ((dedupL (sqOf (nxtI H x) (runsN Kp (nxtI H x) kk P n))).map (fun v => rget Kp v P)))))))))) ≤
      (Kp - n * kk) * (ST (fun H => SC (fun c => sm (fun x => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) *
        sumTo (Kp ^ Kp) (fun H4 => indB (E (progL Kp (pos P (pgJ P H H4 c x).1 (sv P H H4 c x)) (pgJ P H H4 c x).2 P)
          (pgJ P H H4 c x).1 (sv P H H4 c x))))))) + ε) +
      K4w * (Kp ^ (Kp - 1) * (ST (fun _ => sm (fun _ => 1)) *
        (((Kp - n * kk) * (n * (n * kk + n)) + Kp * n * ((sumTo (n * kk) (fun j => j) + n * kk * n) * Fκ)) *
          sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) := by
  intro sD ψ kk K4w ST sm SC nxtI rv pgF pgJ sv pos ε
  have hcomp := sud_interleaveLGψ (kr := 0) (kq := 0) (K4 := Kp) φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp
    S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hKp hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
    Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 hKp inner hin κ hκ hpk2 z pre0 blk bf hG hN hn hbf hinj
    hd hdxC hX L (fun r _ => encC r) (fun r _ i hi => henc r i hi) δ0 hsp1 ht hs0 (fun _ => false) (fun _ _ => (0, 0, ())) n
  have hST : Lin ST := lin_sum3 _ _ _
  have hsm : Lin sm := lin_smPowD (fun i => lin_sm _ _ _ _) n
  have hSC : Lin SC := lin_scPowD (fun _ => lin_sum4c _ _ _ _) n
  have hkk : 0 < kk := Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _)
  exact zk_squeezeN (K := Kp) (k := kk) (n := n) (K4w := K4w) (ε := ε) hKp hkk κ hF ST hST sm hsm SC nxtI
    (fun _ _ _ _ => hin _ _) (fun _ _ _ a l => hκin a _) rv pgJ sv pos
    (fun P H x g => sud_hpr off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G L encC n P H x _ g)
    (fun D => hypN_of_zkbT ST hST sm hsm SC hSC (fun H H4 => (H.1, H.2.1, H.2.2, H4))
      (fun TT => ((TT.1, TT.2.1, TT.2.2.1), TT.2.2.2)) (fun _ _ => rfl) _ _ _ hcomp
      (fun P H x H4 => rv (runsN Kp (nxtI H x) kk P n) H x
        (getAt (dedupL (sqOf (nxtI H x) (runsN Kp (nxtI H x) kk P n)))
          ((dedupL (sqOf (nxtI H x) (runsN Kp (nxtI H x) kk P n))).map (fun v => rget Kp v H4))))
      pgJ sv
      (fun P H H4 x => sud_rv_local off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G L encC hKp hin n P H H4 x)
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) D) E

end


/-- **The hypotheses `sud_squeezeN` adds or changes in form hold at 0.8's
    sponge**: `hF` at `F = p^R p`; absorption keeping the capacity's tail
    (`hκin`); an encoding of the commitments alone (`henc`, `encC r = []`);
    `hB4` at `K4 = Kp`, `B4 = Kp`; and the openings at `kr = 0` beside a
    salt commitment, each outputting the opened values of its challenge
    (`hp1`–`hp3` with `G c4 _ d _ _ = op c4 d`).  The sponge's others
    (`hin`, `hκ`, `hpk2`, `hd`, `hdxC`) hold as in `SpongeAlign`. -/
theorem sud_squeezeN_sat08 {R p Q : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) {D O W : Type} (NS : Nat)
    (op : Nat → D → O) (K1 K2 K3 n1 L X : Nat) (hX : 0 < X) (φ : Nat → W → Nat)
    (nx : Nat → Nat → List Nat → Nat × Nat × W) (αd : Nat → EF) :
    (∀ s x, inner08 R (p ^ R) p Q s x < p ^ R * (p * Q)) ∧ (∀ u, κ08 (p ^ R) p Q u < Q) ∧
      (∀ s s' x x', inner08 R (p ^ R) p Q s x = inner08 R (p ^ R) p Q s' x' → κ08 (p ^ R) p Q s = κ08 (p ^ R) p Q s') ∧
      (∀ iv a b, a < p ^ R → b < p ^ R → a ≠ b → inner08 R (p ^ R) p Q iv a ≠ inner08 R (p ^ R) p Q iv b) ∧
      (∀ iv s s' x c c', c < p ^ R → c' < p ^ R → inner08 R (p ^ R) p Q s x = inner08 R (p ^ R) p Q iv c →
        inner08 R (p ^ R) p Q s' x = inner08 R (p ^ R) p Q iv c' → c = c') ∧
      (∀ v, sumTo (p ^ R * (p * Q)) (fun u => indB (decide (κ08 (p ^ R) p Q u = v))) ≤ p ^ R * p) ∧
      (∀ s x, κ08 (p ^ R) p Q (inner08 R (p ^ R) p Q s x) = κ08 (p ^ R) p Q s) ∧
      (∀ (r : Nat) i, i < L → ((fun (_ : Nat) => ([] : List Nat)) r).getD i 0 < X) ∧
      (sumTo (p ^ R * (p * Q)) (fun c4 => indB (!genB (αd c4))) ≤ p ^ R * (p * Q)) ∧
      (∀ c4 T1 T2 T3 T4 M, ComPfHides NS (fun (_ : D) σ => σ % NS)
        (pfRdM K1 K2 K3 (p ^ R * (p * Q)) n1 0 φ nx (fun c4 _ d _ _ => op c4 d) c4 T1 T2 T3 T4 M) (op c4)) :=
  ⟨inner08_lt hR hp hQ, κ08_lt hQ, inner08_hpk2 hR hp, (align08_sat hR hp hp).2.2.1, (align08_sat hR hp hp).2.2.2,
    κ08_count (Nat.mul_pos (Nat.pow_pos hp) hp), κ08_inner08 hR hp, fun _ _ _ => hX,
    Nat.le_trans (sumTo_mono _ (fun _ _ => indB_le_one _)) (Nat.le_of_eq (Eq.trans (sumTo_const 1 _) (Nat.mul_one _))),
    fun c4 _ _ _ _ _ => comSalt_pf NS (op c4)⟩

end Circuit
