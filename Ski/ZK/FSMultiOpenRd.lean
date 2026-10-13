import Ski.ZK.FSMultiInterleave
import Ski.ZK.FSMultiOpen

/-!
# Outputs with read lists are interleaving components

`FSMultiInterleave` composes proofs and query phases in any order when each
component's view meets `hrd`: a finite list of `(table, point)` reads whose
misses leave the view unchanged.  `rd4T_hrd` gives it for outputs of
`outR4`'s shape.  Here any four-round output with an explicit read list,
taken at the challenges the view reads (`rdOutG`), meets it (`rd4G_hrd`):
the messages' four reads fix the challenges, and the output's reads at those
challenges fix the output (`hout'`, asked only at the challenges read, not
at all of them).

`FSMultiOpen`'s readers instanced so: an opening reading at transcript
points, its strategy a function of the fourth challenge and the third
message alone, as challenges drawn from earlier transcript points are (FRI's
folding challenges hash its layer roots, so they need the data-reading
openings below) (`pfRdM`, a `pfRd`, so `RdOK`, `pfRdM_ok`; its reads
`pfRdMReads`, unchanged where they miss, `pfRdM_prog`).  The Sudoku proof
with such openings then meets `hout'` (`sudFS4T_houtL`) and `hrd` with `4 +
3 kq` reads (`sudFS4T_hrd`, `sud_rd_length`), so it can be interleaved with
query phases in `zkbT_powD_rd`.  Openings whose strategy also reads their
data and salt (`pfRd`), as FRI's layer-root challenges need, are components
too: the read list names each opening's data (`sudMain1` …) and salt
(`pfRdReads`, `pfRd_progD`, `sudFS4T_houtD`, `sudFS4T_hrdD`).  The composed
theorem is `FSMultiMix`'s `fs4_interleave`.  Not shown: its spread `hsp` for
these proofs (each programmed coordinate: the first three the first
commitment's, the fourth through a digit read-back on `φ` of `hdg`'s kind);
that FRI's challenges are such a strategy (FRI's commit phase is not
modelled); the hidden-term and composed circuits.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- An output's reads at the challenges a four-round view reads from `H`. -/
def rdOutG {X : Type} (K1 K2 K3 K4 : Nat) (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat)
    (q : Nat → Nat → Nat → X → Nat)
    (rlO : Nat × Nat × Nat × Nat → Nat → Nat → Nat → Nat → X → List (Nat × Nat))
    (H : Nat × Nat × Nat × Nat) (x : X) : List (Nat × Nat) :=
  rlO H (rget K4 (q (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1)
      (rget K3 (m3 (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1) x) H.2.2.1) x) H.2.2.2)
    (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1)
    (rget K3 (m3 (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1) x) H.2.2.1) x

/-- **A four-round output with a read list meets `hrd`**: the messages'
    reads (`rd4`) and the output's reads at the challenges read
    (`rdOutG`). -/
theorem rd4G_hrd {X O : Type} {K1 K2 K3 K4 : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (q : Nat → Nat → Nat → X → Nat)
    (out : Nat × Nat × Nat × Nat → Nat → Nat → Nat → Nat → X → O)
    (rlO : Nat × Nat × Nat × Nat → Nat → Nat → Nat → Nat → X → List (Nat × Nat))
    (hout' : ∀ H p a c4 c1 c2 c3 x, a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4 →
      (rlO H c4 c1 c2 c3 x).any (fun r => decide (coord4 r.1 p = r.2)) = false →
      out (prog4 K1 K2 K3 K4 H p a) c4 c1 c2 c3 x = out H c4 c1 c2 c3 x)
    (H p a : Nat × Nat × Nat × Nat) (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (x : X)
    (hm : (rd4 K1 K2 K3 m1 m2 m3 q H x ++ rdOutG K1 K2 K3 K4 m1 m2 m3 q rlO H x).any
      (fun r => decide (coord4 r.1 p = r.2)) = false) :
    read4T K1 K2 K3 K4 m1 m2 m3 q out (prog4 K1 K2 K3 K4 H p a) x = read4T K1 K2 K3 K4 m1 m2 m3 q out H x := by
  rw [List.any_append, Bool.or_eq_false_iff] at hm
  obtain ⟨hm4, hmo⟩ := hm
  simp only [rd4, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    coord4] at hm4
  obtain ⟨n1, n2, n3, n4⟩ := hm4
  obtain ⟨b1, b2, b3, b4⟩ := ha
  have e1 : rget K1 (m1 x) (rset K1 p.1 H.1 a.1) = rget K1 (m1 x) H.1 := rget_rset_ne h1 (Ne.symm n1) b1
  have e2 : rget K2 (m2 (rget K1 (m1 x) H.1) x) (rset K2 p.2.1 H.2.1 a.2.1) =
      rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1 := rget_rset_ne h2 (Ne.symm n2) b2
  have e3 := rget_rset_ne (H := H.2.2.1) h3 (Ne.symm n3) b3
  have e4 := rget_rset_ne (H := H.2.2.2) h4 (Ne.symm n4) b4
  have ho := hout' H p a _ _ _ _ x ⟨b1, b2, b3, b4⟩ hmo
  generalize hP : prog4 K1 K2 K3 K4 H p a = P at ho
  have hP1 : P.1 = rset K1 p.1 H.1 a.1 := by rw [← hP]; rfl
  have hP2 : P.2.1 = rset K2 p.2.1 H.2.1 a.2.1 := by rw [← hP]; rfl
  have hP3 : P.2.2.1 = rset K3 p.2.2.1 H.2.2.1 a.2.2.1 := by rw [← hP]; rfl
  have hP4 : P.2.2.2 = rset K4 p.2.2.2 H.2.2.2 a.2.2.2 := by rw [← hP]; rfl
  simp only [read4T, hP1, hP2, hP3, hP4, e1, e2, e3, e4]
  rw [ho]

/-- An opening reading the tables at transcript points: `k` reads by
    `runR4` at `M % n1`, the strategy a function of the fourth challenge and
    the third message alone, as challenges drawn from earlier transcript
    points are; the result any function of the reads, the data and the
    salt. -/
def pfRdM {D P W : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → List Nat → Nat × Nat × W) (G : Nat → Nat → D → Nat → List Nat → P)
    (c4 T1 T2 T3 T4 M : Nat) (d : D) (σ : Nat) : P :=
  G c4 M d σ (runR4 K1 K2 K3 K4 n1 (M % n1) φ (nxt c4 M) (T1, T2, T3, T4) k)

/-- Its reads, `(table, point)`. -/
def pfRdMReads {W : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → W → Nat) (nxt : Nat → Nat → List Nat → Nat × Nat × W)
    (H : Nat × Nat × Nat × Nat) (c4 M : Nat) : List (Nat × Nat) :=
  (readsR4 K1 K2 K3 K4 n1 (M % n1) φ (nxt c4 M) H k).map (fun r => (r.1, pt4 n1 φ (M % n1) r))

theorem pfRdMReads_length {W : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → List Nat → Nat × Nat × W) (H : Nat × Nat × Nat × Nat) (c4 M : Nat) :
    (pfRdMReads K1 K2 K3 K4 n1 k φ nxt H c4 M).length = k := by
  unfold pfRdMReads; rw [List.length_map, readsR4_length]

/-- `pfRdM` is `pfRd` with a strategy ignoring the data and the salt. -/
theorem pfRdM_eq {D P W : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → List Nat → Nat × Nat × W) (G : Nat → Nat → D → Nat → List Nat → P) :
    pfRdM K1 K2 K3 K4 n1 k φ nxt G = pfRd K1 K2 K3 K4 n1 k φ (fun c4 M _ _ => nxt c4 M) G := rfl

/-- **`pfRdM` reads only at its digit** (`pfRd_ok`), so `FSMultiOpen`'s
    `n`-statement theorems apply to it. -/
theorem pfRdM_ok {D P W : Type} {K1 K2 K3 K4 n1 k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (dg : Nat → Nat) (φ : Nat → W → Nat) (hdg : ∀ m w, dg (φ m w) = m % n1)
    (nxt : Nat → Nat → List Nat → Nat × Nat × W) (G : Nat → Nat → D → Nat → List Nat → P) :
    RdOK K1 K2 K3 K4 n1 dg (pfRdM K1 K2 K3 K4 n1 k φ nxt G) := by
  rw [pfRdM_eq]; exact pfRd_ok h1 h2 h3 h4 dg φ hdg _ G

/-- **The opening is unchanged by a programming its reads miss.** -/
theorem pfRdM_prog {D P W : Type} {K1 K2 K3 K4 n1 k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (φ : Nat → W → Nat) (nxt : Nat → Nat → List Nat → Nat × Nat × W) (G : Nat → Nat → D → Nat → List Nat → P)
    (H p a : Nat × Nat × Nat × Nat) (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (c4 M : Nat)
    (hm : (pfRdMReads K1 K2 K3 K4 n1 k φ nxt H c4 M).any (fun r => decide (coord4 r.1 p = r.2)) = false) :
    pfRdM K1 K2 K3 K4 n1 k φ nxt G c4 (prog4 K1 K2 K3 K4 H p a).1 (prog4 K1 K2 K3 K4 H p a).2.1
      (prog4 K1 K2 K3 K4 H p a).2.2.1 (prog4 K1 K2 K3 K4 H p a).2.2.2 M =
      pfRdM K1 K2 K3 K4 n1 k φ nxt G c4 H.1 H.2.1 H.2.2.1 H.2.2.2 M := by
  funext d σ
  unfold pfRdM
  congr 1
  refine runR4_prog h1 h2 h3 h4 φ (nxt c4 M) H p a ha k (fun r hr e => ?_)
  have hit : (pfRdMReads K1 K2 K3 K4 n1 k φ nxt H c4 M).any (fun r => decide (coord4 r.1 p = r.2)) = true :=
    List.any_eq_true.2 ⟨(r.1, pt4 n1 φ (M % n1) r), List.mem_map.2 ⟨r, hr, rfl⟩, decide_eq_true e⟩
  rw [hm] at hit; exact Bool.false_ne_true hit

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **The Sudoku proof with transcript-reading openings meets
    `FSMultiInterleave`'s `hout'`**: its output's reads at the challenges
    read are the three openings' reads at the third message. -/
theorem sudFS4T_houtL {V Wv P1 P2 P3 W1 W2 W3 : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat)  (Com2 : List (List (List F)) → Nat → Nat)  (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)  (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    {kq : Nat} (h1 : 0 < Q4 * Q4) (h2 : 0 < K2) (h3 : 0 < Q4) (h4 : 0 < K4)
    (φ1 : Nat → W1 → Nat) (nx1 : Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → List (List (List F)) → Nat → List Nat → P1)
    (φ2 : Nat → W2 → Nat) (nx2 : Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → List (List (List F)) → Nat → List Nat → P2)
    (φ3 : Nat → W3 → Nat) (nx3 : Nat → Nat → List Nat → Nat × Nat × W3)
    (G3 : Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3) :
    ∀ H p a c4 c1 c2 c3 x, a.1 < Q4 * Q4 ∧ a.2.1 < K2 ∧ a.2.2.1 < Q4 ∧ a.2.2.2 < K4 →
      (pfRdMReads (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) ++
        pfRdMReads (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) ++
        pfRdMReads (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x)).any
        (fun r => decide (coord4 r.1 p = r.2)) = false →
      (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).out (prog4 (Q4 * Q4) K2 Q4 K4 H p a) c4 c1 c2 c3 x = (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).out H c4 c1 c2 c3 x := by
  intro H p a c4 c1 c2 c3 x ha hm
  rw [List.any_append, List.any_append, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hm
  have e1 := pfRdM_prog h1 h2 h3 h4 φ1 nx1 G1 H p a ha c4 _ hm.1.1
  have e2 := pfRdM_prog h1 h2 h3 h4 φ2 nx2 G2 H p a ha c4 _ hm.1.2
  have e3 := pfRdM_prog h1 h2 h3 h4 φ3 nx3 G3 H p a ha c4 _ hm.2
  dsimp only [sudFS4T] at e1 e2 e3 ⊢
  rw [e1, e2, e3]

set_option maxRecDepth 100000 in
/-- **The Sudoku proof with transcript-reading openings is an interleaving
    component**: its view meets `hrd` (`rd4G_hrd` at `sudFS4T_houtL`), the
    messages' four reads and the openings' `3 kq` at the challenges read. -/
theorem sudFS4T_hrd {V Wv P1 P2 P3 W1 W2 W3 : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat)  (Com2 : List (List (List F)) → Nat → Nat)  (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)  (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    {kq : Nat} (h1 : 0 < Q4 * Q4) (h2 : 0 < K2) (h3 : 0 < Q4) (h4 : 0 < K4)
    (φ1 : Nat → W1 → Nat) (nx1 : Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → List (List (List F)) → Nat → List Nat → P1)
    (φ2 : Nat → W2 → Nat) (nx2 : Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → List (List (List F)) → Nat → List Nat → P2)
    (φ3 : Nat → W3 → Nat) (nx3 : Nat → Nat → List Nat → Nat × Nat × W3)
    (G3 : Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3) :
    ∀ H p a x, a.1 < Q4 * Q4 ∧ a.2.1 < K2 ∧ a.2.2.1 < Q4 ∧ a.2.2.2 < K4 →
      (rd4 (Q4 * Q4) K2 Q4 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m1 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m2 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).q H x ++
        rdOutG (Q4 * Q4) K2 Q4 K4 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m1 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m2 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).q
          (fun H c4 c1 c2 _ x => pfRdMReads (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) ++
            pfRdMReads (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) ++
            pfRdMReads (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x)) H x).any
        (fun r => decide (coord4 r.1 p = r.2)) = false →
      read4T (Q4 * Q4) K2 Q4 K4 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m1 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m2 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).q (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).out (prog4 (Q4 * Q4) K2 Q4 K4 H p a) x =
        read4T (Q4 * Q4) K2 Q4 K4 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m1 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m2 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).q (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRdM (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).out H x :=
  fun H p a x ha hm => rd4G_hrd h1 h2 h3 h4 _ _ _ _ _ _
    (sudFS4T_houtL off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 hqr h1 h2 h3 h4 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) H p a ha x hm

/-- The component's read count: `4 + 3 kq`. -/
theorem sud_rd_length {W1 W2 W3 X : Type} (K1 K2 K3 K4 n1 kq : Nat) (m1 : X → Nat) (m2 : Nat → X → Nat)
    (m3 : Nat → Nat → X → Nat) (q : Nat → Nat → Nat → X → Nat)
    (φ1 : Nat → W1 → Nat) (nx1 : Nat → Nat → List Nat → Nat × Nat × W1)
    (φ2 : Nat → W2 → Nat) (nx2 : Nat → Nat → List Nat → Nat × Nat × W2)
    (φ3 : Nat → W3 → Nat) (nx3 : Nat → Nat → List Nat → Nat × Nat × W3) (H : Nat × Nat × Nat × Nat) (x : X) :
    (rd4 K1 K2 K3 m1 m2 m3 q H x ++ rdOutG K1 K2 K3 K4 m1 m2 m3 q
      (fun H c4 c1 c2 _ x => pfRdMReads K1 K2 K3 K4 n1 kq φ1 nx1 H c4 (m3 c1 c2 x) ++
        pfRdMReads K1 K2 K3 K4 n1 kq φ2 nx2 H c4 (m3 c1 c2 x) ++
        pfRdMReads K1 K2 K3 K4 n1 kq φ3 nx3 H c4 (m3 c1 c2 x)) H x).length = 4 + 3 * kq := by
  simp only [rdOutG, List.length_append, rd4_length, pfRdMReads_length]
  rw [show 3 * kq = kq + kq + kq by rw [Nat.succ_mul, Nat.succ_mul, Nat.one_mul]]

end

/-- `pfRd`'s reads at its data and salt, `(table, point)`. -/
def pfRdReads {D W : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → D → Nat → List Nat → Nat × Nat × W) (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D)
    (σ : Nat) : List (Nat × Nat) :=
  (readsR4 K1 K2 K3 K4 n1 (M % n1) φ (nxt c4 M d σ) H k).map (fun r => (r.1, pt4 n1 φ (M % n1) r))

theorem pfRdReads_length {D W : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → D → Nat → List Nat → Nat × Nat × W) (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D)
    (σ : Nat) : (pfRdReads K1 K2 K3 K4 n1 k φ nxt H c4 M d σ).length = k := by
  unfold pfRdReads; rw [List.length_map, readsR4_length]

/-- **`pfRd` at its data and salt is unchanged by a programming its reads
    there miss.** -/
theorem pfRd_progD {D P W : Type} {K1 K2 K3 K4 n1 k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (φ : Nat → W → Nat) (nxt : Nat → Nat → D → Nat → List Nat → Nat × Nat × W) (G : Nat → Nat → D → Nat → List Nat → P)
    (H p a : Nat × Nat × Nat × Nat) (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (c4 M : Nat) (d : D)
    (σ : Nat)
    (hm : (pfRdReads K1 K2 K3 K4 n1 k φ nxt H c4 M d σ).any (fun r => decide (coord4 r.1 p = r.2)) = false) :
    pfRd K1 K2 K3 K4 n1 k φ nxt G c4 (prog4 K1 K2 K3 K4 H p a).1 (prog4 K1 K2 K3 K4 H p a).2.1
      (prog4 K1 K2 K3 K4 H p a).2.2.1 (prog4 K1 K2 K3 K4 H p a).2.2.2 M d σ =
      pfRd K1 K2 K3 K4 n1 k φ nxt G c4 H.1 H.2.1 H.2.2.1 H.2.2.2 M d σ := by
  unfold pfRd
  congr 1
  refine runR4_prog h1 h2 h3 h4 φ (nxt c4 M d σ) H p a ha k (fun r hr e => ?_)
  have hit : (pfRdReads K1 K2 K3 K4 n1 k φ nxt H c4 M d σ).any (fun r => decide (coord4 r.1 p = r.2)) = true :=
    List.any_eq_true.2 ⟨(r.1, pt4 n1 φ (M % n1) r), List.mem_map.2 ⟨r, hr, rfl⟩, decide_eq_true e⟩
  rw [hm] at hit; exact Bool.false_ne_true hit

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sudFS4T_houtL` with openings whose strategy reads the data and the
    salt** (`pfRd`): the read list names each opening's data
    (`sudMain1`, `sudMain2`, `sudMain3`) and salt (`x.1`, and `x.2.1` split
    by `pfPair`). -/
theorem sudFS4T_houtD {V Wv P1 P2 P3 W1 W2 W3 : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat)  (Com2 : List (List (List F)) → Nat → Nat)  (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)  (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    {kq : Nat} (h1 : 0 < Q4 * Q4) (h2 : 0 < K2) (h3 : 0 < Q4) (h4 : 0 < K4)
    (φ1 : Nat → W1 → Nat) (nx1 : Nat → Nat → List (List (List F)) → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → List (List (List F)) → Nat → List Nat → P1)
    (φ2 : Nat → W2 → Nat) (nx2 : Nat → Nat → List (List (List F)) → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → List (List (List F)) → Nat → List Nat → P2)
    (φ3 : Nat → W3 → Nat) (nx3 : Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → Nat × Nat × W3)
    (G3 : Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3) :
    ∀ H p a c4 c1 c2 c3 x, a.1 < Q4 * Q4 ∧ a.2.1 < K2 ∧ a.2.2.1 < Q4 ∧ a.2.2.2 < K4 →
      (pfRdReads (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) (sudMain1 V Wv off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri NR2 Rb Ro x.2.2.2 x.2.2.1) x.1 ++
        pfRdReads (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) (sudMain2 V Wv off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri NR2 Rb Ro c1 x.2.2.2 x.2.2.1)
          (x.2.1 % NS2) ++
        pfRdReads (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) (sudMain3 V Wv off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri NR2 Rb Ro c1 c2 x.2.2.2 x.2.2.1)
          (x.2.1 / NS2)).any (fun r => decide (coord4 r.1 p = r.2)) = false →
      (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).out (prog4 (Q4 * Q4) K2 Q4 K4 H p a) c4 c1 c2 c3 x = (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).out H c4 c1 c2 c3 x := by
  intro H p a c4 c1 c2 c3 x ha hm
  rw [List.any_append, List.any_append, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hm
  have e1 := pfRd_progD h1 h2 h3 h4 φ1 nx1 G1 H p a ha c4 _ _ _ hm.1.1
  have e2 := pfRd_progD h1 h2 h3 h4 φ2 nx2 G2 H p a ha c4 _ _ _ hm.1.2
  have e3 := pfRd_progD h1 h2 h3 h4 φ3 nx3 G3 H p a ha c4 _ _ _ hm.2
  dsimp only [sudFS4T, sudMain1, sudMain2, sudMain3, pfPair] at e1 e2 e3 ⊢
  rw [e1, e2, e3]

set_option maxRecDepth 100000 in
/-- **The Sudoku proof with data-reading openings is an interleaving
    component** (`rd4G_hrd` at `sudFS4T_houtD`), `4 + 3 kq` reads. -/
theorem sudFS4T_hrdD {V Wv P1 P2 P3 W1 W2 W3 : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat)  (Com2 : List (List (List F)) → Nat → Nat)  (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)  (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    {kq : Nat} (h1 : 0 < Q4 * Q4) (h2 : 0 < K2) (h3 : 0 < Q4) (h4 : 0 < K4)
    (φ1 : Nat → W1 → Nat) (nx1 : Nat → Nat → List (List (List F)) → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → List (List (List F)) → Nat → List Nat → P1)
    (φ2 : Nat → W2 → Nat) (nx2 : Nat → Nat → List (List (List F)) → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → List (List (List F)) → Nat → List Nat → P2)
    (φ3 : Nat → W3 → Nat) (nx3 : Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → Nat × Nat × W3)
    (G3 : Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3) :
    ∀ H p a x, a.1 < Q4 * Q4 ∧ a.2.1 < K2 ∧ a.2.2.1 < Q4 ∧ a.2.2.2 < K4 →
      (rd4 (Q4 * Q4) K2 Q4 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m1 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m2 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).q H x ++
        rdOutG (Q4 * Q4) K2 Q4 K4 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m1 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m2 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).q
          (fun H c4 c1 c2 _ x => pfRdReads (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) (sudMain1 V Wv off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri NR2 Rb Ro x.2.2.2 x.2.2.1) x.1 ++
        pfRdReads (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) (sudMain2 V Wv off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri NR2 Rb Ro c1 x.2.2.2 x.2.2.1)
          (x.2.1 % NS2) ++
        pfRdReads (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 H c4 ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 c1 c2 x) (sudMain3 V Wv off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri NR2 Rb Ro c1 c2 x.2.2.2 x.2.2.1)
          (x.2.1 / NS2)) H x).any (fun r => decide (coord4 r.1 p = r.2)) = false →
      read4T (Q4 * Q4) K2 Q4 K4 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m1 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m2 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).q (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).out (prog4 (Q4 * Q4) K2 Q4 K4 H p a) x =
        read4T (Q4 * Q4) K2 Q4 K4 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m1 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m2 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).m3 (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).q (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ1 nx1 G1) Com2 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ2 nx2 G2) Com3 (pfRd (Q4 * Q4) K2 Q4 K4 n1 kq φ3 nx3 G3) hqr).out H x :=
  fun H p a x ha hm => rd4G_hrd h1 h2 h3 h4 _ _ _ _ _ _
    (sudFS4T_houtD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 hqr h1 h2 h3 h4 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) H p a ha x hm

end

end Circuit
