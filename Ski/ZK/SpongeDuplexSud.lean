import Ski.ZK.SpongeDuplexFS

/-!
# A Sudoku proof's four challenges squeezed from one duplex run

`zk_duplex4` applied to `sud_fs4T`, its openings reading no table, its
fourth index constant (`sD1`; the side conditions by `rfl`): a duplex run
absorbing the domain-separator prefix, the three commitments and the
trace's openings at `ζ`, each phase of fixed length, squeezing after each
(`nxtD`, `timesD`), gives every challenge as the low part of a squeezed
state (`sud_duplex1`).  The view fixes the run on the answers consistent
with the drawn states (`nxtD_cons`): its commitments are the prover's
messages at the real challenges, and its trace openings at `ζ` are the
ones the run absorbs (`sudRvFS_oz`).  `sud_duplex1_sat08` meets the
duplex's hypotheses at 0.8's sponge over the Sudoku field.

Limits.  One proof: the interleaved proofs share tables, which needs the
squeeze positions injective in the transcript prefixes.  The openings read
no table and the quotient chunks' and codewords' openings at `ζ` are not
absorbed.  Each challenge is one squeeze's low part; 0.8 pops a phase's
challenges from one state, which fits when a phase's challenges fit the
rate.  The Sudoku run's hypotheses are left as `sud_fs4T` states them.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

theorem lt_mix {a b n m : Nat} (ha : a < n) (hb : b < m) : a + n * b < n * m :=
  calc a + n * b < n + n * b := Nat.add_lt_add_right ha _
    _ = n * (b + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ n * m := Nat.mul_le_mul_left _ hb

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

variable {V Wv P1 P2 P3 : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat)
  (row : Nat → Air.Row) (tP : Nat) (S16 S10 SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
  (wm wc ww wp : Nat → List (EF → EF → List F)) (K2 K4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat)
  (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF))
  (Ro : Nat → EF → EF → Nat → Wv) (NS1 NS2 NS3 n1 n2 n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat)
  (Pf1 : Nat → Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat)
  (Pf2 : Nat → Nat → List (List (List F)) → Nat → P2)
  (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
  (Pf3 : Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3)
  (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)

/-- The single Sudoku proof with its openings reading no table and its
    fourth index constant. -/
def sD1 : FS4DT (Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF) :=
  sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (fun _ _ => 0) 1 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
    n1 n2 n3 Com1 (fun c4 _ _ _ _ M => Pf1 c4 M) Com2 (fun c4 _ _ _ _ M => Pf2 c4 M) Com3 (fun c4 _ _ _ _ M => Pf3 c4 M)
    hqr

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sD1_out (H H' : Nat × Nat × Nat × Nat) :
    (sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1
      Com2 Pf2 Com3 Pf3 hqr).out H =
    (sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1
      Com2 Pf2 Com3 Pf3 hqr).out H' := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sD1_sv (H H' c : Nat × Nat × Nat × Nat) (x : XSud) :
    (sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1
      Com2 Pf2 Com3 Pf3 hqr).sv H c x =
    (sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1
      Com2 Pf2 Com3 Pf3 hqr).sv H' c x := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sD1_svp (H c : Nat × Nat × Nat × Nat) (x : XSud) :
    let D := sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1
      Pf1 Com2 Pf2 Com3 Pf3 hqr
    (D.sv H c x).1 = (D.pts c x).1 ∧ (D.sv H c x).2.1 = (D.pts c x).2.1 ∧ (D.sv H c x).2.2.1 = (D.pts c x).2.2.1 :=
  ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sD1_q (c1 c2 c3 : Nat) (x : XSud) :
    (sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1
      Com2 Pf2 Com3 Pf3 hqr).q c1 c2 c3 x = 0 := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sD1_pts4 (c : Nat × Nat × Nat × Nat) (x : XSud) :
    ((sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1
      Com2 Pf2 Com3 Pf3 hqr).pts c x).2.2.2 = 0 := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sD1_out_rvFS (H : Nat × Nat × Nat × Nat) (c4 c1 c2 c3 : Nat) (x : XSud) :
    ((sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1
      Com2 Pf2 Com3 Pf3 hqr).out H c4 c1 c2 c3 x).2.2 =
    sudRvFS off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri Rb Ro c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4))
      x.2.2.1 x.2.2.2 := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sD1_ranges (hr1 : ∀ d σ, Com1 d σ < n1) (hr2 : ∀ d σ, Com2 d σ < n2) (hr3 : ∀ d σ, Com3 d σ < n3) :
    let D := sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr
    (∀ x, D.m1 x < n1) ∧ (∀ c x, D.m2 c x < n1 * n2) ∧ (∀ c1 c2 x, D.m3 c1 c2 x < n1 * (n2 * n3)) ∧
    (∀ c x, (D.pts c x).1 < n1) ∧ (∀ c x, (D.pts c x).2.1 < n1 * n2) ∧
    (∀ c x, (D.pts c x).2.2.1 < n1 * (n2 * n3)) :=
  ⟨fun _ => hr1 _ _, fun _ _ => lt_mix (hr1 _ _) (hr2 _ _),
    fun _ _ _ => lt_mix (hr1 _ _) (lt_mix (hr2 _ _) (hr3 _ _)), fun _ _ => hr1 _ _,
    fun _ _ => lt_mix (hr1 _ _) (hr2 _ _), fun _ _ => lt_mix (hr1 _ _) (lt_mix (hr2 _ _) (hr3 _ _))⟩

variable (inner : Nat → Nat → Nat) (z : Nat) (pre : List Nat) (enc1 enc2 enc3 : Nat → List Nat)
  (enc4 : Option (List (List (List EF))) → List Nat) (ℓ : Nat → Nat)

/-- The duplex's blocks: the prefix, the three commitments' encodings, and
    the trace openings at `ζ`, the later ones chosen by the challenges. -/
def blocksD (c1 c2 c3 : Nat) (x : XSud) : List Nat :=
  pre ++ enc1 ((sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m1 x) ++ enc2 ((sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m2 c1 x) ++ enc3 ((sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).m3 c1 c2 x) ++
    enc4 (ozζV (sudRvFS off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri Rb Ro 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))

/-- The last answer, or `z` before any. -/
def headOr (z : Nat) : List Nat → Nat
  | [] => z
  | a :: _ => a

/-- The squeeze times: after the prefix and each phase's blocks. -/
def timesD (i : Nat) : Nat := pre.length + sumTo (i + 1) ℓ - 1

/-- The answer at time `s` of answers listed newest first. -/
def ansL (l : List Nat) (s : Nat) : Nat := l.getD (l.length - 1 - s) 0

/-- **The duplex run's next position**: the next block absorbed into the
    last answer, the blocks after a squeeze chosen by the challenges read
    off the squeezed answers. -/
def nxtD (x : XSud) (l : List Nat) : Nat :=
  inner (headOr z l)
    ((blocksD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1
      Pf1 Com2 Pf2 Com3 Pf3 hqr pre enc1 enc2 enc3 enc4 (ansL l (timesD pre ℓ 0) % (Q4 * Q4)) (ansL l (timesD pre ℓ 1) % K2)
      (ansL l (timesD pre ℓ 2) % Q4) x).getD l.length 0)

/-- The run's next position read off a view: its commitments and its trace
    openings at `ζ`. -/
def nxtVD (v : Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF)) (l : List Nat) : Nat :=
  inner (headOr z l)
    ((pre ++ enc1 v.1 ++ enc2 v.2.1 ++ enc3 v.2.2.1 ++ enc4 (ozζV v.2.2.2.2.2)).getD l.length 0)

theorem consW_at {K : Nat} {times : Nat → Nat} {W : Nat} {l : List Nat} (h : consW K times 4 W l = true) (i : Nat)
    (hi : i < 4) (ht : times i < l.length) : ansL l (times i) = rget K i W := by
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [decide_eq_true ht, Bool.not_true, Bool.false_or] at this
  exact beq_iff_eq.1 this

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The view's run agrees with the real one on consistent answers**: with
    the prefix and the first three phases' encodings of fixed lengths, an
    answer list showing `W`'s states at the squeezes it reaches gives the
    view's next position, read off the real view at `W`'s challenges. -/
theorem nxtD_cons {K : Nat} (hℓ : ∀ j, 0 < ℓ j) (hl1 : ∀ m, (enc1 m).length = ℓ 0)
    (hl2 : ∀ m, (enc2 m).length = ℓ 1) (hl3 : ∀ m, (enc3 m).length = ℓ 2) (x : XSud) (W : Nat) (l : List Nat)
    (hc : consW K (timesD pre ℓ) 4 W l = true) :
    let D := sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr
    let C := cW4 K (Q4 * Q4) K2 Q4 K4 W
    nxtVD inner z pre enc1 enc2 enc3 enc4 (D.m1 x, D.m2 C.1 x, D.m3 C.1 C.2.1 x, D.out (0, 0, 0, 0) C.2.2.2 C.1 C.2.1 C.2.2.1 x) l =
      nxtD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1
        Com2 Pf2 Com3 Pf3 hqr inner z pre enc1 enc2 enc3 enc4 ℓ x l := by
  intro D C
  show inner (headOr z l)
      ((pre ++ enc1 (D.m1 x) ++ enc2 (D.m2 C.1 x) ++ enc3 (D.m3 C.1 C.2.1 x) ++
        enc4 (ozζV (D.out (0, 0, 0, 0) C.2.2.2 C.1 C.2.1 C.2.2.1 x).2.2)).getD l.length 0) =
    inner (headOr z l)
      ((blocksD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr pre enc1 enc2 enc3 enc4 (ansL l (timesD pre ℓ 0) % (Q4 * Q4)) (ansL l (timesD pre ℓ 1) % K2)
        (ansL l (timesD pre ℓ 2) % Q4) x).getD l.length 0)
  refine congrArg _ ?_
  have hv : pre ++ enc1 (D.m1 x) ++ enc2 (D.m2 C.1 x) ++ enc3 (D.m3 C.1 C.2.1 x) ++
      enc4 (ozζV (D.out (0, 0, 0, 0) C.2.2.2 C.1 C.2.1 C.2.2.1 x).2.2) = blocksD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr pre enc1 enc2 enc3 enc4 C.1 C.2.1 C.2.2.1 x := by
    show _ ++ enc4 (ozζV (D.out (0, 0, 0, 0) C.2.2.2 C.1 C.2.1 C.2.2.1 x).2.2) = _ ++ _
    rw [sD1_out_rvFS, sudRvFS_oz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C.2.2.2 0]
  rw [hv]
  -- the challenges the list has reached are `W`'s
  have t0 : timesD pre ℓ 0 = pre.length + ℓ 0 - 1 := by
    show pre.length + (0 + ℓ 0) - 1 = _; rw [Nat.zero_add]
  have t1 : timesD pre ℓ 1 = pre.length + (ℓ 0 + ℓ 1) - 1 := by
    show pre.length + (0 + ℓ 0 + ℓ 1) - 1 = _; rw [Nat.zero_add]
  have t2 : timesD pre ℓ 2 = pre.length + (ℓ 0 + ℓ 1 + ℓ 2) - 1 := by
    show pre.length + (0 + ℓ 0 + ℓ 1 + ℓ 2) - 1 = _; rw [Nat.zero_add]
  have h0 := hℓ 0
  have h1 := hℓ 1
  have h2 := hℓ 2
  let t := l.length
  have L1 : ∀ a, (pre ++ enc1 a).length = pre.length + ℓ 0 := fun a => by rw [List.length_append, hl1]
  have L2 : ∀ a b, (pre ++ enc1 a ++ enc2 b).length = pre.length + (ℓ 0 + ℓ 1) := fun a b => by
    rw [List.length_append, L1, hl2, Nat.add_assoc]
  have L3 : ∀ a b c, (pre ++ enc1 a ++ enc2 b ++ enc3 c).length = pre.length + (ℓ 0 + ℓ 1 + ℓ 2) := fun a b c => by
    rw [List.length_append, L2, hl3, Nat.add_assoc]
  have A3 : ∀ a b c d, t < pre.length + (ℓ 0 + ℓ 1 + ℓ 2) →
      (pre ++ enc1 a ++ enc2 b ++ enc3 c ++ enc4 d).getD t 0 = (pre ++ enc1 a ++ enc2 b ++ enc3 c).getD t 0 :=
    fun a b c d h => getD_app_left _ _ t (by rw [L3]; exact h)
  have A2 : ∀ a b c, t < pre.length + (ℓ 0 + ℓ 1) →
      (pre ++ enc1 a ++ enc2 b ++ enc3 c).getD t 0 = (pre ++ enc1 a ++ enc2 b).getD t 0 :=
    fun a b c h => getD_app_left _ _ t (by rw [L2]; exact h)
  have A1 : ∀ a b, t < pre.length + ℓ 0 → (pre ++ enc1 a ++ enc2 b).getD t 0 = (pre ++ enc1 a).getD t 0 :=
    fun a b h => getD_app_left _ _ t (by rw [L1]; exact h)
  unfold blocksD
  by_cases a0 : t < pre.length + ℓ 0
  · have b1 : t < pre.length + (ℓ 0 + ℓ 1) := by omega
    have b2 : t < pre.length + (ℓ 0 + ℓ 1 + ℓ 2) := by omega
    rw [A3 _ _ _ _ b2, A3 _ _ _ _ b2, A2 _ _ _ b1, A2 _ _ _ b1, A1 _ _ a0, A1 _ _ a0]
  · have e1 : ansL l (timesD pre ℓ 0) % (Q4 * Q4) = C.1 := by
      rw [consW_at hc 0 (by decide) (by rw [t0]; omega)]; rfl
    rw [e1]
    by_cases a1 : t < pre.length + (ℓ 0 + ℓ 1)
    · have b2 : t < pre.length + (ℓ 0 + ℓ 1 + ℓ 2) := by omega
      rw [A3 _ _ _ _ b2, A3 _ _ _ _ b2, A2 _ _ _ a1, A2 _ _ _ a1]
    · have e2 : ansL l (timesD pre ℓ 1) % K2 = C.2.1 := by
        rw [consW_at hc 1 (by decide) (by rw [t1]; omega)]; rfl
      rw [e2]
      by_cases a2 : t < pre.length + (ℓ 0 + ℓ 1 + ℓ 2)
      · rw [A3 _ _ _ _ a2, A3 _ _ _ _ a2]
      · have e3 : ansL l (timesD pre ℓ 2) % Q4 = C.2.2.1 := by
          rw [consW_at hc 2 (by decide) (by rw [t2]; omega)]; rfl
        rw [e3]

end


theorem sumTo_lt_pos {ℓ : Nat → Nat} (hℓ : ∀ j, 0 < ℓ j) (n : Nat) : ∀ d, sumTo n ℓ < sumTo (n + d + 1) ℓ
  | 0 => Nat.lt_add_of_pos_right (hℓ n)
  | d + 1 => Nat.lt_trans (sumTo_lt_pos hℓ n d) (Nat.lt_add_of_pos_right (hℓ _))

theorem timesD_mono (pre : List Nat) {ℓ : Nat → Nat} (hℓ : ∀ j, 0 < ℓ j) :
    ∀ i j, i < j → timesD pre ℓ i < timesD pre ℓ j := by
  intro i j hij
  unfold timesD
  have h1 := sumTo_lt_pos hℓ (i + 1) (j - i - 1)
  have e : i + 1 + (j - i - 1) + 1 = j + 1 := by omega
  rw [e] at h1
  have h0 : 0 < sumTo (i + 1) ℓ := Nat.lt_of_lt_of_le (hℓ i) (Nat.le_add_left _ _)
  omega

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **A Sudoku proof with all four challenges squeezed from one duplex
    run.**  `sud_fs4T`, its openings reading no table and its fourth index
    constant, through `zk_duplex4`: the run absorbs the domain-separator
    prefix, the three commitments' encodings and the trace openings at `ζ`,
    each phase's blocks of fixed length, and squeezes after each phase
    (`nxtD`, `timesD`); each challenge is the low part of its squeezed
    state, the state `K = K_j L_j`.  The simulated distinguisher sees the
    permutation programmed at the squeezes in order with the simulated
    states, its run read off the simulated view (`nxtVD`). -/
theorem sud_duplex1 {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    (S16 S10 SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
        (hS16 : ∀ c4, ∀ x ∈ S16 c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ c4, ∀ x ∈ S10 c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz16 : ∀ c4, 2 * (S16 c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ c4, 2 * (S10 c4).length + 8 ≤ 2 ^ 10)
    (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V)
    (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ∀ c4 M, ComPfHides NS1 Com1 (Pf1 c4 M) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4 M, ComPfHides NS2 Com2 (Pf2 c4 M) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4 M, ComPfHides NS3 Com3 (Pf3 c4 M) (fun d => (opQ (sudSsT (S16 c4) (S10 c4) (SP c4)) d.1, opCw (sudSsC tP (S16 c4) (S10 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F))) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    {K L1 L2 L3 L4 : Nat} (hK : 0 < K) (e1 : K = Q4 * Q4 * L1) (e2 : K = K2 * L2) (e3 : K = Q4 * L3)
    (e4 : K = K4 * L4) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (z : Nat) (pre : List Nat)
    (enc1 enc2 enc3 : Nat → List Nat) (enc4 : Option (List (List (List EF))) → List Nat) (ℓ : Nat → Nat)
    (hℓ : ∀ j, 0 < ℓ j) (hl1 : ∀ m, (enc1 m).length = ℓ 0) (hl2 : ∀ m, (enc2 m).length = ℓ 1)
    (hl3 : ∀ m, (enc3 m).length = ℓ 2)
    (E : Nat → Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF) → Bool) :
    let D := sD1 off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr
    let nxt := nxtD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3
      Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr inner z pre enc1 enc2 enc3 enc4 ℓ
    let nxtV := nxtVD (P1 := P1) (P2 := P2) (P3 := P3) (V := V) (Wv := Wv) inner z pre enc1 enc2 enc3 enc4
    let times := timesD pre ℓ
    let rvc := fun (c : Nat × Nat × Nat × Nat) (x : XSud) =>
      (D.m1 x, D.m2 c.1 x, D.m3 c.1 c.2.1 x, D.out (0, 0, 0, 0) c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    let TT := K4 ^ 1 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * Q4 ^ (n1 * (n2 * n3))))
    TT * (K ^ 4 * D.sm 2 (fun x => sumTo (K ^ K) (fun P => indB (permB K P &&
        E P (rvc (cW4 K (Q4 * Q4) K2 Q4 K4 (WofR K (nxt x) times 4 P)) x))))) ≤
      TT * D.sm 2 (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ 4) (fun W =>
        indB (E (progSeqN K (nxtV (D.sv (0, 0, 0, 0) (cW4 K (Q4 * Q4) K2 Q4 K4 W) x)) times 4 W P)
          (D.sv (0, 0, 0, 0) (cW4 K (Q4 * Q4) K2 Q4 K4 W) x))))) +
      sumTo (K ^ K) (fun P => indB (permB K P)) * (L4 * (L3 * (L2 * (L1 * D.ε)))) +
      TT * D.sm 2 (fun x => 2 * badSeq K (nxt x) times 4 + sumTo 4 (fun j => K ^ (4 - j) * badSeq K (nxt x) times j)) := by
  intro D nxt nxtV times rvc TT
  have hQ : 0 < Q4 := Q4_pos
  have hR := sD1_ranges off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
    n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr hr1 hr2 hr3
  have h := sud_fs4T off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4
    (fun _ _ => 0) (N4 := 1) (fun _ _ => Nat.one_pos) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
    Com1 (fun c4 _ _ _ _ M => Pf1 c4 M) hc1 (fun c4 _ _ _ _ M => hp1 c4 M) hr1 d1
    Com2 (fun c4 _ _ _ _ M => Pf2 c4 M) hc2 (fun c4 _ _ _ _ M => hp2 c4 M) hr2 d2
    Com3 (fun c4 _ _ _ _ M => Pf3 c4 M) hc3 (fun c4 _ _ _ _ M => hp3 c4 M) hr3 d3 hqr
  exact zk_duplex4 (N1 := n1) (N2 := n1 * n2) (N3 := n1 * (n2 * n3)) (N4 := 1) hK (Nat.mul_pos hQ hQ) hK2 hQ hK4
    e1 e2 e3 e4 (D.sm 2) (lin_sm _ _ _ _) D.m1 D.m2 D.m3 D.q D.out D.pts D.sv
    hR.1 hR.2.1 hR.2.2.1 (fun _ _ _ _ => Nat.one_pos) hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2
    (fun _ _ => Nat.one_pos)
    (sD1_out off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1
      Pf1 Com2 Pf2 Com3 Pf3 hqr)
    (sD1_sv off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1
      Pf1 Com2 Pf2 Com3 Pf3 hqr)
    (sD1_svp off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1
      Pf1 Com2 Pf2 Com3 Pf3 hqr)
    (fun _ => 0) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ => rfl) h nxt (fun _ _ => hin _ _) times
    (timesD_mono pre hℓ) nxtV
    (fun x W l hl => nxtD_cons off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
      n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr inner z pre enc1 enc2 enc3 enc4 ℓ hℓ hl1 hl2 hl3 x W l hl) E

end

theorem Q4_eq : Q4 = P ^ 4 := by
  unfold Q4
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_one]; ac_rfl

/-- **`sud_duplex1`'s duplex hypotheses hold at 0.8's sponge over the
    Sudoku field**: width 16, rate 8 (`K = p^8 · p · p^7`), the first and
    third challenges' spaces `Q4²` and `Q4` dividing the state, the
    absorption below `K`, and one-block phases. -/
theorem sud_duplex1_sat08 :
    let K := P ^ 8 * (P * P ^ 7)
    (K = Q4 * Q4 * P ^ 8) ∧ (K = Q4 * P ^ 12) ∧ (K = K * 1) ∧
      (∀ s x, inner08 8 (P ^ 8) P (P ^ 7) s x < K) ∧
      (∀ j, 0 < (fun _ : Nat => 1) j) ∧ (∀ m : Nat, [m].length = 1) := by
  intro K
  have hK : K = P ^ 16 := by
    show P ^ 8 * (P * P ^ 7) = P ^ 16
    rw [← Nat.pow_succ', ← Nat.pow_add]
  refine ⟨?_, ?_, (Nat.mul_one K).symm, inner08_lt (by decide) P_pos (Nat.pow_pos P_pos), fun _ => Nat.one_pos,
    fun _ => rfl⟩
  · rw [hK, Q4_eq, ← Nat.pow_add, ← Nat.pow_add]
  · rw [hK, Q4_eq, ← Nat.pow_add]

end Circuit
