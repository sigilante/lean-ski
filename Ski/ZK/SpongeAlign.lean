import Ski.ZK.SpongePrefix

/-!
# A first commitment split across two absorptions

Plonky3 0.8's `observe` buffers elements and permutes at `RATE` of them.
In the bench's Sudoku proof seven elements sit in the buffer when the
8-element `MAIN_COMMITMENT` arrives (measured on `release/sudoku`), so
the first permutation absorbs those seven and the commitment's first
element, and the second the commitment's other seven and one public
element.

- **Groups.** A commitment `c < n1 = G N0` splits as its group `c % G`,
  absorbed as the last block of the prefix `pre0 ++ [blk (c % G)]`, and
  its rest `c / G`, absorbed as the chain's first block `bf (c / G)`
  (`loadφG`).  Each group is `SpongePrefix`'s setting with its own
  prefix.
- **The spread.** The index's preimage is at most the groups' preimages
  summed; with `bf` injective into `N` blocks (`sumTo_inj_le`) each is at
  most that group's `loadTP`, so `δs' = δs loadG`, `loadG` the groups'
  loads summed, meets `hsp1` and `hφsp` (`loadG_hsp`), and averaged it
  is `G` times one group's bound (`loadG_δs_countP`).  The composite:
  `sud_interleaveLG`, `sud_interleaveLGN`.
- **0.8.** `bf h = h + p ^ 7 e` for the public element `e`, injective
  into full-rate blocks below `p ^ 8`, with `hd` and `hdxC` from every
  state (`align08_sat`).

Size.  At width 16, rate 8, `F / K = 1 / p ^ 7`, `N = p ^ 8`, `G = p`,
a 16-block prefix and blocks below `X = 9 p ^ 8`, optimizing `t` and
`s0` makes `E[loadG]` about `2^77`, `2^80`, `2^83`, `2^93` for
`L = 1, 3, 10, 100`, against `n1 = p ^ 8 ≈ 2^247` commitments.

Limits: the fourth table `H4` stays independent of the permutation, which
Plonky3 squeezes the challenge from; the seven buffered elements are read
off one statement's proof, not derived from the transcript's shape.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **The index with the first commitment split**: commitment `c = m % n1`
    absorbed as its group `c % G`, the last block of the prefix
    `pre0 ++ [blk (c % G)]`, then the rest `c / G` in the chain's first
    block `bf (c / G)`, then the later blocks. -/
def loadφG {W : Type} (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat)
    (G n1 L : Nat) (enc : Nat → W → List Nat) (H : Nat) : Nat → Nat → W → Nat :=
  fun _ m w => chain1 K inner (ivP K inner z (pre0 ++ [blk ((m % n1) % G)]) H) (bf ((m % n1) / G) :: enc (m / n1) w) H (L + 1)

/-- The groups' loads summed. -/
def loadG (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat) (blk : Nat → Nat) (G N X L t s0 H : Nat) : Nat :=
  sumTo G (fun g => loadTP K inner z (pre0 ++ [blk g]) N X L t s0 H)

/-- **A count through an injection**: the `q < N0` whose image under `bf`
    meets `P` number at most the `c < N` meeting it. -/
theorem sumTo_inj_le {N0 N : Nat} (bf : Nat → Nat) (P : Nat → Bool) (hbf : ∀ h, h < N0 → bf h < N)
    (hinj : ∀ h h', h < N0 → h' < N0 → bf h = bf h' → h = h') :
    sumTo N0 (fun q => indB (P (bf q))) ≤ sumTo N (fun c => indB (P c)) := by
  have e : ∀ q, q < N0 → indB (P (bf q)) = sumTo N (fun c => indB (decide (bf q = c)) * indB (P c)) := fun q hq => by
    rw [sumTo_congr _ (fun c _ => by
      show indB (decide (bf q = c)) * indB (P c) = indB (P (bf q)) * indB (decide (c = bf q))
      by_cases h : bf q = c
      · rw [h, decide_eq_true rfl, Nat.mul_comm]
      · rw [decide_eq_false h, decide_eq_false (Ne.symm h)]; simp [indB])]
    have hpt : sumTo N (fun c => indB (decide (c = bf q))) = 1 := by
      have := sumTo_point 1 N (hbf q hq)
      rw [← this]; exact sumTo_congr _ (fun c _ => (Nat.mul_one _).symm)
    rw [← sumTo_mul, hpt, Nat.mul_one]
  rw [sumTo_congr _ e, sumTo_exch]
  refine sumTo_mono _ (fun c _ => ?_)
  rw [sumTo_congr _ (fun q _ => Nat.mul_comm _ _), ← sumTo_mul]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sum_le_one N0 (fun q q' hq hq' h1 h2 => ?_))) (Nat.le_of_eq (Nat.mul_one _))
  exact hinj q q' hq hq' ((of_decide_eq_true h1).trans (of_decide_eq_true h2).symm)

/-- **`SudChallenger`'s spread hypotheses at every permutation table, the
    first commitment split**: `n1 = G N` commitments, each group's chains
    after its own prefix; the table's `δs' = δs loadG` meets `hsp1` and
    `hφsp` (`s0 ≥ 2`). -/
theorem loadG_hsp {D W : Type} {K NS1 n1 δs X G N0 N : Nat} (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat)
    (blk bf : Nat → Nat) (hG : 0 < G) (hN : 0 < N) (hn : n1 = G * N0) (hbf : ∀ h, h < N0 → bf h < N)
    (hinj : ∀ h h', h < N0 → h' < N0 → bf h = bf h' → h = h') (hX : 0 < X) (L t : Nat)
    (enc : Nat → W → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) {s0 : Nat} (hs0 : 2 ≤ s0) (H : Nat) :
    (∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs * loadG K inner z pre0 blk G N X L t s0 H) ∧
      (∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        (loadφG K inner z pre0 blk bf G n1 L enc H 0 (Com1 d σ1 + n1 * rest) w = v))) ≤
        δs * loadG K inner z pre0 blk G N X L t s0 H) := by
  have h1 : 1 ≤ loadG K inner z pre0 blk G N X L t s0 H := by
    unfold loadG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    show 1 ≤ sumTo G' _ + loadTP K inner z (pre0 ++ [blk G']) N X L t s0 H
    exact Nat.le_trans (Nat.le_trans (Nat.le_sub_of_add_le hs0) (Nat.le_add_right _ _)) (Nat.le_add_left _ _)
  refine ⟨fun d v => Nat.le_trans (hsp1 d v) (Nat.le_trans (Nat.le_of_eq (Nat.mul_one δs).symm)
    (Nat.mul_le_mul_left _ h1)), fun d rest w v => ?_⟩
  have hn1 : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (hr1 d 0)
  have em : ∀ σ1, (Com1 d σ1 + n1 * rest) % n1 = Com1 d σ1 ∧ (Com1 d σ1 + n1 * rest) / n1 = rest := fun σ1 =>
    ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hr1 d σ1)],
     by rw [Nat.add_mul_div_left _ _ hn1, Nat.div_eq_of_lt (hr1 d σ1), Nat.zero_add]⟩
  let φ := fun c => chain1 K inner (ivP K inner z (pre0 ++ [blk (c % G)]) H) (bf (c / G) :: enc rest w) H (L + 1)
  have e : ∀ σ1, loadφG K inner z pre0 blk bf G n1 L enc H 0 (Com1 d σ1 + n1 * rest) w = φ (Com1 d σ1) := fun σ1 => by
    unfold loadφG
    rw [(em σ1).1, (em σ1).2]
  rw [sumTo_congr _ (fun σ1 _ => by rw [e σ1]), sumTo_split_pos (Com1 d) (hr1 d)]
  have each : ∀ c, sumTo NS1 (fun σ => indB (decide (Com1 d σ = c)) * indB (decide (φ (Com1 d σ) = v))) ≤
      δs * indB (decide (φ c = v)) := fun c => by
    have e : ∀ σ, indB (decide (Com1 d σ = c)) * indB (decide (φ (Com1 d σ) = v)) =
        indB (decide (φ c = v)) * indB (decide (Com1 d σ = c)) := fun σ => by
      by_cases h : Com1 d σ = c
      · rw [h, Nat.mul_comm]
      · rw [decide_eq_false h]; simp [indB]
    rw [sumTo_congr _ (fun σ _ => e σ), ← sumTo_mul, Nat.mul_comm δs]
    exact Nat.mul_le_mul_left _ (hsp1 d c)
  refine Nat.le_trans (sumTo_mono _ (fun c _ => each c)) ?_
  rw [← sumTo_mul]
  refine Nat.mul_le_mul_left _ ?_
  -- commitments as group and rest: `c = g + G q`
  rw [hn, sumTo_split G _ N0, sumTo_exch]
  unfold loadG
  refine sumTo_mono _ (fun g hg => ?_)
  have hgq : ∀ q, (g + G * q) % G = g ∧ (g + G * q) / G = q := fun q =>
    ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hg],
     by rw [Nat.add_mul_div_left _ _ hG, Nat.div_eq_of_lt hg, Nat.zero_add]⟩
  let P := fun c => decide (chain1 K inner (ivP K inner z (pre0 ++ [blk g]) H) (c :: enc rest w) H (L + 1) = v)
  refine Nat.le_trans (Nat.le_of_eq (sumTo_congr _ (fun q _ => ?_)))
    (Nat.le_trans (sumTo_inj_le bf P hbf hinj) (preimage_loadTP K inner z (pre0 ++ [blk g]) hN hX L t s0 (enc rest w) (henc rest w) H v))
  show indB (decide (chain1 K inner (ivP K inner z (pre0 ++ [blk ((g + G * q) % G)]) H)
    (bf ((g + G * q) / G) :: enc rest w) H (L + 1) = v)) = _
  rw [(hgq q).1, (hgq q).2]

/-- **The split commitment's load averaged**: each group's bound, `G`
    times; every group's prefix has `m0 + 1` blocks. -/
theorem loadG_δs_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre0 : List Nat) (blk : Nat → Nat)
    (G : Nat) {N : Nat} (hN : 0 < N)
    (hd : ∀ iv a b, a < N → b < N → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ iv s s' x c c', c < N → c' < N → inner s x = inner iv c → inner s' x = inner iv c' → c = c') (X L : Nat)
    {t : Nat} (ht : 0 < t) (s0 δs : Nat) :
    fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (K - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t *
        sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadG K inner z pre0 blk G N X L t s0 H)) ≤
      δs * (G * ((fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (K - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t * (s0 - 1) +
        N * (X ^ L * (N ^ t * (sumTo (((pre0.length + 1) + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - ((pre0.length + 1) + 2 * L))))) * sumTo (K ^ K) (fun H => indB (permB K H)))) := by
  have each : ∀ g, fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (K - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t *
        sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadTP K inner z (pre0 ++ [blk g]) N X L t s0 H)) ≤
      δs * ((fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (K - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t * (s0 - 1) +
        N * (X ^ L * (N ^ t * (sumTo (((pre0.length + 1) + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - ((pre0.length + 1) + 2 * L))))) * sumTo (K ^ K) (fun H => indB (permB K H))) := fun g => by
    have h := loadTP_δs_countP hK inner hin κ hκ hF hpk2 z (pre0 ++ [blk g]) hN hd hdxC X L ht s0 δs
    rw [List.length_append, List.length_singleton] at h
    exact h
  have e : sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadG K inner z pre0 blk G N X L t s0 H)) =
      sumTo G (fun g => sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadTP K inner z (pre0 ++ [blk g]) N X L t s0 H))) := by
    unfold loadG
    rw [← sumTo_exch]
    refine sumTo_congr _ (fun H _ => ?_)
    rw [← sumTo_mul, ← sumTo_mul]
  rw [e, sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun g _ => each g)) (Nat.le_of_eq ?_)
  rw [sumTo_const, Nat.mul_left_comm]

/-- **Plonky3 0.8's split commitment meets the block map's premises**: the
    last `R - 1` elements `h < p ^ (R - 1)` and one public element `e < p`
    fill the second absorption, `bf h = h + p ^ (R - 1) e`, injective into
    full-rate blocks below `p ^ R`; and 0.8's absorption meets `hd` and
    `hdxC` from every state for full-rate first blocks (`inner08_hd`,
    `inner08_hdx`). -/
theorem align08_sat {R p Q : Nat} (hR : 0 < R) (hp : 0 < p) {e : Nat} (he : e < p) :
    (∀ h, h < p ^ (R - 1) → h + p ^ (R - 1) * e < p ^ R) ∧
      (∀ h h', h < p ^ (R - 1) → h' < p ^ (R - 1) → h + p ^ (R - 1) * e = h' + p ^ (R - 1) * e → h = h') ∧
      (∀ iv a b, a < p ^ R → b < p ^ R → a ≠ b → inner08 R (p ^ R) p Q iv a ≠ inner08 R (p ^ R) p Q iv b) ∧
      (∀ iv s s' x c c', c < p ^ R → c' < p ^ R → inner08 R (p ^ R) p Q s x = inner08 R (p ^ R) p Q iv c →
        inner08 R (p ^ R) p Q s' x = inner08 R (p ^ R) p Q iv c' → c = c') := by
  have hpR : p ^ R = p ^ (R - 1) * p := by
    conv => lhs; rw [← Nat.sub_add_cancel hR]
    rw [Nat.pow_succ]
  refine ⟨fun h hh => ?_, fun h h' _ _ e1 => Nat.add_right_cancel e1, fun iv a b ha hb hab => inner08_hd iv ha hb hab,
    fun iv s s' x c c' hc hc' e1 e2 => inner08_hdx hR hp (Nat.le_refl _) iv s s' x c c' hc hc' e1 e2⟩
  rw [hpR]
  calc h + p ^ (R - 1) * e < p ^ (R - 1) + p ^ (R - 1) * e := Nat.add_lt_add_right hh _
    _ = p ^ (R - 1) * (e + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ p ^ (R - 1) * p := Nat.mul_le_mul_left _ he

/-- The spread the permutation `H` gives proof `ix`, the first commitment
    split: `δ0 ix loadG`. -/
def δsG (K : Nat) (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat) (blk : Nat → Nat) (G N X L t s0 : Nat)
    (δ0 : Nat → Nat) (H ix : Nat) : Nat :=
  δ0 ix * loadG K inner z pre0 blk G N X L t s0 H

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_interleaveS` averaged over a uniform permutation, the first
    commitment split** (`loadφG`): at each permutation table `P` with
    `δsG P = δ0 loadG` (`loadG_hsp`); the error the permutation-weighted
    sum of the tables' errors (`zkbT_avgW`). -/
theorem sud_interleaveLG {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
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
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
      (fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x)
      (fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x))
      (fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x)
      (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsG Kp inner z pre0 blk G N X L t s0 δ0 P n))))))) n))) := by
  intro n
  exact zkbT_avgW (fun P => indB (permB Kp P)) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
    (fun P => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n)) (fun P => (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n)) (fun P => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n))
    (fun P => (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsG Kp inner z pre0 blk G N X L t s0 δ0 P n))))))) n)) (fun P _ hw =>
    sud_interleaveS φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp
      hK2 hK4 (loadφG Kp inner z pre0 blk bf G n1 L enc P) (fun _ _ _ => rget_lt hKp _ _) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
      Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 (δsG Kp inner z pre0 blk G N X L t s0 δ0 P)
      (fun ix => (loadG_hsp inner z pre0 blk bf hG hN hn hbf hinj hX L t enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).1)
      (fun ix => (loadG_hsp inner z pre0 blk bf hG hN hn hbf hinj hX L t enc henc (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).2) isQ nxtQ n)


-- The statement unfolds `sudDD`'s fields at every `ix`; elaborating it exceeds the default heartbeats.
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
/-- **`sud_interleaveLG` with a number for its error**: `m = m0 + 1`,
    `k = m + t (L+1)`, `e = t - 1 - (m + 2 L)`, `Kq = e! (Kp - k)^e s0 (s0-1) ⋯
    (s0-t+1)` times the averaged real count is at most `Kq` times the
    averaged simulation plus `errPowD` at the errors `Kq W ε` and each
    spread `δ0 i G (Kq (s0 - 1) + N X^L N^t ((0 + ⋯ + (k - 1)) F)^e) W`, `W`
    the number of permutation tables (`avg_err_bound`, `loadG_δs_countP`). -/
theorem sud_interleaveLGN {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat)
    {G N0 N : Nat} (hG : 0 < G) (hN : 0 < N) (hn : n1 = G * N0) (hbf : ∀ h, h < N0 → bf h < N)
    (hinj : ∀ h h', h < N0 → h' < N0 → bf h = bf h' → h = h')
    (hd : ∀ iv a b, a < N → b < N → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ iv s s' x c c', c < N → c' < N → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (δ0 : Nat → Nat) (hn1 : 0 < n1) {F : Nat} (hF : ∀ v, sumTo Kp (fun u => indB (decide (κ u = v))) ≤ F)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n (E : Nat × (Nat × Nat × Nat × Nat) → _ → Bool),
      (fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (Kp - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t) * ((KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E H ((fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x) H x))))) ≤
        (fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (Kp - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n) (fun c => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E ((fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x)) H c x) ((fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x) H c x))))) +
        errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => (fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (Kp - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))) * (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) i) (fun i => (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x))))))) i ((fun i => δ0 i * (G * ((fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (Kp - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t * (s0 - 1) + N * (X ^ L * (N ^ t * (sumTo (((pre0.length + 1) + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - ((pre0.length + 1) + 2 * L))))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P)))))) i)) n := by
  intro n E
  have h := sud_interleaveLG (kq := kq) φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 hKp inner hin κ hκ hpk2 z pre0 blk bf hG hN hn hbf hinj hd hdxC hX L enc henc δ0 hsp1 ht hs0 isQ nxtQ n
  have hb := (avg_err_bound (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) (Kp ^ Kp) (fun P => indB (permB Kp P))
      (fun P i => δsG Kp inner z pre0 blk G N X L t s0 δ0 P i) (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφG Kp inner z pre0 blk bf G n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x)))))))
      (fun i x => wrap_scale (lin_sum4 _ _ _ _) (lin_sum4 _ _ _ _) (lin_smPowD (fun _ => lin_sm _ _ _ _) i) _ _ _ _ _ x)
      (fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (Kp - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t) (fun i => δ0 i * (G * ((fact (t - 1 - ((pre0.length + 1) + 2 * L)) * (Kp - ((pre0.length + 1) + t * (L + 1))) ^ (t - 1 - ((pre0.length + 1) + 2 * L)) * ffac s0 t * (s0 - 1) + N * (X ^ L * (N ^ t * (sumTo (((pre0.length + 1) + t * (L + 1))) (fun j => j) * F) ^ (t - 1 - ((pre0.length + 1) + 2 * L))))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P)))))) (fun i => loadG_δs_countP hKp inner hin κ hκ hF hpk2 z pre0 blk G hN hd hdxC X L ht s0 (δ0 i)) n)
  exact zkbT_err_le h _ _ hb E

end

end Circuit
