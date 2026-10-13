import Ski.ZK.FSMulti

/-!
# A commitment drawn from the random oracle hides

The theorems so far take the commitment as a primitive apart from the
oracle, and let the distinguisher read the oracle's whole table.  A salted
commitment read off the oracle itself, `Com d σ = H(pos d σ)`, cannot hide
from such a distinguisher, which tries every salt.  Against a
distinguisher of `k` adaptive queries it does: reprogramming a position
the run never queries leaves the run as it was (`runQ_rset`), so the
commitment's answer is uniform beside the run, its queries chosen after
seeing the commitment (`rom_offQ`, `rom_offQ'`),
and the counts at two data differ by at most the tables times `2 s k`,
`s` salts at most taking a position (`rom_hideQ`), `2 s k / NS` once
normalized.  The fixed-query case first (`rom_off`, `rom_hide`).

The Fiat–Shamir theorems take exact hiding (`ComHides`, `ComPfHides`);
approximate hiding (`ComHidesA`, `ComPfHidesA`) enters only the real side,
so one round with the commitment opened keeps its bound with the slack
added (`open_realA`, `open_real_tA`, `fs_openA`).  The opened commitment
hides against such runs: the salt split into its shown part the
proof shows and the hidden rest (`rom_hidePfQ`, `2 s k / NSh`
normalized).  Composed for one round (`fs_openROM`): the commitment's
table and both salt parts folded into the salt (`comR`), the proof carrying
the distinguisher's `k` queries into that table, chosen after the opening
and the commitment (`pfR`), so the bare commitment hides exactly
(`comR_hides`) and the opened one up to the slack (`pfR_hidesA`).

What this covers, and what it leaves out:
* a single-hash commitment, one oracle position per datum and salt, that
  opens to some values and part of its salt; a Merkle tree's
  authentication path and its positions read off child hashes are not
  modelled;
* the distinguisher's queries read the opening, the commitment and their
  earlier answers, not the Fiat–Shamir table or the view;
* where the prover aborts, the distinguisher sees the commitment and no
  query answers;
* one round; the commitment's table apart from the Fiat–Shamir table, as a
  domain-separated oracle's.

**The route through every round.**  The ideal opening answers the
distinguisher's queries on the commitment's table with the commitment's own
answer re-randomized by one more salt digit (`comI`, `pfI`); the
re-randomized table is uniform and apart from the commitment
(`reprog_swap`), so the pair hides exactly (`comI_hides`, `pfI_hides`) and
every exact Fiat–Shamir theorem here applies to it unchanged, every round
and every instance.  The real opening differs from the ideal only where the distinguisher's run
queries the commitment's own position (`pfR_pfI`), and those runs are few:
at most `NSo Kⁿ s k` over the salts and the table, `s k / NSh` normalized
(`rset_back`, `hit_rset`, `hit_bound`).  So each theorem's real count with
the commitment drawn from the oracle is its count with the ideal opening,
to which the exact theorem applies, up to the hits.  Writing that transfer
into each theorem's statement is not yet done.
-/

namespace Circuit

open ZKF

/-- **A commitment off the queries is uniform beside them**: `K` times the
    count of an event of the table's answers at the positions `Q` and at
    `p ∉ Q` is the count over the tables and every answer at `p`. -/
theorem rom_off {K n p : Nat} (hK : 0 < K) (hp : p < n) (Q : List Nat) (hQ : p ∉ Q)
    (E : List Nat → Nat → Bool) :
    K * sumTo (K ^ n) (fun H => indB (E (Q.map (fun q => rget K q H)) (rget K p H))) =
      sumTo (K ^ n) (fun H => sumTo K (fun c => indB (E (Q.map (fun q => rget K q H)) c))) := by
  rw [← oracle_reprog_get hK hp (fun H c => indB (E (Q.map (fun q => rget K q H)) c))]
  refine sumTo_congr _ (fun H _ => sumTo_congr _ (fun c hc => ?_))
  have e : Q.map (fun q => rget K q (rset K p H c)) = Q.map (fun q => rget K q H) :=
    List.map_congr_left (fun q hq => rget_rset_ne hK (fun e => hQ (e ▸ hq)) hc)
  rw [e]

/-- **A salted commitment from the oracle hides against a fixed set of
    queries**: the distinguisher sees the table at the positions `Q` and the
    commitment `H(pos d σ)`; over the tables and the salts, its counts at two
    data differ by at most the salts that put either commitment's position
    among the queries, each counting the whole table. -/
theorem rom_hide {D : Type} {K n NS : Nat} (hK : 0 < K) (pos : D → Nat → Nat) (hpos : ∀ d σ, pos d σ < n)
    (Q : List Nat) (E : List Nat → Nat → Bool) (d d' : D) :
    K * sumTo NS (fun σ => sumTo (K ^ n) (fun H => indB (E (Q.map (fun q => rget K q H)) (rget K (pos d σ) H)))) ≤
      K * sumTo NS (fun σ => sumTo (K ^ n) (fun H => indB (E (Q.map (fun q => rget K q H)) (rget K (pos d' σ) H)))) +
        K * K ^ n * sumTo NS (fun σ => indB (decide (pos d σ ∈ Q)) + indB (decide (pos d' σ ∈ Q))) := by
  rw [sumTo_mul, sumTo_mul, sumTo_mul, ← sumTo_add]
  refine sumTo_mono _ (fun σ _ => ?_)
  by_cases h1 : pos d σ ∈ Q
  · have : K * sumTo (K ^ n) (fun H => indB (E (Q.map (fun q => rget K q H)) (rget K (pos d σ) H))) ≤ K * K ^ n := by
      refine Nat.mul_le_mul_left _ (Nat.le_trans (sumTo_mono _ (fun H _ => indB_le _)) (Nat.le_of_eq ?_))
      rw [sumTo_const, Nat.mul_one]
    refine Nat.le_trans this (Nat.le_trans ?_ (Nat.le_add_left _ _))
    simp only [h1, decide_true, indB, if_true]
    exact Nat.le_mul_of_pos_right _ (by omega)
  · by_cases h2 : pos d' σ ∈ Q
    · have : K * sumTo (K ^ n) (fun H => indB (E (Q.map (fun q => rget K q H)) (rget K (pos d σ) H))) ≤
          K * K ^ n := by
        refine Nat.mul_le_mul_left _ (Nat.le_trans (sumTo_mono _ (fun H _ => indB_le _)) (Nat.le_of_eq ?_))
        rw [sumTo_const, Nat.mul_one]
      refine Nat.le_trans this (Nat.le_trans ?_ (Nat.le_add_left _ _))
      simp only [h2, decide_true, indB, if_true]
      exact Nat.le_mul_of_pos_right _ (by split <;> omega)
    · rw [rom_off hK (hpos d σ) Q h1, rom_off hK (hpos d' σ) Q h2]
      exact Nat.le_add_right _ _

/-- **An adaptive run of `k` queries**, after seeing the commitment's value
    `c`: each query's position read off `c` and the answers so far
    (`nxt`), the answers newest first. -/
def runQ (K : Nat) (nxt : Nat → List Nat → Nat) (c : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, H => rget K (nxt c (runQ K nxt c k H)) H :: runQ K nxt c k H

/-- The positions the run queries. -/
def qposQ (K : Nat) (nxt : Nat → List Nat → Nat) (c : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, H => nxt c (runQ K nxt c k H) :: qposQ K nxt c k H

/-- **A run that never queries `p` does not see `p` set.** -/
theorem runQ_rset {K p a : Nat} (hK : 0 < K) (ha : a < K) (nxt : Nat → List Nat → Nat) (c : Nat) :
    ∀ k H, p ∉ qposQ K nxt c k H → runQ K nxt c k (rset K p H a) = runQ K nxt c k H ∧
      qposQ K nxt c k (rset K p H a) = qposQ K nxt c k H
  | 0, _, _ => ⟨rfl, rfl⟩
  | k + 1, H, h => by
    simp only [qposQ, List.mem_cons, not_or] at h
    obtain ⟨e1, e2⟩ := runQ_rset hK ha nxt c k H h.2
    refine ⟨?_, ?_⟩
    · show rget K (nxt c (runQ K nxt c k (rset K p H a))) (rset K p H a) :: runQ K nxt c k (rset K p H a) =
        rget K (nxt c (runQ K nxt c k H)) H :: runQ K nxt c k H
      rw [e1, rget_rset_ne hK (fun e => h.1 e.symm) ha]
    · show nxt c (runQ K nxt c k (rset K p H a)) :: qposQ K nxt c k (rset K p H a) =
        nxt c (runQ K nxt c k H) :: qposQ K nxt c k H
      rw [e1, e2]

/-- **A commitment off an adaptive run is uniform beside it**, the run
    choosing its queries after seeing the commitment, up to the tables and
    values whose run queries it. -/
theorem rom_offQ {K n p k : Nat} (hK : 0 < K) (hp : p < n) (nxt : Nat → List Nat → Nat)
    (E : List Nat → Nat → Bool) :
    K * sumTo (K ^ n) (fun H => indB (E (runQ K nxt (rget K p H) k H) (rget K p H))) ≤
      sumTo (K ^ n) (fun H => sumTo K (fun c => indB (E (runQ K nxt c k H) c))) +
        sumTo (K ^ n) (fun H => sumTo K (fun c => indB (decide (p ∈ qposQ K nxt c k H)))) := by
  rw [← oracle_reprog_get hK hp (fun H c => indB (E (runQ K nxt c k H) c)), ← sumTo_add]
  refine sumTo_mono _ (fun H _ => ?_)
  rw [← sumTo_add]
  refine sumTo_mono _ (fun c hc => ?_)
  by_cases hq : p ∈ qposQ K nxt c k H
  · have e : indB (decide (p ∈ qposQ K nxt c k H)) = 1 := by simp [indB, hq]
    rw [e]; exact Nat.le_trans (indB_le _) (Nat.le_add_left _ _)
  · rw [(runQ_rset hK hc nxt c k H hq).1]; exact Nat.le_add_right _ _

theorem rom_offQ' {K n p k : Nat} (hK : 0 < K) (hp : p < n) (nxt : Nat → List Nat → Nat)
    (E : List Nat → Nat → Bool) :
    sumTo (K ^ n) (fun H => sumTo K (fun c => indB (E (runQ K nxt c k H) c))) ≤
      K * sumTo (K ^ n) (fun H => indB (E (runQ K nxt (rget K p H) k H) (rget K p H))) +
        sumTo (K ^ n) (fun H => sumTo K (fun c => indB (decide (p ∈ qposQ K nxt c k H)))) := by
  rw [← oracle_reprog_get hK hp (fun H c => indB (E (runQ K nxt c k H) c)), ← sumTo_add]
  refine sumTo_mono _ (fun H _ => ?_)
  rw [← sumTo_add]
  refine sumTo_mono _ (fun c hc => ?_)
  by_cases hq : p ∈ qposQ K nxt c k H
  · have e : indB (decide (p ∈ qposQ K nxt c k H)) = 1 := by simp [indB, hq]
    rw [e]; exact Nat.le_trans (indB_le _) (Nat.le_add_left _ _)
  · rw [(runQ_rset hK hc nxt c k H hq).1]; exact Nat.le_add_right _ _

theorem qposQ_length (K : Nat) (nxt : Nat → List Nat → Nat) (c : Nat) : ∀ k H, (qposQ K nxt c k H).length = k
  | 0, _ => rfl
  | k + 1, H => by simp only [qposQ, List.length_cons, qposQ_length K nxt c k H]

/-- Salts whose position lies in a list: at most `s` per listed position. -/
theorem salts_in {NS s : Nat} (pos : Nat → Nat) (hs : ∀ v, sumTo NS (fun σ => indB (decide (pos σ = v))) ≤ s) :
    ∀ L : List Nat, sumTo NS (fun σ => indB (decide (pos σ ∈ L))) ≤ s * L.length
  | [] => by simp [indB, sumTo_const]
  | a :: L => by
    have hpt : ∀ σ, indB (decide (pos σ ∈ a :: L)) ≤ indB (decide (pos σ = a)) + indB (decide (pos σ ∈ L)) :=
      fun σ => by
        by_cases h1 : pos σ = a
        · simp [indB, h1]
        · by_cases h2 : pos σ ∈ L <;> simp [indB, h1, h2]
    refine Nat.le_trans (sumTo_mono _ (fun σ _ => hpt σ)) ?_
    rw [sumTo_add, List.length_cons, Nat.mul_succ, Nat.add_comm (s * L.length)]
    exact Nat.add_le_add (hs a) (salts_in pos hs L)

/-- **A salted commitment from the oracle hides against an adaptive
    distinguisher of `k` queries**, its queries chosen after it sees the
    commitment: over the tables and the salts, its counts at two data
    differ by at most `K Kⁿ 2 s k`, each position taken by at most `s`
    salts of either datum; normalized, `2 s k / NS`. -/
theorem rom_hideQ {D : Type} {K n NS s k : Nat} (hK : 0 < K) (pos : D → Nat → Nat) (hpos : ∀ d σ, pos d σ < n)
    (hs : ∀ d v, sumTo NS (fun σ => indB (decide (pos d σ = v))) ≤ s)
    (nxt : Nat → List Nat → Nat) (E : List Nat → Nat → Bool) (d d' : D) :
    K * sumTo NS (fun σ => sumTo (K ^ n) (fun H =>
      indB (E (runQ K nxt (rget K (pos d σ) H) k H) (rget K (pos d σ) H)))) ≤
    K * sumTo NS (fun σ => sumTo (K ^ n) (fun H =>
      indB (E (runQ K nxt (rget K (pos d' σ) H) k H) (rget K (pos d' σ) H)))) +
      K * (K ^ n * (2 * (s * k))) := by
  have step : ∀ σ, K * sumTo (K ^ n) (fun H =>
      indB (E (runQ K nxt (rget K (pos d σ) H) k H) (rget K (pos d σ) H))) ≤
      K * sumTo (K ^ n) (fun H => indB (E (runQ K nxt (rget K (pos d' σ) H) k H) (rget K (pos d' σ) H))) +
        sumTo (K ^ n) (fun H => sumTo K (fun c => indB (decide (pos d' σ ∈ qposQ K nxt c k H)) +
          indB (decide (pos d σ ∈ qposQ K nxt c k H)))) := fun σ => by
    simp only [sumTo_add]
    rw [← Nat.add_assoc]
    exact Nat.le_trans (rom_offQ hK (hpos d σ) nxt E) (Nat.add_le_add_right (rom_offQ' hK (hpos d' σ) nxt E) _)
  rw [sumTo_mul, sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun σ _ => step σ)) ?_
  rw [sumTo_add]
  refine Nat.add_le_add_left ?_ _
  rw [sumTo_exch _ (K ^ n) NS]
  have hin : ∀ H, sumTo NS (fun σ => sumTo K (fun c => indB (decide (pos d' σ ∈ qposQ K nxt c k H)) +
      indB (decide (pos d σ ∈ qposQ K nxt c k H)))) ≤ K * (2 * (s * k)) := fun H => by
    rw [sumTo_exch _ K NS, ← sumTo_const (2 * (s * k)) K]
    refine sumTo_mono _ (fun c _ => ?_)
    rw [sumTo_add, show 2 * (s * k) = s * k + s * k by omega]
    have h1 := salts_in (pos d') (hs d') (qposQ K nxt c k H)
    have h2 := salts_in (pos d) (hs d) (qposQ K nxt c k H)
    rw [qposQ_length] at h1 h2
    exact Nat.add_le_add h1 h2
  refine Nat.le_trans (sumTo_mono _ (fun H _ => hin H)) (Nat.le_of_eq ?_)
  rw [sumTo_const, Nat.mul_left_comm]
/-- **A commitment from the oracle hides given its openings, against `k`
    adaptive queries**: the salt split into the part the opening shows
    (`σo`) and the part it hides (`σh`); the
    commitment the oracle's answer at `pos d σo σh`; the opening proof
    `g (op d) σo`, reading only the opened values and the shown salts.  The
    distinguisher sees the opening, the commitment and a run of `k` queries
    chosen after both.  At two data with the same opened values, its counts
    differ by at most `K NSo Kⁿ 2 s k`, `s` hidden salts at most taking a
    position; normalized, `2 s k / NSh`. -/
theorem rom_hidePfQ {D O P : Type} {K n NSo NSh s k : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hpos : ∀ d σo σh, pos d σo σh < n) (op : D → O) (g : O → Nat → P)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxt : P → Nat → List Nat → Nat) (E : P → List Nat → Nat → Bool) (d d' : D) (hop : op d = op d') :
    K * sumTo NSo (fun σo => sumTo NSh (fun σh => sumTo (K ^ n) (fun H =>
      indB (E (g (op d) σo) (runQ K (nxt (g (op d) σo)) (rget K (pos d σo σh) H) k H) (rget K (pos d σo σh) H))))) ≤
    K * sumTo NSo (fun σo => sumTo NSh (fun σh => sumTo (K ^ n) (fun H =>
      indB (E (g (op d') σo) (runQ K (nxt (g (op d') σo)) (rget K (pos d' σo σh) H) k H)
        (rget K (pos d' σo σh) H))))) +
      K * (NSo * (K ^ n * (2 * (s * k)))) := by
  rw [hop, sumTo_mul, sumTo_mul, ← sumTo_const (K ^ n * (2 * (s * k))) NSo, sumTo_mul, ← sumTo_add]
  refine sumTo_mono _ (fun σo _ => ?_)
  exact rom_hideQ hK (fun d σh => pos d σo σh) (fun d σh => hpos d σo σh) (fun d v => hs d σo v)
    (nxt (g (op d') σo)) (E (g (op d') σo)) d d'

/-- **A commitment hides up to `η`**: over the salt, the counts of any event
    at two data differ by at most `η`, one way (the other by symmetry). -/
def ComHidesA {D C : Type} (NS η : Nat) (Com : D → Nat → C) : Prop :=
  ∀ (d d' : D) (E : C → Bool), sumTo NS (fun σ => indB (E (Com d σ))) ≤ sumTo NS (fun σ => indB (E (Com d' σ))) + η

/-- **Hiding given the openings, up to `η`.** -/
def ComPfHidesA {D O Pp : Type} (NS η : Nat) (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (op : D → O) : Prop :=
  ∀ (d d' : D), op d = op d' → ∀ E : Nat → Pp → Bool,
    sumTo NS (fun σ => indB (E (Com d σ) (Pf d σ))) ≤ sumTo NS (fun σ => indB (E (Com d' σ) (Pf d' σ))) + η

theorem ComHides.approx {D C : Type} {NS : Nat} {Com : D → Nat → C} (h : ComHides NS Com) : ComHidesA NS 0 Com :=
  fun d d' E => Nat.le_of_eq (h d d' E)

theorem ComPfHides.approx {D O Pp : Type} {NS : Nat} {Com : D → Nat → Nat} {Pf : D → Nat → Pp} {op : D → O}
    (h : ComPfHides NS Com Pf op) : ComPfHidesA NS 0 Com Pf op :=
  fun d d' hd E => Nat.le_of_eq (h d d' hd E)

/-- **`open_real` with hiding up to `η`**, both ways: the real count and the
    view events' differ by at most `η` per draw. -/
theorem open_realA {PV PB D O Pp : Type} {NS NR m η : Nat} (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (op : D → O)
    (sd : O → D) (d0 : D) (hcom : ComHidesA NS η Com) (hpf : ComPfHidesA NS η Com Pf op)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (v : Nat → (Nat → Tup) → TViewN PV PB) (hvo : ∀ r t, v r t = none ∨ ov (v r t) = some (op (main t r)))
    (F : Nat → Option Pp → TViewN PV PB → Bool) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (F (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ)) (v r t))))) ≤
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (openEv Com Pf sd d0 ov F σ (v r t))))) +
      NR * (Q4 ^ m * η) ∧
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (openEv Com Pf sd d0 ov F σ (v r t))))) ≤
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (F (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ)) (v r t))))) +
      NR * (Q4 ^ m * η) := by
  have key : ∀ r t, sumTo NS (fun σ => indB (F (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ))
      (v r t))) ≤ sumTo NS (fun σ => indB (openEv Com Pf sd d0 ov F σ (v r t))) + η ∧
      sumTo NS (fun σ => indB (openEv Com Pf sd d0 ov F σ (v r t))) ≤
      sumTo NS (fun σ => indB (F (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ)) (v r t))) + η := by
    intro r t
    rcases hvo r t with e | e
    · rw [e]
      unfold openEv
      rw [hovn]
      exact ⟨hcom (main t r) d0 (fun mm => F mm none none), hcom d0 (main t r) (fun mm => F mm none none)⟩
    · unfold openEv
      rw [e]
      exact ⟨hpf (main t r) (sd (op (main t r))) (hsd t r).symm (fun mm p => F mm (some p) (v r t)),
        hpf (sd (op (main t r))) (main t r) (hsd t r) (fun mm p => F mm (some p) (v r t))⟩
  have fin : ∀ (a b : Nat → (Nat → Tup) → Nat), (∀ r t, a r t ≤ b r t + η) →
      sumTo NR (fun r => sumN m (fun t => a r t)) ≤ sumTo NR (fun r => sumN m (fun t => b r t)) + NR * (Q4 ^ m * η) :=
    fun a b h => by
      rw [← sumN_const m η, ← sumTo_const _ NR, ← sumTo_add]
      refine sumTo_mono _ (fun r _ => ?_)
      refine Nat.le_trans (sumN_mono m (fun t => h r t)) (Nat.le_of_eq ?_)
      exact sm_add (sumN m) (fun N f => (sumTo_sumN m N f).symm) _ _
  simp only [sig_in]
  exact ⟨fin _ _ (fun r t => (key r t).1), fin _ _ (fun r t => (key r t).2)⟩

/-- `open_real_t` with hiding up to `η`. -/
theorem open_real_tA {PV PB D O Pp : Type} {NR m NS η : Nat} (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (op : D → O)
    (sd : O → D) (d0 : D) (ov : TViewN PV PB → Option O) (main : (Nat → Tup) → Nat → D)
    (rv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r)) (hcom : ComHidesA NS η Com)
    (hpf : ComPfHidesA NS η Com Pf op) (hovn : ov none = none)
    (hrvo : ∀ α β r t, rv α β r t = none ∨ ov (rv α β r t) = some (op (main t r)))
    (F : Nat → Nat → Option Pp × TViewN PV PB → Bool) :
    let L := sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
        ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          rv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))
    let R := sumTo NS (fun σ => tsumN NR m (fun α β r t =>
      indB (genB β && openG Com Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α) (rv α β r t))))
    L ≤ R + Q4 * Q4 * (NR * (Q4 ^ m * η)) ∧ R ≤ L + Q4 * Q4 * (NR * (Q4 ^ m * η)) := by
  intro L R
  have hR : R = sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (openEv Com Pf sd d0 ov (fun mm p w => genB (efOf (c % Q4)) && F c mm (p, w)) σ
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) := by
    show sumTo NS (fun σ => tsumN NR m (fun α β r t =>
      indB (genB β && openG Com Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α) (rv α β r t)))) = _
    rw [sumTo_exch _ NS (Q4 * Q4)]
    refine sumTo_congr _ (fun σ _ => ?_)
    rw [← csum_tsumN rv (fun c v => openG Com Pf sd d0 ov F σ c v)]
    exact sumTo_congr _ (fun c _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
      (sumN_mono m (fun t => Nat.le_of_eq (by rw [openEv_and]; rfl)))
      (sumN_mono m (fun t => Nat.le_of_eq (by rw [openEv_and]; rfl))))) |>.symm
  rw [hR]
  have hc := fun c => open_realA (NR := NR) (m := m) Com Pf op sd d0 hcom hpf ov hovn main hsd
    (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hrvo _ _ r t)
    (fun mm p w => genB (efOf (c % Q4)) && F c mm (p, w))
  rw [← sumTo_const (NR * (Q4 ^ m * η)) (Q4 * Q4), ← sumTo_add, ← sumTo_add]
  exact ⟨sumTo_mono _ (fun c _ => (hc c).1), sumTo_mono _ (fun c _ => (hc c).2)⟩
/-- **`fs_open` with the commitment hiding up to `η`** (`ComHidesA`,
    `ComPfHidesA`): the error gains `Q4² NR Q4^m η`, each draw's hiding
    slack.  For a commitment drawn from the oracle, the distinguisher's
    queries into its table carried in the proof, `fs_openROM`. -/
theorem fs_openA {PV PB D O Pp : Type} {NR m NS n e1 e2 η : Nat} (Com : D → Nat → Nat) (Pf : D → Nat → Pp)
    (op : D → O) (sd : O → D) (d0 : D) (hcom : ComHidesA NS η Com)
    (hpf : ComPfHidesA NS η Com Pf op) (hrange : ∀ d σ, Com d σ < n)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (sop : Nat → (Nat → Tup) → O) {rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB}
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (hrvo : ∀ α β r t, rv α β r t = none ∨ ov (rv α β r t) = some (op (main t r)))
    (hsvo : ∀ α β r t, ov (sv α β r t) = some (sop r t))
    (E : Nat → Nat → Option Pp × TViewN PV PB → Bool) :
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)).map (fun _ => Pf (main t r) σ),
          rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)))))) ≤
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sd (sop r t)) σ) H c) (Com (sd (sop r t)) σ)
        (some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ n * (NS * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * η))) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sd (sop r t)) σ) H c) (Com (sd (sop r t)) σ)
        (some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)).map (fun _ => Pf (main t r) σ),
          rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)))))) +
    (Q4 * Q4) ^ n * (NS * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * η))) := by
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × (Nat → Tup) → Nat),
      sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => sumTo N (fun i => f i (σ, r, t))))) =
        sumTo N (fun i => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => f i (σ, r, t))))) :=
    fun N f => sm_exch (fun i σ r t => f i (σ, r, t))
  have core : ∀ F : Nat → Nat → Option Pp × TViewN PV PB → Bool,
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
          ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf (main t r) σ),
            rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) ≤
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (sd (sop r t)) σ)
          (some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) + (NS * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * η))) ∧
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (sd (sop r t)) σ)
          (some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) ≤
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
          ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf (main t r) σ),
            rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) + (NS * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * η))) := by
    intro F
    have ha := open_real_tA (NR := NR) (m := m) Com Pf op sd d0 ov main rv hsd hcom hpf hovn hrvo F
    rw [open_sim_t Com Pf sd d0 ov sop sv hsvo F]
    have hb : ∀ σ, tsumN NR m (fun α β r t => indB (genB β && openG Com Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α)
        (rv α β r t))) ≤ tsumN NR m (fun α β r t => indB (genB β && openG Com Pf sd d0 ov F σ
          (efIdx β + Q4 * efIdx α) (sv α β r t))) + (e1 + e2) ∧
        tsumN NR m (fun α β r t => indB (genB β && openG Com Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α)
          (sv α β r t))) ≤ tsumN NR m (fun α β r t => indB (genB β && openG Com Pf sd d0 ov F σ
            (efIdx β + Q4 * efIdx α) (rv α β r t))) + (e1 + e2) := fun σ =>
      tsumN_ab rv sv hrv hsv h1' h2' _
    have s1 := sumTo_mono NS (fun σ _ => (hb σ).1)
    have s2 := sumTo_mono NS (fun σ _ => (hb σ).2)
    rw [sumTo_add, sumTo_const] at s1 s2
    dsimp only at ha
    obtain ⟨ha1, ha2⟩ := ha
    constructor <;> omega
  refine ⟨fs_zk (X := Nat × Nat × (Nat → Tup)) (K := Q4 * Q4) (n := n) (ε := (NS * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * η))))
    (Nat.mul_pos Q4_pos Q4_pos) (fun g => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ, r, t))))) hsm
    (fun x => Com (main x.2.2 x.2.1) x.1) (fun x => Com (sd (sop x.2.1 x.2.2)) x.1) (fun x => hrange _ _)
    (fun c x => ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2)).map (fun _ => Pf (main x.2.2 x.2.1) x.1),
      rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c x => (some (Pf (sd (sop x.2.1 x.2.2)) x.1), sv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c => genB (efOf (c % Q4))) (fun F => (core F).1) (fun H mm _ w => E H mm w),
    fs_zk' (X := Nat × Nat × (Nat → Tup)) (K := Q4 * Q4) (n := n) (ε := (NS * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * η))))
    (Nat.mul_pos Q4_pos Q4_pos) (fun g => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ, r, t))))) hsm
    (fun x => Com (main x.2.2 x.2.1) x.1) (fun x => Com (sd (sop x.2.1 x.2.2)) x.1) (fun x => hrange _ _)
    (fun c x => ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2)).map (fun _ => Pf (main x.2.2 x.2.1) x.1),
      rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c x => (some (Pf (sd (sop x.2.1 x.2.2)) x.1), sv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c => genB (efOf (c % Q4))) (fun F => (core F).2) (fun H mm _ w => E H mm w)⟩

/-- The salt `σ'` of a commitment from the oracle, three parts: the hidden
    salt, the shown salt, the commitment's table. -/
def saltH (NSh : Nat) (σ' : Nat) : Nat := σ' % NSh
def saltO (NSh NSo : Nat) (σ' : Nat) : Nat := σ' / NSh % NSo
def saltT (NSh NSo : Nat) (σ' : Nat) : Nat := σ' / NSh / NSo

/-- **A commitment drawn from the oracle**: the commitment table's answer
    at the position the data and both salt parts give. -/
def comR {D : Type} (K NSh NSo : Nat) (pos : D → Nat → Nat → Nat) (d : D) (σ' : Nat) : Nat :=
  rget K (pos d (saltO NSh NSo σ') (saltH NSh σ')) (saltT NSh NSo σ')

/-- **Its opening, with the distinguisher's `k` queries into its table**:
    the opening proof reads the opened values and the shown salt; the
    queries are chosen after the opening and the commitment (`nxt`). -/
def pfR {D O P : Type} (K NSh NSo k : Nat) (pos : D → Nat → Nat → Nat) (op : D → O) (g : O → Nat → P)
    (nxt : P → Nat → List Nat → Nat) (d : D) (σ' : Nat) : P × List Nat :=
  (g (op d) (saltO NSh NSo σ'),
   runQ K (nxt (g (op d) (saltO NSh NSo σ'))) (comR K NSh NSo pos d σ') k (saltT NSh NSo σ'))

theorem sum_salt (NSh NSo T : Nat) (f : Nat → Nat) :
    sumTo (NSh * (NSo * T)) f =
      sumTo T (fun h => sumTo NSo (fun o => sumTo NSh (fun σh => f (σh + NSh * (o + NSo * h))))) := by
  rw [sumTo_split NSh f (NSo * T), sumTo_split NSo _ T]

theorem salt_dec {NSh NSo σh o h : Nat} (hh : σh < NSh) (ho : o < NSo) :
    saltH NSh (σh + NSh * (o + NSo * h)) = σh ∧ saltO NSh NSo (σh + NSh * (o + NSo * h)) = o ∧
      saltT NSh NSo (σh + NSh * (o + NSo * h)) = h := by
  have hp : 0 < NSh := by omega
  have hq : 0 < NSo := by omega
  have e1 : (σh + NSh * (o + NSo * h)) / NSh = o + NSo * h := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hh, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · unfold saltH; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hh]
  · unfold saltO; rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ho]
  · unfold saltT; rw [e1, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt ho, Nat.zero_add]

/-- The salts in the order the ROM lemmas sum them: shown, hidden, table. -/
theorem sum_salt' (NSh NSo T : Nat) (f : Nat → Nat → Nat → Nat) :
    sumTo T (fun h => sumTo NSo (fun o => sumTo NSh (fun σh => f h o σh))) =
      sumTo NSo (fun o => sumTo NSh (fun σh => sumTo T (fun h => f h o σh))) := by
  rw [sumTo_exch _ NSo T]
  exact sumTo_congr _ (fun o _ => sumTo_exch _ NSh T)

theorem sum_salt_eq (NSh NSo T : Nat) (f : Nat → Nat) :
    sumTo (NSh * (NSo * T)) f =
      sumTo NSo (fun o => sumTo NSh (fun σh => sumTo T (fun h => f (σh + NSh * (o + NSo * h))))) := by
  rw [sum_salt]; exact sum_salt' NSh NSo T (fun h o σh => f (σh + NSh * (o + NSo * h)))

/-- **The bare commitment from the oracle hides exactly**, against events
    of its value alone. -/
theorem comR_hides {D : Type} {K n NSh NSo : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hpos : ∀ d σo σh, pos d σo σh < n) : ComHides (NSh * (NSo * K ^ n)) (comR K NSh NSo pos) := by
  intro d d' E
  have key : ∀ p, p < n → sumTo (K ^ n) (fun H => indB (E (rget K p H))) =
      sumTo (K ^ n) (fun H => sumTo K (fun c => indB (E c))) / K := fun p hp => by
    have := rom_off (n := n) hK hp [] List.not_mem_nil (fun _ c => E c)
    rw [← this, Nat.mul_div_cancel_left _ hK]
  rw [sum_salt_eq, sum_salt_eq]
  refine sumTo_congr _ (fun o ho => sumTo_congr _ (fun σh hh => ?_))
  have e := fun (dd : D) => sumTo_congr (K ^ n) (fun h (_ : h < K ^ n) =>
    show indB (E (comR K NSh NSo pos dd (σh + NSh * (o + NSo * h)))) = indB (E (rget K (pos dd o σh) h)) by
      unfold comR; obtain ⟨a, b, c⟩ := salt_dec (h := h) hh ho; rw [a, b, c])
  rw [e d, e d', key _ (hpos d o σh), key _ (hpos d' o σh)]

/-- **The opened commitment from the oracle hides up to `rom_hidePfQ`'s
    slack**, against the distinguisher's `k` queries into its table. -/
theorem pfR_hidesA {D O P : Type} {K n NSh NSo s k : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hpos : ∀ d σo σh, pos d σo σh < n) (op : D → O) (g : O → Nat → P)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s) (nxt : P → Nat → List Nat → Nat) :
    ComPfHidesA (NSh * (NSo * K ^ n)) (NSo * (K ^ n * (2 * (s * k)))) (comR K NSh NSo pos)
      (pfR K NSh NSo k pos op g nxt) op := by
  intro d d' hop E
  have h := rom_hidePfQ (NSo := NSo) (k := k) hK pos hpos op g hs nxt (fun pf ans c => E c (pf, ans)) d d' hop
  rw [← Nat.mul_add] at h
  have h' := Nat.le_of_mul_le_mul_left h hK
  rw [sum_salt_eq, sum_salt_eq]
  have e := fun (dd : D) => sumTo_congr NSo (fun o (ho : o < NSo) => sumTo_congr NSh (fun σh (hh : σh < NSh) =>
    sumTo_congr (K ^ n) (fun h (_ : h < K ^ n) =>
    show indB (E (comR K NSh NSo pos dd (σh + NSh * (o + NSo * h))) (pfR K NSh NSo k pos op g nxt dd
        (σh + NSh * (o + NSo * h)))) =
      indB (E (rget K (pos dd o σh) h) (g (op dd) o, runQ K (nxt (g (op dd) o)) (rget K (pos dd o σh) h) k h)) by
      unfold pfR comR; obtain ⟨a, b, c⟩ := salt_dec (h := h) hh ho; rw [a, b, c])))
  rw [e d, e d']
  exact h'
/-- **One Fiat–Shamir round with the commitment drawn from the oracle**
    (`fs_openA` over `comR`, `pfR`): the commitment the answer of its own
    table at a salted position, the salt split into its shown part
    the proof shows and the hidden rest; the distinguisher, besides the
    Fiat–Shamir table, the commitment and the opening, sees the answers to
    `k` queries into the commitment's table, chosen after the opening and
    the commitment (`nxt`).  The bound gains `Q4² NR Q4^m NSo Kc^nc 2 s k`,
    normalized `2 s k / NSh` a draw.  One round, the commitment table apart
    from the Fiat–Shamir table as a domain-separated oracle's. -/
theorem fs_openROM {PV PB D O P : Type} {NR m e1 e2 Kc nc NSh NSo s k : Nat} (hKc : 0 < Kc)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < nc) (g : O → Nat → P)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s) (nxt : P → Nat → List Nat → Nat)
    (op : D → O) (sd : O → D) (d0 : D)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (sop : Nat → (Nat → Tup) → O) {rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB}
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (hrvo : ∀ α β r t, rv α β r t = none ∨ ov (rv α β r t) = some (op (main t r)))
    (hsvo : ∀ α β r t, ov (sv α β r t) = some (sop r t))
    (E : Nat → Nat → Option (P × List Nat) × TViewN PV PB → Bool) :
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ Kc) (fun H => sumTo (NSh * (NSo * Kc ^ nc)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H % Q4)) && E H ((comR Kc NSh NSo pos) (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H % Q4))
            r t)).map (fun _ => (pfR Kc NSh NSo k pos op g nxt) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H % Q4))
            r t)))))) ≤
    sumTo ((Q4 * Q4) ^ Kc) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSh * (NSo * Kc ^ nc)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) ((comR Kc NSh NSo pos) (sd (sop r t)) σ) H c) ((comR Kc NSh NSo pos) (sd (sop r t)) σ)
        (some ((pfR Kc NSh NSo k pos op g nxt) (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ Kc * ((NSh * (NSo * Kc ^ nc)) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * (NSo * (Kc ^ nc * (2 * (s * k))))))) ∧
    sumTo ((Q4 * Q4) ^ Kc) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSh * (NSo * Kc ^ nc)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) ((comR Kc NSh NSo pos) (sd (sop r t)) σ) H c) ((comR Kc NSh NSo pos) (sd (sop r t)) σ)
        (some ((pfR Kc NSh NSo k pos op g nxt) (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ Kc) (fun H => sumTo (NSh * (NSo * Kc ^ nc)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H % Q4)) && E H ((comR Kc NSh NSo pos) (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H % Q4))
            r t)).map (fun _ => (pfR Kc NSh NSo k pos op g nxt) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comR Kc NSh NSo pos) (main t r) σ) H % Q4))
            r t)))))) +
    (Q4 * Q4) ^ Kc * ((NSh * (NSo * Kc ^ nc)) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * (NSo * (Kc ^ nc * (2 * (s * k))))))) := by
  have hcom : ComHidesA (NSh * (NSo * Kc ^ nc)) (NSo * (Kc ^ nc * (2 * (s * k)))) (comR Kc NSh NSo pos) := fun d d' E =>
    Nat.le_trans (Nat.le_of_eq (comR_hides hKc pos hpos d d' E)) (Nat.le_add_right _ _)
  have hrange : ∀ d σ, comR Kc NSh NSo pos d σ < Kc := fun d σ => Nat.mod_lt _ hKc
  exact fs_openA (comR Kc NSh NSo pos) (pfR Kc NSh NSo k pos op g nxt) op sd d0 hcom (pfR_hidesA hKc pos hpos op g hs nxt) hrange ov hovn main hsd sop h1 h2 hrv hsv hrvo hsvo E

/-- **Re-randomizing one answer is a bijection**: over the tables and the
    answers `u` set at `p`, the pair (the old answer at `p`, the new table) is
    every (answer, table) pair once. -/
theorem reprog_swap {K n p : Nat} (hK : 0 < K) (hp : p < n) (f : Nat → Nat → Nat) :
    sumTo (K ^ n) (fun H => sumTo K (fun u => f (rget K p H) (rset K p H u))) =
      sumTo (K ^ n) (fun H => sumTo K (fun c => f c H)) := by
  have hn : K ^ n = K ^ p * (K * K ^ (n - p - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
  have hpos : 0 < K ^ p := Nat.pow_pos hK
  rw [hn, sumTo_split (K ^ p) _ (K * K ^ (n - p - 1)), sumTo_split (K ^ p) _ (K * K ^ (n - p - 1))]
  rw [sumTo_split K _ (K ^ (n - p - 1)), sumTo_split K _ (K ^ (n - p - 1))]
  refine sumTo_congr _ (fun hi _ => ?_)
  -- left: Σ_d Σ_lo Σ_u f(d, lo + K^p(u + K hi)); right: Σ_d Σ_lo Σ_c f(c, lo + K^p(d + K hi))
  have hl : ∀ d, d < K → sumTo (K ^ p) (fun lo => sumTo K (fun u =>
      f (rget K p (lo + K ^ p * (d + K * hi))) (rset K p (lo + K ^ p * (d + K * hi)) u))) =
      sumTo (K ^ p) (fun lo => sumTo K (fun u => f d (lo + K ^ p * (u + K * hi)))) := fun d hd =>
    sumTo_congr _ (fun lo hlo => sumTo_congr _ (fun u _ => by
      rw [(split_digit hK hlo hd).1, (split_digit hK hlo hd).2 u]))
  rw [sumTo_congr K hl]
  rw [sumTo_congr K (fun d _ => sumTo_exch (fun lo c => f c (lo + K ^ p * (d + K * hi))) K (K ^ p))]
  rw [sumTo_exch _ K K]
  exact sumTo_congr _ (fun d _ => sumTo_exch (fun lo u => f d (lo + K ^ p * (u + K * hi))) K (K ^ p))

/-- The commitment with one more salt digit `u`, which it ignores. -/
def comI {D : Type} (K NSh NSo : Nat) (pos : D → Nat → Nat → Nat) (d : D) (σ : Nat) : Nat :=
  comR K NSh NSo pos d (σ / K)

/-- **The ideal opening**: the distinguisher's queries answered on the
    commitment's table with the commitment's own answer re-randomized to the
    extra digit `u`. -/
def pfI {D O P : Type} (K NSh NSo k : Nat) (pos : D → Nat → Nat → Nat) (op : D → O) (g : O → Nat → P)
    (nxt : P → Nat → List Nat → Nat) (d : D) (σ : Nat) : P × List Nat :=
  (g (op d) (saltO NSh NSo (σ / K)),
   runQ K (nxt (g (op d) (saltO NSh NSo (σ / K)))) (comI K NSh NSo pos d σ) k
     (rset K (pos d (saltO NSh NSo (σ / K)) (saltH NSh (σ / K))) (saltT NSh NSo (σ / K)) (σ % K)))

theorem sum_digit (K N : Nat) (f : Nat → Nat) :
    sumTo (N * K) f = sumTo N (fun σ => sumTo K (fun u => f (u + K * σ))) := by
  rw [Nat.mul_comm]; exact sumTo_split K f N

theorem digit_dec {K σ u : Nat} (hu : u < K) : (u + K * σ) / K = σ ∧ (u + K * σ) % K = u := by
  have hK : 0 < K := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hu, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]

/-- **The ideal opening hides exactly**: the re-randomized table is
    uniform and apart from the commitment's answer (`reprog_swap`). -/
theorem pfI_hides {D O P : Type} {K n NSh NSo k : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hpos : ∀ d σo σh, pos d σo σh < n) (op : D → O) (g : O → Nat → P) (nxt : P → Nat → List Nat → Nat) :
    ComPfHides (NSh * (NSo * K ^ n) * K) (comI K NSh NSo pos) (pfI K NSh NSo k pos op g nxt) op := by
  intro d d' hop E
  have key : ∀ dd : D, op dd = op d → sumTo (NSh * (NSo * K ^ n) * K) (fun σ =>
      indB (E (comI K NSh NSo pos dd σ) (pfI K NSh NSo k pos op g nxt dd σ))) =
      sumTo NSo (fun o => sumTo NSh (fun _ => sumTo (K ^ n) (fun H => sumTo K (fun c =>
        indB (E c (g (op d) o, runQ K (nxt (g (op d) o)) c k H)))))) := fun dd hdd => by
    rw [sum_digit, sum_salt_eq]
    refine sumTo_congr _ (fun o ho => sumTo_congr _ (fun σh hh => ?_))
    rw [← reprog_swap hK (hpos dd o σh) (fun c H => indB (E c (g (op d) o, runQ K (nxt (g (op d) o)) c k H)))]
    refine sumTo_congr _ (fun h _ => sumTo_congr _ (fun u hu => ?_))
    obtain ⟨e1, e2⟩ := digit_dec (σ := σh + NSh * (o + NSo * h)) hu
    obtain ⟨a, b, c⟩ := salt_dec (h := h) hh ho
    simp only [pfI, comI, comR, e1, e2, a, b, c, hdd]
  rw [key d rfl, key d' hop.symm]

/-- **The real and the ideal openings differ only where a query hits the
    commitment's answer**: `K` times the count with the real opening is at
    most the count with the ideal one plus `K` per hitting draw, and back. -/
theorem pfR_pfI {D O P : Type} {K NSh NSo k : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (op : D → O) (g : O → Nat → P) (nxt : P → Nat → List Nat → Nat) (F : Nat → P × List Nat → Bool) (d : D)
    (σ : Nat) :
    let hit := decide (pos d (saltO NSh NSo σ) (saltH NSh σ) ∈
      qposQ K (nxt (g (op d) (saltO NSh NSo σ))) (comR K NSh NSo pos d σ) k (saltT NSh NSo σ))
    K * indB (F (comR K NSh NSo pos d σ) (pfR K NSh NSo k pos op g nxt d σ)) ≤
      sumTo K (fun u => indB (F (comI K NSh NSo pos d (u + K * σ)) (pfI K NSh NSo k pos op g nxt d (u + K * σ)))) +
        K * indB hit ∧
    sumTo K (fun u => indB (F (comI K NSh NSo pos d (u + K * σ)) (pfI K NSh NSo k pos op g nxt d (u + K * σ)))) ≤
      K * indB (F (comR K NSh NSo pos d σ) (pfR K NSh NSo k pos op g nxt d σ)) + K * indB hit := by
  intro hit
  have eq : ∀ u, u < K → (comI K NSh NSo pos d (u + K * σ), pfI K NSh NSo k pos op g nxt d (u + K * σ)) =
      (comR K NSh NSo pos d σ, (g (op d) (saltO NSh NSo σ), runQ K (nxt (g (op d) (saltO NSh NSo σ)))
        (comR K NSh NSo pos d σ) k (rset K (pos d (saltO NSh NSo σ) (saltH NSh σ)) (saltT NSh NSo σ) u))) :=
    fun u hu => by obtain ⟨e1, e2⟩ := digit_dec (σ := σ) hu; simp only [pfI, comI, e1, e2]
  cases hh : hit
  · have hq : pos d (saltO NSh NSo σ) (saltH NSh σ) ∉
        qposQ K (nxt (g (op d) (saltO NSh NSo σ))) (comR K NSh NSo pos d σ) k (saltT NSh NSo σ) := by
      simpa [hit] using hh
    have e : sumTo K (fun u => indB (F (comI K NSh NSo pos d (u + K * σ)) (pfI K NSh NSo k pos op g nxt d (u + K * σ)))) =
        K * indB (F (comR K NSh NSo pos d σ) (pfR K NSh NSo k pos op g nxt d σ)) := by
      rw [show K * indB (F (comR K NSh NSo pos d σ) (pfR K NSh NSo k pos op g nxt d σ)) =
        sumTo K (fun _ => indB (F (comR K NSh NSo pos d σ) (pfR K NSh NSo k pos op g nxt d σ))) from
        (sumTo_const _ K).symm]
      refine sumTo_congr _ (fun u hu => ?_)
      have e3 := eq u hu
      rw [Prod.mk.injEq] at e3
      rw [e3.1, e3.2, (runQ_rset hK hu _ _ k _ hq).1]
      rfl
    rw [e]; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · have b1 : K * indB (F (comR K NSh NSo pos d σ) (pfR K NSh NSo k pos op g nxt d σ)) ≤ K * indB true :=
      Nat.mul_le_mul_left _ (indB_le _)
    have b2 : sumTo K (fun u => indB (F (comI K NSh NSo pos d (u + K * σ))
        (pfI K NSh NSo k pos op g nxt d (u + K * σ)))) ≤ K * indB true := by
      refine Nat.le_trans (sumTo_mono _ (fun u _ => indB_le _)) (Nat.le_of_eq ?_)
      rw [sumTo_const]; rfl
    exact ⟨Nat.le_trans b1 (Nat.le_add_left _ _), Nat.le_trans b2 (Nat.le_add_left _ _)⟩

/-- The bare commitment with the extra digit hides exactly. -/
theorem comI_hides {D : Type} {K n NSh NSo : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hpos : ∀ d σo σh, pos d σo σh < n) : ComHides (NSh * (NSo * K ^ n) * K) (comI K NSh NSo pos) := by
  intro d d' E
  have e : ∀ dd : D, sumTo (NSh * (NSo * K ^ n) * K) (fun σ => indB (E (comI K NSh NSo pos dd σ))) =
      K * sumTo (NSh * (NSo * K ^ n)) (fun σ => indB (E (comR K NSh NSo pos dd σ))) := fun dd => by
    rw [sum_digit, sumTo_mul]
    refine sumTo_congr _ (fun σ _ => ?_)
    rw [show K * indB (E (comR K NSh NSo pos dd σ)) = sumTo K (fun _ => indB (E (comR K NSh NSo pos dd σ))) from
      (sumTo_const _ K).symm]
    exact sumTo_congr _ (fun u hu => by simp only [comI, (digit_dec (σ := σ) hu).1])
  rw [e d, e d', comR_hides hK pos hpos d d' E]
/-- Setting an answer and setting it back restores the table. -/
theorem rset_back {K p H u : Nat} (hK : 0 < K) (hu : u < K) :
    rset K p (rset K p H u) (rget K p H) = H := by
  have hpos : 0 < K ^ p := Nat.pow_pos hK
  have h1 := Nat.mod_add_div H (K ^ p)
  have h2 := Nat.mod_add_div (H / K ^ p) K
  have hH : H = H % K ^ p + K ^ p * (H / K ^ p % K + K * (H / K ^ p / K)) := by rw [h2]; exact h1.symm
  obtain ⟨g0, s0⟩ := split_digit (m := p) hK (Nat.mod_lt H hpos) (Nat.mod_lt (H / K ^ p) hK) (hi := H / K ^ p / K)
  rw [← hH] at g0 s0
  rw [s0 u, (split_digit hK (Nat.mod_lt H hpos) hu).2, g0, ← hH]

/-- **Whether a run hits `p` does not read the answer at `p`.** -/
theorem hit_rset {K p a : Nat} (hK : 0 < K) (ha : a < K) (nxt : Nat → List Nat → Nat) (c k H : Nat) :
    (p ∈ qposQ K nxt c k (rset K p H a)) ↔ (p ∈ qposQ K nxt c k H) := by
  constructor
  · intro h
    by_cases h' : p ∈ qposQ K nxt c k H
    · exact h'
    · rw [(runQ_rset hK ha nxt c k H h').2] at h
      exact absurd h h'
  · intro h
    by_cases h' : p ∈ qposQ K nxt c k (rset K p H a)
    · exact h'
    · have hb := (runQ_rset (a := rget K p H) hK (Nat.mod_lt _ hK) nxt c k (rset K p H a) h').2
      rw [rset_back hK ha] at hb
      rw [← hb] at h'
      exact absurd h h'

/-- **The hitting draws are few**: over the salts and the commitment's
    table, the runs that query the commitment's own position number at most
    `NSo Kⁿ s k`; normalized, `s k / NSh`. -/
theorem hit_bound {D P : Type} {K n NSh NSo s k : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hpos : ∀ d σo σh, pos d σo σh < n)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (pf : Nat → P) (nxt : P → Nat → List Nat → Nat) (d : D) :
    sumTo (NSh * (NSo * K ^ n)) (fun σ => indB (decide (pos d (saltO NSh NSo σ) (saltH NSh σ) ∈
      qposQ K (nxt (pf (saltO NSh NSo σ))) (comR K NSh NSo pos d σ) k (saltT NSh NSo σ)))) ≤
      NSo * (K ^ n * (s * k)) := by
  rw [sum_salt_eq]
  have key : ∀ o σh, K * sumTo (K ^ n) (fun h => indB (decide (pos d o σh ∈
      qposQ K (nxt (pf o)) (rget K (pos d o σh) h) k h))) =
      sumTo (K ^ n) (fun H => sumTo K (fun c => indB (decide (pos d o σh ∈ qposQ K (nxt (pf o)) c k H))))
      := fun o σh => by
    rw [← reprog_swap hK (hpos d o σh) (fun c H => indB (decide (pos d o σh ∈ qposQ K (nxt (pf o)) c k H))),
      sumTo_mul]
    refine sumTo_congr _ (fun h _ => ?_)
    rw [show K * indB (decide (pos d o σh ∈ qposQ K (nxt (pf o)) (rget K (pos d o σh) h) k h)) =
      sumTo K (fun _ => indB (decide (pos d o σh ∈ qposQ K (nxt (pf o)) (rget K (pos d o σh) h) k h))) from
      (sumTo_const _ K).symm]
    refine sumTo_congr _ (fun u hu => ?_)
    simp only [hit_rset hK hu]
  have per : ∀ o, o < NSo → K * sumTo NSh (fun σh => sumTo (K ^ n) (fun h => indB (decide (pos d o σh ∈
      qposQ K (nxt (pf o)) (rget K (pos d o σh) h) k h)))) ≤ K * (K ^ n * (s * k)) := fun o ho => by
    rw [sumTo_mul, sumTo_congr _ (fun σh _ => key o σh), sumTo_exch _ (K ^ n) NSh]
    rw [show K * (K ^ n * (s * k)) = sumTo (K ^ n) (fun _ => K * (s * k)) by rw [sumTo_const]; ac_rfl]
    refine sumTo_mono _ (fun H _ => ?_)
    rw [sumTo_exch _ K NSh, ← sumTo_const (s * k) K]
    refine sumTo_mono _ (fun c _ => ?_)
    have h := salts_in (pos d o) (hs d o) (qposQ K (nxt (pf o)) c k H)
    rwa [qposQ_length] at h
  rw [← sumTo_const (K ^ n * (s * k)) NSo]
  refine sumTo_mono _ (fun o ho => ?_)
  have e : sumTo NSh (fun σh => sumTo (K ^ n) (fun h => indB (decide (pos d (saltO NSh NSo (σh + NSh * (o + NSo * h)))
      (saltH NSh (σh + NSh * (o + NSo * h))) ∈ qposQ K (nxt (pf (saltO NSh NSo (σh + NSh * (o + NSo * h)))))
        (comR K NSh NSo pos d (σh + NSh * (o + NSo * h))) k (saltT NSh NSo (σh + NSh * (o + NSo * h))))))) =
      sumTo NSh (fun σh => sumTo (K ^ n) (fun h => indB (decide (pos d o σh ∈
        qposQ K (nxt (pf o)) (rget K (pos d o σh) h) k h)))) :=
    sumTo_congr _ (fun σh hh => sumTo_congr _ (fun h _ => by
      obtain ⟨a, b, c⟩ := salt_dec (h := h) hh ho
      simp only [comR, a, b, c]))
  rw [e]
  exact Nat.le_of_mul_le_mul_left (per o ho) hK
end Circuit
