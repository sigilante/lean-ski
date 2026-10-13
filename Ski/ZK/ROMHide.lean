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
added (`open_realA`, `open_real_tA`, `fs_openA`).  Not yet composed: the
Fiat–Shamir distinguisher must also query the commitment's own oracle
domain, at most `k` times, and the theorems' distinguishers do not yet
take those queries.
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
    slack.  For a commitment drawn from the oracle against a distinguisher of
    `k` queries, `rom_hideQ` gives the slack. -/
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

end Circuit
