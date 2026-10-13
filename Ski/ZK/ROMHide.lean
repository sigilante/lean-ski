import Ski.ZK.FSMulti

/-!
# A commitment drawn from the random oracle hides

The theorems so far take the commitment as a primitive apart from the
oracle, and let the distinguisher read the oracle's whole table.  A salted
commitment read off the oracle itself, `Com d σ = H(pos d σ)`, cannot hide
from such a distinguisher, which tries every salt.  Against a
distinguisher of `k` adaptive queries it does: reprogramming a position
the run never queries leaves the run as it was (`runQ_rset`), so the
commitment's answer is uniform beside the run (`rom_offQ`, `rom_offQ'`),
and the counts at two data differ by at most the tables times `2 s k`,
`s` salts at most taking a position (`rom_hideQ`), `2 s k / NS` once
normalized.  The fixed-query case first (`rom_off`, `rom_hide`).  Not yet
composed with the Fiat–Shamir theorems: their distinguishers read the
whole table.
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

/-- **An adaptive run of `k` queries**: each query's position read off the
    answers so far (`nxt`), the answers newest first. -/
def runQ (K : Nat) (nxt : List Nat → Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, H => rget K (nxt (runQ K nxt k H)) H :: runQ K nxt k H

/-- The positions the run queries. -/
def qposQ (K : Nat) (nxt : List Nat → Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, H => nxt (runQ K nxt k H) :: qposQ K nxt k H

/-- **A run that never queries `p` does not see `p` set.** -/
theorem runQ_rset {K p c : Nat} (hK : 0 < K) (hc : c < K) (nxt : List Nat → Nat) :
    ∀ k H, p ∉ qposQ K nxt k H → runQ K nxt k (rset K p H c) = runQ K nxt k H ∧
      qposQ K nxt k (rset K p H c) = qposQ K nxt k H
  | 0, _, _ => ⟨rfl, rfl⟩
  | k + 1, H, h => by
    simp only [qposQ, List.mem_cons, not_or] at h
    obtain ⟨e1, e2⟩ := runQ_rset hK hc nxt k H h.2
    refine ⟨?_, ?_⟩
    · show rget K (nxt (runQ K nxt k (rset K p H c))) (rset K p H c) :: runQ K nxt k (rset K p H c) =
        rget K (nxt (runQ K nxt k H)) H :: runQ K nxt k H
      rw [e1, rget_rset_ne hK (fun e => h.1 e.symm) hc]
    · show nxt (runQ K nxt k (rset K p H c)) :: qposQ K nxt k (rset K p H c) = nxt (runQ K nxt k H) :: qposQ K nxt k H
      rw [e1, e2]

theorem qposQ_rset {K p c : Nat} (hK : 0 < K) (hc : c < K) (nxt : List Nat → Nat) (k H : Nat) :
    p ∈ qposQ K nxt k (rset K p H c) → p ∈ qposQ K nxt k H := by
  intro h
  by_cases h' : p ∈ qposQ K nxt k H
  · exact h'
  · rw [(runQ_rset hK hc nxt k H h').2] at h; exact absurd h h'

/-- **A commitment off an adaptive run is uniform beside it**, up to the
    tables whose run queries it. -/
theorem rom_offQ {K n p k : Nat} (hK : 0 < K) (hp : p < n) (nxt : List Nat → Nat) (E : List Nat → Nat → Bool) :
    K * sumTo (K ^ n) (fun H => indB (E (runQ K nxt k H) (rget K p H))) ≤
      sumTo (K ^ n) (fun H => sumTo K (fun c => indB (E (runQ K nxt k H) c))) +
        K * sumTo (K ^ n) (fun H => indB (decide (p ∈ qposQ K nxt k H))) := by
  rw [← oracle_reprog_get hK hp (fun H c => indB (E (runQ K nxt k H) c)), sumTo_mul, ← sumTo_add]
  refine sumTo_mono _ (fun H _ => ?_)
  rw [← sumTo_const (indB (decide (p ∈ qposQ K nxt k H))) K, ← sumTo_add]
  refine sumTo_mono _ (fun c hc => ?_)
  by_cases hq : p ∈ qposQ K nxt k H
  · have e : indB (decide (p ∈ qposQ K nxt k H)) = 1 := by simp [indB, hq]
    rw [e]; exact Nat.le_trans (indB_le _) (Nat.le_add_left _ _)
  · rw [(runQ_rset hK hc nxt k H hq).1]; exact Nat.le_add_right _ _

theorem rom_offQ' {K n p k : Nat} (hK : 0 < K) (hp : p < n) (nxt : List Nat → Nat) (E : List Nat → Nat → Bool) :
    sumTo (K ^ n) (fun H => sumTo K (fun c => indB (E (runQ K nxt k H) c))) ≤
      K * sumTo (K ^ n) (fun H => indB (E (runQ K nxt k H) (rget K p H))) +
        K * sumTo (K ^ n) (fun H => indB (decide (p ∈ qposQ K nxt k H))) := by
  rw [← oracle_reprog_get hK hp (fun H c => indB (E (runQ K nxt k H) c)), sumTo_mul, ← sumTo_add]
  refine sumTo_mono _ (fun H _ => ?_)
  rw [← sumTo_const (indB (decide (p ∈ qposQ K nxt k H))) K, ← sumTo_add]
  refine sumTo_mono _ (fun c hc => ?_)
  by_cases hq : p ∈ qposQ K nxt k H
  · have e : indB (decide (p ∈ qposQ K nxt k H)) = 1 := by simp [indB, hq]
    rw [e]; exact Nat.le_trans (indB_le _) (Nat.le_add_left _ _)
  · rw [(runQ_rset hK hc nxt k H hq).1]; exact Nat.le_add_right _ _

theorem qposQ_length (K : Nat) (nxt : List Nat → Nat) : ∀ k H, (qposQ K nxt k H).length = k
  | 0, _ => rfl
  | k + 1, H => by simp only [qposQ, List.length_cons, qposQ_length K nxt k H]

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
    distinguisher of `k` queries**: over the tables and the salts, its
    counts at two data differ by at most the tables times `2 s k`, each
    position taken by at most `s` salts of either datum. -/
theorem rom_hideQ {D : Type} {K n NS s k : Nat} (hK : 0 < K) (pos : D → Nat → Nat) (hpos : ∀ d σ, pos d σ < n)
    (hs : ∀ d v, sumTo NS (fun σ => indB (decide (pos d σ = v))) ≤ s)
    (nxt : List Nat → Nat) (E : List Nat → Nat → Bool) (d d' : D) :
    K * sumTo NS (fun σ => sumTo (K ^ n) (fun H => indB (E (runQ K nxt k H) (rget K (pos d σ) H)))) ≤
      K * sumTo NS (fun σ => sumTo (K ^ n) (fun H => indB (E (runQ K nxt k H) (rget K (pos d' σ) H)))) +
        K * (K ^ n * (2 * (s * k))) := by
  have step : ∀ σ, K * sumTo (K ^ n) (fun H => indB (E (runQ K nxt k H) (rget K (pos d σ) H))) ≤
      K * sumTo (K ^ n) (fun H => indB (E (runQ K nxt k H) (rget K (pos d' σ) H))) +
        K * sumTo (K ^ n) (fun H => indB (decide (pos d' σ ∈ qposQ K nxt k H)) +
          indB (decide (pos d σ ∈ qposQ K nxt k H))) := fun σ => by
    rw [sumTo_add, Nat.mul_add, ← Nat.add_assoc]
    exact Nat.le_trans (rom_offQ hK (hpos d σ) nxt E) (Nat.add_le_add_right (rom_offQ' hK (hpos d' σ) nxt E) _)
  rw [sumTo_mul, sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun σ _ => step σ)) ?_
  rw [sumTo_add]
  refine Nat.add_le_add_left ?_ _
  rw [← sumTo_mul, sumTo_exch _ (K ^ n) NS]
  refine Nat.mul_le_mul_left _ (Nat.le_trans (sumTo_mono _ (fun H _ => ?_)) (Nat.le_of_eq (sumTo_const _ _)))
  rw [sumTo_add, show 2 * (s * k) = s * k + s * k by omega]
  have h1 := salts_in (pos d') (hs d') (qposQ K nxt k H)
  have h2 := salts_in (pos d) (hs d) (qposQ K nxt k H)
  rw [qposQ_length] at h1 h2
  exact Nat.add_le_add h1 h2
end Circuit
