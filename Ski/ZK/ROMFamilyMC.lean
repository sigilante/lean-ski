import Ski.ZK.ROMFamilyM
import Ski.ZK.ROMInstMC

/-!
# The Merkle commitment's spread when leaves may share a hash

`ROMFamilyM`'s families ask the first commitment to spread fully: at most
`NSl^L Kⁿ / K^L` of its draws give any one value (`comM_spreadL`), the
leaves' answers being distinct table entries.  When two leaves share a
position their answers coincide and the full spread fails.  It holds at
the salt vectors where no two leaves meet, and the others, at most
`L² NSl^(L-1) s` (`collB_count`), are charged in full: `comM_spreadLC`,
`comMI_spreadLC`.  Not shown: the families themselves without `hdist`;
`sud_fs_open4_powD` and its kin take every statement's commitment to hide
exactly and spread fully, and the approximate hiding (`FSOpenA`) and
spread here would enter through approximate versions of them.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **A Merkle tree's leaves' answers spread, leaves sharing positions or
    not**: `comM_spreadL` plus the salt vectors where leaves meet, each
    charged its `Kⁿ` tables. -/
theorem comM_spreadLC {D : Type} {K n NSl L s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s) (d : D) (v : Nat) :
    K ^ L * sumTo (NSl ^ L * K ^ n) (fun σ => indB (decide (comM K NSl L pos d σ = v))) ≤
      NSl ^ L * K ^ n + K ^ L * (K ^ n * (L * (L * (NSl ^ (L - 1) * s)))) := by
  rw [Nat.mul_comm (NSl ^ L) (K ^ n), sum_digit (NSl ^ L) (K ^ n)]
  have hN' : ∀ u, u < NSl ^ L → ∀ H, comM K NSl L pos d (u + NSl ^ L * H) = rgetL K (posAll pos L NSl d u) H :=
    fun u hu H => by unfold comM; rw [(digit_dec hu).1, (digit_dec hu).2]
  rw [sumTo_congr _ (fun H _ => sumTo_congr _ (fun u hu => by rw [hN' u hu H])), sumTo_exch _ (NSl ^ L) (K ^ n),
    sumTo_mul]
  have each : ∀ u, u < NSl ^ L → K ^ L * sumTo (K ^ n) (fun H => indB (decide (rgetL K (posAll pos L NSl d u) H = v))) ≤
      K ^ n + K ^ L * (K ^ n * indB (collB pos L NSl d u)) := fun u _ => by
    cases hb : collB pos L NSl d u
    · have hnd : (posAll pos L NSl d u).Nodup := by
        unfold posAll
        exact nodup_map_on _ _ (lr_nodup L) (fun a ha b hb' hne => collB_dist hb a b (mem_lr ha) (mem_lr hb') hne)
      have h := rgetL_spread hK (posAll pos L NSl d u) hnd
        (fun p hp => by
          unfold posAll at hp
          obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
          exact hlt d l _ (mem_lr hl)) v
      rw [posAll_length] at h
      exact Nat.le_trans h (Nat.le_add_right _ _)
    · refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_le_const (fun _ => indB_le _) _)) ?_
      simp only [indB, if_true, Nat.mul_one]
      exact Nat.le_add_left _ _
  refine Nat.le_trans (sumTo_mono _ each) ?_
  rw [sumTo_add, sumTo_const, ← sumTo_mul, ← sumTo_mul, Nat.mul_comm (NSl ^ L) (K ^ n)]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (collB_count hN pos hs d))) _

/-- **The ideal Merkle commitment spreads, leaves sharing positions or
    not** (`comM_spreadLC`). -/
theorem comMI_spreadLC {D : Type} {K n NSl L s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s) (d : D) (v : Nat) :
    sumTo (NSl ^ L * K ^ n * K ^ L) (fun σ => indB (decide (comMI K NSl L L pos d σ = v))) ≤
      NSl ^ L * K ^ n + K ^ L * (K ^ n * (L * (L * (NSl ^ (L - 1) * s)))) := by
  rw [sum_digit (K ^ L) (NSl ^ L * K ^ n)]
  have e : ∀ σ, sumTo (K ^ L) (fun u => indB (decide (comMI K NSl L L pos d (u + K ^ L * σ) = v))) =
      K ^ L * indB (decide (comM K NSl L pos d σ = v)) := fun σ => by
    rw [sumTo_congr _ (fun u hu => by unfold comMI; rw [(digit_dec hu).1]), sumTo_const]
  rw [sumTo_congr _ (fun σ _ => e σ), ← sumTo_mul]
  exact comM_spreadLC hK hN pos hlt hs d v

end Circuit
