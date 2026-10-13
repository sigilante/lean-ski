import Ski.ZK.ROMMerkle4

/-!
# Leaves that may share a hash

`ROMMerkleOpen` takes distinct leaves to distinct positions at every salt
(`hdist`), a leaf index in the hash input that Plonky3's leaf hash does not
carry.  Without it two leaves with equal rows and equal salts share a
position.  Here distinctness is asked only at the salt vectors a predicate
`bad` clears (`hdistS`), and the bad salt vectors are counted: at most `β`
of the `NSl^L` for every data (`hbad`).  The ideal opening then hides up to
`2 β K^n K^UL`, the bad salt vectors charged in full on both sides
(`pfMI_hidesA`); the exact `pfMI_hides` is its case `β = 0`.
-/

set_option autoImplicit false
namespace Circuit
open ZKF

/-- The unopened leaves' positions are distinct at a salt vector where all
    leaves' are. -/
theorem posU_nodupS {D : Type} (pos : D → Nat → Nat → Nat) (L NSl : Nat) (isO : Nat → Bool) (d : D) (σh : Nat)
    (hd : ∀ l l', l < L → l' < L → l ≠ l' → pos d l (lsalt NSl l σh) ≠ pos d l' (lsalt NSl l' σh)) :
    (posU pos L NSl isO d σh).Nodup := by
  unfold posU unop
  exact nodup_map_on _ _ (nodup_filter _ _ (lr_nodup L))
    (fun a ha b hb hne => hd a b (mem_lr (List.mem_filter.1 ha).1) (mem_lr (List.mem_filter.1 hb).1) hne)

/-- An opened leaf's position is no unopened leaf's at such a salt vector. -/
theorem posU_not_memS {D : Type} {pos : D → Nat → Nat → Nat} {L NSl : Nat} {isO : Nat → Bool} {d : D} {σh l : Nat}
    (hd : ∀ l l', l < L → l' < L → l ≠ l' → pos d l (lsalt NSl l σh) ≠ pos d l' (lsalt NSl l' σh))
    (hl : l < L) (hO : isO l = true) :
    pos d l (lsalt NSl l σh) ∉ posU pos L NSl isO d σh := by
  intro hm
  obtain ⟨l', hl', e⟩ := List.mem_map.1 hm
  have hu : isO l' = false := by
    have := (List.mem_filter.1 hl').2
    cases h : isO l' <;> simp_all
  have hne : l' ≠ l := fun e' => by rw [e'] at hu; rw [hu] at hO; exact Bool.false_ne_true hO
  exact hd l' l (mem_lr (List.mem_filter.1 hl').1) hl hne e

/-- **The ideal opening hides up to the bad salt vectors**: distinct
    positions asked only where `bad` clears the salt vector (`hdistS`), at
    most `β` bad ones for every data (`hbad`). -/
theorem pfMI_hidesA {D O P : Type} {K n NSl L k β : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (bad : D → Nat → Bool)
    (hdistS : ∀ d σh, bad d σh = false → ∀ l l', l < L → l' < L → l ≠ l' →
      pos d l (lsalt NSl l σh) ≠ pos d l' (lsalt NSl l' σh))
    (hbad : ∀ d, sumTo (NSl ^ L) (fun σh => indB (bad d σh)) ≤ β)
    (hlt : ∀ d l a, l < L → pos d l a < n)
    (isO : Nat → Bool) (op : D → O) (hposO : ∀ d d', op d = op d' → ∀ l a, isO l = true → pos d l a = pos d' l a)
    (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) :
    ComPfHidesA (NSl ^ L * K ^ n * K ^ (unop L isO).length) (2 * β * (K ^ n * K ^ (unop L isO).length))
      (comMI K NSl L (unop L isO).length pos) (pfMI K NSl L (unop L isO).length k pos isO op g nxt) op := by
  intro d d' hop E
  let f := fun (dd : D) (σ : Nat) =>
    indB (E (comMI K NSl L (unop L isO).length pos dd σ) (pfMI K NSl L (unop L isO).length k pos isO op g nxt dd σ))
  let A := fun (dd : D) (σh : Nat) => sumTo (K ^ n) (fun h => sumTo (K ^ (unop L isO).length) (fun u =>
    f dd (u + K ^ (unop L isO).length * (σh + NSl ^ L * h))))
  have split : ∀ dd, sumTo (NSl ^ L * K ^ n * K ^ (unop L isO).length) (f dd) = sumTo (NSl ^ L) (A dd) := fun dd => by
    rw [sum_digit, sumTo_split (NSl ^ L), sumTo_exch _ (NSl ^ L) (K ^ n)]
  let G := fun (dd : D) (σh cU H : Nat) =>
    indB (E (rgetL K (posAll pos L NSl dd σh) (rsetL K (posU pos L NSl isO dd σh) H cU))
      (g (op d) (shownS NSl L isO σh), runQ K (nxt (g (op d) (shownS NSl L isO σh)))
        (rgetL K (posAll pos L NSl dd σh) (rsetL K (posU pos L NSl isO dd σh) H cU)) k H))
  -- at a good salt vector, the swap over the unopened positions
  have good : ∀ dd : D, op dd = op d → ∀ σh, σh < NSl ^ L → bad dd σh = false →
      A dd σh = sumTo (K ^ n) (fun H => sumTo (K ^ (unop L isO).length) (fun cU => G dd σh cU H)) := by
    intro dd hdd σh hσ hb
    have hnd := posU_nodupS pos L NSl isO dd σh (hdistS dd σh hb)
    have hlen : (posU pos L NSl isO dd σh).length = (unop L isO).length := List.length_map ..
    have r := reprog_swapL (n := n) hK (posU pos L NSl isO dd σh) hnd
      (fun p hp => by obtain ⟨l, hl, e⟩ := List.mem_map.1 hp; rw [← e]; exact hlt _ _ _ (mem_lr (List.mem_filter.1 hl).1))
      (fun cU H => G dd σh cU H)
    rw [hlen] at r
    rw [← r]
    refine sumTo_congr _ (fun h _ => sumTo_congr _ (fun u hu => ?_))
    obtain ⟨e1, e2⟩ := digit_dec (σ := σh + NSl ^ L * h) hu
    obtain ⟨f1, f2⟩ := digit_dec (σ := h) hσ
    have back := rsetL_back hK (posU pos L NSl isO dd σh) hnd h u
    simp only [f, G, pfMI, comMI, comM, e1, e2, f1, f2, back, hdd]
  -- at a salt vector good for both data, the two agree
  have both : ∀ σh, σh < NSl ^ L → bad d σh = false → bad d' σh = false → A d σh = A d' σh := by
    intro σh hσ hb hb'
    rw [good d rfl σh hσ hb, good d' hop.symm σh hσ hb']
    refine sumTo_congr _ (fun H _ => sumTo_congr _ (fun cU _ => ?_))
    have hc : rgetL K (posAll pos L NSl d' σh) (rsetL K (posU pos L NSl isO d' σh) H cU) =
        rgetL K (posAll pos L NSl d σh) (rsetL K (posU pos L NSl isO d σh) H cU) := by
      refine rgetL_congr _ _ _ _ (by simp only [posAll, List.length_map]) (fun i hi => ?_)
      have hi' : i < (lr L).length := by simp only [posAll, List.length_map] at hi; exact hi
      have hl := lr_getD_lt (n := L) (i := i) (by rw [lr_length] at hi'; exact hi')
      simp only [posAll]
      rw [getD_mapN _ _ hi', getD_mapN _ _ hi']
      cases hO : isO ((lr L).getD i 0)
      · obtain ⟨j, hj, ej⟩ := unop_index hl hO
        have hj' : j < (posU pos L NSl isO d' σh).length := by simp only [posU, List.length_map]; exact hj
        have hj'' : j < (posU pos L NSl isO d σh).length := by simp only [posU, List.length_map]; exact hj
        have a1 := rget_rsetL_at hK _ (posU_nodupS pos L NSl isO d' σh (hdistS d' σh hb')) j hj' H cU
        have a2 := rget_rsetL_at hK _ (posU_nodupS pos L NSl isO d σh (hdistS d σh hb)) j hj'' H cU
        have p1 : (posU pos L NSl isO d' σh).getD j 0 = pos d' ((lr L).getD i 0) (lsalt NSl ((lr L).getD i 0) σh) := by
          unfold posU; rw [getD_mapN _ _ hj, ej]
        have p2 : (posU pos L NSl isO d σh).getD j 0 = pos d ((lr L).getD i 0) (lsalt NSl ((lr L).getD i 0) σh) := by
          unfold posU; rw [getD_mapN _ _ hj, ej]
        rw [p1] at a1; rw [p2] at a2
        rw [a1, a2]
      · rw [rget_rsetL_not hK _ (posU_not_memS (hdistS d' σh hb') hl hO),
          rget_rsetL_not hK _ (posU_not_memS (hdistS d σh hb) hl hO), hposO d' d hop.symm _ _ hO]
    simp only [G, hc]
  -- every salt vector's count is at most the tables and re-randomizations
  have cap : ∀ dd σh, A dd σh ≤ K ^ n * K ^ (unop L isO).length := fun dd σh =>
    sumTo_le_const (fun _ => Nat.le_trans (sumTo_le_const (fun _ => indB_le _) _)
      (Nat.le_of_eq (Nat.mul_one _))) _
  have each : ∀ σh, σh < NSl ^ L → A d σh ≤
      A d' σh + (K ^ n * K ^ (unop L isO).length) * (indB (bad d σh) + indB (bad d' σh)) := by
    intro σh hσ
    cases hb : bad d σh <;> cases hb' : bad d' σh
    · rw [both σh hσ hb hb']; exact Nat.le_add_right _ _
    all_goals
      have h1 : 1 ≤ indB (bad d σh) + indB (bad d' σh) := by simp [hb, hb', indB]
      rw [hb, hb'] at h1
      exact Nat.le_trans (cap d σh) (Nat.le_trans (Nat.le_mul_of_pos_right _ h1) (Nat.le_add_left _ _))
  rw [split d, split d']
  refine Nat.le_trans (sumTo_mono _ each) ?_
  rw [sumTo_add, ← sumTo_mul, sumTo_add, Nat.mul_comm (2 * β)]
  refine Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_trans (Nat.add_le_add (hbad d) (hbad d')) ?_)) _
  omega

/-- **`pfMIP_hides` up to the bad salt vectors**: the padded ideal opening,
    every opened set at one salt range. -/
theorem pfMIP_hidesA {D O P : Type} {K n NSl L k β : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (bad : D → Nat → Bool)
    (hdistS : ∀ d σh, bad d σh = false → ∀ l l', l < L → l' < L → l ≠ l' →
      pos d l (lsalt NSl l σh) ≠ pos d l' (lsalt NSl l' σh))
    (hbad : ∀ d, sumTo (NSl ^ L) (fun σh => indB (bad d σh)) ≤ β)
    (hlt : ∀ d l a, l < L → pos d l a < n)
    (isO : Nat → Bool) (op : D → O) (hposO : ∀ d d', op d = op d' → ∀ l a, isO l = true → pos d l a = pos d' l a)
    (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) :
    ComPfHidesA (NSl ^ L * K ^ n * K ^ L) (2 * β * (K ^ n * K ^ L)) (comMI K NSl L L pos)
      (pfMI K NSl L L k pos isO op g nxt) op := by
  intro d d' hop E
  have hUL := unop_le L isO
  have hsp : K ^ L = K ^ (unop L isO).length * K ^ (L - (unop L isO).length) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hUL]
  have key : ∀ dd : D, sumTo (NSl ^ L * K ^ n * K ^ L) (fun σ => indB (E (comMI K NSl L L pos dd σ)
      (pfMI K NSl L L k pos isO op g nxt dd σ))) =
      K ^ (L - (unop L isO).length) * sumTo (NSl ^ L * K ^ n * K ^ (unop L isO).length) (fun σ =>
        indB (E (comMI K NSl L (unop L isO).length pos dd σ) (pfMI K NSl L (unop L isO).length k pos isO op g nxt dd σ))) :=
    fun dd => by
    rw [sum_digit (K ^ L), sum_digit (K ^ (unop L isO).length), sumTo_mul]
    refine sumTo_congr _ (fun σ' _ => ?_)
    rw [hsp, sumTo_split (K ^ (unop L isO).length), ← sumTo_const _ (K ^ (L - (unop L isO).length))]
    refine sumTo_congr _ (fun q hq => sumTo_congr _ (fun r hr => ?_))
    have hu : r + K ^ (unop L isO).length * q < K ^ (unop L isO).length * K ^ (L - (unop L isO).length) := by
      calc r + K ^ (unop L isO).length * q < K ^ (unop L isO).length + K ^ (unop L isO).length * q :=
            Nat.add_lt_add_right hr _
        _ = K ^ (unop L isO).length * (q + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        _ ≤ _ := Nat.mul_le_mul_left _ hq
    rw [← hsp] at hu
    obtain ⟨a1, a2⟩ := digit_dec (σ := σ') hu
    obtain ⟨b1, b2⟩ := digit_dec (σ := σ') hr
    have hlen : (posU pos L NSl isO dd (σ' % NSl ^ L)).length = (unop L isO).length := List.length_map ..
    have hm : (r + K ^ (unop L isO).length * q) % K ^ (unop L isO).length = r := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have hset : rsetL K (posU pos L NSl isO dd (σ' % NSl ^ L)) (σ' / NSl ^ L) (r + K ^ (unop L isO).length * q) =
        rsetL K (posU pos L NSl isO dd (σ' % NSl ^ L)) (σ' / NSl ^ L) r := by
      rw [rsetL_mod hK, hlen, hm]
    rw [← hsp]
    simp only [pfMI, comMI, a1, a2, b1, b2, hset]
  rw [key d, key d']
  have h := pfMI_hidesA (k := k) hK pos bad hdistS hbad hlt isO op hposO g nxt d d' hop E
  refine Nat.le_trans (Nat.mul_le_mul_left _ h) (Nat.le_of_eq ?_)
  rw [Nat.mul_add]
  congr 1
  rw [hsp]
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end Circuit
