import Ski.ZK.ROMMerkle4

/-!
# Leaves that may share a hash

`ROMMerkleOpen` takes distinct leaves to distinct positions at every salt
(`hdist`), a leaf index in the hash input that Plonky3's leaf hash does not
carry: there two leaves with equal rows and equal salts share a position.
Here `hdist` is dropped and the collisions are counted through the salt's
spread `hs` alone.

- The ideal opening hides up to the salt vectors a predicate `bad` flags,
  distinct positions asked elsewhere (`pfMI_hidesA`, padded `pfMIP_hidesA`).
- The salt vectors where two leaves meet (`collB`) number at most
  `L² NSl^(L-1) s` (`collB_count`): with the other leaf's salt fixed, `s`
  of a leaf's salts reach its position (`pair_count`).
- A leaf's salt moves no other leaf's answer where its position meets none
  (`comM_val`), and such meetings number at most `L s` of its salts, so the
  hits on an unopened leaf gain `L` queries' worth (`hitLeaf_boundC`,
  `hitM_boundC`, `transferMC`).
- The real opening hides up to `2 UL s (k + L) / NSl + 2 L² s / NSl` a draw
  (`pfM_hidesC`); one Fiat–Shamir round keeps it with `L` in place of
  `UL` (`fs_openROMMC`).  `collide_sat` meets the hypotheses with Plonky3's
  shape, a leaf's position its salt and its row's hash, and two leaves
  meeting.

Not shown: the four-round theorems (`ROMMerkle4`, the circuit families)
without `hdist`.  They need three more pieces: an approximate `fs_open4`
for the hiding here; collision versions of the hit bounds with the opened
set read off the commitment (`hitLeafc_bound`, `hitMc_bound`,
`transferMc`); and an approximate spread of the commitment
(`comM_spreadL`), whose full `K^L` fails when two leaves share an
answer.
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

/-- A list of answers as one number, digit by digit. -/
def encL (K : Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => v + K * encL K vs

theorem rgetL_enc (K : Nat) : ∀ (ps : List Nat) (X : Nat), rgetL K ps X = encL K (ps.map (fun p => rget K p X))
  | [], _ => rfl
  | p :: ps, X => by
    show rget K p X + K * rgetL K ps X = rget K p X + K * encL K (ps.map (fun p => rget K p X))
    rw [rgetL_enc K ps X]

/-- **Leaf `l`'s salt moves no other leaf's answer** where its position
    meets no other leaf's: the commitment, its answer set to `a`, is then
    the same at every such salt `x`. -/
theorem comM_val {D : Type} {K NSl L l lo x hi a H : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (d : D) (hlo : lo < NSl ^ l) (hx : x < NSl) (ha : a < K)
    (hgood : ∀ l', l' ∈ lr L → l' ≠ l → pos d l' (lsalt NSl l' (lo + NSl ^ l * (0 + NSl * hi))) ≠ pos d l x) :
    rgetL K (posAll pos L NSl d (lo + NSl ^ l * (x + NSl * hi))) (rset K (pos d l x) H a) =
      encL K ((lr L).map (fun l' => if l' = l then a else rget K (pos d l' (lsalt NSl l' (lo + NSl ^ l * (0 + NSl * hi)))) H)) := by
  rw [rgetL_enc]
  unfold posAll
  rw [List.map_map]
  congr 1
  refine List.map_congr_left (fun l' hl' => ?_)
  by_cases e : l' = l
  · subst e
    simp only [Function.comp, lsalt_at hlo hx, rget_rset hK ha, if_true]
  · simp only [Function.comp, if_neg e, lsalt_ne hN e hlo hx]
    exact rget_rset_ne hK (hgood l' hl' e) ha

/-- **An unopened leaf's position is hit by few draws, leaves sharing
    positions or not**: `hitLeaf_bound` without `hdist`, the salts at which
    the leaf meets another leaf's position counted through the spread `hs`,
    at most `L s` of them; `s (k + L)` in place of `s k`. -/
theorem hitLeaf_boundC {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isO : Nat → Bool) (op : D → O) (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) (d : D)
    {l : Nat} (hl : l < L) (hu : isO l = false) :
    sumTo (NSl ^ L) (fun σh => sumTo (K ^ n) (fun h => indB (decide (pos d l (lsalt NSl l σh) ∈
      qposQ K (nxt (g (op d) (shownS NSl L isO σh))) (rgetL K (posAll pos L NSl d σh) h) k h)))) ≤
      K ^ n * (NSl ^ (L - l - 1) * (NSl ^ l * (s * (k + L)))) := by
  let f := fun (σh a H : Nat) => indB (decide (pos d l (lsalt NSl l σh) ∈
    qposQ K (nxt (g (op d) (shownS NSl L isO σh))) (rgetL K (posAll pos L NSl d σh)
      (rset K (pos d l (lsalt NSl l σh)) H a)) k H))
  have swap : ∀ σh, K * sumTo (K ^ n) (fun h => indB (decide (pos d l (lsalt NSl l σh) ∈
      qposQ K (nxt (g (op d) (shownS NSl L isO σh))) (rgetL K (posAll pos L NSl d σh) h) k h))) =
      sumTo (K ^ n) (fun H => sumTo K (fun a => f σh a H)) := fun σh => by
    rw [← reprog_swap hK (hlt d l (lsalt NSl l σh) hl) (fun a H => f σh a H), sumTo_mul]
    refine sumTo_congr _ (fun h _ => ?_)
    rw [← sumTo_const _ K]
    refine sumTo_congr _ (fun u hu => ?_)
    show _ = indB (decide (pos d l (lsalt NSl l σh) ∈ qposQ K (nxt (g (op d) (shownS NSl L isO σh)))
      (rgetL K (posAll pos L NSl d σh) (rset K (pos d l (lsalt NSl l σh)) (rset K (pos d l (lsalt NSl l σh)) h u)
        (rget K (pos d l (lsalt NSl l σh)) h))) k (rset K (pos d l (lsalt NSl l σh)) h u)))
    rw [rset_back hK hu, decide_eq_decide.2 (hit_rset hK hu _ _ k h)]
  have per : ∀ H a, a < K → sumTo (NSl ^ L) (fun σh => f σh a H) ≤ NSl ^ (L - l - 1) * (NSl ^ l * (s * (k + L))) := by
    intro H a ha
    rw [sum_split_digit NSl L l hl, ← sumTo_const (NSl ^ l * (s * (k + L))) (NSl ^ (L - l - 1))]
    refine sumTo_mono _ (fun hi _ => ?_)
    rw [sumTo_exch _ (NSl ^ l) NSl, ← sumTo_const (s * (k + L)) (NSl ^ l)]
    refine sumTo_mono _ (fun lo hlo => ?_)
    let σ0 := lo + NSl ^ l * (0 + NSl * hi)
    let vs := (lr L).map (fun l' => if l' = l then a else rget K (pos d l' (lsalt NSl l' σ0)) H)
    let Q := qposQ K (nxt (g (op d) (shownS NSl L isO σ0))) (encL K vs) k H
    let coll := fun x => (lr L).any (fun l' => l' != l && decide (pos d l' (lsalt NSl l' σ0) = pos d l x))
    have e : ∀ x, x < NSl → f (lo + NSl ^ l * (x + NSl * hi)) a H ≤
        indB (decide (pos d l x ∈ Q)) + indB (coll x) := fun x hx => by
      cases hc : coll x
      · have hgood : ∀ l', l' ∈ lr L → l' ≠ l → pos d l' (lsalt NSl l' σ0) ≠ pos d l x := fun l' hl' hne e' => by
          have : coll x = true := List.any_eq_true.2 ⟨l', hl', by simp [hne, e']⟩
          rw [hc] at this; exact Bool.false_ne_true this
        show indB (decide (pos d l (lsalt NSl l (lo + NSl ^ l * (x + NSl * hi))) ∈ _)) ≤ _
        rw [lsalt_at hlo hx, shownS_eq hN hu hlo hx, comM_val hK hN pos d hlo hx ha hgood]
        exact Nat.le_add_right _ _
      · exact Nat.le_trans (indB_le _) (Nat.le_add_left _ _)
    refine Nat.le_trans (sumTo_mono _ e) ?_
    rw [sumTo_add, Nat.mul_add]
    refine Nat.add_le_add ?_ ?_
    · have h := salts_in (pos d l) (hs d l) Q
      rwa [qposQ_length] at h
    · -- the colliding salts: at most `s` meet each other leaf's position
      have hc : ∀ x, indB (coll x) ≤ sumTo (lr L).length (fun j =>
          indB (decide (pos d l x = pos d ((lr L).getD j 0) (lsalt NSl ((lr L).getD j 0) σ0)))) := fun x => by
        refine Nat.le_trans (any_le_sum (fun l' => l' != l && decide (pos d l' (lsalt NSl l' σ0) = pos d l x)) (lr L))
          (sumTo_mono _ (fun j _ => ?_))
        cases hb : ((lr L).getD j 0 != l) <;>
          cases he : decide (pos d ((lr L).getD j 0) (lsalt NSl ((lr L).getD j 0) σ0) = pos d l x) <;>
          simp_all [indB]
      refine Nat.le_trans (sumTo_mono _ (fun x _ => hc x)) ?_
      rw [sumTo_exch _ (lr L).length NSl, lr_length, Nat.mul_comm s L, ← sumTo_const s L]
      exact sumTo_mono _ (fun j _ => hs d l _)
  refine Nat.le_of_mul_le_mul_left ?_ hK
  rw [sumTo_mul, sumTo_congr _ (fun σh _ => swap σh), sumTo_exch _ (K ^ n) (NSl ^ L)]
  rw [show K * (K ^ n * (NSl ^ (L - l - 1) * (NSl ^ l * (s * (k + L))))) =
    sumTo (K ^ n) (fun _ => sumTo K (fun _ => NSl ^ (L - l - 1) * (NSl ^ l * (s * (k + L))))) by
      rw [sumTo_const, sumTo_const]; ac_rfl]
  refine sumTo_mono _ (fun H _ => ?_)
  rw [sumTo_exch _ K (NSl ^ L)]
  exact sumTo_mono _ (fun a ha => per H a ha)

/-- **The draws that hit an unopened leaf are few**: at most
    `UL Kⁿ NSl^(L-1) s (k + L)` over the salts and the table; normalized,
    `UL s (k + L) / NSl`, `UL` the unopened leaves. -/
theorem hitM_boundC {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isO : Nat → Bool) (op : D → O) (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) (d : D) :
    sumTo (NSl ^ L * K ^ n) (fun σ => indB (hitL K (posU pos L NSl isO d (σ % NSl ^ L))
      (nxt (g (op d) (shownS NSl L isO (σ % NSl ^ L)))) (comM K NSl L pos d σ) k (σ / NSl ^ L))) ≤
      (unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (s * (k + L)))) := by
  rw [sumTo_split (NSl ^ L), sumTo_exch _ (NSl ^ L) (K ^ n)]
  have e : ∀ σh, σh < NSl ^ L → ∀ h, indB (hitL K (posU pos L NSl isO d ((σh + NSl ^ L * h) % NSl ^ L))
      (nxt (g (op d) (shownS NSl L isO ((σh + NSl ^ L * h) % NSl ^ L)))) (comM K NSl L pos d (σh + NSl ^ L * h)) k
        ((σh + NSl ^ L * h) / NSl ^ L)) ≤
      sumTo (unop L isO).length (fun j => indB (decide (pos d ((unop L isO).getD j 0)
        (lsalt NSl ((unop L isO).getD j 0) σh) ∈ qposQ K (nxt (g (op d) (shownS NSl L isO σh)))
          (rgetL K (posAll pos L NSl d σh) h) k h))) := fun σh hσ h => by
    obtain ⟨f1, f2⟩ := digit_dec (σ := h) hσ
    simp only [comM, f1, f2]
    have a := any_le_sum (fun p => decide (p ∈ qposQ K (nxt (g (op d) (shownS NSl L isO σh)))
      (rgetL K (posAll pos L NSl d σh) h) k h)) (posU pos L NSl isO d σh)
    have hlen : (posU pos L NSl isO d σh).length = (unop L isO).length := List.length_map ..
    rw [hlen] at a
    refine Nat.le_trans a (Nat.le_of_eq (sumTo_congr _ (fun j hj => ?_)))
    unfold posU; rw [getD_mapN _ _ hj]
  refine Nat.le_trans (sumTo_mono _ (fun σh hσ => sumTo_mono _ (fun h _ => e σh hσ h))) ?_
  rw [sumTo_congr _ (fun σh _ => sumTo_exch _ _ _), sumTo_exch _ (unop L isO).length (NSl ^ L),
    ← sumTo_const (K ^ n * (NSl ^ (L - 1) * (s * (k + L)))) (unop L isO).length]
  refine sumTo_mono _ (fun j hj => ?_)
  have hm : (unop L isO).getD j 0 ∈ unop L isO := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem ..
  obtain ⟨hl, hu⟩ := unop_mem hm
  have b := hitLeaf_boundC (k := k) hK hN pos hlt hs isO op g nxt d hl hu
  refine Nat.le_trans b (Nat.le_of_eq ?_)
  rw [← Nat.mul_assoc (NSl ^ (L - _ - 1)), ← Nat.pow_add]
  congr 3; omega

/-- **The real opening of a Merkle tree's leaves is the ideal's up to the
    hits**: `K^UL` times the real count is within `K^UL UL Kⁿ NSl^(L-1) s (k + L)`
    of the ideal count, both ways. -/
theorem transferMC {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isO : Nat → Bool) (op : D → O) (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat)
    (F : Nat → P × List Nat → Bool) (d : D) :
    let UL := (unop L isO).length
    K ^ UL * sumTo (NSl ^ L * K ^ n) (fun σ => indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ))) ≤
      sumTo (NSl ^ L * K ^ n * K ^ UL) (fun σ =>
        indB (F (comMI K NSl L UL pos d σ) (pfMI K NSl L UL k pos isO op g nxt d σ))) +
        K ^ UL * (UL * (K ^ n * (NSl ^ (L - 1) * (s * (k + L))))) ∧
    sumTo (NSl ^ L * K ^ n * K ^ UL) (fun σ =>
        indB (F (comMI K NSl L UL pos d σ) (pfMI K NSl L UL k pos isO op g nxt d σ))) ≤
      K ^ UL * sumTo (NSl ^ L * K ^ n) (fun σ => indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ))) +
        K ^ UL * (UL * (K ^ n * (NSl ^ (L - 1) * (s * (k + L))))) := by
  intro UL
  have hb := hitM_boundC (n := n) (L := L) (k := k) hK hN pos hlt hs isO op g nxt d
  have hk := Nat.mul_le_mul_left (K ^ UL) hb
  rw [sum_digit (K ^ UL) (NSl ^ L * K ^ n), sumTo_mul (K ^ UL) _ (NSl ^ L * K ^ n)]
  have pt := fun σ => pfM_pfMI (NSl := NSl) (L := L) (k := k) hK pos isO op g nxt F d σ
  constructor
  · refine Nat.le_trans (sumTo_mono _ (fun σ _ => (pt σ).1)) ?_
    rw [sumTo_add]
    exact Nat.add_le_add_left (Nat.le_trans (Nat.le_of_eq (sumTo_mul (K ^ UL) _ _).symm) hk) _
  · refine Nat.le_trans (sumTo_mono _ (fun σ _ => (pt σ).2)) ?_
    rw [sumTo_add]
    exact Nat.add_le_add_left (Nat.le_trans (Nat.le_of_eq (sumTo_mul (K ^ UL) _ _).symm) hk) _

/-- Two leaves meet: some pair of distinct leaves at one position. -/
def collB {D : Type} (pos : D → Nat → Nat → Nat) (L NSl : Nat) (d : D) (σh : Nat) : Bool :=
  (lr L).any (fun l => (lr L).any (fun l' => l != l' && decide (pos d l (lsalt NSl l σh) = pos d l' (lsalt NSl l' σh))))

theorem collB_dist {D : Type} {pos : D → Nat → Nat → Nat} {L NSl : Nat} {d : D} {σh : Nat}
    (h : collB pos L NSl d σh = false) :
    ∀ l l', l < L → l' < L → l ≠ l' → pos d l (lsalt NSl l σh) ≠ pos d l' (lsalt NSl l' σh) := by
  intro l l' hl hl' hne e
  have : collB pos L NSl d σh = true :=
    List.any_eq_true.2 ⟨l, lr_mem hl, List.any_eq_true.2 ⟨l', lr_mem hl', by simp [hne, e]⟩⟩
  rw [h] at this; exact Bool.false_ne_true this

/-- Two given leaves meet at few salt vectors: `NSl^(L-1) s`, leaf `l`'s
    salt spreading with the other's fixed. -/
theorem pair_count {D : Type} {NSl L s : Nat} (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s) (d : D)
    {l l' : Nat} (hl : l < L) (hne : l' ≠ l) :
    sumTo (NSl ^ L) (fun σh => indB (decide (pos d l (lsalt NSl l σh) = pos d l' (lsalt NSl l' σh)))) ≤
      NSl ^ (L - l - 1) * (NSl ^ l * s) := by
  rw [sum_split_digit NSl L l hl, ← sumTo_const (NSl ^ l * s) (NSl ^ (L - l - 1))]
  refine sumTo_mono _ (fun hi _ => ?_)
  rw [sumTo_exch _ (NSl ^ l) NSl, ← sumTo_const s (NSl ^ l)]
  refine sumTo_mono _ (fun lo hlo => ?_)
  refine Nat.le_trans (Nat.le_of_eq (sumTo_congr _ (fun x hx => ?_))) (hs d l (pos d l' (lsalt NSl l' (lo + NSl ^ l * (0 + NSl * hi)))))
  rw [lsalt_at hlo hx, lsalt_ne hN hne hlo hx]

/-- **Leaves meet at few salt vectors**: at most `L² NSl^(L-1) s`. -/
theorem collB_count {D : Type} {NSl L s : Nat} (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s) (d : D) :
    sumTo (NSl ^ L) (fun σh => indB (collB pos L NSl d σh)) ≤ L * (L * (NSl ^ (L - 1) * s)) := by
  have hpt : ∀ σh, indB (collB pos L NSl d σh) ≤ sumTo L (fun i => sumTo L (fun j =>
      indB ((lr L).getD i 0 != (lr L).getD j 0 &&
        decide (pos d ((lr L).getD i 0) (lsalt NSl ((lr L).getD i 0) σh) =
          pos d ((lr L).getD j 0) (lsalt NSl ((lr L).getD j 0) σh))))) := fun σh => by
    unfold collB
    refine Nat.le_trans (any_le_sum _ (lr L)) ?_
    rw [lr_length]
    exact sumTo_mono _ (fun i _ => Nat.le_trans (any_le_sum _ (lr L)) (by rw [lr_length]; exact Nat.le_refl _))
  refine Nat.le_trans (sumTo_mono _ (fun σh _ => hpt σh)) ?_
  rw [sumTo_exch _ L (NSl ^ L), ← sumTo_const _ L]
  refine sumTo_mono _ (fun i hi => ?_)
  rw [sumTo_exch _ L (NSl ^ L), ← sumTo_const _ L]
  refine sumTo_mono _ (fun j hj => ?_)
  have hli := lr_getD_lt (n := L) hi
  by_cases e : (lr L).getD i 0 = (lr L).getD j 0
  · rw [e]; simp [indB, sumTo_const]
  · have hb : ∀ σh, indB ((lr L).getD i 0 != (lr L).getD j 0 &&
        decide (pos d ((lr L).getD i 0) (lsalt NSl ((lr L).getD i 0) σh) =
          pos d ((lr L).getD j 0) (lsalt NSl ((lr L).getD j 0) σh))) =
        indB (decide (pos d ((lr L).getD i 0) (lsalt NSl ((lr L).getD i 0) σh) =
          pos d ((lr L).getD j 0) (lsalt NSl ((lr L).getD j 0) σh))) := fun σh => by
      rw [show ((lr L).getD i 0 != (lr L).getD j 0) = true from bne_iff_ne.2 e, Bool.true_and]
    rw [sumTo_congr _ (fun σh _ => hb σh)]
    refine Nat.le_trans (pair_count hN pos hs d hli (Ne.symm e)) (Nat.le_of_eq ?_)
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    congr 2; omega

/-- **The real opening of a Merkle tree's leaves hides, leaves sharing
    positions or not**: `pfM_hidesA` with no `hdist`, only the spread `hs`;
    the hits gain `L` queries' worth (`hitLeaf_boundC`) and the salt
    vectors where leaves meet cost `2 L² NSl^(L-1) s Kⁿ` (`collB_count`),
    `2 L² s / NSl` a draw normalized. -/
theorem pfM_hidesC {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isO : Nat → Bool) (op : D → O) (hposO : ∀ d d', op d = op d' → ∀ l a, isO l = true → pos d l a = pos d' l a)
    (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) :
    ComPfHidesA (NSl ^ L * K ^ n)
      ((unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * (k + L))))) +
        2 * (L * (L * (NSl ^ (L - 1) * s))) * K ^ n)
      (comM K NSl L pos) (pfM K NSl L k pos isO op g nxt) op := by
  intro d d' hop E
  have hKL : 0 < K ^ (unop L isO).length := Nat.pow_pos hK
  have t1 := (transferMC (n := n) (L := L) (k := k) hK hN pos hlt hs isO op g nxt E d).1
  have t2 := (transferMC (n := n) (L := L) (k := k) hK hN pos hlt hs isO op g nxt E d').2
  have hi := pfMI_hidesA (n := n) (NSl := NSl) (L := L) (k := k) (β := L * (L * (NSl ^ (L - 1) * s))) hK pos
    (collB pos L NSl) (fun _ _ h => collB_dist h) (fun dd => collB_count hN pos hs dd) hlt isO op hposO g nxt d d' hop E
  refine Nat.le_of_mul_le_mul_left ?_ hKL
  refine Nat.le_trans t1 (Nat.le_trans (Nat.add_le_add_right hi _)
    (Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right t2 _) _) (Nat.le_of_eq ?_)))
  have e1 : (unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * (k + L))))) =
      (unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (s * (k + L)))) +
        (unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (s * (k + L)))) := by
    rw [Nat.two_mul]; simp only [Nat.mul_add]
  have e2 : 2 * (L * (L * (NSl ^ (L - 1) * s))) * (K ^ n * K ^ (unop L isO).length) =
      K ^ (unop L isO).length * (2 * (L * (L * (NSl ^ (L - 1) * s))) * K ^ n) := by ac_rfl
  rw [e1, e2]
  simp only [Nat.mul_add]
  omega

/-- **One Fiat–Shamir round over a Merkle tree's leaves drawn from the
    oracle** (`fs_openA` over `comM`, `pfM`): each leaf's hash the answer of
    the commitment's table at its position, read off its data and its own
    salt; the opening shows the opened leaves' data and salts, the unopened
    leaves' salts hidden; leaves may share a position (no `hdist`); the bound
    gains `2 L s (k + L) / NSl + 2 L² s / NSl` a draw (`pfM_hidesC`). -/
theorem fs_openROMMC {PV PB D O P : Type} {NR m e1 e2 K n NSl L s k : Nat} (hK : 0 < K) (hN : 0 < NSl)
    (pos : D → Nat → Nat → Nat)
    (hlt : ∀ d l a, l < L → pos d l a < n) (g : O → List Nat → P)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s) (nxt : P → Nat → List Nat → Nat) (isO : Nat → Bool)
    (op : D → O) (hposO : ∀ d d', op d = op d' → ∀ l a, isO l = true → pos d l a = pos d' l a) (sd : O → D) (d0 : D)
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
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H % Q4)) && E H ((comM K NSl L pos) (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H % Q4))
            r t)).map (fun _ => (pfM K NSl L k pos isO op g nxt) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H % Q4))
            r t)))))) ≤
    sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) ((comM K NSl L pos) (sd (sop r t)) σ) H c) ((comM K NSl L pos) (sd (sop r t)) σ)
        (some ((pfM K NSl L k pos isO op g nxt) (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ (K ^ L) * ((NSl ^ L * K ^ n) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * ((L * (K ^ n * (NSl ^ (L - 1) * (2 * (s * (k + L))))) + 2 * (L * (L * (NSl ^ (L - 1) * s))) * K ^ n))))) ∧
    sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) ((comM K NSl L pos) (sd (sop r t)) σ) H c) ((comM K NSl L pos) (sd (sop r t)) σ)
        (some ((pfM K NSl L k pos isO op g nxt) (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H % Q4)) && E H ((comM K NSl L pos) (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H % Q4))
            r t)).map (fun _ => (pfM K NSl L k pos isO op g nxt) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H % Q4))
            r t)))))) +
    (Q4 * Q4) ^ (K ^ L) * ((NSl ^ L * K ^ n) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * ((L * (K ^ n * (NSl ^ (L - 1) * (2 * (s * (k + L))))) + 2 * (L * (L * (NSl ^ (L - 1) * s))) * K ^ n))))) := by
  have hcom : ComHidesA (NSl ^ L * K ^ n) (L * (K ^ n * (NSl ^ (L - 1) * (2 * (s * (k + L))))) + 2 * (L * (L * (NSl ^ (L - 1) * s))) * K ^ n) (comM K NSl L pos) :=
    fun d d' E => Nat.le_trans (pfM_hidesC (n := n) (L := L) (k := 0) (O := Unit) (P := Unit) hK hN pos hlt hs
      (fun _ => false) (fun _ => ()) (fun _ _ _ _ _ h => absurd h Bool.false_ne_true) (fun _ _ => ()) (fun _ _ _ => 0)
      d d' rfl (fun c _ => E c)) (Nat.add_le_add_left (Nat.add_le_add_right
        (Nat.mul_le_mul (unop_le L _) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.zero_le k) L)))))) _) _)
  have hpf : ComPfHidesA (NSl ^ L * K ^ n) (L * (K ^ n * (NSl ^ (L - 1) * (2 * (s * (k + L))))) + 2 * (L * (L * (NSl ^ (L - 1) * s))) * K ^ n) (comM K NSl L pos) (pfM K NSl L k pos isO op g nxt) op :=
    fun d d' hop E => Nat.le_trans (pfM_hidesC hK hN pos hlt hs isO op hposO g nxt d d' hop E)
      (Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_right _ (unop_le L isO)) _) _)
  have hrange : ∀ d σ, comM K NSl L pos d σ < K ^ L := fun d σ => by
    have h := rgetL_lt hK (posAll pos L NSl d (σ % NSl ^ L)) (σ / NSl ^ L)
    rwa [posAll_length] at h
  exact fs_openA (comM K NSl L pos) (pfM K NSl L k pos isO op g nxt) op sd d0 hcom hpf hrange ov hovn main hsd sop
    h1 h2 hrv hsv hrvo hsvo E

/-- **`pfM_hidesC`'s hypotheses, met by Plonky3's leaf hash**: a leaf's
    position its salt and its row's hash `h` (no leaf index), the opened
    data the opened rows' hashes; two leaves with equal rows and salts
    meet. -/
theorem collide_sat (L NSl M : Nat) (hL : 2 ≤ L) (hN : 0 < NSl) (hM : 0 < M) (isO : Nat → Bool) :
    let pos := fun (d : Nat → Nat) (l a : Nat) => a % NSl + NSl * (d l % M)
    let op := fun (d : Nat → Nat) (l : Nat) => if isO l = true then d l % M else 0
    (∀ d l a, l < L → pos d l a < NSl * M) ∧
    (∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ 1) ∧
    (∀ d d', op d = op d' → ∀ l a, isO l = true → pos d l a = pos d' l a) ∧
    (0 < L ∧ 1 < L ∧ ∀ a, pos (fun _ => 0) 0 a = pos (fun _ => 0) 1 a) := by
  intro pos op
  refine ⟨fun d l a _ => ?_, fun d l v => ?_, fun d d' hop l a hO => ?_, by omega, by omega, fun _ => rfl⟩
  · show a % NSl + NSl * (d l % M) < NSl * M
    have h1 : d l % M + 1 ≤ M := Nat.mod_lt _ hM
    calc a % NSl + NSl * (d l % M) < NSl + NSl * (d l % M) := Nat.add_lt_add_right (Nat.mod_lt _ hN) _
      _ = NSl * (d l % M + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ NSl * M := Nat.mul_le_mul_left _ h1
  · have one := hs_one (D := Nat → Nat) NSl d 0 0 Nat.one_pos (v % NSl)
    refine Nat.le_trans (sumTo_mono _ (fun x hx => ?_)) one
    show indB (decide (x % NSl + NSl * (d l % M) = v)) ≤ indB (decide (x = v % NSl))
    by_cases e : x % NSl + NSl * (d l % M) = v
    · have : x = v % NSl := by
        rw [← e, Nat.add_mul_mod_self_left, Nat.mod_mod, Nat.mod_eq_of_lt hx]
      rw [decide_eq_true this]; exact indB_le _
    · simp only [e, decide_false, indB]; exact Nat.zero_le _
  · have := congrFun hop l
    simp only [op, hO, if_true] at this
    show a % NSl + NSl * (d l % M) = a % NSl + NSl * (d' l % M)
    rw [this]

end Circuit
