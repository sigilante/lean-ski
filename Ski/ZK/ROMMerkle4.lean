import Ski.ZK.ROMRounds
import Ski.ZK.ROMMerkleOpen

/-!
# Four rounds over a Merkle tree's leaves, the opened set read at the challenge

`Ski/ZK/ROMMerkleOpen.lean` opens a fixed set of leaves.  In the four-round
proofs the leaves opened are those the query challenge `c4` names, and `c4`
is hashed from the transcript, the commitment's value among it.  The ideal
opening is padded to `L` extra digits, which the unopened leaves read in
part (`rsetL_mod`), so one salt range serves every opened set
(`pfMIP_hides`); the real and ideal openings differ only where a query hits
an unopened leaf, the opened set read off the commitment on both sides
(`pfMc_pfMI`); each leaf's hits are counted over its own salt, the swap at
its position leaving the opened set, the opened data and the shown salts
free of that salt (`hitLeafc_bound`), `L s k / NSl` in all (`hitMc_bound`);
the transfer runs inside the other draws' count (`transferMc_in`), and
`fs_open4` holds at the padded ideal openings (`fs_open4ROMM`), and with a
root of the leaves hashed in their place (`fs_open4ROMMR`).
-/

set_option autoImplicit false
namespace Circuit
open ZKF

theorem mod_mul_div {K M u : Nat} (hK : 0 < K) : u % (K * M) / K = u / K % M := by
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; rw [Nat.mul_zero, Nat.mod_zero, Nat.mod_zero]
  · have hr : u % (K * M) / K < M := (Nat.div_lt_iff_lt_mul hK).2 (by rw [Nat.mul_comm]; exact Nat.mod_lt _ (Nat.mul_pos h hK))
    have h1 : u = u % (K * M) + K * (M * (u / (K * M))) := by
      rw [← Nat.mul_assoc, Nat.add_comm]; exact (Nat.div_add_mod u (K * M)).symm
    have h2 : u / K = u % (K * M) / K + M * (u / (K * M)) := by
      conv => lhs; rw [h1]
      rw [Nat.add_mul_div_left _ _ hK]
    rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

theorem rsetL_mod {K : Nat} (hK : 0 < K) : ∀ (ps : List Nat) (H u : Nat), rsetL K ps H u = rsetL K ps H (u % K ^ ps.length)
  | [], _, _ => rfl
  | p :: ps, H, u => by
    show rsetL K ps (rset K p H (u % K)) (u / K) = rsetL K ps (rset K p H (u % K ^ (ps.length + 1) % K)) (u % K ^ (ps.length + 1) / K)
    have e1 : u % K ^ (ps.length + 1) % K = u % K := by
      rw [Nat.pow_succ', Nat.mod_mul_right_mod]
    have e2 : u % K ^ (ps.length + 1) / K = u / K % K ^ ps.length := by
      rw [Nat.pow_succ', mod_mul_div hK]
    rw [e1, e2, rsetL_mod hK ps _ (u / K), rsetL_mod hK ps _ (u / K % K ^ ps.length), Nat.mod_mod]

theorem unop_le (L : Nat) (isO : Nat → Bool) : (unop L isO).length ≤ L := by
  unfold unop; exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (lr_length L))

/-- **The ideal opening padded to `L` extra digits hides exactly**, the
    digits past the unopened leaves read by nothing: so one salt range serves
    every opened set. -/
theorem pfMIP_hides {D O P : Type} {K n NSl L k : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (isO : Nat → Bool) (op : D → O) (hposO : ∀ d d', op d = op d' → ∀ l a, isO l = true → pos d l a = pos d' l a)
    (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) :
    ComPfHides (NSl ^ L * K ^ n * K ^ L) (comMI K NSl L L pos) (pfMI K NSl L L k pos isO op g nxt) op := by
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
  rw [key d, key d', pfMI_hides hK pos hdist hlt isO op hposO g nxt d d' hop E]

/-- **With the opened set read off the commitment, the real and the padded
    ideal openings differ only where a query hits an unopened leaf**: the
    commitment, and so the opened set `isOf (c4f c)` and data `op1 (c4f c)`,
    is the same on both sides. -/
theorem pfMc_pfMI {D O P : Type} {K NSl L k : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (isOf : Nat → Nat → Bool) (op1 : Nat → D → O) (c4f : Nat → Nat) (g : O → List Nat → P)
    (nxt : P → Nat → List Nat → Nat) (F : Nat → P × List Nat → Bool) (d : D) (σ : Nat) :
    let c := comM K NSl L pos d σ
    let hit := hitL K (posU pos L NSl (isOf (c4f c)) d (σ % NSl ^ L))
      (nxt (g (op1 (c4f c) d) (shownS NSl L (isOf (c4f c)) (σ % NSl ^ L)))) c k (σ / NSl ^ L)
    K ^ L * indB (F c (pfM K NSl L k pos (isOf (c4f c)) (op1 (c4f c)) g nxt d σ)) ≤
      sumTo (K ^ L) (fun u => indB (F (comMI K NSl L L pos d (u + K ^ L * σ))
        (pfMI K NSl L L k pos (isOf (c4f (comMI K NSl L L pos d (u + K ^ L * σ))))
          (op1 (c4f (comMI K NSl L L pos d (u + K ^ L * σ)))) g nxt d (u + K ^ L * σ)))) + K ^ L * indB hit := by
  intro c hit
  have eq : ∀ u, u < K ^ L → (comMI K NSl L L pos d (u + K ^ L * σ),
      pfMI K NSl L L k pos (isOf (c4f (comMI K NSl L L pos d (u + K ^ L * σ))))
        (op1 (c4f (comMI K NSl L L pos d (u + K ^ L * σ)))) g nxt d (u + K ^ L * σ)) =
      (c, (g (op1 (c4f c) d) (shownS NSl L (isOf (c4f c)) (σ % NSl ^ L)),
        runQ K (nxt (g (op1 (c4f c) d) (shownS NSl L (isOf (c4f c)) (σ % NSl ^ L)))) c k
          (rsetL K (posU pos L NSl (isOf (c4f c)) d (σ % NSl ^ L)) (σ / NSl ^ L) u))) :=
    fun u hu => by obtain ⟨e1, e2⟩ := digit_dec (σ := σ) hu; simp only [pfMI, comMI, e1, e2]; rfl
  cases hh : hit
  · have hq := hitL_false hh
    have e : sumTo (K ^ L) (fun u => indB (F (comMI K NSl L L pos d (u + K ^ L * σ))
        (pfMI K NSl L L k pos (isOf (c4f (comMI K NSl L L pos d (u + K ^ L * σ))))
          (op1 (c4f (comMI K NSl L L pos d (u + K ^ L * σ)))) g nxt d (u + K ^ L * σ)))) =
        K ^ L * indB (F c (pfM K NSl L k pos (isOf (c4f c)) (op1 (c4f c)) g nxt d σ)) := by
      rw [show K ^ L * indB (F c (pfM K NSl L k pos (isOf (c4f c)) (op1 (c4f c)) g nxt d σ)) =
        sumTo (K ^ L) (fun _ => indB (F c (pfM K NSl L k pos (isOf (c4f c)) (op1 (c4f c)) g nxt d σ))) from
        (sumTo_const _ _).symm]
      refine sumTo_congr _ (fun u hu => ?_)
      have e3 := eq u hu
      rw [Prod.mk.injEq] at e3
      rw [e3.2, e3.1, (runQ_rsetL hK _ _ k _ _ u hq).1]
      rfl
    rw [e]; exact Nat.le_add_right _ _
  · have b1 : K ^ L * indB (F c (pfM K NSl L k pos (isOf (c4f c)) (op1 (c4f c)) g nxt d σ)) ≤ K ^ L * indB true :=
      Nat.mul_le_mul_left _ (indB_le _)
    exact Nat.le_trans b1 (Nat.le_add_left _ _)

theorem any_unop_le (isO : Nat → Bool) (f : Nat → Nat) (Pr : Nat → Bool) : ∀ L,
    indB (((unop L isO).map f).any Pr) ≤ sumTo L (fun l => indB (!isO l && Pr (f l)))
  | 0 => Nat.zero_le _
  | L + 1 => by
    have ih := any_unop_le isO f Pr L
    show indB ((((L :: lr L).filter (fun l => !isO l)).map f).any Pr) ≤
      sumTo L (fun l => indB (!isO l && Pr (f l))) + indB (!isO L && Pr (f L))
    cases h : isO L
    · rw [List.filter_cons_of_pos (by rw [h]; rfl), List.map_cons, List.any_cons]
      show indB (Pr (f L) || ((unop L isO).map f).any Pr) ≤ _
      cases Pr (f L)
      · simp only [Bool.false_or, Bool.not_false, Bool.and_false, indB] at ih ⊢; omega
      · simp only [Bool.true_or, Bool.not_false, Bool.and_true, indB]; omega
    · rw [List.filter_cons_of_neg (by rw [h]; exact Bool.false_ne_true)]
      simp only [Bool.not_true, Bool.false_and, indB, Nat.add_zero]
      exact ih

/-- **With the opened set read off the commitment, an unopened leaf's
    position is hit by few draws**: the swap at the leaf's position leaves
    the opened set, the opened data and the shown salts free of its salt. -/
theorem hitLeafc_bound {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isOf : Nat → Nat → Bool) (op1 : Nat → D → O) (c4f : Nat → Nat) (g : O → List Nat → P)
    (nxt : P → Nat → List Nat → Nat) (d : D) {l : Nat} (hl : l < L) :
    sumTo (NSl ^ L) (fun σh => sumTo (K ^ n) (fun h =>
      indB (!isOf (c4f (rgetL K (posAll pos L NSl d σh) h)) l &&
        decide (pos d l (lsalt NSl l σh) ∈ qposQ K (nxt (g (op1 (c4f (rgetL K (posAll pos L NSl d σh) h)) d)
          (shownS NSl L (isOf (c4f (rgetL K (posAll pos L NSl d σh) h))) σh))) (rgetL K (posAll pos L NSl d σh) h) k h)))) ≤
      K ^ n * (NSl ^ (L - l - 1) * (NSl ^ l * (s * k))) := by
  let Ev := fun (σh : Nat) (c H : Nat) => !isOf (c4f c) l &&
    decide (pos d l (lsalt NSl l σh) ∈ qposQ K (nxt (g (op1 (c4f c) d) (shownS NSl L (isOf (c4f c)) σh))) c k H)
  let f := fun (σh a H : Nat) => indB (Ev σh (rgetL K (posAll pos L NSl d σh) (rset K (pos d l (lsalt NSl l σh)) H a)) H)
  have swap : ∀ σh, K * sumTo (K ^ n) (fun h => indB (Ev σh (rgetL K (posAll pos L NSl d σh) h) h)) =
      sumTo (K ^ n) (fun H => sumTo K (fun a => f σh a H)) := fun σh => by
    rw [← reprog_swap hK (hlt d l (lsalt NSl l σh) hl) (fun a H => f σh a H), sumTo_mul]
    refine sumTo_congr _ (fun h _ => ?_)
    rw [← sumTo_const _ K]
    refine sumTo_congr _ (fun u hu => ?_)
    show _ = indB (Ev σh (rgetL K (posAll pos L NSl d σh) (rset K (pos d l (lsalt NSl l σh))
      (rset K (pos d l (lsalt NSl l σh)) h u) (rget K (pos d l (lsalt NSl l σh)) h))) (rset K (pos d l (lsalt NSl l σh)) h u))
    rw [rset_back hK hu]
    simp only [Ev, decide_eq_decide.2 (hit_rset hK hu _ _ k h)]
  have per : ∀ H a, a < K → sumTo (NSl ^ L) (fun σh => f σh a H) ≤ NSl ^ (L - l - 1) * (NSl ^ l * (s * k)) := by
    intro H a ha
    rw [sum_split_digit NSl L l hl, ← sumTo_const (NSl ^ l * (s * k)) (NSl ^ (L - l - 1))]
    refine sumTo_mono _ (fun hi _ => ?_)
    rw [sumTo_exch _ (NSl ^ l) NSl, ← sumTo_const (s * k) (NSl ^ l)]
    refine sumTo_mono _ (fun lo hlo => ?_)
    let c0 := rgetL K (posAll pos L NSl d (lo + NSl ^ l * (0 + NSl * hi))) (rset K (pos d l 0) H a)
    have e : ∀ x, x < NSl → f (lo + NSl ^ l * (x + NSl * hi)) a H = indB (!isOf (c4f c0) l && decide (pos d l x ∈
        qposQ K (nxt (g (op1 (c4f c0) d) (shownS NSl L (isOf (c4f c0)) (lo + NSl ^ l * (0 + NSl * hi))))) c0 k H)) :=
      fun x hx => by
      show indB (Ev (lo + NSl ^ l * (x + NSl * hi)) (rgetL K (posAll pos L NSl d (lo + NSl ^ l * (x + NSl * hi)))
        (rset K (pos d l (lsalt NSl l (lo + NSl ^ l * (x + NSl * hi)))) H a)) H) = _
      rw [lsalt_at hlo hx, comM_eq hK hN pos hdist d hl hlo hx ha]
      show indB (!isOf (c4f c0) l && decide (pos d l (lsalt NSl l (lo + NSl ^ l * (x + NSl * hi))) ∈ _)) = _
      cases hO : isOf (c4f c0) l
      · rw [lsalt_at hlo hx, shownS_eq hN hO hlo hx]
      · rfl
    rw [sumTo_congr _ e]
    cases hO : isOf (c4f c0) l
    · simp only [Bool.not_false, Bool.true_and]
      have h := salts_in (pos d l) (hs d l) (qposQ K (nxt (g (op1 (c4f c0) d)
        (shownS NSl L (isOf (c4f c0)) (lo + NSl ^ l * (0 + NSl * hi))))) c0 k H)
      rwa [qposQ_length] at h
    · simp only [Bool.not_true, Bool.false_and, indB, sumTo_const, Nat.mul_zero]; exact Nat.zero_le _
  refine Nat.le_of_mul_le_mul_left ?_ hK
  rw [sumTo_mul, sumTo_congr _ (fun σh _ => swap σh), sumTo_exch _ (K ^ n) (NSl ^ L)]
  rw [show K * (K ^ n * (NSl ^ (L - l - 1) * (NSl ^ l * (s * k)))) =
    sumTo (K ^ n) (fun _ => sumTo K (fun _ => NSl ^ (L - l - 1) * (NSl ^ l * (s * k)))) by
      rw [sumTo_const, sumTo_const]; ac_rfl]
  refine sumTo_mono _ (fun H _ => ?_)
  rw [sumTo_exch _ K (NSl ^ L)]
  exact sumTo_mono _ (fun a ha => per H a ha)

/-- **With the opened set read off the commitment, the draws that hit an
    unopened leaf are few**: `L Kⁿ NSl^(L-1) s k`, `L s k / NSl` normalized. -/
theorem hitMc_bound {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isOf : Nat → Nat → Bool) (op1 : Nat → D → O) (c4f : Nat → Nat) (g : O → List Nat → P)
    (nxt : P → Nat → List Nat → Nat) (d : D) :
    sumTo (NSl ^ L * K ^ n) (fun σ => indB (hitL K (posU pos L NSl (isOf (c4f (comM K NSl L pos d σ))) d (σ % NSl ^ L))
      (nxt (g (op1 (c4f (comM K NSl L pos d σ)) d) (shownS NSl L (isOf (c4f (comM K NSl L pos d σ))) (σ % NSl ^ L))))
      (comM K NSl L pos d σ) k (σ / NSl ^ L))) ≤ L * (K ^ n * (NSl ^ (L - 1) * (s * k))) := by
  rw [sumTo_split (NSl ^ L), sumTo_exch _ (NSl ^ L) (K ^ n)]
  have e : ∀ σh, σh < NSl ^ L → ∀ h, indB (hitL K (posU pos L NSl (isOf (c4f (comM K NSl L pos d (σh + NSl ^ L * h)))) d
      ((σh + NSl ^ L * h) % NSl ^ L)) (nxt (g (op1 (c4f (comM K NSl L pos d (σh + NSl ^ L * h))) d)
      (shownS NSl L (isOf (c4f (comM K NSl L pos d (σh + NSl ^ L * h)))) ((σh + NSl ^ L * h) % NSl ^ L))))
      (comM K NSl L pos d (σh + NSl ^ L * h)) k ((σh + NSl ^ L * h) / NSl ^ L)) ≤
      sumTo L (fun l => indB (!isOf (c4f (rgetL K (posAll pos L NSl d σh) h)) l &&
        decide (pos d l (lsalt NSl l σh) ∈ qposQ K (nxt (g (op1 (c4f (rgetL K (posAll pos L NSl d σh) h)) d)
          (shownS NSl L (isOf (c4f (rgetL K (posAll pos L NSl d σh) h))) σh))) (rgetL K (posAll pos L NSl d σh) h) k h))) :=
    fun σh hσ h => by
    obtain ⟨f1, f2⟩ := digit_dec (σ := h) hσ
    simp only [comM, f1, f2]
    exact any_unop_le _ _ _ L
  refine Nat.le_trans (sumTo_mono _ (fun σh hσ => sumTo_mono _ (fun h _ => e σh hσ h))) ?_
  rw [sumTo_congr _ (fun σh _ => sumTo_exch _ _ _), sumTo_exch _ L (NSl ^ L),
    ← sumTo_const (K ^ n * (NSl ^ (L - 1) * (s * k))) L]
  refine sumTo_mono _ (fun l hl => ?_)
  refine Nat.le_trans (hitLeafc_bound (k := k) hK hN pos hdist hlt hs isOf op1 c4f g nxt d hl) (Nat.le_of_eq ?_)
  rw [← Nat.mul_assoc (NSl ^ (L - l - 1)), ← Nat.pow_add]
  congr 3; omega

/-- **The transfer with the opened set read off the commitment**:
    `K^L` times the real count is at most the padded ideal count plus
    `K^L L Kⁿ NSl^(L-1) s k`. -/
theorem transferMc {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isOf : Nat → Nat → Bool) (op1 : Nat → D → O) (c4f : Nat → Nat) (g : O → List Nat → P)
    (nxt : P → Nat → List Nat → Nat) (F : Nat → P × List Nat → Bool) (d : D) :
    K ^ L * sumTo (NSl ^ L * K ^ n) (fun σ => indB (F (comM K NSl L pos d σ)
      (pfM K NSl L k pos (isOf (c4f (comM K NSl L pos d σ))) (op1 (c4f (comM K NSl L pos d σ))) g nxt d σ))) ≤
      sumTo (NSl ^ L * K ^ n * K ^ L) (fun σ => indB (F (comMI K NSl L L pos d σ)
        (pfMI K NSl L L k pos (isOf (c4f (comMI K NSl L L pos d σ))) (op1 (c4f (comMI K NSl L L pos d σ))) g nxt d σ))) +
        K ^ L * (L * (K ^ n * (NSl ^ (L - 1) * (s * k)))) := by
  have hb := hitMc_bound (n := n) (L := L) (k := k) hK hN pos hdist hlt hs isOf op1 c4f g nxt d
  have hk := Nat.mul_le_mul_left (K ^ L) hb
  rw [sum_digit (K ^ L) (NSl ^ L * K ^ n), sumTo_mul (K ^ L) _ (NSl ^ L * K ^ n)]
  refine Nat.le_trans (sumTo_mono _ (fun σ _ => pfMc_pfMI (NSl := NSl) (L := L) (k := k) hK pos isOf op1 c4f g nxt F d σ)) ?_
  rw [sumTo_add]
  exact Nat.add_le_add_left (Nat.le_trans (Nat.le_of_eq (sumTo_mul (K ^ L) _ _).symm) hk) _

/-- `transferMc` inside a count of the other draws, the data, the choice
    of opened set and the event read off them. -/
theorem transferMc_in {Y D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (so : (Y → Nat) → Nat)
    (hso : Lin so) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isOf : Nat → Nat → Bool) (op1 : Nat → D → O) (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat)
    (dat : Y → D) (c4f : Y → Nat → Nat) (G : Y → Nat → P × List Nat → Bool) :
    K ^ L * so (fun y => sumTo (NSl ^ L * K ^ n) (fun σ => indB (G y (comM K NSl L pos (dat y) σ)
      (pfM K NSl L k pos (isOf (c4f y (comM K NSl L pos (dat y) σ))) (op1 (c4f y (comM K NSl L pos (dat y) σ))) g nxt
        (dat y) σ)))) ≤
      so (fun y => sumTo (NSl ^ L * K ^ n * K ^ L) (fun σ => indB (G y (comMI K NSl L L pos (dat y) σ)
        (pfMI K NSl L L k pos (isOf (c4f y (comMI K NSl L L pos (dat y) σ))) (op1 (c4f y (comMI K NSl L L pos (dat y) σ)))
          g nxt (dat y) σ)))) +
        K ^ L * (L * (K ^ n * (NSl ^ (L - 1) * (s * k)))) * so (fun _ => 1) := by
  have t := fun y => transferMc (n := n) (k := k) hK hN pos hdist hlt hs isOf op1 (c4f y) g nxt (G y) (dat y)
  have eE := smC so hso (K ^ L * (L * (K ^ n * (NSl ^ (L - 1) * (s * k)))))
  rw [← smK so hso, ← eE, ← sm_add so hso]
  exact sm_mono so hso t
/-- **Four Fiat–Shamir rounds over a Merkle tree's leaves drawn from the
    oracle**: `fs_open4ROM` with the first commitment the leaves' answers
    (`comM`, its range `K = KA^L`), the opened set and data read at the drawn
    query challenge (`isOf c4`, `op1 c4`), and so off the commitment's
    value (`transferMc_in`); the ideal opening, padded to `L` digits, hides
    at each challenge (`pfMIP_hides`).  Normalized, the bound gains
    `L s k / NSl` a draw; one direction. -/
theorem fs_open4ROMM {PV PB D O Pq D2 O2 P2 D3 O3 P3 W : Type}
    {K KA NR m e1 e2 NSl L s k n NS2 NS3 K2 K3 K4 n2 n3 : Nat}
    (hKA : 0 < KA) (hN : 0 < NSl) (hKL : K = KA ^ L) (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φ : Nat → W → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (rv sv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (g4 : Nat → Bool) {B4 : Nat} (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hrv : ∀ c4 c2 c3 α β r t, rv c4 c2 c3 α β r t = none ∨ ∃ p x y, rv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c4 c2 c3 α β r t, ∃ p x y, sv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (oz : TViewN PV PB → W) (hoz : ∀ c4 c2 c3 α β r t, oz (rv c4 c2 c3 α β r t) = oz (rv 0 c2 c3 α β r t))
    (h1 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) + e1 + e2)
    (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b)
    (hlt : ∀ d l a, l < L → pos d l a < n) (g : O → List Nat → Pq)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (nxt : Pq → Nat → List Nat → Nat) (op1 : Nat → D → O) (isOf : Nat → Nat → Bool)
    (hposO : ∀ c4 d d', op1 c4 d = op1 c4 d' → ∀ l a, isOf c4 l = true → pos d l a = pos d' l a) (sd1 : Nat → O → D) (d1 : D)
    (ov1 : Nat → TViewN PV PB → Option O) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : Nat → TViewN PV PB → Option O3) (hov3 : ∀ c4, ov3 c4 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r))
    (hvo1 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 c4 (main1 t r)))
    (hvo2 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 c4 (main2 c t r)))
    (hvo3 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN PV PB → Bool) :
    let Com1 := comM KA NSl L pos
    let Pf1 := fun c4 => pfM KA NSl L k pos (isOf c4) (op1 c4) g nxt
    let Cmi := comMI KA NSl L L pos
    let Pfi := fun c4 => pfMI KA NSl L L k pos (isOf c4) (op1 c4) g nxt
    let smR := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ n) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ, r, t)))))
    let smI := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ n * K) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + K * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + K * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 _c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + K * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + K * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let sm4I := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => smI (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    K * (K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
      indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
        (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
    sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => sumTo (K3 ^ (K * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => smI (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
          (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K2 * (K3 * (NSl ^ L * KA ^ n * K * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NSl ^ L * KA ^ n * K * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4I (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * K3) * (K4 ^ N4 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K * (L * (KA ^ n * (NSl ^ (L - 1) * (s * k)))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))))))))) := by
  subst hKL
  have hc1 : ComHides (NSl ^ L * KA ^ n * KA ^ L) (comMI KA NSl L L pos) := fun d d' E =>
    pfMIP_hides (k := 0) (O := Unit) (P := Unit) hKA pos hdist hlt (fun _ => false) (fun _ => ())
      (fun _ _ _ _ _ h => absurd h Bool.false_ne_true) (fun _ _ => ()) (fun _ _ _ => 0) d d' rfl (fun c _ => E c)
  have hr1 : ∀ d σ, comMI KA NSl L L pos d σ < KA ^ L := fun d σ => by
    have h := rgetL_lt hKA (posAll pos L NSl d (σ / KA ^ L % NSl ^ L)) (σ / KA ^ L / NSl ^ L)
    rwa [posAll_length] at h
  intro Com1 Pf1 Cmi Pfi smR smI m1 m2 m3 rvo s1 s2 s3 svo sm4 sm4I r1 r2 r3 Mq
  have fo := fs_open4 (NS1 := NSl ^ L * KA ^ n * (KA ^ L)) (n1 := (KA ^ L)) hK2 hK3 hK4 φ hφ rv sv gz hgz g4 hB4 hrv hsv oz hoz
    h1 h2 Cmi Pfi op1 sd1 d1 hc1 (fun c4 => pfMIP_hides hKA pos hdist hlt (isOf c4) (op1 c4) (hposO c4) g nxt) hr1 ov1 hov1 main1 hsd1
    Com2 Pf2 op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 Com3 Pf3 op3 sd3 d3 hc3 hp3 hr3 ov3 hov3 main3 hsd3
    hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E
  -- the query challenge and the event, read off the first commitment's value `c`
  let c4f := fun (H1 H2 H3 H4 : Nat) (y : Nat × Nat × (Nat → Tup)) (c : Nat) =>
    let c1 := rget (Q4 * Q4) c H1
    let c2 := rget K2 (c + (KA ^ L) * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)) H2
    let mm3 := c + (KA ^ L) * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H3
    rget K4 (φ mm3 (oz (rv 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2))) H4
  let ev := fun (H1 H2 H3 H4 : Nat) (y : Nat × Nat × (Nat → Tup)) (c : Nat) (pf : Pq × List Nat) =>
    let c1 := rget (Q4 * Q4) c H1
    let mm2 := c + (KA ^ L) * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)
    let c2 := rget K2 mm2 H2
    let mm3 := c + (KA ^ L) * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H3
    let c4 := c4f H1 H2 H3 H4 y c
    E H1 H2 H3 H4 c mm2 mm3
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map (fun _ => pf),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)
  have hso := smT_lin (NS2 * NS3) NR m
  have so1 := smT_one (NS2 * NS3) NR m
  have step : ∀ H4 H1 H2 H3,
      (KA ^ L) * smR (fun x => indB (ev H1 H2 H3 H4 x.2 (Com1 (main1 x.2.2.2 x.2.2.1) x.1)
        (Pf1 (c4f H1 H2 H3 H4 x.2 (Com1 (main1 x.2.2.2 x.2.2.1) x.1)) (main1 x.2.2.2 x.2.2.1) x.1))) ≤
      smI (fun x => indB (ev H1 H2 H3 H4 x.2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)
        (Pfi (c4f H1 H2 H3 H4 x.2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)) (main1 x.2.2.2 x.2.2.1) x.1))) +
        (KA ^ L) * (L * (KA ^ n * (NSl ^ (L - 1) * (s * k)))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))) := fun H4 H1 H2 H3 => by
    have tr := transferMc_in (n := n) (NSl := NSl) (L := L) (s := s) (k := k) hKA hN (smT (NS2 * NS3) NR m) hso
      pos hdist hlt hs isOf op1 g nxt (fun y => main1 y.2.2 y.2.1) (fun y c => c4f H1 H2 H3 H4 y c)
      (fun y c pf => ev H1 H2 H3 H4 y c pf)
    rw [hso, hso, so1] at tr
    exact tr
  have hb : ∀ X : Nat → Nat → Nat → Nat → Nat, (KA ^ L) * (K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 =>
      sumTo ((Q4 * Q4) ^ (KA ^ L)) (fun H1 => sumTo (K2 ^ ((KA ^ L) * n2)) (fun H2 =>
        sumTo (K3 ^ ((KA ^ L) * (n2 * n3))) (fun H3 => X H4 H1 H2 H3)))))) =
      K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 =>
      sumTo ((Q4 * Q4) ^ (KA ^ L)) (fun H1 => sumTo (K2 ^ ((KA ^ L) * n2)) (fun H2 =>
        sumTo (K3 ^ ((KA ^ L) * (n2 * n3))) (fun H3 => (KA ^ L) * X H4 H1 H2 H3))))) := fun X => by
    rw [Nat.mul_left_comm (KA ^ L) K4, Nat.mul_left_comm (KA ^ L) (Q4 * Q4 * (K2 * K3)), sumTo_mul]
    exact congrArg (fun z => K4 * (Q4 * Q4 * (K2 * K3) * z)) (sumTo_congr _ (fun H4 _ =>
      (sumTo_mul _ _ _).trans (sumTo_congr _ (fun H1 _ =>
        (sumTo_mul _ _ _).trans (sumTo_congr _ (fun H2 _ => sumTo_mul _ _ _))))))
  rw [hb]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (sumTo_mono _ (fun H4 _ => sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ =>
      sumTo_mono _ (fun H3 _ => step H4 H1 H2 H3))))))) ?_
  simp only [sumTo_add, sumTo_const]
  rw [Nat.mul_add (Q4 * Q4 * (K2 * K3)), Nat.mul_add K4]
  exact Nat.add_le_add_right fo _

/-- **Four Fiat–Shamir rounds over a Merkle tree's root drawn from the
    oracle**: `fs_open4ROMM` with the root `R` of the leaves' answers hashed
    in their place, its range `K`; the transfer pads with `KT = KA^L` digits.
    Normalized, the bound gains `L s k / NSl` a draw; one direction. -/
theorem fs_open4ROMMR {PV PB D O Pq D2 O2 P2 D3 O3 P3 W : Type}
    {K KA KT NR m e1 e2 NSl L s k n NS2 NS3 K2 K3 K4 n2 n3 : Nat}
    (hKA : 0 < KA) (hN : 0 < NSl) (hKT : KT = KA ^ L) (R : Nat → Nat) (hR : ∀ c, R c < K) (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φ : Nat → W → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (rv sv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (g4 : Nat → Bool) {B4 : Nat} (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hrv : ∀ c4 c2 c3 α β r t, rv c4 c2 c3 α β r t = none ∨ ∃ p x y, rv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c4 c2 c3 α β r t, ∃ p x y, sv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (oz : TViewN PV PB → W) (hoz : ∀ c4 c2 c3 α β r t, oz (rv c4 c2 c3 α β r t) = oz (rv 0 c2 c3 α β r t))
    (h1 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) + e1 + e2)
    (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b)
    (hlt : ∀ d l a, l < L → pos d l a < n) (g : O → List Nat → Pq)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (nxt : Pq → Nat → List Nat → Nat) (op1 : Nat → D → O) (isOf : Nat → Nat → Bool)
    (hposO : ∀ c4 d d', op1 c4 d = op1 c4 d' → ∀ l a, isOf c4 l = true → pos d l a = pos d' l a) (sd1 : Nat → O → D) (d1 : D)
    (ov1 : Nat → TViewN PV PB → Option O) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : Nat → TViewN PV PB → Option O3) (hov3 : ∀ c4, ov3 c4 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r))
    (hvo1 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 c4 (main1 t r)))
    (hvo2 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 c4 (main2 c t r)))
    (hvo3 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN PV PB → Bool) :
    let Com1 := rootM R KA NSl L pos
    let Pf1 := fun c4 => pfM KA NSl L k pos (isOf c4) (op1 c4) g nxt
    let Cmi := fun (d : D) (σ : Nat) => R (comMI KA NSl L L pos d σ)
    let Pfi := fun c4 => pfMI KA NSl L L k pos (isOf c4) (op1 c4) g nxt
    let smR := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ n) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ, r, t)))))
    let smI := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ n * KT) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + K * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + K * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 _c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + K * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + K * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let sm4I := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => smI (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    KT * (K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
      indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
        (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
    sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => sumTo (K3 ^ (K * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => smI (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
          (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K2 * (K3 * (NSl ^ L * KA ^ n * KT * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NSl ^ L * KA ^ n * KT * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4I (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * K3) * (K4 ^ N4 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (KT * (L * (KA ^ n * (NSl ^ (L - 1) * (s * k)))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))))))))) := by
  subst hKT
  have hc1 : ComHides (NSl ^ L * KA ^ n * KA ^ L) (fun (d : D) (σ : Nat) => R (comMI KA NSl L L pos d σ)) := fun d d' E =>
    pfMIP_hides (k := 0) (O := Unit) (P := Unit) hKA pos hdist hlt (fun _ => false) (fun _ => ())
      (fun _ _ _ _ _ h => absurd h Bool.false_ne_true) (fun _ _ => ()) (fun _ _ _ => 0) d d' rfl (fun c _ => E (R c))
  have hp1 : ∀ c4, ComPfHides (NSl ^ L * KA ^ n * KA ^ L) (fun (d : D) (σ : Nat) => R (comMI KA NSl L L pos d σ))
      (pfMI KA NSl L L k pos (isOf c4) (op1 c4) g nxt) (op1 c4) := fun c4 d d' hop E =>
    pfMIP_hides hKA pos hdist hlt (isOf c4) (op1 c4) (hposO c4) g nxt d d' hop (fun c pf => E (R c) pf)
  intro Com1 Pf1 Cmi Pfi smR smI m1 m2 m3 rvo s1 s2 s3 svo sm4 sm4I r1 r2 r3 Mq
  have fo := fs_open4 (NS1 := NSl ^ L * KA ^ n * (KA ^ L)) (n1 := K) hK2 hK3 hK4 φ hφ rv sv gz hgz g4 hB4 hrv hsv oz hoz
    h1 h2 Cmi Pfi op1 sd1 d1 hc1 hp1 (fun _ _ => hR _) ov1 hov1 main1 hsd1
    Com2 Pf2 op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 Com3 Pf3 op3 sd3 d3 hc3 hp3 hr3 ov3 hov3 main3 hsd3
    hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E
  -- the query challenge and the event, read off the first commitment's value `c`
  let c4f := fun (H1 H2 H3 H4 : Nat) (y : Nat × Nat × (Nat → Tup)) (c : Nat) =>
    let c1 := rget (Q4 * Q4) c H1
    let c2 := rget K2 (c + K * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)) H2
    let mm3 := c + K * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H3
    rget K4 (φ mm3 (oz (rv 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2))) H4
  let ev := fun (H1 H2 H3 H4 : Nat) (y : Nat × Nat × (Nat → Tup)) (c : Nat) (pf : Pq × List Nat) =>
    let c1 := rget (Q4 * Q4) c H1
    let mm2 := c + K * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)
    let c2 := rget K2 mm2 H2
    let mm3 := c + K * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H3
    let c4 := c4f H1 H2 H3 H4 y c
    E H1 H2 H3 H4 c mm2 mm3
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map (fun _ => pf),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)
  have hso := smT_lin (NS2 * NS3) NR m
  have so1 := smT_one (NS2 * NS3) NR m
  have step : ∀ H4 H1 H2 H3,
      (KA ^ L) * smR (fun x => indB (ev H1 H2 H3 H4 x.2 (Com1 (main1 x.2.2.2 x.2.2.1) x.1)
        (Pf1 (c4f H1 H2 H3 H4 x.2 (Com1 (main1 x.2.2.2 x.2.2.1) x.1)) (main1 x.2.2.2 x.2.2.1) x.1))) ≤
      smI (fun x => indB (ev H1 H2 H3 H4 x.2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)
        (Pfi (c4f H1 H2 H3 H4 x.2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)) (main1 x.2.2.2 x.2.2.1) x.1))) +
        (KA ^ L) * (L * (KA ^ n * (NSl ^ (L - 1) * (s * k)))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))) := fun H4 H1 H2 H3 => by
    have tr := transferMc_in (n := n) (NSl := NSl) (L := L) (s := s) (k := k) hKA hN (smT (NS2 * NS3) NR m) hso
      pos hdist hlt hs isOf op1 g nxt (fun y => main1 y.2.2 y.2.1) (fun y c => c4f H1 H2 H3 H4 y (R c))
      (fun y c pf => ev H1 H2 H3 H4 y (R c) pf)
    rw [hso, hso, so1] at tr
    exact tr
  have hb : ∀ X : Nat → Nat → Nat → Nat → Nat, (KA ^ L) * (K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => X H4 H1 H2 H3)))))) =
      K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => (KA ^ L) * X H4 H1 H2 H3))))) := fun X => by
    rw [Nat.mul_left_comm (KA ^ L) K4, Nat.mul_left_comm (KA ^ L) (Q4 * Q4 * (K2 * K3)), sumTo_mul]
    exact congrArg (fun z => K4 * (Q4 * Q4 * (K2 * K3) * z)) (sumTo_congr _ (fun H4 _ =>
      (sumTo_mul _ _ _).trans (sumTo_congr _ (fun H1 _ =>
        (sumTo_mul _ _ _).trans (sumTo_congr _ (fun H2 _ => sumTo_mul _ _ _))))))
  rw [hb]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (sumTo_mono _ (fun H4 _ => sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ =>
      sumTo_mono _ (fun H3 _ => step H4 H1 H2 H3))))))) ?_
  simp only [sumTo_add, sumTo_const]
  rw [Nat.mul_add (Q4 * Q4 * (K2 * K3)), Nat.mul_add K4]
  exact Nat.add_le_add_right fo _
end Circuit
