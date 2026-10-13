import Ski.ZK.ROMHide

/-!
# A commitment to several leaves drawn from the oracle

`Ski/ZK/ROMHide.lean`'s commitment is one answer of its own table.  A
Merkle commitment hashes each leaf, its data with a salt, into a leaf
hash, and the root and the authentication paths are functions of the leaf
hashes.  Here the commitment is `L` leaf hashes, the answers of the
commitment's table at the leaves' salted positions (`comRL`), every
position depending on the hidden salt.  This is the step towards a Merkle
commitment, not yet the commitment itself: the opened leaves' salts are
never shown (a Merkle opening shows them, and which leaves open depends on
the later challenges), no two leaves share a position (`hnd`; salted leaves
with equal rows and salts would), the internal hashing is apart from the
leaves' table, and Fiat–Shamir hashes the leaf vector, not a root.  The ideal opening re-randomizes
every leaf's answer (`comIL`, `pfIL`), and hides exactly
(`reprog_swapL`, `pfIL_hides`, `comIL_hides`); the real opening differs
from it only where a query hits a leaf (`pfRL_pfIL`, `hitL_rsetL`), at most
`L s k / NSh` of the draws (`hitL_bound`), both ways (`transferRL`); so
the real opening hides up to `2 L s k / NSh` (`pfRL_hidesA`), and one
Fiat–Shamir round keeps its bound with that slack (`fs_openROML`).
-/

set_option autoImplicit false
namespace Circuit
open ZKF

/-- The answers at a list of positions, as digits base `K`. -/
def rgetL (K : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | p :: ps, H => rget K p H + K * rgetL K ps H

/-- The answers at a list of positions set from the digits of `u`. -/
def rsetL (K : Nat) : List Nat → Nat → Nat → Nat
  | [], H, _ => H
  | p :: ps, H, u => rsetL K ps (rset K p H (u % K)) (u / K)

theorem rgetL_rset {K p a : Nat} (hK : 0 < K) (ha : a < K) :
    ∀ (ps : List Nat), p ∉ ps → ∀ H, rgetL K ps (rset K p H a) = rgetL K ps H
  | [], _, _ => rfl
  | q :: qs, h, H => by
    have hq : q ≠ p := fun e => h (e ▸ List.mem_cons_self ..)
    have hs : p ∉ qs := fun e => h (List.mem_cons_of_mem _ e)
    show rget K q (rset K p H a) + K * rgetL K qs (rset K p H a) = rget K q H + K * rgetL K qs H
    rw [rget_rset_ne hK hq ha, rgetL_rset hK ha qs hs H]

/-- **Re-randomizing several answers is a bijection** (`reprog_swap` at a
    list of distinct positions): over the tables and the new answers `u`,
    the pair (the old answers, the new table) is every (answers, table)
    pair once. -/
theorem reprog_swapL {K n : Nat} (hK : 0 < K) :
    ∀ (ps : List Nat), ps.Nodup → (∀ p ∈ ps, p < n) → ∀ (f : Nat → Nat → Nat),
    sumTo (K ^ n) (fun H => sumTo (K ^ ps.length) (fun u => f (rgetL K ps H) (rsetL K ps H u))) =
      sumTo (K ^ n) (fun H => sumTo (K ^ ps.length) (fun c => f c H))
  | [], _, _, f => rfl
  | p :: qs, hnd, hlt, f => by
    have hp : p < n := hlt p (List.mem_cons_self ..)
    have hnq : p ∉ qs := (List.nodup_cons.1 hnd).1
    have hq := reprog_swapL (K := K) (n := n) hK qs (List.nodup_cons.1 hnd).2
      (fun q hq => hlt q (List.mem_cons_of_mem _ hq))
    show sumTo (K ^ n) (fun H => sumTo (K ^ (qs.length + 1)) (fun u =>
        f (rget K p H + K * rgetL K qs H) (rsetL K qs (rset K p H (u % K)) (u / K)))) =
      sumTo (K ^ n) (fun H => sumTo (K ^ (qs.length + 1)) (fun c => f c H))
    rw [Nat.pow_succ']
    have sp : ∀ g : Nat → Nat, sumTo (K * K ^ qs.length) g = sumTo (K ^ qs.length) (fun b => sumTo K (fun a => g (a + K * b))) :=
      fun g => sumTo_split K g _
    simp only [sp]
    have e1 : ∀ H, sumTo (K ^ qs.length) (fun b => sumTo K (fun a =>
        f (rget K p H + K * rgetL K qs H) (rsetL K qs (rset K p H ((a + K * b) % K)) ((a + K * b) / K)))) =
        sumTo K (fun a => sumTo (K ^ qs.length) (fun b =>
          f (rget K p H + K * rgetL K qs (rset K p H a)) (rsetL K qs (rset K p H a) b))) := fun H => by
      rw [sumTo_exch _ K (K ^ qs.length)]
      refine sumTo_congr _ (fun a ha => sumTo_congr _ (fun b _ => ?_))
      obtain ⟨d1, d2⟩ := digit_dec (σ := b) ha
      rw [Nat.add_comm a (K * b)] at d1 d2 ⊢
      rw [show (K * b + a) / K = b by rw [Nat.add_comm]; exact (digit_dec ha).1,
        show (K * b + a) % K = a by rw [Nat.add_comm]; exact (digit_dec ha).2, rgetL_rset hK ha qs hnq H]
    rw [sumTo_congr _ (fun H _ => e1 H)]
    rw [reprog_swap hK hp (fun c H' => sumTo (K ^ qs.length) (fun b => f (c + K * rgetL K qs H') (rsetL K qs H' b)))]
    calc sumTo (K ^ n) (fun H => sumTo K (fun c => sumTo (K ^ qs.length) (fun b =>
          f (c + K * rgetL K qs H) (rsetL K qs H b))))
        = sumTo K (fun c => sumTo (K ^ n) (fun H => sumTo (K ^ qs.length) (fun b =>
          f (c + K * rgetL K qs H) (rsetL K qs H b)))) := sumTo_exch _ _ _
      _ = sumTo K (fun c => sumTo (K ^ n) (fun H => sumTo (K ^ qs.length) (fun c' => f (c + K * c') H))) :=
          sumTo_congr _ (fun c _ => hq (fun c' H' => f (c + K * c') H'))
      _ = sumTo (K ^ n) (fun H => sumTo K (fun c => sumTo (K ^ qs.length) (fun c' => f (c + K * c') H))) :=
          (sumTo_exch _ _ _).symm
      _ = _ := sumTo_congr _ (fun H _ => sumTo_exch _ _ _)

/-- **A commitment to several leaves drawn from the oracle**: the answers of
    the commitment's table at the leaves' salted positions (`ps`, one list
    for the data and both salt parts), as digits; the root, any function of
    them, is an event of these. -/
def comRL {D : Type} (K NSh NSo : Nat) (ps : D → Nat → Nat → List Nat) (d : D) (σ' : Nat) : Nat :=
  rgetL K (ps d (saltO NSh NSo σ') (saltH NSh σ')) (saltT NSh NSo σ')

/-- Its opening, with the distinguisher's `k` queries into its table. -/
def pfRL {D O P : Type} (K NSh NSo k : Nat) (ps : D → Nat → Nat → List Nat) (op : D → O) (g : O → Nat → P)
    (nxt : P → Nat → List Nat → Nat) (d : D) (σ' : Nat) : P × List Nat :=
  (g (op d) (saltO NSh NSo σ'),
   runQ K (nxt (g (op d) (saltO NSh NSo σ'))) (comRL K NSh NSo ps d σ') k (saltT NSh NSo σ'))

/-- The commitment with `L` more salt digits, which it ignores. -/
def comIL {D : Type} (K NSh NSo L : Nat) (ps : D → Nat → Nat → List Nat) (d : D) (σ : Nat) : Nat :=
  comRL K NSh NSo ps d (σ / K ^ L)

/-- **The ideal opening**: the queries answered on the table with every
    leaf's answer re-randomized to the extra digits. -/
def pfIL {D O P : Type} (K NSh NSo L k : Nat) (ps : D → Nat → Nat → List Nat) (op : D → O) (g : O → Nat → P)
    (nxt : P → Nat → List Nat → Nat) (d : D) (σ : Nat) : P × List Nat :=
  (g (op d) (saltO NSh NSo (σ / K ^ L)),
   runQ K (nxt (g (op d) (saltO NSh NSo (σ / K ^ L)))) (comIL K NSh NSo L ps d σ) k
     (rsetL K (ps d (saltO NSh NSo (σ / K ^ L)) (saltH NSh (σ / K ^ L))) (saltT NSh NSo (σ / K ^ L)) (σ % K ^ L)))

/-- **The ideal opening of several leaves hides exactly** (`reprog_swapL`). -/
theorem pfIL_hides {D O P : Type} {K n NSh NSo L k : Nat} (hK : 0 < K) (ps : D → Nat → Nat → List Nat)
    (hnd : ∀ d σo σh, (ps d σo σh).Nodup) (hlen : ∀ d σo σh, (ps d σo σh).length = L)
    (hlt : ∀ d σo σh, ∀ p ∈ ps d σo σh, p < n) (op : D → O) (g : O → Nat → P) (nxt : P → Nat → List Nat → Nat) :
    ComPfHides (NSh * (NSo * K ^ n) * K ^ L) (comIL K NSh NSo L ps) (pfIL K NSh NSo L k ps op g nxt) op := by
  intro d d' hop E
  have hKL : 0 < K ^ L := Nat.pow_pos hK
  have key : ∀ dd : D, op dd = op d → sumTo (NSh * (NSo * K ^ n) * K ^ L) (fun σ =>
      indB (E (comIL K NSh NSo L ps dd σ) (pfIL K NSh NSo L k ps op g nxt dd σ))) =
      sumTo NSo (fun o => sumTo NSh (fun _ => sumTo (K ^ n) (fun H => sumTo (K ^ L) (fun c =>
        indB (E c (g (op d) o, runQ K (nxt (g (op d) o)) c k H)))))) := fun dd hdd => by
    rw [sum_digit, sum_salt_eq]
    refine sumTo_congr _ (fun o ho => sumTo_congr _ (fun σh hh => ?_))
    have r := reprog_swapL (n := n) hK (ps dd o σh) (hnd dd o σh) (hlt dd o σh)
      (fun c H => indB (E c (g (op d) o, runQ K (nxt (g (op d) o)) c k H)))
    rw [hlen dd o σh] at r
    rw [← r]
    refine sumTo_congr _ (fun h _ => sumTo_congr _ (fun u hu => ?_))
    obtain ⟨e1, e2⟩ := digit_dec (σ := σh + NSh * (o + NSo * h)) hu
    obtain ⟨a, b, c⟩ := salt_dec (h := h) hh ho
    simp only [pfIL, comIL, comRL, e1, e2, a, b, c, hdd]
  rw [key d rfl, key d' hop.symm]

/-- **The bare commitment to several leaves, with the extra digits, hides
    exactly.** -/
theorem comIL_hides {D : Type} {K n NSh NSo L : Nat} (hK : 0 < K) (ps : D → Nat → Nat → List Nat)
    (hnd : ∀ d σo σh, (ps d σo σh).Nodup) (hlen : ∀ d σo σh, (ps d σo σh).length = L)
    (hlt : ∀ d σo σh, ∀ p ∈ ps d σo σh, p < n) : ComHides (NSh * (NSo * K ^ n) * K ^ L) (comIL K NSh NSo L ps) := by
  intro d d' E
  have h := pfIL_hides (NSh := NSh) (NSo := NSo) (k := 0) (O := Unit) (P := Unit) hK ps hnd hlen hlt (fun _ => ()) (fun _ _ => ())
    (fun _ _ _ => 0) d d' rfl (fun c _ => E c)
  exact h

/-- **A run that queries none of the positions does not see them set.** -/
theorem runQ_rsetL {K : Nat} (hK : 0 < K) (nxt : Nat → List Nat → Nat) (c k : Nat) :
    ∀ (ps : List Nat) (H u : Nat), (∀ p ∈ ps, p ∉ qposQ K nxt c k H) →
      runQ K nxt c k (rsetL K ps H u) = runQ K nxt c k H ∧ qposQ K nxt c k (rsetL K ps H u) = qposQ K nxt c k H
  | [], _, _, _ => ⟨rfl, rfl⟩
  | p :: ps, H, u, h => by
    have hp := h p (List.mem_cons_self ..)
    obtain ⟨r1, q1⟩ := runQ_rset (p := p) hK (Nat.mod_lt u hK) nxt c k H hp
    have h' : ∀ q ∈ ps, q ∉ qposQ K nxt c k (rset K p H (u % K)) := fun q hq => by
      rw [q1]; exact h q (List.mem_cons_of_mem _ hq)
    obtain ⟨r2, q2⟩ := runQ_rsetL hK nxt c k ps (rset K p H (u % K)) (u / K) h'
    exact ⟨r2.trans r1, q2.trans q1⟩

/-- Whether a run hits any of the leaves' positions. -/
def hitL (K : Nat) (ps : List Nat) (nxt : Nat → List Nat → Nat) (c k H : Nat) : Bool :=
  ps.any (fun p => decide (p ∈ qposQ K nxt c k H))

theorem hitL_false {K : Nat} {ps : List Nat} {nxt : Nat → List Nat → Nat} {c k H : Nat}
    (h : hitL K ps nxt c k H = false) : ∀ p ∈ ps, p ∉ qposQ K nxt c k H := by
  intro p hp hq
  have : hitL K ps nxt c k H = true := List.any_eq_true.2 ⟨p, hp, decide_eq_true hq⟩
  rw [h] at this; exact Bool.false_ne_true this

/-- **The real and the ideal openings of several leaves differ only where a
    query hits a leaf's position.** -/
theorem pfRL_pfIL {D O P : Type} {K NSh NSo L k : Nat} (hK : 0 < K) (ps : D → Nat → Nat → List Nat)
    (op : D → O) (g : O → Nat → P) (nxt : P → Nat → List Nat → Nat) (F : Nat → P × List Nat → Bool) (d : D)
    (σ : Nat) :
    let hit := hitL K (ps d (saltO NSh NSo σ) (saltH NSh σ)) (nxt (g (op d) (saltO NSh NSo σ)))
      (comRL K NSh NSo ps d σ) k (saltT NSh NSo σ)
    K ^ L * indB (F (comRL K NSh NSo ps d σ) (pfRL K NSh NSo k ps op g nxt d σ)) ≤
      sumTo (K ^ L) (fun u => indB (F (comIL K NSh NSo L ps d (u + K ^ L * σ))
        (pfIL K NSh NSo L k ps op g nxt d (u + K ^ L * σ)))) + K ^ L * indB hit ∧
    sumTo (K ^ L) (fun u => indB (F (comIL K NSh NSo L ps d (u + K ^ L * σ))
        (pfIL K NSh NSo L k ps op g nxt d (u + K ^ L * σ)))) ≤
      K ^ L * indB (F (comRL K NSh NSo ps d σ) (pfRL K NSh NSo k ps op g nxt d σ)) + K ^ L * indB hit := by
  intro hit
  have eq : ∀ u, u < K ^ L → (comIL K NSh NSo L ps d (u + K ^ L * σ), pfIL K NSh NSo L k ps op g nxt d (u + K ^ L * σ)) =
      (comRL K NSh NSo ps d σ, (g (op d) (saltO NSh NSo σ), runQ K (nxt (g (op d) (saltO NSh NSo σ)))
        (comRL K NSh NSo ps d σ) k (rsetL K (ps d (saltO NSh NSo σ) (saltH NSh σ)) (saltT NSh NSo σ) u))) :=
    fun u hu => by obtain ⟨e1, e2⟩ := digit_dec (σ := σ) hu; simp only [pfIL, comIL, e1, e2]
  cases hh : hit
  · have hq := hitL_false hh
    have e : sumTo (K ^ L) (fun u => indB (F (comIL K NSh NSo L ps d (u + K ^ L * σ))
        (pfIL K NSh NSo L k ps op g nxt d (u + K ^ L * σ)))) =
        K ^ L * indB (F (comRL K NSh NSo ps d σ) (pfRL K NSh NSo k ps op g nxt d σ)) := by
      rw [show K ^ L * indB (F (comRL K NSh NSo ps d σ) (pfRL K NSh NSo k ps op g nxt d σ)) =
        sumTo (K ^ L) (fun _ => indB (F (comRL K NSh NSo ps d σ) (pfRL K NSh NSo k ps op g nxt d σ))) from
        (sumTo_const _ _).symm]
      refine sumTo_congr _ (fun u hu => ?_)
      have e3 := eq u hu
      rw [Prod.mk.injEq] at e3
      rw [e3.1, e3.2, (runQ_rsetL hK _ _ k _ _ u hq).1]
      rfl
    rw [e]; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · have b1 : K ^ L * indB (F (comRL K NSh NSo ps d σ) (pfRL K NSh NSo k ps op g nxt d σ)) ≤ K ^ L * indB true :=
      Nat.mul_le_mul_left _ (indB_le _)
    have b2 : sumTo (K ^ L) (fun u => indB (F (comIL K NSh NSo L ps d (u + K ^ L * σ))
        (pfIL K NSh NSo L k ps op g nxt d (u + K ^ L * σ)))) ≤ K ^ L * indB true := by
      refine Nat.le_trans (sumTo_mono _ (fun u _ => indB_le _)) (Nat.le_of_eq ?_)
      rw [sumTo_const]; rfl
    exact ⟨Nat.le_trans b1 (Nat.le_add_left _ _), Nat.le_trans b2 (Nat.le_add_left _ _)⟩

theorem rget_mul_le (K m X : Nat) : rget K m X * K ^ m ≤ X :=
  Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mod_le _ _)) (Nat.div_mul_le_self _ _)

/-- Answers set at two positions commute. -/
theorem rset_comm {K p q H a b : Nat} (hK : 0 < K) (hpq : p ≠ q) (ha : a < K) (hb : b < K) :
    rset K p (rset K q H b) a = rset K q (rset K p H a) b := by
  have g1 : rget K p (rset K q H b) = rget K p H := rget_rset_ne hK hpq hb
  have g2 : rget K q (rset K p H a) = rget K q H := rget_rset_ne hK (Ne.symm hpq) ha
  have l1 := rget_mul_le K q H
  have l2 := rget_mul_le K p H
  have l3 := rget_mul_le K p (rset K q H b)
  have l4 := rget_mul_le K q (rset K p H a)
  rw [g1] at l3; rw [g2] at l4
  unfold rset at l3 l4 ⊢
  rw [show rget K p (H - rget K q H * K ^ q + b * K ^ q) = rget K p H from g1,
    show rget K q (H - rget K p H * K ^ p + a * K ^ p) = rget K q H from g2]
  generalize rget K q H * K ^ q = A at *
  generalize rget K p H * K ^ p = C at *
  generalize b * K ^ q = B at *
  generalize a * K ^ p = D at *
  omega

theorem rset_rsetL {K p a : Nat} (hK : 0 < K) (ha : a < K) :
    ∀ (ps : List Nat), p ∉ ps → ∀ X w, rset K p (rsetL K ps X w) a = rsetL K ps (rset K p X a) w
  | [], _, _, _ => rfl
  | q :: qs, h, X, w => by
    have hq : p ≠ q := fun e => h (e ▸ List.mem_cons_self ..)
    have hs : p ∉ qs := fun e => h (List.mem_cons_of_mem _ e)
    show rset K p (rsetL K qs (rset K q X (w % K)) (w / K)) a = rsetL K qs (rset K q (rset K p X a) (w % K)) (w / K)
    rw [rset_rsetL hK ha qs hs, rset_comm hK hq ha (Nat.mod_lt w hK)]

/-- Setting the leaves' answers and setting them back restores the table. -/
theorem rsetL_back {K : Nat} (hK : 0 < K) :
    ∀ (ps : List Nat), ps.Nodup → ∀ H u, rsetL K ps (rsetL K ps H u) (rgetL K ps H) = H
  | [], _, _, _ => rfl
  | p :: qs, hnd, H, u => by
    have hnq : p ∉ qs := (List.nodup_cons.1 hnd).1
    have hlt : rget K p H < K := Nat.mod_lt _ hK
    obtain ⟨d1, d2⟩ := digit_dec (σ := rgetL K qs H) hlt
    show rsetL K qs (rset K p (rsetL K qs (rset K p H (u % K)) (u / K)) ((rget K p H + K * rgetL K qs H) % K))
      ((rget K p H + K * rgetL K qs H) / K) = H
    rw [d1, d2, rset_rsetL hK hlt qs hnq, rset_back hK (Nat.mod_lt u hK)]
    exact rsetL_back hK qs (List.nodup_cons.1 hnd).2 H (u / K)

/-- **Whether a run hits a leaf does not read the leaves' answers.** -/
theorem hitL_rsetL {K : Nat} (hK : 0 < K) (nxt : Nat → List Nat → Nat) (c k : Nat) (ps : List Nat) (hnd : ps.Nodup)
    (H u : Nat) : hitL K ps nxt c k (rsetL K ps H u) = hitL K ps nxt c k H := by
  cases h1 : hitL K ps nxt c k H
  · have e := (runQ_rsetL hK nxt c k ps H u (hitL_false h1)).2
    unfold hitL at h1 ⊢; rw [e, h1]
  · cases h2 : hitL K ps nxt c k (rsetL K ps H u)
    · have e := (runQ_rsetL hK nxt c k ps (rsetL K ps H u) (rgetL K ps H) (hitL_false h2)).2
      rw [rsetL_back hK ps hnd] at e
      unfold hitL at h1 h2; rw [e] at h1; rw [h1] at h2; exact h2.symm
    · rfl

theorem any_le_sum (f : Nat → Bool) : ∀ (ps : List Nat),
    indB (ps.any f) ≤ sumTo ps.length (fun l => indB (f (ps.getD l 0)))
  | [] => Nat.zero_le _
  | p :: ps => by
    rw [show (p :: ps).length = ps.length + 1 from rfl, sumTo_shift']
    show indB (f p || ps.any f) ≤ indB (f p) + sumTo ps.length (fun l => indB (f (ps.getD l 0)))
    have ih := any_le_sum f ps
    cases f p
    · simp only [Bool.false_or, indB]; simp only [indB] at ih; omega
    · simp only [Bool.true_or, indB]; omega

/-- **The draws that hit a leaf are few**: over the salts and the table,
    at most `L NSo Kⁿ s k`, `s` salts at most putting any leaf at any
    position; normalized, `L s k / NSh`. -/
theorem hitL_bound {D P : Type} {K n NSh NSo L s k : Nat} (hK : 0 < K) (ps : D → Nat → Nat → List Nat)
    (hnd : ∀ d σo σh, (ps d σo σh).Nodup) (hlen : ∀ d σo σh, (ps d σo σh).length = L)
    (hlt : ∀ d σo σh, ∀ p ∈ ps d σo σh, p < n)
    (hs : ∀ d σo l, l < L → ∀ v, sumTo NSh (fun σh => indB (decide ((ps d σo σh).getD l 0 = v))) ≤ s)
    (pf : Nat → P) (nxt : P → Nat → List Nat → Nat) (d : D) :
    sumTo (NSh * (NSo * K ^ n)) (fun σ => indB (hitL K (ps d (saltO NSh NSo σ) (saltH NSh σ))
      (nxt (pf (saltO NSh NSo σ))) (comRL K NSh NSo ps d σ) k (saltT NSh NSo σ))) ≤ NSo * (K ^ n * (L * (s * k))) := by
  have hKL : 0 < K ^ L := Nat.pow_pos hK
  rw [sum_salt_eq, ← sumTo_const (K ^ n * (L * (s * k))) NSo]
  refine sumTo_mono _ (fun o ho => ?_)
  -- the leaves' answers swapped for uniform ones
  have key : ∀ σh, K ^ L * sumTo (K ^ n) (fun h => indB (hitL K (ps d o σh) (nxt (pf o))
      (rgetL K (ps d o σh) h) k h)) =
      sumTo (K ^ n) (fun H => sumTo (K ^ L) (fun c => indB (hitL K (ps d o σh) (nxt (pf o)) c k H))) := fun σh => by
    have r := reprog_swapL (n := n) hK (ps d o σh) (hnd d o σh) (hlt d o σh)
      (fun c H => indB (hitL K (ps d o σh) (nxt (pf o)) c k H))
    rw [hlen d o σh] at r
    rw [← r, sumTo_mul]
    refine sumTo_congr _ (fun h _ => ?_)
    rw [← sumTo_const (indB (hitL K (ps d o σh) (nxt (pf o)) (rgetL K (ps d o σh) h) k h)) (K ^ L)]
    refine sumTo_congr _ (fun u _ => ?_)
    rw [hitL_rsetL hK _ _ k _ (hnd d o σh)]
  have e : sumTo NSh (fun σh => sumTo (K ^ n) (fun h => indB (hitL K (ps d (saltO NSh NSo (σh + NSh * (o + NSo * h)))
      (saltH NSh (σh + NSh * (o + NSo * h)))) (nxt (pf (saltO NSh NSo (σh + NSh * (o + NSo * h)))))
      (comRL K NSh NSo ps d (σh + NSh * (o + NSo * h))) k (saltT NSh NSo (σh + NSh * (o + NSo * h)))))) =
      sumTo NSh (fun σh => sumTo (K ^ n) (fun h => indB (hitL K (ps d o σh) (nxt (pf o)) (rgetL K (ps d o σh) h) k h))) :=
    sumTo_congr _ (fun σh hh => sumTo_congr _ (fun h _ => by
      obtain ⟨a, b, c⟩ := salt_dec (h := h) hh ho
      simp only [comRL, a, b, c]))
  rw [e]
  refine Nat.le_of_mul_le_mul_left ?_ hKL
  rw [sumTo_mul, sumTo_congr _ (fun σh _ => key σh), sumTo_exch _ (K ^ n) NSh]
  rw [show K ^ L * (K ^ n * (L * (s * k))) = sumTo (K ^ n) (fun _ => sumTo (K ^ L) (fun _ => L * (s * k))) by
    rw [sumTo_const, sumTo_const]; ac_rfl]
  refine sumTo_mono _ (fun H _ => ?_)
  rw [sumTo_exch _ (K ^ L) NSh]
  refine sumTo_mono _ (fun c _ => ?_)
  -- for a fixed table and commitment the queries are fixed; each leaf's salts spread
  calc sumTo NSh (fun σh => indB (hitL K (ps d o σh) (nxt (pf o)) c k H))
      ≤ sumTo NSh (fun σh => sumTo L (fun l => indB (decide ((ps d o σh).getD l 0 ∈ qposQ K (nxt (pf o)) c k H)))) :=
        sumTo_mono _ (fun σh _ => by
          have := any_le_sum (fun p => decide (p ∈ qposQ K (nxt (pf o)) c k H)) (ps d o σh)
          rw [hlen d o σh] at this; exact this)
    _ = sumTo L (fun l => sumTo NSh (fun σh => indB (decide ((ps d o σh).getD l 0 ∈ qposQ K (nxt (pf o)) c k H)))) :=
        sumTo_exch _ _ _
    _ ≤ sumTo L (fun _ => s * k) := sumTo_mono _ (fun l hl => by
          have h := salts_in (fun σh => (ps d o σh).getD l 0) (hs d o l hl) (qposQ K (nxt (pf o)) c k H)
          rwa [qposQ_length] at h)
    _ = L * (s * k) := sumTo_const _ _

/-- **The real opening of several leaves is the ideal's up to the hits**:
    for any event of the commitment and its opening, `K^L` times its count
    with the real opening is within `K^L NSo Kⁿ L s k` of its count with the
    ideal one, both ways; normalized, `L s k / NSh`. -/
theorem transferRL {D O P : Type} {K n NSh NSo L s k : Nat} (hK : 0 < K) (ps : D → Nat → Nat → List Nat)
    (hnd : ∀ d σo σh, (ps d σo σh).Nodup) (hlen : ∀ d σo σh, (ps d σo σh).length = L)
    (hlt : ∀ d σo σh, ∀ p ∈ ps d σo σh, p < n)
    (hs : ∀ d σo l, l < L → ∀ v, sumTo NSh (fun σh => indB (decide ((ps d σo σh).getD l 0 = v))) ≤ s)
    (op : D → O) (g : O → Nat → P) (nxt : P → Nat → List Nat → Nat) (F : Nat → P × List Nat → Bool) (d : D) :
    K ^ L * sumTo (NSh * (NSo * K ^ n)) (fun σ => indB (F (comRL K NSh NSo ps d σ) (pfRL K NSh NSo k ps op g nxt d σ))) ≤
      sumTo (NSh * (NSo * K ^ n) * K ^ L) (fun σ =>
        indB (F (comIL K NSh NSo L ps d σ) (pfIL K NSh NSo L k ps op g nxt d σ))) +
        K ^ L * (NSo * (K ^ n * (L * (s * k)))) ∧
    sumTo (NSh * (NSo * K ^ n) * K ^ L) (fun σ =>
        indB (F (comIL K NSh NSo L ps d σ) (pfIL K NSh NSo L k ps op g nxt d σ))) ≤
      K ^ L * sumTo (NSh * (NSo * K ^ n)) (fun σ => indB (F (comRL K NSh NSo ps d σ) (pfRL K NSh NSo k ps op g nxt d σ))) +
        K ^ L * (NSo * (K ^ n * (L * (s * k)))) := by
  have hb := hitL_bound (n := n) (NSh := NSh) (NSo := NSo) (L := L) (s := s) (k := k) hK ps hnd hlen hlt hs (fun o => g (op d) o) nxt d
  have hk := Nat.mul_le_mul_left (K ^ L) hb
  rw [sum_digit (K ^ L) (NSh * (NSo * K ^ n)), sumTo_mul (K ^ L) _ (NSh * (NSo * K ^ n))]
  have pt := fun σ => pfRL_pfIL (NSh := NSh) (NSo := NSo) (L := L) (k := k) hK ps op g nxt F d σ
  constructor
  · refine Nat.le_trans (sumTo_mono _ (fun σ _ => (pt σ).1)) ?_
    rw [sumTo_add]
    exact Nat.add_le_add_left (Nat.le_trans (Nat.le_of_eq (sumTo_mul (K ^ L) _ _).symm) hk) _
  · refine Nat.le_trans (sumTo_mono _ (fun σ _ => (pt σ).2)) ?_
    rw [sumTo_add]
    exact Nat.add_le_add_left (Nat.le_trans (Nat.le_of_eq (sumTo_mul (K ^ L) _ _).symm) hk) _

theorem rgetL_lt {K : Nat} (hK : 0 < K) : ∀ (ps : List Nat) (H : Nat), rgetL K ps H < K ^ ps.length
  | [], _ => Nat.one_pos
  | p :: ps, H => by
    show rget K p H + K * rgetL K ps H < K ^ (ps.length + 1)
    have h1 : rget K p H < K := Nat.mod_lt _ hK
    have h2 := rgetL_lt hK ps H
    rw [Nat.pow_succ']
    calc rget K p H + K * rgetL K ps H < K + K * rgetL K ps H := Nat.add_lt_add_right h1 _
      _ = K * (rgetL K ps H + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ K * K ^ ps.length := Nat.mul_le_mul_left _ h2

/-- **The real opening of several leaves hides up to the hits**, both
    transfers and the ideal opening's exact hiding. -/
theorem pfRL_hidesA {D O P : Type} {K n NSh NSo L s k : Nat} (hK : 0 < K) (ps : D → Nat → Nat → List Nat)
    (hnd : ∀ d σo σh, (ps d σo σh).Nodup) (hlen : ∀ d σo σh, (ps d σo σh).length = L)
    (hlt : ∀ d σo σh, ∀ p ∈ ps d σo σh, p < n)
    (hs : ∀ d σo l, l < L → ∀ v, sumTo NSh (fun σh => indB (decide ((ps d σo σh).getD l 0 = v))) ≤ s)
    (op : D → O) (g : O → Nat → P) (nxt : P → Nat → List Nat → Nat) :
    ComPfHidesA (NSh * (NSo * K ^ n)) (NSo * (K ^ n * (2 * (L * (s * k))))) (comRL K NSh NSo ps)
      (pfRL K NSh NSo k ps op g nxt) op := by
  intro d d' hop E
  have hKL : 0 < K ^ L := Nat.pow_pos hK
  have t1 := (transferRL (n := n) (NSh := NSh) (NSo := NSo) (L := L) (s := s) (k := k) hK ps hnd hlen hlt hs op g nxt E d).1
  have t2 := (transferRL (n := n) (NSh := NSh) (NSo := NSo) (L := L) (s := s) (k := k) hK ps hnd hlen hlt hs op g nxt E d').2
  have hi := pfIL_hides (n := n) (NSh := NSh) (NSo := NSo) (L := L) (k := k) hK ps hnd hlen hlt op g nxt d d' hop E
  rw [hi] at t1
  refine Nat.le_of_mul_le_mul_left ?_ hKL
  calc K ^ L * sumTo (NSh * (NSo * K ^ n)) (fun σ => indB (E (comRL K NSh NSo ps d σ) (pfRL K NSh NSo k ps op g nxt d σ)))
      ≤ K ^ L * sumTo (NSh * (NSo * K ^ n)) (fun σ => indB (E (comRL K NSh NSo ps d' σ) (pfRL K NSh NSo k ps op g nxt d' σ))) +
        K ^ L * (NSo * (K ^ n * (L * (s * k)))) + K ^ L * (NSo * (K ^ n * (L * (s * k)))) :=
        Nat.le_trans t1 (Nat.add_le_add_right t2 _)
    _ = K ^ L * (sumTo (NSh * (NSo * K ^ n)) (fun σ => indB (E (comRL K NSh NSo ps d' σ) (pfRL K NSh NSo k ps op g nxt d' σ))) +
        NSo * (K ^ n * (2 * (L * (s * k))))) := by
        rw [Nat.mul_add, Nat.add_assoc, ← Nat.mul_add]
        congr 2
        rw [← Nat.mul_add]; congr 1; rw [← Nat.mul_add]; congr 1; omega
/-- **One Fiat–Shamir round, the commitment to `L` leaves drawn from the
    oracle** (`fs_openA` over `comRL`, `pfRL`): `fs_openROM` with the
    commitment the leaves' answers at their salted positions, the leaf
    vector hashed; the bound gains `L` times `fs_openROM`'s hit term,
    `2 L s k / NSh` a draw normalized. -/
theorem fs_openROML {PV PB D O P : Type} {NR m e1 e2 K n NSh NSo L s k : Nat} (hK : 0 < K)
    (ps : D → Nat → Nat → List Nat) (hnd : ∀ d σo σh, (ps d σo σh).Nodup) (hlen : ∀ d σo σh, (ps d σo σh).length = L)
    (hlt : ∀ d σo σh, ∀ p ∈ ps d σo σh, p < n) (g : O → Nat → P)
    (hs : ∀ d σo l, l < L → ∀ v, sumTo NSh (fun σh => indB (decide ((ps d σo σh).getD l 0 = v))) ≤ s) (nxt : P → Nat → List Nat → Nat)
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
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (NSh * (NSo * K ^ n)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H % Q4)) && E H ((comRL K NSh NSo ps) (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H % Q4))
            r t)).map (fun _ => (pfRL K NSh NSo k ps op g nxt) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H % Q4))
            r t)))))) ≤
    sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSh * (NSo * K ^ n)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) ((comRL K NSh NSo ps) (sd (sop r t)) σ) H c) ((comRL K NSh NSo ps) (sd (sop r t)) σ)
        (some ((pfRL K NSh NSo k ps op g nxt) (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ (K ^ L) * ((NSh * (NSo * K ^ n)) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * (NSo * (K ^ n * (2 * (L * (s * k)))))))) ∧
    sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSh * (NSo * K ^ n)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) ((comRL K NSh NSo ps) (sd (sop r t)) σ) H c) ((comRL K NSh NSo ps) (sd (sop r t)) σ)
        (some ((pfRL K NSh NSo k ps op g nxt) (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (NSh * (NSo * K ^ n)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H % Q4)) && E H ((comRL K NSh NSo ps) (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H % Q4))
            r t)).map (fun _ => (pfRL K NSh NSo k ps op g nxt) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comRL K NSh NSo ps) (main t r) σ) H % Q4))
            r t)))))) +
    (Q4 * Q4) ^ (K ^ L) * ((NSh * (NSo * K ^ n)) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * (NSo * (K ^ n * (2 * (L * (s * k)))))))) := by
  have hη : NSo * (K ^ n * (2 * (L * (s * 0)))) ≤ NSo * (K ^ n * (2 * (L * (s * k)))) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ (Nat.zero_le k)))))
  have hcom : ComHidesA (NSh * (NSo * K ^ n)) (NSo * (K ^ n * (2 * (L * (s * k))))) (comRL K NSh NSo ps) :=
    fun d d' E => Nat.le_trans (pfRL_hidesA (n := n) (L := L) (s := s) (k := 0) (O := Unit) (P := Unit) hK ps hnd hlen hlt hs
      (fun _ => ()) (fun _ _ => ()) (fun _ _ _ => 0) d d' rfl (fun c _ => E c)) (Nat.add_le_add_left hη _)
  have hrange : ∀ d σ, comRL K NSh NSo ps d σ < K ^ L := fun d σ => by
    have h := rgetL_lt hK (ps d (saltO NSh NSo σ) (saltH NSh σ)) (saltT NSh NSo σ)
    rwa [hlen] at h
  exact fs_openA (comRL K NSh NSo ps) (pfRL K NSh NSo k ps op g nxt) op sd d0 hcom
    (pfRL_hidesA hK ps hnd hlen hlt hs op g nxt) hrange ov hovn main hsd sop h1 h2 hrv hsv hrvo hsvo E

/-- **The spread hypothesis is met with `s = 1`** (not vacuous): one leaf
    per draw, its position the hidden salt itself. -/
theorem hs_one {D : Type} (NSh : Nat) :
    ∀ (d : D) (σo l : Nat), l < 1 → ∀ v, sumTo NSh (fun σh => indB (decide (([σh] : List Nat).getD l 0 = v))) ≤ 1 := by
  intro d σo l hl v
  have hl0 : l = 0 := by omega
  subst hl0
  show sumTo NSh (fun σh => indB (decide (σh = v))) ≤ 1
  induction NSh with
  | zero => exact Nat.zero_le _
  | succ N ih =>
    show sumTo N (fun σh => indB (decide (σh = v))) + indB (decide (N = v)) ≤ 1
    by_cases h : N = v
    · subst h
      have z : sumTo N (fun σh => indB (decide (σh = N))) = 0 := by
        have : ∀ M, M ≤ N → sumTo M (fun σh => indB (decide (σh = N))) = 0 := by
          intro M; induction M with
          | zero => intro _; rfl
          | succ M ihM => intro hM; show sumTo M _ + indB (decide (M = N)) = 0
                          rw [ihM (by omega)]; simp [indB, show M ≠ N by omega]
        exact this N (Nat.le_refl _)
      rw [z]; simp [indB]
    · simp only [h, decide_false, indB, Nat.add_zero]; exact ih
end Circuit
