import Ski.ZK.ROMMerkle

/-!
# A Merkle tree's leaves drawn from the oracle, some opened

`Ski/ZK/ROMMerkle.lean` commits to leaves whose salts stay hidden.  Here each
leaf has its own salt, a digit of the hidden salt (`lsalt`), and its
position in the commitment's table is read off its data and its salt
alone (`pos d l a`, distinct across leaves, `hdist`: a leaf index in the
hash input, which Plonky3's leaf hash does not carry; a strengthening, not a
conservative simplification: without it two unopened leaves with equal data
and equal salts share a hash, a term of about the equal-data pairs over
`NSl` this module does not count; `ROMMerkleColl` counts it for one round);
the commitment is
the leaves' answers in leaf order (`comM`).  The opening opens a fixed set
of leaves (`isO`): their data, through `op`, which fixes their positions
(`hposO`), and their salts (`shownS`), as a Merkle opening shows them.  The
ideal opening re-randomizes only the unopened leaves' answers (`pfMI`),
and hides exactly (`pfMI_hides`: the swap over the unopened positions, the
commitment rebuilt by setting them back); the real opening differs only
where a query hits an unopened leaf (`pfM_pfMI`), each leaf's hits counted
over its own salt with the others fixed (`hitLeaf_bound`), `UL s k / NSl`
in all (`hitM_bound`), both ways (`transferM`); so the real opening hides
up to `2 UL s k / NSl` (`pfM_hidesA`), and one Fiat–Shamir round keeps its
bound (`fs_openROMM`), likewise with a root of the leaves hashed in their
place (`fs_openROMMR`).  `merkleOpen_sat` meets the hypotheses together.
Not yet: the opened set chosen by a later challenge (the four-round
theorems').  The root is a function of the leaves' answers computed apart
from their table, an assumption.
-/

set_option autoImplicit false
namespace Circuit
open ZKF

theorem rget_rsetL_not {K p : Nat} (hK : 0 < K) :
    ∀ (ps : List Nat), p ∉ ps → ∀ H u, rget K p (rsetL K ps H u) = rget K p H
  | [], _, _, _ => rfl
  | q :: qs, h, H, u => by
    have hq : p ≠ q := fun e => h (e ▸ List.mem_cons_self ..)
    have hs : p ∉ qs := fun e => h (List.mem_cons_of_mem _ e)
    show rget K p (rsetL K qs (rset K q H (u % K)) (u / K)) = rget K p H
    rw [rget_rsetL_not hK qs hs, rget_rset_ne hK hq (Nat.mod_lt u hK)]

theorem rget_rsetL_at {K : Nat} (hK : 0 < K) :
    ∀ (ps : List Nat), ps.Nodup → ∀ i, i < ps.length → ∀ H u,
      rget K (ps.getD i 0) (rsetL K ps H u) = u / K ^ i % K
  | [], _, i, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | q :: qs, hnd, i, hi, H, u => by
    have hnq : q ∉ qs := (List.nodup_cons.1 hnd).1
    show rget K ((q :: qs).getD i 0) (rsetL K qs (rset K q H (u % K)) (u / K)) = u / K ^ i % K
    cases i with
    | zero =>
      show rget K q (rsetL K qs (rset K q H (u % K)) (u / K)) = u / K ^ 0 % K
      rw [rget_rsetL_not hK qs hnq, rget_rset hK (Nat.mod_lt u hK), Nat.pow_zero, Nat.div_one]
    | succ j =>
      show rget K (qs.getD j 0) (rsetL K qs (rset K q H (u % K)) (u / K)) = u / K ^ (j + 1) % K
      rw [rget_rsetL_at hK qs (List.nodup_cons.1 hnd).2 j (Nat.lt_of_succ_lt_succ hi), Nat.pow_succ',
        Nat.div_div_eq_div_mul]

theorem rgetL_congr {K : Nat} : ∀ (ps ps' : List Nat) (X X' : Nat), ps.length = ps'.length →
    (∀ i, i < ps.length → rget K (ps.getD i 0) X = rget K (ps'.getD i 0) X') → rgetL K ps X = rgetL K ps' X'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], _, _, h, _ => absurd h (Nat.succ_ne_zero _)
  | p :: ps, p' :: ps', X, X', hl, h => by
    show rget K p X + K * rgetL K ps X = rget K p' X' + K * rgetL K ps' X'
    have h0 : rget K p X = rget K p' X' := h 0 (Nat.succ_pos _)
    rw [h0, rgetL_congr ps ps' X X' (Nat.succ.inj hl) (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

/-- Leaf `l`'s own salt, a digit of the hidden salt. -/
def lsalt (NSl l σh : Nat) : Nat := σh / NSl ^ l % NSl

/-- The leaves `L - 1, …, 0`. -/
def lr : Nat → List Nat
  | 0 => []
  | n + 1 => n :: lr n

theorem mem_lr : ∀ {n m : Nat}, m ∈ lr n → m < n
  | 0, _, h => absurd h List.not_mem_nil
  | n + 1, m, h => by
    rcases List.mem_cons.1 h with e | h'
    · rw [e]; exact Nat.lt_succ_self n
    · exact Nat.lt_succ_of_lt (mem_lr h')

theorem lr_mem : ∀ {n m : Nat}, m < n → m ∈ lr n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, m, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | e
    · exact List.mem_cons_of_mem _ (lr_mem h')
    · rw [e]; exact List.mem_cons_self ..

theorem lr_nodup : ∀ n, (lr n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => List.nodup_cons.2 ⟨fun h => Nat.lt_irrefl _ (mem_lr h), lr_nodup n⟩

theorem nodup_filter (p : Nat → Bool) : ∀ (l : List Nat), l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    have ih := nodup_filter p l (List.nodup_cons.1 h).2
    cases hp : p a
    · rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]; exact ih
    · rw [List.filter_cons_of_pos hp]
      exact List.nodup_cons.2 ⟨fun hm => (List.nodup_cons.1 h).1 (List.mem_filter.1 hm).1, ih⟩

/-- The unopened leaves, in order. -/
def unop (L : Nat) (isO : Nat → Bool) : List Nat := (lr L).filter (fun l => !isO l)

/-- Every leaf's position, in leaf order. -/
def posAll {D : Type} (pos : D → Nat → Nat → Nat) (L NSl : Nat) (d : D) (σh : Nat) : List Nat :=
  (lr L).map (fun l => pos d l (lsalt NSl l σh))

/-- The unopened leaves' positions. -/
def posU {D : Type} (pos : D → Nat → Nat → Nat) (L NSl : Nat) (isO : Nat → Bool) (d : D) (σh : Nat) : List Nat :=
  (unop L isO).map (fun l => pos d l (lsalt NSl l σh))

theorem nodup_map_on (f : Nat → Nat) : ∀ (l : List Nat), l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, a ≠ b → f a ≠ f b) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, h => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on f l (List.nodup_cons.1 hnd).2
      (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    have hab : a ≠ b := fun e' => (List.nodup_cons.1 hnd).1 (e' ▸ hb)
    exact h a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) hab e.symm

theorem posU_nodup {D : Type} (pos : D → Nat → Nat → Nat) (L NSl : Nat) (isO : Nat → Bool)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (d : D) (σh : Nat) :
    (posU pos L NSl isO d σh).Nodup := by
  unfold posU unop
  exact nodup_map_on _ _ (nodup_filter _ _ (lr_nodup L)) (fun a ha b hb hne => hdist d a b _ _ (mem_lr (List.mem_filter.1 ha).1) (mem_lr (List.mem_filter.1 hb).1) hne)

theorem unop_index {L : Nat} {isO : Nat → Bool} {l : Nat} (hl : l < L) (hu : isO l = false) :
    ∃ j, j < (unop L isO).length ∧ (unop L isO).getD j 0 = l := by
  have hm : l ∈ unop L isO := by
    unfold unop; rw [List.mem_filter]; exact ⟨lr_mem hl, by rw [hu]; rfl⟩
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
  exact ⟨j, hj, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, e]⟩

theorem getD_mapN (f : Nat → Nat) (l : List Nat) {j : Nat} (hj : j < l.length) :
    (l.map f).getD j 0 = f (l.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

theorem lr_length : ∀ n, (lr n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (lr_length n)

theorem lr_getD_lt : ∀ {n i : Nat}, i < n → (lr n).getD i 0 < n := fun {n i} hi => by
  have hm : (lr n).getD i 0 ∈ lr n := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [lr_length]; exact hi)]
    exact List.getElem_mem ..
  exact mem_lr hm

/-- The shown salts: the opened leaves'. -/
def shownS (NSl L : Nat) (isO : Nat → Bool) (σh : Nat) : List Nat :=
  ((lr L).filter isO).map (fun l => lsalt NSl l σh)

/-- **A Merkle tree's leaves committed from the oracle, some opened**: the
    commitment the leaves' answers in leaf order (`σ' = σh + NSl^L h`, the
    hidden salt `σh` a digit per leaf, the table `h`). -/
def comM {D : Type} (K NSl L : Nat) (pos : D → Nat → Nat → Nat) (d : D) (σ' : Nat) : Nat :=
  rgetL K (posAll pos L NSl d (σ' % NSl ^ L)) (σ' / NSl ^ L)

/-- Its opening: the opened data and the opened leaves' salts, and the
    distinguisher's `k` queries into the table. -/
def pfM {D O P : Type} (K NSl L k : Nat) (pos : D → Nat → Nat → Nat) (isO : Nat → Bool) (op : D → O)
    (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) (d : D) (σ' : Nat) : P × List Nat :=
  (g (op d) (shownS NSl L isO (σ' % NSl ^ L)),
   runQ K (nxt (g (op d) (shownS NSl L isO (σ' % NSl ^ L)))) (comM K NSl L pos d σ') k (σ' / NSl ^ L))

/-- The commitment with the extra digits, which it ignores. -/
def comMI {D : Type} (K NSl L UL : Nat) (pos : D → Nat → Nat → Nat) (d : D) (σ : Nat) : Nat :=
  comM K NSl L pos d (σ / K ^ UL)

/-- **The ideal opening**: the queries answered with the unopened leaves'
    answers re-randomized to the extra digits. -/
def pfMI {D O P : Type} (K NSl L UL k : Nat) (pos : D → Nat → Nat → Nat) (isO : Nat → Bool) (op : D → O)
    (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) (d : D) (σ : Nat) : P × List Nat :=
  (g (op d) (shownS NSl L isO (σ / K ^ UL % NSl ^ L)),
   runQ K (nxt (g (op d) (shownS NSl L isO (σ / K ^ UL % NSl ^ L)))) (comMI K NSl L UL pos d σ) k
     (rsetL K (posU pos L NSl isO d (σ / K ^ UL % NSl ^ L)) (σ / K ^ UL / NSl ^ L) (σ % K ^ UL)))

theorem posU_not_mem {D : Type} {pos : D → Nat → Nat → Nat} {L NSl : Nat} {isO : Nat → Bool}
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) {d : D} {σh l a : Nat} (hl : l < L) (hO : isO l = true) :
    pos d l a ∉ posU pos L NSl isO d σh := by
  intro hm
  obtain ⟨l', hl', e⟩ := List.mem_map.1 hm
  have hu : isO l' = false := by
    have := (List.mem_filter.1 hl').2
    cases h : isO l' <;> simp_all
  have hne : l' ≠ l := fun e' => by rw [e'] at hu; rw [hu] at hO; exact Bool.false_ne_true hO
  exact hdist d l' l _ _ (mem_lr (List.mem_filter.1 hl').1) hl hne e

/-- **The ideal opening hides exactly given the opened leaves**: with the
    opened leaves' positions read off the opened data (`hposO`). -/
theorem pfMI_hides {D O P : Type} {K n NSl L k : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (isO : Nat → Bool) (op : D → O) (hposO : ∀ d d', op d = op d' → ∀ l a, isO l = true → pos d l a = pos d' l a)
    (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) :
    ComPfHides (NSl ^ L * K ^ n * K ^ (unop L isO).length) (comMI K NSl L (unop L isO).length pos)
      (pfMI K NSl L (unop L isO).length k pos isO op g nxt) op := by
  intro d d' hop E
  have UL := (unop L isO).length
  have hNL : 0 < K ^ (unop L isO).length := Nat.pow_pos hK
  let G := fun (dd : D) (σh cU H : Nat) =>
    indB (E (rgetL K (posAll pos L NSl dd σh) (rsetL K (posU pos L NSl isO dd σh) H cU))
      (g (op d) (shownS NSl L isO σh), runQ K (nxt (g (op d) (shownS NSl L isO σh)))
        (rgetL K (posAll pos L NSl dd σh) (rsetL K (posU pos L NSl isO dd σh) H cU)) k H))
  have key : ∀ dd : D, op dd = op d → sumTo (NSl ^ L * K ^ n * K ^ (unop L isO).length) (fun σ =>
      indB (E (comMI K NSl L (unop L isO).length pos dd σ) (pfMI K NSl L (unop L isO).length k pos isO op g nxt dd σ))) =
      sumTo (NSl ^ L) (fun σh => sumTo (K ^ n) (fun H =>
        sumTo (K ^ (unop L isO).length) (fun cU => G dd σh cU H))) := fun dd hdd => by
    rw [sum_digit, sumTo_split (NSl ^ L), sumTo_exch _ (NSl ^ L) (K ^ n)]
    refine sumTo_congr _ (fun σh hσ => ?_)
    have hlen : (posU pos L NSl isO dd σh).length = (unop L isO).length := List.length_map ..
    have r := reprog_swapL (n := n) hK (posU pos L NSl isO dd σh) (posU_nodup pos L NSl isO hdist dd σh)
      (fun p hp => by obtain ⟨l, hl, e⟩ := List.mem_map.1 hp; rw [← e]; exact hlt _ _ _ (mem_lr (List.mem_filter.1 hl).1)) (fun cU H => G dd σh cU H)
    rw [hlen] at r
    rw [← r]
    refine sumTo_congr _ (fun h _ => sumTo_congr _ (fun u hu => ?_))
    obtain ⟨e1, e2⟩ := digit_dec (σ := σh + NSl ^ L * h) hu
    obtain ⟨f1, f2⟩ := digit_dec (σ := h) hσ
    have back := rsetL_back hK (posU pos L NSl isO dd σh) (posU_nodup pos L NSl isO hdist dd σh) h u
    simp only [G, pfMI, comMI, comM, e1, e2, f1, f2, back, hdd]
  rw [key d rfl, key d' hop.symm]
  refine sumTo_congr _ (fun σh _ => sumTo_congr _ (fun H _ => sumTo_congr _ (fun cU _ => ?_)))
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
      have a1 := rget_rsetL_at hK _ (posU_nodup pos L NSl isO hdist d' σh) j hj' H cU
      have a2 := rget_rsetL_at hK _ (posU_nodup pos L NSl isO hdist d σh) j hj'' H cU
      have p1 : (posU pos L NSl isO d' σh).getD j 0 = pos d' ((lr L).getD i 0) (lsalt NSl ((lr L).getD i 0) σh) := by
        unfold posU; rw [getD_mapN _ _ hj, ej]
      have p2 : (posU pos L NSl isO d σh).getD j 0 = pos d ((lr L).getD i 0) (lsalt NSl ((lr L).getD i 0) σh) := by
        unfold posU; rw [getD_mapN _ _ hj, ej]
      rw [p1] at a1; rw [p2] at a2
      rw [a1, a2]
    · rw [rget_rsetL_not hK _ (posU_not_mem hdist hl hO), rget_rsetL_not hK _ (posU_not_mem hdist hl hO),
        hposO d' d hop.symm _ _ hO]
  simp only [G, hc]

/-- **The real and the ideal openings differ only where a query hits an
    unopened leaf.** -/
theorem pfM_pfMI {D O P : Type} {K NSl L k : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat) (isO : Nat → Bool)
    (op : D → O) (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) (F : Nat → P × List Nat → Bool) (d : D)
    (σ : Nat) :
    let UL := (unop L isO).length
    let hit := hitL K (posU pos L NSl isO d (σ % NSl ^ L)) (nxt (g (op d) (shownS NSl L isO (σ % NSl ^ L))))
      (comM K NSl L pos d σ) k (σ / NSl ^ L)
    K ^ UL * indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ)) ≤
      sumTo (K ^ UL) (fun u => indB (F (comMI K NSl L UL pos d (u + K ^ UL * σ))
        (pfMI K NSl L UL k pos isO op g nxt d (u + K ^ UL * σ)))) + K ^ UL * indB hit ∧
    sumTo (K ^ UL) (fun u => indB (F (comMI K NSl L UL pos d (u + K ^ UL * σ))
        (pfMI K NSl L UL k pos isO op g nxt d (u + K ^ UL * σ)))) ≤
      K ^ UL * indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ)) + K ^ UL * indB hit := by
  intro UL hit
  have eq : ∀ u, u < K ^ UL → (comMI K NSl L UL pos d (u + K ^ UL * σ), pfMI K NSl L UL k pos isO op g nxt d (u + K ^ UL * σ)) =
      (comM K NSl L pos d σ, (g (op d) (shownS NSl L isO (σ % NSl ^ L)),
        runQ K (nxt (g (op d) (shownS NSl L isO (σ % NSl ^ L)))) (comM K NSl L pos d σ) k
          (rsetL K (posU pos L NSl isO d (σ % NSl ^ L)) (σ / NSl ^ L) u))) :=
    fun u hu => by obtain ⟨e1, e2⟩ := digit_dec (σ := σ) hu; simp only [pfMI, comMI, e1, e2]
  cases hh : hit
  · have hq := hitL_false hh
    have e : sumTo (K ^ UL) (fun u => indB (F (comMI K NSl L UL pos d (u + K ^ UL * σ))
        (pfMI K NSl L UL k pos isO op g nxt d (u + K ^ UL * σ)))) =
        K ^ UL * indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ)) := by
      rw [show K ^ UL * indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ)) =
        sumTo (K ^ UL) (fun _ => indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ))) from
        (sumTo_const _ _).symm]
      refine sumTo_congr _ (fun u hu => ?_)
      have e3 := eq u hu
      rw [Prod.mk.injEq] at e3
      rw [e3.1, e3.2, (runQ_rsetL hK _ _ k _ _ u hq).1]
      rfl
    rw [e]; exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · have b1 : K ^ UL * indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ)) ≤ K ^ UL * indB true :=
      Nat.mul_le_mul_left _ (indB_le _)
    have b2 : sumTo (K ^ UL) (fun u => indB (F (comMI K NSl L UL pos d (u + K ^ UL * σ))
        (pfMI K NSl L UL k pos isO op g nxt d (u + K ^ UL * σ)))) ≤ K ^ UL * indB true := by
      refine Nat.le_trans (sumTo_mono _ (fun u _ => indB_le _)) (Nat.le_of_eq ?_)
      rw [sumTo_const]; rfl
    exact ⟨Nat.le_trans b1 (Nat.le_add_left _ _), Nat.le_trans b2 (Nat.le_add_left _ _)⟩

theorem lsalt_at {NSl l lo x hi : Nat} (hlo : lo < NSl ^ l) (hx : x < NSl) :
    lsalt NSl l (lo + NSl ^ l * (x + NSl * hi)) = x := by
  have hp : 0 < NSl ^ l := Nat.lt_of_le_of_lt (Nat.zero_le _) hlo
  unfold lsalt
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlo, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hx]

theorem lsalt_lt {NSl l l' lo Y : Nat} (hN : 0 < NSl) (hl : l' < l) :
    lsalt NSl l' (lo + NSl ^ l * Y) = lsalt NSl l' lo := by
  unfold lsalt
  have e : NSl ^ l = NSl ^ l' * (NSl * NSl ^ (l - l' - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.pow_pos hN), Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem lsalt_gt {NSl l l' lo x hi : Nat} (hN : 0 < NSl) (hl : l < l') (hlo : lo < NSl ^ l) (hx : x < NSl) :
    lsalt NSl l' (lo + NSl ^ l * (x + NSl * hi)) = hi / NSl ^ (l' - l - 1) % NSl := by
  unfold lsalt
  have hp : 0 < NSl ^ l := Nat.pow_pos hN
  have e1 : lo + NSl ^ l * (x + NSl * hi) = (lo + NSl ^ l * x) + NSl ^ (l + 1) * hi := by
    rw [Nat.mul_add, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc]
  have hb : lo + NSl ^ l * x < NSl ^ (l + 1) := by
    rw [Nat.pow_succ]
    calc lo + NSl ^ l * x < NSl ^ l + NSl ^ l * x := Nat.add_lt_add_right hlo _
      _ = NSl ^ l * (x + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ NSl ^ l * NSl := Nat.mul_le_mul_left _ hx
  have e2 : NSl ^ l' = NSl ^ (l + 1) * NSl ^ (l' - l - 1) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e1, e2, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.pow_pos hN), Nat.div_eq_of_lt hb, Nat.zero_add]

theorem sum_split_digit (NSl L l : Nat) (hl : l < L) (f : Nat → Nat) :
    sumTo (NSl ^ L) f = sumTo (NSl ^ (L - l - 1)) (fun hi => sumTo NSl (fun x => sumTo (NSl ^ l) (fun lo =>
      f (lo + NSl ^ l * (x + NSl * hi))))) := by
  have e : NSl ^ L = NSl ^ l * (NSl * NSl ^ (L - l - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
  rw [e, sumTo_split (NSl ^ l) f, sumTo_split NSl _ (NSl ^ (L - l - 1))]

theorem lsalt_ne {NSl l l' lo x hi : Nat} (hN : 0 < NSl) (hne : l' ≠ l) (hlo : lo < NSl ^ l) (hx : x < NSl) :
    lsalt NSl l' (lo + NSl ^ l * (x + NSl * hi)) = lsalt NSl l' (lo + NSl ^ l * (0 + NSl * hi)) := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · rw [lsalt_lt hN h, lsalt_lt hN h]
  · rw [lsalt_gt hN h hlo hx, lsalt_gt hN h hlo hN]

theorem shownS_eq {NSl L l lo x hi : Nat} {isO : Nat → Bool} (hN : 0 < NSl) (hu : isO l = false)
    (hlo : lo < NSl ^ l) (hx : x < NSl) :
    shownS NSl L isO (lo + NSl ^ l * (x + NSl * hi)) = shownS NSl L isO (lo + NSl ^ l * (0 + NSl * hi)) := by
  unfold shownS
  refine List.map_congr_left (fun l' hl' => ?_)
  have ho : isO l' = true := (List.mem_filter.1 hl').2
  have hne : l' ≠ l := fun e => by rw [e, hu] at ho; exact Bool.false_ne_true ho
  exact lsalt_ne hN hne hlo hx

theorem comM_eq {D : Type} {K NSl L l lo x hi a H : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (d : D) (hl : l < L) (hlo : lo < NSl ^ l) (hx : x < NSl) (ha : a < K) :
    rgetL K (posAll pos L NSl d (lo + NSl ^ l * (x + NSl * hi))) (rset K (pos d l x) H a) =
      rgetL K (posAll pos L NSl d (lo + NSl ^ l * (0 + NSl * hi))) (rset K (pos d l 0) H a) := by
  refine rgetL_congr _ _ _ _ (by simp only [posAll, List.length_map]) (fun i hi' => ?_)
  have hi2 : i < (lr L).length := by simp only [posAll, List.length_map] at hi'; exact hi'
  have hL := lr_getD_lt (n := L) (i := i) (by rw [lr_length] at hi2; exact hi2)
  simp only [posAll]
  rw [getD_mapN _ _ hi2, getD_mapN _ _ hi2]
  by_cases e : (lr L).getD i 0 = l
  · rw [e, lsalt_at hlo hx, lsalt_at hlo hN, rget_rset hK ha, rget_rset hK ha]
  · rw [lsalt_ne hN e hlo hx, rget_rset_ne hK (hdist d _ l _ _ hL hl e) ha, rget_rset_ne hK (hdist d _ l _ _ hL hl e) ha]

/-- **An unopened leaf's position is hit by few draws**: over the salts and
    the table, at most `Kⁿ NSl^(L-1) s k`, `s` of a leaf's salts at most
    putting it at any position; normalized, `s k / NSl`. -/
theorem hitLeaf_bound {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isO : Nat → Bool) (op : D → O) (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) (d : D)
    {l : Nat} (hl : l < L) (hu : isO l = false) :
    sumTo (NSl ^ L) (fun σh => sumTo (K ^ n) (fun h => indB (decide (pos d l (lsalt NSl l σh) ∈
      qposQ K (nxt (g (op d) (shownS NSl L isO σh))) (rgetL K (posAll pos L NSl d σh) h) k h)))) ≤
      K ^ n * (NSl ^ (L - l - 1) * (NSl ^ l * (s * k))) := by
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
  have per : ∀ H a, a < K → sumTo (NSl ^ L) (fun σh => f σh a H) ≤ NSl ^ (L - l - 1) * (NSl ^ l * (s * k)) := by
    intro H a ha
    rw [sum_split_digit NSl L l hl, ← sumTo_const (NSl ^ l * (s * k)) (NSl ^ (L - l - 1))]
    refine sumTo_mono _ (fun hi _ => ?_)
    rw [sumTo_exch _ (NSl ^ l) NSl, ← sumTo_const (s * k) (NSl ^ l)]
    refine sumTo_mono _ (fun lo hlo => ?_)
    have e : ∀ x, x < NSl → f (lo + NSl ^ l * (x + NSl * hi)) a H = indB (decide (pos d l x ∈
        qposQ K (nxt (g (op d) (shownS NSl L isO (lo + NSl ^ l * (0 + NSl * hi)))))
          (rgetL K (posAll pos L NSl d (lo + NSl ^ l * (0 + NSl * hi))) (rset K (pos d l 0) H a)) k H)) := fun x hx => by
      show indB (decide (pos d l (lsalt NSl l (lo + NSl ^ l * (x + NSl * hi))) ∈ _)) = _
      rw [lsalt_at hlo hx, shownS_eq hN hu hlo hx, comM_eq hK hN pos hdist d hl hlo hx ha]
    rw [sumTo_congr _ e]
    have h := salts_in (pos d l) (hs d l) (qposQ K (nxt (g (op d) (shownS NSl L isO (lo + NSl ^ l * (0 + NSl * hi)))))
      (rgetL K (posAll pos L NSl d (lo + NSl ^ l * (0 + NSl * hi))) (rset K (pos d l 0) H a)) k H)
    rwa [qposQ_length] at h
  refine Nat.le_of_mul_le_mul_left ?_ hK
  rw [sumTo_mul, sumTo_congr _ (fun σh _ => swap σh), sumTo_exch _ (K ^ n) (NSl ^ L)]
  rw [show K * (K ^ n * (NSl ^ (L - l - 1) * (NSl ^ l * (s * k)))) =
    sumTo (K ^ n) (fun _ => sumTo K (fun _ => NSl ^ (L - l - 1) * (NSl ^ l * (s * k)))) by
      rw [sumTo_const, sumTo_const]; ac_rfl]
  refine sumTo_mono _ (fun H _ => ?_)
  rw [sumTo_exch _ K (NSl ^ L)]
  exact sumTo_mono _ (fun a ha => per H a ha)

theorem unop_mem {L : Nat} {isO : Nat → Bool} {l : Nat} (h : l ∈ unop L isO) : l < L ∧ isO l = false := by
  have h' := List.mem_filter.1 h
  refine ⟨mem_lr h'.1, ?_⟩
  cases e : isO l
  · rfl
  · have := h'.2; rw [e] at this; exact absurd this (by decide)

/-- **The draws that hit an unopened leaf are few**: at most
    `UL Kⁿ NSl^(L-1) s k` over the salts and the table; normalized,
    `UL s k / NSl`, `UL` the unopened leaves. -/
theorem hitM_bound {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isO : Nat → Bool) (op : D → O) (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) (d : D) :
    sumTo (NSl ^ L * K ^ n) (fun σ => indB (hitL K (posU pos L NSl isO d (σ % NSl ^ L))
      (nxt (g (op d) (shownS NSl L isO (σ % NSl ^ L)))) (comM K NSl L pos d σ) k (σ / NSl ^ L))) ≤
      (unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (s * k))) := by
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
    ← sumTo_const (K ^ n * (NSl ^ (L - 1) * (s * k))) (unop L isO).length]
  refine sumTo_mono _ (fun j hj => ?_)
  have hm : (unop L isO).getD j 0 ∈ unop L isO := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem ..
  obtain ⟨hl, hu⟩ := unop_mem hm
  have b := hitLeaf_bound (k := k) hK hN pos hdist hlt hs isO op g nxt d hl hu
  refine Nat.le_trans b (Nat.le_of_eq ?_)
  rw [← Nat.mul_assoc (NSl ^ (L - _ - 1)), ← Nat.pow_add]
  congr 3; omega

/-- **The real opening of a Merkle tree's leaves is the ideal's up to the
    hits**: `K^UL` times the real count is within `K^UL UL Kⁿ NSl^(L-1) s k`
    of the ideal count, both ways. -/
theorem transferM {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isO : Nat → Bool) (op : D → O) (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat)
    (F : Nat → P × List Nat → Bool) (d : D) :
    let UL := (unop L isO).length
    K ^ UL * sumTo (NSl ^ L * K ^ n) (fun σ => indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ))) ≤
      sumTo (NSl ^ L * K ^ n * K ^ UL) (fun σ =>
        indB (F (comMI K NSl L UL pos d σ) (pfMI K NSl L UL k pos isO op g nxt d σ))) +
        K ^ UL * (UL * (K ^ n * (NSl ^ (L - 1) * (s * k)))) ∧
    sumTo (NSl ^ L * K ^ n * K ^ UL) (fun σ =>
        indB (F (comMI K NSl L UL pos d σ) (pfMI K NSl L UL k pos isO op g nxt d σ))) ≤
      K ^ UL * sumTo (NSl ^ L * K ^ n) (fun σ => indB (F (comM K NSl L pos d σ) (pfM K NSl L k pos isO op g nxt d σ))) +
        K ^ UL * (UL * (K ^ n * (NSl ^ (L - 1) * (s * k)))) := by
  intro UL
  have hb := hitM_bound (n := n) (L := L) (k := k) hK hN pos hdist hlt hs isO op g nxt d
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

/-- **The real opening of a Merkle tree's leaves hides up to the hits**,
    `2 UL s k / NSl` a draw normalized. -/
theorem pfM_hidesA {D O P : Type} {K n NSl L k s : Nat} (hK : 0 < K) (hN : 0 < NSl) (pos : D → Nat → Nat → Nat)
    (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) (hlt : ∀ d l a, l < L → pos d l a < n)
    (hs : ∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ s)
    (isO : Nat → Bool) (op : D → O) (hposO : ∀ d d', op d = op d' → ∀ l a, isO l = true → pos d l a = pos d' l a)
    (g : O → List Nat → P) (nxt : P → Nat → List Nat → Nat) :
    ComPfHidesA (NSl ^ L * K ^ n) ((unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))))
      (comM K NSl L pos) (pfM K NSl L k pos isO op g nxt) op := by
  intro d d' hop E
  have hKL : 0 < K ^ (unop L isO).length := Nat.pow_pos hK
  have t1 := (transferM (n := n) (L := L) (k := k) hK hN pos hdist hlt hs isO op g nxt E d).1
  have t2 := (transferM (n := n) (L := L) (k := k) hK hN pos hdist hlt hs isO op g nxt E d').2
  have hi := pfMI_hides (n := n) (NSl := NSl) (L := L) (k := k) hK pos hdist hlt isO op hposO g nxt d d' hop E
  rw [hi] at t1
  refine Nat.le_of_mul_le_mul_left ?_ hKL
  refine Nat.le_trans (Nat.le_trans t1 (Nat.add_le_add_right t2 _)) (Nat.le_of_eq ?_)
  rw [Nat.two_mul]
  simp only [Nat.mul_add, Nat.add_assoc]

theorem posAll_length {D : Type} (pos : D → Nat → Nat → Nat) (L NSl : Nat) (d : D) (σh : Nat) :
    (posAll pos L NSl d σh).length = L := by
  unfold posAll; rw [List.length_map, lr_length]
/-- **One Fiat–Shamir round over a Merkle tree's leaves drawn from the
    oracle** (`fs_openA` over `comM`, `pfM`): each leaf's hash the answer of
    the commitment's table at its position, read off its data and its own
    salt; the opening shows the opened leaves' data and salts, the unopened
    leaves' salts hidden; the bound gains `2 UL s k / NSl` a draw, `UL` the
    unopened leaves. -/
theorem fs_openROMM {PV PB D O P : Type} {NR m e1 e2 K n NSl L s k : Nat} (hK : 0 < K) (hN : 0 < NSl)
    (pos : D → Nat → Nat → Nat) (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b)
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
    (Q4 * Q4) ^ (K ^ L) * ((NSl ^ L * K ^ n) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * ((unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))))))) ∧
    sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) ((comM K NSl L pos) (sd (sop r t)) σ) H c) ((comM K NSl L pos) (sd (sop r t)) σ)
        (some ((pfM K NSl L k pos isO op g nxt) (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ (K ^ L)) (fun H => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H % Q4)) && E H ((comM K NSl L pos) (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H % Q4))
            r t)).map (fun _ => (pfM K NSl L k pos isO op g nxt) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((comM K NSl L pos) (main t r) σ) H % Q4))
            r t)))))) +
    (Q4 * Q4) ^ (K ^ L) * ((NSl ^ L * K ^ n) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * ((unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))))))) := by
  have hη : (unop L (fun _ => false)).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * 0)))) ≤
      (unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))) := by
    simp only [Nat.mul_zero]; exact Nat.zero_le _
  have hcom : ComHidesA (NSl ^ L * K ^ n) ((unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))))
      (comM K NSl L pos) :=
    fun d d' E => Nat.le_trans (pfM_hidesA (n := n) (L := L) (k := 0) (O := Unit) (P := Unit) hK hN pos hdist hlt hs
      (fun _ => false) (fun _ => ()) (fun _ _ _ _ _ h => absurd h Bool.false_ne_true) (fun _ _ => ()) (fun _ _ _ => 0)
      d d' rfl (fun c _ => E c)) (Nat.add_le_add_left hη _)
  have hrange : ∀ d σ, comM K NSl L pos d σ < K ^ L := fun d σ => by
    have h := rgetL_lt hK (posAll pos L NSl d (σ % NSl ^ L)) (σ / NSl ^ L)
    rwa [posAll_length] at h
  exact fs_openA (comM K NSl L pos) (pfM K NSl L k pos isO op g nxt) op sd d0 hcom
    (pfM_hidesA hK hN pos hdist hlt hs isO op hposO g nxt) hrange ov hovn main hsd sop h1 h2 hrv hsv hrvo hsvo E

/-- The root: any function of the leaves' answers (computed apart from
    their table), hashed in their place. -/
def rootM {D : Type} (R : Nat → Nat) (K NSl L : Nat) (pos : D → Nat → Nat → Nat) (d : D) (σ : Nat) : Nat :=
  R (comM K NSl L pos d σ)

/-- **One Fiat–Shamir round over a Merkle tree's root** (`fs_openROMM`
    with the root `R` of the leaves hashed in their place): an event of the
    root is an event of the leaves, so both hidings carry over. -/
theorem fs_openROMMR {PV PB D O P : Type} {NR m e1 e2 K n NSl L s k nR : Nat} (hK : 0 < K) (hN : 0 < NSl)
    (R : Nat → Nat) (hR : ∀ c, R c < nR)
    (pos : D → Nat → Nat → Nat) (hdist : ∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b)
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
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ nR) (fun H => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H % Q4)) && E H ((rootM R K NSl L pos) (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H % Q4))
            r t)).map (fun _ => (pfM K NSl L k pos isO op g nxt) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H % Q4))
            r t)))))) ≤
    sumTo ((Q4 * Q4) ^ nR) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) ((rootM R K NSl L pos) (sd (sop r t)) σ) H c) ((rootM R K NSl L pos) (sd (sop r t)) σ)
        (some ((pfM K NSl L k pos isO op g nxt) (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ nR * ((NSl ^ L * K ^ n) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * ((unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))))))) ∧
    sumTo ((Q4 * Q4) ^ nR) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) ((rootM R K NSl L pos) (sd (sop r t)) σ) H c) ((rootM R K NSl L pos) (sd (sop r t)) σ)
        (some ((pfM K NSl L k pos isO op g nxt) (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ nR) (fun H => sumTo (NSl ^ L * K ^ n) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H % Q4)) && E H ((rootM R K NSl L pos) (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H % Q4))
            r t)).map (fun _ => (pfM K NSl L k pos isO op g nxt) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) ((rootM R K NSl L pos) (main t r) σ) H % Q4))
            r t)))))) +
    (Q4 * Q4) ^ nR * ((NSl ^ L * K ^ n) * (e1 + e2) + Q4 * Q4 * (NR * (Q4 ^ m * ((unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))))))) := by
  have hη : (unop L (fun _ => false)).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * 0)))) ≤
      (unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))) := by
    simp only [Nat.mul_zero]; exact Nat.zero_le _
  have hcom : ComHidesA (NSl ^ L * K ^ n) ((unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))))
      (rootM R K NSl L pos) :=
    fun d d' E => Nat.le_trans (pfM_hidesA (n := n) (L := L) (k := 0) (O := Unit) (P := Unit) hK hN pos hdist hlt hs
      (fun _ => false) (fun _ => ()) (fun _ _ _ _ _ h => absurd h Bool.false_ne_true) (fun _ _ => ()) (fun _ _ _ => 0)
      d d' rfl (fun c _ => E (R c))) (Nat.add_le_add_left hη _)
  have hpf : ComPfHidesA (NSl ^ L * K ^ n) ((unop L isO).length * (K ^ n * (NSl ^ (L - 1) * (2 * (s * k)))))
      (rootM R K NSl L pos) (pfM K NSl L k pos isO op g nxt) op :=
    fun d d' hop E => pfM_hidesA hK hN pos hdist hlt hs isO op hposO g nxt d d' hop (fun c pf => E (R c) pf)
  exact fs_openA (rootM R K NSl L pos) (pfM K NSl L k pos isO op g nxt) op sd d0 hcom hpf
    (fun d σ => hR _) ov hovn main hsd sop h1 h2 hrv hsv hrvo hsvo E

/-- **The hypotheses are met together, with `s = 1`** (not vacuous): leaf
    `l` with salt `a` at position `l + L (a mod NSl)`, below `L NSl`. -/
theorem merkleOpen_sat {D O : Type} (L NSl : Nat) (hL : 0 < L) (hN : 0 < NSl) (isO : Nat → Bool) (op : D → O) :
    let pos := fun (_ : D) (l a : Nat) => l + L * (a % NSl)
    (∀ d l l' a b, l < L → l' < L → l ≠ l' → pos d l a ≠ pos d l' b) ∧
    (∀ d l a, l < L → pos d l a < L * NSl) ∧
    (∀ d l v, sumTo NSl (fun x => indB (decide (pos d l x = v))) ≤ 1) ∧
    (∀ d d', op d = op d' → ∀ l a, isO l = true → pos d l a = pos d' l a) := by
  intro pos
  refine ⟨fun d l l' a b hl hl' hne e => hne ?_, fun d l a hl => ?_, fun d l v => ?_, fun _ _ _ _ _ _ => rfl⟩
  · have := congrArg (· % L) e
    simp only [pos, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at this
    exact this
  · show l + L * (a % NSl) < L * NSl
    have h1 : a % NSl + 1 ≤ NSl := Nat.mod_lt _ hN
    calc l + L * (a % NSl) < L + L * (a % NSl) := Nat.add_lt_add_right hl _
      _ = L * (a % NSl + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ L * NSl := Nat.mul_le_mul_left _ h1
  · have one := hs_one (D := D) NSl d 0 0 Nat.one_pos ((v - l) / L)
    refine Nat.le_trans (sumTo_mono _ (fun x hx => ?_)) one
    show indB (decide (l + L * (x % NSl) = v)) ≤ indB (decide (x = (v - l) / L))
    by_cases e : l + L * (x % NSl) = v
    · have hx' : x % NSl = x := Nat.mod_eq_of_lt hx
      rw [hx'] at e
      have : x = (v - l) / L := by
        rw [← e, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hL]
      rw [decide_eq_true this]; exact indB_le _
    · simp only [e, decide_false, indB]; exact Nat.zero_le _
end Circuit
