import Ski.GCert
open Term

/-!
# The finite graph fact G is sound, and the Ψ-skeleton bound

`notes/S4-bounded-exposure.md`, section R6.  `Ski/GCert.lean` checks a rank certificate on
blocks.  This module proves that the certificate describes head reduction:

* the checks, restated on `β` (`rank_chain`, `rank_other`, `rank_mid`, `fine_chain`, `fine_other`,
  `inv_three`, `inv_four`);
* the round abstraction is an invariant of the head run of `x z` (`round_inv`);
* the last step of a round, with the frame before it (`headChain_penult`);
* **`root_bound`**: a head run from a root frame, through frames that are not stable, has at
  most `rankT` of the frame, hence at most 67, steps whose first item has two or more items;
* **`psi_skeleton`**: a head run of a closed S-term through frames that are not stable has at
  most 77 such steps.
-/

namespace GCert
open HnfS HnfSound PsiSkel

/-! ## The fast copies are the originals -/

theorem all38 {f : Nat → Bool} (h : r38.all f = true) {y : Nat} (hy : y < 38) : f y = true :=
  List.all_eq_true.mp h y (List.mem_range.mpr hy)

theorem imp_of {p q : Bool} (h : (!p || q) = true) (hp : p = true) : q = true := by
  subst hp; exact h

theorem getD_ge {α : Type} : ∀ (l : List α) (n : Nat) (d : α), l.length ≤ n → l.getD n d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: l, n + 1, d, h => getD_ge l n d (Nat.le_of_succ_le_succ h)

def rowB : Bool := r38.all fun a => (blockTable.getD a []).length == 38
theorem rowB_eq : rowB = true := by decide +kernel

theorem ble_false {n x : Nat} (h : x < n) : Nat.ble n x = false := by
  cases hb : Nat.ble n x with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true hb) (Nat.not_le.mpr h)

theorem bf_eq (a b : Nat) : bf a b = β a b := by
  rcases Nat.lt_or_ge a 38 with ha | ha
  · rcases Nat.lt_or_ge b 38 with hb | hb
    · have h := Nat.eq_of_beq_eq_true (all38 (all38 bfB_eq ha) hb)
      exact h
    · have hl : (blockTable.getD a []).length = 38 := by
        have := all38 rowB_eq ha; exact beq_iff_eq.mp this
      show (bif Nat.ble 38 a || Nat.ble 38 b then 36 else _) = (blockTable.getD a []).getD b 36
      rw [Nat.ble_eq_true_of_le hb, Bool.or_true, getD_ge _ _ _ (by rw [hl]; exact hb)]; rfl
  · show (bif Nat.ble 38 a || Nat.ble 38 b then 36 else _) = (blockTable.getD a []).getD b 36
    rw [Nat.ble_eq_true_of_le ha, Bool.true_or, getD_ge blockTable a [] ha]; rfl

theorem pwf_eq (q : Nat) : pwf q = pw q := by
  rcases Nat.lt_or_ge q 38 with hq | hq
  · exact Nat.eq_of_beq_eq_true (all38 pwfB_eq hq)
  · show (bif Nat.ble 38 q then 0 else _) = piTable.getD q 0
    rw [Nat.ble_eq_true_of_le hq, getD_ge piTable q 0 hq]; rfl

theorem isOne_iff {x : Nat} (hx : x < 38) : isOne x = true ↔ x ∈ oneBlocks := by
  have h := all38 oneFB_eq hx
  rw [beq_iff_eq.mp h]; exact List.contains_iff_mem

theorem isComb_iff {x : Nat} (hx : x < 38) : isComb x = true ↔ x ∈ combBlocks := by
  have h := all38 combFB_eq hx
  rw [beq_iff_eq.mp h]; exact List.contains_iff_mem

/-- Blocks of a root frame, as a proposition. -/
def Valid (x y z : Nat) : Prop := x ∉ combBlocks ∧ β (β (β 0 x) y) z = 36

theorem valid_of {x y z : Nat} (hx : x < 38) (h : Valid x y z) : valid x y z = true := by
  have hc : isComb x = false := by
    cases hb : isComb x with
    | false => rfl
    | true => exact absurd ((isComb_iff hx).mp hb) h.1
  show (!isComb x && Nat.beq (bf (bf (bf 0 x) y) z) 36) = true
  rw [hc]; simp only [bf_eq]; rw [h.2]; rfl

theorem fine_z {x y z : Nat} (h : fine x y z = true) : z = 31 ∨ z = 36 := by
  have h1 : (Nat.beq z 31 || Nat.beq z 36) = true := (Bool.and_eq_true _ _ ▸ h : _ ∧ _).1
  rcases (Bool.or_eq_true _ _ ▸ h1 : _ ∨ _) with h | h
  · exact .inl (Nat.eq_of_beq_eq_true h)
  · exact .inr (Nat.eq_of_beq_eq_true h)

theorem all2 {f : Nat → Bool} (h : [31, 36].all f = true) {z : Nat} (hz : z = 31 ∨ z = 36) :
    f z = true := by
  have h' := List.all_eq_true.mp h
  rcases hz with rfl | rfl
  · exact h' 31 (by simp)
  · exact h' 36 (by simp)

/-! ## The checks, restated on `β` -/

theorem rank_chain {a y z : Nat} (ha : a < 38) (hy : y < 38) (hz : z < 38)
    (hv : Valid (β 0 a) y z) (hf : fine (β 0 a) y z = false) (hv' : Valid a z (β y z)) :
    rho1 a z (β y z) ≤ rho1 (β 0 a) y z := by
  have h := all38 (all38 (a1 a ha) hy) hz
  simp only [bf_eq] at h
  refine Nat.le_of_ble_eq_true (imp_of h ?_)
  rw [valid_of (β_lt (by decide) ha) hv, hf, valid_of ha hv']; rfl

theorem rank_other {x y z : Nat} (hx : x < 38) (hy : y < 38) (hz : z < 38)
    (hv : Valid x y z) (ho : x ∉ oneBlocks) (hf : fine x y z = false) :
    1 + pw (β x z) + rhoM (β x z) (β y z) z ≤ rho1 x y z := by
  have h := all38 (all38 (a2 x hx) hy) hz
  simp only [bf_eq, pwf_eq] at h
  refine Nat.le_of_ble_eq_true (imp_of h ?_)
  have h1 : isOne x = false := by
    cases hb : isOne x with
    | false => rfl
    | true => exact absurd ((isOne_iff hx).mp hb) ho
  rw [valid_of hx hv, hf, h1]; rfl

theorem or_elim_false {p q : Bool} (h : (p || q) = true) (hp : p = false) : q = true := by
  subst hp; exact h

theorem rank_mid {z w p y' : Nat} (hw : w < 38) (hy : y' < 38) (hp : p ∈ Lz z) (hp38 : p < 38)
    (hc : p ∉ combBlocks) (hh : β (β 1 y') p ≠ 36) (hb : β (β (β 0 p) (β y' p)) w = 36)
    (hz : z < 38) :
    rho1 p (β y' p) w ≤ rhoM (β (β 1 y') p) w z := by
  have h := List.all_eq_true.mp (a3 z hz) p hp
  have hc' : isComb p = false := by
    cases hb : isComb p with
    | false => rfl
    | true => exact absurd ((isComb_iff hp38).mp hb) hc
  have h := all38 (or_elim_false h hc') hy
  simp only [bf_eq] at h
  have h36 : Nat.beq (β (β 1 y') p) 36 = false := by
    cases hb : Nat.beq (β (β 1 y') p) 36 with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) hh
  have h := all38 (or_elim_false h h36) hw
  exact Nat.le_of_ble_eq_true (imp_of h (by rw [hb]; rfl))

theorem fine_le {c e y z : Nat} (hc : c < 38) (he : e < 38) (hy : y < 38)
    (hf : fine (β c e) y z = true) : rho2 c e y z ≤ rho1 (β c e) y z := by
  have h := all2 (all38 (all38 (cc c hc) he) hy) (fine_z hf)
  simp only [bf_eq] at h
  exact Nat.le_of_ble_eq_true (imp_of h hf)

/-- The rank of `S (c e) y z` is at most the coarse rank of its triple. -/
theorem phi_le {c e y z : Nat} (hc : c < 38) (he : e < 38) (hy : y < 38) :
    phi c e y z ≤ rho1 (β c e) y z := by
  show (bif fine (bf c e) y z then rho2 c e y z else rho1 (bf c e) y z) ≤ _
  rw [bf_eq]
  cases hf : fine (β c e) y z with
  | false => exact Nat.le_refl _
  | true => exact fine_le hc he hy hf

theorem rho1_le {x y z : Nat} (hx : x < 38) (hy : y < 38) (hz : z < 38) : rho1 x y z ≤ 67 :=
  Nat.le_of_ble_eq_true (all38 (all38 (bnd x hx) hy) hz)

theorem phi_fine {c e y z : Nat} (hf : fine (β c e) y z = true) : phi c e y z = rho2 c e y z := by
  show (bif fine (bf c e) y z then rho2 c e y z else rho1 (bf c e) y z) = _
  rw [bf_eq, hf]; rfl

theorem phi_coarse {c e y z : Nat} (hf : fine (β c e) y z = false) :
    phi c e y z = rho1 (β c e) y z := by
  show (bif fine (bf c e) y z then rho2 c e y z else rho1 (bf c e) y z) = _
  rw [bf_eq, hf]; rfl

theorem fine_chain {e y z c2 e2 : Nat} (he : e < 38) (hy : y < 38) (hc2 : c2 < 38) (he2 : e2 < 38)
    (hf : fine (β 0 e) y z = true) (hv : Valid e z (β y z)) (hd : β c2 e2 = e) :
    phi c2 e2 z (β y z) ≤ rho2 0 e y z := by
  have h := all2 (all38 (b0 e he) hy) (fine_z hf)
  simp only [bf_eq] at h
  have h : (!valid e z (bf y z) || r38.all fun c2 => r38.all fun e2 =>
      !(Nat.beq (bf c2 e2) e) || Nat.ble (phi c2 e2 z (bf y z)) (rho2 0 e y z)) = true :=
    imp_of h hf
  simp only [bf_eq] at h
  have h := all38 (all38 (imp_of h (valid_of he hv)) hc2) he2
  exact Nat.le_of_ble_eq_true (imp_of h (by rw [hd]; exact Nat.beq_refl e))

/-! ## Round states -/

theorem sK_mk {l P a b k : Nat} (hk : k < 39) : sK (mk l P a b k) = k := by unfold sK mk; omega
theorem sB_mk {l P a b k : Nat} (hb : b < 38) (hk : k < 39) : sB (mk l P a b k) = b := by
  unfold sB mk; omega
theorem sA_mk {l P a b k : Nat} (ha : a < 38) (hb : b < 38) (hk : k < 39) :
    sA (mk l P a b k) = a := by unfold sA mk; omega
theorem sP_mk {l P a b k : Nat} (hP : P < 38) (ha : a < 38) (hb : b < 38) (hk : k < 39) :
    sP (mk l P a b k) = P := by unfold sP mk; omega
theorem sL_mk {l P a b k : Nat} (hP : P < 38) (ha : a < 38) (hb : b < 38) (hk : k < 39) :
    sL (mk l P a b k) = l := by unfold sL mk; omega

theorem sH_mk {l P a b k : Nat} (hP : P < 38) (ha : a < 38) (hb : b < 38) (hk : k < 39) :
    sH (mk l P a b k) = β (β P a) b := by
  show bf (bf (sP _) (sA _)) (sB _) = _
  rw [sP_mk hP ha hb hk, sA_mk ha hb hk, sB_mk hb hk, bf_eq, bf_eq]

theorem mem_of_any {l : List Nat} {t : Nat} (h : (l.any fun u => Nat.beq u t) = true) : t ∈ l := by
  obtain ⟨u, hu, hb⟩ := List.any_eq_true.mp h
  exact Nat.eq_of_beq_eq_true hb ▸ hu

theorem band_left {p q : Bool} (h : (p && q) = true) : p = true := by
  cases p with
  | true => rfl
  | false => exact h
theorem band_right {p q : Bool} (h : (p && q) = true) : q = true := by
  cases p with
  | true => exact h
  | false => exact Bool.noConfusion h
theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem inv_ok {c e z : Nat} (hc : c < 38) (he : e < 38) (hz : z = 31 ∨ z = 36) :
    invOK c e z = true := by
  have h := all38 (invc c hc) he
  rcases hz with rfl | rfl
  · exact band_left h
  · exact band_right h

/-- Closure of the invariant set at a state of a frame `[x', a, b]`. -/
theorem inv_three {c e z P a b k x : Nat} (hc : c < 38) (he : e < 38) (hz : z = 31 ∨ z = 36)
    (hP : P < 38) (ha : a < 38) (hb : b < 38) (hk : k < 39) (hx : x < 38)
    (hm : mk 1 P a b k ∈ inv c e z) (h0 : β 0 x = P) (hx0 : x ≠ 0)
    (hh : β (β x b) (β a b) = β (β c e) z) :
    mk (bif isOne x then 1 else 0) x b (β a b) (b + 1) ∈ inv c e z := by
  have h := List.all_eq_true.mp (inv_ok hc he hz) _ hm
  unfold stepAll at h
  rw [sL_mk hP ha hb hk, show Nat.beq 1 1 = true from rfl, cond_true] at h
  have h := all38 h hx
  simp only [bf_eq, sP_mk hP ha hb hk, sA_mk ha hb hk, sB_mk hb hk] at h
  have h := imp_of h (by rw [h0, Nat.beq_refl, beq_false hx0]; rfl)
  rw [sH_mk hx hb (β_lt ha hb) (Nat.succ_lt_succ hb), hh] at h
  exact mem_of_any (imp_of h (Nat.beq_refl _))

/-- Closure of the invariant set at a state of a frame `[x', y', a, b]`. -/
theorem inv_four {c e z P a b k x y : Nat} (hc : c < 38) (he : e < 38) (hz : z = 31 ∨ z = 36)
    (hP : P < 38) (ha : a < 38) (hb : b < 38) (hk : k < 39) (hx : x < 38) (hy : y < 38)
    (hm : mk 0 P a b k ∈ inv c e z) (h0 : β (β 0 x) y = P)
    (hh : β (β (β x a) (β y a)) b = β (β c e) z) :
    mk (bif Nat.beq x 0 then 1 else 0) (β x a) (β y a) b k ∈ inv c e z := by
  have h := List.all_eq_true.mp (inv_ok hc he hz) _ hm
  unfold stepAll at h
  rw [sL_mk hP ha hb hk, show Nat.beq 0 1 = false from rfl, cond_false] at h
  have h := all38 (all38 h hx) hy
  simp only [bf_eq, sP_mk hP ha hb hk, sA_mk ha hb hk, sB_mk hb hk, sK_mk hk] at h
  have h := imp_of h (by rw [h0, Nat.beq_refl])
  rw [sH_mk (β_lt hx ha) (β_lt hy ha) hb hk, hh] at h
  exact mem_of_any (imp_of h (Nat.beq_refl _))

/-- The check at a fine node `(c, e, y, z)` with `c ≠ 0`. -/
theorem fine_other {c e y z : Nat} (hc : c < 38) (he : e < 38) (hy : y < 38) (hc0 : c ≠ 0)
    (hf : fine (β c e) y z = true) :
    1 + pw (β (β c e) z) ≤ rho2 c e y z ∧
    (β (β c e) z ≠ 36 →
      mk (bif isOne c then 1 else 0) c e z 0 ∈ inv c e z ∧
      ∀ a b k, a < 38 → b < 38 → k < 39 → mk 1 1 a b k ∈ inv c e z →
        Valid b (β a b) (β y z) →
        (k = 0 → 1 + pw (β (β c e) z) + rho1 b (β a b) (β y z) ≤ rho2 c e y z) ∧
        (∀ c2 g, c2 < 38 → k = g + 1 → β c2 g = b →
          1 + pw (β (β c e) z) + phi c2 g (β a b) (β y z) ≤ rho2 c e y z)) := by
  have h := all2 (all38 (all38 (bb c hc) he) hy) (fine_z hf)
  simp only [bf_eq] at h
  rw [hf, beq_false hc0] at h
  have h : otherOK c e y z = true := h
  unfold otherOK at h
  simp only [bf_eq, pwf_eq] at h
  refine ⟨Nat.le_of_ble_eq_true (band_left h), fun h36 => ?_⟩
  have h := or_elim_false (band_right h) (beq_false h36)
  refine ⟨mem_of_any (band_left h), fun a b k ha hb hk hm hv => ?_⟩
  have h := List.all_eq_true.mp (band_right h) _ hm
  have h1 : (1 : Nat) < 38 := by decide
  simp only [sL_mk h1 ha hb hk, sP_mk h1 ha hb hk, sA_mk ha hb hk, sB_mk hb hk, sK_mk hk] at h
  have h := imp_of h (by rw [valid_of hb hv]; rfl)
  constructor
  · intro hk0; subst hk0; exact Nat.le_of_ble_eq_true h
  · intro c2 g hc2 hkg hd; subst hkg
    have h : (r38.all fun c2 => !(Nat.beq (β c2 (g + 1 - 1)) b) ||
        Nat.ble (1 + pw (β (β c e) z) + phi c2 (g + 1 - 1) (β a b) (β y z)) (rho2 c e y z))
        = true := h
    have h := all38 h hc2
    rw [Nat.add_sub_cancel] at h
    exact Nat.le_of_ble_eq_true (imp_of h (by rw [hd]; exact Nat.beq_refl b))

/-! ## Head runs -/

theorem step_pure {t u₁ u₂ u₃ : Term} {rest : List Term} (ht : PureS t)
    (hS : t = rest.foldl Term.app (S ⬝ u₁ ⬝ u₂ ⬝ u₃)) :
    PureS (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) ∧
    fold (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) = fold t := by
  have hstep : WStep t (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := by
    rw [hS]; exact wstep_foldl (WStep.S u₁ u₂ u₃) rest
  exact wstep_pure hstep ht

theorem step_spine (u₁ u₂ u₃ : Term) (rest : List Term) :
    spine (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) = spine u₁ ++ u₃ :: (u₂ ⬝ u₃) :: rest := by
  rw [spine_foldl]; simp [spine]

theorem headChain_pure {t u : Term} (h : HeadChain t u) (ht : PureS t) :
    PureS u ∧ fold u = fold t := by
  induction h with
  | refl t => exact ⟨ht, rfl⟩
  | step hs hS _ ih =>
    obtain ⟨hp, he⟩ := step_pure ht hS
    obtain ⟨hp', he'⟩ := ih hp
    exact ⟨hp', he'.trans he⟩

theorem short_ne {α : Type} {l : List α} {a b c : α} {r : List α} (h : l = a :: b :: c :: r)
    (hl : l.length ≤ 2) : False := by
  subst h; exact absurd hl (Nat.not_le.mpr (Nat.le_add_left 3 r.length))

theorem spine_nil {t : Term} (ht : PureS t) (h : spine t = []) : t = S := by
  have := pure_eq_foldl ht; rw [h] at this; exact this

/-- The frame of an application `g` has one item exactly when its block is a one-item block. -/
theorem flag_spine {f x : Term} (hf : PureS f) (hx : PureS x) :
    (isOne (fold (f ⬝ x)) = true ∧ (spine (f ⬝ x)).length = 1) ∨
    (isOne (fold (f ⬝ x)) = false ∧ 2 ≤ (spine (f ⬝ x)).length) := by
  have hlt := fold_lt (.app hf hx)
  cases hb : isOne (fold (f ⬝ x)) with
  | true =>
    have h0 := (one_iff (fold_lt hf) (fold_lt hx)).1 ((isOne_iff hlt).1 hb)
    rw [fold_eq_zero hf h0]; exact .inl ⟨rfl, rfl⟩
  | false =>
    refine .inr ⟨rfl, ?_⟩
    match hs : spine f with
    | [] =>
      rw [spine_nil hf hs] at hb
      have := (isOne_iff (fold_lt (.app .S hx))).2 (fold_one_item hx)
      rw [hb] at this; exact Bool.noConfusion this
    | _ :: l =>
      show 2 ≤ (spine f ++ [x]).length
      rw [hs]; simp

/-- The state `(l, P, a, b, k)` describes the frame of `t`: the frame is `pre ++ [A, B]` with
`pre` of one item (`l = 1`) or of at least two (`l = 0`), `P` is the block of `S pre`, `a` and
`b` are the blocks of `A` and `B`, and if `k ≠ 0` then `B = f g` with `k - 1` the block of `g`. -/
def Conc (l P a b k : Nat) (t : Term) : Prop :=
  ∃ pre A B, spine t = pre ++ [A, B] ∧ (l = 1 ∧ pre.length = 1 ∨ l = 0 ∧ 2 ≤ pre.length) ∧
    walk 0 pre = P ∧ fold A = a ∧ fold B = b ∧ (k = 0 ∨ ∃ f g, B = f ⬝ g ∧ k = fold g + 1)

/-- **The round abstraction is an invariant.**  Along a head run from a term `t` of block
`β (β c e) z` whose frame is described by a state of the invariant set of `(c, e, z)`, to a
frame of at most two items, every frame is described by a state of the set; the run ends at
`S B (A B)` from a final state (`n = 3`, `P = 1`).  The states with `l = 0` lump the frames
`pre ++ [A, B]` with `pre` of two items and of more: a step from the latter keeps the state. -/
theorem round_inv {c e z : Nat} (hc38 : c < 38) (he38 : e < 38) (hz : z = 31 ∨ z = 36) :
    ∀ {t u : Term}, HeadChain t u → PureS t → fold t = β (β c e) z → (spine u).length ≤ 2 →
    ∀ l P a b k, Conc l P a b k t → k < 39 → mk l P a b k ∈ inv c e z →
    ∃ a' b' k' A B, a' < 38 ∧ b' < 38 ∧ k' < 39 ∧ mk 1 1 a' b' k' ∈ inv c e z ∧
      u = S ⬝ B ⬝ (A ⬝ B) ∧ fold A = a' ∧ fold B = b' ∧
      (k' = 0 ∨ ∃ f g, B = f ⬝ g ∧ k' = fold g + 1) := by
  intro t u hch
  induction hch with
  | refl t =>
    intro _ _ hu l P a b k hC _ _
    obtain ⟨pre, A, B, hs, hl, -⟩ := hC
    rw [hs, List.length_append] at hu
    have h2 : ([A, B] : List Term).length = 2 := rfl
    rw [h2] at hu
    exfalso
    rcases hl with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  | @step t v u₁ u₂ u₃ rest hs hS hc ih =>
    intro ht hf hu l P a b k hC hk hm
    obtain ⟨hp', he'⟩ := step_pure ht hS
    have hsp := step_spine u₁ u₂ u₃ rest
    have hpure := spine_pure ht
    rw [hs] at hpure
    have p₁ : PureS u₁ := hpure u₁ (by simp)
    have p₂ : PureS u₂ := hpure u₂ (by simp)
    have p₃ : PureS u₃ := hpure u₃ (by simp)
    obtain ⟨pre, A, B, hsC, hl, hP, hA, hB, hK⟩ := hC
    rw [hs] at hsC
    have hft := hf
    rw [← he'] at hf
    rcases hl with ⟨rfl, hl1⟩ | ⟨rfl, hl2⟩
    · -- a frame `[x', A, B]`
      obtain ⟨x', rfl⟩ : ∃ x', pre = [x'] := by
        match pre, hl1 with
        | [x'], _ => exact ⟨x', rfl⟩
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsC
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hsC
      have ha : a < 38 := hA ▸ fold_lt p₂
      have hb : b < 38 := hB ▸ fold_lt p₃
      have hP' : β 0 (fold u₁) = P := hP
      cases p₁ with
      | S =>
        have hP1 : P = 1 := hP'.symm
        subst hP1
        cases hc with
        | refl => exact ⟨a, b, k, u₂, u₃, ha, hb, hk, hm, rfl, hA, hB, hK⟩
        | step hs' _ _ =>
          rw [hsp] at hs'
          exact (short_ne hs' (Nat.le_refl 2)).elim
      | @app f g pf pg =>
        have hX := fold_lt (.app pf pg)
        have hPlt : P < 38 := hP' ▸ β_lt (by decide) hX
        have hmem := inv_three hc38 he38 hz hPlt ha hb hk hX hm hP'
          (beta_ne_zero (fold_lt pf) (fold_lt pg)) (by rw [← hf, ← hA, ← hB]; rfl)
        refine ih hp' hf hu _ _ _ _ _ ?_ (Nat.succ_lt_succ hb) hmem
        refine ⟨spine (f ⬝ g), u₃, u₂ ⬝ u₃, hsp, ?_, walk_spine (.app pf pg), hB, ?_,
          .inr ⟨u₂, u₃, rfl, by rw [hB]⟩⟩
        · rcases flag_spine pf pg with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1]; exact .inl ⟨rfl, h2⟩
          · rw [h1]; exact .inr ⟨rfl, h2⟩
        · show β (fold u₂) (fold u₃) = β a b
          rw [hA, hB]
    · -- a frame `x' :: y' :: pre₂ ++ [A, B]`
      obtain ⟨x', y', pre₂, rfl⟩ : ∃ x' y' pre₂, pre = x' :: y' :: pre₂ := by
        match pre, hl2 with
        | x' :: y' :: pre₂, _ => exact ⟨x', y', pre₂, rfl⟩
      cases pre₂ with
      | nil =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsC
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hsC
        have pB : PureS B := hpure B (by simp)
        have ha : a < 38 := hA ▸ fold_lt p₃
        have hb : b < 38 := hB ▸ fold_lt pB
        have hP' : β (β 0 (fold u₁)) (fold u₂) = P := hP
        have hPlt : P < 38 := hP' ▸ β_lt (β_lt (by decide) (fold_lt p₁)) (fold_lt p₂)
        have hmem := inv_four hc38 he38 hz hPlt ha hb hk (fold_lt p₁) (fold_lt p₂) hm hP'
          (by rw [← hf, ← hA, ← hB]; rfl)
        refine ih hp' hf hu _ _ _ _ _ ?_ hk hmem
        refine ⟨spine u₁ ++ [u₃], u₂ ⬝ u₃, B, by rw [hsp]; simp, ?_, ?_, ?_, hB, hK⟩
        · cases hb0 : Nat.beq (fold u₁) 0 with
          | true =>
            rw [fold_eq_zero p₁ (Nat.eq_of_beq_eq_true hb0)]; exact .inl ⟨rfl, rfl⟩
          | false =>
            refine .inr ⟨rfl, ?_⟩
            match hs1 : spine u₁ with
            | [] => rw [spine_nil p₁ hs1] at hb0; exact Bool.noConfusion hb0
            | _ :: l => simp
        · rw [walk_append, walk_spine p₁]; show β (fold u₁) (fold u₃) = _; rw [hA]
        · show β (fold u₂) (fold u₃) = _; rw [hA]
      | cons w pre₃ =>
        simp only [List.cons_append, List.cons.injEq] at hsC
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hsC
        refine ih hp' hf hu _ _ _ _ _ ?_ hk hm
        refine ⟨spine u₁ ++ u₃ :: (u₂ ⬝ u₃) :: pre₃, A, B, by rw [hsp]; simp, .inr ⟨rfl, by simp; omega⟩,
          ?_, hA, hB, hK⟩
        rw [← hP, walk_append]
        show walk (β (β (walk 0 (spine u₁)) (fold u₃)) (β (fold u₂) (fold u₃))) pre₃ =
          walk (β (β (β 0 (fold u₁)) (fold u₂)) (fold u₃)) pre₃
        rw [walk_spine p₁, compat (fold_lt p₁) (fold_lt p₂) (fold_lt p₃)]

/-- **The frame before the last step.**  A head run from a frame of at least three items to a
frame of at most two passes through `S S y z` and ends at `S z (y z)`. -/
theorem headChain_penult {t u : Term} (h : HeadChain t u) (ht : PureS t)
    (hl : 3 ≤ (spine t).length) (hu : (spine u).length ≤ 2) :
    ∃ y z, HeadChain t (S ⬝ S ⬝ y ⬝ z) ∧ u = S ⬝ z ⬝ (y ⬝ z) := by
  induction h with
  | refl t => exact absurd hl (Nat.not_le.mpr (Nat.lt_succ_of_le hu))
  | @step t v u₁ u₂ u₃ rest hs hS hc ih =>
    have hsp := step_spine u₁ u₂ u₃ rest
    have hp' := (step_pure ht hS).1
    have p₁ : PureS u₁ := spine_pure ht u₁ (by rw [hs]; exact List.mem_cons_self)
    match hsu : spine u₁, hr : rest with
    | a :: l, _ =>
      subst hr
      have h3 : 3 ≤ (spine (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃)))).length := by
        rw [hsp, hsu]
        show 3 ≤ (a :: (l ++ u₃ :: (u₂ ⬝ u₃) :: rest)).length
        rw [List.length_cons, List.length_append, List.length_cons, List.length_cons]
        exact Nat.succ_le_succ (Nat.le_trans (Nat.le_add_left 2 rest.length) (Nat.le_add_left _ _))
      obtain ⟨y, z, h1, h2⟩ := ih hp' h3 hu
      exact ⟨y, z, .step hs hS h1, h2⟩
    | [], r :: rest' =>
      subst hr
      have h3 : 3 ≤ (spine ((r :: rest').foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃)))).length := by
        rw [hsp, hsu]
        show 3 ≤ (u₃ :: (u₂ ⬝ u₃) :: r :: rest').length
        rw [List.length_cons, List.length_cons, List.length_cons]
        exact Nat.le_add_left 3 rest'.length
      obtain ⟨y, z, h1, h2⟩ := ih hp' h3 hu
      exact ⟨y, z, .step hs hS h1, h2⟩
    | [], [] =>
      subst hr
      have e₁ : u₁ = S := spine_nil p₁ hsu
      subst e₁
      cases hc with
      | refl => exact ⟨u₂, u₃, hS ▸ .refl _, rfl⟩
      | step hs' _ _ =>
        rw [hsp, hsu] at hs'
        exact (short_ne hs' (Nat.le_refl 2)).elim

/-! ## Runs through frames that are not stable -/

/-- A term of at least two items. -/
def isOther : Term → Bool
  | .app (.app _ _) _ => true
  | _ => false

/-- The frame `f w` is stable: `f` has no head normal form. -/
def Stable (t : Term) : Prop := ∃ f w, t = f ⬝ w ∧ ¬ HasHnf f

/-- `Run k n t u`: a head run of `k` steps from `t` to `u`, every step from a frame that is not
stable; `n` of the steps are *other* steps, those whose first frame item has at least two
items. -/
inductive Run : Nat → Nat → Term → Term → Prop
  | refl (t : Term) : Run 0 0 t t
  | step {k n : Nat} {t v u₁ u₂ u₃ : Term} {rest : List Term}
      (hs : spine t = u₁ :: u₂ :: u₃ :: rest)
      (hS : t = rest.foldl Term.app (S ⬝ u₁ ⬝ u₂ ⬝ u₃))
      (hns : ¬ Stable t)
      (h : Run k n (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) v) :
      Run (k + 1) (n + (if isOther u₁ then 1 else 0)) t v

/-- `Run` is inhabited beyond `refl`: one other step from `S (S S S) S S`, whose prefix
`S (S S S) S` is a head normal form. -/
theorem run_example :
    Run 1 1 (S ⬝ (S ⬝ S ⬝ S) ⬝ S ⬝ S) (S ⬝ S ⬝ S ⬝ S ⬝ (S ⬝ S)) :=
  Run.step (k := 0) (n := 0) (u₁ := S ⬝ S ⬝ S) (u₂ := S) (u₃ := S) (rest := []) rfl rfl
    (fun ⟨_, _, he, hn⟩ => by
      injection he with h1 _
      subst h1
      exact hn ⟨_, .refl _, .inr (.inr ⟨_, _, rfl⟩)⟩)
    (.refl _)

/-- An other step is not exempt in the sense of `HnfSound.root_step`. -/
theorem other_le {u : Term} (hu : PureS u) :
    (if isOther u then 1 else 0) ≤ (if exempt (fold u) then 0 else 1) := by
  match u, hu with
  | .S, _ => exact Nat.zero_le _
  | .app .S _, _ => exact Nat.zero_le _
  | .app (.app f a) b, hu =>
    obtain ⟨hfa, hb⟩ := hu.app_inv
    obtain ⟨hf, ha⟩ := hfa.app_inv
    obtain ⟨h1, h0⟩ := fold_two_items hf ha hb
    have he : exempt (fold (f ⬝ a ⬝ b)) = false := by
      cases h : exempt (fold (f ⬝ a ⬝ b)) with
      | false => rfl
      | true =>
        simp only [exempt, towerBlock, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h | h
        · exact absurd h h0
        · exact absurd (h ▸ (by decide : 17 ∈ oneBlocks)) h1
    rw [he]; exact Nat.le_refl _
  | .app .K _, hu => exact absurd hu.app_inv.1 PureS.not_K
  | .app .I _, hu => exact absurd hu.app_inv.1 PureS.not_I

theorem r1_le_pw {t : Term} (ht : PureS t) (hb : fold t ≠ 36) : r₁ t ≤ pw (fold t) := by
  have h := wt_le_pot 0 (by decide) (spine t) (spine_pure ht) (allH_spine ht hb)
  rw [walk_spine ht] at h
  have h0 : pw 0 = 0 := rfl
  rw [h0, Nat.zero_add] at h
  exact h

/-- A run from a term with a head normal form has at most `r₁` other steps. -/
theorem run_hnf {k n : Nat} {t u : Term} (h : Run k n t u) : PureS t → fold t ≠ 36 → n ≤ r₁ t := by
  induction h with
  | refl t => intro _ _; exact Nat.zero_le _
  | @step k n t v u₁ u₂ u₃ rest hs hS _ _ ih =>
    intro ht hb
    obtain ⟨hstep, _, hr, _, _⟩ := root_step ht hb hs
    obtain ⟨hp', he⟩ := wstep_pure hstep ht
    have := ih hp' (by rw [he]; exact hb)
    have := other_le (spine_pure ht u₁ (by rw [hs]; exact List.mem_cons_self))
    omega

/-- **Rounds (F2).**  A run from `f w` with `f` of block other than ⊥ follows the head run of
`f`: either it ends within it, after at most `r₁ f` other steps, or `f` head-reduces to a head
normal form `S p q` of two items and the run continues from the root frame `S p q w`. -/
theorem phase {k n : Nat} {t u : Term} (h : Run k n t u) :
    ∀ {f w : Term}, t = f ⬝ w → PureS f → PureS w → fold f ≠ 36 →
    n ≤ r₁ f ∨ ∃ k' n' p q, k' ≤ k ∧ n ≤ r₁ f + n' ∧ HeadChain f (S ⬝ p ⬝ q) ∧
      Run k' n' (S ⬝ p ⬝ q ⬝ w) u := by
  induction h with
  | refl t => intro _ _ _ _ _ _; exact .inl (Nat.zero_le _)
  | @step k n t v u₁ u₂ u₃ rest hs hS hns h ih =>
    intro f w ht hf hw hb
    subst ht
    have hsw : spine (f ⬝ w) = spine f ++ [w] := rfl
    rw [hsw] at hs
    match hsf : spine f with
    | [] => rw [hsf] at hs; exact (short_ne hs (Nat.le_succ 1)).elim
    | [_] => rw [hsf] at hs; exact (short_ne hs (Nat.le_refl 2)).elim
    | [p, q] =>
      have hfe : f = S ⬝ p ⬝ q := by have := pure_eq_foldl hf; rw [hsf] at this; exact this
      subst hfe
      exact .inr ⟨k + 1, _, p, q, Nat.le_refl _, Nat.le_add_left _ _, .refl _,
        .step (hsw ▸ hs) hS hns h⟩
    | a₁ :: a₂ :: a₃ :: r' =>
      rw [hsf] at hs
      simp only [List.cons_append, List.cons.injEq] at hs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
      obtain ⟨hstep, _, hr, _, _⟩ := root_step hf hb hsf
      obtain ⟨hp', he⟩ := wstep_pure hstep hf
      have hSf : f = r'.foldl Term.app (S ⬝ a₁ ⬝ a₂ ⬝ a₃) := by
        have h0 := pure_eq_foldl hf
        rw [hsf] at h0
        simpa only [List.foldl] using h0
      have hol := other_le (spine_pure hf a₁ (by rw [hsf]; exact List.mem_cons_self))
      rcases ih (f := r'.foldl Term.app (a₁ ⬝ a₃ ⬝ (a₂ ⬝ a₃))) (w := w)
          (by rw [List.foldl_append]; rfl) hp' hw (by rw [he]; exact hb) with hn | ⟨k', n', p, q, hk', hn, hch, hrun⟩
      · exact .inl (by omega)
      · exact .inr ⟨k', n', p, q, Nat.le_succ_of_le hk', by omega, .step hsf hSf hch, hrun⟩

/-! ## The bound -/

/-- The rank of a root frame `S (c e) y z`. -/
def rankT : Term → Nat
  | .app (.app (.app .S (.app c e)) y) z => phi (fold c) (fold e) (fold y) (fold z)
  | _ => 0

/-- The first item of a root frame is an application. -/
theorem root_head_app {x y z : Term} (hx : PureS x) (hy : PureS y) (hz : PureS z)
    (hb : fold (S ⬝ x ⬝ y ⬝ z) = 36) : ∃ c e, x = c ⬝ e ∧ PureS c ∧ PureS e := by
  cases hx with
  | S => exact absurd (by decide : fold S ∈ combBlocks) (root_head_not_comb hy hz hb)
  | @app c e hc he => exact ⟨c, e, rfl, hc, he⟩

theorem rankT_le {x y z : Term} (hx : PureS x) (hy : PureS y) (hz : PureS z)
    (hb : fold (S ⬝ x ⬝ y ⬝ z) = 36) :
    rankT (S ⬝ x ⬝ y ⬝ z) ≤ rho1 (fold x) (fold y) (fold z) := by
  obtain ⟨c, e, rfl, hc, he⟩ := root_head_app hx hy hz hb
  exact phi_le (fold_lt hc) (fold_lt he) (fold_lt hy)

theorem root_valid {x y z : Term} (hy : PureS y) (hz : PureS z)
    (hb : fold (S ⬝ x ⬝ y ⬝ z) = 36) : Valid (fold x) (fold y) (fold z) :=
  ⟨root_head_not_comb hy hz hb, hb⟩

theorem root_bound_aux : ∀ (K : Nat) {k n : Nat} {x y z u : Term}, k ≤ K → PureS x → PureS y →
    PureS z → fold (S ⬝ x ⬝ y ⬝ z) = 36 → Run k n (S ⬝ x ⬝ y ⬝ z) u →
    n ≤ rankT (S ⬝ x ⬝ y ⬝ z) := by
  intro K
  induction K with
  | zero =>
    intro k n x y z u hk _ _ _ _ h
    cases h with
    | refl => exact Nat.zero_le _
    | step _ _ _ _ => exact absurd hk (Nat.not_succ_le_zero _)
  | succ K ih =>
    intro k n x y z u hk hx hy hz hb h
    cases h with
    | refl => exact Nat.zero_le _
    | @step k' n' _ _ u₁ u₂ u₃ rest hs hS hns h =>
      have hs' : [x, y, z] = u₁ :: u₂ :: u₃ :: rest := hs
      simp only [List.cons.injEq] at hs'
      obtain ⟨rfl, rfl, rfl, hrest⟩ := hs'
      subst hrest
      have hk' : k' ≤ K := Nat.le_of_succ_le_succ hk
      have h : Run k' n' (x ⬝ z ⬝ (y ⬝ z)) u := h
      have hv := root_valid hy hz hb
      obtain ⟨hpn, hen⟩ := step_pure (rest := []) (.app (.app (.app .S hx) hy) hz) rfl
      have hbn : fold (x ⬝ z ⬝ (y ⬝ z)) = 36 := hen.trans hb
      obtain ⟨cT, eT, rfl, hcT, heT⟩ := root_head_app hx hy hz hb
      have hc := fold_lt hcT; have he := fold_lt heT
      have hy38 := fold_lt hy; have hz38 := fold_lt hz
      have hw38 : β (fold y) (fold z) < 38 := β_lt hy38 hz38
      cases hcT with
      | S =>
        -- a chain round: the next root frame is `S e z (y z)`
        have hn := ih hk' heT hz (.app hy hz) hbn h
        have hv' : Valid (fold eT) (fold z) (β (fold y) (fold z)) :=
          root_valid hz (.app hy hz) hbn
        obtain ⟨c₂, e₂, rfl, hc₂, he₂⟩ := root_head_app heT hz (.app hy hz) hbn
        refine Nat.le_trans hn ?_
        show phi (fold c₂) (fold e₂) (fold z) (β (fold y) (fold z)) ≤
          phi 0 (fold (c₂ ⬝ e₂)) (fold y) (fold z)
        cases hf : fine (β 0 (fold (c₂ ⬝ e₂))) (fold y) (fold z) with
        | true =>
          rw [phi_fine hf]
          exact fine_chain he hy38 (fold_lt hc₂) (fold_lt he₂) hf hv' rfl
        | false =>
          rw [phi_coarse hf]
          exact Nat.le_trans (phi_le (fold_lt hc₂) (fold_lt he₂) hz38)
            (rank_chain he hy38 hz38 hv hf hv')
      | @app c₁ c₀ hc₁ hc₀ =>
        -- an other round
        have hcT : PureS (c₁ ⬝ c₀) := .app hc₁ hc₀
        have hX := fold_two_items hc₁ hc₀ heT
        have hXlt := fold_lt (.app hcT heT)
        have hc0 : fold (c₁ ⬝ c₀) ≠ 0 := beta_ne_zero (fold_lt hc₁) (fold_lt hc₀)
        have pf : PureS (c₁ ⬝ c₀ ⬝ eT ⬝ z) := .app (.app hcT heT) hz
        have pw' : PureS (y ⬝ z) := .app hy hz
        -- the weight of the round is below the rank
        have hwt : 1 + pw (fold (c₁ ⬝ c₀ ⬝ eT ⬝ z)) ≤ rankT (S ⬝ (c₁ ⬝ c₀ ⬝ eT) ⬝ y ⬝ z) := by
          show _ ≤ phi (fold (c₁ ⬝ c₀)) (fold eT) (fold y) (fold z)
          cases hf : fine (β (fold (c₁ ⬝ c₀)) (fold eT)) (fold y) (fold z) with
          | true => rw [phi_fine hf]; exact (fine_other hc he hy38 hc0 hf).1
          | false =>
            rw [phi_coarse hf]
            exact Nat.le_trans (Nat.le_add_right _ _) (rank_other hXlt hy38 hz38 hv hX.1 hf)
        have hone : (if isOther (c₁ ⬝ c₀ ⬝ eT) then 1 else 0) = 1 := rfl
        rw [hone]
        rcases Nat.decEq (fold (c₁ ⬝ c₀ ⬝ eT ⬝ z)) 36 with h36 | h36
        · -- `x z` has a head normal form
          have hr1 := r1_le_pw pf h36
          rcases phase h rfl pf pw' h36 with hn | ⟨k'', n'', p, q, hk'', hn, hch, hrun⟩
          · exact Nat.le_trans (by omega) hwt
          · obtain ⟨hpq, hfq⟩ := headChain_pure hch pf
            have hp := hpq.app_inv.1.app_inv.2
            have hq := hpq.app_inv.2
            have hbr : fold (S ⬝ p ⬝ q ⬝ (y ⬝ z)) = 36 := by
              show β (fold (S ⬝ p ⬝ q)) (fold (y ⬝ z)) = 36
              rw [hfq]; exact hbn
            have hn'' := ih (Nat.le_trans hk'' hk') hp hq pw' hbr hrun
            have hv' := root_valid hq pw' hbr
            obtain ⟨c₂, e₂, rfl, hc₂, he₂⟩ := root_head_app hp hq pw' hbr
            have hgoal : 1 + pw (fold (c₁ ⬝ c₀ ⬝ eT ⬝ z)) +
                rankT (S ⬝ (c₂ ⬝ e₂) ⬝ q ⬝ (y ⬝ z)) ≤ rankT (S ⬝ (c₁ ⬝ c₀ ⬝ eT) ⬝ y ⬝ z) := by
              show _ + phi (fold c₂) (fold e₂) (fold q) (β (fold y) (fold z)) ≤
                phi (fold (c₁ ⬝ c₀)) (fold eT) (fold y) (fold z)
              cases hf : fine (β (fold (c₁ ⬝ c₀)) (fold eT)) (fold y) (fold z) with
              | false =>
                rw [phi_coarse hf]
                obtain ⟨y', z', hch', hE⟩ := headChain_penult hch pf
                  (by show 3 ≤ (spine c₁ ++ [c₀] ++ [eT] ++ [z]).length; simp) (Nat.le_refl 2)
                injection hE with hE1 hE2
                injection hE1 with _ hE1
                subst hE1; subst hE2
                obtain ⟨hpp, hfp⟩ := headChain_pure hch' pf
                have hy' := hpp.app_inv.1.app_inv.2
                have hL : fold (c₂ ⬝ e₂) ∈ Lz (fold z) :=
                  last_mem_Lz hch' pf hz38 (Lz_self hz38)
                have hh : β (β 1 (fold y')) (fold (c₂ ⬝ e₂)) = fold (c₁ ⬝ c₀ ⬝ eT ⬝ z) := hfp
                have hmid := rank_mid hw38 (fold_lt hy') hL (fold_lt hp) hv'.1
                  (by rw [hh]; exact h36) hv'.2 hz38
                rw [hh] at hmid
                have hoth := rank_other hXlt hy38 hz38 hv hX.1 hf
                have hle := phi_le (y := fold (y' ⬝ (c₂ ⬝ e₂))) (z := β (fold y) (fold z))
                  (fold_lt hc₂) (fold_lt he₂) (fold_lt hq)
                have hmid' : rho1 (β (fold c₂) (fold e₂)) (fold (y' ⬝ (c₂ ⬝ e₂)))
                    (β (fold y) (fold z)) ≤
                    rhoM (fold (c₁ ⬝ c₀ ⬝ eT ⬝ z)) (β (fold y) (fold z)) (fold z) := hmid
                have hoth' : 1 + pw (fold (c₁ ⬝ c₀ ⬝ eT ⬝ z)) +
                    rhoM (fold (c₁ ⬝ c₀ ⬝ eT ⬝ z)) (β (fold y) (fold z)) (fold z) ≤
                    rho1 (β (fold (c₁ ⬝ c₀)) (fold eT)) (fold y) (fold z) := hoth
                omega
              | true =>
                rw [phi_fine hf]
                obtain ⟨hstart, hfin⟩ := (fine_other hc he hy38 hc0 hf).2 h36
                have hconc : Conc (bif isOne (fold (c₁ ⬝ c₀)) then 1 else 0) (fold (c₁ ⬝ c₀))
                    (fold eT) (fold z) 0 (c₁ ⬝ c₀ ⬝ eT ⬝ z) := by
                  refine ⟨spine (c₁ ⬝ c₀), eT, z, by simp [spine], ?_, walk_spine hcT, rfl, rfl,
                    .inl rfl⟩
                  rcases flag_spine hc₁ hc₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · rw [h1]; exact .inl ⟨rfl, h2⟩
                  · rw [h1]; exact .inr ⟨rfl, h2⟩
                obtain ⟨a', b', k₁, A, B, ha', hb', hk₁, hmem, hE, hA, hB, hK⟩ :=
                  round_inv hc he (fine_z hf) hch pf rfl (Nat.le_refl 2) _ _ _ _ _ hconc
                    (by decide) hstart
                injection hE with hE1 hE2
                injection hE1 with _ hE1
                subst hE1; subst hE2
                have hval : Valid b' (β a' b') (β (fold y) (fold z)) := by
                  rw [← hA, ← hB]; exact hv'
                obtain ⟨hz0, hsucc⟩ := hfin a' b' k₁ ha' hb' hk₁ hmem hval
                rcases hK with hK | ⟨f, g, hfg, hK⟩
                · have h1 := hz0 hK
                  have hle := phi_le (y := fold (A ⬝ (c₂ ⬝ e₂))) (z := β (fold y) (fold z))
                    (fold_lt hc₂) (fold_lt he₂) (fold_lt hq)
                  have hle' : phi (fold c₂) (fold e₂) (fold (A ⬝ (c₂ ⬝ e₂))) (β (fold y) (fold z))
                      ≤ rho1 b' (β a' b') (β (fold y) (fold z)) := by
                    rw [← hA, ← hB]; exact hle
                  exact Nat.le_trans (Nat.add_le_add_left hle' _) h1
                · injection hfg with hf1 hf2
                  subst hf1; subst hf2
                  have h1 := hsucc (fold c₂) (fold e₂) (fold_lt hc₂) hK hB
                  have h1' : 1 + pw (β (β (fold (c₁ ⬝ c₀)) (fold eT)) (fold z)) +
                      phi (fold c₂) (fold e₂) (fold (A ⬝ (c₂ ⬝ e₂))) (β (fold y) (fold z)) ≤
                      rho2 (fold (c₁ ⬝ c₀)) (fold eT) (fold y) (fold z) := by
                    rw [← hA, ← hB] at h1; exact h1
                  exact h1'
            omega
        · -- `x z` is hnf-less: the frame `x z (y z)` is stable and the run stops
          cases h with
          | refl => have := hwt; omega
          | step _ _ hns' _ =>
            exact absurd ⟨_, _, rfl, no_hnf_of_bot pf h36⟩ hns'

/-- **Root frames.**  A run from a root frame (an hnf-less `S x y z`) has at most `rankT`
other steps. -/
theorem root_bound {k n : Nat} {x y z u : Term} (hx : PureS x) (hy : PureS y) (hz : PureS z)
    (hb : fold (S ⬝ x ⬝ y ⬝ z) = 36) (h : Run k n (S ⬝ x ⬝ y ⬝ z) u) :
    n ≤ rankT (S ⬝ x ⬝ y ⬝ z) :=
  root_bound_aux k (Nat.le_refl k) hx hy hz hb h

/-- A run from a root frame has at most 67 other steps. -/
theorem root_bound_67 {k n : Nat} {x y z u : Term} (hx : PureS x) (hy : PureS y) (hz : PureS z)
    (hb : fold (S ⬝ x ⬝ y ⬝ z) = 36) (h : Run k n (S ⬝ x ⬝ y ⬝ z) u) : n ≤ 67 :=
  Nat.le_trans (root_bound hx hy hz hb h)
    (Nat.le_trans (rankT_le hx hy hz hb) (rho1_le (fold_lt hx) (fold_lt hy) (fold_lt hz)))

/-- **Ψ-skeleton.**  A head run of a closed S-term through frames that are not stable has at
most 77 other steps (steps whose first frame item has at least two items).  In particular the
head run of an hnf-less term up to its first stable frame has at most 77 other steps. -/
theorem psi_skeleton {k n : Nat} {t u : Term} (ht : PureS t) (h : Run k n t u) : n ≤ 77 := by
  rcases Nat.decEq (fold t) 36 with hb | hb
  · exact Nat.le_trans (run_hnf h ht hb) (Nat.le_trans (BExp.r1_le ht hb) (by decide))
  · cases h with
    | refl => exact Nat.zero_le _
    | @step k' n' _ _ u₁ u₂ u₃ rest hs hS hns h' =>
      cases ht with
      | S => exact (short_ne hs (Nat.zero_le 2)).elim
      | @app f w hf hw =>
        have hfb : fold f ≠ 36 := fun h36 => hns ⟨f, w, rfl, no_hnf_of_bot hf h36⟩
        have hr := BExp.r1_le hf hfb
        rcases phase (.step hs hS hns h') rfl hf hw hfb with hn | ⟨k'', n'', p, q, _, hn, hch, hrun⟩
        · omega
        · obtain ⟨hpq, hfq⟩ := headChain_pure hch hf
          have hbr : fold (S ⬝ p ⬝ q ⬝ w) = 36 := by
            show β (fold (S ⬝ p ⬝ q)) (fold w) = 36
            rw [hfq]; exact hb
          have := root_bound_67 hpq.app_inv.1.app_inv.2 hpq.app_inv.2 hw hbr hrun
          omega

end GCert
