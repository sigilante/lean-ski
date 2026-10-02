import Ski.ZK.Transcript

/-!
# Polynomials over the extension, and their roots

A polynomial over `EF` as its coefficient list, lowest first (`cval`).
Synthetic division by `x - a` (`divq`) gives the root bound: a polynomial
with a nonzero coefficient vanishes at fewer distinct points than it has
coefficients (`roots_lt`), so among the `P^4` elements of `EF` it has fewer
roots than coefficients (`root_count`).  `EF` has no zero divisors
(`EF.mul_eq_zero`), because a nonzero element has an inverse.
-/

namespace Circuit

open ZKF

namespace EF

theorem mul_ne_zero {x y : EF} (hx : x ≠ zero) (hy : y ≠ zero) : x.mul y ≠ zero := fun h =>
  (mul_eq_zero h).elim hx hy

theorem sub_ne_zero {x y : EF} (h : x ≠ y) : x.sub y ≠ zero := fun e => h ((sub_eq_zero_iff x y).1 e)

end EF

-- ---------------------------------------------------------------------------
-- Polynomials as coefficient lists
-- ---------------------------------------------------------------------------

/-- A polynomial's value at `x`, its coefficients lowest first. -/
def cval (x : EF) : List EF → EF
  | [] => EF.zero
  | c :: cs => c.add (x.mul (cval x cs))

/-- Every coefficient is zero. -/
def AllZero (cs : List EF) : Prop := ∀ c ∈ cs, c = EF.zero

theorem cval_allZero (x : EF) : ∀ cs : List EF, AllZero cs → cval x cs = EF.zero
  | [], _ => rfl
  | c :: cs, h => by
    show c.add (x.mul (cval x cs)) = EF.zero
    rw [h c List.mem_cons_self, cval_allZero x cs (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')),
      EF.mul_zero, EF.zero_add]

/-- The quotient of synthetic division by `x - a`: one coefficient fewer. -/
def divq (a : EF) : List EF → List EF
  | [] => []
  | [_] => []
  | _ :: d :: cs => cval a (d :: cs) :: divq a (d :: cs)

theorem divq_length (a : EF) : ∀ cs : List EF, (divq a cs).length = cs.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: d :: cs => by
    show (divq a (d :: cs)).length + 1 = (d :: cs).length + 1 - 1
    rw [divq_length a (d :: cs)]
    simp only [List.length_cons]
    omega

/-- `c + x ((x - a) q + p_a) = (x - a) (p_a + x q) + (c + a p_a)`. -/
theorem div_step (x a c pa qx : EF) :
    c.add (x.mul (((x.sub a).mul qx).add pa)) = ((x.sub a).mul (pa.add (x.mul qx))).add (c.add (a.mul pa)) :=
  Q.eq_of_norm
    (p := (Q.var 2).add ((Q.var 0).mul ((((Q.var 0).sub (Q.var 1)).mul (Q.var 4)).add (Q.var 3))))
    (q := (((Q.var 0).sub (Q.var 1)).mul ((Q.var 3).add ((Q.var 0).mul (Q.var 4)))).add
      ((Q.var 2).add ((Q.var 1).mul (Q.var 3))))
    (by decide) (env8 x a c pa qx EF.zero EF.zero EF.zero)

/-- **Synthetic division**: `p(x) = (x - a) q(x) + p(a)`. -/
theorem cval_divq (x a : EF) : ∀ cs : List EF,
    cval x cs = ((x.sub a).mul (cval x (divq a cs))).add (cval a cs)
  | [] => by show EF.zero = ((x.sub a).mul EF.zero).add EF.zero; rw [EF.mul_zero, EF.add_zero]
  | [c] => by
    show c.add (x.mul EF.zero) = ((x.sub a).mul EF.zero).add (c.add (a.mul EF.zero))
    simp only [EF.mul_zero, EF.add_zero, EF.zero_add]
  | c :: d :: cs => by
    show c.add (x.mul (cval x (d :: cs))) =
      ((x.sub a).mul ((cval a (d :: cs)).add (x.mul (cval x (divq a (d :: cs)))))).add
        (c.add (a.mul (cval a (d :: cs))))
    rw [cval_divq x a (d :: cs)]
    exact div_step x a c _ _

/-- A root whose quotient is all zero is a zero polynomial. -/
theorem allZero_of_divq (a : EF) : ∀ cs : List EF, cval a cs = EF.zero → AllZero (divq a cs) → AllZero cs
  | [], _, _ => fun _ h => nomatch h
  | [c], h, _ => by
    have : c.add (a.mul EF.zero) = EF.zero := h
    rw [EF.mul_zero, EF.add_zero] at this
    intro c' hc'
    rw [List.mem_singleton.1 hc', this]
  | c :: d :: cs, h, hq => by
    have hq0 : cval a (d :: cs) = EF.zero := hq _ List.mem_cons_self
    have hrest : AllZero (d :: cs) :=
      allZero_of_divq a (d :: cs) hq0 (fun c' hc' => hq c' (List.mem_cons_of_mem _ hc'))
    have hc : c.add (a.mul (cval a (d :: cs))) = EF.zero := h
    rw [hq0, EF.mul_zero, EF.add_zero] at hc
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hc
    · exact hrest c' hc'

/-- **The root bound**: a polynomial with a nonzero coefficient vanishes at
    fewer distinct points than it has coefficients. -/
theorem roots_lt : ∀ (n : Nat) (cs : List EF), cs.length ≤ n → ¬ AllZero cs →
    ∀ pts : List EF, pts.Nodup → (∀ x ∈ pts, cval x cs = EF.zero) → pts.length < cs.length
  | n, cs, _, hz, [], _, _ => by
    rcases cs with _ | ⟨c, cs⟩
    · exact absurd (fun _ h => nomatch h) hz
    · exact Nat.succ_pos _
  | 0, cs, hl, hz, _ :: _, _, _ => by
    rcases cs with _ | ⟨c, cs⟩
    · exact absurd (fun _ h => nomatch h) hz
    · simp only [List.length_cons] at hl; omega
  | n + 1, cs, hl, hz, a :: rest, hnd, hr => by
    have ha : cval a cs = EF.zero := hr a List.mem_cons_self
    have hqz : ¬ AllZero (divq a cs) := fun h => hz (allZero_of_divq a cs ha h)
    have hql : (divq a cs).length = cs.length - 1 := divq_length a cs
    have hrest : ∀ x ∈ rest, cval x (divq a cs) = EF.zero := by
      intro x hx
      have hxa : x ≠ a := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hx)
      have e := cval_divq x a cs
      rw [hr x (List.mem_cons_of_mem _ hx), ha, EF.add_zero] at e
      exact ((EF.mul_eq_zero e.symm).resolve_left (EF.sub_ne_zero hxa))
    have ih := roots_lt n (divq a cs) (by omega) hqz rest (List.nodup_cons.1 hnd).2 hrest
    have hpos : 0 < cs.length := by
      rcases cs with _ | ⟨c, cs⟩
      · exact absurd (fun _ h => nomatch h) hz
      · exact Nat.succ_pos _
    simp only [List.length_cons]
    omega

-- ---------------------------------------------------------------------------
-- Counting roots among the elements of `EF`
-- ---------------------------------------------------------------------------

theorem efOf_inj {i j : Nat} (hi : i < Q4) (hj : j < Q4) (h : efOf i = efOf j) : i = j := by
  have h' : Tup.dec i = Tup.dec j := by
    have := (toEF_eq (a := Tup.dec i) (t := efOf j)).1 h
    rw [this]; rfl
  rw [← Tup.enc_dec hi, ← Tup.enc_dec hj, h']

theorem sumTo_filter (p : Nat → Bool) : ∀ n, sumTo n (fun i => if p i then 1 else 0) = ((List.range n).filter p).length
  | 0 => rfl
  | n + 1 => by
    show sumTo n _ + _ = _
    rw [sumTo_filter p n, List.range_succ, List.filter_append, List.length_append]
    show _ + (if p n = true then 1 else 0) = _
    cases h : p n
    · rw [List.filter_cons_of_neg (by rw [h]; decide), List.filter_nil]; rfl
    · rw [List.filter_cons_of_pos h, List.filter_nil]; rfl

/-- The elements numbered by a filtered range are distinct (without
    `List.nodup_range`, which uses choice). -/
theorem nodup_efOf_filter (p : Nat → Bool) : ∀ n, n ≤ Q4 → (((List.range n).filter p).map efOf).Nodup
  | 0, _ => List.nodup_nil
  | n + 1, hn => by
    rw [List.range_succ, List.filter_append, List.map_append, List.nodup_append]
    refine ⟨nodup_efOf_filter p n (by omega), ?_, ?_⟩
    · cases h : p n
      · rw [List.filter_cons_of_neg (by rw [h]; decide), List.filter_nil, List.map_nil]; exact List.nodup_nil
      · rw [List.filter_cons_of_pos h, List.filter_nil, List.map_cons, List.map_nil]
        exact List.nodup_cons.2 ⟨(fun h => nomatch h), List.nodup_nil⟩
    · intro a ha b hb e
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
      have hi' := List.mem_range.1 (List.mem_filter.1 hi).1
      have hj' : j = n := by
        have := (List.mem_filter.1 hj).1
        rw [List.mem_singleton] at this; exact this
      have := efOf_inj (by omega) (by omega) e
      omega

/-- **A polynomial with a nonzero coefficient has fewer roots in `EF` than
    coefficients.** -/
theorem root_count (cs : List EF) (hz : ¬ AllZero cs) :
    sumTo Q4 (fun i => if decide (cval (efOf i) cs = EF.zero) then 1 else 0) < cs.length := by
  rw [sumTo_filter]
  have hm := roots_lt cs.length cs (Nat.le_refl _) hz
    (((List.range Q4).filter (fun i => decide (cval (efOf i) cs = EF.zero))).map efOf)
    (nodup_efOf_filter _ Q4 (Nat.le_refl _))
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact of_decide_eq_true (List.mem_filter.1 hi).2)
  rwa [List.length_map] at hm

-- ---------------------------------------------------------------------------
-- Building polynomials
-- ---------------------------------------------------------------------------

/-- The sum of two polynomials. -/
def cadd : List EF → List EF → List EF
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => a.add b :: cadd p q

theorem cval_cadd (x : EF) : ∀ p q : List EF, cval x (cadd p q) = (cval x p).add (cval x q)
  | [], q => by show cval x q = EF.zero.add (cval x q); rw [EF.zero_add]
  | a :: p, [] => by show cval x (a :: p) = (cval x (a :: p)).add EF.zero; rw [EF.add_zero]
  | a :: p, b :: q => by
    show (a.add b).add (x.mul (cval x (cadd p q))) = (a.add (x.mul (cval x p))).add (b.add (x.mul (cval x q)))
    rw [cval_cadd x p q]
    exact Q.eq_of_norm
      (p := ((Q.var 0).add (Q.var 1)).add ((Q.var 2).mul ((Q.var 3).add (Q.var 4))))
      (q := ((Q.var 0).add ((Q.var 2).mul (Q.var 3))).add ((Q.var 1).add ((Q.var 2).mul (Q.var 4))))
      (by decide) (env8 a b x (cval x p) (cval x q) EF.zero EF.zero EF.zero)

theorem cadd_length : ∀ p q : List EF, (cadd p q).length ≤ max p.length q.length
  | [], q => by simp [cadd]
  | a :: p, [] => by simp [cadd]
  | a :: p, b :: q => by
    show (cadd p q).length + 1 ≤ max (p.length + 1) (q.length + 1)
    have := cadd_length p q
    omega

/-- A scalar multiple. -/
def cscale (c : EF) (p : List EF) : List EF := p.map c.mul

theorem cval_cscale (x c : EF) : ∀ p : List EF, cval x (cscale c p) = c.mul (cval x p)
  | [] => by show EF.zero = c.mul EF.zero; rw [EF.mul_zero]
  | a :: p => by
    show (c.mul a).add (x.mul (cval x (cscale c p))) = c.mul (a.add (x.mul (cval x p)))
    rw [cval_cscale x c p]
    exact Q.eq_of_norm
      (p := ((Q.var 0).mul (Q.var 1)).add ((Q.var 2).mul ((Q.var 0).mul (Q.var 3))))
      (q := (Q.var 0).mul ((Q.var 1).add ((Q.var 2).mul (Q.var 3))))
      (by decide) (env4 c a x (cval x p))

theorem cscale_length (c : EF) (p : List EF) : (cscale c p).length = p.length := List.length_map _

/-- The product with `x - a`. -/
def clin (a : EF) (p : List EF) : List EF := cadd (EF.zero :: p) (cscale a.neg p)

theorem cval_clin (x a : EF) (p : List EF) : cval x (clin a p) = (x.sub a).mul (cval x p) := by
  unfold clin
  rw [cval_cadd, cval_cscale]
  show (EF.zero.add (x.mul (cval x p))).add (a.neg.mul (cval x p)) = (x.sub a).mul (cval x p)
  exact Q.eq_of_norm
    (p := ((⟨k 0, k 0, k 0, k 0⟩ : Q).add ((Q.var 0).mul (Q.var 2))).add ((Q.var 1).neg.mul (Q.var 2)))
    (q := ((Q.var 0).sub (Q.var 1)).mul (Q.var 2))
    (by decide) (env3 x a (cval x p))

theorem clin_length (a : EF) (p : List EF) : (clin a p).length ≤ p.length + 1 := by
  unfold clin
  have := cadd_length (EF.zero :: p) (cscale a.neg p)
  rw [cscale_length] at this
  simp only [List.length_cons] at this
  omega

end Circuit
