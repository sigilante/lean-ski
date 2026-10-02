import Ski.ZK.Poly
import Ski.Circuit.ProbeBal

/-!
# LogUp is sound

**`logup_accept`**: tables whose buses do not balance pass Plonky3's
LogUp check for at most `P^4 (M^2 W + 2M)` of the `P^4 · P^4` challenge
pairs `(α, β)`, `M` the number of messages and `W` the widest tuple: a
fraction `(M^2 W + 2M) / P^4`.  Passing is the terminals summing to zero,
or a denominator vanishing, where a cheating prover's fraction column is
unconstrained and the verifier, which never checks denominators, accepts
whatever it holds.  `logup_sound` bounds the pairs with no vanishing
denominator by `P^4 (M^2 W + M)`; `abort_count` the others by `P^4 M`.

This is the interactive core, one attempt at uniform challenges for tables
fixed before them: that the tables are the ones the main commitment binds,
and that they satisfy the AIR, are the STARK's soundness, assumed; in the
non-interactive proof an adversary may retry, at a cost of `2^b` hashes a
try for the lookup grinding's `b` bits, and the challenges are hash
outputs, uniform in the random-oracle model.

The challenges are Plonky3's (`p3-batch-stark` 0.8.0, `p3-lookup`'s
`Challenges`): one pair for the batch; bus `i`'s prefix is
`α + (i + 1) β^W`, and a tuple `v` of a bus combines to `Σ v_j β^(w-1-j)`
(`hornerL`), every tuple of one bus of one width `w ≤ W`.  A message
`(b, v)` then has the denominator `α - φ_(b,v)(β)`, its fingerprint
`φ_(b,v)(β) = hornerL β v - (i + 1) β^W` a polynomial in `β` of `W + 1`
coefficients, distinct messages' distinct (`kpoly_inj`).  Two steps:

- at all but `M^2 W` values of `β`, the fingerprints of distinct messages
  differ (`root_count` on their difference);
- then the terminals' sum is `Σ_k c_k / (α - φ_k)` over the distinct
  messages, with net counts `c_k` (`group`), one nonzero when the buses do
  not balance; its numerator `Σ_k c_k ∏_(l ≠ k) (α - φ_l)` is nonzero at
  `φ_k` (`npoly_at`), so it has fewer than `M` roots (`alpha_count`).
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- A sum of fractions and its numerator
-- ---------------------------------------------------------------------------

/-- `Σ c / (α - φ)` over counts and points. -/
def rsum (α : EF) (ks : List (F × EF)) : EF := sumL (fun e => (EF.ofF e.1).mul (α.sub e.2).inv) ks

/-- `∏ (x - φ)`. -/
def dpoly : List (F × EF) → List EF
  | [] => [EF.one]
  | e :: r => clin e.2 (dpoly r)

/-- `Σ_k c_k ∏_(l ≠ k) (x - φ_l)`. -/
def npoly : List (F × EF) → List EF
  | [] => []
  | e :: r => cadd (cscale (EF.ofF e.1) (dpoly r)) (clin e.2 (npoly r))

theorem dpoly_length : ∀ ks : List (F × EF), (dpoly ks).length ≤ ks.length + 1
  | [] => Nat.le_refl 1
  | e :: r => by
    have := clin_length e.2 (dpoly r)
    have := dpoly_length r
    show (clin e.2 (dpoly r)).length ≤ r.length + 1 + 1
    omega

theorem npoly_length : ∀ ks : List (F × EF), (npoly ks).length ≤ ks.length
  | [] => Nat.le_refl 0
  | e :: r => by
    have h1 := cadd_length (cscale (EF.ofF e.1) (dpoly r)) (clin e.2 (npoly r))
    rw [cscale_length] at h1
    have h2 := dpoly_length r
    have h3 := clin_length e.2 (npoly r)
    have h4 := npoly_length r
    show (cadd _ _).length ≤ r.length + 1
    omega

theorem cval_one (x : EF) : cval x [EF.one] = EF.one := by
  show EF.one.add (x.mul EF.zero) = EF.one; rw [EF.mul_zero, EF.add_zero]

theorem dpoly_cons (x : EF) (e : F × EF) (r : List (F × EF)) :
    cval x (dpoly (e :: r)) = (x.sub e.2).mul (cval x (dpoly r)) := cval_clin x e.2 (dpoly r)

/-- `∏ (x - φ)` is nonzero off the points. -/
theorem dpoly_ne (x : EF) : ∀ ks : List (F × EF), (∀ e ∈ ks, x ≠ e.2) → cval x (dpoly ks) ≠ EF.zero
  | [], _ => by rw [show dpoly [] = [EF.one] from rfl, cval_one]; exact EF.one_ne_zero
  | e :: r, h => by
    rw [dpoly_cons]
    exact EF.mul_ne_zero (EF.sub_ne_zero (h e List.mem_cons_self))
      (dpoly_ne x r (fun e' he' => h e' (List.mem_cons_of_mem _ he')))

/-- `∏ (x - φ)` vanishes at the points. -/
theorem dpoly_root (x : EF) : ∀ ks : List (F × EF), (∃ e ∈ ks, e.2 = x) → cval x (dpoly ks) = EF.zero
  | [], ⟨_, h, _⟩ => nomatch h
  | e :: r, ⟨e', he', hx⟩ => by
    rw [dpoly_cons]
    rcases List.mem_cons.1 he' with rfl | hr
    · rw [hx, EF.sub_self, EF.zero_mul]
    · rw [dpoly_root x r ⟨e', hr, hx⟩, EF.mul_zero]

/-- `u (D (c u⁻¹ + R)) = (u u⁻¹) (c D) + u (D R)`. -/
theorem frac_step (u iu c d r : EF) :
    (u.mul d).mul ((c.mul iu).add r) = ((u.mul iu).mul (c.mul d)).add (u.mul (d.mul r)) :=
  Q.eq_of_norm
    (p := ((Q.var 0).mul (Q.var 3)).mul (((Q.var 2).mul (Q.var 1)).add (Q.var 4)))
    (q := (((Q.var 0).mul (Q.var 1)).mul ((Q.var 2).mul (Q.var 3))).add ((Q.var 0).mul ((Q.var 3).mul (Q.var 4))))
    (by decide) (env8 u iu c d r EF.zero EF.zero EF.zero)

/-- **The numerator**: off the points, `N(x) = (∏ (x - φ)) · Σ c / (x - φ)`. -/
theorem npoly_eval (x : EF) : ∀ ks : List (F × EF), (∀ e ∈ ks, x ≠ e.2) →
    cval x (npoly ks) = (cval x (dpoly ks)).mul (rsum x ks)
  | [], _ => by
    show EF.zero = (cval x [EF.one]).mul EF.zero
    rw [EF.mul_zero]
  | e :: r, h => by
    have hr := npoly_eval x r (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    show cval x (cadd (cscale (EF.ofF e.1) (dpoly r)) (clin e.2 (npoly r))) =
      (cval x (dpoly (e :: r))).mul (((EF.ofF e.1).mul (x.sub e.2).inv).add (rsum x r))
    rw [cval_cadd, cval_cscale, cval_clin, hr, dpoly_cons, frac_step,
      EF.mul_inv (EF.sub_ne_zero (h e List.mem_cons_self)), EF.one_mul]

theorem ofF_ne_zero {c : F} (h : c ≠ 0) : EF.ofF c ≠ EF.zero := fun e => h (congrArg EF.x0 e)

/-- **The numerator is nonzero at a point with a nonzero count**, the points
    distinct. -/
theorem npoly_at : ∀ ks : List (F × EF), (ks.map Prod.snd).Nodup → ∀ e ∈ ks, e.1 ≠ 0 →
    cval e.2 (npoly ks) ≠ EF.zero
  | [], _, _, h, _ => nomatch h
  | e0 :: r, hnd, e, he, hc => by
    rw [List.map_cons, List.nodup_cons] at hnd
    show cval e.2 (cadd (cscale (EF.ofF e0.1) (dpoly r)) (clin e0.2 (npoly r))) ≠ EF.zero
    rw [cval_cadd, cval_cscale, cval_clin]
    rcases List.mem_cons.1 he with rfl | hr
    · rw [EF.sub_self, EF.zero_mul, EF.add_zero]
      exact EF.mul_ne_zero (ofF_ne_zero hc)
        (dpoly_ne _ r (fun e' he' h' => hnd.1 (List.mem_map.2 ⟨e', he', h'.symm⟩)))
    · have hne : e.2 ≠ e0.2 := fun h' => hnd.1 (h' ▸ List.mem_map.2 ⟨e, hr, rfl⟩)
      rw [dpoly_root e.2 r ⟨e, hr, rfl⟩, EF.mul_zero, EF.zero_add]
      exact EF.mul_ne_zero (EF.sub_ne_zero hne) (npoly_at r hnd.2 e hr hc)

/-- **The bound in `α`**: for distinct points and a nonzero count, fewer
    than as many `α` as there are points, off the points, zero the sum. -/
theorem alpha_count (ks : List (F × EF)) (hnd : (ks.map Prod.snd).Nodup) (hc : ∃ e ∈ ks, e.1 ≠ 0) :
    sumTo Q4 (fun i => if decide ((∀ e ∈ ks, efOf i ≠ e.2) ∧ rsum (efOf i) ks = EF.zero) then 1 else 0) <
      ks.length + 1 := by
  obtain ⟨e, he, hce⟩ := hc
  have hz : ¬ AllZero (npoly ks) := fun h => npoly_at ks hnd e he hce (cval_allZero _ _ h)
  have hlt := root_count (npoly ks) hz
  have hle : sumTo Q4 (fun i => if decide ((∀ e ∈ ks, efOf i ≠ e.2) ∧ rsum (efOf i) ks = EF.zero) then 1 else 0) ≤
      sumTo Q4 (fun i => if decide (cval (efOf i) (npoly ks) = EF.zero) then 1 else 0) := by
    refine sumTo_mono Q4 (fun i _ => ?_)
    rcases (inferInstance : Decidable ((∀ e ∈ ks, efOf i ≠ e.2) ∧ rsum (efOf i) ks = EF.zero)) with h | h
    · rw [decide_eq_false h]; exact Nat.zero_le _
    · rw [decide_eq_true h, decide_eq_true (by rw [npoly_eval _ ks h.1, h.2, EF.mul_zero])]
      exact Nat.le_refl _
  have := npoly_length ks
  omega

-- ---------------------------------------------------------------------------
-- Messages grouped by key
-- ---------------------------------------------------------------------------

/-- The distinct keys of a list of counted messages, each with its net
    count. -/
def group {K : Type} [DecidableEq K] : Nat → List (K × F) → List (K × F)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, e :: L => (e.1, countOf (e :: L) e.1) :: group n (L.filter (fun e' => !decide (e'.1 = e.1)))

theorem countOf_split {K : Type} [DecidableEq K] (k0 : K) : ∀ L : List (K × F),
    countOf L k0 = countOf (L.filter (fun e => decide (e.1 = k0))) k0 +
      countOf (L.filter (fun e => !decide (e.1 = k0))) k0
  | [] => (zero_add' 0).symm
  | e' :: L => by
    rcases (inferInstance : Decidable (e'.1 = k0)) with h' | h'
    · rw [List.filter_cons_of_neg (by simp only [decide_eq_false h']; decide),
        List.filter_cons_of_pos (by simp only [decide_eq_false h', Bool.not_false]), countOf_cons, countOf_cons,
        if_neg h', zero_add', zero_add', countOf_split k0 L]
    · rw [List.filter_cons_of_pos (by simp only [decide_eq_true h']), List.filter_cons_of_neg
        (by simp only [decide_eq_true h', Bool.not_true]; decide), countOf_cons, countOf_cons, if_pos h',
        countOf_split k0 L, add_assoc']

/-- **Grouping keeps the sum**: a sum over messages, each weighted by its
    key, is the sum over the distinct keys of their net counts. -/
theorem group_sum {K : Type} [DecidableEq K] (g : K → EF) : ∀ (n : Nat) (L : List (K × F)), L.length ≤ n →
    sumL (fun e => (EF.ofF e.2).mul (g e.1)) L = sumL (fun e => (EF.ofF e.2).mul (g e.1)) (group n L)
  | 0, [], _ => rfl
  | n + 1, [], _ => rfl
  | n + 1, e :: L, hl => by
    let k0 := e.1
    have ih := group_sum g n (L.filter (fun e' => !decide (e'.1 = k0)))
      (Nat.le_trans (List.length_filter_le _ _) (by simp only [List.length_cons] at hl; omega))
    show _ = ((EF.ofF (countOf (e :: L) k0)).mul (g k0)).add (sumL _ (group n _))
    rw [← ih, sumL_cons, sumL_filter _ (fun e' => decide (e'.1 = k0)) L,
      sumL_samekey g k0 _ (fun e' he' => of_decide_eq_true (List.mem_filter.1 he').2), ← EF.add_assoc,
      ← EF.add_mul, ← EF.ofF_add, countOf_cons, if_pos rfl, countOf_split k0 L, countOf_filter_eq, add_zero']

theorem group_keys {K : Type} [DecidableEq K] : ∀ (n : Nat) (L : List (K × F)), ∀ e ∈ group n L, ∃ e' ∈ L, e'.1 = e.1
  | 0, _, _, h => nomatch h
  | n + 1, [], _, h => nomatch h
  | n + 1, e0 :: L, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨e0, List.mem_cons_self, rfl⟩
    · obtain ⟨e', he', hk⟩ := group_keys n _ e h
      exact ⟨e', List.mem_cons_of_mem _ (List.mem_filter.1 he').1, hk⟩

theorem group_nodup {K : Type} [DecidableEq K] : ∀ (n : Nat) (L : List (K × F)), ((group n L).map Prod.fst).Nodup
  | 0, _ => List.nodup_nil
  | n + 1, [] => List.nodup_nil
  | n + 1, e0 :: L => by
    show ((e0.1, countOf (e0 :: L) e0.1) :: group n _).map Prod.fst |>.Nodup
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, group_nodup n _⟩
    obtain ⟨e, he, hk⟩ := List.mem_map.1 hm
    obtain ⟨e', he', hk'⟩ := group_keys n _ e he
    have := (List.mem_filter.1 he').2
    rw [hk', hk] at this
    simp at this

theorem group_count {K : Type} [DecidableEq K] : ∀ (n : Nat) (L : List (K × F)), L.length ≤ n →
    ∀ k, countOf L k ≠ 0 → (k, countOf L k) ∈ group n L
  | 0, [], _, _, h => absurd rfl h
  | 0, _ :: _, hl, _, _ => by simp only [List.length_cons] at hl; omega
  | n + 1, [], _, _, h => absurd rfl h
  | n + 1, e0 :: L, hl, k, h => by
    show (k, countOf (e0 :: L) k) ∈ (e0.1, countOf (e0 :: L) e0.1) :: group n _
    rcases (inferInstance : Decidable (k = e0.1)) with hk | hk
    · refine List.mem_cons_of_mem _ ?_
      have e1 : countOf (e0 :: L) k = countOf (L.filter (fun e' => !decide (e'.1 = e0.1))) k := by
        rw [countOf_cons, if_neg (fun e => hk e.symm), zero_add', countOf_filter_ne e0.1 k hk]
      rw [e1] at h ⊢
      exact group_count n _ (Nat.le_trans (List.length_filter_le _ _) (by simp only [List.length_cons] at hl; omega))
        k h
    · rw [hk]; exact List.mem_cons_self

theorem group_length {K : Type} [DecidableEq K] : ∀ (n : Nat) (L : List (K × F)), (group n L).length ≤ L.length
  | 0, _ => Nat.zero_le _
  | n + 1, [] => Nat.le_refl 0
  | n + 1, e0 :: L => by
    show (group n _).length + 1 ≤ L.length + 1
    exact Nat.succ_le_succ (Nat.le_trans (group_length n _) (List.length_filter_le _ _))

-- ---------------------------------------------------------------------------
-- Plonky3's fingerprints
-- ---------------------------------------------------------------------------

/-- `x^n`. -/
def epow (x : EF) : Nat → EF
  | 0 => EF.one
  | n + 1 => x.mul (epow x n)

theorem epow_add (x : EF) (a : Nat) : ∀ b, epow x (a + b) = (epow x a).mul (epow x b)
  | 0 => by rw [Nat.add_zero]; show _ = (epow x a).mul EF.one; rw [EF.mul_one]
  | b + 1 => by
    show x.mul (epow x (a + b)) = (epow x a).mul (x.mul (epow x b))
    rw [epow_add x a b, ← EF.mul_assoc, EF.mul_comm x, EF.mul_assoc]

/-- Bus `b`'s offset: `(i + 1) β^W`, `i` its index (`Challenges::new`). -/
def boff (idx : String → Nat) (W : Nat) (β : EF) (b : String) : EF := (EF.ofF (ofN (idx b + 1))).mul (epow β W)

/-- A message's fingerprint: its denominator is `α - fp`. -/
def fp (idx : String → Nat) (W : Nat) (β : EF) (k : String × List F) : EF := (hornerL β k.2).sub (boff idx W β k.1)

theorem den_fp (idx : String → Nat) (W : Nat) (α β : EF) (b : String) (v : List F) :
    den (prefixOf α (boff idx W β)) β b v = α.sub (fp idx W β (b, v)) := prefix_den _ _ _

/-- A fingerprint's coefficients, lowest first: the tuple reversed, zeros,
    then `-(i + 1)` at `β^W`. -/
def kpoly (idx : String → Nat) (W : Nat) (k : String × List F) : List EF :=
  (k.2.reverse.map EF.ofF ++ List.replicate (W - k.2.length) EF.zero) ++ [(EF.ofF (ofN (idx k.1 + 1))).neg]

theorem cval_append (x : EF) : ∀ p q : List EF, cval x (p ++ q) = (cval x p).add ((epow x p.length).mul (cval x q))
  | [], q => by
    show cval x q = EF.zero.add (EF.one.mul (cval x q)); rw [EF.zero_add, EF.one_mul]
  | c :: p, q => by
    show c.add (x.mul (cval x (p ++ q))) = (c.add (x.mul (cval x p))).add ((x.mul (epow x p.length)).mul (cval x q))
    rw [cval_append x p q]
    exact Q.eq_of_norm
      (p := (Q.var 0).add ((Q.var 1).mul ((Q.var 2).add ((Q.var 3).mul (Q.var 4)))))
      (q := ((Q.var 0).add ((Q.var 1).mul (Q.var 2))).add (((Q.var 1).mul (Q.var 3)).mul (Q.var 4)))
      (by decide) (env8 c x (cval x p) (epow x p.length) (cval x q) EF.zero EF.zero EF.zero)

theorem hornerL_cval (x : EF) : ∀ (l : List F) (acc : EF),
    l.foldl (fun acc e => (acc.mul x).add (EF.ofF e)) acc =
      (acc.mul (epow x l.length)).add (cval x (l.reverse.map EF.ofF))
  | [], acc => by
    show acc = (acc.mul EF.one).add EF.zero; rw [EF.mul_one, EF.add_zero]
  | e :: l, acc => by
    rw [List.foldl_cons, hornerL_cval x l, List.reverse_cons, List.map_append, cval_append, List.length_map,
      List.length_reverse]
    show (((acc.mul x).add (EF.ofF e)).mul (epow x l.length)).add (cval x (l.reverse.map EF.ofF)) =
      (acc.mul (x.mul (epow x l.length))).add ((cval x (l.reverse.map EF.ofF)).add
        ((epow x l.length).mul ((EF.ofF e).add (x.mul EF.zero))))
    exact Q.eq_of_norm
      (p := ((((Q.var 0).mul (Q.var 1)).add (Q.var 2)).mul (Q.var 3)).add (Q.var 4))
      (q := ((Q.var 0).mul ((Q.var 1).mul (Q.var 3))).add ((Q.var 4).add
        ((Q.var 3).mul ((Q.var 2).add ((Q.var 1).mul ⟨k 0, k 0, k 0, k 0⟩)))))
      (by decide) (env8 acc x (EF.ofF e) (epow x l.length) (cval x (l.reverse.map EF.ofF)) EF.zero EF.zero EF.zero)

theorem hornerL_eq (x : EF) (l : List F) : hornerL x l = cval x (l.reverse.map EF.ofF) := by
  unfold hornerL
  rw [hornerL_cval, EF.zero_mul, EF.zero_add]

theorem cval_replicate (x : EF) (n : Nat) : cval x (List.replicate n EF.zero) = EF.zero :=
  cval_allZero x _ (fun _ h => (List.eq_of_mem_replicate h))

/-- **The coefficients are the fingerprint's.** -/
theorem kpoly_cval (idx : String → Nat) (W : Nat) (β : EF) (k : String × List F) (hW : k.2.length ≤ W) :
    cval β (kpoly idx W k) = fp idx W β k := by
  unfold kpoly fp boff
  rw [cval_append, cval_append, cval_replicate, EF.mul_zero, EF.add_zero, List.length_append, List.length_map,
    List.length_reverse, List.length_replicate, ← hornerL_eq, show k.2.length + (W - k.2.length) = W by omega]
  show (hornerL β k.2).add ((epow β W).mul (((EF.ofF (ofN (idx k.1 + 1))).neg).add (β.mul EF.zero))) =
    (hornerL β k.2).sub ((EF.ofF (ofN (idx k.1 + 1))).mul (epow β W))
  exact Q.eq_of_norm
    (p := (Q.var 0).add ((Q.var 1).mul ((Q.var 2).neg.add ((Q.var 3).mul ⟨.const 0, .const 0, .const 0, .const 0⟩))))
    (q := (Q.var 0).sub ((Q.var 2).mul (Q.var 1)))
    (by decide) (env4 (hornerL β k.2) (epow β W) (EF.ofF (ofN (idx k.1 + 1))) β)

theorem kpoly_length (idx : String → Nat) (W : Nat) (k : String × List F) (hW : k.2.length ≤ W) :
    (kpoly idx W k).length = W + 1 := by
  unfold kpoly
  simp only [List.length_append, List.length_map, List.length_reverse, List.length_replicate, List.length_singleton]
  omega

theorem ofF_inj {a b : F} (h : EF.ofF a = EF.ofF b) : a = b := congrArg EF.x0 h

theorem map_ofF_inj : ∀ {l l' : List F}, l.map EF.ofF = l'.map EF.ofF → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: l, b :: l', h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    rw [ofF_inj h.1, map_ofF_inj h.2]

theorem neg_inj {a b : EF} (h : a.neg = b.neg) : a = b := by
  have := congrArg EF.neg h
  rwa [show ∀ x : EF, x.neg.neg = x from fun x =>
      Q.eq_of_norm (p := (Q.var 0).neg.neg) (q := Q.var 0) (by decide) (env3 x EF.zero EF.zero),
    show ∀ x : EF, x.neg.neg = x from fun x =>
      Q.eq_of_norm (p := (Q.var 0).neg.neg) (q := Q.var 0) (by decide) (env3 x EF.zero EF.zero)] at this

/-- **Distinct messages have distinct coefficients**, each bus of one width
    at most `W`, the buses' indices distinct and below `P - 1`. -/
theorem kpoly_inj (idx : String → Nat) (W : Nat) (wd : String → Nat) {k k' : String × List F}
    (hw : k.2.length = wd k.1 ∧ wd k.1 ≤ W) (hw' : k'.2.length = wd k'.1 ∧ wd k'.1 ≤ W)
    (hP : idx k.1 + 1 < P) (hP' : idx k'.1 + 1 < P) (hidx : idx k.1 = idx k'.1 → k.1 = k'.1)
    (h : kpoly idx W k = kpoly idx W k') : k = k' := by
  unfold kpoly at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  rw [List.cons.injEq] at h2
  have hi : idx k.1 + 1 = idx k'.1 + 1 := ofN_inj hP hP' (ofF_inj (neg_inj h2.1))
  have hb : k.1 = k'.1 := hidx (by omega)
  have hl : (k.2.reverse.map EF.ofF).length = (k'.2.reverse.map EF.ofF).length := by
    simp only [List.length_map, List.length_reverse]; rw [hw.1, hw'.1, hb]
  have := (List.append_inj h1 hl).1
  have hv : k.2 = k'.2 := List.reverse_inj.1 (map_ofF_inj this)
  exact Prod.ext hb hv

/-- `p - q` as coefficients. -/
def cdiff (p q : List EF) : List EF := cadd p (cscale EF.one.neg q)

theorem cval_cdiff (x : EF) (p q : List EF) : cval x (cdiff p q) = (cval x p).sub (cval x q) := by
  unfold cdiff
  rw [cval_cadd, cval_cscale]
  exact Q.eq_of_norm (p := (Q.var 0).add ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 1)))
    (q := (Q.var 0).sub (Q.var 1)) (by decide) (env3 (cval x p) (cval x q) EF.zero)

theorem cdiff_allZero : ∀ (p q : List EF), p.length = q.length → AllZero (cdiff p q) → p = q
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | a :: p, b :: q, hl, hz => by
    have hz' : AllZero ((a.add (EF.one.neg.mul b)) :: cdiff p q) := hz
    have hab : a = b := by
      have e := hz' _ List.mem_cons_self
      calc a = (a.add (EF.one.neg.mul b)).add b :=
            Q.eq_of_norm (p := Q.var 0) (q := ((Q.var 0).add ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 1))).add
              (Q.var 1)) (by decide) (env3 a b EF.zero)
        _ = b := by rw [e, EF.zero_add]
    rw [hab, cdiff_allZero p q (by simp only [List.length_cons] at hl; omega)
      (fun c hc => hz' c (List.mem_cons_of_mem _ hc))]

theorem cdiff_length (p q : List EF) : (cdiff p q).length ≤ max p.length q.length := by
  unfold cdiff
  have := cadd_length p (cscale EF.one.neg q)
  rwa [cscale_length] at this

/-- **Two distinct messages' fingerprints collide at most at `W` values of
    `β`.** -/
theorem collide_count (idx : String → Nat) (W : Nat) (wd : String → Nat) {k k' : String × List F}
    (hw : k.2.length = wd k.1 ∧ wd k.1 ≤ W) (hw' : k'.2.length = wd k'.1 ∧ wd k'.1 ≤ W)
    (hP : idx k.1 + 1 < P) (hP' : idx k'.1 + 1 < P) (hidx : idx k.1 = idx k'.1 → k.1 = k'.1) (hne : k ≠ k') :
    sumTo Q4 (fun j => if decide (fp idx W (efOf j) k = fp idx W (efOf j) k') then 1 else 0) ≤ W := by
  have hl : (kpoly idx W k).length = (kpoly idx W k').length := by
    rw [kpoly_length idx W k (by omega), kpoly_length idx W k' (by omega)]
  have hz : ¬ AllZero (cdiff (kpoly idx W k) (kpoly idx W k')) := fun h =>
    hne (kpoly_inj idx W wd hw hw' hP hP' hidx (cdiff_allZero _ _ hl h))
  have hc := root_count _ hz
  have hlen := cdiff_length (kpoly idx W k) (kpoly idx W k')
  rw [hl, Nat.max_self, kpoly_length idx W k' (by omega)] at hlen
  have hle : sumTo Q4 (fun j => if decide (fp idx W (efOf j) k = fp idx W (efOf j) k') then 1 else 0) ≤
      sumTo Q4 (fun j => if decide (cval (efOf j) (cdiff (kpoly idx W k) (kpoly idx W k')) = EF.zero) then 1 else 0) := by
    refine sumTo_mono Q4 (fun j _ => ?_)
    rcases (inferInstance : Decidable (fp idx W (efOf j) k = fp idx W (efOf j) k')) with h | h
    · rw [decide_eq_false h]; exact Nat.zero_le _
    · rw [decide_eq_true h, decide_eq_true (by
        rw [cval_cdiff, kpoly_cval idx W _ k (by omega), kpoly_cval idx W _ k' (by omega), h, EF.sub_self])]
      exact Nat.le_refl _
  omega

-- ---------------------------------------------------------------------------
-- The theorem
-- ---------------------------------------------------------------------------

/-- Distinct keys, injective images: the images are distinct. -/
theorem nodup_map_of {K : Type} (f : K → EF) : ∀ L : List (K × F), (L.map Prod.fst).Nodup →
    (∀ e ∈ L, ∀ e' ∈ L, e.1 ≠ e'.1 → f e.1 ≠ f e'.1) → (L.map (fun e => f e.1)).Nodup
  | [], _, _ => List.nodup_nil
  | e :: L, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd ⊢
    refine ⟨fun hm => ?_, nodup_map_of f L hnd.2 (fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b
      (List.mem_cons_of_mem _ hb))⟩
    obtain ⟨e', he', hf⟩ := List.mem_map.1 hm
    have hk : e'.1 ≠ e.1 := fun hk => hnd.1 (List.mem_map.2 ⟨e', he', hk⟩)
    exact h e' (List.mem_cons_of_mem _ he') e List.mem_cons_self hk hf

theorem natSum_const {α : Type} (c : Nat) : ∀ l : List α, natSum l (fun _ => c) = l.length * c
  | [] => (Nat.zero_mul c).symm
  | _ :: l => by
    show c + natSum l _ = (l.length + 1) * c
    rw [natSum_const c l, Nat.succ_mul, Nat.add_comm]

/-- The net count on each key is the bus's balance. -/
theorem countOf_allEntries (ts : List (AirD × Table)) (bus : String) (v : List F) :
    countOf (allEntries ts) (bus, v) = ts.foldr (fun p acc => tableSends p.1 p.2 bus v + acc) 0 := by
  induction ts with
  | nil => rfl
  | cons p ts ih =>
    show countOf (entries p.1 p.2 ++ allEntries ts) (bus, v) = _
    rw [countOf_append, ih, countOf_entries, List.foldr_cons]

section
variable (idx : String → Nat) (W : Nat) (wd : String → Nat) (ts : List (AirD × Table))

/-- The terminals' sum, over the distinct messages. -/
theorem terminals_rsum (α β : EF) :
    sumL (fun p => terminal (prefixOf α (boff idx W β)) β p.1 p.2) ts =
      rsum α ((group (allEntries ts).length (allEntries ts)).map (fun e => (e.2, fp idx W β e.1))) := by
  rw [sumL_congr ts (fun p _ => terminal_entries (prefixOf α (boff idx W β)) β p.1 p.2),
    ← sumL_flatMap (fun e => (EF.ofF e.2).mul (den (prefixOf α (boff idx W β)) β e.1.1 e.1.2).inv)
      (fun p : AirD × Table => entries p.1 p.2) ts]
  refine (group_sum (fun k : String × List F => (den (prefixOf α (boff idx W β)) β k.1 k.2).inv)
    (allEntries ts).length (allEntries ts) (Nat.le_refl _)).trans ?_
  unfold rsum
  rw [sumL_map]
  refine sumL_congr _ (fun e _ => ?_)
  show (EF.ofF e.2).mul (den (prefixOf α (boff idx W β)) β e.1.1 e.1.2).inv = (EF.ofF e.2).mul (α.sub (fp idx W β e.1)).inv
  rw [den_fp]

/-- Some distinct messages collide at `β`. -/
def badB (G : List ((String × List F) × F)) (β : EF) : Bool :=
  G.any (fun e => G.any (fun e' => decide (e.1 ≠ e'.1) && decide (fp idx W β e.1 = fp idx W β e'.1)))

/-- **LogUp is sound, off the vanishing denominators**: tables whose buses
    do not balance have no vanishing denominator and terminals summing to
    zero for at most `P^4 (M^2 W + M)` of the `P^4 · P^4` challenge pairs
    `(α, β)` (`α` the `i`-th element of `EF`, `β` the `j`-th), `M` the
    messages.  Each bus carries tuples of one width `wd b ≤ W`, and the
    buses have distinct indices below `P - 1`, as Plonky3 lays them out. -/
theorem logup_sound
    (hw : ∀ e ∈ allEntries ts, e.1.2.length = wd e.1.1 ∧ wd e.1.1 ≤ W)
    (hP : ∀ e ∈ allEntries ts, idx e.1.1 + 1 < P)
    (hidx : ∀ e ∈ allEntries ts, ∀ e' ∈ allEntries ts, idx e.1.1 = idx e'.1.1 → e.1.1 = e'.1.1)
    (hb : ¬ Balanced ts) :
    sumTo Q4 (fun j => sumTo Q4 (fun i =>
      if (!Aborts (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) ts) &&
          decide (sumL (fun p => terminal (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) p.1 p.2) ts = EF.zero)
      then 1 else 0)) ≤
      Q4 * ((allEntries ts).length * (allEntries ts).length * W) + Q4 * (allEntries ts).length := by
  let E := allEntries ts
  let G := group E.length E
  let M := E.length
  have hGl : G.length ≤ M := group_length _ _
  -- the keys of `G` are messages
  have hG : ∀ g ∈ G, ∃ e ∈ E, e.1 = g.1 := group_keys _ _
  -- an unbalanced key
  have hnz : ∃ g ∈ G, g.2 ≠ 0 := by
    rcases (inferInstance : Decidable (∃ g ∈ G, g.2 ≠ 0)) with hno | h
    · refine absurd (fun bus v => ?_) hb
      rw [← countOf_allEntries]
      rcases (inferInstance : Decidable (countOf E (bus, v) = 0)) with h | h
      · exact absurd ⟨_, group_count E.length E (Nat.le_refl _) _ h, h⟩ hno
      · exact h
    · exact h
  -- per `β`
  have hinner : ∀ j, sumTo Q4 (fun i =>
      if (!Aborts (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) ts) &&
          decide (sumL (fun p => terminal (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) p.1 p.2) ts = EF.zero)
      then 1 else 0) ≤ Q4 * (if badB idx W G (efOf j) then 1 else 0) + M := by
    intro j
    cases hbad : badB idx W G (efOf j) with
    | true =>
      refine Nat.le_trans (sumTo_le_const (c := 1) (fun i => ?_) Q4) (by rw [Nat.mul_one]; exact Nat.le_add_right _ _)
      split <;> omega
    | false =>
      let ks := G.map (fun e => (e.2, fp idx W (efOf j) e.1))
      have hnd : (ks.map Prod.snd).Nodup := by
        rw [List.map_map]
        refine nodup_map_of (fp idx W (efOf j)) G (group_nodup _ _) (fun e he e' he' hne hf => ?_)
        have := List.any_eq_false.1 hbad e he
        rw [List.any_eq_true.2 ⟨e', he', by rw [decide_eq_true hne, decide_eq_true hf]; rfl⟩] at this
        exact this rfl
      have hc : ∃ e ∈ ks, e.1 ≠ 0 := by
        obtain ⟨g, hg, hg0⟩ := hnz
        exact ⟨_, List.mem_map.2 ⟨g, hg, rfl⟩, hg0⟩
      have hcount := alpha_count ks hnd hc
      have hks : ks.length = G.length := List.length_map _
      refine Nat.le_trans (sumTo_mono (g := fun i =>
          if decide ((∀ e ∈ ks, efOf i ≠ e.2) ∧ rsum (efOf i) ks = EF.zero) then 1 else 0) Q4 (fun i _ => ?_))
        (by rw [if_neg (by decide), Nat.mul_zero, Nat.zero_add]; omega)
      rcases hab : Aborts (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) ts with _ | _
      · rw [terminals_rsum]
        rcases (inferInstance : Decidable (rsum (efOf i) ks = EF.zero)) with hr | hr
        · show (if (!false) && decide (rsum (efOf i) ks = EF.zero) then 1 else 0) ≤ _
          rw [decide_eq_false hr]; exact Nat.zero_le _
        · have hoff : ∀ e ∈ ks, efOf i ≠ e.2 := by
            intro e he
            obtain ⟨g, hg, rfl⟩ := List.mem_map.1 he
            obtain ⟨e', he', hk⟩ := hG g hg
            have hden := List.any_eq_false.1 hab e' he'
            intro h
            apply hden
            have h' : efOf i = fp idx W (efOf j) g.1 := h
            rw [den_fp, show (e'.1.1, e'.1.2) = g.1 from hk, ← h', EF.sub_self]
            rfl
          show (if (!false) && decide (rsum (efOf i) ks = EF.zero) then 1 else 0) ≤
            if decide ((∀ e ∈ ks, efOf i ≠ e.2) ∧ rsum (efOf i) ks = EF.zero) then 1 else 0
          rw [decide_eq_true hr, decide_eq_true ⟨hoff, hr⟩]
          exact Nat.le_refl _
      · show (if (!true) && _ then 1 else 0) ≤ _
        exact Nat.zero_le _
  -- the colliding `β`
  have hcol : sumTo Q4 (fun j => if badB idx W G (efOf j) then 1 else 0) ≤ M * M * W := by
    let q : Nat → ((String × List F) × F) → ((String × List F) × F) → Nat := fun j e e' =>
      if decide (e.1 ≠ e'.1) && decide (fp idx W (efOf j) e.1 = fp idx W (efOf j) e'.1) then 1 else 0
    have h1 : ∀ j, (if badB idx W G (efOf j) then 1 else 0) ≤ natSum G (fun e => natSum G (fun e' => q j e e')) := by
      intro j
      refine Nat.le_trans (any_le _ G) (natSum_le G (fun e _ => any_le _ G))
    have h2 : ∀ e ∈ G, ∀ e' ∈ G, sumTo Q4 (fun j => q j e e') ≤ W := by
      intro e he e' he'
      rcases (inferInstance : Decidable (e.1 = e'.1)) with hk | hk
      · obtain ⟨a, ha, hak⟩ := hG e he
        obtain ⟨b, hb', hbk⟩ := hG e' he'
        refine Nat.le_trans (sumTo_mono Q4 (fun j _ => ?_)) (collide_count idx W wd (k := e.1) (k' := e'.1)
          (hak ▸ hw a ha) (hbk ▸ hw b hb') (hak ▸ hP a ha) (hbk ▸ hP b hb')
          (fun h => by rw [← hak, ← hbk]; exact hidx a ha b hb' (by rw [hak, hbk]; exact h)) hk)
        show (if decide (e.1 ≠ e'.1) && decide (fp idx W (efOf j) e.1 = fp idx W (efOf j) e'.1) then 1 else 0) ≤ _
        rw [decide_eq_true hk]
        exact Nat.le_refl _
      · refine Nat.le_trans (Nat.le_of_eq ((congrArg (sumTo Q4) (funext fun j => ?_)).trans
          (by rw [sumTo_const, Nat.mul_zero] : sumTo Q4 (fun _ => 0) = 0))) (Nat.zero_le W)
        show (if decide (e.1 ≠ e'.1) && _ then 1 else 0) = 0
        rw [decide_eq_false (fun h => h hk)]; rfl
    calc sumTo Q4 (fun j => if badB idx W G (efOf j) then 1 else 0)
        ≤ sumTo Q4 (fun j => natSum G (fun e => natSum G (fun e' => q j e e'))) := sumTo_mono Q4 (fun j _ => h1 j)
      _ = natSum G (fun e => natSum G (fun e' => sumTo Q4 (fun j => q j e e'))) := by
          rw [sumTo_natSum]; congr 1; funext e; rw [sumTo_natSum]
      _ ≤ natSum G (fun _ => natSum G (fun _ => W)) :=
          natSum_le G (fun e he => natSum_le G (fun e' he' => h2 e he e' he'))
      _ = G.length * (G.length * W) := by rw [natSum_const, natSum_const]
      _ ≤ M * (M * W) := Nat.mul_le_mul hGl (Nat.mul_le_mul_right W hGl)
      _ = M * M * W := (Nat.mul_assoc _ _ _).symm
  calc _ ≤ sumTo Q4 (fun j => Q4 * (if badB idx W G (efOf j) then 1 else 0) + M) := sumTo_mono Q4 (fun j _ => hinner j)
    _ = Q4 * sumTo Q4 (fun j => if badB idx W G (efOf j) then 1 else 0) + Q4 * M := by
        rw [sumTo_add, sumTo_mul_left, sumTo_const]
    _ ≤ Q4 * (M * M * W) + Q4 * M := Nat.add_le_add_right (Nat.mul_le_mul_left Q4 hcol) _

/-- **LogUp is sound**: tables whose buses do not balance pass the check --
    the terminals sum to zero, or a denominator vanishes and the cheating
    prover's column there is free -- for at most `P^4 (M^2 W + 2M)` of the
    `P^4 · P^4` challenge pairs. -/
theorem logup_accept
    (hw : ∀ e ∈ allEntries ts, e.1.2.length = wd e.1.1 ∧ wd e.1.1 ≤ W)
    (hP : ∀ e ∈ allEntries ts, idx e.1.1 + 1 < P)
    (hidx : ∀ e ∈ allEntries ts, ∀ e' ∈ allEntries ts, idx e.1.1 = idx e'.1.1 → e.1.1 = e'.1.1)
    (hb : ¬ Balanced ts) :
    sumTo Q4 (fun j => sumTo Q4 (fun i =>
      if Aborts (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) ts ||
          decide (sumL (fun p => terminal (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) p.1 p.2) ts = EF.zero)
      then 1 else 0)) ≤
      Q4 * ((allEntries ts).length * (allEntries ts).length * W) + 2 * (Q4 * (allEntries ts).length) := by
  have hs := logup_sound idx W wd ts hw hP hidx hb
  have ha : sumTo Q4 (fun j => sumTo Q4 (fun i =>
      if Aborts (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) ts then 1 else 0)) ≤
      Q4 * (allEntries ts).length :=
    sumTo_le_const (fun j => abort_count (boff idx W (efOf j)) (efOf j) ts) Q4
  calc _ ≤ sumTo Q4 (fun j => sumTo Q4 (fun i =>
          (if (!Aborts (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) ts) &&
            decide (sumL (fun p => terminal (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) p.1 p.2) ts =
              EF.zero) then 1 else 0) +
          (if Aborts (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) ts then 1 else 0))) := by
        refine sumTo_mono Q4 (fun j _ => sumTo_mono Q4 (fun i _ => ?_))
        cases Aborts (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) ts <;>
          cases decide (sumL (fun p => terminal (prefixOf (efOf i) (boff idx W (efOf j))) (efOf j) p.1 p.2) ts =
            EF.zero) <;> decide
    _ = _ := by
        rw [show (fun j => sumTo Q4 (fun i => _ + _)) = fun j => _ from funext fun j => sumTo_add _ _ Q4, sumTo_add]
    _ ≤ _ := by omega

end

end Circuit
