import Ski.ZK.Terminal

/-!
# A blinding tree hides the terminals

`chain_hides` (`Chain.lean`) blinds three tables along a path with two
tuples.  A circuit with more private tables blinds them along any
spanning tree: each edge a bus of its own, carrying one uniform 4-tuple,
its LogUp term added to one end's terminal and taken from the other's.
This file proves that such a tree hides the terminals: for a generic `β`,
two witnesses whose unblinded terminals have the same sum publish
identically distributed views over the tuples (`tree_hides`).

**The tree**, built leaf by leaf (`viewT`).  Vertex `k + 1` hangs from its
parent `par (k + 1) ≤ k` by edge `k`, with prefix `pre k`, tuple `t k`
and sign `sg k`: the new vertex publishes its terminal plus the edge's
term (`edgeTerm`: the tuple's LogUp term, negated when `sg k`, so the bus
may run either way), and the parent's terminal loses it.  Every tree has such a numbering (number the
vertices in any order that visits a parent before its children), so this
is every spanning tree.  `countN m` counts over the tuples of edges
`0 … m - 1`, each ranging over all of `F^4`.

**The proof**, by induction on the last leaf.  Shift the leaf's tuple by
the difference of the two witnesses' leaf terminals, a bijection for a
generic `β` (`edge_shift`): the leaf's view is then the other witness's,
and the difference moves to its parent.  Fix the leaf's tuple, and the
rest is a tree with one vertex fewer and equal sums.

`tree_chain` shows the three-table chain of the composed circuits is the
path memory ← CPU ← witness, and `chain_hides_tree` recovers
`chain_hides` from `tree_hides`.
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Views and counts
-- ---------------------------------------------------------------------------

/-- `x` with its value at `p` replaced by `v`. -/
def updF (x : Nat → EF) (p : Nat) (v : EF) : Nat → EF := fun j => if j = p then v else x j

/-- `t` with its tuple at `k` replaced by `a`. -/
def updT (t : Nat → Tup) (k : Nat) (a : Tup) : Nat → Tup := fun j => if j = k then a else t j

/-- The tuple outside the counted edges. -/
def tup0 : Tup := ⟨0, 0, 0, 0⟩

/-- **How many tuple assignments satisfy `p`**: edges `0 … m - 1`, each
    over all `P^4` tuples, the last edge outermost. -/
def countN : Nat → ((Nat → Tup) → Bool) → Nat
  | 0, p => if p (fun _ => tup0) then 1 else 0
  | m + 1, p => sumTo Q4 fun i => countN m (fun t => p (updT t m (Tup.dec i)))

/-- Edge `k`'s term on its child's side: the tuple's LogUp term, negated
    when the edge's bus runs the other way (`sg k`); the parent's side
    takes it away. -/
def edgeTerm (β : EF) (pre : Nat → EF) (sg : Nat → Bool) (k : Nat) (a : Tup) : EF :=
  if sg k then EF.zero.sub (blindTerm β (pre k) a) else blindTerm β (pre k) a

/-- **The tree's published view** of base terminals `x` under tuples `t`:
    `n` terminals, vertex `k + 1` a leaf on `par (k + 1)` by edge `k`. -/
def viewT (β : EF) (pre : Nat → EF) (sg : Nat → Bool) (par : Nat → Nat) : Nat → (Nat → EF) → (Nat → Tup) → List EF
  | 0, _, _ => []
  | 1, x, _ => [x 0]
  | n + 2, x, t =>
    viewT β pre sg par (n + 1) (updF x (par (n + 1)) ((x (par (n + 1))).sub (edgeTerm β pre sg n (t n)))) t ++
      [(x (n + 1)).add (edgeTerm β pre sg n (t n))]

section
variable {β : EF} {pre : Nat → EF} {sg : Nat → Bool} {par : Nat → Nat}

/-- The view reads the base terminals below `n` only. -/
theorem viewT_congr_x (hpar : ∀ k, par (k + 1) ≤ k) :
    ∀ (n : Nat) (x z : Nat → EF) (t : Nat → Tup), (∀ j, j < n → x j = z j) →
      viewT β pre sg par n x t = viewT β pre sg par n z t
  | 0, _, _, _, _ => rfl
  | 1, x, z, _, h => by show [x 0] = [z 0]; rw [h 0 (by omega)]
  | n + 2, x, z, t, h => by
    show viewT β pre sg par (n + 1) _ t ++ _ = viewT β pre sg par (n + 1) _ t ++ _
    have hp := hpar n
    rw [h (n + 1) (by omega), h (par (n + 1)) (by omega)]
    congr 1
    refine viewT_congr_x hpar (n + 1) _ _ t (fun j hj => ?_)
    unfold updF
    split
    · rfl
    · exact h j (by omega)

/-- The view reads the tuples of edges below `n - 1` only. -/
theorem viewT_congr_t : ∀ (n : Nat) (x : Nat → EF) (t s : Nat → Tup), (∀ j, j + 1 < n → t j = s j) →
    viewT β pre sg par n x t = viewT β pre sg par n x s
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | n + 2, x, t, s, h => by
    show viewT β pre sg par (n + 1) _ t ++ _ = viewT β pre sg par (n + 1) _ s ++ _
    rw [h n (by omega), viewT_congr_t (n + 1) _ t s (fun j hj => h j (by omega))]

end

theorem updT_self (t : Nat → Tup) (k : Nat) (a : Tup) : updT t k a k = a := if_pos rfl

theorem updT_updT (t : Nat → Tup) (k : Nat) (a b : Tup) : updT (updT t k a) k b = updT t k b := by
  funext j; unfold updT; split <;> rfl

/-- **A count does not change when a bijection reindexes the last edge.** -/
theorem countN_last (m : Nat) (p : (Nat → Tup) → Bool) {σ τ : Tup → Tup} (hl : ∀ a, τ (σ a) = a)
    (hr : ∀ a, σ (τ a) = a) :
    countN (m + 1) (fun t => p (updT t m (σ (t m)))) = countN (m + 1) p := by
  show (sumTo Q4 fun i => countN m (fun t => p (updT (updT t m (Tup.dec i)) m (σ (updT t m (Tup.dec i) m))))) =
    sumTo Q4 fun i => countN m (fun t => p (updT t m (Tup.dec i)))
  simp only [updT_updT, updT_self]
  exact sumTo_tup (fun a => countN m (fun t => p (updT t m a))) σ τ hl hr

-- ---------------------------------------------------------------------------
-- Sums over a range
-- ---------------------------------------------------------------------------

theorem sumL_range_succ (z : Nat → EF) (k : Nat) :
    sumL z (List.range (k + 1)) = (sumL z (List.range k)).add (z k) := by
  rw [List.range_succ, sumL_append, sumL_cons, sumL_nil, EF.add_zero]

theorem sumL_range_congr {f g : Nat → EF} : ∀ k, (∀ j, j < k → f j = g j) →
    sumL f (List.range k) = sumL g (List.range k)
  | 0, _ => rfl
  | k + 1, h => by
    rw [sumL_range_succ, sumL_range_succ, sumL_range_congr k (fun j hj => h j (by omega)), h k (by omega)]

theorem ef_upd_last (S zk w : EF) : S.add w = ((S.add zk).sub zk).add w :=
  Q.eq_of_norm (p := (Q.var 0).add (Q.var 2)) (q := (((Q.var 0).add (Q.var 1)).sub (Q.var 1)).add (Q.var 2))
    (by decide) (env3 S zk w)

theorem ef_upd_mid (S zp w zk : EF) : (((S.sub zp).add w).add zk) = (((S.add zk).sub zp).add w) :=
  Q.eq_of_norm (p := (((Q.var 0).sub (Q.var 1)).add (Q.var 2)).add (Q.var 3))
    (q := (((Q.var 0).add (Q.var 3)).sub (Q.var 1)).add (Q.var 2)) (by decide) (env4 S zp w zk)

/-- Replacing one entry below `k` changes the sum by the difference. -/
theorem sumL_updF (z : Nat → EF) (p : Nat) (w : EF) : ∀ k, p < k →
    sumL (updF z p w) (List.range k) = ((sumL z (List.range k)).sub (z p)).add w
  | 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, h => by
    rw [sumL_range_succ, sumL_range_succ]
    rcases Nat.lt_or_ge p k with hp | hp
    · rw [sumL_updF z p w k hp]
      have : updF z p w k = z k := if_neg (by omega)
      rw [this]
      exact ef_upd_mid _ _ _ _
    · have e : p = k := by omega
      subst e
      have ec := sumL_range_congr (f := updF z p w) (g := z) p (fun j hj => (if_neg (by omega) : updF z p w j = z j))
      rw [ec]
      have : updF z p w p = w := if_pos rfl
      rw [this]
      exact ef_upd_last _ _ _

-- ---------------------------------------------------------------------------
-- The tree hides the terminals
-- ---------------------------------------------------------------------------

theorem ef_leaf (x x' B : EF) : x'.add (B.add (x.sub x')) = x.add B := ef_shift_w x x' B

theorem ef_parent (a d b : EF) : (a.add d).sub (b.add d) = a.sub b :=
  Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).sub ((Q.var 2).add (Q.var 1)))
    (q := (Q.var 0).sub (Q.var 2)) (by decide) (env3 a d b)

/-- The sums after the leaf's shift: `S + x_v = S' + x'_v` gives
    `S + (x_v - x'_v) = S'`. -/
theorem ef_sums (S S' xv xv' : EF) (h : S.add xv = S'.add xv') : S.add (xv.sub xv') = S' := by
  have e : S.add (xv.sub xv') = (S.add xv).sub xv' :=
    Q.eq_of_norm (p := (Q.var 0).add ((Q.var 1).sub (Q.var 2))) (q := ((Q.var 0).add (Q.var 1)).sub (Q.var 2))
      (by decide) (env3 S xv xv')
  rw [e, h]
  exact Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).sub (Q.var 1)) (q := Q.var 0) (by decide) (env3 S' xv' EF.zero)

theorem ef_sub_both (S S' a a' B : EF) (h : S = S') :
    ((S.sub a).add (a.sub B)) = ((S'.sub a').add (a'.sub B)) := by
  subst h
  have e : ∀ c : EF, (S.sub c).add (c.sub B) = S.sub B := fun c =>
    Q.eq_of_norm (p := ((Q.var 0).sub (Q.var 1)).add ((Q.var 1).sub (Q.var 2)))
      (q := (Q.var 0).sub (Q.var 2)) (by decide) (env3 S c B)
  rw [e, e]

/-- The shift that adds `d` to an edge's term: `d` itself, or its negation
    on a negated edge. -/
def sgd (sg : Nat → Bool) (k : Nat) (d : EF) : EF := if sg k then EF.zero.sub d else d

theorem ef_neg_shift (B d : EF) : EF.zero.sub (B.add (EF.zero.sub d)) = (EF.zero.sub B).add d :=
  Q.eq_of_norm (p := (⟨k 0, k 0, k 0, k 0⟩ : Q).sub ((Q.var 0).add ((⟨k 0, k 0, k 0, k 0⟩ : Q).sub (Q.var 1))))
    (q := ((⟨k 0, k 0, k 0, k 0⟩ : Q).sub (Q.var 0)).add (Q.var 1)) (by decide) (env3 B d EF.zero)

/-- **Shifting an edge's tuple shifts its term**, for a generic `β`, on an
    edge of either sign. -/
theorem edge_shift {β : EF} (hg : Generic β) (pre : Nat → EF) (sg : Nat → Bool) (k : Nat) (d : EF) (a : Tup) :
    edgeTerm β pre sg k (shiftTup β (pre k) (sgd sg k d) a) = (edgeTerm β pre sg k a).add d := by
  unfold edgeTerm sgd
  cases sg k
  · simp only [Bool.false_eq_true, if_false]; exact shift_term hg _ _ _
  · simp only [if_true]; rw [shift_term hg]; exact ef_neg_shift _ _

/-- The leaf's shift: `x` with the leaf `v` set to `x'`'s and the
    difference moved to the parent `p`. -/
def leafShift (x x' : Nat → EF) (p v : Nat) : Nat → EF :=
  updF (updF x v (x' v)) p ((x p).add ((x v).sub (x' v)))

theorem leafShift_v {x x' : Nat → EF} {p v : Nat} (h : p < v) : leafShift x x' p v v = x' v := by
  unfold leafShift updF; rw [if_neg (by omega), if_pos rfl]

theorem leafShift_p (x x' : Nat → EF) (p v : Nat) : leafShift x x' p v p = (x p).add ((x v).sub (x' v)) := by
  unfold leafShift updF; rw [if_pos rfl]

theorem leafShift_j {x x' : Nat → EF} {p v j : Nat} (hj : j < v) (hjp : j ≠ p) : leafShift x x' p v j = x j := by
  unfold leafShift updF; rw [if_neg hjp, if_neg (by omega)]

/-- **A blinding tree hides the terminals**: for a generic `β`, a tree of
    `n` tables numbered leaf by leaf (`par (k + 1) ≤ k`), and two witnesses
    whose unblinded terminals `x` and `x'` have the same sum, the published
    views are identically distributed over the `n - 1` edge tuples: every
    event has the same count. -/
theorem tree_hides {β : EF} (hg : Generic β) (pre : Nat → EF) (sg : Nat → Bool) (par : Nat → Nat)
    (hpar : ∀ k, par (k + 1) ≤ k) :
    ∀ (n : Nat) (x x' : Nat → EF), sumL x (List.range n) = sumL x' (List.range n) → ∀ E : List EF → Bool,
      countN (n - 1) (fun t => E (viewT β pre sg par n x t)) = countN (n - 1) (fun t => E (viewT β pre sg par n x' t))
  | 0, _, _, _, _ => rfl
  | 1, x, x', hs, E => by
    have h0 : x 0 = x' 0 := by
      have := hs
      simp only [List.range_one, sumL_cons, sumL_nil, EF.add_zero] at this
      exact this
    show countN 0 (fun _ => E [x 0]) = countN 0 (fun _ => E [x' 0])
    rw [h0]
  | n + 2, x, x', hs, E => by
    show countN (n + 1) (fun t => E (viewT β pre sg par (n + 2) x t)) =
      countN (n + 1) (fun t => E (viewT β pre sg par (n + 2) x' t))
    have hp : par (n + 1) ≤ n := hpar n
    -- A. shift the leaf's tuple: the view of `x` is the view of the shifted base
    have stepA : ∀ t, viewT β pre sg par (n + 2) x t =
        viewT β pre sg par (n + 2) (leafShift x x' (par (n + 1)) (n + 1))
          (updT t n (shiftTup β (pre n) (sgd sg n ((x (n + 1)).sub (x' (n + 1)))) (t n))) := by
      intro t
      show viewT β pre sg par (n + 1) _ t ++ [(x (n + 1)).add (edgeTerm β pre sg n (t n))] =
        viewT β pre sg par (n + 1) _ _ ++ [(leafShift x x' (par (n + 1)) (n + 1) (n + 1)).add
          (edgeTerm β pre sg n (updT t n (shiftTup β (pre n) (sgd sg n ((x (n + 1)).sub (x' (n + 1)))) (t n)) n))]
      rw [updT_self, edge_shift hg, leafShift_v (by omega), ef_leaf]
      refine congrArg (fun L => L ++ [(x (n + 1)).add (edgeTerm β pre sg n (t n))]) ?_
      rw [viewT_congr_t (n + 1) _ (updT t n (shiftTup β (pre n) (sgd sg n ((x (n + 1)).sub (x' (n + 1)))) (t n))) t
        (fun j hj => (if_neg (by omega) : updT t n _ j = t j))]
      refine viewT_congr_x hpar (n + 1) _ _ t (fun j hj => ?_)
      show (if j = par (n + 1) then (x (par (n + 1))).sub _ else x j) =
        (if j = par (n + 1) then (leafShift x x' (par (n + 1)) (n + 1) (par (n + 1))).sub _
          else leafShift x x' (par (n + 1)) (n + 1) j)
      split
      · rw [leafShift_p, ef_parent]
      · next hjp => exact (leafShift_j (by omega) hjp).symm
    have hA : countN (n + 1) (fun t => E (viewT β pre sg par (n + 2) x t)) =
        countN (n + 1) (fun t => E (viewT β pre sg par (n + 2) (leafShift x x' (par (n + 1)) (n + 1)) t)) := by
      have key := countN_last n (fun s => E (viewT β pre sg par (n + 2) (leafShift x x' (par (n + 1)) (n + 1)) s))
        (σ := shiftTup β (pre n) (sgd sg n ((x (n + 1)).sub (x' (n + 1)))))
        (τ := unshiftTup β (pre n) (sgd sg n ((x (n + 1)).sub (x' (n + 1)))))
        (unshift_shift hg (pre n) _) (shift_unshift hg (pre n) _)
      rw [← key]
      exact congrArg (countN (n + 1)) (funext fun t => congrArg E (stepA t))
    rw [hA]
    -- B. fix the leaf's tuple; the rest is a tree of `n + 1` with equal sums
    show (sumTo Q4 fun i => countN n (fun t =>
        E (viewT β pre sg par (n + 2) (leafShift x x' (par (n + 1)) (n + 1)) (updT t n (Tup.dec i))))) =
      sumTo Q4 fun i => countN n (fun t => E (viewT β pre sg par (n + 2) x' (updT t n (Tup.dec i))))
    refine sumTo_congr _ fun i _ => ?_
    have split : ∀ (z : Nat → EF) (t : Nat → Tup), viewT β pre sg par (n + 2) z (updT t n (Tup.dec i)) =
        viewT β pre sg par (n + 1)
          (updF z (par (n + 1)) ((z (par (n + 1))).sub (edgeTerm β pre sg n (Tup.dec i)))) t ++
          [(z (n + 1)).add (edgeTerm β pre sg n (Tup.dec i))] := by
      intro z t
      show viewT β pre sg par (n + 1) _ (updT t n (Tup.dec i)) ++
        [(z (n + 1)).add (edgeTerm β pre sg n (updT t n (Tup.dec i) n))] = _
      rw [updT_self, viewT_congr_t (n + 1) _ (updT t n (Tup.dec i)) t
        (fun j hj => (if_neg (by omega) : updT t n _ j = t j))]
    simp only [split, leafShift_v (show par (n + 1) < n + 1 by omega)]
    -- the sums of the smaller tree agree
    have hsx : (sumL x (List.range (n + 1))).add (x (n + 1)) =
        (sumL x' (List.range (n + 1))).add (x' (n + 1)) := by
      rw [← sumL_range_succ, ← sumL_range_succ]; exact hs
    have hy : sumL (leafShift x x' (par (n + 1)) (n + 1)) (List.range (n + 1)) = sumL x' (List.range (n + 1)) := by
      have e1 : sumL (leafShift x x' (par (n + 1)) (n + 1)) (List.range (n + 1)) =
          sumL (updF x (par (n + 1)) ((x (par (n + 1))).add ((x (n + 1)).sub (x' (n + 1))))) (List.range (n + 1)) :=
        sumL_range_congr (n + 1) fun j hj => by
          by_cases hjp : j = par (n + 1)
          · subst hjp; rw [leafShift_p]; exact (if_pos rfl).symm
          · rw [leafShift_j hj hjp]; exact (if_neg hjp).symm
      rw [e1, sumL_updF x (par (n + 1)) _ (n + 1) (by omega)]
      rw [show ((sumL x (List.range (n + 1))).sub (x (par (n + 1)))).add
            ((x (par (n + 1))).add ((x (n + 1)).sub (x' (n + 1)))) =
          (sumL x (List.range (n + 1))).add ((x (n + 1)).sub (x' (n + 1))) from
        Q.eq_of_norm (p := ((Q.var 0).sub (Q.var 1)).add ((Q.var 1).add (Q.var 2)))
          (q := (Q.var 0).add (Q.var 2)) (by decide)
          (env3 (sumL x (List.range (n + 1))) (x (par (n + 1))) ((x (n + 1)).sub (x' (n + 1))))]
      exact ef_sums _ _ _ _ hsx
    have hsum : sumL (updF (leafShift x x' (par (n + 1)) (n + 1)) (par (n + 1))
          (((leafShift x x' (par (n + 1)) (n + 1)) (par (n + 1))).sub (edgeTerm β pre sg n (Tup.dec i))))
          (List.range (n + 1)) =
        sumL (updF x' (par (n + 1)) ((x' (par (n + 1))).sub (edgeTerm β pre sg n (Tup.dec i))))
          (List.range (n + 1)) := by
      rw [sumL_updF _ (par (n + 1)) _ (n + 1) (by omega), sumL_updF x' (par (n + 1)) _ (n + 1) (by omega)]
      exact ef_sub_both _ _ _ _ _ hy
    exact tree_hides hg pre sg par hpar (n + 1) _ _ hsum
      (fun L => E (L ++ [(x' (n + 1)).add (edgeTerm β pre sg n (Tup.dec i))]))

theorem ef_edge_cancel (S xp B xv : EF) : ((S.sub xp).add (xp.sub B)).add (xv.add B) = S.add xv :=
  Q.eq_of_norm
    (p := (((Q.var 0).sub (Q.var 1)).add ((Q.var 1).sub (Q.var 2))).add ((Q.var 3).add (Q.var 2)))
    (q := (Q.var 0).add (Q.var 3)) (by decide) (env4 S xp B xv)

/-- **The edges cancel**: the published view sums to the unblinded
    terminals' sum, whatever the tuples. -/
theorem viewT_sum (β : EF) (pre : Nat → EF) (sg : Nat → Bool) (par : Nat → Nat) (hpar : ∀ k, par (k + 1) ≤ k) :
    ∀ (n : Nat) (x : Nat → EF) (t : Nat → Tup),
      sumL (fun e => e) (viewT β pre sg par n x t) = sumL x (List.range n)
  | 0, _, _ => rfl
  | 1, x, _ => by
    show (x 0).add EF.zero = sumL x (List.range 1)
    simp only [List.range_one, sumL_cons, sumL_nil]
  | n + 2, x, t => by
    show sumL (fun e => e) (viewT β pre sg par (n + 1) _ t ++ [_]) = sumL x (List.range (n + 1 + 1))
    rw [sumL_range_succ x (n + 1), sumL_append, viewT_sum β pre sg par hpar (n + 1), sumL_cons, sumL_nil,
      EF.add_zero, sumL_updF x (par (n + 1)) _ (n + 1) (by have := hpar n; omega)]
    exact ef_edge_cancel _ _ _ _

-- ---------------------------------------------------------------------------
-- The chain is a tree
-- ---------------------------------------------------------------------------

/-- The composed circuits' chain as a tree: memory the root (0), the CPU
    on it by `blind_b` (edge 0), the witness table on the CPU by `blind_a`
    (edge 1). -/
def chainPar : Nat → Nat
  | 2 => 1
  | _ => 0

def chainPre (preA preB : EF) : Nat → EF
  | 0 => preB
  | _ => preA

def chainBase (x : View3) : Nat → EF
  | 0 => x.tm
  | 1 => x.tc
  | _ => x.tw

def chainTups (a b : Tup) : Nat → Tup := fun j => if j = 0 then b else a

theorem chainPar_ok : ∀ k, chainPar (k + 1) ≤ k
  | 0 => Nat.le_refl 0
  | 1 => Nat.le_refl 1
  | _ + 2 => Nat.zero_le _

/-- **The chain's view is the tree's**, in the order memory, CPU,
    witness. -/
theorem tree_chain (β preA preB : EF) (x : View3) (a b : Tup) :
    viewT β (chainPre preA preB) (fun _ => false) chainPar 3 (chainBase x) (chainTups a b) =
      [(chainView β preA preB x a b).tm, (chainView β preA preB x a b).tc, (chainView β preA preB x a b).tw] := by
  rfl

theorem chainBase_sum (x : View3) : sumL (chainBase x) (List.range 3) = x.sum :=
  Q.eq_of_norm (p := (Q.var 2).add ((Q.var 1).add ((Q.var 0).add ⟨k 0, k 0, k 0, k 0⟩)))
    (q := ((Q.var 0).add (Q.var 1)).add (Q.var 2)) (by decide) (env3 x.tw x.tc x.tm)

/-- The chain's event, on the tree's view. -/
def chainEvent (E : View3 → Bool) : List EF → Bool
  | [m, c, w] => E ⟨w, c, m⟩
  | _ => false

/-- **`chain_hides` from `tree_hides`**: the three-table instance. -/
theorem chain_hides_tree {β : EF} (hg : Generic β) (preA preB : EF) (x x' : View3) (hs : x.sum = x'.sum)
    (E : View3 → Bool) :
    count2 (fun a b => E (chainView β preA preB x a b)) = count2 (fun a b => E (chainView β preA preB x' a b)) := by
  have h := tree_hides hg (chainPre preA preB) (fun _ => false) chainPar chainPar_ok 3 (chainBase x) (chainBase x')
    (by rw [chainBase_sum, chainBase_sum, hs]) (chainEvent E)
  have e : ∀ z : View3, countN 2 (fun t => chainEvent E (viewT β (chainPre preA preB) (fun _ => false) chainPar 3 (chainBase z) t)) =
      count2 (fun a b => E (chainView β preA preB z a b)) := by
    intro z
    show (sumTo Q4 fun i => sumTo Q4 fun j => if chainEvent E (viewT β (chainPre preA preB) (fun _ => false) chainPar 3 (chainBase z)
      (updT (updT (fun _ => tup0) 0 (Tup.dec j)) 1 (Tup.dec i))) then 1 else 0) = _
    unfold count2
    refine sumTo_congr _ fun i _ => sumTo_congr _ fun j _ => ?_
    rw [viewT_congr_t 3 (chainBase z) _ (chainTups (Tup.dec i) (Tup.dec j)) (fun k hk => by
      unfold updT chainTups
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> rfl), tree_chain]
    rfl
  rw [← e x, ← e x']
  exact h

end Circuit
