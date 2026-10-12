import Ski.ZK.MaskRand

/-!
# FRI's view, and when a mask hides it

FRI tests the batched polynomial `B` for low degree by folding it: with a
challenge `β`, `B(X) = E(X²) + X·O(X²)` folds to `E + β·O` (`ffold`).  A
query at `x` reveals, at each layer, the sibling value `B_i(-x_i)`, the
verifier computing `B_{i+1}(x_i²)` from the pair (`fold_formula`), and the
last layer is sent as coefficients.  Polynomials here are coefficient
functions with an explicit length, so folding is pointwise.

FRI's view is linear in `B` (`friView_add`).  So a mask hides it the way
the column masks hide the openings: if a shift `Δ` of the mask's
randomness leaves every other opening alone and cancels the difference of
two witnesses on what FRI reveals, the views have one distribution
(`fri_hides_of_cancel`).  Plonky3 masks `B` with the random codeword and
randomization columns (ePrint 2024/1037 §4); that such a shift exists for
its parameters, a count of the points and functionals FRI reveals against
the masks' freedom, is not proved here.
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Polynomials as coefficient functions
-- ---------------------------------------------------------------------------

/-- The value at `x` of the polynomial with coefficients `c 0, …, c (n-1)`. -/
def ev : Nat → (Nat → EF) → EF → EF
  | 0, _, _ => EF.zero
  | n + 1, c, x => (c 0).add (x.mul (ev n (fun i => c (i + 1)) x))

theorem ev_add (x : EF) : ∀ (n : Nat) (c c' : Nat → EF),
    ev n (fun i => (c i).add (c' i)) x = (ev n c x).add (ev n c' x)
  | 0, _, _ => by show EF.zero = EF.zero.add EF.zero; rw [EF.add_zero]
  | n + 1, c, c' => by
    show ((c 0).add (c' 0)).add (x.mul (ev n (fun i => (c (i + 1)).add (c' (i + 1))) x)) =
      ((c 0).add (x.mul (ev n (fun i => c (i + 1)) x))).add ((c' 0).add (x.mul (ev n (fun i => c' (i + 1)) x)))
    rw [ev_add x n (fun i => c (i + 1)) (fun i => c' (i + 1))]
    exact Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).add ((Q.var 2).mul ((Q.var 3).add (Q.var 4))))
      (q := ((Q.var 0).add ((Q.var 2).mul (Q.var 3))).add ((Q.var 1).add ((Q.var 2).mul (Q.var 4))))
      (by decide) (env8 (c 0) (c' 0) x (ev n (fun i => c (i + 1)) x) (ev n (fun i => c' (i + 1)) x)
        EF.zero EF.zero EF.zero)

theorem ev_smul (x β : EF) : ∀ (n : Nat) (c : Nat → EF), ev n (fun i => β.mul (c i)) x = β.mul (ev n c x)
  | 0, _ => by show EF.zero = β.mul EF.zero; rw [EF.mul_zero]
  | n + 1, c => by
    show (β.mul (c 0)).add (x.mul (ev n (fun i => β.mul (c (i + 1))) x)) =
      β.mul ((c 0).add (x.mul (ev n (fun i => c (i + 1)) x)))
    rw [ev_smul x β n (fun i => c (i + 1))]
    exact Q.eq_of_norm (p := ((Q.var 0).mul (Q.var 1)).add ((Q.var 2).mul ((Q.var 0).mul (Q.var 3))))
      (q := (Q.var 0).mul ((Q.var 1).add ((Q.var 2).mul (Q.var 3)))) (by decide)
      (env4 β (c 0) x (ev n (fun i => c (i + 1)) x))

theorem ev_congr (x : EF) : ∀ (n : Nat) {c c' : Nat → EF}, (∀ i, i < n → c i = c' i) → ev n c x = ev n c' x
  | 0, _, _, _ => rfl
  | n + 1, c, c', h => by
    show (c 0).add (x.mul (ev n (fun i => c (i + 1)) x)) = (c' 0).add (x.mul (ev n (fun i => c' (i + 1)) x))
    rw [h 0 (Nat.succ_pos n), ev_congr x n (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

/-- The even and the odd coefficients. -/
def evens (c : Nat → EF) : Nat → EF := fun i => c (2 * i)
def odds (c : Nat → EF) : Nat → EF := fun i => c (2 * i + 1)

theorem split_step (c0 c1 x E O : EF) :
    (c0.add (x.mul (c1.add (x.mul ((E.add (x.mul O))))))) =
      (c0.add ((x.mul x).mul E)).add (x.mul (c1.add ((x.mul x).mul O))) :=
  Q.eq_of_norm (p := (Q.var 0).add ((Q.var 2).mul ((Q.var 1).add ((Q.var 2).mul ((Q.var 3).add ((Q.var 2).mul (Q.var 4)))))))
    (q := ((Q.var 0).add (((Q.var 2).mul (Q.var 2)).mul (Q.var 3))).add
      ((Q.var 2).mul ((Q.var 1).add (((Q.var 2).mul (Q.var 2)).mul (Q.var 4)))))
    (by decide) (env8 c0 c1 x E O EF.zero EF.zero EF.zero)

/-- **`B(X) = E(X²) + X·O(X²)`**. -/
theorem ev_split (x : EF) : ∀ (n : Nat) (c : Nat → EF),
    ev (2 * n) c x = (ev n (evens c) (x.mul x)).add (x.mul (ev n (odds c) (x.mul x)))
  | 0, _ => by
    show EF.zero = EF.zero.add (x.mul EF.zero); rw [EF.mul_zero, EF.add_zero]
  | n + 1, c => by
    have ih := ev_split x n (fun i => c (i + 2))
    have he : evens (fun i => c (i + 2)) = fun i => evens c (i + 1) :=
      funext fun i => by show c (2 * i + 2) = c (2 * (i + 1)); rw [Nat.mul_succ]
    have ho : odds (fun i => c (i + 2)) = fun i => odds c (i + 1) :=
      funext fun i => by show c (2 * i + 1 + 2) = c (2 * (i + 1) + 1); exact congrArg c (by omega)
    rw [he, ho] at ih
    show ev (2 * n + 2) c x = _
    show (c 0).add (x.mul ((c 1).add (x.mul (ev (2 * n) (fun i => c (i + 2)) x)))) =
      ((c 0).add ((x.mul x).mul (ev n (fun i => evens c (i + 1)) (x.mul x)))).add
        (x.mul ((c 1).add ((x.mul x).mul (ev n (fun i => odds c (i + 1)) (x.mul x)))))
    rw [ih]
    exact split_step _ _ _ _ _

-- ---------------------------------------------------------------------------
-- Folding
-- ---------------------------------------------------------------------------

/-- **One fold**: `E + β·O`. -/
def ffold (β : EF) (c : Nat → EF) : Nat → EF := fun i => (evens c i).add (β.mul (odds c i))

theorem ev_ffold (y β : EF) (n : Nat) (c : Nat → EF) :
    ev n (ffold β c) y = (ev n (evens c) y).add (β.mul (ev n (odds c) y)) := by
  unfold ffold
  rw [ev_add, ev_smul]

/-- `2` in the extension. -/
def two : EF := EF.one.add EF.one

theorem two_ne_zero : two ≠ EF.zero := by decide

theorem fold_step (E O x β i2 ix : EF) (h2 : two.mul i2 = EF.one) (hx : (two.mul x).mul ix = EF.one) :
    E.add (β.mul O) = (i2.mul ((E.add (x.mul O)).add (E.add (x.neg.mul O)))).add
      (β.mul (((E.add (x.mul O)).sub (E.add (x.neg.mul O))).mul ix)) := by
  have e1 : (E.add (x.mul O)).add (E.add (x.neg.mul O)) = two.mul E :=
    Q.eq_of_norm (p := ((Q.var 0).add ((Q.var 2).mul (Q.var 1))).add ((Q.var 0).add ((Q.var 2).neg.mul (Q.var 1))))
      (q := (⟨k 2, k 0, k 0, k 0⟩ : Q).mul (Q.var 0)) (by decide) (env3 E O x)
  have e2 : (E.add (x.mul O)).sub (E.add (x.neg.mul O)) = (two.mul x).mul O :=
    Q.eq_of_norm (p := ((Q.var 0).add ((Q.var 2).mul (Q.var 1))).sub ((Q.var 0).add ((Q.var 2).neg.mul (Q.var 1))))
      (q := ((⟨k 2, k 0, k 0, k 0⟩ : Q).mul (Q.var 2)).mul (Q.var 1)) (by decide) (env3 E O x)
  rw [e1, e2, show i2.mul (two.mul E) = E by rw [← EF.mul_assoc, EF.mul_comm i2, h2, EF.one_mul],
    show ((two.mul x).mul O).mul ix = O by rw [EF.mul_assoc, EF.mul_comm O, ← EF.mul_assoc, hx, EF.one_mul]]

theorem neg_sq (x : EF) : x.neg.mul x.neg = x.mul x :=
  Q.eq_of_norm (p := (Q.var 0).neg.mul (Q.var 0).neg) (q := (Q.var 0).mul (Q.var 0)) (by decide)
    (env3 x EF.zero EF.zero)

/-- **The verifier's fold**: the folded polynomial at `x²` from the
    polynomial at `x` and at `-x`, `(B(x) + B(-x))/2 + β (B(x) - B(-x))/(2x)`. -/
theorem fold_formula (x β : EF) (hx : two.mul x ≠ EF.zero) (n : Nat) (c : Nat → EF) :
    ev n (ffold β c) (x.mul x) =
      (two.inv.mul ((ev (2 * n) c x).add (ev (2 * n) c x.neg))).add
        (β.mul (((ev (2 * n) c x).sub (ev (2 * n) c x.neg)).mul (two.mul x).inv)) := by
  rw [ev_ffold, ev_split x n c, ev_split x.neg n c, neg_sq]
  exact fold_step _ _ _ _ _ _ (EF.mul_inv two_ne_zero) (EF.mul_inv hx)

theorem ffold_add (β : EF) (c c' : Nat → EF) :
    ffold β (fun i => (c i).add (c' i)) = fun i => (ffold β c i).add (ffold β c' i) :=
  funext fun i => Q.eq_of_norm
    (p := ((Q.var 0).add (Q.var 1)).add ((Q.var 4).mul ((Q.var 2).add (Q.var 3))))
    (q := ((Q.var 0).add ((Q.var 4).mul (Q.var 2))).add ((Q.var 1).add ((Q.var 4).mul (Q.var 3)))) (by decide)
    (env8 (c (2 * i)) (c' (2 * i)) (c (2 * i + 1)) (c' (2 * i + 1)) β EF.zero EF.zero EF.zero)

-- ---------------------------------------------------------------------------
-- FRI's view
-- ---------------------------------------------------------------------------

/-- **One query's path**: at each of `k` layers the sibling `B_i(-x_i)`,
    `B_i` of `2^(k-i)` coefficients, then on to `B_{i+1} = ffold β_i B_i`
    at `x_i²`. -/
def friPath : Nat → List EF → (Nat → EF) → EF → List EF
  | k + 1, β :: βs, c, x => ev (2 ^ (k + 1)) c x.neg :: friPath k βs (ffold β c) (x.mul x)
  | _, _, _, _ => []

/-- The last layer, after every fold. -/
def friLast : List EF → (Nat → EF) → (Nat → EF)
  | β :: βs, c => friLast βs (ffold β c)
  | [], c => c

/-- **FRI's view**: every query's path and the last layer's first `m`
    coefficients. -/
def friView (k m : Nat) (βs : List EF) (xs : List EF) (c : Nat → EF) : List (List EF) × List EF :=
  (xs.map (friPath k βs c), (List.range m).map (friLast βs c))

theorem friPath_add : ∀ (k : Nat) (βs : List EF) (c c' : Nat → EF) (x : EF),
    friPath k βs (fun i => (c i).add (c' i)) x = List.zipWith EF.add (friPath k βs c x) (friPath k βs c' x)
  | 0, _, _, _, _ => rfl
  | _ + 1, [], _, _, _ => rfl
  | k + 1, β :: βs, c, c', x => by
    show ev (2 ^ (k + 1)) (fun i => (c i).add (c' i)) x.neg ::
        friPath k βs (ffold β (fun i => (c i).add (c' i))) (x.mul x) =
      EF.add (ev (2 ^ (k + 1)) c x.neg) (ev (2 ^ (k + 1)) c' x.neg) ::
        List.zipWith EF.add (friPath k βs (ffold β c) (x.mul x)) (friPath k βs (ffold β c') (x.mul x))
    rw [ev_add, ffold_add, friPath_add k βs]

theorem friLast_add : ∀ (βs : List EF) (c c' : Nat → EF),
    friLast βs (fun i => (c i).add (c' i)) = fun i => (friLast βs c i).add (friLast βs c' i)
  | [], _, _ => rfl
  | β :: βs, c, c' => by
    show friLast βs (ffold β (fun i => (c i).add (c' i))) = _
    rw [ffold_add, friLast_add βs]
    rfl

/-- The sum of two views, entry by entry. -/
def vplus (a b : List (List EF) × List EF) : List (List EF) × List EF :=
  (List.zipWith (List.zipWith EF.add) a.1 b.1, List.zipWith EF.add a.2 b.2)

/-- **FRI's view is linear**: the view of a sum is the sum of the views. -/
theorem friView_add (k m : Nat) (βs xs : List EF) (c c' : Nat → EF) :
    friView k m βs xs (fun i => (c i).add (c' i)) = vplus (friView k m βs xs c) (friView k m βs xs c') := by
  unfold friView vplus
  show _ = (List.zipWith (List.zipWith EF.add) (xs.map (friPath k βs c)) (xs.map (friPath k βs c')),
    List.zipWith EF.add ((List.range m).map (friLast βs c)) ((List.range m).map (friLast βs c')))
  rw [List.zipWith_map, List.zipWith_self, List.zipWith_map, List.zipWith_self, friLast_add]
  congr 1
  exact List.map_congr_left (fun x _ => friPath_add k βs c c' x)

-- ---------------------------------------------------------------------------
-- A mask that cancels hides
-- ---------------------------------------------------------------------------

/-- **A mask that can cancel hides FRI's view**: a mask `U` linear in its
    randomness, and a shift `Δ` of the randomness that leaves the other
    openings `O` alone and turns `W'` into `W` on everything FRI reveals,
    give the views over `W` and `W'` one distribution with the other
    openings. -/
theorem fri_hides_of_cancel {V : Type} {N k m : Nat} {βs xs : List EF} (U : List F → Nat → EF) (O : List F → V)
    (W W' : Nat → EF) (Δ : List F) (hΔ : Δ.length = N)
    (hU : ∀ r : List F, r.length = N → U (vadd r Δ) = fun i => (U r i).add (U Δ i))
    (hO : ∀ r : List F, r.length = N → O (vadd r Δ) = O r)
    (hcancel : friView k m βs xs (fun i => (W' i).add (U Δ i)) = friView k m βs xs W)
    (E : V → List (List EF) × List EF → Bool) :
    vsum N (fun r => if E (O r) (friView k m βs xs (fun i => (W i).add (U r i))) then 1 else 0) =
      vsum N (fun r => if E (O r) (friView k m βs xs (fun i => (W' i).add (U r i))) then 1 else 0) := by
  rw [← vsum_shift N Δ hΔ (fun r => if E (O r) (friView k m βs xs (fun i => (W' i).add (U r i))) then 1 else 0)]
  refine vsum_congr N (fun r hr => ?_)
  show (if E (O r) (friView k m βs xs (fun i => (W i).add (U r i))) = true then 1 else 0) =
    (if E (O (vadd r Δ)) (friView k m βs xs (fun i => (W' i).add (U (vadd r Δ) i))) = true then 1 else 0)
  have e : (fun i => (W' i).add (U (vadd r Δ) i)) = fun i => ((W' i).add (U Δ i)).add (U r i) := by
    rw [hU r hr]
    funext i
    exact Q.eq_of_norm (p := (Q.var 0).add ((Q.var 1).add (Q.var 2)))
      (q := ((Q.var 0).add (Q.var 2)).add (Q.var 1)) (by decide) (env3 (W' i) (U r i) (U Δ i))
  rw [hO r hr, e]
  have h1 : friView k m βs xs (fun i => ((W' i).add (U Δ i)).add (U r i)) =
      friView k m βs xs (fun i => (W i).add (U r i)) :=
    (friView_add k m βs xs (fun i => (W' i).add (U Δ i)) (U r)).trans
      (by rw [hcancel]; exact (friView_add k m βs xs W (U r)).symm)
  rw [h1]

end Circuit
