import Ski.ZK.Comb

/-!
# Counting blinding choices

The prover draws each blinding tuple uniformly from `F^4`.  A probability
over the blinding is a count over `Tup × Tup` (`count2`), `P^4` choices
each, enumerated by base-`P` digits (`Tup.dec`).  A sum does not change
when a bijection reindexes it (`sumTo_perm`), so neither does a count
(`count2_bij`).
-/

namespace Circuit

-- ---------------------------------------------------------------------------
-- Sums are invariant under bijections
-- ---------------------------------------------------------------------------

/-- Changing one term of a sum. -/
theorem sumTo_update (f : Nat → Nat) (k x : Nat) : ∀ n, k < n →
    sumTo n f + x = sumTo n (fun i => if i = k then x else f i) + f k
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    show sumTo n f + f n + x = sumTo n (fun i => if i = k then x else f i) + (if n = k then x else f n) + f k
    rcases Nat.lt_or_ge k n with hk | hk
    · have ih := sumTo_update f k x n hk
      rw [if_neg (by omega)]
      omega
    · have e : k = n := by omega
      subst e
      have hc : sumTo k (fun i => if i = k then x else f i) = sumTo k f :=
        sumTo_congr k (fun i hi => if_neg (by omega))
      rw [if_pos rfl, hc]
      omega

/-- **A sum over `[0, n)` is invariant under a bijection of `[0, n)`.** -/
theorem sumTo_perm (f : Nat → Nat) : ∀ (n : Nat) (σ τ : Nat → Nat), (∀ i, i < n → σ i < n) →
    (∀ i, i < n → τ i < n) → (∀ i, i < n → τ (σ i) = i) → (∀ i, i < n → σ (τ i) = i) →
    sumTo n (fun i => f (σ i)) = sumTo n f
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, σ, τ, hσ, hτ, h1, h2 => by
    let k := τ n
    have hk : k < n + 1 := hτ n (by omega)
    have hσk : σ k = n := h2 n (by omega)
    -- `σ'` sends `k` where `σ` sends `n`
    let σ' : Nat → Nat := fun i => if i = k then σ n else σ i
    let τ' : Nat → Nat := fun j => if j = σ n then k else τ j
    have inj : ∀ i j, i < n + 1 → j < n + 1 → σ i = σ j → i = j := fun i j hi hj e => by
      rw [← h1 i hi, ← h1 j hj, e]
    rcases Nat.lt_or_ge k n with hkn | hkn
    · have hσn : σ n < n := by
        have := hσ n (by omega)
        rcases Nat.lt_or_ge (σ n) n with h | h
        · exact h
        · exfalso; have e : σ n = σ k := by rw [hσk]; omega
          have := inj n k (by omega) hk e; omega
      have hs' : ∀ i, i < n → σ' i < n := fun i hi => by
        show (if i = k then σ n else σ i) < n
        split
        · exact hσn
        · next hik =>
          have := hσ i (by omega)
          rcases Nat.lt_or_ge (σ i) n with h | h
          · exact h
          · exfalso; exact hik (inj i k (by omega) hk (by rw [hσk]; omega))
      have ht' : ∀ j, j < n → τ' j < n := fun j hj => by
        show (if j = σ n then k else τ j) < n
        split
        · exact hkn
        · next hj' =>
          have := hτ j (by omega)
          rcases Nat.lt_or_ge (τ j) n with h | h
          · exact h
          · exfalso
            have e : τ j = n := by omega
            have := h2 j (by omega)
            rw [e] at this; exact hj' this.symm
      have r1 : ∀ i, i < n → τ' (σ' i) = i := fun i hi => by
        show (if (if i = k then σ n else σ i) = σ n then k else τ (if i = k then σ n else σ i)) = i
        rcases Nat.decEq i k with hik | hik
        · rw [if_neg hik]
          rw [if_neg (fun e => hik (by have := inj i n (by omega) (by omega) e; omega))]
          exact h1 i (by omega)
        · rw [if_pos hik, if_pos rfl, hik]
      have r2 : ∀ j, j < n → σ' (τ' j) = j := fun j hj => by
        show (if (if j = σ n then k else τ j) = k then σ n else σ (if j = σ n then k else τ j)) = j
        rcases Nat.decEq j (σ n) with hj' | hj'
        · rw [if_neg hj']
          rw [if_neg (fun e => by have := h2 j (by omega); rw [e, hσk] at this; omega)]
          exact h2 j (by omega)
        · rw [if_pos hj', if_pos rfl, hj']
      have ih := sumTo_perm f n σ' τ' hs' ht' r1 r2
      show sumTo n (fun i => f (σ i)) + f (σ n) = sumTo n f + f n
      have hu := sumTo_update (fun i => f (σ i)) k (f (σ n)) n hkn
      have e : (fun i => if i = k then f (σ n) else f (σ i)) = fun i => f (σ' i) := by
        funext i; show _ = f (if i = k then σ n else σ i); split <;> rfl
      rw [e, ih, hσk] at hu
      omega
    · -- `k = n`: `σ` fixes `n`
      have e : k = n := by omega
      have hσn : σ n = n := by have h' := hσk; rw [e] at h'; exact h'
      have hs' : ∀ i, i < n → σ i < n := fun i hi => by
        have := hσ i (by omega)
        rcases Nat.lt_or_ge (σ i) n with h | h
        · exact h
        · exfalso; have := inj i n (by omega) (by omega) (by rw [hσn]; omega); omega
      have ht' : ∀ j, j < n → τ j < n := fun j hj => by
        have := hτ j (by omega)
        rcases Nat.lt_or_ge (τ j) n with h | h
        · exact h
        · exfalso
          have e2 : τ j = n := by omega
          have := h2 j (by omega); rw [e2, hσn] at this; omega
      have ih := sumTo_perm f n σ τ hs' ht' (fun i hi => h1 i (by omega)) (fun j hj => h2 j (by omega))
      show sumTo n (fun i => f (σ i)) + f (σ n) = sumTo n f + f n
      rw [ih, hσn]

-- ---------------------------------------------------------------------------
-- Tuples, enumerated
-- ---------------------------------------------------------------------------

/-- The number of 4-tuples: `P^4`. -/
def Q4 : Nat := P * (P * (P * P))

namespace Tup

/-- Tuple number `i`, by base-`P` digits. -/
def dec (i : Nat) : Tup := ⟨ofN (i % P), ofN (i / P % P), ofN (i / P / P % P), ofN (i / P / P / P)⟩

/-- A tuple's number. -/
def enc (a : Tup) : Nat := a.t0.val + P * (a.t1.val + P * (a.t2.val + P * a.t3.val))

theorem enc_lt (a : Tup) : enc a < Q4 := by
  have h0 := a.t0.isLt; have h1 := a.t1.isLt; have h2 := a.t2.isLt; have h3 := a.t3.isLt
  unfold enc Q4
  generalize a.t0.val = x0 at *; generalize a.t1.val = x1 at *
  generalize a.t2.val = x2 at *; generalize a.t3.val = x3 at *
  have e3 : P * x3 ≤ P * (P - 1) := Nat.mul_le_mul_left P (by omega)
  have e2 : x2 + P * x3 < P * P := by
    have : P * (P - 1) + P = P * P := by rw [← Nat.mul_succ]; congr 1
    omega
  have e2' : P * (x2 + P * x3) ≤ P * (P * P - 1) := Nat.mul_le_mul_left P (by omega)
  have e1 : x1 + P * (x2 + P * x3) < P * (P * P) := by
    have : P * (P * P - 1) + P = P * (P * P) := by
      rw [← Nat.mul_succ]; congr 1
    omega
  have e1' : P * (x1 + P * (x2 + P * x3)) ≤ P * (P * (P * P) - 1) := Nat.mul_le_mul_left P (by omega)
  have : P * (P * (P * P) - 1) + P = P * (P * (P * P)) := by
    rw [← Nat.mul_succ]; congr 1
  omega

theorem digit (x y : Nat) (hx : x < P) : (x + P * y) % P = x ∧ (x + P * y) / P = y := by
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  · rw [Nat.add_mul_div_left _ _ P_pos, Nat.div_eq_of_lt hx, Nat.zero_add]

theorem dec_enc (a : Tup) : dec (enc a) = a := by
  unfold dec enc
  obtain ⟨m0, d0⟩ := digit a.t0.val (a.t1.val + P * (a.t2.val + P * a.t3.val)) a.t0.isLt
  obtain ⟨m1, d1⟩ := digit a.t1.val (a.t2.val + P * a.t3.val) a.t1.isLt
  obtain ⟨m2, d2⟩ := digit a.t2.val a.t3.val a.t2.isLt
  rw [m0, d0, m1, d1, m2, d2, ofN_val, ofN_val, ofN_val, ofN_val]

theorem div_lt' {x m n : Nat} (h : x < m * n) : x / m < n := by
  rcases Nat.lt_or_ge (x / m) n with h' | h'
  · exact h'
  · exfalso
    have e1 := Nat.mul_le_mul_left m h'
    have e2 := Nat.mul_div_le x m
    omega

theorem enc_dec {i : Nat} (hi : i < Q4) : enc (dec i) = i := by
  unfold enc dec
  have hP := P_pos
  have h3 : i / P / P / P < P := by
    unfold Q4 at hi
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    exact div_lt' (by rw [Nat.mul_assoc, Nat.mul_assoc]; exact hi)
  rw [val_ofN (Nat.mod_lt _ hP), val_ofN (Nat.mod_lt _ hP), val_ofN (Nat.mod_lt _ hP), val_ofN h3]
  have a3 := Nat.mod_add_div (i / P / P) P
  have a2 := Nat.mod_add_div (i / P) P
  have a1 := Nat.mod_add_div i P
  rw [a3, a2, a1]

end Tup

/-- **How many blinding pairs satisfy `p`**: out of `P^4 · P^4`. -/
def count2 (p : Tup → Tup → Bool) : Nat :=
  sumTo Q4 fun i => sumTo Q4 fun j => if p (Tup.dec i) (Tup.dec j) then 1 else 0

/-- Reindexing a sum over tuples by a bijection of tuples. -/
theorem sumTo_tup (g : Tup → Nat) (τ ρ : Tup → Tup) (hl : ∀ a, ρ (τ a) = a) (hr : ∀ a, τ (ρ a) = a) :
    sumTo Q4 (fun i => g (τ (Tup.dec i))) = sumTo Q4 (fun i => g (Tup.dec i)) := by
  have e : (fun i => g (τ (Tup.dec i))) = fun i => (fun j => g (Tup.dec j)) (Tup.enc (τ (Tup.dec i))) := by
    funext i; show _ = g (Tup.dec (Tup.enc _)); rw [Tup.dec_enc]
  rw [e]
  exact sumTo_perm (fun j => g (Tup.dec j)) Q4 (fun i => Tup.enc (τ (Tup.dec i))) (fun i => Tup.enc (ρ (Tup.dec i)))
    (fun _ _ => Tup.enc_lt _) (fun _ _ => Tup.enc_lt _)
    (fun i hi => by show Tup.enc (ρ (Tup.dec (Tup.enc _))) = i; rw [Tup.dec_enc, hl, Tup.enc_dec hi])
    (fun i hi => by show Tup.enc (τ (Tup.dec (Tup.enc _))) = i; rw [Tup.dec_enc, hr, Tup.enc_dec hi])

/-- **A count does not change when bijections reindex the blinding.** -/
theorem count2_bij (p : Tup → Tup → Bool) {τ1 ρ1 τ2 ρ2 : Tup → Tup} (hl1 : ∀ a, ρ1 (τ1 a) = a)
    (hr1 : ∀ a, τ1 (ρ1 a) = a) (hl2 : ∀ a, ρ2 (τ2 a) = a) (hr2 : ∀ a, τ2 (ρ2 a) = a) :
    count2 (fun a b => p (τ1 a) (τ2 b)) = count2 p := by
  unfold count2
  rw [sumTo_congr Q4 (fun i _ => sumTo_tup (fun b => if p (τ1 (Tup.dec i)) b then 1 else 0) τ2 ρ2 hl2 hr2)]
  exact sumTo_tup (fun a => sumTo Q4 fun j => if p a (Tup.dec j) then 1 else 0) τ1 ρ1 hl1 hr1

end Circuit
