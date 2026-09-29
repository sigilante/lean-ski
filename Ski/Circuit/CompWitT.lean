import Ski.Circuit.CompTable

/-!
# The honest witness table

For a memory whose bit cells are `K` or `A 0 1` and whose region is well
formed, the witness table the prover builds (`witTable`): per private
address, its cell's kind flag, its fields, and the 24-bit decompositions
the range checks read.  **`wit_sat`**: it satisfies the witness AIR.
-/

namespace Circuit

open B Compose CompM Wit

/-- Bits from column `base` reassemble their number, below `2^24`. -/
theorem foldBits_val {T : Table} {r : Nat} (hr : r < T.h) (base n : Nat)
    (hb : ∀ i, i < RANGE_BITS → T.main r (base + i) = ofN ((n / 2 ^ i) % 2)) (hn : n < 2 ^ 24) :
    ((List.range RANGE_BITS).foldl (fun v i => E.add v (E.mul (col (base + i)) (c (2 ^ i)))) zero).eval
      (T.env r) = ofN n := by
  have step : ∀ m, m ≤ RANGE_BITS →
      ((List.range m).foldl (fun v i => E.add v (E.mul (col (base + i)) (c (2 ^ i)))) zero).eval
        (T.env r) = ofN (n % 2 ^ m) := by
    intro m
    induction m with
    | zero => intro _; show ofN 0 = ofN (n % 1); rw [Nat.mod_one]
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      show E.eval (T.env r) (List.foldl _ zero (List.range m)) + T.env r (.main 0 (base + m)) * ofN (2 ^ m) = _
      rw [ih (Nat.le_of_succ_le hm), env_main0 hr, hb m hm, ← ofN_mul, ← ofN_add, mod_two_pow_succ, Nat.mul_comm]
  rw [step RANGE_BITS (Nat.le_refl _), Nat.mod_eq_of_lt (show n < 2 ^ RANGE_BITS from hn)]

/-- A witness row's kind flag: `S`, `K`, `I`, an application. -/
def wkind : Cell → Nat
  | .S => 0
  | .K => 1
  | .I => 2
  | .app _ _ => 3
  | _ => 4

/-- A witness row's numbers: the fields and their gaps below the address. -/
def wnums (a : Nat) (c : Cell) (k : Nat) : Nat :=
  match c with
  | .app x y => if k = 0 then x else if k = 1 then a - x - 1 else if k = 2 then y else a - y - 1
  | _ => 0

/-- **The honest witness row** `q`: the cell at private address `3 + q`,
    for `q < N + W`; zeros below. -/
def witCol (A : List Cell) (N W q col : Nat) : F :=
  if q < N + W then
    let a := 3 + q
    let cell := A.getD a .nil
    if col < 4 then (if col = wkind cell then 1 else 0)
    else if col = WT_A then ofN (cellFields cell).1
    else if col = WT_B then ofN (cellFields cell).2
    else if col < WT_BLIND then
      ofN ((wnums a cell ((col - WT_BITS) / RANGE_BITS) / 2 ^ ((col - WT_BITS) % RANGE_BITS)) % 2)
    else 0
  else 0

def witTable (A : List Cell) (N W : Nat) : Table :=
  ⟨(witRows N W).length, fun q col => witCol A N W q col, fun q j => ((witRows N W).getD q []).getD j 0⟩

theorem witRows_pad {N W q : Nat} (hq : N + W ≤ q) (hl : q < (witRows N W).length) :
    (witRows N W).getD q [] = [ofN 0, ofN 0, ofN 0] := by
  unfold witRows at *
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
  simp only [List.length_append, List.length_map, List.length_range, List.length_replicate] at hl ⊢
  rw [if_pos (by omega)]
  rfl

section

variable {A : List Cell} {N W : Nat}
  (hbits : ∀ i, i < N → A.getD (3 + i) .nil = .K ∨ A.getD (3 + i) .nil = .app 0 1)
  (hreg : ∀ i, i < W → cellOK (3 + N + i) (A.getD (3 + N + i) .nil) = true)
  (hsmall : 3 + N + W ≤ 2 ^ 24)

theorem witT_env {q : Nat} (hq : q < (witTable A N W).h) (c : Nat) :
    (col c).eval ((witTable A N W).env q) = witCol A N W q c := by
  show (witTable A N W).main ((q + 0) % _) c = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl

theorem witT_penv {q : Nat} (hq : q < (witTable A N W).h) (j : Nat) :
    (prec j).eval ((witTable A N W).env q) = ((witRows N W).getD q []).getD j 0 := by
  show (witTable A N W).pre ((q + 0) % _) j = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl

include hbits hreg in
/-- An active witness row's cell: a bit is `K` or `A 0 1`; every cell is
    well formed. -/
theorem wit_cell {q : Nat} (hq : q < N + W) :
    cellOK (3 + q) (A.getD (3 + q) .nil) = true ∧
      (q < N → A.getD (3 + q) .nil = .K ∨ A.getD (3 + q) .nil = .app 0 1) := by
  refine ⟨?_, fun hN => hbits q hN⟩
  rcases Nat.lt_or_ge q N with hN | hN
  · rcases hbits q hN with h | h <;> rw [h]
    · rfl
    · show (decide (0 < 3 + q) && decide (1 < 3 + q)) = true
      rw [decide_eq_true (by omega), decide_eq_true (by omega)]; rfl
  · have := hreg (q - N) (by omega)
    rwa [show 3 + N + (q - N) = 3 + q by omega] at this

/-- An active row's columns. -/
theorem witCol_active {q : Nat} (hq : q < N + W) :
    (∀ i, i < 4 → witCol A N W q i = if i = wkind (A.getD (3 + q) .nil) then 1 else 0) ∧
    witCol A N W q WT_A = ofN (cellFields (A.getD (3 + q) .nil)).1 ∧
    witCol A N W q WT_B = ofN (cellFields (A.getD (3 + q) .nil)).2 ∧
    (∀ k, k < 4 → ∀ b, b < RANGE_BITS → witCol A N W q (WT_BITS + k * RANGE_BITS + b) =
      ofN ((wnums (3 + q) (A.getD (3 + q) .nil) k / 2 ^ b) % 2)) ∧
    witCol A N W q (WT_BLIND + 4) = 0 := by
  have c1 : WT_A = 4 := rfl
  have c2 : WT_B = 5 := rfl
  have c3 : WT_BITS = 6 := rfl
  have c4 : WT_BLIND = 102 := rfl
  have c5 : RANGE_BITS = 24 := rfl
  refine ⟨fun i hi => ?_, ?_, ?_, fun k hk b hb => ?_, ?_⟩
  · unfold witCol; rw [if_pos hq]; simp only; rw [if_pos hi]
  · unfold witCol; rw [if_pos hq]; simp only; rw [if_neg (by omega), if_pos trivial]
  · unfold witCol; rw [if_pos hq]; simp only; rw [if_neg (by omega), if_neg (by omega), if_pos trivial]
  · have hkr : k * RANGE_BITS ≤ 72 := by rw [c5]; omega
    unfold witCol; rw [if_pos hq]; simp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have e1 : (WT_BITS + k * RANGE_BITS + b - WT_BITS) / RANGE_BITS = k := by rw [c5] at *; omega
    have e2 : (WT_BITS + k * RANGE_BITS + b - WT_BITS) % RANGE_BITS = b := by rw [c5] at *; omega
    rw [e1, e2]
  · unfold witCol; rw [if_pos hq]; simp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem witCol_inactive {q : Nat} (hq : N + W ≤ q) (c : Nat) : witCol A N W q c = 0 := by
  unfold witCol; rw [if_neg (by omega)]

include hbits hreg hsmall in
/-- An active row's numbers, reassembled from its bits. -/
theorem wit_nums {q : Nat} (hq : q < N + W) (hqh : q < (witTable A N W).h) {k : Nat} (hk : k < 4) :
    (wnum k).eval ((witTable A N W).env q) = ofN (wnums (3 + q) (A.getD (3 + q) .nil) k) := by
  obtain ⟨hok, _⟩ := wit_cell hbits hreg hq
  have hlt : wnums (3 + q) (A.getD (3 + q) .nil) k < 2 ^ 24 := by
    generalize A.getD (3 + q) .nil = cell at hok ⊢
    cases cell with
    | app x y =>
      simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hx, hy⟩ := hok
      have hq3 : 3 + q ≤ 2 ^ 24 := by omega
      unfold wnums
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
      · exact Nat.lt_of_lt_of_le hx hq3
      · show 3 + q - x - 1 < 2 ^ 24; omega
      · exact Nat.lt_of_lt_of_le hy hq3
      · show 3 + q - y - 1 < 2 ^ 24; omega
    | _ => show 0 < 2 ^ 24; decide
  unfold wnum
  rw [show WT_BITS + k * RANGE_BITS = WT_BITS + k * RANGE_BITS from rfl]
  have := foldBits_val hqh (WT_BITS + k * RANGE_BITS) (wnums (3 + q) (A.getD (3 + q) .nil) k)
    (fun b hb => by
      show witCol A N W q (WT_BITS + k * RANGE_BITS + b) = _
      exact (witCol_active hq).2.2.2.1 k hk b hb) hlt
  simpa only [Nat.add_assoc] using this

theorem cellOK_cases {i : Nat} {c : Cell} (h : cellOK i c = true) :
    c = .S ∨ c = .K ∨ c = .I ∨ ∃ x y, c = .app x y ∧ x < i ∧ y < i := by
  cases c with
  | S => exact .inl rfl
  | K => exact .inr (.inl rfl)
  | I => exact .inr (.inr (.inl rfl))
  | app x y =>
    simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .inr (.inr (.inr ⟨x, y, rfl, h.1, h.2⟩))
  | nil => simp [cellOK] at h
  | cons _ _ => simp [cellOK] at h
  | atom _ => simp [cellOK] at h

theorem wkind_lt {i : Nat} {c : Cell} (h : cellOK i c = true) : wkind c < 4 := by
  rcases cellOK_cases h with rfl | rfl | rfl | ⟨x, y, rfl, _, _⟩
  · decide
  · decide
  · decide
  · show 3 < 4; decide

theorem flags_sum : ∀ k, k < 4 → ((((if 0 = k then (1 : F) else 0) + (if 1 = k then 1 else 0)) +
    (if 2 = k then 1 else 0)) + (if 3 = k then 1 else 0)) = 1
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide

include hbits hreg hsmall in
/-- **The honest witness table satisfies the witness AIR.** -/
theorem wit_sat : Sat (witAir N W) (witTable A N W) := by
  refine ⟨show 0 < (witRows N W).length by unfold witRows; simp; omega, fun c hc q (hq : q < (witTable A N W).h) => ?_⟩
  have ev := witT_env (A := A) hq
  have pv := witT_penv (A := A) hq
  simp only [witAir, witCons, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hc
  by_cases hact : q < N + W
  · -- an active row
    obtain ⟨hok, hbit⟩ := wit_cell hbits hreg hact
    obtain ⟨vf, va, vb, vbits, vbl⟩ := witCol_active (A := A) hact
    have hpre := witRows_get (N := N) (W := W) hact
    have nums := fun (k : Nat) (hk : k < 4) => wit_nums hbits hreg hsmall hact hq hk
    have p0 : (prec 0).eval ((witTable A N W).env q) = ofN (3 + q) := by rw [pv, hpre]; rfl
    have p1 : (prec 1).eval ((witTable A N W).env q) = ofN 1 := by rw [pv, hpre]; rfl
    have p2 : (prec 2).eval ((witTable A N W).env q) = ofN (if q < N then 1 else 0) := by rw [pv, hpre]; rfl
    have f0 := vf 0 (by decide)
    have f1 := vf 1 (by decide)
    have f2 := vf 2 (by decide)
    have f3 := vf 3 (by decide)
    rcases hc with (((⟨i, hi, rfl⟩ | (rfl | rfl | rfl)) | ⟨i, hi, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))
    · simp only [B.bool, E.eval, ev, B.one, B.c, ofN_one, vf i hi]
      split <;> decide
    · simp only [B.eq, E.eval, ev, p1, f0, f1, f2, f3]
      rw [flags_sum _ (wkind_lt hok), ofN_one]; exact sub_self' _
    · simp only [E.eval, ev, B.one, B.c, ofN_one, f3, va]
      generalize A.getD (3 + q) .nil = cell at hok ⊢
      rcases cellOK_cases hok with rfl | rfl | rfl | ⟨x, y, rfl, _, _⟩ <;> simp only [wkind, cellFields]
      · decide
      · decide
      · decide
      · rw [if_pos trivial, sub_self', zero_mul']
    · simp only [E.eval, ev, B.one, B.c, ofN_one, f3, vb]
      generalize A.getD (3 + q) .nil = cell at hok ⊢
      rcases cellOK_cases hok with rfl | rfl | rfl | ⟨x, y, rfl, _, _⟩ <;> simp only [wkind, cellFields]
      · decide
      · decide
      · decide
      · rw [if_pos trivial, sub_self', zero_mul']
    · -- a number's bit
      have c5 : RANGE_BITS = 24 := rfl
      have hk : i / RANGE_BITS < 4 := by rw [c5]; omega
      have e : WT_BITS + i = WT_BITS + i / RANGE_BITS * RANGE_BITS + i % RANGE_BITS := by
        rw [c5]; omega
      simp only [B.bool, E.eval, ev, B.one, B.c, ofN_one]
      rw [e, vbits _ hk _ (Nat.mod_lt _ (by decide))]
      rcases Nat.mod_two_eq_zero_or_one (wnums (3 + q) (A.getD (3 + q) .nil) (i / RANGE_BITS) / 2 ^ (i % RANGE_BITS))
        with h | h <;> rw [h] <;> decide
    · -- `A`'s first pointer is its number
      simp only [E.eval, ev, f3, va, nums 0 (by decide)]
      generalize A.getD (3 + q) .nil = cell at hok ⊢
      rcases cellOK_cases hok with rfl | rfl | rfl | ⟨x, y, rfl, _, _⟩
      · rw [if_neg (by decide), zero_mul']
      · rw [if_neg (by decide), zero_mul']
      · rw [if_neg (by decide), zero_mul']
      · rw [if_pos (show 3 = wkind (Cell.app x y) from rfl)]
        exact (by rw [sub_self', mul_zero'] : (1 : F) * (ofN x - ofN x) = 0)
    · -- and lies below the address
      simp only [E.eval, ev, f3, va, p0, B.one, B.c, ofN_one, nums 1 (by decide)]
      generalize A.getD (3 + q) .nil = cell at hok ⊢
      rcases cellOK_cases hok with rfl | rfl | rfl | ⟨x, y, rfl, hx, _⟩
      · rw [if_neg (by decide), zero_mul']
      · rw [if_neg (by decide), zero_mul']
      · rw [if_neg (by decide), zero_mul']
      · rw [if_pos (show 3 = wkind (Cell.app x y) from rfl), one_mul']
        show ofN (3 + q) - ofN x - 1 - ofN (3 + q - x - 1) = 0
        have e : ofN (3 + q) = ofN (3 + q - x - 1) + ofN x + 1 := by
          rw [← ofN_one, ← ofN_add, ← ofN_add]; congr 1; omega
        rw [e]; exact range_identity _ _
    · simp only [E.eval, ev, f3, vb, nums 2 (by decide)]
      generalize A.getD (3 + q) .nil = cell at hok ⊢
      rcases cellOK_cases hok with rfl | rfl | rfl | ⟨x, y, rfl, _, _⟩
      · rw [if_neg (by decide), zero_mul']
      · rw [if_neg (by decide), zero_mul']
      · rw [if_neg (by decide), zero_mul']
      · rw [if_pos (show 3 = wkind (Cell.app x y) from rfl)]
        exact (by rw [sub_self', mul_zero'] : (1 : F) * (ofN y - ofN y) = 0)
    · simp only [E.eval, ev, f3, vb, p0, B.one, B.c, ofN_one, nums 3 (by decide)]
      generalize A.getD (3 + q) .nil = cell at hok ⊢
      rcases cellOK_cases hok with rfl | rfl | rfl | ⟨x, y, rfl, _, hy⟩
      · rw [if_neg (by decide), zero_mul']
      · rw [if_neg (by decide), zero_mul']
      · rw [if_neg (by decide), zero_mul']
      · rw [if_pos (show 3 = wkind (Cell.app x y) from rfl), one_mul']
        show ofN (3 + q) - ofN y - 1 - ofN (3 + q - y - 1) = 0
        have e : ofN (3 + q) = ofN (3 + q - y - 1) + ofN y + 1 := by
          rw [← ofN_one, ← ofN_add, ← ofN_add]; congr 1; omega
        rw [e]; exact range_identity _ _
    all_goals
      simp only [E.eval, ev, p2, f0, f2, f3, va, vb, B.bool, B.one, B.c, ofN_one, vbl]
      first
        | exact zero_mul' _
        | (by_cases hN : q < N
           · rw [if_pos hN]
             rcases hbit hN with h | h <;> rw [h] <;> decide
           · rw [if_neg hN]
             first | exact zero_mul' _ | decide)
  · -- an inactive row: all zero
    have hpre := witRows_pad (N := N) (W := W) (by omega) hq
    have z : ∀ c, (col c).eval ((witTable A N W).env q) = 0 := fun c => by rw [ev, witCol_inactive (by omega)]
    have zp : ∀ j, (prec j).eval ((witTable A N W).env q) = 0 := fun j => by
      rw [pv, hpre]
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | h
      · rfl
      · rfl
      · rfl
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show [ofN 0, ofN 0, ofN 0].length ≤ j by simp; omega)]; rfl
    rcases hc with (((⟨i, hi, rfl⟩ | (rfl | rfl | rfl)) | ⟨i, hi, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))
    all_goals simp only [B.bool, B.eq, E.eval, z, zp, B.one, B.c, ofN_one, zero_mul', mul_zero', sub_self']
    all_goals decide

end

end Circuit
