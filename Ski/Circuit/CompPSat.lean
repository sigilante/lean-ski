import Ski.Circuit.CompPComplete
import Ski.Circuit.CompWitT

/-!
# The honest tables of the circuit with the Poseidon2 jet satisfy their AIRs

`Ski/Circuit/CompPComplete.lean` proves that the honest tables balance;
here each satisfies its AIR's constraints (`Sat`), table by table, but the
CPU's (`Ski/Circuit/CompPCpuSat.lean`):

- the witness table (`witP_sat`): rows below `N + W` read as the composed
  circuit's witness table, which `wit_sat` covers, and the padding rows
  are zero;
- P2IN (`pin_sat`) and P2OUT (`pout_sat`): each row is `pinRow` or
  `poutRow` of a call's bits, or zero.  P2OUT's canonical check holds since
  the permutation's outputs lie below `p` (`P2Air.permute_lt`);
- the Poseidon2 table (`p2_sat`): a call's row and the padding row are
  `traceAll` of their inputs, whose rounds meet each constraint
  (`gen_zero`), the converse of `P2Air.gen_ok`;
- the public level table, which has no constraints (`idx_sat`, in
  `Ski/Circuit/CompPCompleteFinal.lean`, which assembles the tables).
-/

namespace Circuit

open B Air Compose CompM Mach

-- ---------------------------------------------------------------------------
-- Rows and constraints
-- ---------------------------------------------------------------------------

/-- The current row's atoms: its main and preprocessed columns. -/
def curAtom : Atom → Bool
  | .main 0 _ => true
  | .pre 0 _ => true
  | _ => false

/-- Two environments that agree on the current row's atoms evaluate a
    constraint reading only them alike. -/
theorem eval_cur {ρ ρ' : Atom → F} (h : ∀ a, curAtom a = true → ρ a = ρ' a) {e : E}
    (he : e.onlyAtoms curAtom = true) : e.eval ρ = e.eval ρ' :=
  E.eval_congr h e he

theorem env_pre0 {T : Table} {q : Nat} (hq : q < T.h) (j : Nat) : T.env q (.pre 0 j) = T.pre q j := by
  show T.pre ((q + 0) % T.h) j = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hq]

-- ---------------------------------------------------------------------------
-- The witness table
-- ---------------------------------------------------------------------------

theorem witCons_cur : witCons.all (fun e => e.onlyAtoms curAtom) = true := by decide

theorem witCons_zero : witCons.all (fun e => decide (e.eval (fun _ => 0) = 0)) = true := by decide

section

variable {A : List Cell} {N W : Nat}
  (hbits : ∀ i, i < N → A.getD (3 + i) .nil = .K ∨ A.getD (3 + i) .nil = .app 0 1)
  (hreg : ∀ i, i < W → Wit.cellOK (3 + N + i) (A.getD (3 + N + i) .nil) = true)
  (hsmall : 3 + N + W ≤ 2 ^ 24)

include hbits hreg hsmall in
/-- **The honest witness table satisfies its AIR**: below `N + W` its rows
    read as the composed circuit's witness table's (`wit_sat`); the padding
    rows are zero. -/
theorem witP_sat : Sat (witAirP N W) (witTableP A N W) := by
  have hl := witRowsP_length N W
  refine ⟨show 0 < (witRowsP N W).length by
    unfold witRowsP; simp only [List.length_append, List.length_replicate]
    have := pow2From_ge 64 (2 ^ 9) ((List.range N).map (fun i => [ofN (3 + i), ofN 1, ofN 1]) ++
      (List.range W).map (fun i => [ofN (3 + N + i), ofN 1, ofN 0])).length
    simp only [List.length_append] at this
    unfold pow2Min
    omega, fun c hc q (hq : q < (witRowsP N W).length) => ?_⟩
  have hcur := List.all_eq_true.1 witCons_cur c hc
  by_cases hact : q < N + W
  · -- the composed witness table's row
    have hG := wit_sat (a0 := 3) (A := A) (N := N) (W := W) (fun _ => by decide) hbits hreg hsmall
    have hqG : q < (witTableG 3 A N W).h := Nat.lt_of_lt_of_le hact (witRowsG_length 3 N W)
    rw [← hG.2 c hc q hqG]
    refine eval_cur (fun a ha => ?_) hcur
    match a, ha with
    | .main 0 j, _ =>
      rw [env_main0 hq, env_main0 hqG]; rfl
    | .pre 0 j, _ =>
      rw [env_pre0 hq, env_pre0 hqG]
      show ((witRowsP N W).getD q []).getD j 0 = ((witRowsG 3 N W).getD q []).getD j 0
      rw [witRowsP_get hact, witRowsG_get hact]
  · -- a padding row: zero
    have z := of_decide_eq_true (List.all_eq_true.1 witCons_zero c hc)
    rw [← z]
    refine eval_cur (fun a ha => ?_) hcur
    match a, ha with
    | .main 0 j, _ =>
      rw [env_main0 hq]
      exact witCol_inactive (by omega) j
    | .pre 0 j, _ =>
      rw [env_pre0 hq]
      show ((witRowsP N W).getD q []).getD j 0 = 0
      rw [witRowsP_pad (by omega) hq]
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | h
      · rfl
      · rfl
      · rfl
      · simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (show [ofN 0, ofN 0, ofN 0].length ≤ j by simp; omega)]
        rfl

end

-- ---------------------------------------------------------------------------
-- Tables of rows
-- ---------------------------------------------------------------------------

/-- **A table of rows satisfies an AIR reading only the current row** when
    every row, and the zero row its padding reads as, satisfies each
    constraint. -/
theorem sat_ofRows {A : AirD} {rows : List (List F)} {H : Nat} (hH : 0 < H)
    (hcur : A.cons.all (fun e => e.onlyAtoms curAtom) = true)
    (hrow : ∀ rw ∈ rows, ∀ c ∈ A.cons, c.eval (envOf rw) = 0)
    (hz : ∀ c ∈ A.cons, c.eval (envOf []) = 0) :
    Sat A ⟨H, ofRows rows, fun _ _ => 0⟩ := by
  refine ⟨hH, fun c hc q (hq : q < H) => ?_⟩
  have ag : ∀ a, curAtom a = true → (Table.env ⟨H, ofRows rows, fun _ _ => 0⟩ q) a = envOf (rows.getD q []) a := by
    intro a ha
    match a, ha with
    | .main 0 j, _ =>
      show ofRows rows ((q + 0) % H) j = _
      rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
    | .pre 0 j, _ => rfl
  rw [eval_cur ag (List.all_eq_true.1 hcur c hc)]
  rcases Nat.lt_or_ge q rows.length with hl | hl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
    exact hrow _ (List.getElem_mem hl) c hc
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl, Option.getD_none]
    exact hz c hc

theorem bF_bool (b : Bool) : bF b * (bF b - 1) = 0 := by cases b <;> decide

theorem bF_toNat (b : Bool) : ofN b.toNat = bF b := by cases b <;> rfl

-- ---------------------------------------------------------------------------
-- P2IN
-- ---------------------------------------------------------------------------

theorem p2in_cur : p2inAir.cons.all (fun e => e.onlyAtoms curAtom) = true := by decide

theorem p2in_zero : ∀ c ∈ p2inAir.cons, c.eval (envOf []) = 0 := by
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.1 (show p2inAir.cons.all (fun e => decide (e.eval (envOf []) = 0)) = true
    by decide) c hc)

theorem sub_succ_add_one (a : F) : (a - (a + 1)) + 1 = 0 :=
  E.eval_eq_of_norm (e := .add (.sub (.atom (.main 0 0)) (.add (.atom (.main 0 0)) (.const 1))) (.const 1))
    (e' := .const 0) (by decide) (fun | .main 0 0 => a | _ => 0)

/-- **A P2IN row satisfies P2IN's constraints**: on the stack, when the
    inputs' cells reach down to `s₁ - 495`. -/
theorem pinRow_cons (ctr : Nat) (bs : List Bool) (stk : Bool) (s1 rest l : Nat) (hl0 : l < P2_BITS)
    (hs : stk = true → l + 1 < P2_BITS → l + 1 ≤ s1) :
    ∀ c ∈ p2inAir.cons, c.eval (envOf (pinRow ctr bs stk s1 rest l)) = 0 := by
  intro c hc
  simp only [p2inAir, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- the activity is a bit
    show (1 : F) * (1 - ofN 1) = 0
    decide
  · -- the bit is a bit
    exact bF_bool _
  · -- the value adds the bit's power
    show ofN (accN bs l + 2 ^ (l % 31) * (bs.getD l false).toNat) -
      (ofN (accN bs l) + ofN (2 ^ (l % 31)) * bF (bs.getD l false)) = 0
    rw [ofN_add, ofN_mul, bF_toNat, sub_self']
  · -- the next accumulator restarts after an element's last bit
    show (if l % 31 = 30 then 0 else ofN (accN bs l + 2 ^ (l % 31) * (bs.getD l false).toNat)) -
      ((ofN 1 - bF (decide (l % 31 = 30))) * ofN (accN bs l + 2 ^ (l % 31) * (bs.getD l false).toNat)) = 0
    by_cases h : l % 31 = 30
    · rw [if_pos h, decide_eq_true h]; show (0 : F) - ((ofN 1 - 1) * _) = 0
      rw [show (ofN 1 - 1 : F) = 0 by decide, zero_mul']; decide
    · rw [if_neg h, decide_eq_false h]; show _ - ((ofN 1 - 0) * _) = (0 : F)
      rw [show (ofN 1 - 0 : F) = 1 by decide, one_mul', sub_self']
  · -- the element's message fires at its last bit
    show bF (decide (l % 31 = 30)) - (1 * bF (decide (l % 31 = 30))) = 0
    rw [one_mul', sub_self']
  · -- `ca`
    show bF (!stk) - (1 * (ofN 1 - bF stk)) = 0
    cases stk <;> decide
  · -- `sa`
    show bF stk - (1 * bF stk) = 0
    cases stk <;> decide
  · -- on the comb the stack pointer passes along
    show (ofN 1 - bF stk) * (ofN (if stk then spnAt s1 rest l else rest) -
      ofN (if stk then spAt s1 l else rest)) = 0
    cases stk
    · show (ofN 1 - 0) * (ofN rest - ofN rest) = (0 : F)
      rw [sub_self']; exact mul_zero' _
    · show (ofN 1 - 1) * _ = (0 : F)
      rw [show (ofN 1 - 1 : F) = 0 by decide, zero_mul']
  · -- the read's address
    cases stk
    · show ofN (l + 3) - (0 * ofN rest + 1 * (ofN l + ofN 3)) = (0 : F)
      rw [zero_mul', zero_add', one_mul', ← ofN_add, sub_self']
    · show ofN (spAt s1 l) - (1 * ofN (spAt s1 l) + 0 * (ofN l + ofN 3)) = (0 : F)
      rw [zero_mul', add_zero', one_mul', sub_self']
  · -- the read's tag
    cases stk
    · show ofN (3 - 2 * (bs.getD l false).toNat) - (0 * ofN 5 + 1 * (ofN 3 - bF (bs.getD l false) * ofN 2)) = (0 : F)
      rw [zero_mul', zero_add', one_mul']
      cases bs.getD l false <;> decide
    · show (5 : F) - (1 * ofN 5 + 0 * (ofN 3 - bF (bs.getD l false) * ofN 2)) = 0
      rw [zero_mul', add_zero', one_mul']; decide
  · -- the read's first field
    cases stk
    · show (0 : F) - 0 * (ofN 2 - bF (bs.getD l false) * ofN 2) = 0
      rw [zero_mul']; decide
    · show ofN (2 - 2 * (bs.getD l false).toNat) - 1 * (ofN 2 - bF (bs.getD l false) * ofN 2) = (0 : F)
      rw [one_mul']
      cases bs.getD l false <;> decide
  · -- the read's second field
    cases stk
    · show ofN (1 - (bs.getD l false).toNat) - (0 * ofN rest + 1 * (ofN 1 - bF (bs.getD l false))) = (0 : F)
      rw [zero_mul', zero_add', one_mul']
      cases bs.getD l false <;> decide
    · show ofN (spnAt s1 rest l) - (1 * ofN (spnAt s1 rest l) + 0 * (ofN 1 - bF (bs.getD l false))) = (0 : F)
      rw [zero_mul', add_zero', one_mul', sub_self']
  · -- `sl`
    show bF (stk && !decide (l = P2_BITS - 1)) - (bF stk * (ofN 1 - bF (decide (l = P2_BITS - 1)))) = 0
    cases stk <;> by_cases hl : l = P2_BITS - 1
    · rw [decide_eq_true hl]; decide
    · rw [decide_eq_false hl]; decide
    · rw [decide_eq_true hl]; decide
    · rw [decide_eq_false hl]; decide
  · -- on the stack the inputs are consecutive cells
    show bF (stk && !decide (l = P2_BITS - 1)) *
      ((ofN (if stk then spnAt s1 rest l else rest) - ofN (if stk then spAt s1 l else rest)) + ofN 1) = (0 : F)
    cases stk
    · show (0 : F) * _ = 0; exact zero_mul' _
    · by_cases hl : l = P2_BITS - 1
      · rw [decide_eq_true hl]; show (0 : F) * _ = 0; exact zero_mul' _
      · rw [decide_eq_false hl]
        have h1 := hs rfl (by unfold P2_BITS at hl hl0 ⊢; omega)
        obtain ⟨a, ha⟩ : ∃ a, s1 - l = a + 1 := ⟨s1 - l - 1, by omega⟩
        show (1 : F) * ((ofN (spnAt s1 rest l) - ofN (spAt s1 l)) + ofN 1) = 0
        unfold spnAt spAt
        rw [if_neg hl, ha, Nat.add_sub_cancel, ofN_add, ofN_one, sub_succ_add_one, mul_zero']

-- ---------------------------------------------------------------------------
-- P2OUT
-- ---------------------------------------------------------------------------

theorem ofN_sub_of_le {x y : Nat} (h : y ≤ x) : ofN (x - y) = ofN x - ofN y := by
  have e := add_sub_right (ofN (x - y)) (ofN y)
  rw [← ofN_add, Nat.sub_add_cancel h] at e
  exact e.symm

/-- Bit `j` of `n`. -/
theorem bitsOf_getD : ∀ (k n j : Nat), j < k → (BitArith.bitsOf k n).getD j false = (n / 2 ^ j % 2 == 1)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, 0, _ => by simp [BitArith.bitsOf]
  | k + 1, n, j + 1, h => by
    show (BitArith.bitsOf k (n / 2)).getD j false = _
    rw [bitsOf_getD k (n / 2) j (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (2 ^ j) 2]

theorem two27 : (2 : Nat) ^ 27 = 134217728 := rfl

/-- **A value below `p` is canonical**: its bits from the `27`th are not all
    set while one below is, since `p = 15 · 2^27 + 1`. -/
theorem canon_bits {y : Nat} (hy : y < Poseidon2.p) (hlo : ∃ j, j < 27 ∧ y / 2 ^ j % 2 = 1)
    (hhi : ∀ t, t < 4 → y / 2 ^ (27 + t) % 2 = 1) : False := by
  -- `omega` below sees no `∧` or `∃`: it would reach for `Classical.choice`
  obtain ⟨j, hj, hb⟩ := hlo
  have ht : ∀ t, t < 4 → y / 134217728 / 2 ^ t % 2 = 1 := by
    intro t ht'
    have := hhi t ht'
    rwa [Nat.pow_add, two27, ← Nat.div_div_eq_div_mul] at this
  clear hhi
  have hp : Poseidon2.p = 15 * 134217728 + 1 := rfl
  have hd := Nat.div_add_mod y (2 ^ 27)
  rw [two27] at hd
  have hm : y / 134217728 < 16 := by omega
  have h0 := ht 0 (by decide)
  have h1 := ht 1 (by decide)
  have h2 := ht 2 (by decide)
  have h3 := ht 3 (by decide)
  simp only [Nat.pow_zero, Nat.div_one, Nat.pow_succ, Nat.one_mul] at h0 h1 h2 h3
  clear ht
  have h15 : y / 134217728 = 15 := by omega
  have hr : y % 134217728 ≠ 0 := by
    intro hz
    have hy' : y = 2 ^ j * (2 ^ (27 - j) * (y / 134217728)) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' (by omega), two27]; omega
    have hk : 27 - j = (26 - j) + 1 := by omega
    rw [hy', Nat.mul_div_cancel_left _ (Nat.two_pow_pos j), hk, Nat.pow_succ, Nat.mul_comm (2 ^ (26 - j)) 2,
      Nat.mul_assoc, Nat.mul_mod_right] at hb
    exact absurd hb (by decide)
  omega

theorem bF_or_and (lo il b : Bool) : bF (lo || (il && b)) - (bF lo + bF il * bF b * (1 - bF lo)) = 0 := by
  cases lo <;> cases il <;> cases b <;> decide

theorem bF_and_or (hi il b : Bool) : bF (hi && (il || b)) - bF hi * (bF il + (1 - bF il) * bF b) = 0 := by
  cases hi <;> cases il <;> cases b <;> decide

theorem p2out_cur : p2outAir.cons.all (fun e => e.onlyAtoms curAtom) = true := by decide

theorem p2out_zero : ∀ c ∈ p2outAir.cons, c.eval (envOf []) = 0 := by
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.1 (show p2outAir.cons.all (fun e => decide (e.eval (envOf []) = 0)) = true
    by decide) c hc)

/-- The output bits' element `ε`, bit `j`. -/
theorem outBits_bit (bs : List Bool) {ε j : Nat} (he : ε < 16) (hj : j < 31) :
    bitF (P2Jet.outBits bs) (31 * ε + j) =
      ((Poseidon2.permute (Poseidon2SKI.valsB bs)).getD ε 0 / 2 ^ j % 2 == 1) := by
  unfold bitF P2Jet.outBits
  rw [flatMap_bits_getD _ ε j (by rw [Poseidon2SKI.permute_len _ (Poseidon2SKI.valsB_length bs)]; exact he) hj,
    bitsOf_getD 31 _ j hj]

/-- **The output's canonical check passes**: at an element's last bit,
    the low and high flags are not both set. -/
theorem out_canon (bs : List Bool) {l : Nat} (hl : l < P2_BITS) (hlast : l % 31 = 30) :
    ¬ (lowL (P2Jet.outBits bs) l = true ∧
      (hiL (P2Jet.outBits bs) l && (P2Jet.outBits bs).getD l false) = true) := by
  rintro ⟨hlo, hhi⟩
  rw [Bool.and_eq_true] at hhi
  have hP : P2_BITS = 496 := rfl
  have he : l / 31 < 16 := by omega
  have hb : l - 30 = 31 * (l / 31) := by omega
  have hy := P2Air.permute_lt _ (Poseidon2SKI.valsB_length bs) _
    (List.getElem_mem (l := Poseidon2.permute (Poseidon2SKI.valsB bs)) (n := l / 31)
      (by rw [Poseidon2SKI.permute_len _ (Poseidon2SKI.valsB_length bs)]; exact he))
  replace hy : (Poseidon2.permute (Poseidon2SKI.valsB bs)).getD (l / 31) 0 < Poseidon2.p := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [Poseidon2SKI.permute_len _ (Poseidon2SKI.valsB_length bs)]; exact he),
      Option.getD_some]
    exact hy
  have bit : ∀ j, j < 31 → bitF (P2Jet.outBits bs) (l - 30 + j) =
      ((Poseidon2.permute (Poseidon2SKI.valsB bs)).getD (l / 31) 0 / 2 ^ j % 2 == 1) := fun j hj => by
    rw [hb]; exact outBits_bit bs he hj
  refine canon_bits hy ?_ ?_
  · unfold lowL lowB at hlo
    rw [hlast] at hlo
    obtain ⟨j, hj, hjb⟩ := List.any_eq_true.1 hlo
    rw [Bool.and_eq_true, decide_eq_true_eq] at hjb
    have hj' := List.mem_range.1 hj
    refine ⟨j, hjb.1, ?_⟩
    have := hjb.2
    rw [bit j (by omega)] at this
    simpa using this
  · intro t ht
    rcases Nat.lt_or_ge t 3 with h3 | h3
    · have hall := hhi.1
      unfold hiL hiB at hall
      rw [hlast] at hall
      have := List.all_eq_true.1 hall (27 + t) (List.mem_range.2 (by omega))
      rw [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h | h
      · omega
      · rw [bit (27 + t) (by omega)] at h; simpa using h
    · have ht3 : t = 3 := by omega
      subst ht3
      have h := hhi.2
      have e : l = l - 30 + 30 := by omega
      rw [show (P2Jet.outBits bs).getD l false = bitF (P2Jet.outBits bs) (l - 30 + 30) by
        unfold bitF; rw [← e], bit 30 (by decide)] at h
      simpa using h

/-- **A P2OUT row of a call's outputs satisfies P2OUT's constraints.** -/
theorem poutRow_cons (ctr rest : Nat) (bs : List Bool) {l : Nat} (hl : l < P2_BITS) :
    ∀ c ∈ p2outAir.cons, c.eval (envOf (poutRow ctr rest (P2Jet.outBits bs) l)) = 0 := by
  intro c hc
  have hP : P2_BITS = 496 := rfl
  simp only [p2outAir, List.mem_cons, List.not_mem_nil, or_false] at hc
  generalize hob : P2Jet.outBits bs = ob
  have canon := out_canon bs hl
  rw [hob] at canon
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show (1 : F) * (1 - ofN 1) = 0; decide
  · show bF (ob.getD l false) * (bF (ob.getD l false) - ofN 1) = 0; exact bF_bool _
  · show ofN (accN ob l + 2 ^ (l % 31) * (ob.getD l false).toNat) -
      (ofN (accN ob l) + ofN (2 ^ (l % 31)) * bF (ob.getD l false)) = 0
    rw [ofN_add, ofN_mul, bF_toNat, sub_self']
  · show (if l % 31 = 30 then 0 else ofN (accN ob l + 2 ^ (l % 31) * (ob.getD l false).toNat)) -
      ((ofN 1 - bF (decide (l % 31 = 30))) * ofN (accN ob l + 2 ^ (l % 31) * (ob.getD l false).toNat)) = 0
    by_cases h : l % 31 = 30
    · rw [if_pos h, decide_eq_true h]; show (0 : F) - ((ofN 1 - 1) * _) = 0
      rw [show (ofN 1 - 1 : F) = 0 by decide, zero_mul']; decide
    · rw [if_neg h, decide_eq_false h]; show _ - ((ofN 1 - 0) * _) = (0 : F)
      rw [show (ofN 1 - 0 : F) = 1 by decide, one_mul', sub_self']
  · exact bF_or_and _ _ _
  · exact bF_and_or _ _ _
  · -- the canonical check
    show bF (decide (l % 31 = 30)) * bF (hiL ob l && (decide (l % 31 < 27) || ob.getD l false)) *
      bF (lowL ob l || (decide (l % 31 < 27) && ob.getD l false)) = 0
    by_cases h : l % 31 = 30
    · rw [decide_eq_true h, show decide (l % 31 < 27) = false from decide_eq_false (by omega),
        Bool.false_or, Bool.false_and, Bool.or_false]
      cases hlo : lowL ob l with
      | false => show bF true * _ * 0 = 0; exact mul_zero' _
      | true =>
        cases hhi : (hiL ob l && ob.getD l false) with
        | false => show bF true * 0 * bF true = 0; decide
        | true => exact absurd ⟨hlo, hhi⟩ (canon h)
    · rw [decide_eq_false h]; show 0 * _ * _ = (0 : F); rw [zero_mul', zero_mul']
  · show (if l % 31 = 30 then 0 else bF (lowL ob l || (decide (l % 31 < 27) && ob.getD l false))) -
      ((ofN 1 - bF (decide (l % 31 = 30))) * bF (lowL ob l || (decide (l % 31 < 27) && ob.getD l false))) = 0
    by_cases h : l % 31 = 30
    · rw [if_pos h, decide_eq_true h]; show (0 : F) - ((ofN 1 - 1) * _) = 0
      rw [show (ofN 1 - 1 : F) = 0 by decide, zero_mul']; decide
    · rw [if_neg h, decide_eq_false h]; show _ - ((ofN 1 - 0) * _) = (0 : F)
      rw [show (ofN 1 - 0 : F) = 1 by decide, one_mul', sub_self']
  · show (if l % 31 = 30 then 1 else bF (hiL ob l && (decide (l % 31 < 27) || ob.getD l false))) -
      ((ofN 1 - bF (decide (l % 31 = 30))) * bF (hiL ob l && (decide (l % 31 < 27) || ob.getD l false)) +
        bF (decide (l % 31 = 30))) = 0
    by_cases h : l % 31 = 30
    · rw [if_pos h, decide_eq_true h]; show (1 : F) - ((ofN 1 - 1) * _ + 1) = 0
      rw [show (ofN 1 - 1 : F) = 0 by decide, zero_mul', zero_add']; decide
    · rw [if_neg h, decide_eq_false h]; show _ - ((ofN 1 - 0) * _ + 0) = (0 : F)
      rw [show (ofN 1 - 0 : F) = 1 by decide, one_mul', add_zero', sub_self']
  · show bF (decide (l % 31 = 30)) - 1 * bF (decide (l % 31 = 30)) = 0
    rw [one_mul', sub_self']
  · -- the stack cell's address
    show 1 * (ofN (ctr + (P2_BITS - 1) - l) - (ofN ctr + ofN (P2_BITS - 1) - ofN l)) = 0
    rw [ofN_sub_of_le (show l ≤ ctr + (P2_BITS - 1) by omega), ofN_add, sub_self', mul_zero']
  · -- its predecessor: the stack below, or the cell before
    show 1 * (ofN (if l = P2_BITS - 1 then rest else ctr + (P2_BITS - 1) - l - 1) -
      (bF (decide (l = P2_BITS - 1)) * ofN rest +
        (ofN 1 - bF (decide (l = P2_BITS - 1))) * (ofN (ctr + (P2_BITS - 1) - l) - ofN 1))) = 0
    rw [one_mul']
    by_cases h : l = P2_BITS - 1
    · rw [if_pos h, decide_eq_true h]; show ofN rest - (1 * ofN rest + (ofN 1 - 1) * _) = 0
      rw [one_mul', show (ofN 1 - 1 : F) = 0 by decide, zero_mul', add_zero', sub_self']
    · rw [if_neg h, decide_eq_false h]; show _ - (0 * ofN rest + (ofN 1 - 0) * _) = (0 : F)
      rw [zero_mul', zero_add', show (ofN 1 - 0 : F) = 1 by decide, one_mul',
        ofN_sub_of_le (show 1 ≤ ctr + (P2_BITS - 1) - l by omega), sub_self']
  · -- the cell's pointer: `K` for a set bit, `K I` for a clear one
    show 1 * (ofN (P2Jet.bitPtr (ob.getD l false)) - (ofN 2 - ofN 2 * bF (ob.getD l false))) = 0
    cases ob.getD l false <;> decide

-- ---------------------------------------------------------------------------
-- The Poseidon2 table: a row of the specification's trace meets every
-- round's constraints
-- ---------------------------------------------------------------------------

section P2

open P2Air Poseidon2SKI

variable (ρ : Atom → F)

theorem allZ_app : ∀ (a b : List E), allZ ρ a → allZ ρ b → allZ ρ (a ++ b)
  | [], _, _, hb => hb
  | _ :: a, b, ⟨h, ha⟩, hb => ⟨h, allZ_app a b ha hb⟩

theorem allZ_mem : ∀ (l : List E), allZ ρ l → ∀ e ∈ l, e.eval ρ = 0
  | [], _, _, he => absurd he List.not_mem_nil
  | x :: l, ⟨h, hs⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · exact h
    · exact allZ_mem l hs e he

theorem range_map_getD (f : Nat → Nat) {n i : Nat} (hi : i < n) : ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem mapEval_getD (vs : List Nat) (es : List Ex) (i : Nat) :
    (es.map (Ex.eval (at16 vs))).getD i 0 = (es.getD i (.lit 0)).eval (at16 vs) :=
  getD_map (Ex.eval (at16 vs)) (.lit 0) es i

/-- Sixteen columns from `k` holding `vs`. -/
theorem ev_cols (k : Nat) (vs : List Nat) (hv : vs.length = 16)
    (hcol : ∀ i, i < 16 → ρ (.main 0 (k + i)) = ofN (vs.getD i 0)) : Ev ρ (colsFrom k) vs := by
  show ((List.range 16).map fun i => col (k + i)).map (E.eval ρ) = vs.map ofN
  rw [List.map_map]
  conv => rhs; rw [← range16_map 0 vs hv, List.map_map]
  exact List.map_congr_left fun i hi => hcol i (List.mem_range.1 hi)

/-- **A linear layer's constraints vanish** when its columns hold the
    layer's values on the state's. -/
theorem lin_zero (st : List E) (vs : List Nat) (es : List Ex) (k : Nat) (hst : Ev ρ st vs)
    (hcol : ∀ i, i < 16 → ρ (.main 0 (k + i)) = ofN ((es.getD i (.lit 0)).eval (at16 vs))) :
    allZ ρ (linCons st es k) := by
  refine allZ_of_mem ρ _ fun e he => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
  have hi' := List.mem_range.1 hi
  show ρ (.main 0 (k + i)) - (toE (stE st) (es.getD i (.lit 0))).eval ρ = 0
  rw [toE_eval, show (fun j => (stE st j).eval ρ) = fun j => ofN (at16 vs j) from funext hst.get, evalF_ofN,
    hcol i hi', sub_self']

/-- An S-box's input, cube and output, in the field. -/
theorem cube_ofN (n : Nat) : ofN (n ^ 3 % Poseidon2.p) = fpow (ofN n) 3 := by
  rw [p_eq, ofN_mod, fpow_ofN]

theorem triple_get {A B C : List Nat} (hA : A.length = 16) (hB : B.length = 16) {i : Nat} (hi : i < 16) :
    (A ++ B ++ C).getD i 0 = A.getD i 0 ∧ (A ++ B ++ C).getD (16 + i) 0 = B.getD i 0 ∧
      (A ++ B ++ C).getD (32 + i) 0 = C.getD i 0 := by
  have hAB : (A ++ B).length = 32 := by rw [List.length_append, hA, hB]
  refine ⟨?_, ?_, ?_⟩
  · rw [getD_append_lt _ _ _ (by omega), getD_append_lt _ _ _ (by omega)]
  · rw [getD_append_lt _ _ _ (by omega), getD_append_ge _ _ _ (by omega), hA, Nat.add_sub_cancel_left]
  · rw [getD_append_ge _ _ _ (by omega), hAB, Nat.add_sub_cancel_left]

/-- **A round's constraints vanish** on columns holding its trace, from a
    state holding `vs`; its new state holds the round's values. -/
theorem round_zero (r : Round) (hr : ∀ rc, r = .full rc → rc.length = 16) (k : Nat) (st : List E)
    (vs : List Nat) (hst : Ev ρ st vs) (hv : vs.length = 16)
    (hcol : ∀ j, j < lenR r → ρ (.main 0 (k + j)) = ofN ((traceR r vs).getD j 0)) :
    allZ ρ (r.gen k st).1 ∧ (r.gen k st).2.2 = k + lenR r ∧ Ev ρ (r.gen k st).2.1 (r.spec vs) := by
  cases r with
  | l0 =>
    have he := bridge_ext vs hv
    have hl : (Poseidon2.extLinear vs).length = 16 := by rw [← he, List.length_map]; rfl
    refine ⟨?_, rfl, ?_⟩
    · refine lin_zero ρ st vs extLE k hst fun i hi => ?_
      rw [hcol i hi]
      show ofN ((Poseidon2.extLinear vs).getD i 0) = _
      rw [← he, mapEval_getD]
    · exact ev_cols ρ k _ hl fun i hi => hcol i hi
  | full rc =>
    have hc := hr rc rfl
    have hsl := sboxL_len rc vs hv hc
    have hsr := sboxL_range vs rc hv hc
    have he := bridge_ext (sboxL rc vs) hsl
    have hx : Poseidon2.extRound vs rc = Poseidon2.extLinear (sboxL rc vs) := by
      rw [extRound_split, extLinear_split]
    have hxl : (Poseidon2.extRound vs rc).length = 16 := by rw [hx, ← he, List.length_map]; rfl
    have hA : ((List.range 16).map (fun i => (vs.getD i 0 + rc.getD i 0) ^ 3 % Poseidon2.p)).length = 16 := by simp
    have hB : ((List.range 16).map (fun i => Poseidon2.sbox (vs.getD i 0 + rc.getD i 0))).length = 16 := by simp
    -- the columns
    have vcube : ∀ i, i < 16 → ρ (.main 0 (k + i)) = fpow (ofN (vs.getD i 0 + rc.getD i 0)) 3 := fun i hi => by
      rw [hcol i (show i < 48 by omega)]
      show ofN ((_ ++ _ ++ Poseidon2.extRound vs rc).getD i 0) = _
      rw [(triple_get hA hB hi).1, range_map_getD _ hi, cube_ofN]
    have vsbox : ∀ i, i < 16 → ρ (.main 0 (k + 16 + i)) = ofN (Poseidon2.sbox (vs.getD i 0 + rc.getD i 0)) :=
      fun i hi => by
        rw [show k + 16 + i = k + (16 + i) by omega, hcol (16 + i) (show 16 + i < 48 by omega)]
        show ofN ((_ ++ _ ++ Poseidon2.extRound vs rc).getD (16 + i) 0) = _
        rw [(triple_get hA hB hi).2.1, range_map_getD _ hi]
    have vlin : ∀ i, i < 16 → ρ (.main 0 (k + 32 + i)) = ofN ((Poseidon2.extRound vs rc).getD i 0) :=
      fun i hi => by
        rw [show k + 32 + i = k + (32 + i) by omega, hcol (32 + i) (show 32 + i < 48 by omega)]
        show ofN ((_ ++ _ ++ Poseidon2.extRound vs rc).getD (32 + i) 0) = _
        rw [(triple_get hA hB hi).2.2]
    have ha : ∀ i, (sboxA st rc i).eval ρ = ofN (vs.getD i 0 + rc.getD i 0) := fun i => by
      show (stE st i).eval ρ + ofN (rc.getD i 0) = _
      rw [hst.get i, ofN_add]
    refine ⟨allZ_app ρ _ _ ?_ ?_, rfl, ?_⟩
    · -- the S-boxes
      refine allZ_of_mem ρ _ fun e he' => ?_
      obtain ⟨i, hi, he2⟩ := List.mem_flatMap.1 he'
      have hi' := List.mem_range.1 hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he2
      rcases he2 with rfl | rfl
      · show ρ (.main 0 (k + i)) - (epow (sboxA st rc i) 3).eval ρ = 0
        rw [epow_eval, ha, vcube i hi', sub_self']
      · show ρ (.main 0 (k + 16 + i)) - ρ (.main 0 (k + i)) * ρ (.main 0 (k + i)) * (sboxA st rc i).eval ρ = 0
        rw [ha, sbox_ofN _ _ (vcube i hi'), vsbox i hi', sub_self']
    · -- the linear layer, on the S-boxes' outputs
      have hst' : Ev ρ (colsFrom (k + 16)) (sboxL rc vs) := ev_cols ρ (k + 16) _ hsl fun i hi => by
        rw [vsbox i hi, ← hsr, range_map_getD _ hi]
      refine lin_zero ρ _ _ extLE (k + 32) hst' fun i hi => ?_
      rw [vlin i hi, hx, ← he, mapEval_getD]
    · exact ev_cols ρ (k + 32) _ hxl fun i hi => vlin i hi
  | part c =>
    match st, vs, hst, hv with
    | e0 :: st', v0 :: vs', hst, hv =>
      have hl0 : (sbox0L c (v0 :: vs')).length = 16 := hv
      have he := bridge_intLin _ hl0
      have hi0 : Poseidon2.intRound (v0 :: vs') c = Poseidon2.intLinear (sbox0L c (v0 :: vs')) := intRound_split _ c
      have hil : (Poseidon2.intRound (v0 :: vs') c).length = 16 := by rw [hi0, ← he, List.length_map]; rfl
      have v0' : ρ (.main 0 k) = fpow (ofN (v0 + c)) 3 := by
        rw [show k = k + 0 from rfl, hcol 0 (by show 0 < 18; decide)]
        show ofN ((v0 + c) ^ 3 % Poseidon2.p) = _
        rw [cube_ofN]
      have v1 : ρ (.main 0 (k + 1)) = ofN (Poseidon2.sbox (v0 + c)) := hcol 1 (by show 1 < 18; decide)
      have vlin : ∀ i, i < 16 → ρ (.main 0 (k + 2 + i)) = ofN ((Poseidon2.intRound (v0 :: vs') c).getD i 0) :=
        fun i hi => by
          rw [show k + 2 + i = k + (2 + i) by omega, hcol (2 + i) (show 2 + i < 18 by omega)]
          show ofN (([_, _] ++ Poseidon2.intRound (v0 :: vs') c).getD (2 + i) 0) = _
          rw [getD_append_ge _ _ _ (by simp)]
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            show 2 + i - (1 + 1) = i by omega]
      have ha : (E.add (stE (e0 :: st') 0) (.const (ofN c))).eval ρ = ofN (v0 + c) := by
        show (stE (e0 :: st') 0).eval ρ + ofN c = _
        rw [hst.get 0, ofN_add]; rfl
      refine ⟨allZ_app ρ _ _ ?_ ?_, rfl, ?_⟩
      · refine ⟨?_, ?_, trivial⟩
        · show ρ (.main 0 k) - (epow (.add (stE (e0 :: st') 0) (.const (ofN c))) 3).eval ρ = 0
          rw [epow_eval, ha, v0', sub_self']
        · show ρ (.main 0 (k + 1)) - ρ (.main 0 k) * ρ (.main 0 k) *
            (E.add (stE (e0 :: st') 0) (.const (ofN c))).eval ρ = 0
          rw [ha, sbox_ofN _ _ v0', v1, sub_self']
      · have hst' : Ev ρ (col (k + 1) :: st') (sbox0L c (v0 :: vs')) := by
          show _ :: _ = _ :: _
          rw [show (col (k + 1)).eval ρ = ρ (.main 0 (k + 1)) from rfl, v1]
          exact congrArg _ hst.tail
        refine lin_zero ρ _ _ intLinLE (k + 2) hst' fun i hi => ?_
        rw [vlin i hi, hi0, ← he, mapEval_getD]
      · exact ev_cols ρ (k + 2) _ hil fun i hi => vlin i hi
    | [], _ :: _, hst, _ => nomatch hst
    | _, [], _, hv => nomatch hv

/-- **The rounds' constraints vanish on columns holding their trace.** -/
theorem gen_zero : ∀ (rs : List Round), RcOK rs → ∀ (k : Nat) (st : List E) (vs : List Nat),
    Ev ρ st vs → vs.length = 16 →
    (∀ j, j < (traceAll rs vs).length → ρ (.main 0 (k + j)) = ofN ((traceAll rs vs).getD j 0)) →
    allZ ρ (gen rs k st).1
  | [], _, _, _, _, _, _, _ => trivial
  | r :: rs, ⟨hr, hrs⟩, k, st, vs, hst, hv, hcol => by
    obtain ⟨hl1, hl2⟩ := traceR_len r hr vs hv
    have et : traceAll (r :: rs) vs = traceR r vs ++ traceAll rs (r.spec vs) := rfl
    have hlen : (traceAll (r :: rs) vs).length = lenR r + (traceAll rs (r.spec vs)).length := by
      rw [et, List.length_append, hl1]
    have hc1 : ∀ j, j < lenR r → ρ (.main 0 (k + j)) = ofN ((traceR r vs).getD j 0) := fun j hj => by
      have := hcol j (by omega)
      rwa [et, getD_append_lt _ _ _ (by omega)] at this
    obtain ⟨z1, e2, ev⟩ := round_zero ρ r hr k st vs hst hv hc1
    show allZ ρ ((r.gen k st).1 ++ (gen rs (r.gen k st).2.2 (r.gen k st).2.1).1)
    refine allZ_app ρ _ _ z1 (gen_zero rs hrs _ _ _ ev hl2 fun j hj => ?_)
    have := hcol (lenR r + j) (by omega)
    rw [et, getD_append_ge _ _ _ (by omega), hl1, Nat.add_sub_cancel_left] at this
    rw [e2, Nat.add_assoc]; exact this

/-- A Poseidon2 table's row: the inputs and the rounds' columns, then the
    key and the activity.  A call's row and the padding row are such rows. -/
def p2Row (s : List Nat) (key act : F) : List F := (s ++ traceAll rounds s).map ofN ++ [key, act]

theorem p2RowT_eq (c : Nat) (s : List Nat) : p2RowT c s = p2Row s (ofN c) 1 := rfl

theorem p2Pad_eq : p2Pad = p2Row (List.replicate 16 0) 0 0 := rfl

-- The constraints read only the current row's columns.

theorem epow_cur (a : E) (ha : a.onlyAtoms curAtom = true) : ∀ n, (epow a n).onlyAtoms curAtom = true
  | 0 => rfl
  | n + 1 => by
    show ((epow a n).onlyAtoms curAtom && a.onlyAtoms curAtom) = true
    rw [epow_cur a ha n, ha]; rfl

theorem toE_cur (env : Nat → E) (h : ∀ i, (env i).onlyAtoms curAtom = true) :
    ∀ e : Ex, (toE env e).onlyAtoms curAtom = true
  | .var i => h i
  | .lit _ => rfl
  | .add a b | .mul a b => by
    show ((toE env a).onlyAtoms curAtom && (toE env b).onlyAtoms curAtom) = true
    rw [toE_cur env h a, toE_cur env h b]; rfl
  | .md a => toE_cur env h a
  | .sbox a => epow_cur _ (toE_cur env h a) 7

/-- Every entry of a state reads only the current row. -/
def StCur (st : List E) : Prop := ∀ e ∈ st, e.onlyAtoms curAtom = true

theorem stE_cur {st : List E} (h : StCur st) (i : Nat) : (stE st i).onlyAtoms curAtom = true := by
  unfold stE
  rw [List.getD_eq_getElem?_getD]
  cases hg : st[i]? with
  | none => rfl
  | some x => exact h x (List.mem_of_getElem? hg)

theorem colsFrom_cur (k : Nat) : StCur (colsFrom k) := by
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 he
  rfl

/-- Every expression of a list reads only the current row. -/
def LCur (l : List E) : Prop := ∀ e ∈ l, e.onlyAtoms curAtom = true

theorem lcur_app {a b : List E} (ha : LCur a) (hb : LCur b) : LCur (a ++ b) := fun e he => by
  rcases List.mem_append.1 he with he | he
  · exact ha e he
  · exact hb e he

theorem lin_cur {st : List E} (h : StCur st) (es : List Ex) (k : Nat) : LCur (linCons st es k) := by
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 he
  show ((col (k + i)).onlyAtoms curAtom && (toE (stE st) (es.getD i (.lit 0))).onlyAtoms curAtom) = true
  rw [toE_cur _ (stE_cur h)]; rfl

theorem round_cur (r : Round) (k : Nat) {st : List E} (h : StCur st) :
    LCur (r.gen k st).1 ∧ StCur (r.gen k st).2.1 := by
  have hA : ∀ (rc : List Nat) (i : Nat), (sboxA st rc i).onlyAtoms curAtom = true := fun rc i => by
    show ((stE st i).onlyAtoms curAtom && true) = true
    rw [stE_cur h]; rfl
  cases r with
  | l0 => exact ⟨lin_cur h extLE k, colsFrom_cur k⟩
  | full rc =>
    refine ⟨lcur_app ?_ (lin_cur (colsFrom_cur _) extLE _), colsFrom_cur _⟩
    intro e he
    obtain ⟨i, _, he2⟩ := List.mem_flatMap.1 he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he2
    rcases he2 with rfl | rfl
    · show (true && (epow (sboxA st rc i) 3).onlyAtoms curAtom) = true
      rw [epow_cur _ (hA rc i)]; rfl
    · show (true && ((true && true) && (sboxA st rc i).onlyAtoms curAtom)) = true
      rw [hA]; rfl
  | part c =>
    have h0 : (E.add (stE st 0) (.const (ofN c))).onlyAtoms curAtom = true := by
      show ((stE st 0).onlyAtoms curAtom && true) = true
      rw [stE_cur h]; rfl
    have ht : StCur (col (k + 1) :: st.tail) := by
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · rfl
      · exact h e (List.mem_of_mem_tail he)
    refine ⟨lcur_app ?_ (lin_cur ht intLinLE _), colsFrom_cur _⟩
    intro e he
    simp only [partCons, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · show (true && (epow _ 3).onlyAtoms curAtom) = true
      rw [epow_cur _ h0]; rfl
    · show (true && ((true && true) && (E.add (stE st 0) (.const (ofN c))).onlyAtoms curAtom)) = true
      rw [h0]; rfl

theorem gen_cur : ∀ (rs : List Round) (k : Nat) {st : List E}, StCur st → LCur (gen rs k st).1
  | [], _, _, _ => fun _ he => absurd he List.not_mem_nil
  | r :: rs, k, st, h => by
    obtain ⟨h1, h2⟩ := round_cur r k h
    exact lcur_app h1 (gen_cur rs _ h2)

theorem p2Cons_cur : p2Air.cons.all (fun e => e.onlyAtoms curAtom) = true := by
  refine List.all_eq_true.2 fun e he => ?_
  rcases List.mem_append.1 he with he | he
  · exact gen_cur rounds 16 (colsFrom_cur 0) e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; rfl

/-- **A row of the specification's trace satisfies the Poseidon2 table's
    constraints**, its activity a bit. -/
theorem p2Row_cons (s : List Nat) (hs : s.length = 16) (key act : F) (hact : act * (act - 1) = 0) :
    ∀ e ∈ p2Air.cons, e.eval (envOf (p2Row s key act)) = 0 := by
  have hT := traceAll_len rounds rounds_rcOK s hs
  rw [rounds_len] at hT
  have hm : ((s ++ traceAll rounds s).map ofN).length = 650 := by
    rw [List.length_map, List.length_append, hs, hT]
  have get : ∀ j, j < 650 → envOf (p2Row s key act) (.main 0 j) = ofN ((s ++ traceAll rounds s).getD j 0) :=
    fun j hj => by
      show (_ ++ [key, act]).getD j 0 = _
      rw [getD_append_lt _ _ _ (by rw [hm]; exact hj), getD_map_ofN]
  intro e he
  rcases List.mem_append.1 he with he | he
  · have hst : Ev (envOf (p2Row s key act)) (colsFrom 0) s := ev_cols _ 0 s hs fun i hi => by
      rw [get _ (by omega), Nat.zero_add, getD_append_lt _ _ _ (by rw [hs]; exact hi)]
    refine allZ_mem _ _ (gen_zero _ rounds rounds_rcOK 16 (colsFrom 0) s hst hs fun j hj => ?_) e he
    rw [get _ (by omega), getD_append_ge _ _ _ (by rw [hs]; omega), hs, Nat.add_sub_cancel_left]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    show (p2Row s key act).getD ACT 0 * ((p2Row s key act).getD ACT 0 - ofN 1) = 0
    have ea : (p2Row s key act).getD ACT 0 = act := by
      show (_ ++ [key, act]).getD 651 0 = act
      rw [getD_append_ge _ _ _ (by rw [hm]; decide), hm]; rfl
    rw [ea]; exact hact

end P2

/-- **A table of rows, as many as its height, satisfies an AIR reading only
    the current row** when every row does. -/
theorem sat_ofRows_full {A : AirD} {rows : List (List F)} {H : Nat} (hH : 0 < H) (hlen : H ≤ rows.length)
    (hcur : A.cons.all (fun e => e.onlyAtoms curAtom) = true)
    (hrow : ∀ rw ∈ rows, ∀ c ∈ A.cons, c.eval (envOf rw) = 0) :
    Sat A ⟨H, ofRows rows, fun _ _ => 0⟩ := by
  refine ⟨hH, fun c hc q (hq : q < H) => ?_⟩
  have ag : ∀ a, curAtom a = true → (Table.env ⟨H, ofRows rows, fun _ _ => 0⟩ q) a = envOf (rows.getD q []) a := by
    intro a ha
    match a, ha with
    | .main 0 j, _ =>
      show ofRows rows ((q + 0) % H) j = _
      rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
    | .pre 0 j, _ => rfl
  rw [eval_cur ag (List.all_eq_true.1 hcur c hc)]
  have hl : q < rows.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact hrow _ (List.getElem_mem hl) c hc

-- ---------------------------------------------------------------------------
-- The jet's tables, from a run
-- ---------------------------------------------------------------------------

namespace P2Run

variable (R : P2Run)

theorem pin_sat {K H : Nat} (hH : 0 < H) : Sat p2inAir (R.pinTable K H) :=
  sat_ofRows hH p2in_cur (fun rw hrw c hc => by
    obtain ⟨i, _, _, l, hl, rfl⟩ := P2Run.pinRows_mem (R := R) hrw
    exact pinRow_cons _ _ _ _ _ l hl (fun hs hl1 => by
      have := (R.jetS_facts hs).2.2.2
      unfold P2_BITS at this hl1; omega) c hc) p2in_zero

theorem pout_sat {K H : Nat} (hH : 0 < H) : Sat p2outAir (R.poutTable K H) :=
  sat_ofRows hH p2out_cur (fun rw hrw c hc => by
    obtain ⟨_, _, _, l, hl, rfl⟩ := P2Run.poutRows_mem (R := R) hrw
    exact poutRow_cons _ _ _ hl c hc) p2out_zero

theorem p2_sat {K H : Nat} (hH : 0 < H) (hlen : (R.p2Rows K).length ≤ H) : Sat P2Air.p2Air (R.p2Table K H) := by
  refine sat_ofRows_full hH (by rw [List.length_append, List.length_replicate]; omega) p2Cons_cur
    (fun rw hrw c hc => ?_)
  rcases List.mem_append.1 hrw with hrw | hrw
  · obtain ⟨_, _, _, rfl⟩ := P2Run.p2Rows_mem (R := R) hrw
    rw [p2RowT_eq]
    exact p2Row_cons _ (Poseidon2SKI.valsB_length _) _ _ (by decide) c hc
  · rw [List.eq_of_mem_replicate hrw, p2Pad_eq]
    exact p2Row_cons _ List.length_replicate _ _ (by decide) c hc

end P2Run

end Circuit
