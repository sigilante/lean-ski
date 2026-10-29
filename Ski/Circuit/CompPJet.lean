import Ski.Circuit.CompPStep
import Ski.Circuit.Flow
import Ski.P2Jet

/-!
# The circuit with the Poseidon2 jet: the jet's row

A CPU row of kind `12` takes the jet's step (`P2Jet.p2Row`):

- **The counter.**  Every row's counter is its head address, one, and a
  24-bit value, so it stays far below `P`; it grows by what the row's kind
  adds, `496` at a jet row.  So no two jet rows share a counter
  (`CompPOK.jet_key_unique`), and each call's messages, keyed by its
  counter, are its own.
- **The chains.**  P2IN's rows on `p2i`, and P2OUT's on `p2o`, are flows
  with one supply and one demand at a jet row's key, so each is one path
  through the levels `0 … 495` (`Edges.path`).
- **The permutation.**  On `p2v` and `p2w`, the Poseidon2 table's active
  rows at a call's key number exactly one, whose inputs are P2IN's
  elements and whose outputs are P2OUT's.
-/

namespace Circuit

open B Air BitArith

/-- What a kind adds to the counter. -/
def incP (k : Nat) : Nat := if k = 0 then 1 else if k = 3 then 3 else if k = 12 then 496 else 0

theorem actOfP_zero (k : Nat) : actOfP k 0 = 1 := by
  unfold actOfP actOfC; split
  · rfl
  · split <;> rfl

/-- A chain row's two messages, as its outgoing edge less its incoming one. -/
theorem ite_edge (A B : Prop) [Decidable A] [Decidable B] :
    ((if A then (-1 : F) else 0) + if B then 1 else 0) = ofN (if B then 1 else 0) - ofN (if A then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp only [hA, hB, if_true, if_false] <;> decide

/-- P2IN's rows at the key `t`, as edges: level `lvl`, from `(acc, m, sp)`
    to `(nacc, m, spn)`. -/
def pinEdges (Pi : Table) (t : F) : Edges :=
  ⟨Pi.h, fun q => decide (Pi.main q 4 = 1) && decide (Pi.main q 0 = t), fun q => Pi.main q 1,
    fun q => [Pi.main q 3, Pi.main q 13, Pi.main q 14], fun q => [Pi.main q 11, Pi.main q 13, Pi.main q 15]⟩

/-- A P2IN row's `p2i` messages: its outgoing edge less its incoming one. -/
theorem pin_rowSends {Pi : Table} (hs : Sat p2inAir Pi) {q : Nat} (hq : q < Pi.h) (t l s m sp : F) :
    rowSends p2inAir Pi "p2i" [t, l, s, m, sp] q =
      ofN (if (pinEdges Pi t).act q && decide ((pinEdges Pi t).outN q = (l, [s, m, sp])) then 1 else 0) -
      ofN (if (pinEdges Pi t).act q && decide ((pinEdges Pi t).inN q = (l, [s, m, sp])) then 1 else 0) := by
  have cv := col_eval hq
  simp only [rowSends, p2inAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, cv,
    B.one, B.c, ofN_one]
  rw [if_neg (show ¬ ("p2idx" = "p2i" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("mem" = "p2i" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("p2v" = "p2i" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [true_and, zero_add', add_zero']
  unfold pinEdges Edges.outN Edges.inN
  dsimp only
  rcases bit_of (pin_act hs hq) with ha | ha <;> simp only [ha]
  · have z : decide ((0 : F) = 1) = false := by decide
    simp only [z, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split <;> split <;> decide
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq, List.cons.injEq, and_true, true_and]
    exact ite_edge _ _

/-- The CPU's `p2i` messages: a jet row starts its chain and ends it. -/
theorem cpuP_p2i {hd0 stk0 ctr0 n nilA J root : Nat} {C : Table} {r : Nat} (hr : r < C.h) (v : List F) :
    rowSends (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C "p2i" v r =
      (if [C.main r CTR, 0, 0, C.main r P2MODE, C.main r P2SP0] = v then C.main r P2SEL else 0) +
      (if [C.main r CTR, ofN P2_BITS, 0, C.main r P2MODE, C.main r P2REST] = v then -C.main r P2SEL else 0) := by
  have cv := col_eval hr
  unfold rowSends
  show cpuIntersP2.foldr _ 0 = _
  rw [cpuIntersP2_eq]
  simp only [List.foldr_cons, List.foldr_nil, readInterP, List.map_cons, List.map_nil, E.eval, cv, B.c, sP2,
    ofN_zero]
  simp (config := { decide := true }) only [false_and, ↓reduceIte, zero_add', add_zero', true_and]

/-- The CPU's two chain messages at its jet row, as nodes. -/
theorem ite_ends (A B : Prop) [Decidable A] [Decidable B] :
    ((if A then (1 : F) else 0) + if B then -1 else 0) = ofN (if A then 1 else 0) - ofN (if B then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp only [hA, hB, if_true, if_false] <;> decide


/-- P2OUT's rows at the key `t`, as edges: level `lvl`, from `(rest, acc,
    low, hi)` to `(rest, nacc, nlowr, nhir)`. -/
def poutEdges (Po : Table) (t : F) : Edges :=
  ⟨Po.h, fun q => decide (Po.main q 7 = 1) && decide (Po.main q 0 = t), fun q => Po.main q 1,
    fun q => [Po.main q 2, Po.main q 4, Po.main q 5, Po.main q 6],
    fun q => [Po.main q 2, Po.main q 14, Po.main q 17, Po.main q 18]⟩

/-- A P2OUT row's `p2o` messages: its outgoing edge less its incoming one. -/
theorem pout_rowSends {Po : Table} (hs : Sat p2outAir Po) {q : Nat} (hq : q < Po.h) (t l a b c' d : F) :
    rowSends p2outAir Po "p2o" [t, l, a, b, c', d] q =
      ofN (if (poutEdges Po t).act q && decide ((poutEdges Po t).outN q = (l, [a, b, c', d])) then 1 else 0) -
      ofN (if (poutEdges Po t).act q && decide ((poutEdges Po t).inN q = (l, [a, b, c', d])) then 1 else 0) := by
  have cv := col_eval hq
  simp only [rowSends, p2outAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, cv,
    B.one, B.c, ofN_one]
  rw [if_neg (show ¬ ("p2idx" = "p2o" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("mem" = "p2o" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("p2w" = "p2o" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [true_and, zero_add', add_zero']
  unfold poutEdges Edges.outN Edges.inN
  dsimp only
  rcases bit_of (pout_act hs hq) with ha | ha <;> simp only [ha]
  · have z : decide ((0 : F) = 1) = false := by decide
    simp only [z, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split <;> split <;> decide
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq, List.cons.injEq, and_true, true_and]
    exact ite_edge _ _

/-- The CPU's `p2o` messages: a jet row starts its chain and ends it. -/
theorem cpuP_p2o {hd0 stk0 ctr0 n nilA J root : Nat} {C : Table} {r : Nat} (hr : r < C.h) (v : List F) :
    rowSends (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C "p2o" v r =
      (if [C.main r CTR, 0, C.main r P2REST, 0, 0, 1] = v then C.main r P2SEL else 0) +
      (if [C.main r CTR, ofN P2_BITS, C.main r P2REST, 0, 0, 1] = v then -C.main r P2SEL else 0) := by
  have cv := col_eval hr
  unfold rowSends
  show cpuIntersP2.foldr _ 0 = _
  rw [cpuIntersP2_eq]
  simp only [List.foldr_cons, List.foldr_nil, readInterP, List.map_cons, List.map_nil, E.eval, cv, B.c, sP2, fld,
    ofN_zero, ofN_one]
  simp (config := { decide := true }) only [false_and, ↓reduceIte, zero_add', add_zero', true_and]

/-- The level table's rows: `idxRow` of each level, padded with level `0`. -/
theorem idxRows_get {x : Nat} (hx : x < 512) : idxRows.getD x [] = idxRow (if x < P2_BITS then x else 0) := by
  have hb : P2_BITS = 496 := rfl
  unfold idxRows
  rw [hb, List.getD_eq_getElem?_getD]
  by_cases h : x < 496
  · rw [if_pos h, List.getElem?_append_left (by simp; exact h), List.getElem?_map, List.getElem?_range h]; rfl
  · rw [if_neg h, List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
    simp only [List.length_map, List.length_range]
    rw [if_pos (by omega)]; rfl

theorem idxRows_length : idxRows.length = 512 := by simp [idxRows, P2_BITS]

/-- A level row's fields, at a level below `496`. -/
theorem idx_of {Px : Table} (hp : PreIs p2idxAir Px) {x : Nat} (hx : x < Px.h) {i : Nat} (hi : i < P2_BITS)
    {e pw ls lo il : F} (hv : (List.range 6).map (fun j => Px.pre x j) = [ofN i, e, pw, ls, lo, il]) :
    [e, pw, ls, lo, il] = (idxRow i).tail := by
  have hh : Px.h = 512 := by rw [hp.1]; exact idxRows_length
  have hrow : (List.range 6).map (fun j => Px.pre x j) = idxRow (if x < P2_BITS then x else 0) := by
    have e6 : ∀ j, j < 6 → Px.pre x j = (idxRow (if x < P2_BITS then x else 0)).getD j 0 := by
      intro j hj
      rw [hp.2 x j hx hj, show p2idxAir.pretrace = idxRows from rfl, idxRows_get (by omega)]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append]
    rw [e6 0 (by decide), e6 1 (by decide), e6 2 (by decide), e6 3 (by decide), e6 4 (by decide), e6 5 (by decide)]
    unfold idxRow; rfl
  rw [hrow] at hv
  have hl : (if x < P2_BITS then x else 0) < P2_BITS := by split <;> unfold P2_BITS at * <;> omega
  generalize (if x < P2_BITS then x else 0) = x' at hv hl
  have h0 : ofN x' = ofN i := by unfold idxRow at hv; simp only [List.cons.injEq] at hv; exact hv.1
  have hP : P2_BITS < P := by decide
  rw [ofN_inj (Nat.lt_trans hl hP) (Nat.lt_trans hi hP) h0] at hv
  rw [hv]; rfl

/-- The bits `b base, …, b (base + j - 1)`. -/
def preB (b : Nat → Bool) (base j : Nat) : List Bool := (List.range j).map fun j' => b (base + j')

theorem preB_length (b : Nat → Bool) (base j : Nat) : (preB b base j).length = j := by simp [preB]

theorem preB_succ (b : Nat → Bool) (base j : Nat) : preB b base (j + 1) = preB b base j ++ [b (base + j)] := by
  simp [preB, List.range_succ]

theorem preB_add (b : Nat → Bool) (base m : Nat) : ∀ k, preB b base (m + k) = preB b base m ++ preB b (base + m) k
  | 0 => by simp [preB]
  | k + 1 => by
    rw [← Nat.add_assoc, preB_succ, preB_add b base m k, preB_succ, List.append_assoc, Nat.add_assoc]

theorem val_append : ∀ (l l' : List Bool), val (l ++ l') = val l + 2 ^ l.length * val l'
  | [], l' => by simp [val]
  | a :: l, l' => by
    simp only [List.cons_append, val, val_append l l', List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ l.length), Nat.add_assoc]

theorem val_snoc (l : List Bool) (b : Bool) : val (l ++ [b]) = val l + 2 ^ l.length * b.toNat := by
  rw [val_append]; simp [val]

/-- **Bits accumulated along a chain**: the value of the element's prefix. -/
theorem accum (A V : Nat → F) (bv : Nat → Bool) (base : Nat) (h0 : A base = 0)
    (hV : ∀ j, j < 31 → V (base + j) = A (base + j) + ofN (2 ^ j) * ofN (bv (base + j)).toNat)
    (hA : ∀ j, j < 30 → A (base + j + 1) = V (base + j)) :
    ∀ j, j < 31 → V (base + j) = ofN (val (preB bv base (j + 1)))
  | 0, _ => by
    rw [hV 0 (by decide), Nat.add_zero, h0, zero_add', Nat.pow_zero, ofN_one, one_mul']
    simp [preB, val]
  | j + 1, hj => by
    rw [hV (j + 1) hj, ← Nat.add_assoc, hA j (by omega), accum A V bv base h0 hV hA j (by omega),
      preB_succ bv base (j + 1), val_snoc, preB_length, ← ofN_mul, ← ofN_add, Nat.add_assoc]

/-- Some bit among the low `27` of the first `j` is set. -/
def lowB (b : Nat → Bool) (base j : Nat) : Bool := (List.range j).any fun j' => decide (j' < 27) && b (base + j')
/-- Every bit from the `27`th among the first `j` is set. -/
def hiB (b : Nat → Bool) (base j : Nat) : Bool := (List.range j).all fun j' => decide (j' < 27) || b (base + j')

theorem lowB_succ (b : Nat → Bool) (base j : Nat) :
    lowB b base (j + 1) = (lowB b base j || (decide (j < 27) && b (base + j))) := by
  simp [lowB, List.range_succ, List.any_append]

theorem hiB_succ (b : Nat → Bool) (base j : Nat) :
    hiB b base (j + 1) = (hiB b base j && (decide (j < 27) || b (base + j))) := by
  simp [hiB, List.range_succ, List.all_append]

/-- **The canonical check along a chain**: the flags are `lowB` and `hiB`. -/
theorem lowhi (LO HI NLO NHI : Nat → F) (bv : Nat → Bool) (base : Nat) (h0 : LO base = 0) (h1 : HI base = 1)
    (hNL : ∀ j, j < 31 → NLO (base + j) =
      LO (base + j) + ofN (if j < 27 then 1 else 0) * ofN (bv (base + j)).toNat * (1 - LO (base + j)))
    (hNH : ∀ j, j < 31 → NHI (base + j) =
      HI (base + j) * (ofN (if j < 27 then 1 else 0) + (1 - ofN (if j < 27 then 1 else 0)) * ofN (bv (base + j)).toNat))
    (hL : ∀ j, j < 30 → LO (base + j + 1) = NLO (base + j))
    (hH : ∀ j, j < 30 → HI (base + j + 1) = NHI (base + j)) :
    ∀ j, j < 31 → NLO (base + j) = ofN (lowB bv base (j + 1)).toNat ∧ NHI (base + j) = ofN (hiB bv base (j + 1)).toNat
  | 0, _ => by
    rw [hNL 0 (by decide), hNH 0 (by decide), Nat.add_zero, h0, h1, lowB_succ, hiB_succ]
    simp only [lowB, hiB, List.range_zero, List.any_nil, List.all_nil, Bool.false_or, Bool.true_and, Nat.add_zero]
    cases bv base <;> decide
  | j + 1, hj => by
    obtain ⟨ihl, ihh⟩ := lowhi LO HI NLO NHI bv base h0 h1 hNL hNH hL hH j (by omega)
    rw [hNL (j + 1) hj, hNH (j + 1) hj, ← Nat.add_assoc, hL j (by omega), hH j (by omega), ihl, ihh,
      lowB_succ bv base (j + 1), hiB_succ bv base (j + 1), Nat.add_assoc]
    generalize lowB bv base (j + 1) = lo
    generalize hiB bv base (j + 1) = hi
    generalize bv (base + (j + 1)) = b
    by_cases h27 : j + 1 < 27
    · rw [if_pos h27, decide_eq_true h27]
      cases lo <;> cases hi <;> cases b <;> decide
    · rw [if_neg h27, decide_eq_false h27]
      cases lo <;> cases hi <;> cases b <;> decide

theorem val_preB_zero (b : Nat → Bool) (base : Nat) : ∀ j, j ≤ 27 → lowB b base j = false → val (preB b base j) = 0
  | 0, _, _ => rfl
  | j + 1, hj, hl => by
    rw [lowB_succ, Bool.or_eq_false_iff] at hl
    rw [preB_succ, val_snoc, val_preB_zero b base j (by omega) hl.1]
    have : b (base + j) = false := by
      have := hl.2
      rw [decide_eq_true (show j < 27 by omega), Bool.true_and] at this
      exact this
    rw [this]; rfl

/-- **The canonical check**: unless the high four bits are all set and some
    low bit is too, the 31 bits' value is below `p`. -/
theorem canon (b : Nat → Bool) (base : Nat) (h : ¬ (lowB b base 31 = true ∧ hiB b base 31 = true)) :
    val (preB b base 31) < Poseidon2.p := by
  have hp : Poseidon2.p = 15 * 2 ^ 27 + 1 := rfl
  rw [show (31 : Nat) = 27 + 4 from rfl, preB_add, val_append, preB_length]
  have hlow := Poseidon2SKI.val_lt (preB b base 27)
  rw [preB_length] at hlow
  have e4 : preB b (base + 27) 4 = [b (base + 27), b (base + 27 + 1), b (base + 27 + 2), b (base + 27 + 3)] := by
    simp only [preB, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append, Nat.add_zero]
  have hl31 : lowB b base 31 = lowB b base 27 := by
    simp only [lowB_succ, show ¬ (27 < 27) by decide, show ¬ (28 < 27) by decide, show ¬ (29 < 27) by decide,
      show ¬ (30 < 27) by decide, decide_false, Bool.false_and, Bool.or_false]
  have hh31 : hiB b base 31 = (hiB b base 27 && b (base + 27) && b (base + 28) && b (base + 29) && b (base + 30)) := by
    simp only [hiB_succ, show ¬ (27 < 27) by decide, show ¬ (28 < 27) by decide, show ¬ (29 < 27) by decide,
      show ¬ (30 < 27) by decide, decide_false, Bool.false_or]
  have hh27 : hiB b base 27 = true := by
    unfold hiB
    rw [List.all_eq_true]
    intro j hj
    rw [decide_eq_true (List.mem_range.1 hj), Bool.true_or]
  rw [hl31, hh31, hh27, Bool.true_and] at h
  rw [e4]
  cases h28 : b (base + 27) <;> cases h29 : b (base + 27 + 1) <;> cases h30 : b (base + 27 + 2) <;>
    cases h31 : b (base + 27 + 3)
  all_goals first
    | (simp only [val, Bool.toNat_false, Bool.toNat_true]; rw [hp]; omega)
    | skip
  have hz : lowB b base 27 = false := by
    cases hl : lowB b base 27
    · rfl
    · exact absurd ⟨rfl, by rw [show base + 28 = base + 27 + 1 from rfl, show base + 29 = base + 27 + 2 from rfl,
        show base + 30 = base + 27 + 3 from rfl, h28, h29, h30, h31]; rfl⟩ (hl ▸ h)
  rw [val_preB_zero b base 27 (Nat.le_refl _) hz]
  simp only [val, Bool.toNat_true]; rw [hp]; omega


/-- P2IN's constraints at a row. -/
theorem pin_eqs {Pi : Table} (hs : Sat p2inAir Pi) {q : Nat} (hq : q < Pi.h) :
    Pi.main q 2 * (Pi.main q 2 - 1) = 0 ∧ Pi.main q 10 = Pi.main q 3 + Pi.main q 6 * Pi.main q 2 ∧
    Pi.main q 11 = (1 - Pi.main q 7) * Pi.main q 10 ∧ Pi.main q 12 = Pi.main q 4 * Pi.main q 7 := by
  have cv := col_eval hq
  have c := fun (e : E) (he : e ∈ p2inAir.cons) => hs.2 e he q hq
  have c1 := c _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have c2 := c _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have c3 := c _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have c4 := c _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self))))
  simp only [B.bool, B.eq, B.one, B.c, E.eval, cv, ofN_one] at c1 c2 c3 c4
  exact ⟨c1, sub_eq_zero c2, sub_eq_zero c3, sub_eq_zero c4⟩

/-- P2IN's read: its gates and the cell it reads, by mode. -/
theorem pin_eqsR {Pi : Table} (hs : Sat p2inAir Pi) {q : Nat} (hq : q < Pi.h) :
    Pi.main q 20 = Pi.main q 4 * (1 - Pi.main q 13) ∧ Pi.main q 21 = Pi.main q 4 * Pi.main q 13 ∧
    (1 - Pi.main q 13) * (Pi.main q 15 - Pi.main q 14) = 0 ∧
    Pi.main q 16 = Pi.main q 21 * Pi.main q 14 + Pi.main q 20 * (Pi.main q 1 + ofN 3) ∧
    Pi.main q 17 = Pi.main q 21 * ofN 5 + Pi.main q 20 * (ofN 3 - Pi.main q 2 * ofN 2) ∧
    Pi.main q 18 = Pi.main q 21 * (ofN 2 - Pi.main q 2 * ofN 2) ∧
    Pi.main q 19 = Pi.main q 21 * Pi.main q 15 + Pi.main q 20 * (1 - Pi.main q 2) ∧
    Pi.main q 22 = Pi.main q 21 * (1 - Pi.main q 9) ∧ Pi.main q 22 * (Pi.main q 15 - Pi.main q 14 + 1) = 0 := by
  have cv := col_eval hq
  have c := fun (e : E) (he : e ∈ p2inAir.cons) => hs.2 e he q hq
  have c5 := c (B.eq (col 20) (.mul (col 4) (.sub one (col 13)))) (by simp [p2inAir])
  have c6 := c (B.eq (col 21) (.mul (col 4) (col 13))) (by simp [p2inAir])
  have c7 := c (.mul (.sub one (col 13)) (.sub (col 15) (col 14))) (by simp [p2inAir])
  have c8 := c (B.eq (col 16) (.add (.mul (col 21) (col 14)) (.mul (col 20) (.add (col 1) (B.c 3)))))
    (by simp [p2inAir])
  have c9 := c (B.eq (col 17) (.add (.mul (col 21) (B.c 5)) (.mul (col 20) (.sub (B.c 3) (.mul (col 2) (B.c 2))))))
    (by simp [p2inAir])
  have c10 := c (B.eq (col 18) (.mul (col 21) (.sub (B.c 2) (.mul (col 2) (B.c 2))))) (by simp [p2inAir])
  have c11 := c (B.eq (col 19) (.add (.mul (col 21) (col 15)) (.mul (col 20) (.sub one (col 2)))))
    (by simp [p2inAir])
  have c12 := c (B.eq (col 22) (.mul (col 21) (.sub one (col 9)))) (by simp [p2inAir])
  have c13 := c (.mul (col 22) (.add (.sub (col 15) (col 14)) one)) (by simp [p2inAir])
  simp only [B.eq, B.one, B.c, E.eval, cv, ofN_one] at c5 c6 c7 c8 c9 c10 c11 c12 c13
  exact ⟨sub_eq_zero c5, sub_eq_zero c6, c7, sub_eq_zero c8, sub_eq_zero c9, sub_eq_zero c10, sub_eq_zero c11,
    sub_eq_zero c12, c13⟩

/-- P2OUT's constraints at a row. -/
theorem pout_eqs {Po : Table} (hs : Sat p2outAir Po) {q : Nat} (hq : q < Po.h) :
    Po.main q 3 * (Po.main q 3 - 1) = 0 ∧
    Po.main q 13 = Po.main q 4 + Po.main q 9 * Po.main q 3 ∧
    Po.main q 14 = (1 - Po.main q 10) * Po.main q 13 ∧
    Po.main q 15 = Po.main q 5 + Po.main q 11 * Po.main q 3 * (1 - Po.main q 5) ∧
    Po.main q 16 = Po.main q 6 * (Po.main q 11 + (1 - Po.main q 11) * Po.main q 3) ∧
    Po.main q 10 * Po.main q 16 * Po.main q 15 = 0 ∧
    Po.main q 17 = (1 - Po.main q 10) * Po.main q 15 ∧
    Po.main q 18 = (1 - Po.main q 10) * Po.main q 16 + Po.main q 10 ∧
    Po.main q 19 = Po.main q 7 * Po.main q 10 ∧
    Po.main q 7 * (Po.main q 20 - (Po.main q 0 + ofN (P2_BITS - 1) - Po.main q 1)) = 0 ∧
    Po.main q 7 * (Po.main q 21 - (Po.main q 12 * Po.main q 2 + (1 - Po.main q 12) * (Po.main q 20 - 1))) = 0 ∧
    Po.main q 7 * (Po.main q 22 - (ofN 2 - ofN 2 * Po.main q 3)) = 0 := by
  have cv := col_eval hq
  have c := fun (i : Nat) (hi : i < 13) => hs.2 (p2outAir.cons.getD i zero)
    (List.getD_eq_getElem?_getD .. ▸ by
      rw [List.getElem?_eq_getElem (by show i < 13; exact hi)]; exact List.getElem_mem _) q hq
  have c1 := c 1 (by decide); have c2 := c 2 (by decide); have c3 := c 3 (by decide)
  have c4 := c 4 (by decide); have c5 := c 5 (by decide); have c6 := c 6 (by decide)
  have c7 := c 7 (by decide); have c8 := c 8 (by decide); have c9 := c 9 (by decide)
  have c10 := c 10 (by decide); have c11 := c 11 (by decide); have c12 := c 12 (by decide)
  simp only [p2outAir, List.getD_cons_succ, List.getD_cons_zero, B.bool, B.eq, B.one, B.c, E.eval, cv,
    ofN_one] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
  exact ⟨c1, sub_eq_zero c2, sub_eq_zero c3, sub_eq_zero c4, sub_eq_zero c5, c6, sub_eq_zero c7,
    sub_eq_zero c8, sub_eq_zero c9, c10, c11, c12⟩

theorem ofN_ne_of_lt {a b : Nat} (ha : a < P) (hb : b < P) (h : a ≠ b) : (ofN a : F) ≠ ofN b :=
  fun e => h (ofN_inj ha hb e)

/-- The Poseidon2 table's activity is a bit. -/
theorem p2_act {Pp : Table} (hs : Sat P2Air.p2Air Pp) {q : Nat} (hq : q < Pp.h) :
    Pp.main q P2Air.ACT * (Pp.main q P2Air.ACT - 1) = 0 := by
  have := hs.2 _ (List.mem_append_right _ List.mem_cons_self) q hq
  simpa [B.bool, B.col, B.one, B.c, E.eval, env_main0 hq, ofN_one] using this

theorem p2Air_inters : P2Air.p2Air.inters =
    (List.range 16).map (fun e => (⟨"p2v", 1, .neg (col P2Air.ACT), [col P2Air.KEY, c e, col e]⟩ : Inter)) ++
    (List.range 16).map (fun e => (⟨"p2w", 1, col P2Air.ACT, [col P2Air.KEY, c e, P2Air.p2Out.getD e (c 0)]⟩ : Inter)) :=
  rfl

/-- A Poseidon2 row's `p2v` message for element `ε`: it receives `(key, ε, in_ε)`. -/
theorem p2_rowSends_v {Pp : Table} {q : Nat} (hq : q < Pp.h) {ε : Nat} (he : ε < 16) (t x : F) :
    rowSends P2Air.p2Air Pp "p2v" [t, ofN ε, x] q =
      if Pp.main q P2Air.KEY = t ∧ Pp.main q ε = x then -Pp.main q P2Air.ACT else 0 := by
  have cv := col_eval hq
  unfold rowSends
  rw [p2Air_inters, List.foldr_append, foldr_zero_init _ 0 _ (fun I hI => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hI
      exact if_neg (fun h' => absurd (h'.1 : "p2w" = "p2v") (by decide))),
    List.foldr_map]
  rw [fold_single _ 16 ε he (fun e' _ hne => by
    apply if_neg
    intro h'
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h'
    exact ofN_ne_of_lt (Nat.lt_trans ‹e' < 16› (by decide)) (Nat.lt_trans he (by decide)) hne
      (by simpa [B.c, E.eval] using h'.2.2.1))]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, E.eval, cv, B.c, true_and, and_true]

/-- A Poseidon2 row's `p2w` message for element `ε`: it sends `(key, ε, out_ε)`. -/
theorem p2_rowSends_w {Pp : Table} {q : Nat} (hq : q < Pp.h) {ε : Nat} (he : ε < 16) (t y : F) :
    rowSends P2Air.p2Air Pp "p2w" [t, ofN ε, y] q =
      if Pp.main q P2Air.KEY = t ∧ (P2Air.p2Out.getD ε (c 0)).eval (Pp.env q) = y then Pp.main q P2Air.ACT else 0 := by
  have cv := col_eval hq
  unfold rowSends
  rw [p2Air_inters, List.foldr_append, foldr_zero_init _ _ _ (fun I hI => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hI
      exact if_neg (fun h' => absurd (h'.1 : "p2v" = "p2w") (by decide))),
    List.foldr_map]
  rw [fold_single _ 16 ε he (fun e' he' hne => by
    apply if_neg
    intro h'
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h'
    exact ofN_ne_of_lt (Nat.lt_trans he' (by decide)) (Nat.lt_trans he (by decide)) hne
      (by simpa [B.c, E.eval] using h'.2.2.1))]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, E.eval, cv, B.c, true_and, and_true]
  split <;> rfl

/-- A P2IN row's `p2v` message: an element's value, at its last bit. -/
theorem pin_rowSends_v {Pi : Table} {q : Nat} (hq : q < Pi.h) (v : List F) :
    rowSends p2inAir Pi "p2v" v q = if [Pi.main q 0, Pi.main q 5, Pi.main q 10] = v then Pi.main q 12 else 0 := by
  have cv := col_eval hq
  simp only [rowSends, p2inAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, cv]
  rw [if_neg (show ¬ ("p2idx" = "p2v" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("p2i" = "p2v" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("p2i" = "p2v" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("mem" = "p2v" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [true_and, zero_add', add_zero']

/-- A P2OUT row's `p2w` message: an element's value, received at its last bit. -/
theorem pout_rowSends_w {Po : Table} {q : Nat} (hq : q < Po.h) (v : List F) :
    rowSends p2outAir Po "p2w" v q = if [Po.main q 0, Po.main q 8, Po.main q 13] = v then -Po.main q 19 else 0 := by
  have cv := col_eval hq
  simp only [rowSends, p2outAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, cv]
  rw [if_neg (show ¬ ("p2idx" = "p2w" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("p2o" = "p2w" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("p2o" = "p2w" ∧ _) from fun h' => absurd h'.1 (by decide)),
      if_neg (show ¬ ("mem" = "p2w" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [true_and, zero_add', add_zero']

/-- `a + (0 - b) = 0` makes `a = b`. -/
theorem eq_of_add_zero_sub {a b : F} (h : a + (0 - b) = 0) : a = b := by
  apply sub_eq_zero
  rw [← h]
  exact E.eval_eq_of_norm (e := .sub (.atom (.main 0 0)) (.atom (.main 0 1)))
    (e' := .add (.atom (.main 0 0)) (.sub (.const 0) (.atom (.main 0 1)))) (by decide)
    (fun | .main 0 0 => a | .main 0 1 => b | _ => 0)

theorem sumTo_two {f : Nat → Nat} : ∀ n q q', q < n → q' < n → q ≠ q' → f q + f q' ≤ sumTo n f
  | 0, _, _, hq, _, _ => absurd hq (Nat.not_lt_zero _)
  | n + 1, q, q', hq, hq', hne => by
    show f q + f q' ≤ sumTo n f + f n
    rcases Nat.lt_or_ge q n with h1 | h1 <;> rcases Nat.lt_or_ge q' n with h2 | h2
    · exact Nat.le_trans (sumTo_two n q q' h1 h2 hne) (Nat.le_add_right _ _)
    · rw [Nat.le_antisymm (Nat.le_of_lt_succ hq') h2]; exact Nat.add_le_add_right (sumTo_ge n q h1) _
    · rw [Nat.le_antisymm (Nat.le_of_lt_succ hq) h1, Nat.add_comm]
      exact Nat.add_le_add_right (sumTo_ge n q' h2) _
    · exact absurd ((Nat.le_antisymm (Nat.le_of_lt_succ hq) h1).trans (Nat.le_antisymm (Nat.le_of_lt_succ hq') h2).symm) hne

/-- The blinded jet tables send, on any bus but their blinding buses, what
    the unblinded ones do. -/
theorem pinB_sends (T : Table) (bus : String) (v : List F) (hb : bus ≠ "blind_c" ∧ bus ≠ "blind_d") :
    tableSends p2inAirB T bus v = tableSends p2inAir T bus v :=
  tableSends_withBlocks (fun b hm e => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hb.1 e.symm
    · exact hb.2 e.symm) v

theorem poutB_sends (T : Table) (bus : String) (v : List F) (hb : bus ≠ "blind_d" ∧ bus ≠ "blind_e") :
    tableSends p2outAirB T bus v = tableSends p2outAir T bus v :=
  tableSends_withBlocks (fun b hm e => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hb.1 e.symm
    · exact hb.2 e.symm) v

theorem p2B_sends (T : Table) (bus : String) (v : List F) (hb : bus ≠ "blind_e") :
    tableSends p2AirB T bus v = tableSends P2Air.p2Air T bus v :=
  tableSends_withBlocks (fun b hm e => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    exact hb e.symm) v

section

variable {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg Pi Po Pp Px : Table}
  (h : CompPOK hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px)
include h

theorem CompPOK.cpu_h : C.h ≤ 2 ^ 27 := h.two (cpuAirP2 hd0 stk0 ctr0 n nilA J root, C) (by simp [compPTables])
theorem CompPOK.pin_h : Pi.h ≤ 2 ^ 27 := h.two (p2inAirB, Pi) (by simp [compPTables])
theorem CompPOK.pout_h : Po.h ≤ 2 ^ 27 := h.two (p2outAirB, Po) (by simp [compPTables])
theorem CompPOK.p2_h : Pp.h ≤ 2 ^ 27 := h.two (p2AirB, Pp) (by simp [compPTables])

/-- **Every row's counter** is its head address, one, and a 24-bit value. -/
theorem CompPOK.ctr_eq {r : Nat} (hr : r < C.h) :
    (C.main r HD).val < Mm.h ∧
      (C.main r CTR).val = (C.main r HD).val + 1 + ((rangeVal 0).eval (C.env r)).val := by
  obtain ⟨k, hk⟩ := kind_ofP2 h.cpu hr
  have rd0 := h.read hr hk (j := 0) (by decide) (actOfP_zero k)
  have hlt : (C.main r (addrCol 0)).val < Mm.h := by
    unfold rd at rd0
    split at rd0
    · have := (List.getElem?_eq_some_iff.1 rd0).1
      rw [memOf_length] at this; exact this
    · cases rd0
  obtain ⟨hf, _⟩ := kind_factsP hr hk
  obtain ⟨ha, _⟩ := hf 0 (by decide)
  rw [actOfP_zero, ofN_one] at ha
  have hre := range_eqP2 h.cpu hr (j := 0) (by decide)
  rw [ha, one_mul'] at hre
  have hadr : (addrs.getD 0 zero).eval (C.env r) = C.main r HD := by
    simp [addrs, B.col, E.eval, env_main0 hr]
  rw [hadr] at hre
  have e := sub_eq_zero hre
  have hctr : C.main r CTR = (C.main r HD + 1) + (rangeVal 0).eval (C.env r) := by
    rw [← e, add_sub_cancel3]
  have hv := rangeVal_ltP h hr (j := 0) (by decide)
  have hm := h.mem_h
  have hP := P_big
  have h0 : (C.main r HD).val < Mm.h := hlt
  have h1 : (C.main r HD + 1).val = (C.main r HD).val + 1 :=
    val_add_of_lt (by show _ + 1 < P; omega)
  refine ⟨h0, ?_⟩
  rw [hctr, val_add_of_lt (by rw [h1]; omega), h1]

theorem CompPOK.ctr_lt {r : Nat} (hr : r < C.h) : (C.main r CTR).val < 2 ^ 27 + 2 ^ 24 + 1 := by
  obtain ⟨h0, e⟩ := h.ctr_eq hr
  have hv := rangeVal_ltP h hr (j := 0) (by decide)
  have hm := h.mem_h
  omega

/-- **The counter grows by the row's kind.** -/
theorem CompPOK.next_ctr {r k : Nat} (hn : r + 1 < C.h) (hk : IsKindP C r k) :
    (C.main (r + 1) CTR).val = (C.main r CTR).val + incP k := by
  have hr : r < C.h := Nat.lt_of_succ_lt hn
  obtain ⟨_, _, _, _, _, _, hP2, _, _, hnc⟩ := kind_factsP hr hk
  obtain ⟨_, _, e⟩ := next_regsP2 h.cpu hr hn
  have hsel : C.main r P2SEL = ofN (if k = 12 then 1 else 0) := by rw [← hP2]; exact (col_eval hr P2SEL).symm
  rw [hnc, hsel] at e
  have cv := col_eval hr
  have hb := h.ctr_lt hr
  have hP := P_big
  have fe : C.main (r + 1) CTR = C.main r CTR + ofN (incP k) := by
    rw [e]
    by_cases k0 : k = 0
    · subst k0
      show (E.add (col CTR) one).eval _ + ofN 0 * ofN P2_BITS = _
      simp only [E.eval, cv, B.one, B.c, ofN_zero, zero_mul', add_zero']; rfl
    by_cases k3 : k = 3
    · subst k3
      show (E.add (col CTR) (c 3)).eval _ + ofN 0 * ofN P2_BITS = _
      simp only [E.eval, cv, B.c, ofN_zero, zero_mul', add_zero']; rfl
    by_cases k12 : k = 12
    · subst k12
      show (col CTR).eval _ + ofN 1 * ofN P2_BITS = _
      rw [cv, ofN_one, one_mul']; rfl
    have hc : nextCtrOfP k = col CTR := by
      unfold nextCtrOfP nextCtrOfC nextCtrOf
      rw [if_neg k12]
      by_cases k11 : k = 11
      · rw [if_pos k11]
      · rw [if_neg k11, if_neg k0, if_neg k3]
    have hi : incP k = 0 := by unfold incP; rw [if_neg k0, if_neg k3, if_neg k12]
    rw [hc, cv, if_neg k12, ofN_zero, zero_mul', add_zero', hi, ofN_zero, add_zero']
  have hinc : incP k ≤ 496 := by unfold incP; split <;> (try split) <;> (try split) <;> decide
  have hP' : 2 ^ 27 + 2 ^ 24 + 1 + 496 < P := by decide
  rw [fe, val_add_nat (by omega)]

/-- The counter never decreases. -/
theorem CompPOK.ctr_le {r : Nat} (d : Nat) : r + d < C.h → (C.main r CTR).val ≤ (C.main (r + d) CTR).val := by
  induction d with
  | zero => intro _; exact Nat.le_refl _
  | succ d ih =>
    intro hd
    have hd1 : r + d + 1 < C.h := hd
    have ih := ih (Nat.lt_of_succ_lt hd1)
    obtain ⟨k, hk⟩ := kind_ofP2 h.cpu (Nat.lt_of_succ_lt hd1)
    rw [show r + (d + 1) = r + d + 1 from rfl, h.next_ctr hd1 hk]
    omega

/-- **Past a jet row the counter is `496` higher.** -/
theorem CompPOK.jet_lt {r : Nat} (hp : C.main r P2SEL = 1) {d : Nat} (hd : r + 1 + d < C.h) :
    (C.main r CTR).val + 496 ≤ (C.main (r + 1 + d) CTR).val := by
  have hr1 : r + 1 < C.h := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hd
  obtain ⟨k, hk⟩ := kind_ofP2 h.cpu (Nat.lt_of_succ_lt hr1)
  have k12 : k = 12 := by
    have := hk.2.2.2
    rw [hp] at this
    by_cases e : k = 12
    · exact e
    · rw [if_neg e] at this; exact absurd this (by decide)
  have e := h.next_ctr hr1 hk
  rw [k12] at e
  have hm := h.ctr_le (r := r + 1) d hd
  have : incP 12 = 496 := rfl
  omega

/-- **No two jet rows share a counter.** -/
theorem CompPOK.jet_key_unique {r r' : Nat} (hr : r < C.h) (hr' : r' < C.h) (hp : C.main r P2SEL = 1)
    (hp' : C.main r' P2SEL = 1) (e : C.main r CTR = C.main r' CTR) : r = r' := by
  rcases Nat.lt_trichotomy r r' with hlt | heq | hgt
  · have := h.jet_lt hp (d := r' - r - 1) (by rw [show r + 1 + (r' - r - 1) = r' by omega]; exact hr')
    rw [show r + 1 + (r' - r - 1) = r' by omega, ← e] at this
    omega
  · exact heq
  · have := h.jet_lt hp' (d := r - r' - 1) (by rw [show r' + 1 + (r - r' - 1) = r by omega]; exact hr)
    rw [show r' + 1 + (r - r' - 1) = r by omega, e] at this
    omega

/-- A jet row is of kind `12`. -/
theorem CompPOK.kind12 {r : Nat} (hr : r < C.h) (hp : C.main r P2SEL = 1) : IsKindP C r 12 := by
  obtain ⟨k, hk⟩ := kind_ofP2 h.cpu hr
  have := hk.2.2.2
  rw [hp] at this
  by_cases e : k = 12
  · rw [← e]; exact hk
  · rw [if_neg e] at this; exact absurd this (by decide)

/-- **A jet row's reads**: `cons k s₁` at the stack, the cell `cons a b` at
    `s₁`, and the slots `K`, `I`, `K I`.  On the comb (`MODE = 0`) the atom
    `J` at the head, `a` the root, the stack below the inputs `b` and the
    input chain's start there; on the stack (`MODE = 1`) the atom `J + 1`
    at the head and the input chain's start at `s₁`. -/
theorem CompPOK.jetReads {r : Nat} (hr : r < C.h) (hp : C.main r P2SEL = 1) (hJ : J + 1 < P) (hroot : root < P) :
    ((C.main r P2MODE = 0 ∧ rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some (.atom J) ∧
        (C.main r (FLD + 4)).val = root ∧ C.main r P2REST = C.main r (FLD + 5) ∧
        C.main r P2SP0 = C.main r P2REST) ∨
      (C.main r P2MODE = 1 ∧ rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some (.atom (J + 1)) ∧
        C.main r P2SP0 = C.main r (FLD + 3))) ∧
    rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
      some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) ∧
    rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val =
      some (.cons (C.main r (FLD + 4)).val (C.main r (FLD + 5)).val) ∧
    (memOf Mm)[0]? = some .K ∧ (memOf Mm)[1]? = some .I ∧ (memOf Mm)[2]? = some (.app 0 1) := by
  have hk := h.kind12 hr hp
  obtain ⟨p0, p4, pm, pcm, prest, psp⟩ := p2_pinsP h.cpu hr
  rw [hp, one_mul'] at p0 pcm
  have e0 := sub_eq_zero p0
  have r0 := h.read hr hk (j := 0) (by decide) rfl
  have r1 := h.read hr hk (j := 1) (by decide) rfl
  have r2 := h.read hr hk (j := 2) (by decide) rfl
  have cv := col_eval hr
  have hs1 : sP2.eval (C.env r) = 1 := by rw [show sP2.eval (C.env r) = C.main r P2SEL from cv P2SEL, hp]
  have s0 := h.sendP hr (I := ⟨"mem", 1, sP2, [c 0, c 1, c 0, c 0]⟩)
    (by rw [cpuIntersP2_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
    (a := ofN 0) (t := ofN 1) (x := ofN 0) (y := ofN 0) (by simp only [List.map_cons, List.map_nil, B.c, E.eval]) hs1
  have s1 := h.sendP hr (I := ⟨"mem", 1, sP2, [c 1, c 2, c 0, c 0]⟩)
    (by rw [cpuIntersP2_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
    (a := ofN 1) (t := ofN 2) (x := ofN 0) (y := ofN 0) (by simp only [List.map_cons, List.map_nil, B.c, E.eval]) hs1
  have s2 := h.sendP hr (I := ⟨"mem", 1, sP2, [c 2, c 3, c 0, c 1]⟩)
    (by rw [cpuIntersP2_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
    (a := ofN 2) (t := ofN 3) (x := ofN 0) (y := ofN 1) (by simp only [List.map_cons, List.map_nil, B.c, E.eval]) hs1
  rw [show addrCol 0 = HD from rfl, show tagOfP 12 0 = 6 from rfl, cellOf_atom, e0] at r0
  rw [show addrCol 2 = FLD + 3 from rfl, show tagOfP 12 2 = 5 from rfl, cellOf_cons,
    show FLD + 2 * 2 = FLD + 4 from rfl, show FLD + 2 * 2 + 1 = FLD + 5 from rfl] at r2
  refine ⟨?_, r1, r2, s0.2, s1.2, s2.2⟩
  rcases bit_of pm with hm | hm
  · rw [hm] at pcm psp r0
    rw [show (1 : F) - 0 = 1 by decide] at pcm
    rw [pcm, one_mul'] at p4 prest
    rw [show (0 : F) * C.main r (FLD + 3) = 0 by rw [zero_mul'], show (1 : F) - 0 = 1 by decide, one_mul',
      zero_add'] at psp
    refine .inl ⟨hm, ?_, ?_, sub_eq_zero prest, psp⟩
    · rw [r0, add_zero', val_ofN (Nat.lt_of_succ_lt hJ)]
    · rw [sub_eq_zero p4, val_ofN hroot]
  · rw [hm] at psp r0
    rw [show (1 : F) - 1 = 0 by decide, zero_mul', add_zero', one_mul'] at psp
    refine .inr ⟨hm, ?_, psp⟩
    rw [r0, ← ofN_one, ← ofN_add, val_ofN hJ]

/-- **A jet row's next registers**: `k` at the head, the counter plus `495`
    at the stack, the counter plus `496`. -/
theorem CompPOK.jetNext {r : Nat} (hn : r + 1 < C.h) (hp : C.main r P2SEL = 1) :
    C.main (r + 1) HD = C.main r (FLD + 2) ∧
    C.main (r + 1) STK = C.main r CTR + ofN (P2_BITS - 1) ∧
    C.main (r + 1) CTR = C.main r CTR + ofN P2_BITS := by
  have hr : r < C.h := Nat.lt_of_succ_lt hn
  have hk := h.kind12 hr hp
  obtain ⟨_, _, _, _, _, hRS, _, h1, h2, h3⟩ := kind_factsP hr hk
  obtain ⟨e1, e2, e3⟩ := next_regsP2 h.cpu hr hn
  have cv := col_eval hr
  have hrs : C.main r RS = 0 := by rw [← cv RS]; exact hRS
  rw [h1, hrs, hp, zero_mul', one_mul'] at e1
  rw [h2, hrs, hp, zero_mul', one_mul'] at e2
  rw [h3, hp, one_mul'] at e3
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; show (zero).eval _ + 0 + _ = _; simp only [B.zero, B.c, E.eval, ofN_zero, zero_add', add_zero']
  · rw [e2]; show (zero).eval _ + 0 + _ = _; simp only [B.zero, B.c, E.eval, ofN_zero, zero_add', add_zero']
  · rw [e3]; show (col CTR).eval _ + _ = _; rw [cv]

/-- **`p2i` is a flow** at a jet row's key, from `(0, 0)` to `(496, 0)`. -/
theorem CompPOK.pinConserve {r0 : Nat} (hr0 : r0 < C.h) (hp : C.main r0 P2SEL = 1) :
    (pinEdges Pi (C.main r0 CTR)).Conserve (some ((0 : F), [0, C.main r0 P2MODE, C.main r0 P2SP0]))
      (some (ofN P2_BITS, [0, C.main r0 P2MODE, C.main r0 P2REST])) := by
  intro v
  obtain ⟨l, st⟩ := v
  have hCP : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  have zero_case : (∀ x y z : F, st ≠ [x, y, z]) →
      (pinEdges Pi (C.main r0 CTR)).cntOut (l, st) +
          Edges.oneIf (some ((0 : F), [0, C.main r0 P2MODE, C.main r0 P2SP0])) (l, st) =
        (pinEdges Pi (C.main r0 CTR)).cntIn (l, st) +
          Edges.oneIf (some (ofN P2_BITS, [0, C.main r0 P2MODE, C.main r0 P2REST])) (l, st) := by
    intro hst
    have z1 : (pinEdges Pi (C.main r0 CTR)).cntOut (l, st) = 0 := sumTo_zero (fun q => by
      rw [show decide ((pinEdges Pi (C.main r0 CTR)).outN q = (l, st)) = false from
        decide_eq_false (fun e => hst _ _ _ (congrArg Prod.snd e).symm), Bool.and_false]; rfl) _
    have z2 : (pinEdges Pi (C.main r0 CTR)).cntIn (l, st) = 0 := sumTo_zero (fun q => by
      rw [show decide ((pinEdges Pi (C.main r0 CTR)).inN q = (l, st)) = false from
        decide_eq_false (fun e => hst _ _ _ (congrArg Prod.snd e).symm), Bool.and_false]; rfl) _
    have o1 : Edges.oneIf (some ((0 : F), [0, C.main r0 P2MODE, C.main r0 P2SP0])) (l, st) = 0 :=
      if_neg (fun e => hst _ _ _ (congrArg Prod.snd (Option.some.inj e)).symm)
    have o2 : Edges.oneIf (some (ofN P2_BITS, [0, C.main r0 P2MODE, C.main r0 P2REST])) (l, st) = 0 :=
      if_neg (fun e => hst _ _ _ (congrArg Prod.snd (Option.some.inj e)).symm)
    rw [z1, z2, o1, o2]
  match st with
  | [] => exact zero_case (fun _ _ _ e => by cases e)
  | [_] => exact zero_case (fun _ _ _ e => by cases e)
  | [_, _] => exact zero_case (fun _ _ _ e => by cases e)
  | _ :: _ :: _ :: _ :: _ => exact zero_case (fun _ _ _ e => by cases e)
  | [s, m, sp] =>
    have hb := h.bal "p2i" [C.main r0 CTR, l, s, m, sp]
    simp only [compPTables, List.foldr_cons, List.foldr_nil] at hb
    rw [sends_nobus' (A := memAirC) rfl, sends_nobus' (A := progAirC heap N W) rfl,
      sends_nobus' (A := witAirP N W) rfl, sends_nobus' (A := segsAir roots) rfl,
      sends_nobus' (A := p2outAirB) rfl, sends_nobus' (A := p2AirB) (by decide),
      sends_nobus' (A := p2idxAir) rfl] at hb
    simp only [zero_add', add_zero'] at hb
    rw [pinB_sends Pi _ _ (by decide)] at hb
    have hpin : tableSends p2inAir Pi "p2i" [C.main r0 CTR, l, s, m, sp] =
        ofN ((pinEdges Pi (C.main r0 CTR)).cntOut (l, [s, m, sp])) - ofN ((pinEdges Pi (C.main r0 CTR)).cntIn (l, [s, m, sp])) := by
      unfold tableSends
      rw [foldr_range_congr (f := fun q => rowSends p2inAir Pi "p2i" [C.main r0 CTR, l, s, m, sp] q) Pi.h
        (fun q hq => pin_rowSends h.pin hq _ l s m sp), fold_sub, fold_ofN, fold_ofN]
      rfl
    have hcpu : tableSends (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C "p2i" [C.main r0 CTR, l, s, m, sp] =
        ofN (Edges.oneIf (some ((0 : F), [0, C.main r0 P2MODE, C.main r0 P2SP0])) (l, [s, m, sp])) - ofN (Edges.oneIf (some (ofN P2_BITS, [0, C.main r0 P2MODE, C.main r0 P2REST])) (l, [s, m, sp])) := by
      unfold tableSends
      rw [fold_single _ C.h r0 hr0 (fun r hr hne => by
        rw [cpuP_p2i hr]
        rcases bit_of (p2_bitP h.cpu hr) with hq | hq
        · rw [hq]; split <;> split <;> decide
        · have hne' : C.main r CTR ≠ C.main r0 CTR := fun e => hne (h.jet_key_unique hr hr0 hq hp e)
          rw [if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)),
            if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)), add_zero'])]
      rw [cpuP_p2i hr0, hp]
      unfold Edges.oneIf
      simp only [List.cons.injEq, Option.some.injEq, Prod.mk.injEq, true_and, and_true]
      exact ite_ends _ _
    rw [hcpu, hpin] at hb
    have e := bal_sub hb
    rw [← ofN_add, ← ofN_add] at e
    have b1 := sumTo_le_one (f := fun q => if (pinEdges Pi (C.main r0 CTR)).act q &&
      decide ((pinEdges Pi (C.main r0 CTR)).outN q = (l, [s, m, sp])) then 1 else 0) (fun q => by split <;> decide) Pi.h
    have b2 := sumTo_le_one (f := fun q => if (pinEdges Pi (C.main r0 CTR)).act q &&
      decide ((pinEdges Pi (C.main r0 CTR)).inN q = (l, [s, m, sp])) then 1 else 0) (fun q => by split <;> decide) Pi.h
    have o1 : Edges.oneIf (some ((0 : F), [0, C.main r0 P2MODE, C.main r0 P2SP0])) (l, [s, m, sp]) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have o2 : Edges.oneIf (some (ofN P2_BITS, [0, C.main r0 P2MODE, C.main r0 P2REST])) (l, [s, m, sp]) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have hP : Pi.h + 1 < P := Nat.lt_of_le_of_lt (Nat.add_le_add_right h.pin_h 1) (by decide)
    have e' := ofN_inj (Nat.lt_of_le_of_lt (Nat.add_le_add o1 b1) (by rw [Nat.add_comm]; exact hP))
      (Nat.lt_of_le_of_lt (Nat.add_le_add o2 b2) (by rw [Nat.add_comm]; exact hP)) e
    show sumTo Pi.h _ + _ = sumTo Pi.h _ + _
    omega
/-- **`p2o` is a flow** at a jet row's key, from `(0, (rest, 0, 0, 1))` to `(496, (rest, 0, 0, 1))`. -/
theorem CompPOK.poutConserve {r0 : Nat} (hr0 : r0 < C.h) (hp : C.main r0 P2SEL = 1) :
    (poutEdges Po (C.main r0 CTR)).Conserve (some ((0 : F), [C.main r0 P2REST, 0, 0, 1])) (some (ofN P2_BITS, [C.main r0 P2REST, 0, 0, 1])) := by
  intro v
  obtain ⟨l, st⟩ := v
  have hCP : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  have zero_case : (∀ x y z w : F, st ≠ [x, y, z, w]) →
      (poutEdges Po (C.main r0 CTR)).cntOut (l, st) + Edges.oneIf (some ((0 : F), [C.main r0 P2REST, 0, 0, 1])) (l, st) =
        (poutEdges Po (C.main r0 CTR)).cntIn (l, st) + Edges.oneIf (some (ofN P2_BITS, [C.main r0 P2REST, 0, 0, 1])) (l, st) := by
    intro hst
    have z1 : (poutEdges Po (C.main r0 CTR)).cntOut (l, st) = 0 := sumTo_zero (fun q => by
      rw [show decide ((poutEdges Po (C.main r0 CTR)).outN q = (l, st)) = false from
        decide_eq_false (fun e => hst _ _ _ _ (congrArg Prod.snd e).symm), Bool.and_false]; rfl) _
    have z2 : (poutEdges Po (C.main r0 CTR)).cntIn (l, st) = 0 := sumTo_zero (fun q => by
      rw [show decide ((poutEdges Po (C.main r0 CTR)).inN q = (l, st)) = false from
        decide_eq_false (fun e => hst _ _ _ _ (congrArg Prod.snd e).symm), Bool.and_false]; rfl) _
    have o1 : Edges.oneIf (some ((0 : F), [C.main r0 P2REST, 0, 0, 1])) (l, st) = 0 :=
      if_neg (fun e => hst _ _ _ _ (congrArg Prod.snd (Option.some.inj e)).symm)
    have o2 : Edges.oneIf (some (ofN P2_BITS, [C.main r0 P2REST, 0, 0, 1])) (l, st) = 0 :=
      if_neg (fun e => hst _ _ _ _ (congrArg Prod.snd (Option.some.inj e)).symm)
    rw [z1, z2, o1, o2]
  match st with
  | [] => exact zero_case (fun _ _ _ _ e => by cases e)
  | [_] => exact zero_case (fun _ _ _ _ e => by cases e)
  | [_, _] => exact zero_case (fun _ _ _ _ e => by cases e)
  | [_, _, _] => exact zero_case (fun _ _ _ _ e => by cases e)
  | _ :: _ :: _ :: _ :: _ :: _ => exact zero_case (fun _ _ _ _ e => by cases e)
  | [a, b, c', d] =>
    have hb := h.bal "p2o" [C.main r0 CTR, l, a, b, c', d]
    simp only [compPTables, List.foldr_cons, List.foldr_nil] at hb
    rw [sends_nobus' (A := memAirC) rfl, sends_nobus' (A := progAirC heap N W) rfl,
      sends_nobus' (A := witAirP N W) rfl, sends_nobus' (A := segsAir roots) rfl,
      sends_nobus' (A := p2inAirB) rfl, sends_nobus' (A := p2AirB) (by decide),
      sends_nobus' (A := p2idxAir) rfl] at hb
    simp only [zero_add', add_zero'] at hb
    rw [poutB_sends Po _ _ (by decide)] at hb
    have hpin : tableSends p2outAir Po "p2o" [C.main r0 CTR, l, a, b, c', d] =
        ofN ((poutEdges Po (C.main r0 CTR)).cntOut (l, [a, b, c', d])) - ofN ((poutEdges Po (C.main r0 CTR)).cntIn (l, [a, b, c', d])) := by
      unfold tableSends
      rw [foldr_range_congr (f := fun q => rowSends p2outAir Po "p2o" [C.main r0 CTR, l, a, b, c', d] q) Po.h
        (fun q hq => pout_rowSends h.pout hq _ l a b c' d), fold_sub, fold_ofN, fold_ofN]
      rfl
    have hcpu : tableSends (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C "p2o" [C.main r0 CTR, l, a, b, c', d] =
        ofN (Edges.oneIf (some ((0 : F), [C.main r0 P2REST, 0, 0, 1])) (l, [a, b, c', d])) - ofN (Edges.oneIf (some (ofN P2_BITS, [C.main r0 P2REST, 0, 0, 1])) (l, [a, b, c', d])) := by
      unfold tableSends
      rw [fold_single _ C.h r0 hr0 (fun r hr hne => by
        rw [cpuP_p2o hr]
        rcases bit_of (p2_bitP h.cpu hr) with hq | hq
        · rw [hq]; split <;> split <;> decide
        · have hne' : C.main r CTR ≠ C.main r0 CTR := fun e => hne (h.jet_key_unique hr hr0 hq hp e)
          rw [if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)),
            if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)), add_zero'])]
      rw [cpuP_p2o hr0, hp]
      unfold Edges.oneIf
      simp only [List.cons.injEq, Option.some.injEq, Prod.mk.injEq, true_and, and_true]
      exact ite_ends _ _
    rw [hcpu, hpin] at hb
    have e := bal_sub hb
    rw [← ofN_add, ← ofN_add] at e
    have b1 := sumTo_le_one (f := fun q => if (poutEdges Po (C.main r0 CTR)).act q &&
      decide ((poutEdges Po (C.main r0 CTR)).outN q = (l, [a, b, c', d])) then 1 else 0) (fun q => by split <;> decide) Po.h
    have b2 := sumTo_le_one (f := fun q => if (poutEdges Po (C.main r0 CTR)).act q &&
      decide ((poutEdges Po (C.main r0 CTR)).inN q = (l, [a, b, c', d])) then 1 else 0) (fun q => by split <;> decide) Po.h
    have o1 : Edges.oneIf (some ((0 : F), [C.main r0 P2REST, 0, 0, 1])) (l, [a, b, c', d]) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have o2 : Edges.oneIf (some (ofN P2_BITS, [C.main r0 P2REST, 0, 0, 1])) (l, [a, b, c', d]) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have hP : Po.h + 1 < P := Nat.lt_of_le_of_lt (Nat.add_le_add_right h.pout_h 1) (by decide)
    have e' := ofN_inj (Nat.lt_of_le_of_lt (Nat.add_le_add o1 b1) (by rw [Nat.add_comm]; exact hP))
      (Nat.lt_of_le_of_lt (Nat.add_le_add o2 b2) (by rw [Nat.add_comm]; exact hP)) e
    show sumTo Po.h _ + _ = sumTo Po.h _ + _
    omega

/-- **P2IN's path** at a jet row: one active row per level, chained. -/
theorem CompPOK.pinPath {r0 : Nat} (hr0 : r0 < C.h) (hp : C.main r0 P2SEL = 1) :
    ∃ (e : Nat → Nat) (st : Nat → List F), st 0 = [0, C.main r0 P2MODE, C.main r0 P2SP0] ∧
      st P2_BITS = [0, C.main r0 P2MODE, C.main r0 P2REST] ∧
      (∀ i, i < P2_BITS → e i < Pi.h ∧ Pi.main (e i) 4 = 1 ∧ Pi.main (e i) 0 = C.main r0 CTR ∧
        Pi.main (e i) 1 = ofN i ∧ [Pi.main (e i) 3, Pi.main (e i) 13, Pi.main (e i) 14] = st i ∧
        [Pi.main (e i) 11, Pi.main (e i) 13, Pi.main (e i) 15] = st (i + 1)) ∧
      ∀ q, q < Pi.h → Pi.main q 4 = 1 → Pi.main q 0 = C.main r0 CTR → ∃ i, i < P2_BITS ∧ e i = q := by
  obtain ⟨e, st, h0, hk, hrows, hall⟩ := (pinEdges Pi (C.main r0 CTR)).path
    (Nat.lt_of_le_of_lt h.pin_h (by decide)) (k := P2_BITS) (by decide) (h.pinConserve hr0 hp)
  refine ⟨e, st, h0, hk, fun i hi => ?_, fun q hq ha hk' => ?_⟩
  · obtain ⟨hq, hact, hl, hs, hd⟩ := hrows i hi
    simp only [pinEdges, Bool.and_eq_true, decide_eq_true_eq] at hact
    exact ⟨hq, hact.1, hact.2, hl, hs, hd⟩
  · exact hall q hq (by simp only [pinEdges, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨ha, hk'⟩)

/-- **P2OUT's path** at a jet row. -/
theorem CompPOK.poutPath {r0 : Nat} (hr0 : r0 < C.h) (hp : C.main r0 P2SEL = 1) :
    ∃ (e : Nat → Nat) (st : Nat → List F), st 0 = [C.main r0 P2REST, 0, 0, 1] ∧
      st P2_BITS = [C.main r0 P2REST, 0, 0, 1] ∧
      (∀ i, i < P2_BITS → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = C.main r0 CTR ∧
        Po.main (e i) 1 = ofN i ∧ [Po.main (e i) 2, Po.main (e i) 4, Po.main (e i) 5, Po.main (e i) 6] = st i ∧
        [Po.main (e i) 2, Po.main (e i) 14, Po.main (e i) 17, Po.main (e i) 18] = st (i + 1)) ∧
      ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = C.main r0 CTR → ∃ i, i < P2_BITS ∧ e i = q := by
  obtain ⟨e, st, h0, hk, hrows, hall⟩ := (poutEdges Po (C.main r0 CTR)).path
    (Nat.lt_of_le_of_lt h.pout_h (by decide)) (k := P2_BITS) (by decide) (h.poutConserve hr0 hp)
  refine ⟨e, st, h0, hk, fun i hi => ?_, fun q hq ha hk' => ?_⟩
  · obtain ⟨hq, hact, hl, hs, hd⟩ := hrows i hi
    simp only [poutEdges, Bool.and_eq_true, decide_eq_true_eq] at hact
    exact ⟨hq, hact.1, hact.2, hl, hs, hd⟩
  · exact hall q hq (by simp only [poutEdges, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨ha, hk'⟩)

/-- An active P2IN row's level fields: `idxRow` of its level. -/
theorem CompPOK.pinLevel {q i : Nat} (hq : q < Pi.h) (ha : Pi.main q 4 = 1) (hl : Pi.main q 1 = ofN i)
    (hi : i < P2_BITS) : [Pi.main q 5, Pi.main q 6, Pi.main q 7, Pi.main q 8, Pi.main q 9] = (idxRow i).tail := by
  have cv := col_eval hq
  obtain ⟨x, hx, hv⟩ := h.idxHit ⟨(p2inAirB, Pi), by simp [compPTables], rfl, q, hq,
    ⟨"p2idx", 1, col 4, [col 1, col 5, col 6, col 7, col 8, col 9]⟩, List.mem_append_left _ List.mem_cons_self, rfl, rfl,
    by rw [cv, ha]⟩
  simp only [List.map_cons, List.map_nil, cv, hl] at hv
  exact idx_of h.pxpre hx hi hv

/-- An active P2OUT row's level fields: `idxRow` of its level. -/
theorem CompPOK.poutLevel {q i : Nat} (hq : q < Po.h) (ha : Po.main q 7 = 1) (hl : Po.main q 1 = ofN i)
    (hi : i < P2_BITS) : [Po.main q 8, Po.main q 9, Po.main q 10, Po.main q 11, Po.main q 12] = (idxRow i).tail := by
  have cv := col_eval hq
  obtain ⟨x, hx, hv⟩ := h.idxHit ⟨(p2outAirB, Po), by simp [compPTables], rfl, q, hq,
    ⟨"p2idx", 1, col 7, [col 1, col 8, col 9, col 10, col 11, col 12]⟩, List.mem_append_left _ List.mem_cons_self, rfl, rfl,
    by rw [cv, ha]⟩
  simp only [List.map_cons, List.map_nil, cv, hl] at hv
  exact idx_of h.pxpre hx hi hv

/-- **An active P2IN row reads its bit**: on the comb (`m = 0`) its slot,
    a `K` cell or `K I`; on the stack (`m = 1`) the stack cell at `sp`,
    pointing at the `K` slot or the `K I` slot, over `spn`. -/
theorem CompPOK.pinRead {q i : Nat} (hq : q < Pi.h) (ha : Pi.main q 4 = 1) (hl : Pi.main q 1 = ofN i)
    (hi : i < P2_BITS) (hm : Pi.main q 13 = 0 ∨ Pi.main q 13 = 1) :
    ∃ b : Bool, Pi.main q 2 = ofN b.toNat ∧
      ((Pi.main q 13 = 0 ∧ i + 3 < Mm.h ∧ (memOf Mm)[i + 3]? = some (if b then .K else .app 0 1)) ∨
       (Pi.main q 13 = 1 ∧ (Pi.main q 14).val < Mm.h ∧
         (memOf Mm)[(Pi.main q 14).val]? = some (.cons (P2Jet.bitPtr b) (Pi.main q 15).val))) := by
  have cv := col_eval hq
  have hm' := h.cell (h.memHit ⟨(p2inAirB, Pi), by simp [compPTables], rfl, q, hq,
    ⟨"mem", 1, col 4, [col 16, col 17, col 18, col 19]⟩,
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))), rfl, rfl, by rw [cv, ha]⟩)
  simp only [E.eval, cv] at hm'
  obtain ⟨e20, e21, _, e16, e17, e18, e19, _, _⟩ := pin_eqsR h.pin hq
  rw [ha] at e20 e21
  rcases bit_of (pin_eqs h.pin hq).1 with hb | hb
  · refine ⟨false, by rw [hb]; rfl, ?_⟩
    rcases hm with hm | hm
    · rw [hm] at e20 e21
      rw [show (1 : F) * (1 - 0) = 1 by decide] at e20
      rw [show (1 : F) * 0 = 0 by decide] at e21
      rw [e21, e20, zero_mul', zero_add', one_mul', hl] at e16
      rw [e21, e20, hb, zero_mul', zero_add', one_mul'] at e17 e19
      rw [e21, zero_mul'] at e18
      have hP : i + 3 < P := Nat.lt_trans (Nat.add_lt_add_right hi 3) (by decide)
      rw [e16, e17, e18, e19, ← ofN_add, val_ofN hP] at hm'
      exact .inl ⟨hm, hm'.1, by rw [hm'.2]; rfl⟩
    · rw [hm] at e20 e21
      rw [show (1 : F) * (1 - 1) = 0 by decide] at e20
      rw [one_mul'] at e21
      rw [e21, e20, one_mul', zero_mul', add_zero'] at e16 e17 e19
      rw [e21, hb, one_mul'] at e18
      rw [e16, e17, e18, e19] at hm'
      refine .inr ⟨hm, hm'.1, ?_⟩
      rw [hm'.2]; rfl
  · refine ⟨true, by rw [hb]; rfl, ?_⟩
    rcases hm with hm | hm
    · rw [hm] at e20 e21
      rw [show (1 : F) * (1 - 0) = 1 by decide] at e20
      rw [show (1 : F) * 0 = 0 by decide] at e21
      rw [e21, e20, zero_mul', zero_add', one_mul', hl] at e16
      rw [e21, e20, hb, zero_mul', zero_add', one_mul'] at e17 e19
      rw [e21, zero_mul'] at e18
      have hP : i + 3 < P := Nat.lt_trans (Nat.add_lt_add_right hi 3) (by decide)
      rw [e16, e17, e18, e19, ← ofN_add, val_ofN hP] at hm'
      exact .inl ⟨hm, hm'.1, by rw [hm'.2]; rfl⟩
    · rw [hm] at e20 e21
      rw [show (1 : F) * (1 - 1) = 0 by decide] at e20
      rw [one_mul'] at e21
      rw [e21, e20, one_mul', zero_mul', add_zero'] at e16 e17 e19
      rw [e21, hb, one_mul'] at e18
      rw [e16, e17, e18, e19] at hm'
      refine .inr ⟨hm, hm'.1, ?_⟩
      rw [hm'.2]; rfl

/-- **An active P2OUT row writes its stack cell.** -/
theorem CompPOK.poutWrite {q : Nat} (hq : q < Po.h) (ha : Po.main q 7 = 1) :
    (Po.main q 20).val < Mm.h ∧
      (memOf Mm)[(Po.main q 20).val]? = some (.cons (Po.main q 22).val (Po.main q 21).val) := by
  have cv := col_eval hq
  have hm := h.cell (h.memHit ⟨(p2outAirB, Po), by simp [compPTables], rfl, q, hq,
    ⟨"mem", 1, col 7, [col 20, c 5, col 22, col 21]⟩, (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))), rfl, rfl, by rw [cv, ha]⟩)
  simp only [E.eval, cv, B.c] at hm
  rw [cellOf_cons] at hm
  exact hm

omit h in
theorem idx_e (i : Nat) : (idxRow i).tail = [ofN (i / 31), ofN (2 ^ (i % 31)), ofN (if i % 31 = 30 then 1 else 0),
    ofN (if i % 31 < 27 then 1 else 0), ofN (if i = P2_BITS - 1 then 1 else 0)] := rfl

/-- **P2IN sends element `ε`'s value once**, at its last bit. -/
theorem CompPOK.pinSendsV {t : F} {e : Nat → Nat} {st : Nat → List F}
    (hrows : ∀ i, i < P2_BITS → e i < Pi.h ∧ Pi.main (e i) 4 = 1 ∧ Pi.main (e i) 0 = t ∧
      Pi.main (e i) 1 = ofN i ∧ [Pi.main (e i) 3, Pi.main (e i) 13, Pi.main (e i) 14] = st i ∧
      [Pi.main (e i) 11, Pi.main (e i) 13, Pi.main (e i) 15] = st (i + 1))
    (hall : ∀ q, q < Pi.h → Pi.main q 4 = 1 → Pi.main q 0 = t → ∃ i, i < P2_BITS ∧ e i = q)
    {ε : Nat} (he : ε < 16) (x : F) :
    tableSends p2inAir Pi "p2v" [t, ofN ε, x] = ofN (if Pi.main (e (31 * ε + 30)) 10 = x then 1 else 0) := by
  have hi0 : 31 * ε + 30 < P2_BITS := by unfold P2_BITS; omega
  obtain ⟨hq0, ha0, ht0, hl0, _, _⟩ := hrows _ hi0
  have hlev0 := h.pinLevel hq0 ha0 hl0 hi0
  rw [idx_e] at hlev0
  simp only [List.cons.injEq, and_true] at hlev0
  have hdiv : (31 * ε + 30) / 31 = ε := by omega
  have hmod : (31 * ε + 30) % 31 = 30 := by omega
  rw [hdiv, hmod, if_pos rfl] at hlev0
  unfold tableSends
  rw [fold_single _ Pi.h (e (31 * ε + 30)) hq0 (fun q hq hne => by
    rw [pin_rowSends_v hq]
    obtain ⟨_, _, _, em⟩ := pin_eqs h.pin hq
    rcases bit_of (pin_act h.pin hq) with ha | ha
    · rw [em, ha, zero_mul']; split <;> rfl
    · by_cases ht : Pi.main q 0 = t
      · obtain ⟨i, hi, rfl⟩ := hall q hq ha ht
        have hne' : i ≠ 31 * ε + 30 := fun e' => hne (by rw [e'])
        obtain ⟨_, _, _, hl, _, _⟩ := hrows i hi
        have hlev := h.pinLevel hq ha hl hi
        rw [idx_e] at hlev
        simp only [List.cons.injEq, and_true] at hlev
        by_cases h30 : i % 31 = 30
        · apply if_neg
          intro e'
          simp only [List.cons.injEq] at e'
          have := e'.2.1
          rw [hlev.1] at this
          exact ofN_ne_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans hi (by decide)))
            (Nat.lt_trans he (by decide)) (fun e2 => hne' (by omega)) this
        · rw [em, hlev.2.2.1, if_neg h30, ha]; split <;> rfl
      · exact if_neg (fun e' => ht (by simp only [List.cons.injEq] at e'; exact e'.1)))]
  rw [pin_rowSends_v hq0]
  obtain ⟨_, _, _, em⟩ := pin_eqs h.pin hq0
  rw [em, ha0, hlev0.2.2.1, hlev0.1, ht0, one_mul']
  by_cases hx : Pi.main (e (31 * ε + 30)) 10 = x
  · rw [if_pos (by rw [hx]), if_pos hx]
  · rw [if_neg (fun e' => hx (by simp only [List.cons.injEq] at e'; exact e'.2.2.1)), if_neg hx]; rfl

omit h in
/-- **The Poseidon2 table receives element `ε` at the key** once per active row with that input. -/
theorem p2SendsV (hs : Sat P2Air.p2Air Pp) {ε : Nat} (he : ε < 16) (t x : F) :
    tableSends P2Air.p2Air Pp "p2v" [t, ofN ε, x] = ofN 0 -
      ofN (sumTo Pp.h fun q => if Pp.main q P2Air.ACT = 1 ∧ Pp.main q P2Air.KEY = t ∧ Pp.main q ε = x then 1 else 0) := by
  unfold tableSends
  rw [foldr_range_congr (g := fun q => ofN 0 - ofN (if Pp.main q P2Air.ACT = 1 ∧ Pp.main q P2Air.KEY = t ∧
      Pp.main q ε = x then 1 else 0)) Pp.h (fun q hq => by
    rw [p2_rowSends_v hq he]
    rcases bit_of (p2_act hs hq) with ha | ha
    · rw [ha]
      have z : ¬ ((0 : F) = 1 ∧ Pp.main q P2Air.KEY = t ∧ Pp.main q ε = x) := fun h' => absurd h'.1 (by decide)
      rw [if_neg z]; split <;> decide
    · rw [ha]
      by_cases hc : Pp.main q P2Air.KEY = t ∧ Pp.main q ε = x
      · rw [if_pos hc, if_pos ⟨rfl, hc⟩]; decide
      · rw [if_neg hc, if_neg (fun h' => hc h'.2)]; decide), fold_sub, fold_ofN, fold_ofN,
    sumTo_zero (fun _ => rfl)]

/-- **The `p2v` count**: the active Poseidon2 rows at the key with input `x`
    for element `ε` number one if `x` is P2IN's value, else none. -/
theorem CompPOK.p2vCount {t : F} {e : Nat → Nat} {st : Nat → List F}
    (hrows : ∀ i, i < P2_BITS → e i < Pi.h ∧ Pi.main (e i) 4 = 1 ∧ Pi.main (e i) 0 = t ∧
      Pi.main (e i) 1 = ofN i ∧ [Pi.main (e i) 3, Pi.main (e i) 13, Pi.main (e i) 14] = st i ∧
      [Pi.main (e i) 11, Pi.main (e i) 13, Pi.main (e i) 15] = st (i + 1))
    (hall : ∀ q, q < Pi.h → Pi.main q 4 = 1 → Pi.main q 0 = t → ∃ i, i < P2_BITS ∧ e i = q)
    {ε : Nat} (he : ε < 16) (x : F) :
    (sumTo Pp.h fun q => if Pp.main q P2Air.ACT = 1 ∧ Pp.main q P2Air.KEY = t ∧ Pp.main q ε = x then 1 else 0) =
      if Pi.main (e (31 * ε + 30)) 10 = x then 1 else 0 := by
  have hb := h.bal "p2v" [t, ofN ε, x]
  simp only [compPTables, List.foldr_cons, List.foldr_nil] at hb
  rw [sends_nobus' (A := cpuAirP2 hd0 stk0 ctr0 n nilA J root) (by show cpuIntersP2.all _ = true; decide), sends_nobus' (A := memAirC) rfl,
    sends_nobus' (A := progAirC heap N W) rfl, sends_nobus' (A := witAirP N W) rfl,
    sends_nobus' (A := segsAir roots) rfl, sends_nobus' (A := p2outAirB) rfl,
    sends_nobus' (A := p2idxAir) rfl, pinB_sends Pi _ _ (by decide), p2B_sends Pp _ _ (by decide),
    h.pinSendsV hrows hall he x, p2SendsV h.p2 he t x] at hb
  simp only [zero_add', add_zero'] at hb
  rw [ofN_zero] at hb
  have e1 := eq_of_add_zero_sub hb
  have hc := sumTo_le_one (f := fun q => if Pp.main q P2Air.ACT = 1 ∧ Pp.main q P2Air.KEY = t ∧
    Pp.main q ε = x then 1 else 0) (fun q => by split <;> decide) Pp.h
  have hP : Pp.h + 1 < P := Nat.lt_of_le_of_lt (Nat.add_le_add_right h.p2_h 1) (by decide)
  have e2 := ofN_inj (by split <;> omega) (by omega) e1
  omega

/-- **One Poseidon2 row per call**: exactly one active row at the key, and
    its inputs are P2IN's elements. -/
theorem CompPOK.p2Unique {t : F} {e : Nat → Nat} {st : Nat → List F}
    (hrows : ∀ i, i < P2_BITS → e i < Pi.h ∧ Pi.main (e i) 4 = 1 ∧ Pi.main (e i) 0 = t ∧
      Pi.main (e i) 1 = ofN i ∧ [Pi.main (e i) 3, Pi.main (e i) 13, Pi.main (e i) 14] = st i ∧
      [Pi.main (e i) 11, Pi.main (e i) 13, Pi.main (e i) 15] = st (i + 1))
    (hall : ∀ q, q < Pi.h → Pi.main q 4 = 1 → Pi.main q 0 = t → ∃ i, i < P2_BITS ∧ e i = q) :
    ∃ qs, qs < Pp.h ∧ Pp.main qs P2Air.ACT = 1 ∧ Pp.main qs P2Air.KEY = t ∧
      (∀ ε, ε < 16 → Pp.main qs ε = Pi.main (e (31 * ε + 30)) 10) ∧
      ∀ q, q < Pp.h → Pp.main q P2Air.ACT = 1 → Pp.main q P2Air.KEY = t → q = qs := by
  have inputs : ∀ q, q < Pp.h → Pp.main q P2Air.ACT = 1 → Pp.main q P2Air.KEY = t →
      ∀ ε, ε < 16 → Pp.main q ε = Pi.main (e (31 * ε + 30)) 10 := by
    intro q hq ha hk ε he
    have hge := sumTo_ge (f := fun q' => if Pp.main q' P2Air.ACT = 1 ∧ Pp.main q' P2Air.KEY = t ∧
      Pp.main q' ε = Pp.main q ε then 1 else 0) Pp.h q hq
    rw [h.p2vCount hrows hall he, if_pos ⟨ha, hk, rfl⟩] at hge
    by_cases hv : Pi.main (e (31 * ε + 30)) 10 = Pp.main q ε
    · exact hv.symm
    · rw [if_neg hv] at hge; exact absurd hge (by decide)
  have hc0 := h.p2vCount hrows hall (ε := 0) (by decide) (Pi.main (e (31 * 0 + 30)) 10)
  rw [if_pos rfl] at hc0
  obtain ⟨qs, hqs, hpos⟩ := sumTo_pos _ (by rw [hc0]; decide)
  have hcond : Pp.main qs P2Air.ACT = 1 ∧ Pp.main qs P2Air.KEY = t ∧
      Pp.main qs 0 = Pi.main (e (31 * 0 + 30)) 10 := by
    by_cases c : Pp.main qs P2Air.ACT = 1 ∧ Pp.main qs P2Air.KEY = t ∧
        Pp.main qs 0 = Pi.main (e (31 * 0 + 30)) 10
    · exact c
    · simp only [if_neg c] at hpos; exact absurd hpos (by decide)
  refine ⟨qs, hqs, hcond.1, hcond.2.1, inputs qs hqs hcond.1 hcond.2.1, fun q hq ha hk => ?_⟩
  apply Decidable.byContradiction
  intro hne
  have h2 := sumTo_two (f := fun q' => if Pp.main q' P2Air.ACT = 1 ∧ Pp.main q' P2Air.KEY = t ∧
    Pp.main q' 0 = Pi.main (e (31 * 0 + 30)) 10 then 1 else 0) Pp.h q qs hq hqs hne
  rw [hc0, if_pos ⟨ha, hk, inputs q hq ha hk 0 (by decide)⟩, if_pos hcond] at h2
  exact absurd h2 (by decide)

/-- **P2OUT receives element `ε`'s value once**, at its last bit. -/
theorem CompPOK.poutSendsW {t : F} {e : Nat → Nat} {st : Nat → List F}
    (hrows : ∀ i, i < P2_BITS → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = t ∧
      Po.main (e i) 1 = ofN i ∧ [Po.main (e i) 2, Po.main (e i) 4, Po.main (e i) 5, Po.main (e i) 6] = st i ∧
      [Po.main (e i) 2, Po.main (e i) 14, Po.main (e i) 17, Po.main (e i) 18] = st (i + 1))
    (hall : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = t → ∃ i, i < P2_BITS ∧ e i = q)
    {ε : Nat} (he : ε < 16) (y : F) :
    tableSends p2outAir Po "p2w" [t, ofN ε, y] = 0 - ofN (if Po.main (e (31 * ε + 30)) 13 = y then 1 else 0) := by
  have hi0 : 31 * ε + 30 < P2_BITS := by unfold P2_BITS; omega
  obtain ⟨hq0, ha0, ht0, hl0, _, _⟩ := hrows _ hi0
  have hlev0 := h.poutLevel hq0 ha0 hl0 hi0
  rw [idx_e] at hlev0
  simp only [List.cons.injEq, and_true] at hlev0
  have hdiv : (31 * ε + 30) / 31 = ε := by omega
  have hmod : (31 * ε + 30) % 31 = 30 := by omega
  rw [hdiv, hmod, if_pos rfl] at hlev0
  unfold tableSends
  rw [fold_single _ Po.h (e (31 * ε + 30)) hq0 (fun q hq hne => by
    rw [pout_rowSends_w hq]
    have em := (pout_eqs h.pout hq).2.2.2.2.2.2.2.2.1
    rcases bit_of (pout_act h.pout hq) with ha | ha
    · rw [em, ha, zero_mul']; split <;> decide
    · by_cases ht : Po.main q 0 = t
      · obtain ⟨i, hi, rfl⟩ := hall q hq ha ht
        have hne' : i ≠ 31 * ε + 30 := fun e' => hne (by rw [e'])
        obtain ⟨_, _, _, hl, _, _⟩ := hrows i hi
        have hlev := h.poutLevel hq ha hl hi
        rw [idx_e] at hlev
        simp only [List.cons.injEq, and_true] at hlev
        by_cases h30 : i % 31 = 30
        · apply if_neg
          intro e'
          simp only [List.cons.injEq] at e'
          have := e'.2.1
          rw [hlev.1] at this
          exact ofN_ne_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans hi (by decide)))
            (Nat.lt_trans he (by decide)) (fun e2 => hne' (by omega)) this
        · rw [em, hlev.2.2.1, if_neg h30, ha]; split <;> decide
      · exact if_neg (fun e' => ht (by simp only [List.cons.injEq] at e'; exact e'.1)))]
  rw [pout_rowSends_w hq0]
  have em := (pout_eqs h.pout hq0).2.2.2.2.2.2.2.2.1
  rw [em, ha0, hlev0.2.2.1, hlev0.1, ht0, one_mul']
  by_cases hx : Po.main (e (31 * ε + 30)) 13 = y
  · rw [if_pos (by rw [hx]), if_pos hx]; decide
  · rw [if_neg (fun e' => hx (by simp only [List.cons.injEq] at e'; exact e'.2.2.1)), if_neg hx]; decide

/-- **The Poseidon2 row's outputs are P2OUT's elements.** -/
theorem CompPOK.p2wMatch {t : F} {e : Nat → Nat} {st : Nat → List F}
    (hrows : ∀ i, i < P2_BITS → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = t ∧
      Po.main (e i) 1 = ofN i ∧ [Po.main (e i) 2, Po.main (e i) 4, Po.main (e i) 5, Po.main (e i) 6] = st i ∧
      [Po.main (e i) 2, Po.main (e i) 14, Po.main (e i) 17, Po.main (e i) 18] = st (i + 1))
    (hall : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = t → ∃ i, i < P2_BITS ∧ e i = q)
    {qs : Nat} (hqs : qs < Pp.h) (hact : Pp.main qs P2Air.ACT = 1) (hkey : Pp.main qs P2Air.KEY = t)
    (huniq : ∀ q, q < Pp.h → Pp.main q P2Air.ACT = 1 → Pp.main q P2Air.KEY = t → q = qs)
    {ε : Nat} (he : ε < 16) :
    (P2Air.p2Out.getD ε (c 0)).eval (Pp.env qs) = Po.main (e (31 * ε + 30)) 13 := by
  let y := Po.main (e (31 * ε + 30)) 13
  have hp2 : tableSends P2Air.p2Air Pp "p2w" [t, ofN ε, y] =
      ofN (if (P2Air.p2Out.getD ε (c 0)).eval (Pp.env qs) = y then 1 else 0) := by
    unfold tableSends
    rw [fold_single _ Pp.h qs hqs (fun q hq hne => by
      rw [p2_rowSends_w hq he]
      rcases bit_of (p2_act h.p2 hq) with ha | ha
      · rw [ha]; split <;> rfl
      · exact if_neg (fun h' => hne (huniq q hq ha h'.1)))]
    rw [p2_rowSends_w hqs he, hact]
    by_cases hc : (P2Air.p2Out.getD ε (c 0)).eval (Pp.env qs) = y
    · rw [if_pos ⟨hkey, hc⟩, if_pos hc]; rfl
    · rw [if_neg (fun h' => hc h'.2), if_neg hc]; rfl
  have hb := h.bal "p2w" [t, ofN ε, y]
  simp only [compPTables, List.foldr_cons, List.foldr_nil] at hb
  rw [sends_nobus' (A := cpuAirP2 hd0 stk0 ctr0 n nilA J root) (by show cpuIntersP2.all _ = true; decide),
    sends_nobus' (A := memAirC) rfl, sends_nobus' (A := progAirC heap N W) rfl,
    sends_nobus' (A := witAirP N W) rfl, sends_nobus' (A := segsAir roots) rfl,
    sends_nobus' (A := p2inAirB) rfl, sends_nobus' (A := p2idxAir) rfl,
    poutB_sends Po _ _ (by decide), p2B_sends Pp _ _ (by decide), h.poutSendsW hrows hall he y, hp2, if_pos rfl] at hb
  simp only [zero_add', add_zero'] at hb
  have e1 := eq_of_add_zero_sub (by rw [add_comm']; exact hb)
  by_cases hc : (P2Air.p2Out.getD ε (c 0)).eval (Pp.env qs) = y
  · exact hc
  · rw [if_neg hc] at e1; exact absurd e1.symm (by decide)

end

end Circuit
