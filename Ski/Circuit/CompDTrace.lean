import Ski.Circuit.CompDCompleteFinal

/-!
# The honest DEC rows

`bench/plonky3/src/decair.rs`'s `dec_row_values` in Lean: a DEC row of a
jet call (`DecT.DR`: the call's key, the row's kind, role, mode, pointer,
level, borrow, write count, bit, last flag and verdict) and its columns
over the memory `A` (`DecT.DR.col`).  A row reads its kind's pattern
(`DecT.patOf`) slot by slot, each slot's address the row's pointer or a
field of an earlier slot (`DecT.slots`), its tag the pattern's, its
fields the memory cell's; the columns the constraints define are their
right-hand sides.

**`DecT.row_sat`**: a row that is well formed (`DecT.RowOK`: a kind, a
role, canonical, its head level below `W`, its active slots below the
key) satisfies every one of `Dec.decAir`'s constraints.
-/

namespace Circuit

open B Air

namespace DecT

/-- A slot's address, tag and fields. -/
abbrev Sl := Nat × Nat × Nat × Nat

/-- **A DEC row**, before its slots. -/
structure DR where
  key : Nat
  kind : Nat
  ro : Nat
  m : Bool
  p : Nat
  lvl : Nat
  bw : Bool
  wc : Nat
  bit : Bool
  last : Bool
  err : Bool

/-- A kind's pattern; the nil reads `K` at its pointer. -/
def patOf (k : Nat) : List (Dec.Src × Dec.Tg) :=
  if k = 1 then Dec.cellSlots else if k = 2 then Dec.atomSlots else if k = 3 then Dec.consSlots
  else if k = 4 then [(.rowP, .C 1)] else []

def srcN (out : List Sl) (p : Nat) : Dec.Src → Nat
  | .rowP => p
  | .F1 i => (out.getD i (0, 0, 0, 0)).2.2.1
  | .F2 i => (out.getD i (0, 0, 0, 0)).2.2.2

def tgN (bit last : Bool) : Dec.Tg → Nat
  | .C n => n
  | .BitTag => if bit then 1 else 3
  | .LastTag => if last then 1 else 3

/-- A slot read from the memory. -/
def mk (A : List Cell) (p : Nat) (bit last : Bool) (out : List Sl) (st : Dec.Src × Dec.Tg) : Sl :=
  let a := srcN out p st.1
  (a, tgN bit last st.2, (cellFields (A.getD a .nil)).1, (cellFields (A.getD a .nil)).2)

def step (A : List Cell) (p : Nat) (bit last : Bool) (out : List Sl) (st : Dec.Src × Dec.Tg) : List Sl :=
  out ++ [mk A p bit last out st]

/-- **The row's slots**, read in order. -/
def slots (A : List Cell) (d : DR) : List Sl := (patOf d.kind).foldl (step A d.p d.bit d.last) []

def sl (A : List Cell) (d : DR) (j : Nat) : Sl := (slots A d).getD j (0, 0, 0, 0)

/-- Whether slot `j` reads: in the pattern, and not a gated slot of a set bit. -/
def act (d : DR) (j : Nat) : Bool :=
  decide (j < (patOf d.kind).length) && !(decide (d.kind = 3) && (j == 12 || j == 13) && d.bit)

section Vals
variable (d : DR)
def kc : F := bF (decide (d.kind = 1))
def ka : F := bF (decide (d.kind = 2))
def ks : F := bF (decide (d.kind = 3))
def kn : F := bF (decide (d.kind = 4))
def h0 : F := bF (decide ((d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 0))
def h1 : F := bF (decide ((d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 1))
def vBW : F := bF d.bw
def vBIT : F := bF d.bit
def vL : F := bF d.last
def vM : F := bF d.m
def vDROP : F := vBW d * vBIT d * vL d
def vWR : F := vBW d - vDROP d
def vWL : F := vBW d * vBIT d * (1 - vL d)
def vSUB : F := kc d * h0 d
end Vals

/-- **The row's columns** over the memory `A`. -/
def DR.col (A : List Cell) (d : DR) (c : Nat) : F :=
  if c < Dec.LB then
    match c with
    | 0 => ofN d.key
    | 1 => kc d
    | 2 => ka d
    | 3 => ks d
    | 4 => kn d
    | 5 => ofN d.ro
    | 6 => h0 d
    | 7 => h1 d
    | 8 => ofN d.p
    | 9 => ofN d.lvl
    | 10 => vBW d
    | 11 => ofN d.wc
    | 12 => vBIT d
    | 13 => vL d
    | 14 => vBW d * (1 - vBIT d)
    | 15 => vDROP d
    | 16 => vWR d
    | 17 => vWL d
    | 18 => ofN d.wc + ofN 6 * vWR d
    | 19 => ks d * (1 - vDROP d) * (ofN d.key + ofN 12 + ofN 6 * ofN d.lvl)
    | 20 => ks d * (ofN 2 - ofN 2 * (vBIT d + vBW d - ofN 2 * vBIT d * vBW d))
    | 21 => bF d.err
    | 22 => vM d
    | 23 => ks d * (1 - vL d)
    | 24 => ks d * vL d * (1 - vM d)
    | 25 => kn d * (1 - vM d)
    | 26 => vSUB d
    | 27 => kc d * h1 d
    | 28 => ka d * h0 d
    | 29 => ka d * h1 d
    | 30 => ks d * vWR d
    | 31 => ks d * vWL d
    | 32 => ks d * vBW d
    | 33 => kn d * vBW d
    | 34 => vSUB d * bF d.err
    | 35 => ks d * (1 - vBIT d)
    | _ => 0
  else if c < Dec.ADDR then
    (if d.kind = 3 ∧ d.m = false then ofN ((d.lvl / 2 ^ (c - Dec.LB)) % 2) else 0)
  else if c < Dec.TAG then ofN (sl A d (c - Dec.ADDR)).1
  else if c < Dec.DFLD then ofN (sl A d (c - Dec.TAG)).2.1
  else if c < Dec.DBITS then
    (if (c - Dec.DFLD) % 2 = 0 then ofN (sl A d ((c - Dec.DFLD) / 2)).2.2.1
     else ofN (sl A d ((c - Dec.DFLD) / 2)).2.2.2)
  else if c < Dec.WIDTH then
    (if act d ((c - Dec.DBITS) / RANGE_BITS) then
      ofN (((d.key - (sl A d ((c - Dec.DBITS) / RANGE_BITS)).1 - 1) / 2 ^ ((c - Dec.DBITS) % RANGE_BITS)) % 2)
     else 0)
  else 0

/-- The row as a one-row table. -/
def rowT (A : List Cell) (d : DR) : Table := ⟨1, fun _ c => d.col A c, fun _ _ => 0⟩

/-- The row as a vector. -/
def vec (A : List Cell) (d : DR) : List F := (List.range Dec.WIDTH).map (d.col A)

/-- **A well-formed row**: a kind, a role, canonical, its head's level below
    `W`, its active slots below the key, the key within the range checks. -/
structure RowOK (A : List Cell) (d : DR) : Prop where
  kind : 1 ≤ d.kind ∧ d.kind ≤ 4
  ro : d.ro ≤ 2
  canon : d.kind = 3 → d.last = true → d.bit = true
  lvl : d.kind = 3 → d.m = false → d.lvl < 32
  key : d.key < 2 ^ 24
  below : ∀ j, act d j = true → (sl A d j).1 < d.key


-- ---------------------------------------------------------------------------
-- The slots, read in order
-- ---------------------------------------------------------------------------

theorem foldl_step (A : List Cell) (p : Nat) (bit last : Bool) : ∀ (pat : List (Dec.Src × Dec.Tg)) (out : List Sl),
    (pat.foldl (step A p bit last) out).length = out.length + pat.length ∧
    (pat.foldl (step A p bit last) out).take out.length = out ∧
    ∀ j (h : j < pat.length), (pat.foldl (step A p bit last) out)[out.length + j]? =
      some (mk A p bit last ((pat.foldl (step A p bit last) out).take (out.length + j)) pat[j])
  | [], out => ⟨by simp, by simp, fun j h => absurd h (Nat.not_lt_zero _)⟩
  | st :: rest, out => by
    obtain ⟨h1, h2, h3⟩ := foldl_step A p bit last rest (step A p bit last out st)
    have hl : (step A p bit last out st).length = out.length + 1 := by simp [step]
    rw [List.foldl_cons]
    refine ⟨by rw [h1, hl, List.length_cons]; omega, ?_, ?_⟩
    · have : ((rest.foldl (step A p bit last) (step A p bit last out st)).take (out.length + 1)).take out.length = out := by
        rw [← hl, h2]; simp [step]
      rw [List.take_take, Nat.min_eq_left (Nat.le_succ _)] at this
      exact this
    · intro j hj
      cases j with
      | zero =>
        have e : (rest.foldl (step A p bit last) (step A p bit last out st))[out.length]? = some (mk A p bit last out st) := by
          have := congrArg (fun l => l[out.length]?) h2
          rw [hl, List.getElem?_take, if_pos (Nat.lt_succ_self _)] at this
          rw [this]; simp [step]
        have e2 : (rest.foldl (step A p bit last) (step A p bit last out st)).take out.length = out := by
          have : ((rest.foldl (step A p bit last) (step A p bit last out st)).take (out.length + 1)).take out.length = out := by
            rw [← hl, h2]; simp [step]
          rw [List.take_take, Nat.min_eq_left (Nat.le_succ _)] at this
          exact this
        rw [Nat.add_zero, e, e2]; rfl
      | succ j =>
        have := h3 j (by simp at hj; omega)
        rw [hl, show out.length + 1 + j = out.length + (j + 1) by omega] at this
        rw [this]; rfl

theorem slots_length (A : List Cell) (d : DR) : (slots A d).length = (patOf d.kind).length := by
  have := (foldl_step A d.p d.bit d.last (patOf d.kind) []).1
  simp only [List.length_nil, Nat.zero_add] at this
  exact this

theorem sl_get (A : List Cell) (d : DR) {j : Nat} (hj : j < (patOf d.kind).length) :
    sl A d j = mk A d.p d.bit d.last ((slots A d).take j) (patOf d.kind)[j] := by
  have := (foldl_step A d.p d.bit d.last (patOf d.kind) []).2.2 j hj
  simp only [List.length_nil, Nat.zero_add] at this
  unfold sl slots
  rw [List.getD_eq_getElem?_getD, this]; rfl

theorem sl_none (A : List Cell) (d : DR) {j : Nat} (hj : (patOf d.kind).length ≤ j) : sl A d j = (0, 0, 0, 0) := by
  unfold sl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [slots_length]; exact hj)]; rfl

/-- A source reads only earlier slots. -/
def refsLt (j : Nat) : Dec.Src → Bool
  | .rowP => true
  | .F1 i => decide (i < j)
  | .F2 i => decide (i < j)

def patRefs (pat : List (Dec.Src × Dec.Tg)) : Bool :=
  (List.range pat.length).all fun j => match pat[j]? with
    | some st => refsLt j st.1
    | none => true

theorem patRefs_all : ∀ k, patRefs (patOf k) = true := by
  intro k
  unfold patOf
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split
        · decide
        · decide

theorem pat_refs (k : Nat) {j : Nat} (hj : j < (patOf k).length) : refsLt j (patOf k)[j].1 = true := by
  have := List.all_eq_true.1 (patRefs_all k) j (List.mem_range.2 hj)
  rw [List.getElem?_eq_getElem hj] at this
  exact this

theorem srcN_take (out : List Sl) (p j : Nat) (s : Dec.Src) (h : refsLt j s = true) :
    srcN (out.take j) p s = srcN out p s := by
  cases s with
  | rowP => rfl
  | F1 i =>
    simp only [refsLt, decide_eq_true_eq] at h
    simp only [srcN, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]
  | F2 i =>
    simp only [refsLt, decide_eq_true_eq] at h
    simp only [srcN, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]

/-- **Slot `j` of the pattern**: its address the source over the earlier
    slots, its tag the pattern's, its fields the memory cell's. -/
theorem sl_spec (A : List Cell) (d : DR) {j : Nat} (hj : j < (patOf d.kind).length) :
    (sl A d j).1 = srcN (slots A d) d.p (patOf d.kind)[j].1 ∧
    (sl A d j).2.1 = tgN d.bit d.last (patOf d.kind)[j].2 ∧
    (sl A d j).2.2 = cellFields (A.getD (sl A d j).1 .nil) := by
  rw [sl_get A d hj]
  simp only [mk]
  rw [srcN_take _ _ _ _ (pat_refs d.kind hj)]
  refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial


-- ---------------------------------------------------------------------------
-- The columns' constraints, from the columns' facts
-- ---------------------------------------------------------------------------

/-- The first constraints, the kinds' and the defined columns'. -/
def cons35 : List E := Dec.decCons.take 35

theorem decCons_split : Dec.decCons = cons35 ++ ((List.range Dec.NLB).map (fun i => B.bool (col (Dec.LB + i))) ++
    [.mul (.mul (col Dec.KCONS) (.sub one (col Dec.MODE))) (.sub (col Dec.LVL) Dec.levelVal)] ++
    (List.range Dec.NSLOT).flatMap Dec.slotCons) := by
  unfold cons35 Dec.decCons; simp

/-- **The columns' facts give the first constraints.** -/
theorem cons35_of {D : Table} {q : Nat} (hq : q < D.h) (hf : DecRowF D q) : ∀ e ∈ cons35, e.eval (D.env q) = 0 := by
  intro e he
  simp only [cons35, Dec.decCons, List.cons_append, List.take_succ_cons, List.take_zero, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [E.eval, B.bool, B.eq, B.one, B.c, col_eval hq, ofN_one, Dec.aE]
  · rcases hf.kcell with h | h <;> rw [h] <;> decide
  · rcases hf.katom with h | h <;> rw [h] <;> decide
  · rcases hf.kcons with h | h <;> rw [h] <;> decide
  · rcases hf.knil with h | h <;> rw [h] <;> decide
  · rcases hf.ksum with h | h <;> rw [h] <;> decide
  · rcases hf.h0 with h | h <;> rw [h] <;> decide
  · rcases hf.h1 with h | h <;> rw [h] <;> decide
  · exact hf.h01
  · exact hf.ro
  · rcases hf.bit with h | h <;> rw [h] <;> decide
  · rcases hf.last with h | h <;> rw [h] <;> decide
  · rcases hf.bw with h | h <;> rw [h] <;> decide
  · rcases hf.err with h | h <;> rw [h] <;> decide
  · rcases hf.mode with h | h <;> rw [h] <;> decide
  · exact hf.canon
  · rw [hf.nbw]; exact sub_self' _
  · rw [hf.dropped]; exact sub_self' _
  · rw [hf.writes]; exact sub_self' _
  · rw [hf.wl]; exact sub_self' _
  · rw [hf.wcn]; exact sub_self' _
  · rw [hf.nextl]; exact sub_self' _
  · rw [hf.ptr]; exact sub_self' _
  · rw [hf.csend]; exact sub_self' _
  · rw [hf.done0]; exact sub_self' _
  · rw [hf.done1]; exact sub_self' _
  · rw [hf.sub]; exact sub_self' _
  · rw [hf.hc]; exact sub_self' _
  · rw [hf.asub]; exact sub_self' _
  · rw [hf.hat]; exact sub_self' _
  · rw [hf.cw]; exact sub_self' _
  · rw [hf.cwl]; exact sub_self' _
  · rw [hf.clk]; exact sub_self' _
  · rw [hf.nlk]; exact sub_self' _
  · rw [hf.suberr]; exact sub_self' _
  · rw [hf.cg]; exact sub_self' _


-- ---------------------------------------------------------------------------
-- The row's columns, by block
-- ---------------------------------------------------------------------------

section Cols
variable (A : List Cell) (d : DR)

theorem col_lb {i : Nat} (hi : i < Dec.NLB) :
    d.col A (Dec.LB + i) = if d.kind = 3 ∧ d.m = false then ofN ((d.lvl / 2 ^ i) % 2) else 0 := by
  unfold DR.col; simp only [Dec.ADDR, Dec.LB, Dec.NLB] at hi ⊢
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem col_addr {j : Nat} (hj : j < Dec.NSLOT) : d.col A (Dec.ADDR + j) = ofN (sl A d j).1 := by
  unfold DR.col; simp only [Dec.ADDR, Dec.TAG, Dec.LB, Dec.NLB, Dec.NSLOT] at hj ⊢
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; simp

theorem col_tag {j : Nat} (hj : j < Dec.NSLOT) : d.col A (Dec.TAG + j) = ofN (sl A d j).2.1 := by
  unfold DR.col; simp only [Dec.ADDR, Dec.TAG, Dec.DFLD, Dec.LB, Dec.NLB, Dec.NSLOT] at hj ⊢
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; simp

theorem col_f1 {i : Nat} (hi : i < Dec.NSLOT) : d.col A (Dec.DFLD + 2 * i) = ofN (sl A d i).2.2.1 := by
  unfold DR.col; simp only [Dec.ADDR, Dec.TAG, Dec.DFLD, Dec.DBITS, Dec.LB, Dec.NLB, Dec.NSLOT] at hi ⊢
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_pos (by omega)]; simp

theorem col_f2 {i : Nat} (hi : i < Dec.NSLOT) : d.col A (Dec.DFLD + 2 * i + 1) = ofN (sl A d i).2.2.2 := by
  unfold DR.col; simp only [Dec.ADDR, Dec.TAG, Dec.DFLD, Dec.DBITS, Dec.LB, Dec.NLB, Dec.NSLOT] at hi ⊢
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_neg (by omega)]
  have e2 : (36 + 5 + 25 + 25 + 2 * i + 1 - (36 + 5 + 25 + 25)) / 2 = i := by omega
  rw [e2]

theorem col_bits {j i : Nat} (hj : j < Dec.NSLOT) (hi : i < RANGE_BITS) :
    d.col A (Dec.DBITS + j * RANGE_BITS + i) =
      if act d j then ofN (((d.key - (sl A d j).1 - 1) / 2 ^ i) % 2) else 0 := by
  have e1 : (Dec.DBITS + j * RANGE_BITS + i - Dec.DBITS) / RANGE_BITS = j := by
    rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide),
      Nat.div_eq_of_lt hi, Nat.zero_add]
  have e2 : (Dec.DBITS + j * RANGE_BITS + i - Dec.DBITS) % RANGE_BITS = i := by
    rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  unfold DR.col
  rw [e1, e2]
  simp only [Dec.ADDR, Dec.TAG, Dec.DFLD, Dec.DBITS, Dec.WIDTH, Dec.LB, Dec.NLB, Dec.NSLOT, RANGE_BITS] at hi hj ⊢
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]

theorem col_wide {c : Nat} (hc : Dec.WIDTH ≤ c) : d.col A c = 0 := by
  unfold DR.col; simp only [Dec.ADDR, Dec.TAG, Dec.DFLD, Dec.DBITS, Dec.WIDTH, Dec.LB, Dec.NLB, Dec.NSLOT,
    RANGE_BITS] at hc ⊢
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

end Cols

theorem bF_01 (b : Bool) : bF b = 0 ∨ bF b = 1 := by cases b <;> simp [bF]

theorem ofN_bit01 (n : Nat) : ofN (n % 2) = 0 ∨ ofN (n % 2) = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h]
  · exact .inl rfl
  · exact .inr rfl

theorem kind_cases {k : Nat} (h : 1 ≤ k ∧ k ≤ 4) : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega

theorem env0 (A : List Cell) (d : DR) (i : Nat) : (col i).eval ((rowT A d).env 0) = d.col A i := rfl

section Row
variable {A : List Cell} {d : DR} (hok : RowOK A d)
include hok

/-- **The row's columns' facts.** -/
theorem rowF : DecRowF (rowT A d) 0 := by
  have hk := kind_cases hok.kind
  have hro := hok.ro
  refine ⟨bF_01 _, bF_01 _, bF_01 _, bF_01 _, ?_, bF_01 _, bF_01 _, ?_, ?_, bF_01 _, bF_01 _, bF_01 _, bF_01 _,
    bF_01 _, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · show kc d + ka d + ks d + kn d = 0 ∨ kc d + ka d + ks d + kn d = 1
    rcases hk with h | h | h | h <;> simp only [kc, ka, ks, kn, h] <;> decide
  · show h0 d * h1 d = 0
    have : d.ro = 0 ∨ d.ro = 1 ∨ d.ro = 2 := by omega
    rcases hk with h | h | h | h <;> rcases this with h' | h' | h' <;> simp only [h0, h1, h, h'] <;> decide
  · show (kc d + ka d) * (ofN d.ro - (h1 d + ofN 2 * (1 - h0 d - h1 d))) = 0
    have : d.ro = 0 ∨ d.ro = 1 ∨ d.ro = 2 := by omega
    rcases hk with h | h | h | h <;> rcases this with h' | h' | h' <;> simp only [kc, ka, h0, h1, h, h'] <;> decide
  · show ks d * vL d * (1 - vBIT d) = 0
    by_cases h : d.kind = 3
    · have hc := hok.canon h
      simp only [ks, vL, vBIT, h]
      cases hl : d.last
      · simp only [bF]; exact zero_mul' _
      · rw [hc hl]; decide
    · simp only [ks, h]; simp [bF, zero_mul']

theorem rowK : DKind (rowT A d) 0 d.kind := by
  refine ⟨by have := hok.kind; omega, ?_, ?_, ?_, ?_⟩ <;>
    simp only [rowT, DR.col, kc, ka, ks, kn, bF, Dec.KCELL, Dec.KATOM, Dec.KCONS, Dec.KNIL, Dec.LB] <;>
    simp

end Row

end DecT

end Circuit
