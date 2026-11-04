import Ski.Circuit.DecAir
import Ski.Circuit.CompKind

/-!
# One row of DEC: its columns, its kind, its slots

What `Dec.decAir`'s constraints say of one row, before any bus: the bits
and the columns the constraints define (`DecRowF`, `decRowF`); the row's
kind, one of none, `Cell`, `Atom`, `Cons`, nil (`DKind`, `dkind_of`); and,
by substituting the kind's columns and taking normal forms
(`slotOK_all`), each slot's address, tag and activity as the kind's
pattern gives it (`slot_facts`).
-/

namespace Circuit

open B

-- ---------------------------------------------------------------------------
-- The columns a row's constraints define
-- ---------------------------------------------------------------------------

/-- **A DEC row's columns**, as its constraints define them. -/
structure DecRowF (D : Table) (q : Nat) : Prop where
  kcell : D.main q Dec.KCELL = 0 ∨ D.main q Dec.KCELL = 1
  katom : D.main q Dec.KATOM = 0 ∨ D.main q Dec.KATOM = 1
  kcons : D.main q Dec.KCONS = 0 ∨ D.main q Dec.KCONS = 1
  knil : D.main q Dec.KNIL = 0 ∨ D.main q Dec.KNIL = 1
  ksum : D.main q Dec.KCELL + D.main q Dec.KATOM + D.main q Dec.KCONS + D.main q Dec.KNIL + D.main q Dec.KIND = 0 ∨
    D.main q Dec.KCELL + D.main q Dec.KATOM + D.main q Dec.KCONS + D.main q Dec.KNIL + D.main q Dec.KIND = 1
  h0 : D.main q Dec.H0 = 0 ∨ D.main q Dec.H0 = 1
  h1 : D.main q Dec.H1 = 0 ∨ D.main q Dec.H1 = 1
  h01 : D.main q Dec.H0 * D.main q Dec.H1 = 0
  ro : (D.main q Dec.KCELL + D.main q Dec.KATOM) *
    (D.main q Dec.RO - (D.main q Dec.H1 + ofN 2 * (1 - D.main q Dec.H0 - D.main q Dec.H1))) = 0
  bit : D.main q Dec.BIT = 0 ∨ D.main q Dec.BIT = 1
  last : D.main q Dec.ISLAST = 0 ∨ D.main q Dec.ISLAST = 1
  bw : D.main q Dec.BW = 0 ∨ D.main q Dec.BW = 1
  err : D.main q Dec.ERR = 0 ∨ D.main q Dec.ERR = 1
  mode : D.main q Dec.MODE = 0 ∨ D.main q Dec.MODE = 1
  canon : D.main q Dec.KCONS * D.main q Dec.ISLAST * (1 - D.main q Dec.BIT) = 0
  nbw : D.main q Dec.NBW = D.main q Dec.BW * (1 - D.main q Dec.BIT)
  dropped : D.main q Dec.DROPPED = D.main q Dec.BW * D.main q Dec.BIT * D.main q Dec.ISLAST
  writes : D.main q Dec.WRITES = D.main q Dec.BW - D.main q Dec.DROPPED
  wl : D.main q Dec.WL = D.main q Dec.BW * D.main q Dec.BIT * (1 - D.main q Dec.ISLAST)
  wcn : D.main q Dec.WCN = D.main q Dec.WC + ofN 6 * D.main q Dec.WRITES
  nextl : D.main q Dec.NEXTL = D.main q Dec.KCONS * (1 - D.main q Dec.DROPPED) *
    (D.main q Dec.KEY + ofN 12 + ofN 6 * D.main q Dec.LVL)
  ptr : D.main q Dec.PTR = D.main q Dec.KCONS * (ofN 2 - ofN 2 * (D.main q Dec.BIT + D.main q Dec.BW -
    ofN 2 * D.main q Dec.BIT * D.main q Dec.BW))
  csend : D.main q Dec.CSEND = D.main q Dec.KCONS
  done0 : D.main q Dec.DONE0 = D.main q Dec.KCONS * D.main q Dec.ISLAST * (1 - D.main q Dec.MODE)
  done1 : D.main q Dec.DONE1 = D.main q Dec.KNIL * (1 - D.main q Dec.MODE) * (1 - D.main q Dec.TERM)
  sub : D.main q Dec.SUB = D.main q Dec.KCELL * D.main q Dec.H0
  hc : D.main q Dec.HC = D.main q Dec.KCELL * D.main q Dec.H1
  asub : D.main q Dec.ASUB = D.main q Dec.KATOM * D.main q Dec.H0
  hat : D.main q Dec.HAT = D.main q Dec.KATOM * D.main q Dec.H1
  cw : D.main q Dec.CW = D.main q Dec.KCONS * D.main q Dec.WRITES
  cwl : D.main q Dec.CWL = D.main q Dec.KCONS * D.main q Dec.WL
  clk : D.main q Dec.CLK = D.main q Dec.KCONS * D.main q Dec.BW
  nlk : D.main q Dec.NLK = D.main q Dec.KNIL * D.main q Dec.BW
  suberr : D.main q Dec.SUBERR = D.main q Dec.SUB * D.main q Dec.ERR
  cg : D.main q Dec.CG = D.main q Dec.KCONS * (1 - D.main q Dec.BIT)
  kind : D.main q Dec.KIND = 0 ∨ D.main q Dec.KIND = 1
  ib : D.main q Dec.IB = 0 ∨ D.main q Dec.IB = 1
  ikt : D.main q Dec.IKT = 0 ∨ D.main q Dec.IKT = 1
  term : D.main q Dec.TERM = 0 ∨ D.main q Dec.TERM = 1
  inn : D.main q Dec.INN = D.main q Dec.KIND * (1 - D.main q Dec.IB)
  inb : D.main q Dec.INB = D.main q Dec.KIND * D.main q Dec.IB
  ckt : D.main q Dec.CKT = D.main q Dec.KCELL * D.main q Dec.IKT
  consTerm : D.main q Dec.KCONS * D.main q Dec.TERM = 0
  nilLvl : D.main q Dec.KNIL * (1 - D.main q Dec.TERM) * D.main q Dec.LVL = 0

section Row

variable {D : Table} (hT : Sat Dec.decAir D) {q : Nat} (hq : q < D.h)
include hT hq

theorem decRowF_of : DecRowF D q := by
  have g : ∀ (i : Nat) (e : E), Dec.decCons[i]? = some e → e.eval (D.env q) = 0 := fun i e he => dec_cons hT hq he
  have b : ∀ (i x : Nat), Dec.decCons[i]? = some (B.bool (col x)) → D.main q x = 0 ∨ D.main q x = 1 := fun i x he => by
    have := g i _ he
    simp only [E.eval, B.bool, B.one, B.c, dec_ev hT hq, ofN_one] at this
    exact bit_of this
  have e : ∀ (i x : Nat) (y : E), Dec.decCons[i]? = some (B.eq (col x) y) → D.main q x = y.eval (D.env q) := fun i x y he => by
    have := g i _ he
    simp only [E.eval, B.eq, dec_ev hT hq] at this
    exact sub_eq_zero this
  have k4 := g 4 _ rfl
  have k7 := g 7 _ rfl
  have k8 := g 8 _ rfl
  have k14 := g 14 _ rfl
  simp only [E.eval, B.bool, B.one, B.c, dec_ev hT hq, ofN_one] at k4 k7 k8 k14
  have ev := dec_ev hT hq
  have f15 := e 15 _ _ rfl
  have f16 := e 16 _ _ rfl
  have f17 := e 17 _ _ rfl
  have f18 := e 18 _ _ rfl
  have f19 := e 19 _ _ rfl
  have f20 := e 20 _ _ rfl
  have f21 := e 21 _ _ rfl
  have f22 := e 22 _ _ rfl
  have f23 := e 23 _ _ rfl
  have f24 := e 24 _ _ rfl
  have f25 := e 25 _ _ rfl
  have f26 := e 26 _ _ rfl
  have f27 := e 27 _ _ rfl
  have f28 := e 28 _ _ rfl
  have f29 := e 29 _ _ rfl
  have f30 := e 30 _ _ rfl
  have f31 := e 31 _ _ rfl
  have f32 := e 32 _ _ rfl
  have f33 := e 33 _ _ rfl
  have f34 := e 34 _ _ rfl
  have f45 := e 45 _ _ rfl
  have f46 := e 46 _ _ rfl
  have f47 := e 47 _ _ rfl
  have k48 := g 48 _ rfl
  have k49 := g 49 _ rfl
  simp only [E.eval, B.one, B.c, ev, ofN_one, Dec.aE] at f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f45 f46 f47 k48 k49
  exact ⟨b 0 _ rfl, b 1 _ rfl, b 2 _ rfl, b 3 _ rfl, bit_of k4, b 5 _ rfl, b 6 _ rfl, k7, k8,
    b 9 _ rfl, b 10 _ rfl, b 11 _ rfl, b 12 _ rfl, b 13 _ rfl, k14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24,
    f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, b 41 _ rfl, b 42 _ rfl, b 43 _ rfl, b 44 _ rfl, f45, f46, f47,
    k48, k49⟩

end Row

-- ---------------------------------------------------------------------------
-- The row's kind
-- ---------------------------------------------------------------------------

/-- **A DEC row of kind `dk`**: none (`0`), a `Cell` wrapper (`1`), an `Atom`
    wrapper (`2`), a `Cons` (`3`), a nil (`4`), an indirection (`5`). -/
def DKind (D : Table) (q dk : Nat) : Prop :=
  dk < 6 ∧ D.main q Dec.KCELL = (if dk = 1 then 1 else 0) ∧ D.main q Dec.KATOM = (if dk = 2 then 1 else 0) ∧
    D.main q Dec.KCONS = (if dk = 3 then 1 else 0) ∧ D.main q Dec.KNIL = (if dk = 4 then 1 else 0) ∧
    D.main q Dec.KIND = (if dk = 5 then 1 else 0)

theorem dkind_of {D : Table} {q : Nat} (hf : DecRowF D q) : ∃ dk, DKind D q dk := by
  have hs := hf.ksum
  rcases hf.kcell with a | a <;> rcases hf.katom with b | b <;> rcases hf.kcons with c' | c' <;>
    rcases hf.knil with d | d <;> rcases hf.kind with i | i <;> rw [a, b, c', d, i] at hs
  all_goals first
    | exact absurd hs (by decide)
    | exact ⟨0, by decide, a, b, c', d, i⟩
    | exact ⟨1, by decide, a, b, c', d, i⟩
    | exact ⟨2, by decide, a, b, c', d, i⟩
    | exact ⟨3, by decide, a, b, c', d, i⟩
    | exact ⟨4, by decide, a, b, c', d, i⟩
    | exact ⟨5, by decide, a, b, c', d, i⟩

/-- Kind `dk`'s columns, as constants. -/
def decSubK (dk : Nat) : Atom → E
  | .main 0 i =>
    if i = Dec.KCELL then .const (if dk = 1 then 1 else 0)
    else if i = Dec.KATOM then .const (if dk = 2 then 1 else 0)
    else if i = Dec.KCONS then .const (if dk = 3 then 1 else 0)
    else if i = Dec.KNIL then .const (if dk = 4 then 1 else 0)
    else if i = Dec.KIND then .const (if dk = 5 then 1 else 0)
    else if i = Dec.CG ∧ dk ≠ 3 then .const 0
    else if i = Dec.CKT ∧ dk ≠ 1 then .const 0
    else .atom (.main 0 i)
  | a => .atom a

theorem decSubK_eval {D : Table} {q dk : Nat} (hq : q < D.h) (hf : DecRowF D q) (hk : DKind D q dk) (a : Atom) :
    (decSubK dk a).eval (D.env q) = D.env q a := by
  cases a with
  | main o i =>
    cases o with
    | zero =>
      simp only [decSubK]
      split
      · next h => subst h; rw [env_main0 hq, hk.2.1]; rfl
      · split
        · next h => subst h; rw [env_main0 hq, hk.2.2.1]; rfl
        · split
          · next h => subst h; rw [env_main0 hq, hk.2.2.2.1]; rfl
          · split
            · next h => subst h; rw [env_main0 hq, hk.2.2.2.2.1]; rfl
            · split
              · next h => subst h; rw [env_main0 hq, hk.2.2.2.2.2]; rfl
              · split
                · next h =>
                  obtain ⟨rfl, hne⟩ := h
                  rw [env_main0 hq, hf.cg, hk.2.2.2.1, if_neg hne, zero_mul']; rfl
                · split
                  · next h =>
                    obtain ⟨rfl, hne⟩ := h
                    rw [env_main0 hq, hf.ckt, hk.2.1, if_neg hne, zero_mul']; rfl
                  · rfl
    | succ o => rfl
  | pre _ _ => rfl
  | first => rfl
  | last => rfl
  | trans => rfl

/-- A kind's pattern: its slots. -/
def slotsOf (dk : Nat) : List (Dec.Src × Dec.Tg) :=
  if dk = 1 then Dec.cellSlots else if dk = 2 then Dec.atomSlots else if dk = 3 then Dec.consSlots
  else if dk = 5 then Dec.indSlots else []

/-- Slot `j`'s address, tag and activity on a row of kind `dk`. -/
def expAddr (dk j : Nat) : E :=
  if dk = 4 then (if j = 0 then col Dec.PC else zero)
  else match (slotsOf dk)[j]? with
    | some (s, _) => Dec.src s
    | none => zero

def expTag (dk j : Nat) : E :=
  if dk = 4 then (if j = 0 then c 1 else zero)
  else match (slotsOf dk)[j]? with
    | some (_, t) => Dec.tg t
    | none => zero

def expAct (dk j : Nat) : E :=
  if dk = 4 then (if j = 0 then one else zero)
  else match (slotsOf dk)[j]? with
    | some _ => if dk = 3 ∧ j ∈ Dec.consGated then col Dec.CG
      else if dk = 1 ∧ j ∈ Dec.cellGated then col Dec.CKT else one
    | none => zero

def slotEq (dk : Nat) (e e' : E) : Bool := (e.subst (decSubK dk)).norm == e'.norm

/-- **The slot table**: every slot's address, tag and activity, per kind. -/
def slotOK (dk : Nat) : Bool :=
  (List.range Dec.NSLOT).all fun j =>
    slotEq dk (Dec.addrE j) (expAddr dk j) && slotEq dk (Dec.tagE j) (expTag dk j) &&
      slotEq dk (Dec.actE j) (expAct dk j)

set_option maxRecDepth 100000 in
theorem slotOK_all : (List.range 6).all slotOK = true := by decide

theorem slot_eval {D : Table} {q dk : Nat} (hq : q < D.h) (hf : DecRowF D q) (hk : DKind D q dk) {e e' : E}
    (h : slotEq dk e e' = true) : e.eval (D.env q) = e'.eval (D.env q) := by
  rw [← E.eval_subst (decSubK dk) (D.env q) (decSubK_eval hq hf hk) e]
  exact E.eval_eq_of_norm (beq_iff_eq.1 h) _

/-- **A slot's address, tag and activity**, as the row's kind gives them. -/
theorem slot_kind {D : Table} {q dk : Nat} (hq : q < D.h) (hf : DecRowF D q) (hk : DKind D q dk) {j : Nat}
    (hj : j < Dec.NSLOT) :
    (Dec.addrE j).eval (D.env q) = (expAddr dk j).eval (D.env q) ∧
      (Dec.tagE j).eval (D.env q) = (expTag dk j).eval (D.env q) ∧
      (Dec.actE j).eval (D.env q) = (expAct dk j).eval (D.env q) := by
  have h := List.all_eq_true.1 slotOK_all dk (List.mem_range.2 hk.1)
  simp only [slotOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h j hj
  exact ⟨slot_eval hq hf hk h1, slot_eval hq hf hk h2, slot_eval hq hf hk h3⟩

section Slots

variable {D : Table} (hT : Sat Dec.decAir D) {q : Nat} (hq : q < D.h)
include hT hq

theorem slotCons_mem {j : Nat} (hj : j < Dec.NSLOT) {e : E} (he : e ∈ Dec.slotCons j) : e ∈ Dec.decCons := by
  unfold Dec.decCons
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, he⟩)

/-- **A slot's columns**: its address and tag columns are the muxed ones, its
    range bits bits, and when active its address is below the key by one and
    its range value. -/
theorem slot_cols {j : Nat} (hj : j < Dec.NSLOT) :
    D.main q (Dec.ADDR + j) = (Dec.addrE j).eval (D.env q) ∧
      D.main q (Dec.TAG + j) = (Dec.tagE j).eval (D.env q) ∧
      (∀ i, i < RANGE_BITS → D.main q (Dec.DBITS + j * RANGE_BITS + i) = 0 ∨
        D.main q (Dec.DBITS + j * RANGE_BITS + i) = 1) ∧
      (Dec.actE j).eval (D.env q) *
        (D.main q Dec.KEY - D.main q (Dec.ADDR + j) - 1 - (Dec.rangeValD j).eval (D.env q)) = 0 := by
  have g : ∀ e, e ∈ Dec.slotCons j → e.eval (D.env q) = 0 := fun e he => hT.2 e (slotCons_mem hT hq hj he) q hq
  have ev := dec_ev hT hq
  have a := g _ (show B.eq (col (Dec.ADDR + j)) (Dec.addrE j) ∈ Dec.slotCons j by simp [Dec.slotCons])
  have t := g _ (show B.eq (col (Dec.TAG + j)) (Dec.tagE j) ∈ Dec.slotCons j by simp [Dec.slotCons])
  have r := g _ (show E.mul (Dec.actE j) (.sub (.sub (.sub (col Dec.KEY) (col (Dec.ADDR + j))) one) (Dec.rangeValD j))
    ∈ Dec.slotCons j by simp [Dec.slotCons])
  simp only [E.eval, B.eq, ev] at a t
  simp only [E.eval, B.one, B.c, ev, ofN_one] at r
  refine ⟨sub_eq_zero a, sub_eq_zero t, fun i hi => ?_, r⟩
  have b := g _ (show B.bool (col (Dec.DBITS + j * RANGE_BITS + i)) ∈ Dec.slotCons j by
    simp only [Dec.slotCons, List.mem_append, List.mem_map, List.mem_range]
    exact .inl (.inr ⟨i, hi, rfl⟩))
  simp only [E.eval, B.bool, B.one, B.c, ev, ofN_one] at b
  exact bit_of b

/-- A slot's range value is below `2^24`. -/
theorem rangeValD_lt {j : Nat} (hj : j < Dec.NSLOT) : ((Dec.rangeValD j).eval (D.env q)).val < 2 ^ 24 := by
  have hbits := (slot_cols hT hq hj).2.2.1
  have step : ∀ n, n ≤ RANGE_BITS →
      (((List.range n).foldl (fun v i => E.add v (E.mul (col (Dec.DBITS + j * RANGE_BITS + i)) (c (2 ^ i)))) zero).eval
        (D.env q)).val < 2 ^ n := by
    intro n
    induction n with
    | zero => intro _; show (0 : Nat) < 1; decide
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ih := ih (Nat.le_of_succ_le hn)
      generalize (List.foldl (fun v i => E.add v (E.mul (col (Dec.DBITS + j * RANGE_BITS + i)) (c (2 ^ i))))
        zero (List.range n)) = X at ih ⊢
      simp only [E.eval, B.col, B.c, env_main0 hq]
      generalize X.eval (D.env q) = x at ih ⊢
      have hpow : 2 ^ (n + 1) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hn
      have hP : 2 ^ 24 < P := by decide
      rcases hbits n hn with hb | hb <;> rw [hb]
      · rw [zero_mul', add_zero']
        exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
      · rw [one_mul', val_add_nat (by rw [Nat.pow_succ] at hpow; omega), Nat.pow_succ]
        omega
  exact step RANGE_BITS (Nat.le_refl _)

end Slots

-- ---------------------------------------------------------------------------
-- The row's messages
-- ---------------------------------------------------------------------------

namespace Dec

/-- DEC's messages on its own buses. -/
def busI : List Inter :=
  [⟨"decn", 1, .neg (.add (col KCELL) (col KATOM)), [col KEY, col PC, col RO]⟩,
   ⟨"decn", 1, col KCELL, [col KEY, f2 21, .sub (c 2) (col H0)]⟩,
   ⟨"decn", 1, col KCELL, [col KEY, f2 26, c 2]⟩,
   ⟨"decb", 1, col KATOM, [col KEY, f2 22, .sub one (col H1), c 0, col H1, c 0]⟩,
   ⟨"decb", 1, .neg (col KCONS), [col KEY, col PC, col MODE, col LVL, col BW, col WC]⟩,
   ⟨"decb", 1, col CSEND, [col KEY, f2 14, .add (col MODE) (.mul (c 2) (col ISLAST)), .add (col LVL) one, col NBW,
     col WCN]⟩,
   ⟨"decb", 1, .neg (col KNIL), [col KEY, col PC, mfE, col LVL, col BW, col WC]⟩,
   ⟨"decd", 1, .neg (col SUB), [col KEY, col ERR, col WC]⟩,
   ⟨"decd", 1, col DONE0, [col KEY, c 0, col WCN]⟩,
   ⟨"decd", 1, col DONE1, [col KEY, c 1, col WC]⟩,
   ⟨"decd", 1, col HC, [col KEY, c 1, c 0]⟩,
   ⟨"decx", 1, col SUB, [col KEY, .add (col KEY) (.mul (c 12) (col ERR)),
     .add (.add (.add (col KEY) (c 12)) (col WC)) (.mul (c 3) (col ERR))]⟩,
   ⟨"decx", 1, col ASUB, [col KEY, col KEY, .add (col KEY) (c 3)]⟩,
   ⟨"decn", 1, .neg (col INN), [col KEY, col PC, col RO]⟩,
   ⟨"decn", 1, col INN, [col KEY, f2 1, col RO]⟩,
   ⟨"decb", 1, .neg (col INB), [col KEY, col PC, mfE, col LVL, col BW, col WC]⟩,
   ⟨"decb", 1, col INB, [col KEY, f2 1, mfE, col LVL, col BW, col WC]⟩]

/-- DEC's writes. -/
def writesI : List Inter :=
  [wr (kE 0) (c 0) (kE 1) (col SUB), wr (kE 1) (f1 2) (kE 2) (col SUB), wr (kE 2) (f1 8) (kE 3) (col SUB),
   wr (kE 3) (kE 4) (f2 14) (col SUB), wr (kE 4) (f1 15) (kE 5) (col SUB), wr (kE 5) (f1 17) (kE 6) (col SUB),
   wr (kE 6) (c 0) (kE 7) (col SUB),
   wr (kE 12) (c 0) (kE 13) (col SUBERR), wr (kE 13) (c 0) (kE 14) (col SUBERR), wr (kE 14) (c 0) (c 1) (col SUBERR),
   wr (kE 7) (c 0) (c 0) (col HC), wr (kE 8) (c 0) (c 0) (col HC), wr (kE 9) (c 0) (c 0) (col HC),
   wr (kE 10) (c 0) (c 0) (col HC), wr (kE 11) (c 0) (c 0) (col HC),
   wr (kE 7) (f1 0) (kE 8) (col HAT), wr (kE 8) (f1 6) (kE 9) (col HAT), wr (kE 9) (f1 12) (kE 10) (col HAT),
   wr (kE 10) (f1 18) (kE 11) (col HAT),
   wr (kE 0) (c 0) (kE 1) (col ASUB), wr (kE 1) (c 0) (kE 2) (col ASUB), wr (kE 2) (c 0) (c 1) (col ASUB),
   wr (apE 0) (c 0) (apE 1) (col CW), wr (apE 1) (apE 2) (apE 5) (col CW), wr (apE 2) (f1 3) (apE 3) (col CW),
   wr (apE 3) (f1 5) (apE 4) (col CW), wr (apE 4) (c 0) (col PTR) (col CW),
   wr (apE 5) (c 0) (f2 14) (col CWL),
   wr (.add (.add (col KEY) (c 11)) (.mul (c 6) (col LVL))) (c 0) (col NEXTL) (col CLK),
   wr (kE 11) (c 0) (c 0) (col NLK)]

theorem decInters_split : decInters = (List.range NSLOT).map slotInter ++ busI ++ writesI := rfl

/-- The columns that count DEC's writes. -/
def wcols : List Nat := [SUB, SUBERR, HC, HAT, ASUB, CW, CWL, CLK, NLK]

theorem writesI_mem : ∀ I ∈ writesI, I.bus = "mem" ∧ ∃ X ∈ wcols, I.count = col X := by
  intro I hI
  simp only [writesI, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, _, by simp [wcols], rfl⟩

theorem busI_ne_mem : ∀ I ∈ busI, I.bus ≠ "mem" := by
  intro I hI
  simp only [busI, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

end Dec

theorem bit_mul {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : a * b = 0 ∨ a * b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem bit_one_sub {a : F} (ha : a = 0 ∨ a = 1) : 1 - a = 0 ∨ 1 - a = 1 := by
  rcases ha with rfl | rfl <;> decide

/-- **The write columns are bits.** -/
theorem DecRowF.wbit {D : Table} {q : Nat} (hf : DecRowF D q) : ∀ X ∈ Dec.wcols, D.main q X = 0 ∨ D.main q X = 1 := by
  have hwr : D.main q Dec.WRITES = 0 ∨ D.main q Dec.WRITES = 1 := by
    rw [hf.writes, hf.dropped]
    rcases hf.bw with a | a <;> rcases hf.bit with b | b <;> rcases hf.last with c' | c' <;> rw [a, b, c'] <;> decide
  have hwl : D.main q Dec.WL = 0 ∨ D.main q Dec.WL = 1 := by
    rw [hf.wl]; exact bit_mul (bit_mul hf.bw hf.bit) (bit_one_sub hf.last)
  have hsub : D.main q Dec.SUB = 0 ∨ D.main q Dec.SUB = 1 := by rw [hf.sub]; exact bit_mul hf.kcell hf.h0
  intro X hX
  simp only [Dec.wcols, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsub
  · rw [hf.suberr]; exact bit_mul hsub hf.err
  · rw [hf.hc]; exact bit_mul hf.kcell hf.h1
  · rw [hf.hat]; exact bit_mul hf.katom hf.h1
  · rw [hf.asub]; exact bit_mul hf.katom hf.h0
  · rw [hf.cw]; exact bit_mul hf.kcons hwr
  · rw [hf.cwl]; exact bit_mul hf.kcons hwl
  · rw [hf.clk]; exact bit_mul hf.kcons hf.bw
  · rw [hf.nlk]; exact bit_mul hf.knil hf.bw

theorem expAct_cases (dk j : Nat) :
    expAct dk j = one ∨ expAct dk j = zero ∨ expAct dk j = col Dec.CG ∨ expAct dk j = col Dec.CKT := by
  unfold expAct
  split
  · split
    · exact .inl rfl
    · exact .inr (.inl rfl)
  · split
    · split
      · exact .inr (.inr (.inl rfl))
      · split
        · exact .inr (.inr (.inr rfl))
        · exact .inl rfl
    · exact .inr (.inl rfl)

/-- **A slot's activity is a bit.** -/
theorem actE_bit {D : Table} {q : Nat} (hq : q < D.h) (hf : DecRowF D q) {j : Nat} (hj : j < Dec.NSLOT) :
    (Dec.actE j).eval (D.env q) = 0 ∨ (Dec.actE j).eval (D.env q) = 1 := by
  obtain ⟨dk, hk⟩ := dkind_of hf
  rw [(slot_kind hq hf hk hj).2.2]
  rcases expAct_cases dk j with e | e | e | e <;> rw [e]
  · exact .inr rfl
  · exact .inl rfl
  · show D.env q (.main 0 Dec.CG) = 0 ∨ D.env q (.main 0 Dec.CG) = 1
    rw [env_main0 hq, hf.cg]; exact bit_mul hf.kcons (bit_one_sub hf.bit)
  · show D.env q (.main 0 Dec.CKT) = 0 ∨ D.env q (.main 0 Dec.CKT) = 1
    rw [env_main0 hq, hf.ckt]; exact bit_mul hf.kcell hf.ikt

/-- **DEC's `mem` messages have counts `0` or `1`.** -/
theorem dec_mem_count {D : Table} {q : Nat} (hq : q < D.h) (hf : DecRowF D q) {I : Inter}
    (hI : I ∈ Dec.decAir.inters) (hb : I.bus = "mem") :
    I.count.eval (D.env q) = 0 ∨ I.count.eval (D.env q) = 1 := by
  change I ∈ Dec.decInters at hI
  rw [Dec.decInters_split] at hI
  rcases List.mem_append.1 hI with hI | hI
  · rcases List.mem_append.1 hI with hI | hI
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hI
      exact actE_bit hq hf (List.mem_range.1 hj)
    · exact absurd hb (Dec.busI_ne_mem I hI)
  · obtain ⟨_, X, hX, e⟩ := Dec.writesI_mem I hI
    rw [e]; show D.env q (.main 0 X) = 0 ∨ D.env q (.main 0 X) = 1
    rw [env_main0 hq]; exact hf.wbit X hX

theorem bit_val_le' {x : F} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by rcases h with rfl | rfl <;> decide

end Circuit
