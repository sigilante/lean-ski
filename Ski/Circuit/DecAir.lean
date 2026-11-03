import Ski.Circuit.CompAir
import Ski.Circuit.CompJAir
import Ski.ComposedDText

/-!
# The composed circuit with the `dec` jet, as data

The six AIRs of `bench/plonky3/src/compd.rs` for a statement `decpre p`
(`ComposedDText.publicTextD`), as its verifier builds them (`airs`):

- the composed circuit's five (`Ski/Circuit/CompAir.lean`), the CPU
  carrying the jet's row: a selector `DECSEL` after the restart columns,
  then a blinding block sent to DEC on `blind_c`, then the result's root
  and the new counter, received from DEC; the row reads the atom `J` at
  the head and the stack cell `cons p rest`, sends the subject's need and
  looks up the slots;
- **DEC** (`bench/plonky3/src/decair.rs`): one row per cell pattern of the
  subject (`decAir`), four kinds (the `Cell` wrapper, the `Atom` wrapper, a
  `Cons`, a nil), each reading its pattern's cells through up to 25
  range-checked lookups whose addresses and tags are muxed by the kind, and
  the borrow step of the decrement on the `Cons` rows (`DecJet.decB`); it
  carries a blinding block, the blinding tree's edge `CPU —c— DEC`.

**`decStep_sound`**: on every row of a table that satisfies `decAir`, the
borrow step's columns are the decrement's: the next borrow clears exactly
when the bit is set, a bit is rewritten exactly under a borrow unless it is
the dropped top, and the written bit is the input's exclusive-or with the
borrow, as `DecJet.decB` computes it (`decB_step`).

**`dec_sound_row`**: every row of a table that satisfies `decAir` has one
kind or none (`dec_kinds`); a wrapper row has one of the three roles
(`dec_role`); a `Cons` row takes the borrow step (`decStep_sound`), and in
the head's mode its level is below `W = 32` (`dec_level`), so the head
atom the jet decrements has at most 32 bits.  What DEC's tables prove
together, across rows and buses, is that a jet row whose state decodes is
`DecJet.decRow`'s step (`Circuit.CompDOK.jetRow`, `Ski/Circuit/CompDJetRow.lean`),
and so `Circuit.decpreExport_sound` (`Ski/DecPreSound.lean`).

`lake exe circuit compare-compd` checks the Rust export (`ski-air
export-compd PUBLIC`) against `compDAirsG`.
-/

namespace Circuit

open B Compose CompM

-- ---------------------------------------------------------------------------
-- The CPU's jet columns
-- ---------------------------------------------------------------------------

def DECSEL : Nat := ROOT + 1
def sDec : E := col DECSEL
def DROOT : Nat := DECSEL + 6
def DCTR : Nat := DECSEL + 7

/-- The tags, with the jet row's: an atom at the head, a stack cell. -/
def tagsD : List E :=
  [.add (.add (.add (.add (.add (.mul (.add (.add sK sHK1) sHK2) (c 1)) (.mul (.add sI sHI1) (c 2)))
      (.mul sApp (c 3))) (.mul (.add sHA sPLater) (c 6))) (.mul sRS (c 1))) (.mul sDec (c 6)),
   .add (.add (.mul (sum [sI, sK, sS, sHK2, sHS2, sHS3]) (c 5)) (.mul (sum [sHI1, sHK1, sHS1, sRS]) (c 4)))
      (.mul sDec (c 5)),
   .add (.mul (sum [sK, sS, sHS3]) (c 5)) (.mul (.add sHK2 sHS2) (c 4)),
   .add (.mul sS (c 5)) (.mul sHS3 (c 4))]

def readInterD (j : Nat) : Inter :=
  ⟨"mem", 1, acts.getD j zero, [addrs.getD j zero, tagsD.getD j zero, fld (2 * j), fld (2 * j + 1)]⟩

/-- **The CPU's constraints**, in the Rust's order: `n` segments over the
    nil at `nilA`, the jet's atom `J`. -/
def cpuConsD (hd0 stk0 ctr0 n nilA J : Nat) : List E :=
  (List.range NKINDS).map (fun i => B.bool (col (SEL + i))) ++ [bool sRS, bool sDec] ++
  [eq (sum ((List.range NKINDS).map (fun i => col (SEL + i)) ++ [sRS, sDec])) one] ++
  readCons 0 ++ readCons 1 ++ readCons 2 ++ readCons 3 ++
  [sInst, sPFirst, sPLater,
   whenFirst (col CNT), whenTrans (eq (nxt CNT) (.add (col CNT) sRS)), whenLast (eq (col CNT) (c (n - 1))),
   .mul sDec (.sub (fld 0) (c J)),
   B.bool (col (DECSEL + 5)),
   whenTrans (eq (nxt HD) (.add (.add nextHd (.mul sRS (col ROOT))) (.mul sDec (col DROOT)))),
   whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sRS (c nilA))) (.mul sDec (fld 3)))),
   whenTrans (eq (nxt CTR) (.add nextCtr (.mul sDec (.sub (col DCTR) (col CTR))))),
   whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
   whenLast (eq halt one),
   B.bool (col (BLA + 4)), B.bool (col (BLB + 4)),
   whenLast (eq sHK1 one)]

def cpuIntersD : List Inter :=
  [readInterD 0, readInterD 1, readInterD 2, readInterD 3] ++ writeInters ++
  [⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩,
   -- The slots: `K`, `I`, `K I` at 0, 1, 2.
   ⟨"mem", 1, sDec, [c 0, c 1, c 0, c 0]⟩,
   ⟨"mem", 1, sDec, [c 1, c 2, c 0, c 0]⟩,
   ⟨"mem", 1, sDec, [c 2, c 3, c 0, c 1]⟩,
   -- The subject's need, and the result.
   ⟨"decn", 1, sDec, [col CTR, fld 2, c 0]⟩,
   ⟨"decx", 1, .neg sDec, [col CTR, col DROOT, col DCTR]⟩,
   -- The blinding tree's edge to DEC.
   blindMsg "blind_c" (DECSEL + 1) true,
   ⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩,
   ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩]

def cpuAirDec (hd0 stk0 ctr0 n nilA J : Nat) : AirD :=
  ⟨"cpu", DECSEL + 8, 0, cpuConsD hd0 stk0 ctr0 n nilA J, cpuIntersD, []⟩

-- ---------------------------------------------------------------------------
-- The jet's table
-- ---------------------------------------------------------------------------

namespace Dec

def KEY : Nat := 0
def KCELL : Nat := 1
def KATOM : Nat := 2
def KCONS : Nat := 3
def KNIL : Nat := 4
def RO : Nat := 5
def H0 : Nat := 6
def H1 : Nat := 7
def PC : Nat := 8
def LVL : Nat := 9
def BW : Nat := 10
def WC : Nat := 11
def BIT : Nat := 12
def ISLAST : Nat := 13
def NBW : Nat := 14
def DROPPED : Nat := 15
def WRITES : Nat := 16
def WL : Nat := 17
def WCN : Nat := 18
def NEXTL : Nat := 19
def PTR : Nat := 20
def ERR : Nat := 21
def MODE : Nat := 22
def CSEND : Nat := 23
def DONE0 : Nat := 24
def DONE1 : Nat := 25
def SUB : Nat := 26
def HC : Nat := 27
def ASUB : Nat := 28
def HAT : Nat := 29
def CW : Nat := 30
def CWL : Nat := 31
def CLK : Nat := 32
def NLK : Nat := 33
def SUBERR : Nat := 34
def CG : Nat := 35
def LB : Nat := 36
def NLB : Nat := 5
def NSLOT : Nat := 25
def ADDR : Nat := LB + NLB
def TAG : Nat := ADDR + NSLOT
def DFLD : Nat := TAG + NSLOT
def DBITS : Nat := DFLD + 2 * NSLOT
/-- The columns before the blinding block. -/
def WIDTH : Nat := DBITS + RANGE_BITS * NSLOT

def f1 (j : Nat) : E := col (DFLD + 2 * j)
def f2 (j : Nat) : E := col (DFLD + 2 * j + 1)

/-- Where a slot reads: the row's pointer, or a field of an earlier slot. -/
inductive Src
  | rowP
  | F1 (i : Nat)
  | F2 (i : Nat)

/-- What tag a slot expects: a constant, the bit's, or the peeked tail's. -/
inductive Tg
  | C (n : Nat)
  | BitTag
  | LastTag

def cellSlots : List (Src × Tg) :=
  [(.rowP, .C 3), (.F1 0, .C 1), (.F2 0, .C 3), (.F1 2, .C 3), (.F1 3, .C 0), (.F2 3, .C 3), (.F1 5, .C 1),
   (.F2 5, .C 1), (.F2 2, .C 3), (.F1 8, .C 3), (.F1 9, .C 0), (.F2 9, .C 3), (.F1 11, .C 1), (.F2 11, .C 1),
   (.F2 8, .C 3), (.F1 14, .C 3), (.F1 15, .C 0), (.F2 15, .C 3), (.F1 17, .C 3), (.F1 18, .C 0), (.F2 18, .C 2),
   (.F2 17, .C 3), (.F1 21, .C 1), (.F2 14, .C 3), (.F1 23, .C 1)]

def atomSlots : List (Src × Tg) :=
  [(.rowP, .C 3), (.F1 0, .C 3), (.F1 1, .C 0), (.F2 1, .C 3), (.F1 3, .C 1), (.F2 3, .C 1), (.F2 0, .C 3),
   (.F1 6, .C 3), (.F1 7, .C 0), (.F2 7, .C 3), (.F1 9, .C 1), (.F2 9, .C 1), (.F2 6, .C 3), (.F1 12, .C 3),
   (.F1 13, .C 0), (.F2 13, .C 3), (.F1 15, .C 1), (.F2 15, .C 1), (.F2 12, .C 3), (.F1 18, .C 3), (.F1 19, .C 0),
   (.F2 19, .C 2), (.F2 18, .C 3), (.F1 22, .C 1)]

def consSlots : List (Src × Tg) :=
  [(.rowP, .C 3), (.F1 0, .C 1), (.F2 0, .C 3), (.F1 2, .C 3), (.F1 3, .C 0), (.F2 3, .C 3), (.F1 5, .C 3),
   (.F1 6, .C 0), (.F2 6, .C 2), (.F2 5, .C 3), (.F1 9, .C 1), (.F2 9, .BitTag), (.F1 11, .C 1), (.F2 11, .C 2),
   (.F2 2, .C 3), (.F1 14, .C 1), (.F2 14, .LastTag)]

def consGated : List Nat := [12, 13]

def src : Src → E
  | .rowP => col PC
  | .F1 i => f1 i
  | .F2 i => f2 i

def tg : Tg → E
  | .C n => c n
  | .BitTag => .sub (c 3) (.mul (c 2) (col BIT))
  | .LastTag => .sub (c 3) (.mul (c 2) (col ISLAST))

/-- A kind's part of slot `j`'s address, tag and activity. -/
def part (k : Nat) (slots : List (Src × Tg)) (j : Nat) (gate : E) : E × E × E :=
  match slots[j]? with
  | some (s, t) => (.mul (col k) (src s), .mul (col k) (tg t), gate)
  | none => (zero, zero, zero)

def addrE (j : Nat) : E :=
  let (a1, _, _) := part KCELL cellSlots j (col KCELL)
  let (a2, _, _) := part KATOM atomSlots j (col KATOM)
  let (a3, _, _) := part KCONS consSlots j (col KCONS)
  let a4 : E := if j = 0 then .mul (col KNIL) (col PC) else zero
  .add (.add (.add a1 a2) a3) a4

def tagE (j : Nat) : E :=
  let (_, t1, _) := part KCELL cellSlots j (col KCELL)
  let (_, t2, _) := part KATOM atomSlots j (col KATOM)
  let (_, t3, _) := part KCONS consSlots j (col KCONS)
  let t4 : E := if j = 0 then .mul (col KNIL) (c 1) else zero
  .add (.add (.add t1 t2) t3) t4

def actE (j : Nat) : E :=
  let (_, _, g1) := part KCELL cellSlots j (col KCELL)
  let (_, _, g2) := part KATOM atomSlots j (col KATOM)
  let (_, _, g3) := part KCONS consSlots j (if j ∈ consGated then col CG else col KCONS)
  let g4 : E := if j = 0 then col KNIL else zero
  .add (.add (.add g1 g2) g3) g4

def rangeValD (j : Nat) : E :=
  (List.range RANGE_BITS).foldl (fun v i => .add v (.mul (col (DBITS + j * RANGE_BITS + i)) (c (2 ^ i)))) zero

/-- Slot `j`'s constraints: its address and tag muxed by the kind, its bits
    Boolean, and when active its address below the key. -/
def slotCons (j : Nat) : List E :=
  [eq (col (ADDR + j)) (addrE j), eq (col (TAG + j)) (tagE j)] ++
  (List.range RANGE_BITS).map (fun i => B.bool (col (DBITS + j * RANGE_BITS + i))) ++
  [.mul (actE j) (.sub (.sub (.sub (col KEY) (col (ADDR + j))) one) (rangeValD j))]

def slotInter (j : Nat) : Inter :=
  ⟨"mem", 1, actE j, [col (ADDR + j), col (TAG + j), f1 j, f2 j]⟩

/-- The address a rewritten bit's `Cons` goes to. -/
def aE : E := .add (.add (col KEY) (c 12)) (.mul (c 6) (col LVL))

def levelVal : E := (List.range NLB).foldl (fun v i => .add v (.mul (col (LB + i)) (c (2 ^ i)))) zero

/-- **DEC's constraints**, in the Rust's order. -/
def decCons : List E :=
  [B.bool (col KCELL), B.bool (col KATOM), B.bool (col KCONS), B.bool (col KNIL),
   B.bool (.add (.add (.add (col KCELL) (col KATOM)) (col KCONS)) (col KNIL)),
   B.bool (col H0), B.bool (col H1), .mul (col H0) (col H1),
   .mul (.add (col KCELL) (col KATOM))
     (.sub (col RO) (.add (col H1) (.mul (c 2) (.sub (.sub one (col H0)) (col H1))))),
   B.bool (col BIT), B.bool (col ISLAST), B.bool (col BW), B.bool (col ERR), B.bool (col MODE),
   .mul (.mul (col KCONS) (col ISLAST)) (.sub one (col BIT)),
   eq (col NBW) (.mul (col BW) (.sub one (col BIT))),
   eq (col DROPPED) (.mul (.mul (col BW) (col BIT)) (col ISLAST)),
   eq (col WRITES) (.sub (col BW) (col DROPPED)),
   eq (col WL) (.mul (.mul (col BW) (col BIT)) (.sub one (col ISLAST))),
   eq (col WCN) (.add (col WC) (.mul (c 6) (col WRITES))),
   eq (col NEXTL) (.mul (.mul (col KCONS) (.sub one (col DROPPED))) aE),
   eq (col PTR) (.mul (col KCONS) (.sub (c 2) (.mul (c 2) (.sub (.add (col BIT) (col BW)) (.mul (.mul (c 2) (col BIT)) (col BW)))))),
   eq (col CSEND) (.mul (col KCONS) (.sub one (col ISLAST))),
   eq (col DONE0) (.mul (.mul (col KCONS) (col ISLAST)) (.sub one (col MODE))),
   eq (col DONE1) (.mul (col KNIL) (.sub one (col MODE))),
   eq (col SUB) (.mul (col KCELL) (col H0)),
   eq (col HC) (.mul (col KCELL) (col H1)),
   eq (col ASUB) (.mul (col KATOM) (col H0)),
   eq (col HAT) (.mul (col KATOM) (col H1)),
   eq (col CW) (.mul (col KCONS) (col WRITES)),
   eq (col CWL) (.mul (col KCONS) (col WL)),
   eq (col CLK) (.mul (col KCONS) (col BW)),
   eq (col NLK) (.mul (col KNIL) (col BW)),
   eq (col SUBERR) (.mul (col SUB) (col ERR)),
   eq (col CG) (.mul (col KCONS) (.sub one (col BIT)))] ++
  (List.range NLB).map (fun i => B.bool (col (LB + i))) ++
  [.mul (.mul (col KCONS) (.sub one (col MODE))) (.sub (col LVL) levelVal)] ++
  (List.range NSLOT).flatMap slotCons

/-- A write of the cell `app x y` at `addr`, counted by `count`. -/
def wr (addr x y count : E) : Inter := ⟨"mem", 1, count, [addr, c 3, x, y]⟩

def kE (n : Nat) : E := .add (col KEY) (c n)
def apE (n : Nat) : E := .add aE (c n)

/-- **DEC's messages**, in the Rust's order. -/
def decInters : List Inter :=
  (List.range NSLOT).map slotInter ++
  [⟨"decn", 1, .neg (.add (col KCELL) (col KATOM)), [col KEY, col PC, col RO]⟩,
   ⟨"decn", 1, col KCELL, [col KEY, f2 21, .sub (c 2) (col H0)]⟩,
   ⟨"decn", 1, col KCELL, [col KEY, f2 23, c 2]⟩,
   ⟨"decb", 1, col KATOM, [col KEY, f2 22, .sub one (col H1), c 0, col H1, c 0]⟩,
   ⟨"decb", 1, .neg (col KCONS), [col KEY, col PC, col MODE, col LVL, col BW, col WC]⟩,
   ⟨"decb", 1, col CSEND, [col KEY, f2 14, col MODE, .add (col LVL) one, col NBW, col WCN]⟩,
   ⟨"decb", 1, .neg (col KNIL), [col KEY, col PC, col MODE, col LVL, col BW, col WC]⟩,
   ⟨"decd", 1, .neg (col SUB), [col KEY, col ERR, col WC]⟩,
   ⟨"decd", 1, col DONE0, [col KEY, c 0, col WCN]⟩,
   ⟨"decd", 1, col DONE1, [col KEY, c 1, col WC]⟩,
   ⟨"decd", 1, col HC, [col KEY, c 1, c 0]⟩,
   ⟨"decx", 1, col SUB, [col KEY, .add (col KEY) (.mul (c 12) (col ERR)),
     .add (.add (.add (col KEY) (c 12)) (col WC)) (.mul (c 3) (col ERR))]⟩,
   ⟨"decx", 1, col ASUB, [col KEY, col KEY, .add (col KEY) (c 3)]⟩,
   -- The subject's `Cell` wrapper at `key`.
   wr (kE 0) (c 0) (kE 1) (col SUB), wr (kE 1) (f1 2) (kE 2) (col SUB), wr (kE 2) (f1 8) (kE 3) (col SUB),
   wr (kE 3) (kE 4) (f2 14) (col SUB), wr (kE 4) (f1 15) (kE 5) (col SUB), wr (kE 5) (f1 17) (kE 6) (col SUB),
   wr (kE 6) (c 0) (kE 7) (col SUB),
   -- `errT` at `key + 12` on a crash.
   wr (kE 12) (c 0) (kE 13) (col SUBERR), wr (kE 13) (c 0) (kE 14) (col SUBERR), wr (kE 14) (c 0) (c 1) (col SUBERR),
   -- A cell head: the `Atom` wrapper's slots filled.
   wr (kE 7) (c 0) (c 0) (col HC), wr (kE 8) (c 0) (c 0) (col HC), wr (kE 9) (c 0) (c 0) (col HC),
   wr (kE 10) (c 0) (c 0) (col HC), wr (kE 11) (c 0) (c 0) (col HC),
   -- The head's `Atom` wrapper at `key + 7`.
   wr (kE 7) (f1 0) (kE 8) (col HAT), wr (kE 8) (f1 6) (kE 9) (col HAT), wr (kE 9) (f1 12) (kE 10) (col HAT),
   wr (kE 10) (f1 18) (kE 11) (col HAT),
   -- An atom subject: `errT` at `key`.
   wr (kE 0) (c 0) (kE 1) (col ASUB), wr (kE 1) (c 0) (kE 2) (col ASUB), wr (kE 2) (c 0) (c 1) (col ASUB),
   -- A rewritten bit's `Cons`.
   wr (apE 0) (c 0) (apE 1) (col CW), wr (apE 1) (apE 2) (apE 5) (col CW), wr (apE 2) (f1 3) (apE 3) (col CW),
   wr (apE 3) (f1 5) (apE 4) (col CW), wr (apE 4) (c 0) (col PTR) (col CW),
   wr (apE 5) (c 0) (f2 14) (col CWL),
   -- The link to this bit, from the bit below or the `Atom` wrapper.
   wr (.add (.add (col KEY) (c 11)) (.mul (c 6) (col LVL))) (c 0) (col NEXTL) (col CLK),
   wr (kE 11) (c 0) (c 0) (col NLK)]

/-- **The `dec` jet's table.** -/
def decAir : AirD := ⟨"dec", WIDTH, 0, decCons, decInters, []⟩

end Dec

/-- DEC with its blinding block: the edge `CPU —c— DEC`. -/
def decAirB : AirD := withBlocks Dec.decAir [("blind_c", false)]

/-- **The composed circuit with the `dec` jet** for verifiers `Vs`, open in
    the jet's atom, over one bit and a region of `W` cells: what its
    verifier builds. -/
def compDAirsG (Vs : List OTerm) (W : Nat) : List AirD :=
  let N := BT.nleaves ComposedDText.shpD
  let region := List.replicate W Cell.S
  let ρ0 : Nat → Bool := fun _ => false
  let m := cMachineO ρ0 ComposedDText.shpD region Vs
  let roots := (cHeapO ρ0 ComposedDText.shpD region Vs).2
  [cpuAirDec m.hd m.stk m.heap.length roots.length m.stk ComposedDText.JD, memAirC,
   progAirC m.heap N W, witAir N W, segsAir roots, decAirB]

/-- The circuit for `decpre p` over a region of `W` cells. -/
def compDAirs (p W : Nat) : List AirD := compDAirsG (ComposedDText.VsD p) W

-- ---------------------------------------------------------------------------
-- The borrow step on a row
-- ---------------------------------------------------------------------------

/-- The decrement's step on one bit under a borrow: the written bit and
    the next borrow. -/
def decStep (b bw : Bool) : Bool × Bool := (b != bw, bw && !b)

/-- **`decB` is the fold of the borrow step**: on `b :: bs` under a borrow,
    the step's bit, then the rest under the next borrow; without a borrow
    the bits pass; a set top bit under a borrow is dropped. -/
theorem decB_step (b : Bool) (bs : List Bool) :
    DecJet.decB (b :: bs) =
      if (decStep b true).2 then (decStep b true).1 :: DecJet.decB bs
      else if bs = [] then [] else (decStep b true).1 :: bs := by
  cases b <;> rfl

/-- A `Cons` row's values: the kind, the bit, the borrow, the last flag. -/
def consRow (T : Table) (r : Nat) : Prop :=
  T.main r Dec.KCONS = 1 ∧ (T.main r Dec.BIT = 0 ∨ T.main r Dec.BIT = 1) ∧
    (T.main r Dec.BW = 0 ∨ T.main r Dec.BW = 1) ∧ (T.main r Dec.ISLAST = 0 ∨ T.main r Dec.ISLAST = 1)

/-- **Every `Cons` row of a table satisfying DEC takes the decrement's
    step**: its bit, borrow and last flag are Booleans, the last bit is set
    (canonical), its next borrow is the step's, it is rewritten exactly
    under a borrow unless it is the dropped top, and the slot its written
    bit points at is the step's bit's (`K` at 0 when set, `K I` at 2 when
    clear). -/
theorem decStep_sound (T : Table) (hT : Sat Dec.decAir T) (r : Nat) (hr : r < T.h) (hk : T.main r Dec.KCONS = 1) :
    ∃ b bw last : Bool,
      T.main r Dec.BIT = (if b then 1 else 0) ∧ T.main r Dec.BW = (if bw then 1 else 0) ∧
      T.main r Dec.ISLAST = (if last then 1 else 0) ∧
      (last = true → b = true) ∧
      T.main r Dec.NBW = (if (decStep b bw).2 then 1 else 0) ∧
      T.main r Dec.WRITES = (if bw && !(b && last) then 1 else 0) ∧
      T.main r Dec.PTR = (if (decStep b bw).1 then 0 else 2) := by
  have hc : ∀ c ∈ Dec.decCons, c.eval (T.env r) = 0 := fun c hc => hT.2 c hc r hr
  have mem : ∀ i e, Dec.decCons[i]? = some e → e ∈ Dec.decCons := fun _ _ h => List.mem_of_getElem? h
  have ev : ∀ i, (col i).eval (T.env r) = T.main r i := fun i => by
    show T.main ((r + 0) % T.h) i = _
    rw [Nat.add_zero, Nat.mod_eq_of_lt hr]
  have hbit := hc _ (mem 9 _ rfl)
  have hlast := hc _ (mem 10 _ rfl)
  have hbw := hc _ (mem 11 _ rfl)
  have hcanon := hc _ (mem 14 _ rfl)
  have hnbw := hc _ (mem 15 _ rfl)
  have hdrop := hc _ (mem 16 _ rfl)
  have hwr := hc _ (mem 17 _ rfl)
  have hptr := hc _ (mem 21 _ rfl)
  simp only [E.eval, B.bool, B.eq, B.one, B.c, ev, ofN_one] at hbit hlast hbw hcanon hnbw hdrop hwr hptr
  rw [hk] at hcanon hptr
  have hnbw' := sub_eq_zero hnbw
  have hdrop' := sub_eq_zero hdrop
  have hwr' := sub_eq_zero hwr
  have hptr' := sub_eq_zero hptr
  rcases bit_of hbit with hb | hb <;> rcases bit_of hbw with hw | hw <;> rcases bit_of hlast with hl | hl <;>
    rw [hb, hl] at hcanon <;> rw [hw, hb] at hnbw' <;> rw [hw, hb, hl] at hdrop' <;> rw [hw, hdrop'] at hwr' <;>
    rw [hb, hw] at hptr'
  · refine ⟨false, false, false, hb, hw, hl, (fun h => nomatch h), ?_, ?_, ?_⟩
    · rw [hnbw']; decide
    · rw [hwr']; decide
    · rw [hptr']; decide
  · exact absurd hcanon (by decide)
  · refine ⟨false, true, false, hb, hw, hl, (fun h => nomatch h), ?_, ?_, ?_⟩
    · rw [hnbw']; decide
    · rw [hwr']; decide
    · rw [hptr']; decide
  · exact absurd hcanon (by decide)
  · refine ⟨true, false, false, hb, hw, hl, fun _ => rfl, ?_, ?_, ?_⟩
    · rw [hnbw']; decide
    · rw [hwr']; decide
    · rw [hptr']; decide
  · refine ⟨true, false, true, hb, hw, hl, fun _ => rfl, ?_, ?_, ?_⟩
    · rw [hnbw']; decide
    · rw [hwr']; decide
    · rw [hptr']; decide
  · refine ⟨true, true, false, hb, hw, hl, fun _ => rfl, ?_, ?_, ?_⟩
    · rw [hnbw']; decide
    · rw [hwr']; decide
    · rw [hptr']; decide
  · refine ⟨true, true, true, hb, hw, hl, fun _ => rfl, ?_, ?_, ?_⟩
    · rw [hnbw']; decide
    · rw [hwr']; decide
    · rw [hptr']; decide

-- ---------------------------------------------------------------------------
-- A row of DEC: its kind, its role, its level
-- ---------------------------------------------------------------------------

section Row

variable {T : Table} (hT : Sat Dec.decAir T) {r : Nat} (hr : r < T.h)
include hT hr

theorem dec_cons {i : Nat} {e : E} (he : Dec.decCons[i]? = some e) : e.eval (T.env r) = 0 :=
  hT.2 e (List.mem_of_getElem? he) r hr

theorem dec_ev (i : Nat) : (col i).eval (T.env r) = T.main r i := by
  show T.main ((r + 0) % T.h) i = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hr]

/-- **The kind is one-hot or empty**: each kind's column is a bit, and so
    is their sum. -/
theorem dec_kinds :
    (T.main r Dec.KCELL = 0 ∨ T.main r Dec.KCELL = 1) ∧ (T.main r Dec.KATOM = 0 ∨ T.main r Dec.KATOM = 1) ∧
    (T.main r Dec.KCONS = 0 ∨ T.main r Dec.KCONS = 1) ∧ (T.main r Dec.KNIL = 0 ∨ T.main r Dec.KNIL = 1) ∧
    (T.main r Dec.KCELL + T.main r Dec.KATOM + T.main r Dec.KCONS + T.main r Dec.KNIL = 0 ∨
      T.main r Dec.KCELL + T.main r Dec.KATOM + T.main r Dec.KCONS + T.main r Dec.KNIL = 1) := by
  have h0 := dec_cons hT hr (i := 0) rfl
  have h1 := dec_cons hT hr (i := 1) rfl
  have h2 := dec_cons hT hr (i := 2) rfl
  have h3 := dec_cons hT hr (i := 3) rfl
  have h4 := dec_cons hT hr (i := 4) rfl
  simp only [E.eval, B.bool, B.one, B.c, dec_ev hT hr, ofN_one] at h0 h1 h2 h3 h4
  exact ⟨bit_of h0, bit_of h1, bit_of h2, bit_of h3, bit_of h4⟩

/-- **A wrapper row's role**: the subject (`RO = 0`, `H0`), the head
    (`RO = 1`, `H1`), or a tail noun (`RO = 2`). -/
theorem dec_role (hk : T.main r Dec.KCELL + T.main r Dec.KATOM = 1) :
    (T.main r Dec.H0 = 1 ∧ T.main r Dec.H1 = 0 ∧ T.main r Dec.RO = 0) ∨
    (T.main r Dec.H0 = 0 ∧ T.main r Dec.H1 = 1 ∧ T.main r Dec.RO = 1) ∨
    (T.main r Dec.H0 = 0 ∧ T.main r Dec.H1 = 0 ∧ T.main r Dec.RO = 2) := by
  have h5 := dec_cons hT hr (i := 5) rfl
  have h6 := dec_cons hT hr (i := 6) rfl
  have h7 := dec_cons hT hr (i := 7) rfl
  have h8 := dec_cons hT hr (i := 8) rfl
  simp only [E.eval, B.bool, B.one, B.c, dec_ev hT hr, ofN_one] at h5 h6 h7 h8
  rw [hk, one_mul'] at h8
  have h8' := sub_eq_zero h8
  rcases bit_of h5 with a | a <;> rcases bit_of h6 with b | b <;> rw [a, b] at h8' <;> rw [a, b] at h7
  · exact .inr (.inr ⟨a, b, by rw [h8']; decide⟩)
  · exact .inr (.inl ⟨a, b, by rw [h8']; decide⟩)
  · exact .inl ⟨a, b, by rw [h8']; decide⟩
  · exact absurd h7 (by decide)

/-- The level's bits read below `2^n`. -/
theorem dec_levelVal_lt : ∀ n, n ≤ Dec.NLB →
    (((List.range n).foldl (fun v i => E.add v (E.mul (col (Dec.LB + i)) (c (2 ^ i)))) zero).eval
      (T.env r)).val < 2 ^ n := by
  intro n
  induction n with
  | zero => intro _; show (0 : Nat) < 1; decide
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := ih (Nat.le_of_succ_le hn)
    generalize (List.foldl (fun v i => E.add v (E.mul (col (Dec.LB + i)) (c (2 ^ i)))) zero (List.range n)) = X at ih ⊢
    have hmem : B.bool (col (Dec.LB + n)) ∈ Dec.decCons := by
      unfold Dec.decCons
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩
    have hb := hT.2 _ hmem r hr
    simp only [E.eval, B.bool, B.one, B.c, dec_ev hT hr, ofN_one] at hb
    simp only [E.eval, B.col, B.c, env_main0 hr]
    generalize X.eval (T.env r) = x at ih ⊢
    have hpow : 2 ^ (n + 1) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hn
    have hP : 2 ^ 5 < P := by decide
    rcases bit_of hb with e | e <;> rw [e]
    · rw [zero_mul', add_zero']
      exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
    · rw [one_mul', val_add_nat (by rw [Nat.pow_succ] at hpow; omega), Nat.pow_succ]
      omega

/-- **A bit of the head is below the jet's width**: on a `Cons` row in
    mode `0` (the head's bits), the level is below `W = 32`. -/
theorem dec_level (hk : T.main r Dec.KCONS = 1) (hm : T.main r Dec.MODE = 0) :
    (T.main r Dec.LVL).val < DecJet.W := by
  have h40 := dec_cons hT hr (i := 40) rfl
  simp only [E.eval, B.one, B.c, dec_ev hT hr, ofN_one, hk, hm] at h40
  have e : T.main r Dec.LVL = Dec.levelVal.eval (T.env r) := by
    simp only [show (1 - 0 : F) = 1 from rfl, one_mul'] at h40
    exact sub_eq_zero h40
  rw [e]
  exact dec_levelVal_lt hT hr Dec.NLB (Nat.le_refl _)

/-- **`dec_sound_row`: every row of a table that satisfies DEC** has one
    kind or none; a wrapper row has a role; a `Cons` row takes the
    decrement's borrow step (`decStep_sound`), and in mode `0` its level is
    below `W`. -/
theorem dec_sound_row :
    (T.main r Dec.KCELL + T.main r Dec.KATOM + T.main r Dec.KCONS + T.main r Dec.KNIL = 0 ∨
      T.main r Dec.KCELL + T.main r Dec.KATOM + T.main r Dec.KCONS + T.main r Dec.KNIL = 1) ∧
    (T.main r Dec.KCELL + T.main r Dec.KATOM = 1 →
      (T.main r Dec.H0 = 1 ∧ T.main r Dec.H1 = 0 ∧ T.main r Dec.RO = 0) ∨
      (T.main r Dec.H0 = 0 ∧ T.main r Dec.H1 = 1 ∧ T.main r Dec.RO = 1) ∨
      (T.main r Dec.H0 = 0 ∧ T.main r Dec.H1 = 0 ∧ T.main r Dec.RO = 2)) ∧
    (T.main r Dec.KCONS = 1 →
      (∃ b bw last : Bool,
        T.main r Dec.BIT = (if b then 1 else 0) ∧ T.main r Dec.BW = (if bw then 1 else 0) ∧
        T.main r Dec.ISLAST = (if last then 1 else 0) ∧ (last = true → b = true) ∧
        T.main r Dec.NBW = (if (decStep b bw).2 then 1 else 0) ∧
        T.main r Dec.WRITES = (if bw && !(b && last) then 1 else 0) ∧
        T.main r Dec.PTR = (if (decStep b bw).1 then 0 else 2)) ∧
      (T.main r Dec.MODE = 0 → (T.main r Dec.LVL).val < DecJet.W)) :=
  ⟨(dec_kinds hT hr).2.2.2.2, dec_role hT hr, fun hk => ⟨decStep_sound T hT r hr hk, dec_level hT hr hk⟩⟩

end Row

end Circuit
