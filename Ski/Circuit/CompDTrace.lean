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

end DecT

end Circuit
