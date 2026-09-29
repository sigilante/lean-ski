import Ski.Circuit.Air
import Ski.Heap

/-!
# The corpus circuit, as data

The three AIRs of `bench/plonky3/src/main.rs` for a public term, as the
verifier builds them (`verifier_airs`): the CPU, the memory table and the
program table, constraint for constraint and message for message in the
order the Rust emits them.  `lake exe circuit compare` checks that the
Rust export (`ski-air export-base TERM`) has the same normal forms.

The CPU's columns: `hd stk ctr` (0–2), fourteen kind selectors (3–16),
eight read fields (17–24), four 24-bit range checks (25–120).
-/

namespace Circuit

open B

-- The CPU's layout (main.rs).
def HD : Nat := 0
def STK : Nat := 1
def CTR : Nat := 2
def SEL : Nat := 3
def NKINDS : Nat := 14
def FLD : Nat := SEL + NKINDS
def BITS : Nat := FLD + 8
def RANGE_BITS : Nat := 24
def CPU_WIDTH : Nat := BITS + 4 * RANGE_BITS

/-- The kinds, by selector index. -/
def sApp : E := col (SEL + 0)
def sI : E := col (SEL + 1)
def sK : E := col (SEL + 2)
def sS : E := col (SEL + 3)
def sHI1 : E := col (SEL + 4)
def sHK1 : E := col (SEL + 5)
def sHK2 : E := col (SEL + 6)
def sHS1 : E := col (SEL + 7)
def sHS2 : E := col (SEL + 8)
def sHS3 : E := col (SEL + 9)
def sHA : E := col (SEL + 10)
def sInst : E := col (SEL + 11)
def sPFirst : E := col (SEL + 12)
def sPLater : E := col (SEL + 13)

def fld (i : Nat) : E := col (FLD + i)

def halt : E := sum [sHI1, sHK1, sHK2, sHS1, sHS2, sHS3, sHA]

def acts : List E :=
  [.sub (.sub one sInst) sPFirst,
   .sub (.sub (.sub (.sub one sApp) sHA) sInst) (.add sPFirst sPLater),
   sum [sK, sS, sHK2, sHS2, sHS3],
   .add sS sHS3]

/-- The tags each read requires (`rs`, the restart selector, is zero here). -/
def tags : List E :=
  [.add (.add (.add (.add (.mul (.add (.add sK sHK1) sHK2) (c 1)) (.mul (.add sI sHI1) (c 2)))
      (.mul sApp (c 3))) (.mul (.add sHA sPLater) (c 6))) (.mul zero (c 1)),
   .add (.mul (sum [sI, sK, sS, sHK2, sHS2, sHS3]) (c 5)) (.mul (sum [sHI1, sHK1, sHS1, zero]) (c 4)),
   .add (.mul (sum [sK, sS, sHS3]) (c 5)) (.mul (.add sHK2 sHS2) (c 4)),
   .add (.mul sS (c 5)) (.mul sHS3 (c 4))]

def addrs : List E := [col HD, col STK, fld 3, fld 5]

/-- A range check's value: its 24 bits, weighted. -/
def rangeVal (j : Nat) : E :=
  (List.range RANGE_BITS).foldl (fun v i => .add v (.mul (col (BITS + j * RANGE_BITS + i)) (c (2 ^ i)))) zero

/-- Read `j`'s constraints: its bits are bits, and when active its address
    is below the counter. -/
def readCons (j : Nat) : List E :=
  (List.range RANGE_BITS).map (fun i => bool (col (BITS + j * RANGE_BITS + i))) ++
    [.mul (acts.getD j zero) (.sub (.sub (.sub (col CTR) (addrs.getD j zero)) one) (rangeVal j))]

def readInter (j : Nat) : Inter :=
  ⟨"mem", 1, acts.getD j zero, [addrs.getD j zero, tags.getD j zero, fld (2 * j), fld (2 * j + 1)]⟩

def writeInters : List Inter :=
  [⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩,
   ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩,
   ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩,
   ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩]

def nextHd : E :=
  .add (.add (.mul sApp (fld 0)) (.mul (.add (.add sI sK) sS) (fld 2))) (.mul halt (col HD))

def nextStk : E :=
  .add (.add (.add (.add (.mul sApp (col CTR)) (.mul sI (fld 3))) (.mul sK (fld 5)))
    (.mul sS (.add (col CTR) (c 2)))) (.mul halt (col STK))

def nextCtr : E := .add (.add (col CTR) sApp) (.mul sS (c 3))

/-- **The CPU's constraints**, in the Rust's order. -/
def cpuCons (hd0 stk0 ctr0 : Nat) : List E :=
  (List.range NKINDS).map (fun i => bool (col (SEL + i))) ++
  [eq (sum ((List.range NKINDS).map fun i => col (SEL + i))) one] ++
  readCons 0 ++ readCons 1 ++ readCons 2 ++ readCons 3 ++
  [sInst, sPFirst, sPLater,
   whenTrans (eq (nxt HD) nextHd), whenTrans (eq (nxt STK) nextStk), whenTrans (eq (nxt CTR) nextCtr),
   whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
   whenLast (eq halt one)]

def cpuInters : List Inter :=
  [readInter 0, readInter 1, readInter 2, readInter 3] ++ writeInters

def cpuAir (hd0 stk0 ctr0 : Nat) : AirD :=
  ⟨"cpu", CPU_WIDTH, 0, cpuCons hd0 stk0 ctr0, cpuInters, []⟩

/-- The memory table: `addr tag a b mult`, one entry per address in order. -/
def memAir : AirD :=
  ⟨"mem", 5, 0, [whenFirst (col 0), whenTrans (eq (nxt 0) (.add (col 0) one))],
    [⟨"mem", 0, .neg (col 4), [col 0, col 1, col 2, col 3]⟩], []⟩

/-- A cell's tag and fields on the bus. -/
def cellTag : Cell → Nat
  | .S => 0
  | .K => 1
  | .I => 2
  | .app _ _ => 3
  | .nil => 4
  | .cons _ _ => 5
  | .atom _ => 6

def cellFields : Cell → Nat × Nat
  | .app f x => (f, x)
  | .cons x r => (x, r)
  | .atom n => (n, 0)
  | _ => (0, 0)

/-- Double `p` until it reaches `n`, within `fuel` doublings. -/
def pow2From : Nat → Nat → Nat → Nat
  | 0, p, _ => p
  | fuel + 1, p, n => if p < n then pow2From fuel (2 * p) n else p

/-- `pow2_at_least n 4`, `n.next_power_of_two().max(16)`: the least power
    of two at least `n` and `16`, by doubling from `16` (exact for
    `n ≤ 2^68`, beyond any `usize`). -/
def pow2AtLeast (n : Nat) : Nat := pow2From 64 16 n

/-- The program table of a heap: its cells with their addresses, padded
    with inactive rows. -/
def programRows (heap : List Cell) : List (List F) :=
  (heap.zipIdx.map fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1]) ++
    List.replicate (pow2AtLeast heap.length - heap.length) [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0]

def progAir (heap : List Cell) : AirD :=
  ⟨"prog", 1, 5, [col 0], [⟨"mem", 1, prec 4, [prec 0, prec 1, prec 2, prec 3]⟩], programRows heap⟩

/-- **The corpus circuit for a term**: what the verifier builds. -/
def baseAirs (t : Term) : List AirD :=
  let m := Mach.load t
  [cpuAir m.hd m.stk m.heap.length, memAir, progAir m.heap]

end Circuit
