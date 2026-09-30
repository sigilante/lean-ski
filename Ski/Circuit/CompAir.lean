import Ski.Circuit.Selectors
import Ski.Composed

/-!
# The composed circuit, as data

The five AIRs of `bench/plonky3/src/composed.rs` for a statement — a
formula `M` and a region of `W` cells, the pair `lake exe composed
statement` checks — as its verifier builds them (`airs`): the CPU with the
restart kind, a segment counter, the `segs` lookup, two blinding messages
and the last row's `HK1`; the memory with a blinding message; the program
table of the public cells; the witness table of the bit and region cells;
the segment table of the roots.  `lake exe circuit compare-composed`
checks the Rust export (`ski-air export-composed PUBLIC`) against it.
-/

namespace Circuit

open B Compose CompM

-- The composed CPU's extra columns (`src/main.rs`, `src/composed.rs`).
def BLA : Nat := CPU_WIDTH
def BLB : Nat := CPU_WIDTH + 5
def RS : Nat := CPU_WIDTH + 10
def CNT : Nat := RS + 1
def ROOT : Nat := RS + 2

def sRS : E := col RS

/-- A blinding message's tuple and flag, from column `c`. -/
def blindFields (c : Nat) : List E := [col c, col (c + 1), col (c + 2), col (c + 3)]

/-- The tags, with the restart kind's (`K` at the head, a nil at the stack). -/
def tagsC : List E :=
  [.add (.add (.add (.add (.mul (.add (.add sK sHK1) sHK2) (c 1)) (.mul (.add sI sHI1) (c 2)))
      (.mul sApp (c 3))) (.mul (.add sHA sPLater) (c 6))) (.mul sRS (c 1)),
   .add (.mul (sum [sI, sK, sS, sHK2, sHS2, sHS3]) (c 5)) (.mul (sum [sHI1, sHK1, sHS1, sRS]) (c 4)),
   .add (.mul (sum [sK, sS, sHS3]) (c 5)) (.mul (.add sHK2 sHS2) (c 4)),
   .add (.mul sS (c 5)) (.mul sHS3 (c 4))]

def readInterC (j : Nat) : Inter :=
  ⟨"mem", 1, acts.getD j zero, [addrs.getD j zero, tagsC.getD j zero, fld (2 * j), fld (2 * j + 1)]⟩

/-- **The composed CPU's constraints**, in the Rust's order: `n` segments,
    each starting over the nil at `nilA`. -/
def cpuConsC (hd0 stk0 ctr0 n nilA : Nat) : List E :=
  (List.range NKINDS).map (fun i => B.bool (col (SEL + i))) ++ [bool sRS] ++
  [eq (sum ((List.range NKINDS).map (fun i => col (SEL + i)) ++ [sRS])) one] ++
  readCons 0 ++ readCons 1 ++ readCons 2 ++ readCons 3 ++
  [sInst, sPFirst, sPLater,
   whenFirst (col CNT), whenTrans (eq (nxt CNT) (.add (col CNT) sRS)), whenLast (eq (col CNT) (c (n - 1))),
   whenTrans (eq (nxt HD) (.add nextHd (.mul sRS (col ROOT)))),
   whenTrans (eq (nxt STK) (.add nextStk (.mul sRS (c nilA)))),
   whenTrans (eq (nxt CTR) nextCtr),
   whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
   whenLast (eq halt one),
   B.bool (col (BLA + 4)), B.bool (col (BLB + 4)),
   whenLast (eq sHK1 one)]

def cpuIntersC : List Inter :=
  [readInterC 0, readInterC 1, readInterC 2, readInterC 3] ++ writeInters ++
  [⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩,
   ⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩,
   ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩]

def cpuAirC (hd0 stk0 ctr0 n nilA : Nat) : AirD :=
  ⟨"cpu", ROOT + 1, 0, cpuConsC hd0 stk0 ctr0 n nilA, cpuIntersC, []⟩

/-- The memory table, with a blinding message. -/
def memAirC : AirD :=
  ⟨"mem", 10, 0, [whenFirst (col 0), whenTrans (eq (nxt 0) (.add (col 0) one)), B.bool (col 9)],
    [⟨"mem", 0, .neg (col 4), [col 0, col 1, col 2, col 3]⟩,
     ⟨"blind_b", 1, .neg (col 9), blindFields 5⟩], []⟩

-- The witness table's columns (`src/witness.rs`).
def WT_A : Nat := 4
def WT_B : Nat := 5
def WT_BITS : Nat := 6
def WT_BLIND : Nat := WT_BITS + 4 * RANGE_BITS

/-- A witness row's 24-bit number `k`. -/
def wnum (k : Nat) : E :=
  (List.range RANGE_BITS).foldl (fun v i => .add v (.mul (col (WT_BITS + k * RANGE_BITS + i)) (c (2 ^ i)))) zero

/-- **The witness table's constraints**: one kind per active row; a
    combinator's fields zero; an application's pointers below `2^24` and
    below its address; in bit mode, `K` or `A 0 1`. -/
def witCons : List E :=
  let fl := fun q => col q
  let app := fl 3
  let (pa, pb) := (col WT_A, col WT_B)
  let (addr, act, bit) := (prec 0, prec 1, prec 2)
  (List.range 4).map (fun q => B.bool (fl q)) ++
  [eq (.add (.add (.add (fl 0) (fl 1)) (fl 2)) (fl 3)) act,
   .mul (.sub one app) pa, .mul (.sub one app) pb] ++
  (List.range (4 * RANGE_BITS)).map (fun i => B.bool (col (WT_BITS + i))) ++
  [.mul app (.sub pa (wnum 0)), .mul app (.sub (.sub (.sub addr pa) one) (wnum 1)),
   .mul app (.sub pb (wnum 2)), .mul app (.sub (.sub (.sub addr pb) one) (wnum 3)),
   .mul bit (.add (fl 0) (fl 2)), .mul bit pa, .mul bit (.sub pb app),
   B.bool (col (WT_BLIND + 4))]

def witInters : List Inter :=
  [⟨"mem", 1, prec 1, [prec 0, .add (.add (col 1) (.mul (col 2) (c 2))) (.mul (col 3) (c 3)), col WT_A, col WT_B]⟩,
   ⟨"blind_a", 1, col (WT_BLIND + 4), blindFields WT_BLIND⟩]

/-- `pow2_at_least n log`: the least power of two at least `n` and `2^log`. -/
def pow2Min (lg n : Nat) : Nat := pow2From 64 (2 ^ lg) n

/-- The witness table's preprocessed rows, from base address `a0`: the bit
    cells in bit mode, then the region's, padded to `2^8`. -/
def witRowsG (a0 N W : Nat) : List (List F) :=
  let rows := (List.range N).map (fun i => [ofN (a0 + i), ofN 1, ofN 1]) ++
    (List.range W).map (fun i => [ofN (a0 + N + i), ofN 1, ofN 0])
  rows ++ List.replicate (2 ^ 8 - rows.length) [ofN 0, ofN 0, ofN 0]

/-- The composed circuit's: the bits at `3` on. -/
def witRows (N W : Nat) : List (List F) := witRowsG 3 N W

def witAir (N W : Nat) : AirD := ⟨"wit", WT_BLIND + 5, 3, witCons, witInters, witRows N W⟩

/-- The segment table: `(j, root_j)`, padded with the first. -/
def segRows (roots : List Nat) : List (List F) :=
  let rows := roots.zipIdx.map fun (r, j) => [ofN j, ofN r]
  rows ++ List.replicate (pow2Min 8 rows.length - rows.length) (rows.headD [])

def segsAir (roots : List Nat) : AirD :=
  ⟨"segs", 1, 2, [], [⟨"segs", 0, .neg (col 0), [prec 0, prec 1]⟩], segRows roots⟩

/-- The program table of the public cells: every cell outside the private
    addresses `[3, 3 + N + W)`, padded to `2^8`. -/
def progRowsC (heap : List Cell) (N W : Nat) : List (List F) :=
  let rows := (heap.zipIdx.filter fun (_, i) => !(3 ≤ i && i < 3 + N + W)).map
    fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1]
  rows ++ List.replicate (pow2Min 8 rows.length - rows.length) [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0]

def progAirC (heap : List Cell) (N W : Nat) : AirD :=
  ⟨"prog", 1, 5, [col 0], [⟨"mem", 1, prec 4, [prec 0, prec 1, prec 2, prec 3]⟩], progRowsC heap N W⟩

/-- **The composed circuit for an evaluation statement**: bits of the
    shape `shp`, a region of `W` cells, and the terms `Ps`, each to evaluate
    to `K` on the bits and the region's witness. -/
def compAirsG (shp : BT) (Ps : List Term) (W : Nat) : List AirD :=
  let N := BT.nleaves shp
  let region := List.replicate W Cell.S
  let m := cMachine (fun _ => false) shp region Ps
  let roots := (cHeap (fun _ => false) shp region Ps).2
  [cpuAirC m.hd m.stk m.heap.length roots.length m.stk, memAirC,
   progAirC m.heap N W,
   witAir N W, segsAir roots]

/-- **The composed circuit for a formula**: what its verifier builds. -/
def compAirs (M : MF) (W : Nat) : List AirD := compAirsG (clear M) (stmtOf M) W

end Circuit
