import Ski.Circuit.CompAir
import Ski.Circuit.CompJAir
import Ski.Circuit.P2Air
import Ski.ComposedPText

/-!
# The composed circuit with the Poseidon2 jet, as data

The nine AIRs of `bench/plonky3/src/compp.rs` for a statement `p2pre h`
(`ComposedPText.publicTextP`), as its verifier builds them (`airs`):

- the composed circuit's five (`Ski/Circuit/CompAir.lean`), the CPU
  carrying the jet's row: a selector `P2SEL` after the restart columns,
  then a blinding block sent to P2IN on `blind_c`,
  whose row reads the atom `J` at the head and the stack cells `cons k s₁`
  and `s₁ ↦ cons β rest`, with `β` the comb's root, and the slots;
- P2IN, one row per input bit, reading the bit's slot;
- P2OUT, one row per output bit, writing its stack cell;
- the keyed Poseidon2 table (`P2Air.p2Air`);
- P2IDX, the public table of the bits' levels.

P2IN, P2OUT and P2 carry blinding blocks (`withBlocks`), the blinding
tree's edges `CPU —c— P2IN —d— P2OUT —e— P2`.

`lake exe circuit compare-compp` checks the Rust export (`ski-air
export-compp PUBLIC`) against it.
-/

namespace Circuit

open B Compose CompM

-- The jet's CPU column, after the restart columns.
def P2SEL : Nat := ROOT + 1
def sP2 : E := col P2SEL

/-- The reads' activities: read 2 is the jet row's too. -/
def actsP : List E :=
  [.sub (.sub one sInst) sPFirst,
   .sub (.sub (.sub (.sub one sApp) sHA) sInst) (.add sPFirst sPLater),
   sum [sK, sS, sHK2, sHS2, sHS3, sP2],
   .add sS sHS3]

/-- The tags, with the jet row's: an atom at the head, two stack cells. -/
def tagsP : List E :=
  [.add (.add (.add (.add (.add (.mul (.add (.add sK sHK1) sHK2) (c 1)) (.mul (.add sI sHI1) (c 2)))
      (.mul sApp (c 3))) (.mul (.add sHA sPLater) (c 6))) (.mul sRS (c 1))) (.mul sP2 (c 6)),
   .add (.add (.mul (sum [sI, sK, sS, sHK2, sHS2, sHS3]) (c 5)) (.mul (sum [sHI1, sHK1, sHS1, sRS]) (c 4)))
      (.mul sP2 (c 5)),
   .add (.add (.mul (sum [sK, sS, sHS3]) (c 5)) (.mul (.add sHK2 sHS2) (c 4))) (.mul sP2 (c 5)),
   .add (.mul sS (c 5)) (.mul sHS3 (c 4))]

def readConsP (j : Nat) : List E :=
  (List.range RANGE_BITS).map (fun i => bool (col (BITS + j * RANGE_BITS + i))) ++
    [.mul (actsP.getD j zero) (.sub (.sub (.sub (col CTR) (addrs.getD j zero)) one) (rangeVal j))]

def readInterP (j : Nat) : Inter :=
  ⟨"mem", 1, actsP.getD j zero, [addrs.getD j zero, tagsP.getD j zero, fld (2 * j), fld (2 * j + 1)]⟩

/-- The inputs' bits. -/
def P2_BITS : Nat := 496

/-- **The CPU's constraints**, in the Rust's order: `n` segments over the
    nil at `nilA`, the jet's atom `J` and the comb's root `root`. -/
def cpuConsP2 (hd0 stk0 ctr0 n nilA J root : Nat) : List E :=
  (List.range NKINDS).map (fun i => B.bool (col (SEL + i))) ++ [bool sRS, bool sP2] ++
  [eq (sum ((List.range NKINDS).map (fun i => col (SEL + i)) ++ [sRS, sP2])) one] ++
  readConsP 0 ++ readConsP 1 ++ readConsP 2 ++ readConsP 3 ++
  [sInst, sPFirst, sPLater,
   whenFirst (col CNT), whenTrans (eq (nxt CNT) (.add (col CNT) sRS)), whenLast (eq (col CNT) (c (n - 1))),
   .mul sP2 (.sub (fld 0) (c J)), .mul sP2 (.sub (fld 4) (c root)), B.bool (col (P2SEL + 5)),
   whenTrans (eq (nxt HD) (.add (.add nextHd (.mul sRS (col ROOT))) (.mul sP2 (fld 2)))),
   whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sRS (c nilA))) (.mul sP2 (.add (col CTR) (c (P2_BITS - 1)))))),
   whenTrans (eq (nxt CTR) (.add nextCtr (.mul sP2 (c P2_BITS)))),
   whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
   whenLast (eq halt one),
   B.bool (col (BLA + 4)), B.bool (col (BLB + 4)),
   whenLast (eq sHK1 one)]

def cpuIntersP2 : List Inter :=
  [readInterP 0, readInterP 1, readInterP 2, readInterP 3] ++ writeInters ++
  [⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩,
   -- The slots: `K`, `I`, `K I` at 0, 1, 2.
   ⟨"mem", 1, sP2, [c 0, c 1, c 0, c 0]⟩,
   ⟨"mem", 1, sP2, [c 1, c 2, c 0, c 0]⟩,
   ⟨"mem", 1, sP2, [c 2, c 3, c 0, c 1]⟩,
   -- The input chain, then the output chain.
   ⟨"p2i", 1, sP2, [col CTR, c 0, c 0]⟩,
   ⟨"p2i", 1, .neg sP2, [col CTR, c P2_BITS, c 0]⟩,
   ⟨"p2o", 1, sP2, [col CTR, c 0, fld 5, c 0, c 0, c 1]⟩,
   ⟨"p2o", 1, .neg sP2, [col CTR, c P2_BITS, fld 5, c 0, c 0, c 1]⟩,
   -- The blinding tree's edge to P2IN.
   blindMsg "blind_c" (P2SEL + 1) true,
   ⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩,
   ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩]

def cpuAirP2 (hd0 stk0 ctr0 n nilA J root : Nat) : AirD :=
  ⟨"cpu", P2SEL + 6, 0, cpuConsP2 hd0 stk0 ctr0 n nilA J root, cpuIntersP2, []⟩

/-- The witness table's rows, padded to a power of two at least `2^8`. -/
def witRowsP (N W : Nat) : List (List F) :=
  let rows := (List.range N).map (fun i => [ofN (3 + i), ofN 1, ofN 1]) ++
    (List.range W).map (fun i => [ofN (3 + N + i), ofN 1, ofN 0])
  rows ++ List.replicate (pow2Min 8 rows.length - rows.length) [ofN 0, ofN 0, ofN 0]

def witAirP (N W : Nat) : AirD := ⟨"wit", WT_BLIND + 5, 3, witCons, witInters, witRowsP N W⟩

-- ---------------------------------------------------------------------------
-- The jet's tables
-- ---------------------------------------------------------------------------

/-- P2IN: `ctr lvl b acc act e pow last islow ilast val nacc em`.  The bit
    `lvl` is the slot `3 + lvl`: a `K` cell when true, `app 0 1` when false. -/
def p2inAir : AirD :=
  let v := fun i => col i
  ⟨"p2in", 13, 0,
    [bool (v 4), bool (v 2), eq (v 10) (.add (v 3) (.mul (v 6) (v 2))),
     eq (v 11) (.mul (.sub one (v 7)) (v 10)), eq (v 12) (.mul (v 4) (v 7))],
    [⟨"p2idx", 1, v 4, [v 1, v 5, v 6, v 7, v 8, v 9]⟩,
     ⟨"p2i", 1, .neg (v 4), [v 0, v 1, v 3]⟩,
     ⟨"p2i", 1, v 4, [v 0, .add (v 1) one, v 11]⟩,
     ⟨"mem", 1, v 4, [.add (v 1) (c 3), .sub (c 3) (.mul (v 2) (c 2)), c 0, .sub one (v 2)]⟩,
     ⟨"p2v", 1, v 12, [v 0, v 5, v 10]⟩], []⟩

/-- P2OUT: `ctr lvl rest b acc low hi act e pow last islow ilast val nacc
    nlow nhi nlowr nhir em addr prev ptr`. -/
def p2outAir : AirD :=
  let v := fun i => col i
  ⟨"p2out", 23, 0,
    [bool (v 7), bool (v 3), eq (v 13) (.add (v 4) (.mul (v 9) (v 3))),
     eq (v 14) (.mul (.sub one (v 10)) (v 13)),
     eq (v 15) (.add (v 5) (.mul (.mul (v 11) (v 3)) (.sub one (v 5)))),
     eq (v 16) (.mul (v 6) (.add (v 11) (.mul (.sub one (v 11)) (v 3)))),
     .mul (.mul (v 10) (v 16)) (v 15),
     eq (v 17) (.mul (.sub one (v 10)) (v 15)),
     eq (v 18) (.add (.mul (.sub one (v 10)) (v 16)) (v 10)),
     eq (v 19) (.mul (v 7) (v 10)),
     .mul (v 7) (.sub (v 20) (.sub (.add (v 0) (c (P2_BITS - 1))) (v 1))),
     .mul (v 7) (.sub (v 21) (.add (.mul (v 12) (v 2)) (.mul (.sub one (v 12)) (.sub (v 20) one)))),
     .mul (v 7) (.sub (v 22) (.sub (c 2) (.mul (c 2) (v 3))))],
    [⟨"p2idx", 1, v 7, [v 1, v 8, v 9, v 10, v 11, v 12]⟩,
     ⟨"p2o", 1, .neg (v 7), [v 0, v 1, v 2, v 4, v 5, v 6]⟩,
     ⟨"p2o", 1, v 7, [v 0, .add (v 1) one, v 2, v 14, v 17, v 18]⟩,
     ⟨"mem", 1, v 7, [v 20, c 5, v 22, v 21]⟩,
     ⟨"p2w", 1, .neg (v 19), [v 0, v 8, v 13]⟩], []⟩

/-- P2IDX's rows: `lvl e pow last islow ilast` for each level, padded to
    `2^9` with the first. -/
def idxRow (l : Nat) : List F :=
  let j := l % 31
  [ofN l, ofN (l / 31), ofN (2 ^ j), ofN (if j = 30 then 1 else 0), ofN (if j < 27 then 1 else 0),
   ofN (if l = P2_BITS - 1 then 1 else 0)]

def idxRows : List (List F) :=
  (List.range P2_BITS).map idxRow ++ List.replicate (512 - P2_BITS) (idxRow 0)

def p2idxAir : AirD := ⟨"p2idx", 1, 6, [], [⟨"p2idx", 0, .neg (col 0), (List.range 6).map prec⟩], idxRows⟩

/-- The jet's private tables with their blinding blocks: the blinding tree's
    edges `CPU —c— P2IN —d— P2OUT —e— P2`. -/
def p2inAirB : AirD := withBlocks p2inAir [("blind_c", false), ("blind_d", true)]
def p2outAirB : AirD := withBlocks p2outAir [("blind_d", false), ("blind_e", true)]
def p2AirB : AirD := withBlocks P2Air.p2Air [("blind_e", false)]

/-- **The composed circuit with the Poseidon2 jet for `p2pre h`**: what its
    verifier builds. -/
def compPAirs (h : Nat) : List AirD :=
  let N := BT.nleaves ComposedPText.shpP
  let W := ComposedPText.regionP.length
  let ρ0 : Nat → Bool := fun _ => false
  let m := cMachineO ρ0 ComposedPText.shpP ComposedPText.regionP (ComposedPText.VsP h)
  let roots := (cHeapO ρ0 ComposedPText.shpP ComposedPText.regionP (ComposedPText.VsP h)).2
  [cpuAirP2 m.hd m.stk m.heap.length roots.length m.stk ComposedPText.JP2 ComposedPText.rootP, memAirC,
   progAirC m.heap N W, witAirP N W, segsAir roots, p2inAirB, p2outAirB, p2AirB, p2idxAir]

end Circuit
