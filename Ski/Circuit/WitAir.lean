import Ski.Circuit.CompAir
import Ski.WitnessText

/-!
# The hidden-term circuit, as data

The four AIRs of `bench/plonky3/src/witness.rs` for a statement — an atom
`V x` and a region of `W` cells, the pair `lake exe witness statement`
checks — as its verifier builds them (`airs`): the corpus CPU with two
blinding messages and the last row's `HK1`; the memory with a blinding
message (`memAirC`); the program table of the public cells; the witness
table of the region, at addresses `0` to `W - 1`.  `lake exe circuit
compare-witness` checks the Rust export against it.
-/

namespace Circuit

open B Wit

/-- **The witness circuit's CPU**: the corpus CPU, blinded, ending at `HK1`. -/
def cpuConsW (hd0 stk0 ctr0 : Nat) : List E :=
  cpuCons hd0 stk0 ctr0 ++ [B.bool (col (BLA + 4)), B.bool (col (BLB + 4)), whenLast (eq sHK1 one)]

def cpuIntersW : List Inter :=
  cpuInters ++ [⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩,
    ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩]

def cpuAirW (hd0 stk0 ctr0 : Nat) : AirD := ⟨"cpu", CPU_WIDTH + 10, 0, cpuConsW hd0 stk0 ctr0, cpuIntersW, []⟩

/-- The program table of the public cells: every cell outside the region
    `[0, W)`, padded to `2^8`. -/
def progRowsW (heap : List Cell) (W : Nat) : List (List F) :=
  let rows := (heap.zipIdx.filter fun (_, i) => !(i < W)).map
    fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1]
  rows ++ List.replicate (pow2Min 8 rows.length - rows.length) [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0]

def progAirW (heap : List Cell) (W : Nat) : AirD :=
  ⟨"prog", 1, 5, [col 0], [⟨"mem", 1, prec 4, [prec 0, prec 1, prec 2, prec 3]⟩], progRowsW heap W⟩

/-- The witness table's rows: the region's addresses, active, not in bit
    mode, padded to `2^8`. -/
def witRowsW (W : Nat) : List (List F) :=
  (List.range W).map (fun i => [ofN i, ofN 1, ofN 0]) ++ List.replicate (2 ^ 8 - W) [ofN 0, ofN 0, ofN 0]

def witAirW (W : Nat) : AirD := ⟨"wit", WT_BLIND + 5, 3, witCons, witInters, witRowsW W⟩

/-- **The witness circuit for a statement**: what its verifier builds. -/
def witAirs (V x : Term) (W : Nat) : List AirD :=
  let m := wMachine (List.replicate W .S) (V ⬝ x)
  [cpuAirW m.hd m.stk m.heap.length, memAirC, progAirW m.heap W, witAirW W]

end Circuit
