import Ski.Circuit.CompAir
import Ski.Circuit.JetAir
import Ski.JetPublic

/-!
# The composed circuit with jets, as data

The ten AIRs of `bench/plonky3/src/compj.rs` for a composed statement and
its jet table, as its verifier builds them (`airs`), constraint for
constraint and message for message in the order the Rust emits them
(Avon's `docs/ZK-JETS.md` §4–§5).  `lake exe circuit compare-compJ`
checks the Rust export (`ski-air export-compj PUBLIC JETS`) against it.

- **The CPU** is the composed CPU and the jet CPU at once: the jet columns
  at 121–130 (as in `JetAir`), three blinding blocks at 131, 136 and 141
  (`blind_a` received from the witness table, `blind_b` sent to memory,
  `blind_c` sent to POP), then the restart columns at 146–148.  The
  restart selector sits outside the kinds, so the `INST` kind (selector
  11) and the restart are distinct columns.
- **Memory**, **program**, **witness** and **segments** are the composed
  circuit's.
- **ROOTS**, **HDR** and **TMPL** are the jet table's providers, padded to
  at least `2^8` rows as the hiding PCS needs; **POP** and **INSTW** are
  the jet circuit's.  Each carries the blocks of its edges in the
  blinding tree `WIT —a— CPU —b— MEM`, `CPU —c— POP —d— INSTW —e— TMPL
  —f— HDR —g— ROOTS`: a received block (count `-flag`), then a sent one
  (count `flag`).
-/

namespace Circuit

open B JetTable Compose CompM

-- The CPU's columns after the jet columns (`src/main.rs`).
def BLAJ : Nat := CPU_WIDTH + JET_WIDTH
def BLBJ : Nat := BLAJ + 5
def BLCJ : Nat := BLBJ + 5
def RSJ : Nat := BLCJ + 5
def CNTJ : Nat := RSJ + 1
def ROOTJ : Nat := RSJ + 2

def sRSJ : E := col RSJ

/-- A blinding message: the tuple at `c`, counted by the flag at `c + 4`,
    sent (`flag`) or received (`-flag`). -/
def blindMsg (bus : String) (c : Nat) (send : Bool) : Inter :=
  ⟨bus, 1, if send then col (c + 4) else .neg (col (c + 4)), blindFields c⟩

/-- The tags, with the restart kind's at `RSJ`. -/
def tagsCJ : List E :=
  [.add (.add (.add (.add (.mul (.add (.add sK sHK1) sHK2) (c 1)) (.mul (.add sI sHI1) (c 2)))
      (.mul sApp (c 3))) (.mul (.add sHA sPLater) (c 6))) (.mul sRSJ (c 1)),
   .add (.mul (sum [sI, sK, sS, sHK2, sHS2, sHS3]) (c 5)) (.mul (sum [sHI1, sHK1, sHS1, sRSJ]) (c 4)),
   .add (.mul (sum [sK, sS, sHS3]) (c 5)) (.mul (.add sHK2 sHS2) (c 4)),
   .add (.mul sS (c 5)) (.mul sHS3 (c 4))]

def readInterCJ (j : Nat) : Inter :=
  ⟨"mem", 1, acts.getD j zero, [addrs.getD j zero, tagsCJ.getD j zero, fld (2 * j), fld (2 * j + 1)]⟩

/-- **The CPU's constraints**, in the Rust's order: the kinds and the
    restart one-hot, the reads, the instantiation's, no probe, the segment
    counter, the next registers with both an instantiation's and a
    restart's parts, the first and last rows, the three blinding flags,
    and the last row's `HK1`. -/
def cpuConsCJ (hd0 stk0 ctr0 n nilA : Nat) : List E :=
  (List.range NKINDS).map (fun i => bool (col (SEL + i))) ++ [bool sRSJ] ++
  [eq (sum ((List.range NKINDS).map (fun i => col (SEL + i)) ++ [sRSJ])) one] ++
  readCons 0 ++ readCons 1 ++ readCons 2 ++ readCons 3 ++
  [whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
   bool (col J_RL), bool (col J_RA), bool (col J_RG),
   eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst,
   sPFirst, sPLater,
   whenFirst (col CNTJ), whenTrans (eq (nxt CNTJ) (.add (col CNTJ) sRSJ)), whenLast (eq (col CNTJ) (c (n - 1))),
   whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sRSJ (col ROOTJ)))),
   whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST))) (.mul sRSJ (c nilA)))),
   whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N)))),
   whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
   whenLast (eq halt one),
   bool (col (BLAJ + 4)), bool (col (BLBJ + 4)), bool (col (BLCJ + 4)),
   whenLast (eq sHK1 one)]

def cpuIntersCJ : List Inter :=
  [readInterCJ 0, readInterCJ 1, readInterCJ 2, readInterCJ 3] ++ writeInters ++ jetInters ++
  [⟨"segs", 1, sRSJ, [.add (col CNTJ) one, col ROOTJ]⟩,
   blindMsg "blind_a" BLAJ false, blindMsg "blind_b" BLBJ true, blindMsg "blind_c" BLCJ true]

def cpuAirCJ (hd0 stk0 ctr0 n nilA : Nat) : AirD :=
  ⟨"cpu", ROOTJ + 1, 0, cpuConsCJ hd0 stk0 ctr0 n nilA, cpuIntersCJ, []⟩

-- ---------------------------------------------------------------------------
-- The jet tables, blinded
-- ---------------------------------------------------------------------------

/-- An AIR with blinding blocks after its `w` columns: each `(bus, send)`
    a block of five, its flag Boolean. -/
def withBlocks (A : AirD) (blocks : List (String × Bool)) : AirD :=
  ⟨A.name, A.width + 5 * blocks.length, A.pre,
   A.cons ++ blocks.zipIdx.map (fun (_, i) => bool (col (A.width + 5 * i + 4))),
   A.inters ++ blocks.zipIdx.map (fun ((bus, send), i) => blindMsg bus (A.width + 5 * i) send),
   A.pretrace⟩

/-- Pad to a power of two, at least `2^8`, with copies of the first row. -/
def padCopies8 : List (List F) → List (List F)
  | [] => []
  | r :: rs => (r :: rs) ++ List.replicate (pow2Min 8 (rs.length + 1) - (rs.length + 1)) r

def rootsRowsCJ (roots : List (Nat × Nat)) : List (List F) :=
  padCopies8 (roots.map fun (a, g) => [ofN a, ofN g])

def hdrRowsCJ (jets : List Air.Jet) : List (List F) :=
  padCopies8 (jets.zipIdx.map fun (J, g) => hdrRow J g)

def tmplRowsCJ (jets : List Air.Jet) : List (List F) :=
  padCopies8 (jets.zipIdx.flatMap fun (J, g) =>
    (symCells J J.body 0).1.zipIdx.map fun (cl, j) => tmplRow g j cl)

def rootsAirCJ (roots : List (Nat × Nat)) : AirD :=
  withBlocks (providerAir "roots" 2 (rootsRowsCJ roots)) [("blind_g", false)]

def hdrAirCJ (jets : List Air.Jet) : AirD :=
  withBlocks (providerAir "hdr" 7 (hdrRowsCJ jets)) [("blind_f", false), ("blind_g", true)]

def tmplAirCJ (jets : List Air.Jet) : AirD :=
  withBlocks (providerAir "tmpl" 11 (tmplRowsCJ jets)) [("blind_e", false), ("blind_f", true)]

def popAirCJ : AirD := withBlocks popAir [("blind_c", false), ("blind_d", true)]

def instwAirCJ : AirD := withBlocks instwAir [("blind_d", false), ("blind_e", true)]

-- ---------------------------------------------------------------------------
-- The circuit
-- ---------------------------------------------------------------------------

/-- **The composed circuit with jets** for a statement (its bits' shape,
    terms and region size) and its jet table: what the verifier builds. -/
def compJAirs (shp : BT) (Ps : List Term) (W : Nat) (roots : List (Nat × Nat)) (jets : List Air.Jet) :
    List AirD :=
  let N := BT.nleaves shp
  let region := List.replicate W Cell.S
  let m := cMachine (fun _ => false) shp region Ps
  let segRoots := (cHeap (fun _ => false) shp region Ps).2
  [cpuAirCJ m.hd m.stk m.heap.length segRoots.length m.stk, memAirC,
   progAirC m.heap N W,
   witAir N W, segsAir segRoots,
   rootsAirCJ roots, hdrAirCJ jets, tmplAirCJ jets, popAirCJ, instwAirCJ]

/-- **Memory, program, witness and segments are the composed circuit's**,
    so its facts about them carry over. -/
theorem compJAirs_composed (shp : BT) (Ps : List Term) (W : Nat) (roots : List (Nat × Nat))
    (jets : List Air.Jet) : ((compJAirs shp Ps W roots jets).drop 1).take 4 = (compAirsG shp Ps W).drop 1 :=
  rfl

/-- **A table with blinding blocks keeps its constraints and messages**:
    they come first, the blocks' after. -/
theorem withBlocks_cons (A : AirD) (blocks : List (String × Bool)) :
    (withBlocks A blocks).cons.take A.cons.length = A.cons ∧
      (withBlocks A blocks).inters.take A.inters.length = A.inters := by
  unfold withBlocks
  exact ⟨List.take_left' rfl, List.take_left' rfl⟩

end Circuit
