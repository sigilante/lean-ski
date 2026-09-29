import Ski.Circuit.Base
import Ski.JetTable

/-!
# The jet circuit, as data

The eight AIRs of `bench/plonky3/src/jets.rs` for a public term and its
jet table, as the jet verifier builds them (`airs`), constraint for
constraint and message for message in the order the Rust emits them.
`lake exe circuit compare-jets` checks that the Rust export (`ski-air
export-jets TERM JETS`) has the same normal forms.

- **The CPU** is the corpus CPU with an instantiation kind (selector 11)
  and ten jet columns (121–130): the row counter `clk`, the jet `g`, its
  arity `k`, cell count `n`, root operand (one-hot local, argument,
  global, and its value), the root's argument, and the rest of the stack.
  An `INST` row looks up `ROOTS(hd, g)` and `HDR(g, …)`, starts and ends
  the chains `POPCH(clk, ctr, i, s)` from `(0, stk)` to `(k, rest)` and
  `WCH(clk, ctr, g, j)` from `0` to `n`, and sets `hd' = root`,
  `stk' = rest`, `ctr' = ctr + n`.
- **ROOTS**, **HDR** and **TMPL** provide the jet table's rows, each as
  often as a committed multiplicity says.
- **POP** reads a stack cell below the counter and provides the argument
  on `ARG`; **INSTW** writes one template cell, its operands resolved.
-/

namespace Circuit

open B JetTable

-- The CPU's jet columns (main.rs).
def J_CLK : Nat := CPU_WIDTH
def J_G : Nat := CPU_WIDTH + 1
def J_K : Nat := CPU_WIDTH + 2
def J_N : Nat := CPU_WIDTH + 3
def J_RL : Nat := CPU_WIDTH + 4
def J_RA : Nat := CPU_WIDTH + 5
def J_RG : Nat := CPU_WIDTH + 6
def J_RV : Nat := CPU_WIDTH + 7
def J_XROOT : Nat := CPU_WIDTH + 8
def J_REST : Nat := CPU_WIDTH + 9
def JET_WIDTH : Nat := 10

/-- An instantiation's next head: the root operand, resolved. -/
def jetHd : E :=
  .add (.add (.mul (col J_RL) (.add (col CTR) (col J_RV))) (.mul (col J_RG) (col J_RV)))
    (.mul (col J_RA) (col J_XROOT))

/-- **The jet CPU's constraints**, in the Rust's order: the corpus CPU's,
    with the instantiation's in place of `inst = 0`. -/
def cpuConsJ (hd0 stk0 ctr0 : Nat) : List E :=
  (List.range NKINDS).map (fun i => bool (col (SEL + i))) ++
  [eq (sum ((List.range NKINDS).map fun i => col (SEL + i))) one] ++
  readCons 0 ++ readCons 1 ++ readCons 2 ++ readCons 3 ++
  [whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
   bool (col J_RL), bool (col J_RA), bool (col J_RG),
   eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst,
   sPFirst, sPLater,
   whenTrans (eq (nxt HD) (.add nextHd jetHd)),
   whenTrans (eq (nxt STK) (.add nextStk (.mul sInst (col J_REST)))),
   whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N)))),
   whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
   whenLast (eq halt one)]

/-- The instantiation's messages. -/
def jetInters : List Inter :=
  [⟨"roots", 1, sInst, [col HD, col J_G]⟩,
   ⟨"hdr", 1, sInst, [col J_G, col J_K, col J_N, col J_RL, col J_RA, col J_RG, col J_RV]⟩,
   ⟨"popch", 1, sInst, [col J_CLK, col CTR, c 0, col STK]⟩,
   ⟨"popch", 1, .neg sInst, [col J_CLK, col CTR, col J_K, col J_REST]⟩,
   ⟨"wch", 1, sInst, [col J_CLK, col CTR, col J_G, c 0]⟩,
   ⟨"wch", 1, .neg sInst, [col J_CLK, col CTR, col J_G, col J_N]⟩,
   ⟨"arg", 1, col J_RA, [col J_CLK, col J_RV, col J_XROOT]⟩]

def cpuAirJ (hd0 stk0 ctr0 : Nat) : AirD :=
  ⟨"cpu", CPU_WIDTH + JET_WIDTH, 0, cpuConsJ hd0 stk0 ctr0, cpuInters ++ jetInters, []⟩

-- ---------------------------------------------------------------------------
-- The jet table's preprocessed tables
-- ---------------------------------------------------------------------------

/-- An operand's columns: flags (local, argument, global) and value. -/
def opCols : Op → List F
  | .local_ j => [ofN 1, ofN 0, ofN 0, ofN j]
  | .arg i => [ofN 0, ofN 1, ofN 0, ofN i]
  | .glob a => [ofN 0, ofN 0, ofN 1, ofN a]

/-- Pad to a power of two, at least `16`, with copies of the first row. -/
def padCopies : List (List F) → List (List F)
  | [] => []
  | r :: rs => (r :: rs) ++ List.replicate (pow2AtLeast (rs.length + 1) - (rs.length + 1)) r

def rootsRows (roots : List (Nat × Nat)) : List (List F) :=
  padCopies (roots.map fun (a, g) => [ofN a, ofN g])

/-- A jet's header: `g k n` and the root operand. -/
def hdrRow (J : Air.Jet) (g : Nat) : List F :=
  [ofN g, ofN J.xs.length, ofN (symCells J J.body 0).1.length] ++ opCols (symCells J J.body 0).2

def hdrRows (jets : List Air.Jet) : List (List F) :=
  padCopies (jets.zipIdx.map fun (J, g) => hdrRow J g)

/-- A template row: `g j tag` and the operands (zero for a leaf). -/
def tmplRow (g j : Nat) : Nat × Option (Op × Op) → List F
  | (tag, some (a, b)) => [ofN g, ofN j, ofN tag] ++ opCols a ++ opCols b
  | (tag, none) => [ofN g, ofN j, ofN tag] ++ List.replicate 8 (ofN 0)

def tmplRows (jets : List Air.Jet) : List (List F) :=
  padCopies (jets.zipIdx.flatMap fun (J, g) =>
    (symCells J J.body 0).1.zipIdx.map fun (cl, j) => tmplRow g j cl)

/-- A preprocessed table providing its rows on `bus`, as often as its
    committed multiplicity says. -/
def providerAir (name : String) (w : Nat) (rows : List (List F)) : AirD :=
  ⟨name, 1, w, [], [⟨name, 0, .neg (col 0), (List.range w).map prec⟩], rows⟩

def rootsAir (roots : List (Nat × Nat)) : AirD := providerAir "roots" 2 (rootsRows roots)
def hdrAir (jets : List Air.Jet) : AirD := providerAir "hdr" 7 (hdrRows jets)
def tmplAir (jets : List Air.Jet) : AirD := providerAir "tmpl" 11 (tmplRows jets)

-- ---------------------------------------------------------------------------
-- POP and INSTW
-- ---------------------------------------------------------------------------

/-- POP's range check: `c - s - 1` in 24 bits. -/
def popVal : E :=
  (List.range RANGE_BITS).foldl (fun v i => .add v (.mul (col (8 + i)) (c (2 ^ i)))) zero

/-- POP: `clk c i s x s' uses act`, then the range bits. -/
def popCons : List E :=
  [bool (col 7), .mul (col 6) (.sub one (col 7))] ++
  (List.range RANGE_BITS).map (fun i => bool (col (8 + i))) ++
  [.mul (col 7) (.sub (.sub (.sub (col 1) (col 3)) one) popVal)]

def popInters : List Inter :=
  [⟨"popch", 1, .neg (col 7), [col 0, col 1, col 2, col 3]⟩,
   ⟨"popch", 1, col 7, [col 0, col 1, .add (col 2) one, col 5]⟩,
   ⟨"mem", 1, col 7, [col 3, c 5, col 4, col 5]⟩,
   ⟨"arg", 0, .neg (col 6), [col 0, col 2, col 4]⟩]

def popAir : AirD := ⟨"pop", 8 + RANGE_BITS, 0, popCons, popInters, []⟩

/-- An INSTW operand, resolved: `c + v`, the argument `x`, or `v`. -/
def resolveE (fl fa fg v x : Nat) : E :=
  .add (.add (.mul (col fl) (.add (col 1) (col v))) (.mul (col fa) (col x))) (.mul (col fg) (col v))

/-- INSTW: `clk c g j tag aL aA aG av bL bA bG bv a b xa xb act`. -/
def instwCons : List E :=
  [bool (col 17)] ++
  ([5, 6, 7, 9, 10, 11].flatMap fun k => [bool (col k), .mul (col k) (.sub one (col 17))]) ++
  [eq (col 13) (resolveE 5 6 7 8 15), eq (col 14) (resolveE 9 10 11 12 16)]

def instwInters : List Inter :=
  [⟨"arg", 1, col 6, [col 0, col 8, col 15]⟩,
   ⟨"arg", 1, col 10, [col 0, col 12, col 16]⟩,
   ⟨"wch", 1, .neg (col 17), [col 0, col 1, col 2, col 3]⟩,
   ⟨"wch", 1, col 17, [col 0, col 1, col 2, .add (col 3) one]⟩,
   ⟨"tmpl", 1, col 17, (List.range 11).map fun i => col (2 + i)⟩,
   ⟨"mem", 1, col 17, [.add (col 1) (col 3), col 4, col 13, col 14]⟩]

def instwAir : AirD := ⟨"instw", 18, 0, instwCons, instwInters, []⟩

-- ---------------------------------------------------------------------------
-- The numbers that must fit
-- ---------------------------------------------------------------------------

/-- An operand whose value fits in 24 bits. -/
def opSmall : Op → Bool
  | .local_ j => decide (j < 2 ^ 24)
  | .arg i => decide (i < 2 ^ 24)
  | .glob a => decide (a < 2 ^ 24)

/-- **A jet whose numbers fit**: arity, cell count and operands below
    `2^24`, so they are the same numbers in the field.  `compare-jets`
    checks it of the verifier's jet table. -/
def jetFitB (J : Air.Jet) : Bool :=
  decide (J.xs.length < 2 ^ 24) && decide ((symCells J J.body 0).1.length < 2 ^ 24) &&
    opSmall (symCells J J.body 0).2 &&
    (symCells J J.body 0).1.all fun cl => match cl.2 with
      | some (a, b) => opSmall a && opSmall b
      | none => true

/-- **The jet circuit for a term and its jet table**: what the jet
    verifier builds. -/
def jetAirs (t : Term) (roots : List (Nat × Nat)) (jets : List Air.Jet) : List AirD :=
  let m := Mach.load t
  [cpuAirJ m.hd m.stk m.heap.length, memAir, progAir m.heap, rootsAir roots, hdrAir jets, tmplAir jets,
   popAir, instwAir]

end Circuit
