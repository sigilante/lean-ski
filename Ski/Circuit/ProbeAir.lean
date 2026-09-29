import Ski.Circuit.JetAir
import Ski.AirProbe

/-!
# The probe circuit, as data

The ten AIRs of `bench/plonky3/src/jets.rs` and `src/probe.rs` for a public
term, its jet table and a probe plan, as the probe verifier builds them
(`airs` with a plan), constraint for constraint and message for message.
`lake exe circuit compare-probe` checks the Rust export (`ski-air
export-probe TERM JETS OUTCOME…`), recomputing the plan from the outcome.

- **The CPU** is the jet CPU with the probe kinds (selectors 12 and 13,
  `PFIRST` and `PLATER`) and 43 probe columns after the jet columns: the
  probe count, the pointer the starting segment probes, the starting and
  ending segments' PLAN rows, the rest of the ending stack, the nil read
  (flag, address, range bits), the parent's end row, and how many children
  read this row's fields.
- **PLAN** provides the plan's rows; **PW** writes one marker and its
  stack cell per row, on the `PWCH` chain.
-/

namespace Circuit

open B

-- The CPU's probe columns (probe.rs).
def P_CNT : Nat := J_CLK + JET_WIDTH
def P_F : Nat := P_CNT + 1
def S_BASE : Nat := P_CNT + 2
def E_BASE : Nat := P_CNT + 8
def E_REST : Nat := P_CNT + 14
def P_NILACT : Nat := P_CNT + 15
def P_NILADDR : Nat := P_CNT + 16
def P_CLKP : Nat := P_CNT + 17
def P_NKIDS : Nat := P_CNT + 18
def P_NILBITS : Nat := P_CNT + 19
def PROBE_WIDTH : Nat := 19 + RANGE_BITS

/-- A probe row, either kind. -/
def sProbe : E := .add sPFirst sPLater

/-- The nil read's range check: `ctr - addr - 1` in 24 bits. -/
def nilVal : E :=
  (List.range RANGE_BITS).foldl (fun v i => .add v (.mul (col (P_NILBITS + i)) (c (2 ^ i)))) zero

/-- **The probe constraints**, in the Rust's order: the count, the ending
    segment's marker, fields and nil, the pointer, and the last row. -/
def probeCons (n lastAtom : Nat) : List E :=
  [whenFirst (eq sPFirst one), whenFirst (col P_CNT), .mul sPFirst (col P_CNT),
   whenTrans (eq (nxt P_CNT) (.add (col P_CNT) sProbe)),
   .mul sPLater (.sub (.sub (fld 0) (col (E_BASE + 2))) (col E_BASE)),
   bool (col P_NILACT), .mul sPLater (.sub one (col P_NILACT)),
   .mul sPLater (.sub (col P_NILADDR) (col E_REST))] ++
  (List.range RANGE_BITS).map (fun i => bool (col (P_NILBITS + i))) ++
  [.mul (col P_NILACT) (.sub (.sub (.sub (col CTR) (col P_NILADDR)) one) nilVal),
   .mul (col P_NKIDS) (.sub one sPLater),
   .mul sPFirst (.sub (col P_F) (col HD)),
   whenLast (eq (col P_CNT) (c n)), whenLast (eq sHA one), whenLast (eq (fld 0) (c lastAtom)),
   whenLast (eq (col P_NILACT) one), whenLast (eq (col P_NILADDR) (col STK))]

/-- **The probe CPU's constraints**: the jet CPU's, with the probe
    constraints in place of `p = 0` and the probe rows' parts of the next
    registers. -/
def cpuConsP (hd0 stk0 ctr0 n lastAtom : Nat) : List E :=
  (List.range NKINDS).map (fun i => bool (col (SEL + i))) ++
  [eq (sum ((List.range NKINDS).map fun i => col (SEL + i))) one] ++
  readCons 0 ++ readCons 1 ++ readCons 2 ++ readCons 3 ++
  [whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
   bool (col J_RL), bool (col J_RA), bool (col J_RG),
   eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst] ++
  probeCons n lastAtom ++
  [whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sProbe (col P_F)))),
   whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST)))
     (.mul sProbe (.add (col CTR) (col (S_BASE + 1)))))),
   whenTrans (eq (nxt CTR) (.add (.add nextCtr (.mul sInst (col J_N)))
     (.mul sProbe (.add (.mul (col (S_BASE + 1)) (c 2)) one)))),
   whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
   whenLast (eq halt one)]

/-- The probe rows' messages. -/
def probeInters : List Inter :=
  [⟨"plan", 1, sProbe, col P_CNT :: (List.range 6).map fun i => col (S_BASE + i)⟩,
   ⟨"plan", 1, sPLater, .sub (col P_CNT) one :: (List.range 6).map fun i => col (E_BASE + i)⟩,
   ⟨"popch", 1, sPLater, [col J_CLK, col CTR, c 0, col STK]⟩,
   ⟨"popch", 1, .neg sPLater, [col J_CLK, col CTR, col (E_BASE + 3), col E_REST]⟩,
   ⟨"mem", 1, col P_NILACT, [col P_NILADDR, c 4, c 0, c 0]⟩,
   ⟨"segend", 0, .neg (col P_NKIDS), [.sub (col P_CNT) one, col J_CLK]⟩,
   ⟨"segend", 1, sPLater, [col (S_BASE + 4), col P_CLKP]⟩,
   ⟨"arg", 1, sPLater, [col P_CLKP, col (S_BASE + 5), col P_F]⟩,
   ⟨"pwch", 1, sProbe, [col J_CLK, col CTR, col S_BASE, col (S_BASE + 1), c 0]⟩,
   ⟨"pwch", 1, .neg sProbe, [col J_CLK, col CTR, col S_BASE, col (S_BASE + 1), col (S_BASE + 1)]⟩,
   ⟨"mem", 1, sProbe, [.add (col CTR) (.mul (col (S_BASE + 1)) (c 2)), c 4, c 0, c 0]⟩]

def cpuAirP (hd0 stk0 ctr0 n lastAtom : Nat) : AirD :=
  ⟨"cpu", CPU_WIDTH + JET_WIDTH + PROBE_WIDTH, 0, cpuConsP hd0 stk0 ctr0 n lastAtom,
    cpuInters ++ jetInters ++ probeInters, []⟩

/-- The PLAN table's rows: `j base k ctor arity parent field`, padded with
    copies of the first. -/
def planRows (plan : List Air.Seg) : List (List F) :=
  padCopies (plan.zipIdx.map fun (s, j) =>
    [ofN j, ofN s.base, ofN s.k, ofN s.ctor, ofN s.arity, ofN s.parent, ofN s.field])

def planAir (plan : List Air.Seg) : AirD := providerAir "plan" 7 (planRows plan)

/-- PW: `clk c base k i act`, the atom `base + i` at `c + i` and its stack
    cell `C (c + i) (c + k + i + 1)` at `c + k + i`. -/
def pwAir : AirD :=
  ⟨"pw", 6, 0, [bool (col 5)],
    [⟨"pwch", 1, .neg (col 5), [col 0, col 1, col 2, col 3, col 4]⟩,
     ⟨"pwch", 1, col 5, [col 0, col 1, col 2, col 3, .add (col 4) one]⟩,
     ⟨"mem", 1, col 5, [.add (col 1) (col 4), c 6, .add (col 2) (col 4), c 0]⟩,
     ⟨"mem", 1, col 5, [.add (.add (col 1) (col 3)) (col 4), c 5, .add (col 1) (col 4),
       .add (.add (.add (col 1) (col 3)) (col 4)) one]⟩], []⟩

/-- **The plan's numbers fit** below `2^24`, as the probe verifier checks. -/
def planFitB (plan : List Air.Seg) : Bool :=
  plan.all fun s => decide (s.base < 2 ^ 24) && decide (s.k < 2 ^ 24) && decide (s.ctor < 2 ^ 24) &&
    decide (s.arity < 2 ^ 24) && decide (s.parent < 2 ^ 24) && decide (s.field < 2 ^ 24)

/-- The last segment's marker, `ctor + base`. -/
def lastAtom (plan : List Air.Seg) : Nat := (plan.getLast?.map fun s => s.ctor + s.base).getD 0

/-- **The probe circuit for a term, its jet table and a plan**: what the
    probe verifier builds. -/
def probeAirs (t : Term) (roots : List (Nat × Nat)) (jets : List Air.Jet) (plan : List Air.Seg) : List AirD :=
  let m := Mach.load t
  [cpuAirP m.hd m.stk m.heap.length plan.length (lastAtom plan), memAir, progAir m.heap, rootsAir roots,
   hdrAir jets, tmplAir jets, popAir, instwAir, planAir plan, pwAir]

end Circuit
