import Ski.Circuit.CompPHonest
import Ski.Circuit.JetCntFast

/-!
# The honest CPU rows, their memory read from an array

Each circuit's honest CPU row reads its memory as a list (`rd`, and
`P2Jet.p2Row` through `List.take`), so a read costs the address.  Here the
same rows read through any reader `get : Nat → Option Cell`, as
`Air.checkA` reads its memory, and each is proved equal to its list model
when `get` reads the list (`cpuCol_G` and its kin); with `get` an array's
reader a read is constant time (`Air.getElem?_fun`).

A column of the composed rows also asks for the restart count before the
row (`cntS (rsI e n) i`), a sum over the row's predecessors, and a jet
row's column asks which jet it instantiates, a search of the roots.  The
fast models take both as arguments, computed once a row: the counts from a
prefix sum (`cntArr_get`), the jet from `JRun.instAtG`.

- `cpuColWG`: Sudoku's and the hidden term's CPU (`cpuColW_arr`);
- `cpuColCG`: the composed CPU (`cpuColC_arr`);
- `CRun.cpuColCJG`: the composed CPU with jets (`CRun.cpuColCJ_arr`), and
  the run's instantiations (`JRun.insts_arr`);
- `P2Run.cpuColPG`: the CPU with the Poseidon2 jet (`P2Run.cpuColP_arr`).

`lake exe composed check-*-tables` and `lake exe sudoku check-tables`
compare every CPU row with them.
-/

namespace Circuit

open B Air JetTable Compose CompM Mach

-- ---------------------------------------------------------------------------
-- The base row
-- ---------------------------------------------------------------------------

/-- `kindOf`, over a reader. -/
def kindOfG (get : Nat → Option Cell) (r : Air.Row) : Nat :=
  match rdG get r.ctr r.hd with
  | some (.app _ _) => 0
  | some .I =>
    match rdG get r.ctr r.stk with
    | some (.cons _ _) => 1
    | _ => 4
  | some .K =>
    match rdG get r.ctr r.stk with
    | some (.cons _ s1) =>
      match rdG get r.ctr s1 with
      | some (.cons _ _) => 2
      | _ => 6
    | _ => 5
  | some .S =>
    match rdG get r.ctr r.stk with
    | some (.cons _ s1) =>
      match rdG get r.ctr s1 with
      | some (.cons _ s2) =>
        match rdG get r.ctr s2 with
        | some (.cons _ _) => 3
        | _ => 9
      | _ => 8
    | _ => 7
  | _ => 10

/-- `addrAt`, over a reader. -/
def addrAtG (get : Nat → Option Cell) (r : Air.Row) : Nat → Nat
  | 0 => r.hd
  | 1 => r.stk
  | 2 => (cellFields ((rdG get r.ctr r.stk).getD .nil)).2
  | _ => (cellFields ((rdG get r.ctr (cellFields ((rdG get r.ctr r.stk).getD .nil)).2).getD .nil)).2

/-- `fieldsAt`, over a reader. -/
def fieldsAtG (get : Nat → Option Cell) (r : Air.Row) (j : Nat) : Nat × Nat :=
  cellFields ((rdG get r.ctr (addrAtG get r j)).getD .nil)

/-- `rangeValue`, over a reader. -/
def rangeValueG (get : Nat → Option Cell) (r : Air.Row) (j : Nat) : Nat :=
  if actOf (kindOfG get r) j = 1 then r.ctr - addrAtG get r j - 1 else 0

/-- `cpuCol`, over a reader. -/
def cpuColG (get : Nat → Option Cell) (r : Air.Row) (col : Nat) : F :=
  if col = HD then ofN r.hd
  else if col = STK then ofN r.stk
  else if col = CTR then ofN r.ctr
  else if col < FLD then (if col - SEL = kindOfG get r then 1 else 0)
  else if col < BITS then
    (if (col - FLD) % 2 = 0 then ofN (fieldsAtG get r ((col - FLD) / 2)).1 else ofN (fieldsAtG get r ((col - FLD) / 2)).2)
  else ofN ((rangeValueG get r ((col - BITS) / RANGE_BITS) / 2 ^ ((col - BITS) % RANGE_BITS)) % 2)

theorem kindOf_G (M : List Cell) (r : Air.Row) : kindOf M r = kindOfG (fun a => M[a]?) r := rfl
theorem addrAt_G (M : List Cell) (r : Air.Row) (j : Nat) : addrAt M r j = addrAtG (fun a => M[a]?) r j := by
  match j with
  | 0 | 1 | 2 | _ + 3 => rfl
theorem fieldsAt_G (M : List Cell) (r : Air.Row) (j : Nat) : fieldsAt M r j = fieldsAtG (fun a => M[a]?) r j := by
  unfold fieldsAt fieldsAtG; rw [addrAt_G]; rfl
theorem rangeValue_G (M : List Cell) (r : Air.Row) (j : Nat) :
    rangeValue M r j = rangeValueG (fun a => M[a]?) r j := by
  unfold rangeValue rangeValueG; rw [addrAt_G, kindOf_G]

/-- **The base row over a list's reader is the base row.** -/
theorem cpuCol_G (M : List Cell) (r : Air.Row) (col : Nat) : cpuCol M r col = cpuColG (fun a => M[a]?) r col := by
  unfold cpuCol cpuColG; simp only [kindOf_G, fieldsAt_G, rangeValue_G]; rfl

-- ---------------------------------------------------------------------------
-- Restart counts, once
-- ---------------------------------------------------------------------------

/-- `cntS f i` for every `i ≤ K`, as a prefix sum. -/
def cntArr (f : Nat → Nat) (K : Nat) : Array Nat :=
  ((List.range K).scanl (fun acc r => acc + f r) 0).toArray

theorem foldl_cntS (f : Nat → Nat) : ∀ i, (List.range i).foldl (fun acc r => acc + f r) 0 = cntS f i
  | 0 => rfl
  | i + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_cntS f i]; rfl

/-- **The prefix sum is the count**, at every `i ≤ K`. -/
theorem cntArr_get (f : Nat → Nat) {K i : Nat} (h : i ≤ K) : (cntArr f K).getD i 0 = cntS f i := by
  unfold cntArr
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_scanl,
    if_pos (by rw [List.length_range]; exact h), List.take_range, Nat.min_eq_left h, foldl_cntS]
  rfl

-- ---------------------------------------------------------------------------
-- Sudoku's and the hidden term's CPU
-- ---------------------------------------------------------------------------

/-- `cpuColW`, over a reader. -/
def cpuColWG (get : Nat → Option Cell) (row : Nat → Air.Row) (k i col : Nat) : F :=
  if col < CPU_WIDTH then cpuColG get (rowQ row k i) col else 0

/-- **The witness circuit's honest CPU row, its memory an array.** -/
theorem cpuColW_arr (A : Array Cell) (row : Nat → Air.Row) (k i col : Nat) :
    cpuColWG (fun a => A[a]?) row k i col = cpuColW A.toList row k i col := by
  unfold cpuColWG cpuColW; rw [getElem?_fun, cpuCol_G]

-- ---------------------------------------------------------------------------
-- The composed CPU
-- ---------------------------------------------------------------------------

/-- `cpuColC`, over a reader, the restart count before the row given. -/
def cpuColCG (get : Nat → Option Cell) (row : Nat → Air.Row) (e : Nat → Nat) (n : Nat) (roots : List Nat)
    (cnt i col : Nat) : F :=
  if col < CPU_WIDTH then
    (if SEL ≤ col ∧ col < SEL + NKINDS ∧ isRestart e n i = true then 0 else cpuColG get (rowP row e n i) col)
  else if col = RS then (if isRestart e n i then 1 else 0)
  else if col = CNT then ofN cnt
  else if col = ROOT then ofN (roots.getD (cnt + 1) 0)
  else 0

theorem cpuColC_G (M : List Cell) (row : Nat → Air.Row) (e : Nat → Nat) (n : Nat) (roots : List Nat) (i col : Nat) :
    cpuColC M row e n roots i col = cpuColCG (fun a => M[a]?) row e n roots (cntS (rsI e n) i) i col := by
  unfold cpuColC cpuColCG; rw [cpuCol_G]

/-- **The composed honest CPU row, its memory an array**, its restart
    count from the prefix sum, on every row below `K`. -/
theorem cpuColC_arr (A : Array Cell) (row : Nat → Air.Row) (e : Nat → Nat) (n : Nat) (roots : List Nat)
    {K i : Nat} (hi : i ≤ K) (col : Nat) :
    cpuColCG (fun a => A[a]?) row e n roots ((cntArr (rsI e n) K).getD i 0) i col =
      cpuColC A.toList row e n roots i col := by
  rw [cntArr_get _ hi, cpuColC_G, getElem?_fun]

-- ---------------------------------------------------------------------------
-- The jet CPU
-- ---------------------------------------------------------------------------

/-- `jetOf`, over a reader. -/
def jetOfG (get : Nat → Option Cell) (roots : List (Nat × Nat)) (jets : List Air.Jet) (r r' : Air.Row) :
    Option (Nat × Air.Jet) :=
  if stepRowG get r = some r' ∨ (haltRowG get r = true ∧ r' = r) then none
  else (roots.find? fun p => p.1 == r.hd && match jets[p.2]? with
      | some J => decide (instRowG get J r = some r')
      | none => false).bind fun p => (jets[p.2]?).map fun J => (p.2, J)

theorem jetOf_G (M : List Cell) (roots : List (Nat × Nat)) (jets : List Air.Jet) (r r' : Air.Row) :
    jetOf M roots jets r r' = jetOfG (fun a => M[a]?) roots jets r r' := by
  unfold jetOf jetOfG; simp only [stepRow_G, haltRow_G]; rfl

namespace JRun

variable (get : Nat → Option Cell) (R : JRun)

/-- `instAt`, over a reader. -/
def instAtG (i : Nat) : Option (Nat × Air.Jet) :=
  if R.skip i then none else if i + 1 < R.k then jetOfG get R.roots R.jets (R.row i) (R.row (i + 1)) else none

def psG (i : Nat) (J : Air.Jet) : List Nat :=
  ((popR get (R.row i).ctr J.xs.length (R.row i).stk).map Prod.fst).getD []
def restG (i : Nat) (J : Air.Jet) : Nat :=
  ((popR get (R.row i).ctr J.xs.length (R.row i).stk).map Prod.snd).getD 0

/-- `instCol`, over a reader. -/
def instColG (i g : Nat) (J : Air.Jet) (col : Nat) : F :=
  if col = HD then ofN (R.row i).hd else if col = STK then ofN (R.row i).stk
  else if col = CTR then ofN (R.row i).ctr
  else if col = SEL + 11 then 1
  else if col = J_CLK then ofN i else if col = J_G then ofN g else if col = J_K then ofN J.xs.length
  else if col = J_N then ofN (symCells J J.body 0).1.length
  else if col = J_RL then (opCols (symCells J J.body 0).2).getD 0 0
  else if col = J_RA then (opCols (symCells J J.body 0).2).getD 1 0
  else if col = J_RG then (opCols (symCells J J.body 0).2).getD 2 0
  else if col = J_RV then (opCols (symCells J J.body 0).2).getD 3 0
  else if col = J_XROOT then ofN (argVal (R.psG get i J) (symCells J J.body 0).2)
  else if col = J_REST then ofN (R.restG get i J)
  else 0

/-- `cpuCol`, over a reader, the row's instantiation given. -/
def cpuColG (inst : Option (Nat × Air.Jet)) (i col : Nat) : F :=
  match inst with
  | none => if col < CPU_WIDTH then Circuit.cpuColG get (R.rowQ i) col else if col = J_CLK then ofN i else 0
  | some (g, J) => R.instColG get i g J col

/-- `insts`, over a reader. -/
def instsG (K : Nat) : List (Nat × (Nat × Air.Jet)) :=
  (List.range K).filterMap fun i => (R.instAtG get i).map (i, ·)

theorem instAt_G (i : Nat) : R.instAt i = R.instAtG (fun a => R.A[a]?) i := by
  unfold instAt instAtG; rw [jetOf_G]

theorem cpuCol_G (i col : Nat) : R.cpuCol i col = R.cpuColG (fun a => R.A[a]?) (R.instAtG (fun a => R.A[a]?) i) i col := by
  unfold cpuCol cpuColG; rw [instAt_G]
  cases R.instAtG (fun a => R.A[a]?) i with
  | none => simp only [Circuit.cpuCol_G]
  | some p => rfl

/-- **The run's instantiations, its memory an array.** -/
theorem insts_arr (A : Array Cell) (hA : R.A = A.toList) (K : Nat) :
    R.instsG (fun a => A[a]?) K = R.insts K := by
  unfold instsG insts; simp only [instAt_G, hA, getElem?_fun]

end JRun

namespace CRun

variable (get : Nat → Option Cell) (R : CRun)

/-- `cpuColCJ`, over a reader, the row's instantiation and restart count
    given. -/
def cpuColCJG (inst : Option (Nat × Air.Jet)) (cnt i col : Nat) : F :=
  if col < CPU_WIDTH + JET_WIDTH then
    (if SEL ≤ col ∧ col < SEL + NKINDS ∧ isRestart R.e R.n i = true then 0 else R.J.cpuColG get inst i col)
  else if col = RSJ then (if isRestart R.e R.n i then 1 else 0)
  else if col = CNTJ then ofN cnt
  else if col = ROOTJ then ofN (R.segRoots.getD (cnt + 1) 0)
  else 0

/-- **The composed honest CPU row with jets, its memory an array**, its
    instantiation from `instAtG` and its restart count from the prefix
    sum, on every row below `K`. -/
theorem cpuColCJ_arr (A : Array Cell) (hA : R.A = A.toList) {K i : Nat} (hi : i ≤ K) (col : Nat) :
    R.cpuColCJG (fun a => A[a]?) (R.J.instAtG (fun a => A[a]?) i) ((cntArr (rsI R.e R.n) K).getD i 0) i col =
      R.cpuColCJ i col := by
  have hg : (fun a : Nat => A[a]?) = (fun a : Nat => R.J.A[a]?) := by
    rw [getElem?_fun]; exact congrArg (fun (L : List Cell) (a : Nat) => L[a]?) hA.symm
  unfold cpuColCJG cpuColCJ
  rw [cntArr_get _ hi, hg, JRun.cpuCol_G]

end CRun

-- ---------------------------------------------------------------------------
-- The CPU with the Poseidon2 jet
-- ---------------------------------------------------------------------------

end Circuit

namespace P2Jet

open Air

/-- `boolAt`, over a reader. -/
def boolAtG (h : Nat → Option Cell) (a : Nat) : Option Bool :=
  match h a with
  | some .K => some true
  | some (.app f x) =>
    match h f, h x with
    | some .K, some .I => some false
    | _, _ => none
  | _ => none

/-- `bitsAt`, over a reader. -/
def bitsAtG (h : Nat → Option Cell) : List Nat → Option (List Bool)
  | [] => some []
  | a :: as =>
    match boolAtG h a, bitsAtG h as with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- `slotsOK`, over a reader. -/
def slotsOKG (h : Nat → Option Cell) : Bool :=
  h 0 == some .K && h 1 == some .I && h 2 == some (.app 0 1)

/-- `popN`, over a reader. -/
def popNG (h : Nat → Option Cell) : Nat → Nat → Option (List Nat × Nat)
  | 0, s => some ([], s)
  | k + 1, s =>
    match h s with
    | some (.cons x r) => (popNG h k r).map fun p => (x :: p.1, p.2)
    | _ => none

/-- `p2Row`, over a reader: the heap below the counter read through
    `rdG`, as `List.take` cuts it. -/
def p2RowG (get : Nat → Option Cell) (j root : Nat) (r : Air.Row) : Option Air.Row :=
  match rdG get r.ctr r.hd with
  | some (.atom j') =>
    if j' = j ∧ slotsOKG (rdG get r.ctr) = true then
      match popNG (rdG get r.ctr) 2 r.stk with
      | some ([k, β], rest) =>
        if β = root then
          match bitsAtG (rdG get r.ctr) slotAddrs with
          | some bs =>
            if wrsG get r.ctr (pushR r.ctr rest (outBits bs).reverse) then
              some ⟨k, topOf r.ctr rest (outBits bs).length, r.ctr + (outBits bs).length⟩
            else none
          | none => none
        else none
      | _ => none
    else none
  | _ => none

theorem boolAt_G (H : List Cell) (a : Nat) : boolAt H a = boolAtG (fun a => H[a]?) a := rfl

theorem bitsAt_G (H : List Cell) : ∀ as, bitsAt H as = bitsAtG (fun a => H[a]?) as
  | [] => rfl
  | a :: as => by unfold bitsAt bitsAtG; rw [boolAt_G, bitsAt_G H as]; rfl

theorem slotsOK_G (H : List Cell) : slotsOK H = slotsOKG (fun a => H[a]?) := rfl

theorem popN_G (H : List Cell) : ∀ k s, Mach.popN H k s = popNG (fun a => H[a]?) k s
  | 0, _ => rfl
  | k + 1, s => by
    unfold Mach.popN popNG
    cases H[s]? with
    | none => rfl
    | some c => cases c with
      | cons x r => dsimp only; rw [popN_G H k r]
      | _ => rfl

theorem take_G (M : List Cell) (c : Nat) : (fun a => (M.take c)[a]?) = rdG (fun a => M[a]?) c := by
  funext a; rw [List.getElem?_take]; rfl

/-- **The jet's row over a list's reader is the jet's row.** -/
theorem p2Row_G (M : List Cell) (j root : Nat) (r : Air.Row) : p2Row M j root r = p2RowG (fun a => M[a]?) j root r := by
  unfold p2Row p2RowG
  simp only [bitsAt_G, slotsOK_G, popN_G, take_G, wrs_G]
  rfl

/-- `consecFrom`, over a reader. -/
def consecFromG (h : Nat → Option Cell) : Nat → Nat → Bool
  | _, 0 => true
  | s, n + 1 =>
    match h s with
    | some (.cons _ s') => s' + 1 == s && consecFromG h s' n
    | _ => false

/-- `stackRun`, over a reader. -/
def stackRunG (h : Nat → Option Cell) (stk : Nat) : Bool :=
  match h stk with
  | some (.cons _ s1) => consecFromG h s1 495
  | _ => false

/-- `p2RowS`, over a reader. -/
def p2RowSG (get : Nat → Option Cell) (j : Nat) (r : Air.Row) : Option Air.Row :=
  match rdG get r.ctr r.hd with
  | some (.atom j') =>
    if j' = j ∧ slotsOKG (rdG get r.ctr) = true ∧ stackRunG (rdG get r.ctr) r.stk = true then
      match popNG (rdG get r.ctr) 497 r.stk with
      | some (k :: ps, rest) =>
        match ptrBits ps with
        | some bs =>
          if wrsG get r.ctr (pushR r.ctr rest (outBits bs).reverse) then
            some ⟨k, topOf r.ctr rest (outBits bs).length, r.ctr + (outBits bs).length⟩
          else none
        | none => none
      | _ => none
    else none
  | _ => none

theorem consecFrom_G (H : List Cell) : ∀ s n, consecFrom H s n = consecFromG (fun a => H[a]?) s n
  | _, 0 => rfl
  | s, n + 1 => by
    unfold consecFrom consecFromG
    cases H[s]? with
    | none => rfl
    | some c => cases c with
      | cons x r => dsimp only; rw [consecFrom_G H r n]
      | _ => rfl

theorem stackRun_G (H : List Cell) (stk : Nat) : stackRun H stk = stackRunG (fun a => H[a]?) stk := by
  unfold stackRun stackRunG
  dsimp only
  cases H[stk]? with
  | none => rfl
  | some c => cases c with
    | cons x r => exact consecFrom_G H r 495
    | _ => rfl

/-- **The jet's stack row over a list's reader is the jet's stack row.** -/
theorem p2RowS_G (M : List Cell) (j : Nat) (r : Air.Row) : p2RowS M j r = p2RowSG (fun a => M[a]?) j r := by
  unfold p2RowS p2RowSG
  simp only [slotsOK_G, stackRun_G, popN_G, take_G, wrs_G]
  rfl

end P2Jet

namespace Circuit

open B Air Compose CompM Mach

namespace P2Run

variable (get : Nat → Option Cell) (R : P2Run)

/-- `jetCAt`, over a reader. -/
def jetCAtG (i : Nat) : Bool :=
  !isRestart R.e R.n i && decide (i < R.e (R.n - 1)) &&
    decide (P2Jet.p2RowG get R.J R.root (R.row i) = some (R.row (i + 1)))

/-- `jetSAt`, over a reader. -/
def jetSAtG (i : Nat) : Bool :=
  !isRestart R.e R.n i && decide (i < R.e (R.n - 1)) &&
    decide (P2Jet.p2RowSG get (R.J + 1) (R.row i) = some (R.row (i + 1)))

/-- `jetAt`, over a reader. -/
def jetAtG (i : Nat) : Bool := R.jetCAtG get i || R.jetSAtG get i

/-- `jetRange`, over a reader. -/
def jetRangeG (r : Air.Row) (j : Nat) : Nat := if j < 3 then r.ctr - addrAtG get r j - 1 else 0

/-- `jrest`, over a reader. -/
def jrestG (i : Nat) : Nat :=
  if R.jetSAtG get i then ((P2Jet.popNG (rdG get (R.rowQ i).ctr) 497 (R.rowQ i).stk).getD ([], 0)).2
  else (fieldsAtG get (R.rowQ i) 2).2

/-- `js1`, over a reader. -/
def js1G (i : Nat) : Nat := (fieldsAtG get (R.rowQ i) 1).2

/-- `cpuColP`, over a reader, which jet step the row takes (on the comb,
    on the stack) and its restart count given. -/
def cpuColPG (jc js : Bool) (cnt i c : Nat) : F :=
  if c = P2SEL then bF (jc || js)
  else if (jc || js) = true ∧ SEL ≤ c ∧ c < SEL + NKINDS then 0
  else if (jc || js) = true ∧ BITS ≤ c ∧ c < CPU_WIDTH then
    ofN ((jetRangeG get (R.rowQ i) ((c - BITS) / RANGE_BITS) / 2 ^ ((c - BITS) % RANGE_BITS)) % 2)
  else if c = P2MODE then bF js
  else if c = P2REST then (if (jc || js) then ofN (R.jrestG get i) else 0)
  else if c = P2CM then bF jc
  else if c = P2SP0 then
    (if js then ofN (R.js1G get i) else if (jc || js) then ofN (R.jrestG get i) else 0)
  else cpuColCG get R.row R.e R.n R.segRoots cnt i c

theorem jetCAt_G (i : Nat) : R.jetCAt i = R.jetCAtG (fun a => R.A[a]?) i := by
  unfold jetCAt jetCAtG; rw [P2Jet.p2Row_G]

theorem jetSAt_G (i : Nat) : R.jetSAt i = R.jetSAtG (fun a => R.A[a]?) i := by
  unfold jetSAt jetSAtG; rw [P2Jet.p2RowS_G]

theorem jetAt_G (i : Nat) : R.jetAt i = R.jetAtG (fun a => R.A[a]?) i := by
  unfold jetAt jetAtG; rw [jetCAt_G, jetSAt_G]

theorem jetRange_G (r : Air.Row) (j : Nat) : R.jetRange r j = jetRangeG (fun a => R.A[a]?) r j := by
  unfold jetRange jetRangeG; rw [addrAt_G]

theorem jrest_G (i : Nat) : R.jrest i = R.jrestG (fun a => R.A[a]?) i := by
  unfold jrest jrestG
  rw [jetSAt_G, P2Jet.popN_G, P2Jet.take_G, fieldsAt_G]

theorem js1_G (i : Nat) : R.js1 i = R.js1G (fun a => R.A[a]?) i := by
  unfold js1 js1G; rw [fieldsAt_G]

/-- **The honest CPU row with the Poseidon2 jet, its memory an array**,
    which jet step the row takes from `jetCAtG` and `jetSAtG` and its
    restart count from the prefix sum, on every row below `K`. -/
theorem cpuColP_arr (A : Array Cell) (hA : R.A = A.toList) {K i : Nat} (hi : i ≤ K) (c : Nat) :
    R.cpuColPG (fun a => A[a]?) (R.jetCAtG (fun a => A[a]?) i) (R.jetSAtG (fun a => A[a]?) i)
      ((cntArr (rsI R.e R.n) K).getD i 0) i c = R.cpuColP i c := by
  have hg : (fun a : Nat => A[a]?) = (fun a : Nat => R.A[a]?) := by
    rw [getElem?_fun]; exact congrArg (fun (L : List Cell) (a : Nat) => L[a]?) hA.symm
  unfold cpuColPG cpuColP jetAt
  rw [cntArr_get _ hi, hg, ← jetCAt_G, ← jetSAt_G, ← jrest_G, ← js1_G, ← cpuColC_G]
  simp only [jetRange_G]

end P2Run

end Circuit
