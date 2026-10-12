import Ski.ZK.SudRun
import Ski.ZK.BbGroup

/-!
# The Sudoku proof's composed hiding PCS

The Sudoku circuit commits four tables.  The memory, CPU and witness
tables are private, blinded by the edge tuples (`sudMemT`, `sudCpuT`,
`sudWitT`); the program table is public.  Each is committed as two trace
groups, its main columns and its permutation columns (`bbGroup`,
`mainCols`, `permCols`): eight groups, heights `2^16`, `2^16`, `2^10`
and the program's `2^(tp+1)` (`sudGroups`, `sudCols`).  Each table has a
quotient table over its two groups (`airQTabG`) with Plonky3's chunks.
A private table's LogUp terminal is the transcript's value (`tvAt`); the
program's is public, computed from the challenges (`progTm`), so the
LogUp chain takes any terminal function (`tabsHonest_bb`'s `tm`).

The program table's height is a power of two set by the statement:
`progS_height` and `sud_prog_height` give `2^(progTp + 1)` rows, with
`progTp ≤ 23`, for every run over `2^16` cells.

Each height has its own query points, `S16` for the `2^16` tables, `S10`
for the witness and `SP` for the program, as Plonky3 opens each matrix
at its own height's points.  The AIRs have Plonky3 degree 2, so with
`is_zk` Plonky3 makes `2^(log2_ceil 2 + 1) = 4` chunks per table, the
count `bbTab` fixes.

`sud_pcs`: that PCS, its view every group's openings, every table's
chunks, every codeword and FRI, meets `PCSCloseN` with `ε = 0` over the
Sudoku transcript's values.  `sud_hiding`: for an accepting run of the
Sudoku statement, `sud_transcriptG` over that PCS, its PCS term zero.

Left out of the view: the preprocessed columns.  They hold no witness
(zero for the memory, CPU and program tables' `pre`, `witRowsS` for the
witness's), and their openings at the fixed points are constants;
folding them into FRI's input gives another `fri`, so `sud_pcs` covers
it.  Argued, not proved; it also assumes Plonky3 commits them without
hiding randomness.  The simulator reads the tables' preprocessed columns
only (`sudPsim_pre`).  Assumed:
the query points off the trace domains (`lde_off_trace` gives it for
Plonky3's), `2 |S| + 8` within each height, `ζ` and the FRI challenge
`αb` generic and fixed (with `ws`, `qv` and the query points, not
sampled here), Fiat–Shamir, the Merkle commitments' hiding, and the
modeling facts the earlier modules name (the groups' trace and mask
points, the opened points `S ++ g S`).
-/

namespace Circuit

open ZKF SudokuText B Air Stmt Mach Sudoku

/-- The blinded private tables. -/
def sudMemT (Mm : Table) (t : Nat → Tup) : Table := Mm.setBlind 5 (t 0)
def sudCpuT (C : Table) (t : Nat → Tup) : Table := (C.setBlind BLA (t 1)).setBlind BLB (t 0)
def sudWitT (Wt : Table) (t : Nat → Tup) : Table := Wt.setBlind 1 (t 1)

/-- The eight trace groups: memory, CPU (`2^16` rows), witness (`2^10`)
    and program (`2^(tp+1)`), main and permutation each. -/
def sudGroups (tp : Nat) (S16 S10 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF) :
    List QGroup :=
  [bbGroup 15 S16 ζ qv, bbGroup 15 S16 ζ qv, bbGroup 15 S16 ζ qv, bbGroup 15 S16 ζ qv, bbGroup 9 S10 ζ qv,
   bbGroup 9 S10 ζ qv, bbGroup tp SP ζ qv, bbGroup tp SP ζ qv]

/-- The committed columns: each blinded table's main and permutation
    columns, and the program table's. -/
def sudCols (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (t : Nat → Tup)
    (α β : EF) :
    List (List (List F)) :=
  [mainCols (sudMemT Mm t) memAirC.width,
   permCols (sudMemT Mm t) (busAlphas (prefixOf α (off β)) memAirC) β (corpusLs memAirC),
   mainCols (sudCpuT C t) (cpuAirS hd0 stk0 ctr0 ACC).width,
   permCols (sudCpuT C t) (busAlphas (prefixOf α (off β)) (cpuAirS hd0 stk0 ctr0 ACC)) β
     (corpusLs (cpuAirS hd0 stk0 ctr0 ACC)),
   mainCols (sudWitT Wt t) witAirS.width,
   permCols (sudWitT Wt t) (busAlphas (prefixOf α (off β)) witAirS) β (corpusLs witAirS),
   mainCols (progTableS heap) (progAirS heap).width,
   permCols (progTableS heap) (busAlphas (prefixOf α (off β)) (progAirS heap)) β (corpusLs (progAirS heap))]

/-- The column counts. -/
def sudKs (hd0 stk0 ctr0 : Nat) (heap : List Cell) : List Nat :=
  [memAirC.width, 4 * ((corpusLs memAirC).length + 1), (cpuAirS hd0 stk0 ctr0 ACC).width,
   4 * ((corpusLs (cpuAirS hd0 stk0 ctr0 ACC)).length + 1), witAirS.width, 4 * ((corpusLs witAirS).length + 1),
   (progAirS heap).width, 4 * ((corpusLs (progAirS heap)).length + 1)]

theorem mainCols_shape (Tb : Table) (w : Nat) :
    (mainCols Tb w).length = w ∧ ∀ c ∈ mainCols Tb w, c.length = Tb.h := by
  refine ⟨by unfold mainCols; rw [List.length_map, List.length_range], fun c hc => ?_⟩
  unfold mainCols at hc; obtain ⟨_, _, rfl⟩ := List.mem_map.1 hc; rw [List.length_map, List.length_range]

theorem permCols_shape (Tb : Table) (αs : Nat → EF) (β : EF) (Ls : List (List E × E)) :
    (permCols Tb αs β Ls).length = 4 * (Ls.length + 1) ∧ ∀ c ∈ permCols Tb αs β Ls, c.length = Tb.h := by
  refine ⟨by unfold permCols; rw [List.length_map, List.length_range], fun c hc => ?_⟩
  unfold permCols at hc; obtain ⟨_, _, rfl⟩ := List.mem_map.1 hc; rw [List.length_map, List.length_range]

/-- **The committed columns fit the groups**, when the tables have the
    groups' heights. -/
theorem sudCols_shaped (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) {heap : List Cell} {C Mm Wt : Table} {tp : Nat}
    (hC : C.h = 2 ^ 16) (hM : Mm.h = 2 ^ 16) (hW : Wt.h = 2 ^ 10) (hPg : (progTableS heap).h = 2 ^ (tp + 1))
    (S16 S10 SP : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (t : Nat → Tup) (α β : EF) :
    Shaped ((sudGroups tp S16 S10 SP ζ qv).map QGroup.ext) (sudCols off hd0 stk0 ctr0 heap C Mm Wt t α β) ∧
      (sudCols off hd0 stk0 ctr0 heap C Mm Wt t α β).map List.length = sudKs hd0 stk0 ctr0 heap := by
  have m1 := mainCols_shape (sudMemT Mm t) memAirC.width
  have p1 := permCols_shape (sudMemT Mm t) (busAlphas (prefixOf α (off β)) memAirC) β (corpusLs memAirC)
  have m2 := mainCols_shape (sudCpuT C t) (cpuAirS hd0 stk0 ctr0 ACC).width
  have p2 := permCols_shape (sudCpuT C t) (busAlphas (prefixOf α (off β)) (cpuAirS hd0 stk0 ctr0 ACC)) β
    (corpusLs (cpuAirS hd0 stk0 ctr0 ACC))
  have m3 := mainCols_shape (sudWitT Wt t) witAirS.width
  have p3 := permCols_shape (sudWitT Wt t) (busAlphas (prefixOf α (off β)) witAirS) β (corpusLs witAirS)
  have m4 := mainCols_shape (progTableS heap) (progAirS heap).width
  have p4 := permCols_shape (progTableS heap) (busAlphas (prefixOf α (off β)) (progAirS heap)) β
    (corpusLs (progAirS heap))
  have hMh : (sudMemT Mm t).h = 2 ^ (15 + 1) := hM
  have hCh : (sudCpuT C t).h = 2 ^ (15 + 1) := hC
  have hWh : (sudWitT Wt t).h = 2 ^ (9 + 1) := hW
  refine ⟨⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_, fun c hc => ?_, trivial⟩, ?_⟩
  · rw [m1.2 c hc, hMh]; rfl
  · rw [p1.2 c hc, hMh]; rfl
  · rw [m2.2 c hc, hCh]; rfl
  · rw [p2.2 c hc, hCh]; rfl
  · rw [m3.2 c hc, hWh]; rfl
  · rw [p3.2 c hc, hWh]; rfl
  · rw [m4.2 c hc, hPg]; rfl
  · rw [p4.2 c hc, hPg]; rfl
  · show [_, _, _, _, _, _, _, _] = _
    rw [m1.1, p1.1, m2.1, p2.1, m3.1, p3.1, m4.1, p4.1]; rfl

-- ---------------------------------------------------------------------------
-- The quotient tables and their data
-- ---------------------------------------------------------------------------

/-- A private table's terminal: the transcript's value at `k`. -/
def tvAt (k : Nat) : EF → EF → List EF → EF := fun _ _ v => v.getD k EF.zero

/-- The program table's terminal: public, computed from the challenges. -/
def progTm (off : EF → String → EF) (heap : List Cell) : EF → EF → List EF → EF :=
  fun α β _ => terminal (prefixOf α (off β)) β (progAirS heap) (progTableS heap)

/-- An AIR's constraints with its LogUp constraints at the terminal `tm`
    reads. -/
def lupAF (off : EF → String → EF) (A : AirD) (tm : EF → EF → List EF → EF) : EF → EF → List EF → AirD :=
  fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β v) A.width (corpusLs A)

/-- **A table's quotient table** over its groups `gm`, `gp`. -/
def bbTab (off : EF → String → EF) (A : AirD) (tm : EF → EF → List EF → EF) (tb m : Nat) (P0 : Table) (gm gp : Nat) (S : List F) (ζ : EF)
    (ws : List (EF → EF → List F)) : QTab :=
  airQTabG (lupAF off A tm) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) [gm, gp] (bbκ tb 1 m) (bbCs tb 1 m)
    (bbHl tb 1 m) (bbCl tb 1 m) S ζ ws

/-- **Its data**: the honest chunks where the proof does not abort, the
    canonical ones elsewhere. -/
def bbData (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF) (A : AirD)
    (tm : EF → EF → List EF → EF) (tb m : Nat)
    (P0 : Table) (gm gp : Nat) (S : List F) (ζ : EF) (ws : List (EF → EF → List F)) (qs : List QGroup)
    (cols : (Nat → Tup) → EF → EF → List (List (List F))) (tabs : (Nat → Tup) → List (AirD × Table))
    (t : Nat → Tup) (α β : EF) (ms : List F) : List (List (List F) × List F) :=
  if Aborts (prefixOf α (off β)) β (tabs t) = false then
    airData (withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β (tv (prefixOf α (off β)) β t))
      A.width (corpusLs A)) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) (bbCs tb 1 m) (bbHl tb 1 m)
      ws α β (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) [gm, gp])
  else canonData (bbTab off A tm tb m P0 gm gp S ζ ws).sets α β (tv (prefixOf α (off β)) β t)
    (openMulti (qs.map QGroup.ext) (cols t α β) ms)

/-- The transcript's tables: the blinded private tables and the program. -/
def sudTabs (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (t : Nat → Tup) : List (AirD × Table) :=
  sudTables hd0 stk0 ctr0 heap (sudCpuT C t) (sudMemT Mm t) (progTableS heap) (sudWitT Wt t)

/-- **The Sudoku proof's four quotient tables**, memory, CPU, witness and
    program, with their data. -/
def sudTs (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (tp : Nat)
    (S16 S10 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) :
    List (QTab × ((Nat → Tup) → EF → EF → List F → List (List (List F) × List F))) :=
  let tv := fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t
  let qs := sudGroups tp S16 S10 SP ζ qv
  let cols := sudCols off hd0 stk0 ctr0 heap C Mm Wt
  let tabs := sudTabs hd0 stk0 ctr0 heap C Mm Wt
  [(bbTab off memAirC (tvAt 0) 15 (2 ^ 16 - 1) Mm 0 1 S16 ζ wm,
     bbData off tv memAirC (tvAt 0) 15 (2 ^ 16 - 1) Mm 0 1 S16 ζ wm qs cols tabs),
   (bbTab off (cpuAirS hd0 stk0 ctr0 ACC) (tvAt 1) 15 (2 ^ 16 - 1) C 2 3 S16 ζ wc,
     bbData off tv (cpuAirS hd0 stk0 ctr0 ACC) (tvAt 1) 15 (2 ^ 16 - 1) C 2 3 S16 ζ wc qs cols tabs),
   (bbTab off witAirS (tvAt 2) 9 (2 ^ 10 - 1) Wt 4 5 S10 ζ ww,
     bbData off tv witAirS (tvAt 2) 9 (2 ^ 10 - 1) Wt 4 5 S10 ζ ww qs cols tabs),
   (bbTab off (progAirS heap) (progTm off heap) tp (2 ^ (tp + 1) - 1) (progTableS heap) 6 7 SP ζ wp,
     bbData off tv (progAirS heap) (progTm off heap) tp (2 ^ (tp + 1) - 1) (progTableS heap) 6 7 SP ζ wp qs cols tabs)]

-- ---------------------------------------------------------------------------
-- The program table's height
-- ---------------------------------------------------------------------------

theorem pow2From_pow : ∀ (f e n : Nat), ∃ d, pow2From f (2 ^ e) n = 2 ^ (e + d)
  | 0, e, _ => ⟨0, rfl⟩
  | f + 1, e, n => by
    unfold pow2From
    split
    · obtain ⟨d, hd⟩ := pow2From_pow f (e + 1) n
      refine ⟨d + 1, ?_⟩
      rw [show 2 * 2 ^ e = 2 ^ (e + 1) by rw [Nat.pow_succ, Nat.mul_comm], hd, Nat.add_right_comm, Nat.add_assoc]
    · exact ⟨0, rfl⟩

theorem pow2From_ge_n : ∀ (f p n : Nat), n ≤ p * 2 ^ f → n ≤ pow2From f p n
  | 0, p, n, h => by show n ≤ p; simpa using h
  | f + 1, p, n, h => by
    unfold pow2From
    split
    · exact pow2From_ge_n f (2 * p) n (by rw [Nat.pow_succ] at h; rw [Nat.mul_comm 2 p, Nat.mul_assoc, Nat.mul_comm 2]; exact h)
    · omega

/-- The base-2 logarithm of a power of two, with fuel. -/
def lgF : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n ≤ 1 then 0 else lgF f (n / 2) + 1

theorem lgF_pow : ∀ f d, d ≤ f → lgF f (2 ^ d) = d
  | 0, 0, _ => rfl
  | f + 1, 0, _ => rfl
  | f + 1, d + 1, h => by
    have h2 : ¬ 2 ^ (d + 1) ≤ 1 := by
      have : 2 ^ 1 ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have : (2 : Nat) ^ 1 = 2 := rfl
      omega
    show (if 2 ^ (d + 1) ≤ 1 then 0 else lgF f (2 ^ (d + 1) / 2) + 1) = d + 1
    rw [if_neg h2, Nat.pow_succ, Nat.mul_div_cancel _ (by decide), lgF_pow f d (by omega)]

/-- The program table's height is `2^(progTp + 1)`. -/
def progTp (heap : List Cell) : Nat := lgF 64 (progTableS heap).h - 1

/-- **The program table's height**: with `n` public cells, `3 ≤ n ≤ 2^24`,
    the program table has `2^(progTp + 1)` rows, `progTp ≤ 23`. -/
theorem progS_height {heap : List Cell}
    (hlo : 3 ≤ (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)).length)
    (hhi : (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)).length ≤ 2 ^ 24) :
    progTp heap ≤ 23 ∧ (progTableS heap).h = 2 ^ (progTp heap + 1) := by
  generalize hn : (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)).length = n at hlo hhi
  have hge := pow2From_ge_n 64 1 n (by
    calc n ≤ 2 ^ 24 := hhi
      _ ≤ 1 * 2 ^ 64 := by rw [Nat.one_mul]; exact Nat.pow_le_pow_right (by decide) (by decide))
  have hle := pow2From_le hhi 64 0 (by decide)
  obtain ⟨d, hd⟩ := pow2From_pow 64 0 n
  rw [Nat.pow_zero] at hle hd
  rw [Nat.zero_add] at hd
  have hh : (progTableS heap).h = 2 ^ d := by
    show (progRowsS heap).length = _
    unfold progRowsS
    simp only [List.length_append, List.length_map, List.length_replicate]
    rw [hn, hd]
    rw [hd] at hge
    omega
  rw [hd] at hge hle
  have hd2 : 2 ≤ d := by
    rcases Nat.lt_or_ge d 2 with h | h
    · have : 2 ^ d ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
      have : (2 : Nat) ^ 1 = 2 := rfl
      omega
    · exact h
  have hd24 : d ≤ 24 := by
    rcases Nat.lt_or_ge d 25 with h | h
    · omega
    · have : 2 ^ 25 ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) h
      have : (2 : Nat) ^ 25 = 2 * 2 ^ 24 := rfl
      omega
  have ht : progTp heap = d - 1 := by unfold progTp; rw [hh, lgF_pow 64 d (by omega)]
  refine ⟨by omega, ?_⟩
  rw [ht, hh, Nat.sub_add_cancel (by omega)]

/-- **The Sudoku program table's height**, for a run from the statement
    machine over `2^16` cells. -/
theorem sud_prog_height {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle)) {ρ : Nat → Bool} {A : List Cell}
    {k : Nat} {row : Nat → Air.Row} (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hlen : A.length = 2 ^ 16) :
    let heap := (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap
    progTp heap ≤ 23 ∧ (progTableS heap).h = 2 ^ (progTp heap + 1) := by
  intro heap
  have hb := bounded_sudoku hc
  obtain ⟨_, _, hlenm, _⟩ := stmtMachine_public ρ (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
  obtain ⟨_, _, _, b732⟩ := stmt_fitsB (ρ := fun _ => false) hb
  have h0 : A.take (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap.length =
      (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap := by rw [← hA.ctr0]; exact hA.heap0
  have hml := congrArg List.length h0
  rw [List.length_take] at hml
  have eq := public_length heap 729 0 b732
  have eq' : (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)).length + 729 = heap.length := eq
  have e1 : (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap.length = heap.length := hlenm
  have b732' : 732 ≤ heap.length := b732
  have hle : heap.length ≤ 2 ^ 16 := by rw [← e1, ← hlen]; omega
  have h24 : 2 ^ 16 ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by decide)
  exact progS_height (by omega) (by omega)

-- ---------------------------------------------------------------------------
-- The Sudoku proof's PCS hides
-- ---------------------------------------------------------------------------

set_option maxRecDepth 100000 in
theorem sud_airs_P3 (hd0 stk0 ctr0 : Nat) (heap : List Cell) :
    AirP3 memAirC = true ∧ AirP3 (cpuAirS hd0 stk0 ctr0 ACC) = true ∧ AirP3 witAirS = true ∧
      AirP3 (progAirS heap) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- **The Sudoku proof's composed hiding PCS hides exactly**: with the run's
    tables meeting `Sat` at the heights `2^16`, `2^16`, `2^10`, the
    program table at `2^(tp+1)` with `tp ≤ 24`, the query points off each
    trace domain,
    `ζ` generating the extension and the FRI challenge `αb` generic, the
    PCS whose view is every group's openings, every quotient table's
    chunks, every codeword and FRI meets `PCSCloseN` with `ε = 0`, over
    the Sudoku transcript's values. -/
theorem sud_pcs {V : Type} (off : EF → String → EF) {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Wt : Table}
    (hsC : Sat (cpuAirS hd0 stk0 ctr0 ACC) C) (hsM : Sat memAirC Mm) (hsW : Sat witAirS Wt)
    (hC : C.h = 2 ^ 16) (hM : Mm.h = 2 ^ 16) (hW : Wt.h = 2 ^ 10)
    {tp : Nat} (htp : tp ≤ 24) (hPg : (progTableS heap).h = 2 ^ (tp + 1))
    {S16 S10 SP : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F))
    (hS16 : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tp + 1)) (2 ^ (tp + 1)))
    (hsz16 : 2 * S16.length + 8 ≤ 2 ^ 16) (hsz : 2 * S10.length + 8 ≤ 2 ^ 10)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tp + 1)) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw) :
    let tv := fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t
    let Ts := sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp
    let qs := sudGroups tp S16 S10 SP ζ qv
    PCSCloseN off (P ^ (friN1 qs (sudKs hd0 stk0 ctr0 heap) (Ts.map Prod.fst) + friN2 qs (Ts.map Prod.fst) ncw)) tv
      (pcsFri off tv qs (sudKs hd0 stk0 ctr0 heap) (sudCols off hd0 stk0 ctr0 heap C Mm Wt) (Ts.map Prod.fst)
        (fun t α β ms => Ts.map fun p => p.2 t α β ms) ncw αb fri)
      (psimFri qs (sudKs hd0 stk0 ctr0 heap) (Ts.map Prod.fst) ncw αb fri) 0 := by
  intro tv Ts qs
  obtain ⟨b1, b2, _, _, _, _, b7, b8, _, _⟩ := blind_ok hd0 stk0 ctr0 0 0 0 0
  obtain ⟨pM, pC, pW, pP⟩ := sud_airs_P3 hd0 stk0 ctr0 heap
  have hS4 : S10.length + 4 ≤ 2 ^ 10 - 1 + 1 := by omega
  have hS4' : S16.length + 4 ≤ 2 ^ 16 - 1 + 1 := by omega
  have hpos : 1 ≤ 2 ^ (tp + 1) := Nat.one_le_two_pow
  have hmP : 2 ^ (tp + 1) - 1 + 1 = 2 ^ (tp + 1) := Nat.sub_add_cancel hpos
  have hS4P : SP.length + 4 ≤ 2 ^ (tp + 1) - 1 + 1 := by rw [hmP]; omega
  have hm16 : 2 ^ 16 - 1 + 1 = 2 ^ (15 + 1) := by decide
  have hm10 : 2 ^ 10 - 1 + 1 = 2 ^ (9 + 1) := by decide
  have hsz16' : 2 * S16.length + 8 ≤ 2 ^ (15 + 1) := hsz16
  have hS16' : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen (15 + 1)) (2 ^ 16 - 1 + 1) := by rw [hm16]; exact hS16
  have hS10' : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen (9 + 1)) (2 ^ 10 - 1 + 1) := by rw [hm10]; exact hS10
  have hSP' : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tp + 1)) (2 ^ (tp + 1) - 1 + 1) := by rw [hmP]; exact hSP
  have hcl : ∀ (a b : Nat), a < 8 → b < 8 → ∀ t α β, ∀ j ∈ [a, b], j < (sudCols off hd0 stk0 ctr0 heap C Mm Wt t α β).length :=
    fun a b ha hb _ _ _ j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      show j < 8
      rcases hj with rfl | rfl
      · exact ha
      · exact hb
  refine pcsCloseN_fri_tabs (fun q hq => ?_) (by rfl)
    (fun t α β => sudCols_shaped off hd0 stk0 ctr0 hC hM hW hPg S16 S10 SP ζ qv t α β)
    hdb haw hncw off tv Ts (fun p hp => ?_)
  · simp only [sudGroups, List.mem_cons, List.not_mem_nil, or_false] at hq
    have g16 := bbGroup_OK (tb := 15) (qv := qv) (by decide) hS16 hζ hsz16'
    have g10 := bbGroup_OK (tb := 9) (qv := qv) (by decide) hS10 hζ hsz
    have gP := bbGroup_OK (tb := tp) (qv := qv) (by omega) hSP hζ hszP
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g16
    · exact g16
    · exact g16
    · exact g16
    · exact g10
    · exact g10
    · exact gP
    · exact gP
  · simp only [Ts, sudTs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact tabsHonest_bb off tv pM (tb := 15) (lq := 1) (m := 2 ^ 16 - 1) (gm := 0) (gp := 1) (tm := tvAt 0)
        (by decide) (by decide) (by decide) hm16 ⟨by show _ < 8; decide, rfl⟩ ⟨by show _ < 8; decide, rfl⟩
        (sudMemT Mm) Mm (fun _ => rfl)
        (sudTabs hd0 stk0 ctr0 heap C Mm Wt) (fun t => List.mem_cons_of_mem _ List.mem_cons_self)
        (hcl 0 1 (by decide) (by decide))
        (fun t α β => ⟨sat_setBlind hsM b7 _, by show Mm.h = _; rw [hM], rfl, rfl, rfl⟩)
        hζ hdet hS16' hS4'
    · exact tabsHonest_bb off tv pC (tb := 15) (lq := 1) (m := 2 ^ 16 - 1) (gm := 2) (gp := 3) (tm := tvAt 1)
        (by decide) (by decide) (by decide) hm16 ⟨by show _ < 8; decide, rfl⟩ ⟨by show _ < 8; decide, rfl⟩
        (sudCpuT C) C (fun _ => rfl)
        (sudTabs hd0 stk0 ctr0 heap C Mm Wt) (fun t => List.mem_cons_self) (hcl 2 3 (by decide) (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsC b1 _) b2 _, by show C.h = _; rw [hC], rfl, rfl, rfl⟩)
        hζ hdet hS16' hS4'
    · exact tabsHonest_bb off tv pW (tb := 9) (lq := 1) (m := 2 ^ 10 - 1) (gm := 4) (gp := 5) (tm := tvAt 2)
        (by decide) (by decide) (by decide) hm10 ⟨by show _ < 8; decide, rfl⟩ ⟨by show _ < 8; decide, rfl⟩
        (sudWitT Wt) Wt (fun _ => rfl)
        (sudTabs hd0 stk0 ctr0 heap C Mm Wt)
        (fun t => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        (hcl 4 5 (by decide) (by decide))
        (fun t α β => ⟨sat_setBlind hsW b8 _, by show Wt.h = _; rw [hW], rfl, rfl, rfl⟩)
        hζ hdet hS10' hS4
    · exact tabsHonest_bb off tv pP (tb := tp) (lq := 1) (m := 2 ^ (tp + 1) - 1) (gm := 6) (gp := 7)
        (tm := progTm off heap)
        (by omega) (by decide) (by omega) hmP ⟨by show _ < 8; decide, rfl⟩ ⟨by show _ < 8; decide, rfl⟩
        (fun _ => progTableS heap) (progTableS heap) (fun _ => rfl)
        (sudTabs hd0 stk0 ctr0 heap C Mm Wt)
        (fun t => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (hcl 6 7 (by decide) (by decide))
        (fun t α β => ⟨(progS_sat heap).1, by rw [hPg, hmP], rfl, rfl, rfl⟩)
        hζ hdet hSP' hS4P

-- ---------------------------------------------------------------------------
-- The Sudoku proof's transcript, end to end
-- ---------------------------------------------------------------------------

section
variable {V : Type} (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (tp : Nat)
  (S16 S10 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
  (wm wc ww wp : List (EF → EF → List F)) (ncw : Nat) (αb : EF) (fri : EF → EF → List (EF → EF) → V)

/-- **The Sudoku proof's composed PCS**, its simulator and its randomness. -/
def sudPcs := pcsFri off (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) (sudGroups tp S16 S10 SP ζ qv)
  (sudKs hd0 stk0 ctr0 heap) (sudCols off hd0 stk0 ctr0 heap C Mm Wt)
  ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst)
  (fun t α β ms => (sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map fun p => p.2 t α β ms)
  ncw αb fri

def sudPsim := psimFri (sudGroups tp S16 S10 SP ζ qv) (sudKs hd0 stk0 ctr0 heap)
  ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst) ncw αb fri

def sudNR : Nat := P ^ (friN1 (sudGroups tp S16 S10 SP ζ qv) (sudKs hd0 stk0 ctr0 heap)
  ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst) +
  friN2 (sudGroups tp S16 S10 SP ζ qv) ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst)
    ncw)
end

theorem preInterp_pre {A B : Table} (h : A.pre = B.pre) : preInterp A = preInterp B := by
  unfold preInterp; rw [h]

/-- **The simulator reads the tables' preprocessed columns only**: two
    sets of tables with the same preprocessed columns give the same
    simulator.  The Sudoku tables' preprocessed columns are the public
    rows (`witRowsS` for the witness, zero for the CPU and memory), so the
    simulator uses no witness. -/
theorem sudPsim_pre {V : Type} (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell)
    {C Mm Wt C' Mm' Wt' : Table} (hC : C.pre = C'.pre) (hM : Mm.pre = Mm'.pre) (hW : Wt.pre = Wt'.pre) (tp : Nat)
    (S16 S10 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) (ncw : Nat) (αb : EF) (fri : EF → EF → List (EF → EF) → V) :
    sudPsim off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp ncw αb fri =
      sudPsim off hd0 stk0 ctr0 heap C' Mm' Wt' tp S16 S10 SP ζ qv wm wc ww wp ncw αb fri := by
  simp only [sudPsim, sudTs, List.map_cons, List.map_nil, bbTab, preInterp_pre hC, preInterp_pre hM,
    preInterp_pre hW]

/-- The composed PCS's view. -/
abbrev SudPV (V : Type) : Type :=
  (List (List (List F × List EF) × List (List EF)) × List (List (List (List F × List EF)))) ×
    List (List (List F × List EF)) × V

/-- **The Sudoku proof is zero knowledge over its composed hiding PCS**,
    the program table included: for an accepting run of the Sudoku
    statement, query points off each trace domain, `ζ` generating the
    extension and the FRI challenge generic, the real transcript over
    that PCS and the simulated one, summed over `α, β, r` and the tuples
    with `β` generic, differ by at most the aborting draws:
    `sud_transcriptG` with its PCS term zero.  `tP` is the program
    table's `progTp`; the simulator reads the tables' preprocessed
    columns only (`sudPsim_pre`). -/
theorem sud_hiding {V : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    {S16 S10 SP : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F))
    (hS16 : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz16 : 2 * S16.length + 8 ≤ 2 ^ 16) (hsz : 2 * S10.length + 8 ≤ 2 ^ 10)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (E : TViewN (SudPV V) EF → Bool) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let pcs := sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv wm wc ww wp ncw αb fri
    let psim := sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv wm wc ww wp ncw αb fri
    let NR := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv wm wc ww wp ncw
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) := by
  intro blank C Pg Wt Mm pcs psim NR tabs tv tp M
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sm, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨hP23, hPg⟩ := sud_prog_height hc hA hlen
  rw [← htp] at hP23 hPg
  have hpcs := sud_pcs (heap := blank.heap) off sc sm sw (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) (by omega) hPg qv
    wm wc ww wp hS16 hS10 hSP hsz16 hsz hszP hζ hdet (fri := fri) hdb haw hncw
  exact sud_transcriptG off NR 0 pcs psim hbal hun hpcs E

end Circuit
