import Ski.ZK.SudRun
import Ski.ZK.BbGroup

/-!
# The Sudoku proof's composed hiding PCS

The Sudoku circuit's private tables are the memory, CPU and witness
tables, blinded by the edge tuples (`sudMemT`, `sudCpuT`, `sudWitT`).
Each is committed as two trace groups, its main columns and its
permutation columns (`bbGroup`, `mainCols`, `permCols`): six groups,
heights `2^16`, `2^16` and `2^10` (`sudGroups`, `sudCols`).  Each has a
quotient table over its two groups (`airQTabG`) with Plonky3's chunks.

Each height has its own query points, `S16` for the `2^16` tables and
`S10` for the witness, as Plonky3 opens each matrix at its own height's
points.  The AIRs have Plonky3 degree 2, so with `is_zk` Plonky3 makes
`2^(log2_ceil 2 + 1) = 4` chunks per table, the count `bbTab` fixes.
The public program table has no group and no quotient table here:
Plonky3 commits its main, permutation and quotient matrices, which this
view omits (open).

`sud_pcs`: that PCS, its view every group's openings, every table's
chunks, every codeword and FRI, meets `PCSCloseN` with `ε = 0` over the
Sudoku transcript's values.  `sud_hiding`: for an accepting run of the
Sudoku statement, `sud_transcriptG` over that PCS, its PCS term zero.

Assumed: the query points off the trace domains (`lde_off_trace` gives
it for Plonky3's), `2 |S| + 8` within each height, `ζ` and the FRI
challenge `αb` generic and fixed (with `ws`, `qv` and the query points,
not sampled here), Fiat–Shamir, the Merkle commitments' hiding, and the modeling
facts the earlier modules name (the groups' trace and mask points, the
opened points `S ++ g S`).
-/

namespace Circuit

open ZKF SudokuText B Air Stmt Mach Sudoku

/-- The blinded private tables. -/
def sudMemT (Mm : Table) (t : Nat → Tup) : Table := Mm.setBlind 5 (t 0)
def sudCpuT (C : Table) (t : Nat → Tup) : Table := (C.setBlind BLA (t 1)).setBlind BLB (t 0)
def sudWitT (Wt : Table) (t : Nat → Tup) : Table := Wt.setBlind 1 (t 1)

/-- The six trace groups: memory, CPU (`2^16` rows) and witness (`2^10`),
    main and permutation each. -/
def sudGroups (S16 S10 : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF) : List QGroup :=
  [bbGroup 15 S16 ζ qv, bbGroup 15 S16 ζ qv, bbGroup 15 S16 ζ qv, bbGroup 15 S16 ζ qv, bbGroup 9 S10 ζ qv,
   bbGroup 9 S10 ζ qv]

/-- The committed columns: each blinded table's main and permutation columns. -/
def sudCols (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (C Mm Wt : Table) (t : Nat → Tup) (α β : EF) :
    List (List (List F)) :=
  [mainCols (sudMemT Mm t) memAirC.width,
   permCols (sudMemT Mm t) (busAlphas (prefixOf α (off β)) memAirC) β (corpusLs memAirC),
   mainCols (sudCpuT C t) (cpuAirS hd0 stk0 ctr0 ACC).width,
   permCols (sudCpuT C t) (busAlphas (prefixOf α (off β)) (cpuAirS hd0 stk0 ctr0 ACC)) β
     (corpusLs (cpuAirS hd0 stk0 ctr0 ACC)),
   mainCols (sudWitT Wt t) witAirS.width,
   permCols (sudWitT Wt t) (busAlphas (prefixOf α (off β)) witAirS) β (corpusLs witAirS)]

/-- The column counts. -/
def sudKs (hd0 stk0 ctr0 : Nat) : List Nat :=
  [memAirC.width, 4 * ((corpusLs memAirC).length + 1), (cpuAirS hd0 stk0 ctr0 ACC).width,
   4 * ((corpusLs (cpuAirS hd0 stk0 ctr0 ACC)).length + 1), witAirS.width, 4 * ((corpusLs witAirS).length + 1)]

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
theorem sudCols_shaped (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) {C Mm Wt : Table}
    (hC : C.h = 2 ^ 16) (hM : Mm.h = 2 ^ 16) (hW : Wt.h = 2 ^ 10) (S16 S10 : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (t : Nat → Tup) (α β : EF) :
    Shaped ((sudGroups S16 S10 ζ qv).map QGroup.ext) (sudCols off hd0 stk0 ctr0 C Mm Wt t α β) ∧
      (sudCols off hd0 stk0 ctr0 C Mm Wt t α β).map List.length = sudKs hd0 stk0 ctr0 := by
  have m1 := mainCols_shape (sudMemT Mm t) memAirC.width
  have p1 := permCols_shape (sudMemT Mm t) (busAlphas (prefixOf α (off β)) memAirC) β (corpusLs memAirC)
  have m2 := mainCols_shape (sudCpuT C t) (cpuAirS hd0 stk0 ctr0 ACC).width
  have p2 := permCols_shape (sudCpuT C t) (busAlphas (prefixOf α (off β)) (cpuAirS hd0 stk0 ctr0 ACC)) β
    (corpusLs (cpuAirS hd0 stk0 ctr0 ACC))
  have m3 := mainCols_shape (sudWitT Wt t) witAirS.width
  have p3 := permCols_shape (sudWitT Wt t) (busAlphas (prefixOf α (off β)) witAirS) β (corpusLs witAirS)
  have hMh : (sudMemT Mm t).h = 2 ^ (15 + 1) := hM
  have hCh : (sudCpuT C t).h = 2 ^ (15 + 1) := hC
  have hWh : (sudWitT Wt t).h = 2 ^ (9 + 1) := hW
  refine ⟨⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, trivial⟩, ?_⟩
  · rw [m1.2 c hc, hMh]; rfl
  · rw [p1.2 c hc, hMh]; rfl
  · rw [m2.2 c hc, hCh]; rfl
  · rw [p2.2 c hc, hCh]; rfl
  · rw [m3.2 c hc, hWh]; rfl
  · rw [p3.2 c hc, hWh]; rfl
  · show [_, _, _, _, _, _] = _
    rw [m1.1, p1.1, m2.1, p2.1, m3.1, p3.1]; rfl

-- ---------------------------------------------------------------------------
-- The quotient tables and their data
-- ---------------------------------------------------------------------------

/-- An AIR's constraints with its LogUp constraints at the transcript's
    terminal `k`. -/
def lupAF (off : EF → String → EF) (A : AirD) (k : Nat) : EF → EF → List EF → AirD :=
  fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (v.getD k EF.zero) A.width (corpusLs A)

/-- **A private table's quotient table** over its groups `gm`, `gp`. -/
def bbTab (off : EF → String → EF) (A : AirD) (k tb m : Nat) (P0 : Table) (gm gp : Nat) (S : List F) (ζ : EF)
    (ws : List (EF → EF → List F)) : QTab :=
  airQTabG (lupAF off A k) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) [gm, gp] (bbκ tb 1 m) (bbCs tb 1 m)
    (bbHl tb 1 m) (bbCl tb 1 m) S ζ ws

/-- **Its data**: the honest chunks where the proof does not abort, the
    canonical ones elsewhere. -/
def bbData (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF) (A : AirD) (k tb m : Nat)
    (P0 : Table) (gm gp : Nat) (S : List F) (ζ : EF) (ws : List (EF → EF → List F)) (qs : List QGroup)
    (cols : (Nat → Tup) → EF → EF → List (List (List F))) (tabs : (Nat → Tup) → List (AirD × Table))
    (t : Nat → Tup) (α β : EF) (ms : List F) : List (List (List F) × List F) :=
  if Aborts (prefixOf α (off β)) β (tabs t) = false then
    airData (withLup A (busAlphas (prefixOf α (off β)) A) β ((tv (prefixOf α (off β)) β t).getD k EF.zero)
      A.width (corpusLs A)) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) (bbCs tb 1 m) (bbHl tb 1 m)
      ws α β (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) [gm, gp])
  else canonData (bbTab off A k tb m P0 gm gp S ζ ws).sets α β (tv (prefixOf α (off β)) β t)
    (openMulti (qs.map QGroup.ext) (cols t α β) ms)

/-- The transcript's tables: the blinded private tables and the program. -/
def sudTabs (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (t : Nat → Tup) : List (AirD × Table) :=
  sudTables hd0 stk0 ctr0 heap (sudCpuT C t) (sudMemT Mm t) (progTableS heap) (sudWitT Wt t)

/-- **The Sudoku proof's three quotient tables**, memory, CPU and witness,
    with their data. -/
def sudTs (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (S16 S10 : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (wm wc ww : List (EF → EF → List F)) :
    List (QTab × ((Nat → Tup) → EF → EF → List F → List (List (List F) × List F))) :=
  let tv := fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t
  let qs := sudGroups S16 S10 ζ qv
  let cols := sudCols off hd0 stk0 ctr0 C Mm Wt
  let tabs := sudTabs hd0 stk0 ctr0 heap C Mm Wt
  [(bbTab off memAirC 0 15 (2 ^ 16 - 1) Mm 0 1 S16 ζ wm,
     bbData off tv memAirC 0 15 (2 ^ 16 - 1) Mm 0 1 S16 ζ wm qs cols tabs),
   (bbTab off (cpuAirS hd0 stk0 ctr0 ACC) 1 15 (2 ^ 16 - 1) C 2 3 S16 ζ wc,
     bbData off tv (cpuAirS hd0 stk0 ctr0 ACC) 1 15 (2 ^ 16 - 1) C 2 3 S16 ζ wc qs cols tabs),
   (bbTab off witAirS 2 9 (2 ^ 10 - 1) Wt 4 5 S10 ζ ww,
     bbData off tv witAirS 2 9 (2 ^ 10 - 1) Wt 4 5 S10 ζ ww qs cols tabs)]

-- ---------------------------------------------------------------------------
-- The Sudoku proof's PCS hides
-- ---------------------------------------------------------------------------

set_option maxRecDepth 100000 in
theorem sud_airs_P3 (hd0 stk0 ctr0 : Nat) :
    AirP3 memAirC = true ∧ AirP3 (cpuAirS hd0 stk0 ctr0 ACC) = true ∧ AirP3 witAirS = true :=
  ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- **The Sudoku proof's composed hiding PCS hides exactly**: with the run's
    tables meeting `Sat` at the heights `2^16`, `2^16`, `2^10`, the query
    points off both trace domains, `ζ` generating the extension and the
    FRI challenge `αb` generic, the PCS whose view is every group's
    openings, every quotient table's chunks, every codeword and FRI meets
    `PCSCloseN` with `ε = 0`, over the Sudoku transcript's values. -/
theorem sud_pcs {V : Type} (off : EF → String → EF) {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Wt : Table}
    (hsC : Sat (cpuAirS hd0 stk0 ctr0 ACC) C) (hsM : Sat memAirC Mm) (hsW : Sat witAirS Wt)
    (hC : C.h = 2 ^ 16) (hM : Mm.h = 2 ^ 16) (hW : Wt.h = 2 ^ 10)
    {S16 S10 : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww : List (EF → EF → List F))
    (hS16 : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hsz16 : 2 * S16.length + 8 ≤ 2 ^ 16) (hsz : 2 * S10.length + 8 ≤ 2 ^ 10) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw) :
    let tv := fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t
    let Ts := sudTs off hd0 stk0 ctr0 heap C Mm Wt S16 S10 ζ qv wm wc ww
    PCSCloseN off (P ^ (friN1 (sudGroups S16 S10 ζ qv) (sudKs hd0 stk0 ctr0) (Ts.map Prod.fst) +
        friN2 (sudGroups S16 S10 ζ qv) (Ts.map Prod.fst) ncw)) tv
      (pcsFri off tv (sudGroups S16 S10 ζ qv) (sudKs hd0 stk0 ctr0) (sudCols off hd0 stk0 ctr0 C Mm Wt) (Ts.map Prod.fst)
        (fun t α β ms => Ts.map fun p => p.2 t α β ms) ncw αb fri)
      (psimFri (sudGroups S16 S10 ζ qv) (sudKs hd0 stk0 ctr0) (Ts.map Prod.fst) ncw αb fri) 0 := by
  intro tv Ts
  obtain ⟨b1, b2, _, _, _, _, b7, b8, _, _⟩ := blind_ok hd0 stk0 ctr0 0 0 0 0
  obtain ⟨pM, pC, pW⟩ := sud_airs_P3 hd0 stk0 ctr0
  have hS4 : S10.length + 4 ≤ 2 ^ 10 - 1 + 1 := by omega
  have hS4' : S16.length + 4 ≤ 2 ^ 16 - 1 + 1 := by omega
  have hm16 : 2 ^ 16 - 1 + 1 = 2 ^ (15 + 1) := by decide
  have hm10 : 2 ^ 10 - 1 + 1 = 2 ^ (9 + 1) := by decide
  have hsz16' : 2 * S16.length + 8 ≤ 2 ^ (15 + 1) := hsz16
  have hS16' : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen (15 + 1)) (2 ^ 16 - 1 + 1) := by rw [hm16]; exact hS16
  have hS10' : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen (9 + 1)) (2 ^ 10 - 1 + 1) := by rw [hm10]; exact hS10
  have hcl : ∀ t α β, ∀ j ∈ [0, 1], j < (sudCols off hd0 stk0 ctr0 C Mm Wt t α β).length := fun _ _ _ j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl <;> exact (by show _ < 6; decide)
  have hcl2 : ∀ t α β, ∀ j ∈ [2, 3], j < (sudCols off hd0 stk0 ctr0 C Mm Wt t α β).length := fun _ _ _ j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl <;> exact (by show _ < 6; decide)
  have hcl3 : ∀ t α β, ∀ j ∈ [4, 5], j < (sudCols off hd0 stk0 ctr0 C Mm Wt t α β).length := fun _ _ _ j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl <;> exact (by show _ < 6; decide)
  refine pcsCloseN_fri_tabs (fun q hq => ?_) (by rfl) (fun t α β => sudCols_shaped off hd0 stk0 ctr0 hC hM hW S16 S10 ζ qv t α β)
    hdb haw hncw off tv Ts (fun p hp => ?_)
  · simp only [sudGroups, List.mem_cons, List.not_mem_nil, or_false] at hq
    have g16 := bbGroup_OK (tb := 15) (qv := qv) (by decide) hS16 hζ hsz16'
    have g10 := bbGroup_OK (tb := 9) (qv := qv) (by decide) hS10 hζ hsz
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact g16
    · exact g16
    · exact g16
    · exact g16
    · exact g10
    · exact g10
  · simp only [Ts, sudTs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact tabsHonest_bb off tv pM (tb := 15) (lq := 1) (m := 2 ^ 16 - 1) (gm := 0) (gp := 1) (k := 0)
        (by decide) (by decide) (by decide) hm16 ⟨by show _ < 6; decide, rfl⟩ ⟨by show _ < 6; decide, rfl⟩ (sudMemT Mm) Mm (fun _ => rfl)
        (sudTabs hd0 stk0 ctr0 heap C Mm Wt) (fun t => List.mem_cons_of_mem _ List.mem_cons_self) hcl
        (fun t α β => ⟨sat_setBlind hsM b7 _, by show Mm.h = _; rw [hM], rfl, rfl, rfl⟩)
        hζ hdet hS16' hS4'
    · exact tabsHonest_bb off tv pC (tb := 15) (lq := 1) (m := 2 ^ 16 - 1) (gm := 2) (gp := 3) (k := 1)
        (by decide) (by decide) (by decide) hm16 ⟨by show _ < 6; decide, rfl⟩ ⟨by show _ < 6; decide, rfl⟩ (sudCpuT C) C (fun _ => rfl)
        (sudTabs hd0 stk0 ctr0 heap C Mm Wt) (fun t => List.mem_cons_self) hcl2
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsC b1 _) b2 _, by show C.h = _; rw [hC], rfl, rfl, rfl⟩)
        hζ hdet hS16' hS4'
    · exact tabsHonest_bb off tv pW (tb := 9) (lq := 1) (m := 2 ^ 10 - 1) (gm := 4) (gp := 5) (k := 2)
        (by decide) (by decide) (by decide) hm10 ⟨by show _ < 6; decide, rfl⟩ ⟨by show _ < 6; decide, rfl⟩ (sudWitT Wt) Wt (fun _ => rfl)
        (sudTabs hd0 stk0 ctr0 heap C Mm Wt)
        (fun t => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) hcl3
        (fun t α β => ⟨sat_setBlind hsW b8 _, by show Wt.h = _; rw [hW], rfl, rfl, rfl⟩)
        hζ hdet hS10' hS4

-- ---------------------------------------------------------------------------
-- The Sudoku proof's transcript, end to end
-- ---------------------------------------------------------------------------

section
variable {V : Type} (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table)
  (S16 S10 : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
  (wm wc ww : List (EF → EF → List F)) (ncw : Nat) (αb : EF) (fri : EF → EF → List (EF → EF) → V)

/-- **The Sudoku proof's composed PCS**, its simulator and its randomness. -/
def sudPcs := pcsFri off (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) (sudGroups S16 S10 ζ qv)
  (sudKs hd0 stk0 ctr0) (sudCols off hd0 stk0 ctr0 C Mm Wt) ((sudTs off hd0 stk0 ctr0 heap C Mm Wt S16 S10 ζ qv wm wc ww).map Prod.fst)
  (fun t α β ms => (sudTs off hd0 stk0 ctr0 heap C Mm Wt S16 S10 ζ qv wm wc ww).map fun p => p.2 t α β ms) ncw αb fri

def sudPsim := psimFri (sudGroups S16 S10 ζ qv) (sudKs hd0 stk0 ctr0)
  ((sudTs off hd0 stk0 ctr0 heap C Mm Wt S16 S10 ζ qv wm wc ww).map Prod.fst) ncw αb fri

def sudNR : Nat := P ^ (friN1 (sudGroups S16 S10 ζ qv) (sudKs hd0 stk0 ctr0)
  ((sudTs off hd0 stk0 ctr0 heap C Mm Wt S16 S10 ζ qv wm wc ww).map Prod.fst) +
  friN2 (sudGroups S16 S10 ζ qv) ((sudTs off hd0 stk0 ctr0 heap C Mm Wt S16 S10 ζ qv wm wc ww).map Prod.fst) ncw)
end

/-- The composed PCS's view. -/
abbrev SudPV (V : Type) : Type :=
  (List (List (List F × List EF) × List (List EF)) × List (List (List (List F × List EF)))) ×
    List (List (List F × List EF)) × V

/-- **The Sudoku proof's private tables are zero knowledge over their
    composed hiding PCS**: for an accepting run of the Sudoku statement,
    query points off the trace domains, `ζ` generating the extension and
    the FRI challenge generic, the real transcript over that PCS and the
    simulated one, summed over `α, β, r` and the tuples with `β` generic,
    differ by at most the aborting draws: `sud_transcriptG` with its PCS
    term zero. -/
theorem sud_hiding {V : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {S16 S10 : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww : List (EF → EF → List F))
    (hS16 : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hsz16 : 2 * S16.length + 8 ≤ 2 ^ 16) (hsz : 2 * S10.length + 8 ≤ 2 ^ 10) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (E : TViewN (SudPV V) EF → Bool) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let pcs := sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt S16 S10 ζ qv wm wc ww ncw αb fri
    let psim := sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt S16 S10 ζ qv wm wc ww ncw αb fri
    let NR := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt S16 S10 ζ qv wm wc ww ncw
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
  have hpcs := sud_pcs (heap := blank.heap) off sc sm sw (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) qv wm wc ww
    hS16 hS10 hsz16 hsz hζ hdet (fri := fri) hdb haw hncw
  exact sud_transcriptG off NR 0 pcs psim hbal hun hpcs E

end Circuit
