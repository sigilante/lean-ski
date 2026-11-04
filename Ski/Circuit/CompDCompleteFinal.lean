import Ski.Circuit.CompDBal

/-!
# Completeness of the circuit with the `dec` jet, the CPU's half

**`compDG_complete_dec`**: an honest run of the circuit with the `dec` jet
(`DRun.Honest`) from the composed machine of literal bits and a
well-formed region, at the heights a statement names, with a DEC table that
provides the jet's calls (`DecProvides`: it satisfies DEC, is clear past
its columns, looks up only memory cells and, on every bus but `mem` and
`segs`, receives each jet row's need and sends its result, the negation of
what the honest CPU sends, `DRun.jetSendsD`), gives tables that AIRs with
the normal forms of `compDAirsG Vs W` accept, with Plonky3's selectors.
The CPU table is the honest one (`DRun.cpuTableD`, `cpuD_sat`,
`cpuD_honest`, `cpuD_segsHonest`, `cpuD_jetSends`), and it decodes back to
the run.  What is left of completeness is DEC's honest table
(`todo/DecCompleteTodo.lean`).
-/

namespace Circuit

open B Air Compose CompM Mach Stmt Wit ComposedDText

/-- **A DEC table that provides the jet's calls** of the run `R` within `K`
    CPU rows. -/
structure DecProvides (R : DRun) (K : Nat) (D : Table) : Prop where
  sat : Sat Dec.decAir D
  wide : Wide Dec.decAir D
  mem : HonestMem R.A Dec.decAir D
  sends : ∀ B, B ≠ "mem" → B ≠ "segs" → ∀ v, tableSends Dec.decAir D B v = -(DRun.jetSendsD R K B v)

namespace DRun

variable {R : DRun} {m0 : Mach} {nilA : Nat} (hA : R.Honest m0 nilA)
include hA

/-- **Every counter of an honest run is within the memory.** -/
theorem ctr_le : ∀ i, i ≤ R.e (R.n - 1) → (R.row i).ctr ≤ R.A.length := by
  intro i
  induction i with
  | zero =>
    intro _
    have := congrArg List.length hA.acc.heap0
    rw [List.length_take, ← hA.acc.ctr0] at this
    omega
  | succ i ih =>
    intro hi
    have hc := ih (by omega)
    cases hr : isRestart R.e R.n i with
    | true =>
      obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
      rw [hA.acc.restart j hj]; exact hc
    | false =>
      rcases step_row hA (by omega) hr with h | h
      · have hroots : RootsOK (R.A.take (R.row i).ctr) [] [] := fun _ _ h => nomatch h
        exact (Air.normRow_spec hroots (Nat.le_refl _) hc h).2.1
      · exact (DecJet.decRow_ctr_len h hc).2

/-- **Every stack pointer of an honest run is in memory.** -/
theorem stk_le (hfit : Fits R.A) (hnil : nilA ≤ R.A.length) :
    ∀ i, i ≤ R.e (R.n - 1) → (R.row i).stk ≤ R.A.length := by
  have hc := ctr_le hA
  intro i
  induction i with
  | zero => intro _; rw [hA.acc.stk0]; exact hnil
  | succ i ih =>
    intro hi
    cases hr : isRestart R.e R.n i with
    | true =>
      obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
      rw [hA.acc.restart j hj]; exact hnil
    | false =>
      rcases step_row hA (by omega) hr with (h | ⟨_, _, hm, _, _⟩ | h) | h
      · exact step_stk hfit h (hc i (by omega)) (hc (i + 1) hi)
      · exact absurd hm List.not_mem_nil
      · rw [h.2]; exact ih (by omega)
      · obtain ⟨_, _, p, rest, hstk, hrs⟩ := decRow_inv h
        obtain ⟨_, hget⟩ := rd_get hstk
        have hm := List.mem_of_getElem? hget
        have := (hfit _ hm).2
        rw [hrs]; simp only [cellFields] at this; omega

end DRun

set_option maxRecDepth 100000 in
/-- **Completeness of the circuit with the `dec` jet, given DEC**: an honest
    run from the composed machine of literal bits and a well-formed region
    of `W` cells, over a memory of `2^Lm` cells whose cells point into it,
    ending within `2^R` rows, with a DEC table of `2^LD` rows providing its
    jet calls, gives tables that AIRs with the normal forms of
    `compDAirsG Vs W` accept, with Plonky3's selectors: the honest CPU, the
    memory table counting every lookup, the public program and segment
    tables, the honest witness table, and DEC; the memory and the rows
    decode back. -/
theorem compDG_complete_dec {R Lm LD : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLD : LD ≤ 20)
    {Vs : List OTerm} {W : Nat} {Rs : List AirD} (hs : sameAirsB Rs (compDAirsG Vs W) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpD + 3 + i) c = true)
    (hNW : BT.nleaves shpD + W ≤ 2 ^ 8)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : DRun.Honest ⟨A, JD, (cHeapO ρ shpD region Vs).2, e, Vs.length, row⟩ (cMachineO ρ shpD region Vs)
      (cHeapO ρ shpD region Vs).1.length)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e (Vs.length - 1) < 2 ^ R)
    {D : Table} (hD : D.h = 2 ^ LD)
    (hdec : DecProvides ⟨A, JD, (cHeapO ρ shpD region Vs).2, e, Vs.length, row⟩ (2 ^ R) D) :
    ∃ C Mm Pg Wt Sg, AcceptedP Rs [C, Mm, Pg, Wt, Sg, D] ∧
      C = DRun.cpuTableD ⟨A, JD, (cHeapO ρ shpD region Vs).2, e, Vs.length, row⟩ (2 ^ R) ∧
      Pg = progTableC (blankMO shpD W Vs).heap (BT.nleaves shpD) W ∧ Wt = witTable A (BT.nleaves shpD) W ∧
      C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ memOf Mm = A ∧ ∀ i, i ≤ e (Vs.length - 1) → rowOf C i = row i := by
  let Rn : DRun := ⟨A, JD, (cHeapO ρ shpD region Vs).2, e, Vs.length, row⟩
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots', hlenm, _, _⟩ :=
    cMachineO_public ρ (fun _ => false) shpD region (List.replicate W .S) Vs hl
  have eR : (cHeapO ρ shpD region Vs).2 = blankRootsO shpD W Vs := hroots'
  have hn : 0 < Vs.length := hA.acc.npos
  have hnR : (blankRootsO shpD W Vs).length = Vs.length := blankRootsO_length _ _ _
  have hRb : 2 ^ R ≤ 1048576 := Nat.pow_le_pow_right (by decide) hR
  have hLb : 2 ^ Lm ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLm
  have hctr := DRun.ctr_le hA
  have hK' : Rn.e (Rn.n - 1) < 2 ^ R := hK
  let C := Rn.cpuTableD (2 ^ R)
  have hb : ∀ i, i < 2 ^ R → (rowP Rn.row Rn.e Rn.n i).ctr ≤ 2 ^ 24 := by
    intro i _
    unfold rowP
    split
    · next h => exact Nat.le_trans (hctr i h) (by show A.length ≤ _; omega)
    · exact Nat.le_trans (hctr _ (Nat.le_refl _)) (by show A.length ≤ _; omega)
  have eAir : cpuAirDec (Rn.segRoots.getD 0 0) (cHeapO ρ shpD region Vs).1.length
      (cMachineO ρ shpD region Vs).heap.length Rn.n (cHeapO ρ shpD region Vs).1.length Rn.J = cpuDG Vs W := by
    show cpuAirDec ((cHeapO ρ shpD region Vs).2.getD 0 0) (cHeapO ρ shpD region Vs).1.length
      (cMachineO ρ shpD region Vs).heap.length Vs.length (cHeapO ρ shpD region Vs).1.length JD = _
    rw [eR, hlenm, ← hnR, show (cHeapO ρ shpD region Vs).1.length = (blankMO shpD W Vs).stk from hstk]
    rfl
  have hH : DecHonest A (cpuDG Vs W) (blankRootsO shpD W Vs) C D := by
    refine ⟨?_, ?_, ?_, hdec.sat, hdec.wide, hdec.mem, ?_⟩
    · have := DRun.cpuD_sat hA hK' hb
      rw [eAir] at this; exact this
    · exact DRun.cpuD_honest hA hK' _ _ _ _ _ _
    · have := DRun.cpuD_segsHonest hA hK' (blankMO shpD W Vs).hd (blankMO shpD W Vs).stk
        (blankMO shpD W Vs).heap.length (blankRootsO shpD W Vs).length (blankMO shpD W Vs).stk JD
        (show Rn.segRoots.length = Rn.n by show (cHeapO ρ shpD region Vs).2.length = _; rw [eR, hnR])
      rw [show Rn.segRoots = blankRootsO shpD W Vs from eR] at this
      exact this
    · intro B hBm hBs v
      rw [show cpuDG Vs W = cpuAirDec _ _ _ _ _ _ from rfl, DRun.cpuD_jetSends Rn _ _ _ _ _ _ _ hBm hBs v,
        hdec.sends B hBm hBs v, add_comm']
      exact neg_add_cancel' _
  have hA' : AcceptsCD A (cMachineO ρ shpD region Vs) JD (cHeapO ρ shpD region Vs).2
      (cHeapO ρ shpD region Vs).1.length Vs.length e row := hA.acc
  obtain ⟨hacc, hmem, _⟩ := compDG_complete_of hR hLm hLD hs hrl hr hNW hA' hfit hlen hK rfl hD hH
  refine ⟨C, _, _, _, _, hacc, rfl, rfl, rfl, rfl, hlen, hmem, ?_⟩
  -- the rows decode back
  intro i hi
  have hiK : i < 2 ^ R := by omega
  have hR' := DRun.runC hA hK'
  have hc : (row i).ctr ≤ A.length := hctr i hi
  have hS := shape (hR'.valid i hiK)
  obtain ⟨cell, hrd, _⟩ := hS.reads 0 (by decide) rfl
  have hh := (rd_get hrd).1
  have hq : Rn.rowQ i = row i := DRun.rowQ_of_le (R := Rn) hi
  have e1 : rowP row e Vs.length i = row i := hq
  rw [e1] at hh
  have hnil : (cHeapO ρ shpD region Vs).1.length ≤ A.length := by
    have h0 : (A.take (row 0).ctr).length = (cMachineO ρ shpD region Vs).heap.length :=
      congrArg List.length hA.acc.heap0
    rw [List.length_take] at h0
    have h1 : (row 0).ctr = (cMachineO ρ shpD region Vs).heap.length := hA.acc.ctr0
    have : (cHeapO ρ shpD region Vs).1.length < (cMachineO ρ shpD region Vs).heap.length := by
      show _ < ((cHeapO ρ shpD region Vs).1 ++ [Cell.nil]).length; simp
    omega
  have hst : (row i).stk ≤ A.length := DRun.stk_le hA hfit hnil i hi
  have hPP : P = 2013265921 := rfl
  have hst' : (row i).stk < P := by
    have : (row i).stk ≤ A.length := hst
    omega
  show (⟨(Rn.cpuColD i HD).val, (Rn.cpuColD i STK).val, (Rn.cpuColD i CTR).val⟩ : Air.Row) = row i
  rw [Rn.colD_hd, Rn.colD_stk, Rn.colD_ctr, hq]
  rw [val_ofN (by show (row i).hd < P; have : (row i).hd < (row i).ctr := hh; omega),
    val_ofN hst', val_ofN (by omega)]

end Circuit

namespace Circuit

open B Air

-- ---------------------------------------------------------------------------
-- A run without jet calls: the zero DEC table
-- ---------------------------------------------------------------------------

/-- The zero DEC table of `H` rows: DEC's padding. -/
def decZero (H : Nat) : Table := ⟨H, fun _ _ => 0, fun _ _ => 0⟩

set_option maxRecDepth 100000 in
theorem decCons_now : Dec.decCons.all (fun c => c.onlyAtoms nowAtom) = true := by decide

set_option maxRecDepth 100000 in
theorem decCons_zero : Dec.decCons.all (fun c => decide (c.eval (fun _ => 0) = 0)) = true := by decide

set_option maxRecDepth 100000 in
theorem decInters_now : Dec.decInters.all (fun I => I.count.onlyAtoms nowAtom) = true := by decide

set_option maxRecDepth 100000 in
theorem decInters_zero : Dec.decInters.all (fun I => decide (I.count.eval (fun _ => 0) = 0)) = true := by decide

theorem decZero_env {H r : Nat} : ∀ a, nowAtom a = true → (decZero H).env r a = (fun _ => (0 : F)) a := by
  intro a ha
  cases a with
  | main o c =>
    cases o with
    | zero => rfl
    | succ o => simp [nowAtom] at ha
  | _ => simp [nowAtom] at ha

/-- **The zero row satisfies DEC.** -/
theorem decZero_sat {H : Nat} (hH : 0 < H) : Sat Dec.decAir (decZero H) := by
  refine ⟨hH, fun c hc r _ => ?_⟩
  rw [E.eval_congr decZero_env c (List.all_eq_true.1 decCons_now c hc)]
  exact of_decide_eq_true (List.all_eq_true.1 decCons_zero c hc)

/-- The zero row's messages are quiet. -/
theorem decZero_quiet {H r : Nat} {I : Inter} (hI : I ∈ Dec.decAir.inters) :
    I.count.eval ((decZero H).env r) = 0 := by
  rw [E.eval_congr decZero_env I.count (List.all_eq_true.1 decInters_now I hI)]
  exact of_decide_eq_true (List.all_eq_true.1 decInters_zero I hI)

theorem decZero_sends {H : Nat} (B : String) (v : List F) : tableSends Dec.decAir (decZero H) B v = 0 :=
  sends_zero_of (Q := fun _ => False) (fun _ _ I hI _ hc => hc (decZero_quiet hI)) id

/-- With no jet row, the CPU sends nothing on the jet's buses. -/
theorem jetSendsD_none {R : DRun} {K : Nat} (h : ∀ r, r < K → R.jetAt r = false) (B : String) (v : List F) :
    DRun.jetSendsD R K B v = 0 := by
  unfold DRun.jetSendsD
  apply fold_zero
  intro r hr
  rw [h r (List.mem_range.1 hr)]; rfl

/-- **A run without jet calls has its DEC table**: the zero one. -/
theorem decProvides_none {R : DRun} {K H : Nat} (hH : 0 < H) (h : ∀ r, r < K → R.jetAt r = false) :
    DecProvides R K (decZero H) :=
  ⟨decZero_sat hH, fun _ _ _ _ => rfl, fun _ _ _ hI _ hc => absurd (decZero_quiet hI) hc,
   fun B _ _ v => by rw [decZero_sends, jetSendsD_none h]; exact neg_zero_eq.symm⟩

open Stmt Wit ComposedDText CompM Compose Mach in
/-- **Completeness for a run that never fires the jet**: unconditional, DEC
    the zero table. -/
theorem compDG_complete_nojet {R Lm LD : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLD : LD ≤ 20)
    {Vs : List OTerm} {W : Nat} {Rs : List AirD} (hs : sameAirsB Rs (compDAirsG Vs W) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpD + 3 + i) c = true)
    (hNW : BT.nleaves shpD + W ≤ 2 ^ 8)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : DRun.Honest ⟨A, JD, (cHeapO ρ shpD region Vs).2, e, Vs.length, row⟩ (cMachineO ρ shpD region Vs)
      (cHeapO ρ shpD region Vs).1.length)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e (Vs.length - 1) < 2 ^ R)
    (hnone : ∀ r, r < 2 ^ R → DRun.jetAt ⟨A, JD, (cHeapO ρ shpD region Vs).2, e, Vs.length, row⟩ r = false) :
    ∃ C Mm Pg Wt Sg, AcceptedP Rs [C, Mm, Pg, Wt, Sg, decZero (2 ^ LD)] ∧ memOf Mm = A ∧
      ∀ i, i ≤ e (Vs.length - 1) → rowOf C i = row i := by
  obtain ⟨C, Mm, Pg, Wt, Sg, hacc, _, _, _, _, _, hmem, hrow⟩ :=
    compDG_complete_dec hR hLm hLD hs hrl hr hNW hA hfit hlen hK rfl (decProvides_none (Nat.two_pow_pos _) hnone)
  exact ⟨C, Mm, Pg, Wt, Sg, hacc, hmem, hrow⟩

end Circuit
