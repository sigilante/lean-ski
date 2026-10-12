import Ski.ZK.ComposeZK
import Ski.ZK.Honest

/-!
# The composed circuit as a `PSD`

A `Compose.PSD` instance for the composed circuit, its zero knowledge
proved.  The relation is the circuit's: a statement (a shape of bits, the
terms, the region size, the heights) and an accepted run of its composed
machine within the heights, from literal bits and a well-formed region
(`CRel`, `comp_completeG_log`'s hypotheses).  The prover's proof at a draw
is the real transcript of the honest tables the run gives (`comp_honest_zk`);
the simulator's is `simVN`, from the statement alone.

Zero knowledge is proved: `comp_honest_zk` and `transcript_zkG` give
`CloseD` over the generic draws `tdraws NR 2`, with an error that depends
on the statement alone, the message count `cM` its heights fix
(`comp_entries`).  Completeness, knowledge soundness and the PCS's
closeness are the STARK's, assumed: the constructor `compPSD` takes them
as arguments.  What the relation does not give is the step from an
accepted evaluation witness, bits and a term, to an accepted run within
the heights.
-/

namespace Circuit

open ZKF Compose B Air CompM Mach Wit

/-- **A composed statement**: the shape of the bits, the terms, the region
    size, and the heights `2^R` rows and `2^Lm` memory cells. -/
structure CStmt where
  shp : BT
  Ps : List Term
  W : Nat
  R : Nat
  Lm : Nat

/-- **A run**: the bits, the region, the memory, the segment ends and the
    rows. -/
structure CRun' where
  ρ : Nat → Bool
  region : List Cell
  A : List Cell
  e : Nat → Nat
  row : Nat → Air.Row

/-- **The circuit's relation**: an accepted run of the statement's composed
    machine, within its heights, from literal bits and a well-formed
    region. -/
def CRel (s : CStmt) (w : CRun') : Prop :=
  s.R ≤ 20 ∧ s.Lm ≤ 20 ∧ BT.nleaves s.shp + s.W ≤ 2 ^ 8 ∧ w.region.length = s.W ∧
    (∀ i c, w.region[i]? = some c → cellOK (BT.nleaves s.shp + 3 + i) c = true) ∧
    AcceptsC w.A (cMachine w.ρ s.shp w.region s.Ps) (cHeap w.ρ s.shp w.region s.Ps).2
      (cHeap w.ρ s.shp w.region s.Ps).1.length s.Ps.length w.e w.row ∧
    w.A.length = 2 ^ s.Lm ∧ w.e (s.Ps.length - 1) < 2 ^ s.R

section
variable (s : CStmt) (w : CRun')

/-- The statement's machine, roots, bit count, and public tables. -/
abbrev CStmt.m : Mach := blankM s.shp s.W s.Ps
abbrev CStmt.roots : List Nat := blankRoots s.shp s.W s.Ps
abbrev CStmt.N : Nat := BT.nleaves s.shp
abbrev CStmt.Pg : Table := progTableC s.m.heap s.N s.W

/-- The honest tables of a run: `comp_honest_zk`'s. -/
abbrev hC : Table := cpuTableC w.A w.row w.e s.Ps.length s.roots (2 ^ s.R)
abbrev hWt : Table := witTable w.A s.N s.W
abbrev hMm : Table := memTableC w.A (cpuAirC s.m.hd s.m.stk s.m.heap.length s.roots.length s.m.stk)
  (progAirC s.m.heap s.N s.W) (witAir s.N s.W) (hC s w) s.Pg (hWt s w)

/-- The blinded tables, the published views and the public terminals. -/
def ctabs (t : Nat → Tup) : List (AirD × Table) :=
  compTables s.m.hd s.m.stk s.m.heap.length s.roots.length s.m.stk s.m.heap s.N s.W s.roots
    (((hC s w).setBlind BLA (t 1)).setBlind BLB (t 0)) ((hMm s w).setBlind 5 (t 0)) s.Pg
    ((hWt s w).setBlind WT_BLIND (t 1)) (segsPub s.roots)
def ctv (pre : String → EF) (β : EF) (t : Nat → Tup) : List EF :=
  compViewN pre β s.m.hd s.m.stk s.m.heap.length s.roots.length s.m.stk s.N s.W (hC s w) (hMm s w) (hWt s w) t
def cpb (pre : String → EF) (β : EF) : EF × EF :=
  (terminal pre β (progAirC s.m.heap s.N s.W) s.Pg, terminal pre β (segsAir s.roots) (segsPub s.roots))
def ctp (pre : String → EF) (β : EF) : EF :=
  (terminal pre β (progAirC s.m.heap s.N s.W) s.Pg).add (terminal pre β (segsAir s.roots) (segsPub s.roots))

/-- A table of a height, for counting messages. -/
def hTab (h : Nat) : Table := ⟨h, fun _ _ => 0, fun _ _ => 0⟩

/-- **The statement's message count**: the honest tables' LogUp messages,
    a function of the AIRs and the heights the statement fixes. -/
def cM : Nat :=
  (allEntries (compTables s.m.hd s.m.stk s.m.heap.length s.roots.length s.m.stk s.m.heap s.N s.W s.roots
    (hTab (2 ^ s.R)) (hTab (2 ^ s.Lm)) s.Pg (hTab (2 ^ 8)) (segsPub s.roots))).length
end

/-- **The honest tables' messages are the statement's count**, for every
    blinding: blinding keeps the heights, and the heights are the
    statement's. -/
theorem comp_entries {s : CStmt} {w : CRun'} (h : CRel s w) (t : Nat → Tup) :
    (allEntries (ctabs s w t)).length = cM s := by
  obtain ⟨_, _, hNW, _, _, _, hlen, _⟩ := h
  have hW : (hWt s w).h = 2 ^ 8 := witRows_len hNW
  have hM : (hMm s w).h = 2 ^ s.Lm := hlen
  unfold ctabs cM
  rw [allEntries_length, allEntries_length]
  simp only [compTables, List.map_cons, List.map_nil]
  rw [show (((hC s w).setBlind BLA (t 1)).setBlind BLB (t 0)).h = 2 ^ s.R from rfl,
    show ((hMm s w).setBlind 5 (t 0)).h = 2 ^ s.Lm from hM,
    show ((hWt s w).setBlind WT_BLIND (t 1)).h = 2 ^ 8 from hW]
  rfl

theorem assigns_ne : ∀ m, assigns m ≠ []
  | 0 => by simp [assigns]
  | m + 1 => by
    have ih := assigns_ne m
    cases h : assigns m with
    | nil => exact absurd h ih
    | cons t l =>
      unfold assigns
      rw [h]
      simp only [ne_eq, List.flatMap_eq_nil_iff, List.mem_range, List.map_cons, reduceCtorEq, imp_false]
      exact fun hx => hx 0 (by decide)

/-- **The generic draws are not empty**, given the PCS some randomness. -/
theorem tdraws_ne {NR m : Nat} (hNR : 0 < NR) : tdraws NR m ≠ [] := by
  have hg : genB (efOf P) = true := by decide
  have hP : P < Q4 := by decide
  obtain ⟨t, ht⟩ : ∃ t, t ∈ assigns m := by
    cases h : assigns m with
    | nil => exact absurd h (assigns_ne m)
    | cons t _ => exact ⟨t, List.mem_cons_self⟩
  intro he
  have hmem : (efOf 0, efOf P, 0, t) ∈ tdraws NR m := by
    unfold tdraws
    simp only [List.mem_flatMap, List.mem_range]
    refine ⟨0, by decide, P, hP, ?_⟩
    rw [if_pos hg]
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨0, hNR, t, ht, rfl⟩
  rw [he] at hmem
  exact List.not_mem_nil hmem

/-- **The composed circuit as a `PSD`.**  The relation is `CRel`; the
    draws are `tdraws NR 2`; the prover's proof is the real transcript of
    the run's honest tables under the PCS `pcs`, the simulator's `simVN`
    under `psim`.  The arguments are the STARK's, assumed: the verifier,
    the extractor, completeness, knowledge soundness, and the PCS's
    closeness within `ε`.  Zero knowledge is proved, within
    `M/P^4 + ε/NR` of all the draws, `M` the statement's message count. -/
def compPSD {PV : Type} (off : EF → String → EF) (NR ε : Nat) (hNR : 0 < NR)
    (pcs : CStmt → CRun' → (Nat → Tup) → EF → EF → Nat → PV) (psim : CStmt → EF → EF → List EF → Nat → PV)
    (hpcs : ∀ s w, CRel s w → PCSCloseN off NR (ctv s w) (pcs s w) (psim s) ε)
    (verify : CStmt → PV × EF × EF × List EF × (EF × EF) → Prop)
    (ext : CStmt → PV × EF × EF × List EF × (EF × EF) → CRun')
    (complete : ∀ s w, CRel s w → ∀ (d : EF × EF × Nat × (Nat → Tup)) π,
      realVN off (ctabs s w) (ctv s w) (cpb s) (pcs s w) d.1 d.2.1 d.2.2.1 d.2.2.2 = some π → verify s π)
    (knowledge : ∀ s π, verify s π → CRel s (ext s π)) :
    PSD CStmt CRun' CRel where
  Proof := PV × EF × EF × List EF × (EF × EF)
  Draw := EF × EF × Nat × (Nat → Tup)
  draws := tdraws NR 2
  prove s w d := realVN off (ctabs s w) (ctv s w) (cpb s) (pcs s w) d.1 d.2.1 d.2.2.1 d.2.2.2
  sim s d := simVN off (cpb s) chainBus (fun _ => false) chainPar 3 (ctp s) (psim s) d.1 d.2.1 d.2.2.1 d.2.2.2
  verify := verify
  ext := ext
  err s := Q4 * (NR * (Q4 ^ 2 * cM s)) + Q4 * (Q4 * (Q4 ^ 2 * ε))
  draws_ne := tdraws_ne hNR
  sim_some _ _ := by simp only [simVN, Option.isSome_some]
  complete := complete
  knowledge := knowledge
  zk s w h := by
    have h' := h
    obtain ⟨hR, hLm, hNW, hrl, hr, hA, hlen, hK⟩ := h'
    obtain ⟨hb, hu⟩ := comp_honest_zk hR hrl hr hA hlen hLm hK hNW
    refine closeD_of_transcriptG (V := Option (PV × EF × EF × List EF × (EF × EF))) (NR := NR) (m := 2)
      (real := fun α β r t => realVN off (ctabs s w) (ctv s w) (cpb s) (pcs s w) α β r t)
      (sim := fun α β r t => simVN off (cpb s) chainBus (fun _ => false) chainPar 3 (ctp s) (psim s) α β r t)
      fun E => ?_
    have key := transcript_zkG (PV := PV) (PB := EF × EF) (off := off) (NR := NR) (M := cM s) (ε := ε) (m := 2)
      (bus := chainBus) (sg := fun _ => false) (par := chainPar) (tabs := ctabs s w) (tv := ctv s w)
      (tp := ctp s) (pb := cpb s) (pcs := pcs s w) (psim := psim s) chainPar_ok
      (xu := fun pre β => chainBase ⟨terminal pre β (witAir s.N s.W) (hWt s w),
        terminal pre β (cpuAirC s.m.hd s.m.stk s.m.heap.length s.roots.length s.m.stk) (hC s w),
        terminal pre β memAirC (hMm s w)⟩)
      (fun pre β t => by
        show compViewN pre β _ _ _ _ _ _ _ _ _ _ t = _
        rw [chainBus_pre, chain_viewT, ← comp_chain pre β _ _ _ _ _ _ _ hu (t 1) (t 0)]; rfl)
      (fun pre β => by rw [chainBase_sum]; exact comp_sum pre β hb)
      (fun t => Nat.le_of_eq (comp_entries h t)) (hpcs s w h) E
    exact ⟨by rw [← Nat.add_assoc]; exact key.1, by rw [← Nat.add_assoc]; exact key.2⟩

end Circuit
