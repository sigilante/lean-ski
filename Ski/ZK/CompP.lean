import Ski.ZK.CompJ
import Ski.Circuit.CompPFinal

/-!
# Zero knowledge of the composed circuit with the Poseidon2 jet

**`compP_transcript`**: the transcript of a proof of the circuit with the
Poseidon2 jet is simulatable, over a hiding PCS: `transcript_zkN` for the
tree of six private tables and five blinding tuples that `compPAirs` and
`bench/plonky3/src/compp.rs` blind,

    WIT —a— CPU —b— MEM,   CPU —c— P2IN —d— P2OUT —e— P2,

in the tree's order memory, CPU, witness, P2IN, P2OUT, P2: the composed
circuit with jets' tree (`jetPar`, `jetBus`, `jetSg`) cut to its first
six vertices.  The program, segment and level tables are public, their
terminals the simulator's `tp`.  The level table's multiplicities count the
jet's calls (`idxPub`), so the call count is public.  For `p2pre h` and
`p2commit c pat` it is one: every accepted table has exactly one jet row
(`Circuit.p2pre_once`, `Circuit.p2commit_once`), and ski-air refuses to
prove a run with any other count.

The prover's tables must balance with the public tables and carry clear
blinding flags (`UnblindedCP`).  The honest prover's tables do
(`P2Run.honest_zkP`, `Ski/ZK/CompPHonest.lean`): built from an accepted
run, they balance with the public program, segment and level tables, the
level table's multiplicities those of the run's calls, and their flags
are clear; for `p2pre h` and `p2commit c pat` the run makes one call, so
the level table is `idxPub 1` (`P2Run.honest_zk_p2pre`,
`P2Run.honest_zk_p2commit`).  That
they satisfy each AIR's constraints (`Sat`) is not proved.
-/

namespace Circuit

open ZKF B Air Compose CompM

-- ---------------------------------------------------------------------------
-- The tree
-- ---------------------------------------------------------------------------

/-- **The tree's view, unfolded**, for six vertices. -/
theorem viewT_p2 (β : EF) (pre : String → EF) (x : Nat → EF) (t : Nat → Tup) :
    viewT β (fun k => pre (jetBus k)) jetSg jetPar 6 x t =
      [(x 0).sub (blindTerm β (pre "blind_b") (t 0)),
       (((x 1).sub (EF.zero.sub (blindTerm β (pre "blind_c") (t 2)))).sub (blindTerm β (pre "blind_a") (t 1))).add
         (blindTerm β (pre "blind_b") (t 0)),
       (x 2).add (blindTerm β (pre "blind_a") (t 1)),
       ((x 3).sub (EF.zero.sub (blindTerm β (pre "blind_d") (t 3)))).add
         (EF.zero.sub (blindTerm β (pre "blind_c") (t 2))),
       ((x 4).sub (EF.zero.sub (blindTerm β (pre "blind_e") (t 4)))).add
         (EF.zero.sub (blindTerm β (pre "blind_d") (t 3))),
       (x 5).add (EF.zero.sub (blindTerm β (pre "blind_e") (t 4)))] :=
  rfl

-- ---------------------------------------------------------------------------
-- The public level table
-- ---------------------------------------------------------------------------

/-- **The level table with the honest multiplicities** for `calls` jet
    calls: each level twice per call (P2IN's lookup and P2OUT's), on its
    row; the padding rows, copies of level `0`, none. -/
def idxPub (calls : Nat) : Table :=
  ⟨idxRows.length, fun q _ => if q < P2_BITS then ofN (2 * calls) else 0, fun q j => (idxRows.getD q []).getD j 0⟩

-- ---------------------------------------------------------------------------
-- The published terminals
-- ---------------------------------------------------------------------------

/-- **The six private tables before blinding**: each has a row, and its
    blinding flags are clear (the jet tables' columns past the base AIRs'
    widths, the CPU's at `BLA`, `BLB` and `P2SEL + 1`, the memory's at `5`,
    the witness table's at `WT_BLIND`). -/
structure UnblindedCP (C Mm Wt Pi Po Pp : Table) : Prop where
  hc : 0 < C.h
  hm : 0 < Mm.h
  hw : 0 < Wt.h
  hpi : 0 < Pi.h
  hpo : 0 < Po.h
  hp2 : 0 < Pp.h
  za : ∀ r, r < C.h → C.main r (BLA + 4) = 0
  zb : ∀ r, r < C.h → C.main r (BLB + 4) = 0
  zc : ∀ r, r < C.h → C.main r (P2SEL + 1 + 4) = 0
  zm : ∀ r, r < Mm.h → Mm.main r (5 + 4) = 0
  zw : ∀ r, r < Wt.h → Wt.main r (WT_BLIND + 4) = 0
  wpi : Wide p2inAir Pi
  wpo : Wide p2outAir Po
  wp2 : Wide P2Air.p2Air Pp

/-- The unblinded private terminals, in the tree's order. -/
def cpBase (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA J root N W : Nat) (C Mm Wt Pi Po Pp : Table) :
    Nat → EF
  | 0 => terminal pre β memAirC Mm
  | 1 => terminal pre β (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C
  | 2 => terminal pre β (witAirP N W) Wt
  | 3 => terminal pre β p2inAirB Pi
  | 4 => terminal pre β p2outAirB Po
  | _ => terminal pre β p2AirB Pp

/-- **What a proof of the circuit with the Poseidon2 jet publishes of its
    witness**: the blinded private tables' terminals, in the tree's order;
    `t k` is edge `k`'s tuple (`compp.rs`'s `bb, ba, tc, td, te`). -/
def compPViewN (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA J root N W : Nat) (C Mm Wt Pi Po Pp : Table)
    (t : Nat → Tup) : List EF :=
  [terminal pre β memAirC (Mm.setBlind 5 (t 0)),
   terminal pre β (cpuAirP2 hd0 stk0 ctr0 n nilA J root)
     (((C.setBlind BLA (t 1)).setBlind BLB (t 0)).setBlind (P2SEL + 1) (t 2)),
   terminal pre β (witAirP N W) (Wt.setBlind WT_BLIND (t 1)),
   terminal pre β p2inAirB ((Pi.setBlind p2inAir.width (t 2)).setBlind (p2inAir.width + 5) (t 3)),
   terminal pre β p2outAirB ((Po.setBlind p2outAir.width (t 3)).setBlind (p2outAir.width + 5) (t 4)),
   terminal pre β p2AirB (Pp.setBlind P2Air.p2Air.width (t 4))]

/-- The CPU's messages but its blinding ones. -/
theorem cpuP2_inters (hd0 stk0 ctr0 n nilA J root : Nat) : (cpuAirP2 hd0 stk0 ctr0 n nilA J root).inters =
    cpuIntersP2.take 16 ++ blindInter "blind_c" (P2SEL + 1) false ::
      [blindInter "blind_a" BLA true, blindInter "blind_b" BLB false] := rfl

/-- **The CPU's blinded terminal.** -/
theorem terminal_cpuP2 (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA J root : Nat) {C : Table} (hh : 0 < C.h)
    (za : ∀ r, r < C.h → C.main r (BLA + 4) = 0) (zb : ∀ r, r < C.h → C.main r (BLB + 4) = 0)
    (zc : ∀ r, r < C.h → C.main r (P2SEL + 1 + 4) = 0) (a b c : Tup) :
    terminal pre β (cpuAirP2 hd0 stk0 ctr0 n nilA J root) (((C.setBlind BLA a).setBlind BLB b).setBlind (P2SEL + 1) c) =
      (((terminal pre β (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C).sub (blindTerm β (pre "blind_a") a)).add
        (blindTerm β (pre "blind_b") b)).add (blindTerm β (pre "blind_c") c) := by
  have hA : ∀ I ∈ cpuIntersP2.take 16, I.avoids BLA = true := all_mem (by decide)
  have hB : ∀ I ∈ cpuIntersP2.take 16, I.avoids BLB = true := all_mem (by decide)
  have hC : ∀ I ∈ cpuIntersP2.take 16, I.avoids (P2SEL + 1) = true := all_mem (by decide)
  have iA : (cpuAirP2 hd0 stk0 ctr0 n nilA J root).inters =
      (cpuIntersP2.take 16 ++ [blindInter "blind_c" (P2SEL + 1) false]) ++ blindInter "blind_a" BLA true ::
        [blindInter "blind_b" BLB false] := rfl
  have eA := terminal_setBlind pre β iA
    (fun I hI => by
      rcases List.mem_append.1 hI with hI | hI
      · exact hA I hI
      · exact all_mem (l := [blindInter "blind_c" (P2SEL + 1) false]) (by decide) I hI)
    (all_mem (l := [blindInter "blind_b" BLB false]) (by decide)) C hh za a
  have iB : (cpuAirP2 hd0 stk0 ctr0 n nilA J root).inters =
      (cpuIntersP2.take 16 ++ [blindInter "blind_c" (P2SEL + 1) false, blindInter "blind_a" BLA true]) ++
        blindInter "blind_b" BLB false :: [] := rfl
  have eB := terminal_setBlind pre β iB
    (fun I hI => by
      rcases List.mem_append.1 hI with hI | hI
      · exact hB I hI
      · exact all_mem (l := [blindInter "blind_c" (P2SEL + 1) false, blindInter "blind_a" BLA true]) (by decide) I hI)
    (fun I hI => absurd hI List.not_mem_nil) (C.setBlind BLA a) hh
    (fun r hr => by rw [setBlind_other a (by decide)]; exact zb r hr) b
  have eC := terminal_setBlind pre β (cpuP2_inters hd0 stk0 ctr0 n nilA J root) hC
    (all_mem (l := [blindInter "blind_a" BLA true, blindInter "blind_b" BLB false]) (by decide))
    ((C.setBlind BLA a).setBlind BLB b) hh
    (fun r hr => by rw [setBlind_other b (by decide), setBlind_other a (by decide)]; exact zc r hr) c
  rw [eC, eB, eA, ofF_neg_mul, ofF_one_mul, ofF_one_mul]

/-- The Poseidon2 table's messages avoid its blinding block. -/
theorem p2_avoids : ∀ I ∈ P2Air.p2Air.inters, I.avoids P2Air.p2Air.width = true := by
  rw [p2Air_inters]
  intro I hI
  rcases List.mem_append.1 hI with hI | hI <;> obtain ⟨e, he, rfl⟩ := List.mem_map.1 hI
  · have he' := List.mem_range.1 he
    show Inter.avoids 652 _ = true
    unfold Inter.avoids
    simp only [E.onlyAtoms, List.all_cons, List.all_nil, Bool.and_true, B.col, B.c, avoid]
    simp only [show ¬ (652 ≤ P2Air.ACT) from by decide, show ¬ (652 ≤ P2Air.KEY) from by decide,
      show ¬ (652 ≤ e) from by omega, decide_false, Bool.false_and, Bool.not_false, Bool.and_self]
  · have he' := List.mem_range.1 he
    have hout : P2Air.p2Out.getD e (B.c 0) = col (634 + e) := by
      rw [show P2Air.p2Out = P2Air.colsFrom 634 from rfl]
      exact getD_map_range (fun i => col (634 + i)) _ he'
    show Inter.avoids 652 _ = true
    unfold Inter.avoids
    simp only [hout]
    simp only [E.onlyAtoms, List.all_cons, List.all_nil, Bool.and_true, B.col, B.c, avoid]
    simp only [show ¬ (652 ≤ P2Air.ACT) from by decide, show ¬ (652 ≤ P2Air.KEY) from by decide,
      show ¬ (652 ≤ e) from by omega, show ¬ (652 ≤ 634 + e) from by omega, decide_false, Bool.false_and,
      Bool.not_false, Bool.and_self]

/-- **The published terminals are the tree's view** of the unblinded ones. -/
theorem compP_chain (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA J root N W : Nat) {C Mm Wt Pi Po Pp : Table}
    (h : UnblindedCP C Mm Wt Pi Po Pp) (t : Nat → Tup) :
    compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t =
      viewT β (fun k => pre (jetBus k)) jetSg jetPar 6
        (cpBase pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp) t := by
  rw [viewT_p2]
  have e0 : terminal pre β memAirC (Mm.setBlind 5 (t 0)) =
      (terminal pre β memAirC Mm).sub (blindTerm β (pre "blind_b") (t 0)) := by
    rw [terminal_setBlind pre β (L1 := [⟨"mem", 0, .neg (col 4), [col 0, col 1, col 2, col 3]⟩]) (L2 := [])
      (bus := "blind_b") (c := 5) (neg := true) rfl (all_mem (l := [_]) (by decide))
      (fun I hI => absurd hI List.not_mem_nil) Mm h.hm h.zm (t 0), ofF_neg_mul]
  have e2 : terminal pre β (witAirP N W) (Wt.setBlind WT_BLIND (t 1)) =
      (terminal pre β (witAirP N W) Wt).add (blindTerm β (pre "blind_a") (t 1)) := by
    rw [terminal_setBlind pre β (L1 := [witInters.head (by decide)]) (L2 := []) (bus := "blind_a") (c := WT_BLIND)
      (neg := false) rfl (all_mem (l := [_]) (by decide)) (fun I hI => absurd hI List.not_mem_nil) Wt h.hw h.zw
      (t 1), ofF_one_mul]
  have e1 := terminal_cpuP2 pre β hd0 stk0 ctr0 n nilA J root h.hc h.za h.zb h.zc (t 1) (t 0) (t 2)
  have e3 : terminal pre β p2inAirB ((Pi.setBlind p2inAir.width (t 2)).setBlind (p2inAir.width + 5) (t 3)) = _ :=
    terminal_wb2 pre β (A := p2inAir) (b1 := "blind_c") (b2 := "blind_d")
      (fun I hI => ⟨all_mem (l := p2inAir.inters) (by decide) I hI, all_mem (l := p2inAir.inters) (by decide) I hI⟩)
      h.hpi h.wpi (t 2) (t 3)
  have e4 : terminal pre β p2outAirB ((Po.setBlind p2outAir.width (t 3)).setBlind (p2outAir.width + 5) (t 4)) = _ :=
    terminal_wb2 pre β (A := p2outAir) (b1 := "blind_d") (b2 := "blind_e")
      (fun I hI => ⟨all_mem (l := p2outAir.inters) (by decide) I hI, all_mem (l := p2outAir.inters) (by decide) I hI⟩)
      h.hpo h.wpo (t 3) (t 4)
  have e5 : terminal pre β p2AirB (Pp.setBlind P2Air.p2Air.width (t 4)) = _ :=
    terminal_wb1 pre β (A := P2Air.p2Air) (b1 := "blind_e") p2_avoids h.hp2 h.wp2 (t 4)
  unfold compPViewN
  rw [e0, e1, e2, e3, e4, e5]
  simp only [List.cons.injEq, and_true]
  refine ⟨rfl, ef_cpu _ _ _ _, rfl, ef_mid _ _ _, ef_mid _ _ _, ef_last _ _⟩

/-- **The unblinded private terminals sum to minus the public ones'**, by
    LogUp's completeness over balanced tables. -/
theorem compP_sum (pre : String → EF) (β : EF) {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell} {N W : Nat}
    {roots : List Nat} {C Mm Pg Wt Sg Pi Po Pp Px : Table}
    (hb : Balanced (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px)) :
    sumL (cpBase pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp) (List.range 6) =
      EF.zero.sub (((terminal pre β (progAirC heap N W) Pg).add (terminal pre β (segsAir roots) Sg)).add
        (terminal pre β p2idxAir Px)) := by
  have hl := logup_sum pre β _ hb
  let c := terminal pre β (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C
  let m := terminal pre β memAirC Mm
  let pg := terminal pre β (progAirC heap N W) Pg
  let w := terminal pre β (witAirP N W) Wt
  let sg := terminal pre β (segsAir roots) Sg
  let ti := terminal pre β p2inAirB Pi
  let to := terminal pre β p2outAirB Po
  let tq := terminal pre β p2AirB Pp
  let tx := terminal pre β p2idxAir Px
  have hl' : c.add (m.add (pg.add (w.add (sg.add (ti.add (to.add (tq.add (tx.add EF.zero)))))))) = EF.zero := hl
  have e : sumL (cpBase pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp) (List.range 6) =
      (c.add (m.add (pg.add (w.add (sg.add (ti.add (to.add (tq.add (tx.add EF.zero))))))))).sub
        ((pg.add sg).add tx) := by
    show m.add (c.add (w.add (ti.add (to.add (tq.add EF.zero))))) = _
    let O : Q := ⟨k 0, k 0, k 0, k 0⟩
    exact Q.eq_of_norm
      (p := (Q.var 1).add ((Q.var 0).add ((Q.var 3).add ((Q.var 5).add ((Q.var 6).add ((Q.var 7).add O))))))
      (q := ((Q.var 0).add ((Q.var 1).add ((Q.var 2).add ((Q.var 3).add ((Q.var 4).add ((Q.var 5).add
        ((Q.var 6).add ((Q.var 7).add ((Q.var 8).add O))))))))).sub (((Q.var 2).add (Q.var 4)).add (Q.var 8)))
      (by decide) (env10 c m pg w sg ti to tq tx EF.zero)
  rw [e, hl']

-- ---------------------------------------------------------------------------
-- The transcript
-- ---------------------------------------------------------------------------

/-- **The transcript of a proof of the circuit with the Poseidon2 jet is
    simulatable**, over a hiding PCS: `transcript_zkN` for the tree of six
    private tables and five tuples (`compP_chain`).  The prover's tables
    balance with the public program, segment and level tables (the level
    table's multiplicities those of `calls` jet calls) and carry clear
    blinding flags before it blinds them with the edges' tuples `t`; so the
    simulator's `tp` and `pb`, the public tables' terminals, are public.
    Given at most `M` LogUp messages and a PCS whose view is within `ε` of a
    simulator's (`PCSCloseN`), the simulated transcript matches the real one
    on every event `E`, up to the non-generic challenges, the aborts and the
    PCS, over the `Q4 · Q4 · NR · Q4^5` draws. -/
theorem compP_transcript {PV : Type} (off : EF → String → EF) (NR ε calls : Nat)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
    {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
    {C Mm Wt Pi Po Pp : Table}
    (hb : Balanced (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm (progTableC heap N W) Wt
      (segsPub roots) Pi Po Pp (idxPub calls)))
    (h : UnblindedCP C Mm Wt Pi Po Pp)
    (hpcs : PCSCloseN off NR (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t)
      pcs psim ε)
    (E : TViewN PV ((EF × EF) × EF) → Bool) :
    let tabs := fun t : Nat → Tup => compPTables hd0 stk0 ctr0 n nilA J root heap N W roots
      (((C.setBlind BLA (t 1)).setBlind BLB (t 0)).setBlind (P2SEL + 1) (t 2)) (Mm.setBlind 5 (t 0))
      (progTableC heap N W) (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
      ((Pi.setBlind p2inAir.width (t 2)).setBlind (p2inAir.width + 5) (t 3))
      ((Po.setBlind p2outAir.width (t 3)).setBlind (p2outAir.width + 5) (t 4))
      (Pp.setBlind P2Air.p2Air.width (t 4)) (idxPub calls)
    let tv := fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t
    let pb := fun pre β => ((terminal pre β (progAirC heap N W) (progTableC heap N W),
      terminal pre β (segsAir roots) (segsPub roots)), terminal pre β p2idxAir (idxPub calls))
    let tp := fun pre β => ((terminal pre β (progAirC heap N W) (progTableC heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))).add (terminal pre β p2idxAir (idxPub calls))
    let M := (allEntries (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm (progTableC heap N W)
      Wt (segsPub roots) Pi Po Pp (idxPub calls))).length
    tsumN NR 5 (fun α β r t => indB (E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR 5 (fun α β r t => indB (E (simVN off pb jetBus jetSg jetPar 6 tp psim α β r t))) +
        Q4 * (NR * Q4 ^ 5 * (P * P)) + Q4 * (NR * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * ε)) ∧
    tsumN NR 5 (fun α β r t => indB (E (simVN off pb jetBus jetSg jetPar 6 tp psim α β r t))) ≤
      tsumN NR 5 (fun α β r t => indB (E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * Q4 ^ 5 * (P * P)) + Q4 * (NR * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * ε)) :=
  transcript_zkN (m := 5) jetPar_ok
    (xu := fun pre β => cpBase pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp)
    (fun pre β t => compP_chain pre β hd0 stk0 ctr0 n nilA J root N W h t)
    (fun pre β => compP_sum pre β hb)
    (fun t => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

end Circuit
