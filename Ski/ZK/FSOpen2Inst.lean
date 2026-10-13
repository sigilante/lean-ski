import Ski.ZK.FSOpenFri2

/-!
# The Sudoku proof over two Fiat–Shamir rounds, both commitments opened

`fs_open2` applied to the Sudoku proof.  The first commitment is of the
main groups' matrices (`mainF2`), the second of the permutation groups'
and the quotient tables' chunks with their codewords (`mainP2`,
`tabsPolys`, `tabsCws`).  The committed data must not read `ζ`, which the
second challenge draws after them: they are taken at `ζ = 0`, and the
PCS at any `ζ` agrees with the PCS at `0` on everything they read (the
groups' trace and mask points and sizes, the tables' shapes and query
points, the randomness's slices), and, where the proof does not abort,
on the chunk data (`sud_zeta`).
-/

namespace Circuit

open ZKF

theorem mpolysMulti_congr : ∀ (gs gs' : List MGroup) (tss : List (List (List F))) (rs : List F),
    gs.map (fun g => (g.T, g.R, g.n)) = gs'.map (fun g => (g.T, g.R, g.n)) →
    mpolysMulti gs tss rs = mpolysMulti gs' tss rs
  | [], [], _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _ => rfl
  | g :: gs, g' :: gs', ts :: tss, rs, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨eT, eR, en⟩, h2⟩ := h
    show mpolys g.T g.R g.n ts (rs.take (ts.length * g.n)) :: mpolysMulti gs tss (rs.drop (ts.length * g.n)) =
      mpolys g'.T g'.R g'.n ts (rs.take (ts.length * g'.n)) :: mpolysMulti gs' tss (rs.drop (ts.length * g'.n))
    rw [eT, eR, en, mpolysMulti_congr gs gs' tss _ h2]
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h

theorem traceCws_congr (ncw : Nat) : ∀ (gs gs' : List MGroup) (ct : List F), gs.map MGroup.dom = gs'.map MGroup.dom →
    traceCws ncw gs ct = traceCws ncw gs' ct
  | [], [], _, _ => rfl
  | g :: gs, g' :: gs', ct, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    show cwPolys g.dom g.dom.length ncw (ct.take (ncw * g.dom.length)) :: traceCws ncw gs (ct.drop (ncw * g.dom.length)) =
      cwPolys g'.dom g'.dom.length ncw (ct.take (ncw * g'.dom.length)) :: traceCws ncw gs' (ct.drop (ncw * g'.dom.length))
    rw [h.1, traceCws_congr ncw gs gs' _ h.2]
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

/-- Two PCS shapes the committed data cannot tell apart. -/
structure SameShape (qs qs' : List QGroup) (ks : List Nat) (tabs tabs' : List QTab) (ncw : Nat) : Prop where
  trn : (qs.map QGroup.ext).map (fun g => (g.T, g.R, g.n)) = (qs'.map QGroup.ext).map (fun g => (g.T, g.R, g.n))
  dom : (qs.map QGroup.ext).map MGroup.dom = (qs'.map QGroup.ext).map MGroup.dom
  S : qs.map (·.base.S) = qs'.map (·.base.S)
  shape : tabs.map tShape = tabs'.map tShape
  tS : tabs.map (·.S) = tabs'.map (·.S)
  iS : (tabsInfo ncw tabs).map (·.S) = (tabsInfo ncw tabs').map (·.S)

theorem SameShape.hn {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) : (qs.map QGroup.ext).map MGroup.n = (qs'.map QGroup.ext).map MGroup.n := by
  have := congrArg (List.map (fun x : List F × List F × Nat => x.2.2)) h.trn
  simp only [List.map_map] at this ⊢
  exact this

theorem SameShape.ht {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) :
    tabs.map (fun T => (T.tg.length, T.cs.length, T.h)) = tabs'.map (fun T => (T.tg.length, T.cs.length, T.h)) := by
  have := congrArg (List.map (fun x : Nat × List Chunk × List F × F × Nat => (x.2.2.2.2, x.2.1.length, x.1))) h.shape
  simp only [List.map_map] at this
  exact this

theorem SameShape.n1 {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) : friN1 qs ks tabs = friN1 qs' ks tabs' := by
  unfold friN1; rw [mtotal_congr _ _ ks h.hn, tabsCr_congr tabs tabs' h.ht]

theorem SameShape.n2 {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) : friN2 qs tabs ncw = friN2 qs' tabs' ncw := by
  unfold friN2; rw [traceCw_congr ncw _ _ h.dom, tabsCw_congr ncw tabs tabs' h.ht]

theorem SameShape.ms {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) (ρ : Nat) : msF qs ks tabs ncw ρ = msF qs' ks tabs' ncw ρ := by
  unfold msF; rw [h.n1, h.n2, mtotal_congr _ _ ks h.hn]

theorem SameShape.ct {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) (ρ : Nat) : ctF qs ks tabs ncw ρ = ctF qs' ks tabs' ncw ρ := by
  unfold ctF; rw [h.n1, h.n2, traceCw_congr ncw _ _ h.dom]

theorem SameShape.cr {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) (ρ : Nat) : crF qs ks tabs ncw ρ = crF qs' ks tabs' ncw ρ := by
  unfold crF; rw [h.n1, h.n2, mtotal_congr _ _ ks h.hn]

theorem SameShape.cc {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) (ρ : Nat) : ccF qs ks tabs ncw ρ = ccF qs' ks tabs' ncw ρ := by
  unfold ccF; rw [h.n1, h.n2, traceCw_congr ncw _ _ h.dom]

/-- **The committed data read the shape only.** -/
theorem SameShape.dataF2 {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) (cols : (Nat → Tup) → EF → EF → List (List (List F))) (mk : List Nat)
    (t : Nat → Tup) (ρ : Nat) : mainF2 qs ks cols tabs ncw mk t ρ = mainF2 qs' ks cols tabs' ncw mk t ρ := by
  unfold mainF2; rw [h.ms, h.ct, mpolysMulti_congr _ _ _ _ h.trn, traceCws_congr ncw _ _ _ h.dom]

theorem SameShape.dataP2 {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameShape qs qs' ks tabs tabs' ncw) (cols : (Nat → Tup) → EF → EF → List (List (List F))) (mk : List Nat)
    (t : Nat → Tup) (α β : EF) (ρ : Nat) :
    mainP2 qs ks cols tabs ncw mk t α β ρ = mainP2 qs' ks cols tabs' ncw mk t α β ρ := by
  unfold mainP2; rw [h.ms, h.ct, mpolysMulti_congr _ _ _ _ h.trn, traceCws_congr ncw _ _ _ h.dom]

section
open B Air Stmt Mach Sudoku SudokuText

set_option maxRecDepth 100000 in
/-- **The Sudoku PCS's shape does not depend on `ζ`.** -/
theorem sud_same (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (tp : Nat)
    (S16 S10 SP : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) (ncw : Nat) :
    SameShape (sudGroups tp S16 S10 SP ζ qv) (sudGroups tp S16 S10 SP ζ' qv) (sudKs hd0 stk0 ctr0 heap)
      ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst)
      ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ' qv wm wc ww wp).map Prod.fst) ncw where
  trn := rfl
  dom := rfl
  S := rfl
  shape := by simp only [sudTs, bbTab, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
  tS := by simp only [sudTs, bbTab, airQTabG, List.map_cons, List.map_nil]
  iS := by simp only [sudTs, bbTab, airQTabG, tabsInfo, tInfo, List.map_cons, List.map_nil, List.map_append,
    List.map_replicate]

set_option maxRecDepth 100000 in
/-- **Without an abort, the Sudoku chunk data do not depend on `ζ`.** -/
theorem sud_data_zeta (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (tp : Nat)
    (S16 S10 SP : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) (t : Nat → Tup) (α β : EF) (ms : List F)
    (h : Aborts (prefixOf α (off β)) β (sudTabs hd0 stk0 ctr0 heap C Mm Wt t) = false) :
    (sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map (fun p => p.2 t α β ms) =
      (sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ' qv wm wc ww wp).map (fun p => p.2 t α β ms) := by
  have hg : ∀ tss rs, mpolysMulti ((sudGroups tp S16 S10 SP ζ qv).map QGroup.ext) tss rs =
      mpolysMulti ((sudGroups tp S16 S10 SP ζ' qv).map QGroup.ext) tss rs := fun tss rs =>
    mpolysMulti_congr _ _ _ _ rfl
  simp only [sudTs, bbData, List.map_cons, List.map_nil, h, if_true, hg]
end

section
open B Air Stmt Mach Sudoku SudokuText

set_option maxRecDepth 100000 in
/-- **The Sudoku proof over two Fiat–Shamir rounds, both commitments
    opened**, in the programmable random-oracle model: the first
    commitment of the main groups' matrices, the second of the
    permutation groups' and the quotient chunks' with their codewords,
    each opened beside the view; the simulator commits and opens
    interpolants through its own view's openings and programs both
    tables (`fs_open2`).  Assumed: each commitment hides alone and given
    its openings, perfectly (the second at any opened point lists);
    generic `β` and `ζ`; the folding challenge's round merged; the FRI
    challenge and the query points fixed; one proof per oracle. -/
theorem sud_fs_open2 {V Wv P1 P2 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    {S16 S10 SP : List F} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F))
    (hS16 : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz16 : 2 * S16.length + 8 ≤ 2 ^ 16) (hsz : 2 * S10.length + 8 ≤ 2 ^ 10)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hncw : 4 ≤ ncw) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS1 NS2 n1 n2 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ComPfHides NS1 Com1 Pf1 (opF ((sudGroups tP S16 S10 SP EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) × List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf2 : List (List (List F)) × List (List (List (List F))) × List (List (List F)) → Nat → P2)
    (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ SsT SsC, ComPfHides NS2 Com2 Pf2 (op2F ((sudGroups tP S16 S10 SP EF.zero qv).map (·.base.S)) [1, 3, 5, 7] SsT SsC))
    (hr2 : ∀ d σ, Com2 d σ < n2)
    (d2 : List (List (List F)) × List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Option P1 × Option P2 × TViewN (SudPV (V × Wv)) EF → Bool) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP EF.zero qv wm wc ww wp ncw
    let pcsZ := fun (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ
      qv wm wc ww wp ncw αb (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psimZ := fun (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP
      ζ qv wm wc ww wp ncw αb (friX fri Rb Ro (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP S16 S10 SP EF.zero qv
    let Ss0 := q0.map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv
      wm wc ww wp).map Prod.fst
    let qdZ := fun (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) => (sudTs off blank.hd blank.stk blank.heap.length
      blank.heap C Mm Wt tP S16 S10 SP ζ qv wm wc ww wp).map (fun p => p.2 t α β ms)
    let SsT0 := (tqZ EF.zero).map (·.S)
    let SsC0 := (tabsInfo ncw (tqZ EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      (mainP2 q0 ks cols (tqZ EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0),
       tabsPolys (tqZ EF.zero) (qdZ EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (msF q0 ks (tqZ EF.zero) ncw (r % NR0)))
         (crF q0 ks (tqZ EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ EF.zero) (ccF q0 ks (tqZ EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let qZ := fun (ζ : EF) => sudGroups tP S16 S10 SP ζ qv
    let sop1 := fun (c2 r : Nat) (_ : Nat → Tup) => opF Ss0 mk1 (mainZ2 (qZ (efOf c2)) ks (tqZ (efOf c2)) ncw mk1 (r % NR0))
    let sop2 := fun (c2 c1 r : Nat) (t : Nat → Tup) => op2F Ss0 mk2 SsT0 SsC0
      (mainZ2 (qZ (efOf c2)) ks (tqZ (efOf c2)) ncw mk2 (r % NR0),
       tabsPolys (tqZ (efOf c2)) (canonT (tqZ (efOf c2)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ (efOf c2)).map QGroup.ext) ((((qZ (efOf c2)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F)))) (msF (qZ (efOf c2)) ks (tqZ (efOf c2)) ncw (r % NR0))))
         (crF (qZ (efOf c2)) ks (tqZ (efOf c2)) ncw (r % NR0)),
       tabsCws ncw (tqZ (efOf c2)) (ccF (qZ (efOf c2)) ks (tqZ (efOf c2)) ncw (r % NR0)))
    let ov1 : TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss0 mk1 pv)
      | none => none
    let ov2 : TViewN (SudPV (V × Wv)) EF →
        Option (List (List (List F)) × List (List (List (List F))) × List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ov2F Ss0 mk2 8 pv)
      | none => none
    let rvF := fun (c2 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) => realVN off tabs tv tp (pcsZ (efOf c2)) α β r t
    let svF := fun (c2 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ (efOf c2)) α β r t
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ2, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      Com1 (main1 x.2.2.2 x.2.2.1) x.1 + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rvF c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
       (ov2 (rvF c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => Pf2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1),
       rvF c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 ((sdF Ss0 mk1) (sop1 c2 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 x + n1 * Com2 ((sd2F Ss0 mk2 SsT0 SsC0) (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 ((sdF Ss0 mk1) (sop1 c2 x.2.2.1 x.2.2.2)) x.1), some (Pf2 ((sd2F Ss0 mk2 SsT0 SsC0) (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1),
        svF c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 : Nat) => genB (efOf (c1 % Q4)) && (fun c2 => genB (efOf c2)) c2
    (Q4 * Q4) * (Q4 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (Q4 ^ (n1 * n2)) (fun H2 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget Q4 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget Q4 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (Q4 ^ (n1 * n2)) (fun H2 => sumTo (Q4 * Q4) (fun c1 => sumTo Q4 (fun c2 =>
      sm (fun x => indB (gd c1 c2 && E (rset (Q4 * Q4) (s1 c1 c2 x) H1 c1) (rset Q4 (s2 c1 c2 x) H2 c2)
        (s1 c1 c2 x) (s2 c1 c2 x) (svo c1 c2 x))))))) +
      (Q4 * Q4) ^ n1 * (Q4 ^ (n1 * n2) * (Q4 * (NS1 * (NS2 * ((Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))))) := by
  intro blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv tp M q0 Ss0 ks cols tqZ qdZ SsT0 SsC0 mk1 mk2 main1 main2 vS qZ sop1 sop2 ov1 ov2 rvF svF
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sms, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨hP23, hPg⟩ := sud_prog_height hc hA hlen
  rw [← htp] at hP23 hPg
  have hb : ∀ c2, genB (efOf c2) = true →
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (realVN off tabs tv tp (pcsZ (efOf c2)) α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (simVN off tp chainBus (fun _ => false) chainPar 3 tp
            (psimZ (efOf c2)) α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (simVN off tp chainBus (fun _ => false) chainPar 3 tp
            (psimZ (efOf c2)) α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (realVN off tabs tv tp (pcsZ (efOf c2)) α β r t))) +
            Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c2 hg => by
    have hgz := (genB_iff _).1 hg
    have hpcs := sud_pcsX (heap := blank.heap) (ζ := efOf c2) off sc sms sw (rfl : C.h = 2 ^ 16) hlen
      (rfl : Wt.h = 2 ^ 10) (by omega) hPg qv wm wc ww wp hS16 hS10 hSP hsz16 hsz hszP (generic_ofF_ne hgz)
      (mz_generic hgz) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
    rw [sudNR_zeta off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c2) EF.zero qv
      wm wc ww wp ncw] at hpcs
    exact ⟨fun E' => (sud_transcriptG off NR 0 (pcsZ (efOf c2)) (psimZ (efOf c2)) hbal hun hpcs E').1,
      fun E' => (sud_transcriptG off NR 0 (pcsZ (efOf c2)) (psimZ (efOf c2)) hbal hun hpcs E').2⟩
  have hS := fun c2 => sud_same off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c2)
    EF.zero qv wm wc ww wp ncw
  have hlen8 : ∀ (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun ζ t α β => by
      rw [(sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg
          S16 S10 SP ζ qv t α β).2,
        (sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg
          S16 S10 SP ζ qv t EF.zero EF.zero).2]
  have hmk1 : ∀ k ∈ mk1, k < 8 ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk1, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 8 := by rcases hk' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, sudCols_main off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2 : ∀ k ∈ mk2, k < 8 ∧ ∀ t α β, k < (cols t α β).length := by
    intro k hk
    simp only [mk2, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hkn : k < 8 := by rcases hk with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun _ _ _ => hkn⟩
  have hvo1 : ∀ c2 c r t, rvF c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rvF c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF Ss0 mk1 (main1 t r)) := by
    intro c2 c r t
    show realVN off tabs tv tp (pcsZ (efOf c2)) _ _ r t = none ∨ ov1 (realVN off tabs tv tp (pcsZ (efOf c2)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP S16 S10 SP (efOf c2) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c2) qv wm wc ww wp).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c2) qv wm wc ww wp).map fun p => p.2 t α β ms) ncw αb (friX fri Rb Ro (r / NR0)) mk1 hmk1
        (hlen8 (efOf c2)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hS c2).dataF2 cols mk1 t (r % NR0), (hS c2).S] at e
      exact .inr (congrArg some e)
  have hvo2 : ∀ c2 c r t, rvF c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rvF c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2F Ss0 mk2 SsT0 SsC0 (main2 c t r)) := by
    intro c2 c r t
    show realVN off tabs tv tp (pcsZ (efOf c2)) _ _ r t = none ∨ ov2 (realVN off tabs tv tp (pcsZ (efOf c2)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab' : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t)
        · rfl
        · exact absurd h hab
      have e := pcsFri_ovR2 off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP S16 S10 SP (efOf c2) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c2) qv wm wc ww wp).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c2) qv wm wc ww wp).map fun p => p.2 t α β ms) ncw αb (friX fri Rb Ro (r / NR0)) mk2 hmk2 rfl t
        (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hS c2).S, (hS c2).tS, (hS c2).iS, (hS c2).dataP2 cols mk2 t _ _ (r % NR0),
        tabsPolys_congr _ _ _ _ (hS c2).shape, tabsCws_congr ncw _ _ _ (hS c2).shape, (hS c2).cr (r % NR0),
        (hS c2).cc (r % NR0), (hS c2).ms (r % NR0),
        sud_data_zeta off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c2) EF.zero
          qv wm wc ww wp t _ _ _ hab'] at e
      exact .inr (congrArg some e)
  have hsvo1 : ∀ c2 c r t, ov1 (svF c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 r t) := fun c2 c r t =>
    congrArg some (psimFri_ov2 (qZ (efOf c2)) ks (tqZ (efOf c2)) ncw αb _ mk1 (fun k hk => (hmk1 k hk).1) rfl _ _ _
      (r % NR0))
  have hsvo2 : ∀ c2 c r t, ov2 (svF c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c r t) := by
    intro c2 c r t
    have e := psimFri_ovR2 (sudGroups tP S16 S10 SP (efOf c2) qv) ks ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c2) qv wm wc ww wp).map Prod.fst) ncw αb (friX fri Rb Ro (r / NR0)) mk2 (fun k hk => (hmk2 k hk).1) rfl
      (efOf (c / Q4)) (efOf (c % Q4)) (vS (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0)
    rw [(hS c2).S, (hS c2).tS, (hS c2).iS] at e
    exact congrArg some e
  have hsd1 : ∀ t r, opF Ss0 mk1 (sdF Ss0 mk1 (opF Ss0 mk1 (main1 t r))) = opF Ss0 mk1 (main1 t r) :=
    fun t r => opF_sdF _ _ _
  have hsd2 : ∀ c t r, op2F Ss0 mk2 SsT0 SsC0 (sd2F Ss0 mk2 SsT0 SsC0 (op2F Ss0 mk2 SsT0 SsC0 (main2 c t r))) =
      op2F Ss0 mk2 SsT0 SsC0 (main2 c t r) := fun c t r => op2_sd2 _ _ _ _ _ _ _
  exact fs_open2 Q4_pos rvF svF (fun c2 => genB (efOf c2)) (fun c2 α β r t => realVN_cases _ _ _ _ _ α β r t)
    (fun c2 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) (fun c2 hg => (hb c2 hg).1) (fun c2 hg => (hb c2 hg).2)
    Com1 Pf1 (opF Ss0 mk1) (sdF Ss0 mk1) d1 hc1 hp1 hr1 ov1 rfl main1 hsd1
    Com2 Pf2 (op2F Ss0 mk2 SsT0 SsC0) (sd2F Ss0 mk2 SsT0 SsC0) d2 hc2 (hp2 _ _) hr2 ov2 rfl main2 hsd2
    hvo1 hvo2 sop1 sop2 hsvo1 hsvo2 E
end

end Circuit
