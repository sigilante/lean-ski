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

end Circuit
