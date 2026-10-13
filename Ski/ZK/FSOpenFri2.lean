import Ski.ZK.FSOpen2

/-!
# The second commitment's openings: permutation groups and quotient chunks

The second commitment holds the data computed after the LogUp
challenges: the permutation groups' masked columns with their random
codewords, and each quotient table's chunk polynomials with theirs.  The
view opens every column's chunk polynomials at the table's query points
and `ζ` (`tabsView`); here the chunk polynomials are named (`csPolys`,
`tabsPolys`) and the view's openings at the query points shown to be
their values there (`tabsView_open`).
-/

namespace Circuit

open ZKF

/-- A table's columns' chunk polynomials, as `csView` opens them. -/
def csPolys (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) :
    Nat → List (List (List F) × List F) → List F → List (List (List F))
  | k + 1, d :: ds, cr => chunkPolys h cs Hl cl d.1 d.2 (cr.take (cs.length * h)) ::
      csPolys h cs Hl cl k ds (cr.drop (cs.length * h))
  | _, _, _ => []

/-- Every table's, as `tabsView` opens them. -/
def tabsPolys : List QTab → List (List (List (List F) × List F)) → List F → List (List (List (List F)))
  | T :: tabs, ds :: dss, cr => csPolys T.h T.cs T.Hl T.cl T.tg.length ds (cr.take T.crs) ::
      tabsPolys tabs dss (cr.drop T.crs)
  | _, _, _ => []

theorem csView_setsP (T : QTab) : ∀ (tg : List ((EF → EF → List EF → List (List (List F × List EF)) → F → F) ×
    (EF → EF → List EF → List (List (List F × List EF)) → EF))) (ds : List (List (List F) × List F)) (cr : List F),
    csView (tg.map fun p => (⟨T.cs, T.Hl, T.cl, T.S, T.ζ, T.h, p.1, p.2⟩ : CSet)) ds cr =
      (csPolys T.h T.cs T.Hl T.cl tg.length ds cr).map (openPolys T.S [T.ζ])
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: tg, d :: ds, cr => by
    show chunksView T.S [T.ζ] T.h T.cs T.Hl T.cl d.1 d.2 (cr.take (T.cs.length * T.h)) ::
        csView (tg.map _) ds (cr.drop (T.cs.length * T.h)) = _
    rw [chunksView_eq, csView_setsP T tg ds]
    rfl

/-- **The view's chunk openings are the chunk polynomials' values.** -/
theorem tabsView_open : ∀ (tabs : List QTab) (dss : List (List (List (List F) × List F))) (cr : List F),
    tabsView tabs dss cr = List.zipWith (fun T cps => cps.map (openPolys T.S [T.ζ])) tabs (tabsPolys tabs dss cr)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | T :: tabs, ds :: dss, cr => by
    show csView T.sets ds (cr.take T.crs) :: tabsView tabs dss (cr.drop T.crs) = _
    rw [tabsView_open tabs dss]
    unfold QTab.sets
    rw [csView_setsP T T.tg ds]
    rfl

/-- The chunk openings' values at the query points, as the view shows them. -/
def ovQ {X Y Z : Type} (pv : (X × List (List (List (List F × List EF)))) × Y × Z) : List (List (List (List F))) :=
  pv.1.2.map (fun tab => tab.map (fun col => col.map Prod.fst))

/-- The chunk polynomials' values at their tables' query points. -/
def opQ (Ss : List (List F)) (dq : List (List (List (List F)))) : List (List (List (List F))) :=
  List.zipWith (fun S cps => cps.map (fun ps => ps.map (fun p => S.map (fun s => fval s p)))) Ss dq

theorem openPolys_fst (S : List F) (Z : List EF) (ps : List (List F)) :
    (openPolys S Z ps).map Prod.fst = ps.map (fun p => S.map (fun s => fval s p)) := by
  unfold openPolys; rw [List.map_map]; rfl

theorem tabsView_ovQ : ∀ (tabs : List QTab) (dss : List (List (List (List F) × List F))) (cr : List F),
    (tabsView tabs dss cr).map (fun tab => tab.map (fun col => col.map Prod.fst)) =
      opQ (tabs.map (·.S)) (tabsPolys tabs dss cr)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | T :: tabs, ds :: dss, cr => by
    rw [tabsView_open]
    show ((T.tg.length, ds, cr).1 |> fun _ => (csPolys T.h T.cs T.Hl T.cl T.tg.length ds (cr.take T.crs)).map
        (openPolys T.S [T.ζ])).map (fun col => col.map Prod.fst) ::
      (List.zipWith (fun T cps => cps.map (openPolys T.S [T.ζ])) tabs (tabsPolys tabs dss (cr.drop T.crs))).map
        (fun tab => tab.map (fun col => col.map Prod.fst)) = _
    rw [← tabsView_open, tabsView_ovQ tabs dss, List.map_map]
    show _ :: _ = (fun cps => cps.map (fun ps => ps.map (fun p => T.S.map (fun s => fval s p))))
      (csPolys T.h T.cs T.Hl T.cl T.tg.length ds (cr.take T.crs)) :: _
    congr 1
    exact List.map_congr_left (fun ps _ => openPolys_fst _ _ _)

/-- A table's shape: what its chunk polynomials and randomness read. -/
def tShape (T : QTab) : Nat × List Chunk × List F × F × Nat := (T.h, T.cs, T.Hl, T.cl, T.tg.length)

/-- **The chunk polynomials read only the tables' shapes.** -/
theorem tabsPolys_congr : ∀ (tabs tabs' : List QTab) (dss : List (List (List (List F) × List F))) (cr : List F),
    tabs.map tShape = tabs'.map tShape → tabsPolys tabs dss cr = tabsPolys tabs' dss cr
  | [], [], _, _, _ => rfl
  | T :: tabs, T' :: tabs', [], _, _ => rfl
  | T :: tabs, T' :: tabs', ds :: dss, cr, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [tShape, Prod.mk.injEq] at h1
    obtain ⟨eh, ecs, eHl, ecl, etg⟩ := h1
    have ecr : T.crs = T'.crs := by
      unfold QTab.crs QTab.n; rw [etg, ecs, eh]
    show csPolys T.h T.cs T.Hl T.cl T.tg.length ds (cr.take T.crs) :: tabsPolys tabs dss (cr.drop T.crs) =
      csPolys T'.h T'.cs T'.Hl T'.cl T'.tg.length ds (cr.take T'.crs) :: tabsPolys tabs' dss (cr.drop T'.crs)
    rw [eh, ecs, eHl, ecl, etg, ecr, tabsPolys_congr tabs tabs' dss _ h2]
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h

/-- The chunk matrices' codewords' values at the query points, as the view
    shows them: the codeword openings past the `L` trace matrices. -/
def cwQ {X Y : Type} (L : Nat) (pv : X × List (List (List F × List EF)) × Y) : List (List (List F)) :=
  (pv.2.1.drop L).map (fun mat => mat.map Prod.fst)

/-- The codewords' values at their matrices' query points. -/
def opCw (Ss : List (List F)) (cw : List (List (List F))) : List (List (List F)) :=
  List.zipWith (fun S C => C.map (fun p => S.map (fun s => fval s p))) Ss cw

theorem traceInfo_len (ncw : Nat) : ∀ (gs : List MGroup) (ks : List Nat), ks.length = gs.length →
    (traceInfo ncw gs ks).length = gs.length
  | [], [], _ => rfl
  | _ :: gs, _ :: ks, h => by
    show (traceInfo ncw gs ks).length + 1 = gs.length + 1
    rw [traceInfo_len ncw gs ks (Nat.succ.inj h)]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem traceCws_len (ncw : Nat) : ∀ (gs : List MGroup) (ct : List F), (traceCws ncw gs ct).length = gs.length
  | [], _ => rfl
  | _ :: gs, ct => by
    show (traceCws ncw gs _).length + 1 = gs.length + 1
    rw [traceCws_len ncw gs]

theorem tabsInfo_S (ncw : Nat) : ∀ (tabs : List QTab), (tabsInfo ncw tabs).map (fun m => (m.S, m.Z)) =
    tabs.flatMap (fun T => List.replicate (T.cs.length + 1) (T.S, [T.ζ]))
  | [] => rfl
  | T :: tabs => by
    show (tInfo T ncw ++ tabsInfo ncw tabs).map _ = _
    rw [List.map_append, tabsInfo_S ncw tabs, List.flatMap_cons]
    unfold tInfo
    rw [List.map_replicate]

/-- **The view's chunk codeword openings are the codewords' values.** -/
theorem cw_openQ (ncw : Nat) (gs : List MGroup) (ks : List Nat) (hks : ks.length = gs.length) (ct cc : List F)
    (tabs : List QTab) :
    ((List.zipWith (fun (m : Mat) C => openPolys m.S m.Z C) (traceInfo ncw gs ks ++ tabsInfo ncw tabs)
        (traceCws ncw gs ct ++ tabsCws ncw tabs cc)).drop gs.length).map (fun mat => mat.map Prod.fst) =
      opCw ((tabsInfo ncw tabs).map (·.S)) (tabsCws ncw tabs cc) := by
  rw [List.zipWith_append (by rw [traceInfo_len ncw gs ks hks, traceCws_len]),
    List.drop_left' (by rw [List.length_zipWith, traceInfo_len ncw gs ks hks, traceCws_len, Nat.min_self])]
  unfold opCw
  rw [List.map_zipWith, List.zipWith_map_left]
  congr 1
  funext m C
  exact openPolys_fst _ _ _

theorem tabsCws_congr (ncw : Nat) : ∀ (tabs tabs' : List QTab) (cc : List F),
    tabs.map tShape = tabs'.map tShape → tabsCws ncw tabs cc = tabsCws ncw tabs' cc
  | [], [], _, _ => rfl
  | T :: tabs, T' :: tabs', cc, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [tShape, Prod.mk.injEq] at h1
    obtain ⟨eh, ecs, eHl, ecl, _⟩ := h1
    have ecw : T.cws ncw = T'.cws ncw := by unfold QTab.cws QTab.n; rw [ecs, eh]
    have et : tCws T ncw (cc.take (T.cws ncw)) = tCws T' ncw (cc.take (T'.cws ncw)) := by
      unfold tCws QTab.n; rw [ecw, ecs, eh, eHl, ecl]
    show tCws T ncw (cc.take (T.cws ncw)) ++ tabsCws ncw tabs (cc.drop (T.cws ncw)) =
      tCws T' ncw (cc.take (T'.cws ncw)) ++ tabsCws ncw tabs' (cc.drop (T'.cws ncw))
    rw [et, ecw, tabsCws_congr ncw tabs tabs' _ h2]
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

section
variable {V : Type} (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
  (qs : List QGroup) (ks : List Nat) (cols : (Nat → Tup) → EF → EF → List (List (List F))) (tabs : List QTab)
  (qdT : (Nat → Tup) → EF → EF → List F → List (List (List (List F) × List F))) (ncw : Nat) (αb : EF)
  (fri : EF → EF → List (EF → EF) → V) (mk : List Nat)

/-- **Groups committed after the challenges**: their masked polynomials and
    codewords at the challenges in use. -/
def mainP2 (t : Nat → Tup) (α β : EF) (ρ : Nat) : List (List (List F)) :=
  mk.map (fun k => (mpolysMulti (qs.map QGroup.ext) (cols t α β) (msF qs ks tabs ncw ρ)).getD k [] ++
    (traceCws ncw (qs.map QGroup.ext) (ctF qs ks tabs ncw ρ)).getD k [])

theorem pcsFri_ovP (hmk : ∀ k ∈ mk, k < qs.length ∧ ∀ t α β, k < (cols t α β).length)
    (hks : ks.length = qs.length) (t : Nat → Tup) (α β : EF) (ρ : Nat) :
    ovF2 (qs.map (·.base.S)) mk (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β ρ) =
      opF (qs.map (·.base.S)) mk (mainP2 qs ks cols tabs ncw mk t α β ρ) := by
  unfold ovF2 opF mainP2
  rw [zip_map_self]
  refine List.map_congr_left (fun k hk => ?_)
  obtain ⟨h1, h2⟩ := hmk k hk
  have e : (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β ρ).1.1 =
      quotPost qs α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) (msF qs ks tabs ncw ρ)) :=
    rfl
  have e2 : (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β ρ).2.1 =
      List.zipWith (fun (m : Mat) C => openPolys m.S m.Z C) (traceInfo ncw (qs.map QGroup.ext) ks ++ tabsInfo ncw tabs)
        (traceCws ncw (qs.map QGroup.ext) (ctF qs ks tabs ncw ρ) ++ tabsCws ncw tabs
          (((digitsF (friN1 qs ks tabs + friN2 qs tabs ncw) ρ).drop (friN1 qs ks tabs)).drop
            (traceCw ncw (qs.map QGroup.ext)))) := rfl
  rw [e, e2, quot_open α β _ qs (cols t α β) _ k h1 (h2 t α β), cw_open ncw qs ks _ _ _ k h1 hks]
  show _ = List.map _ (_ ++ _)
  rw [List.map_append]
end

/-- The second commitment's opened values: the groups `mk`'s (masked
    columns and codewords), every quotient table's chunks', and the chunk
    matrices' codewords'. -/
def ov2F {Y : Type} (Ss : List (List F)) (mk : List Nat) (L : Nat)
    (pv : (List (List (List F × List EF) × List (List EF)) × List (List (List (List F × List EF)))) ×
      List (List (List F × List EF)) × Y) : List (List (List F)) × List (List (List (List F))) × List (List (List F)) :=
  (ovF2 Ss mk pv, ovQ pv, cwQ L pv)

/-- The second commitment's data's values at the query points. -/
def op2F (Ss : List (List F)) (mk : List Nat) (SsT SsC : List (List F))
    (d : List (List (List F)) × List (List (List (List F))) × List (List (List F))) :
    List (List (List F)) × List (List (List (List F))) × List (List (List F)) :=
  (opF Ss mk d.1, opQ SsT d.2.1, opCw SsC d.2.2)

/-- Polynomials through given values. -/
def sdQ (SsT : List (List F)) (o : List (List (List (List F)))) : List (List (List (List F))) :=
  List.zipWith (fun S cps => cps.map (fun vs => vs.map (fun vals => finterp (S.zip vals)))) SsT o

def sdCw (SsC : List (List F)) (o : List (List (List F))) : List (List (List F)) :=
  List.zipWith (fun S C => C.map (fun vals => finterp (S.zip vals))) SsC o

def sd2F (Ss : List (List F)) (mk : List Nat) (SsT SsC : List (List F))
    (o : List (List (List F)) × List (List (List (List F))) × List (List (List F))) :
    List (List (List F)) × List (List (List (List F))) × List (List (List F)) :=
  (sdF Ss mk o.1, sdQ SsT o.2.1, sdCw SsC o.2.2)

theorem interp_vals (S : List F) (p : List F) :
    S.map (fun s => fval s (finterp (S.zip (S.map (fun s => fval s p))))) = S.map (fun s => fval s p) := by
  refine List.map_congr_left (fun s hs => ?_)
  have hc : ∀ a ∈ S.zip (S.map (fun s => fval s p)), ∀ b ∈ S.zip (S.map (fun s => fval s p)),
      a.1 = b.1 → a.2 = b.2 := by
    have key : ∀ a ∈ S.zip (S.map (fun s => fval s p)), a.2 = fval a.1 p := by
      intro a ha
      obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 ha
      rw [← e, List.getElem_zip]
      exact List.getElem_map _
    intro a ha b hb e
    rw [key a ha, key b hb, e]
  have hmem : (s, fval s p) ∈ S.zip (S.map (fun s => fval s p)) := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hs
    have := zip_mem (V := S.map (fun s => fval s p)) hi (by rw [List.length_map])
    simpa using this
  exact finterp_eval_cons _ hc _ hmem

theorem zipWith_fgf {α β γ : Type} (f : α → β → γ) (g : α → γ → β) (h : ∀ a b, f a (g a (f a b)) = f a b) :
    ∀ (l : List α) (m : List β), List.zipWith f l (List.zipWith g l (List.zipWith f l m)) = List.zipWith f l m
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l, b :: m => by
    show f a (g a (f a b)) :: _ = f a b :: _
    rw [h, zipWith_fgf f g h l m]

/-- **Interpolation recovers the second commitment's openings.** -/
theorem op2_sd2 (Ss : List (List F)) (mk : List Nat) (SsT SsC : List (List F)) (φ : Nat → List (List F))
    (dq : List (List (List (List F)))) (dc : List (List (List F))) :
    op2F Ss mk SsT SsC (sd2F Ss mk SsT SsC (op2F Ss mk SsT SsC (mk.map φ, dq, dc))) =
      op2F Ss mk SsT SsC (mk.map φ, dq, dc) := by
  show (opF Ss mk (sdF Ss mk (opF Ss mk (mk.map φ))), opQ SsT (sdQ SsT (opQ SsT dq)),
    opCw SsC (sdCw SsC (opCw SsC dc))) = (opF Ss mk (mk.map φ), opQ SsT dq, opCw SsC dc)
  rw [opF_sdF]
  congr 2
  · unfold opQ sdQ
    refine zipWith_fgf _ _ (fun S cps => ?_) SsT dq
    simp only [List.map_map]
    refine List.map_congr_left (fun ps _ => ?_)
    simp only [Function.comp_apply, List.map_map]
    exact List.map_congr_left (fun p _ => interp_vals S p)
  · unfold opCw sdCw
    refine zipWith_fgf _ _ (fun S C => ?_) SsC dc
    simp only [List.map_map]
    exact List.map_congr_left (fun p _ => interp_vals S p)

section
variable {V : Type} (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
  (qs : List QGroup) (ks : List Nat) (cols : (Nat → Tup) → EF → EF → List (List (List F))) (tabs : List QTab)
  (qdT : (Nat → Tup) → EF → EF → List F → List (List (List (List F) × List F))) (ncw : Nat) (αb : EF)
  (fri : EF → EF → List (EF → EF) → V) (mk : List Nat)

/-- The chunk randomness and the chunk codewords' randomness `ρ` gives. -/
def crF (ρ : Nat) : List F :=
  ((digitsF (friN1 qs ks tabs + friN2 qs tabs ncw) ρ).take (friN1 qs ks tabs)).drop (mtotal (qs.map QGroup.ext) ks)
def ccF (ρ : Nat) : List F :=
  ((digitsF (friN1 qs ks tabs + friN2 qs tabs ncw) ρ).drop (friN1 qs ks tabs)).drop (traceCw ncw (qs.map QGroup.ext))

theorem len_ext (qs : List QGroup) : (qs.map QGroup.ext).length = qs.length := List.length_map _

/-- **The real view opens the second commitment's data.** -/
theorem pcsFri_ovR2 (hmk : ∀ k ∈ mk, k < qs.length ∧ ∀ t α β, k < (cols t α β).length)
    (hks : ks.length = qs.length) (t : Nat → Tup) (α β : EF) (ρ : Nat) :
    ov2F (qs.map (·.base.S)) mk qs.length (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β ρ) =
      op2F (qs.map (·.base.S)) mk (tabs.map (·.S)) ((tabsInfo ncw tabs).map (·.S))
        (mainP2 qs ks cols tabs ncw mk t α β ρ, tabsPolys tabs (qdT t α β (msF qs ks tabs ncw ρ)) (crF qs ks tabs ncw ρ),
          tabsCws ncw tabs (ccF qs ks tabs ncw ρ)) := by
  have e1 := pcsFri_ovP off tv qs ks cols tabs qdT ncw αb fri mk hmk hks t α β ρ
  have eq : ovQ (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β ρ) =
      opQ (tabs.map (·.S)) (tabsPolys tabs (qdT t α β (msF qs ks tabs ncw ρ)) (crF qs ks tabs ncw ρ)) :=
    tabsView_ovQ tabs _ _
  have ec : cwQ qs.length (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β ρ) =
      opCw ((tabsInfo ncw tabs).map (·.S)) (tabsCws ncw tabs (ccF qs ks tabs ncw ρ)) := by
    have := cw_openQ ncw (qs.map QGroup.ext) ks (by rw [len_ext]; exact hks) (ctF qs ks tabs ncw ρ)
      (ccF qs ks tabs ncw ρ) tabs
    rw [len_ext] at this
    exact this
  show (_, _, _) = (_, _, _)
  rw [e1, eq, ec]

/-- **The simulated view opens the simulator's second data.** -/
theorem psimFri_ovR2 (hmk : ∀ k ∈ mk, k < qs.length) (hks : ks.length = qs.length) (α β : EF) (v : List EF)
    (ρ : Nat) :
    ov2F (qs.map (·.base.S)) mk qs.length (psimFri qs ks tabs ncw αb fri α β v ρ) =
      op2F (qs.map (·.base.S)) mk (tabs.map (·.S)) ((tabsInfo ncw tabs).map (·.S))
        (mainZ2 qs ks tabs ncw mk ρ,
          tabsPolys tabs (canonT tabs α β v (openMulti (qs.map QGroup.ext)
            (((qs.map QGroup.ext).zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
            (msF qs ks tabs ncw ρ))) (crF qs ks tabs ncw ρ),
          tabsCws ncw tabs (ccF qs ks tabs ncw ρ)) := by
  have e1 := psimFri_ov2 qs ks tabs ncw αb fri mk hmk hks α β v ρ
  have eq : ovQ (psimFri qs ks tabs ncw αb fri α β v ρ) =
      opQ (tabs.map (·.S)) (tabsPolys tabs (canonT tabs α β v (openMulti (qs.map QGroup.ext)
            (((qs.map QGroup.ext).zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
            (msF qs ks tabs ncw ρ))) (crF qs ks tabs ncw ρ)) :=
    tabsView_ovQ tabs _ _
  have ec : cwQ qs.length (psimFri qs ks tabs ncw αb fri α β v ρ) =
      opCw ((tabsInfo ncw tabs).map (·.S)) (tabsCws ncw tabs (ccF qs ks tabs ncw ρ)) := by
    have := cw_openQ ncw (qs.map QGroup.ext) ks (by rw [len_ext]; exact hks) (ctF qs ks tabs ncw ρ)
      (ccF qs ks tabs ncw ρ) tabs
    rw [len_ext] at this
    exact this
  show (_, _, _) = (_, _, _)
  rw [e1, eq, ec]
end

end Circuit
