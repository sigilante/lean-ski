import Ski.ZK.FSOpen

/-!
# The opened main columns of the composed PCS

For `fs_open` an instance names the data its first message commits (the
main groups' masked column polynomials), the values its view opens at the
query points, and the simulator's own.  Here, for the PCS of
`Ski/ZK/MaskFri.lean`:

* the view's openings of the groups `mk` at their query points
  (`ovF`) are the masked polynomials' values there (`quot_open`);
* a group's masked polynomials read only the earlier groups' column
  counts (`mpolysMulti_getD`), so where the main groups' columns do not
  depend on the challenges, neither does the committed data (`mainF`,
  `pcsFri_ov`);
* the simulator's openings are its zero columns' masked polynomials'
  values, which depend on nothing but its randomness (`psimFri_ov`);
* data with given openings: interpolation through the query points
  (`sdF`), exact, the points repeated or not (`finterp_eval_cons`,
  `opF_sdF`);
* with the random codewords Plonky3 commits in each main group's matrix:
  the opened values `ovF2`, the codewords' openings at the query points
  (`cw_open`), the committed data `mainF2`, `mainZ2` (`pcsFri_ov2`,
  `psimFri_ov2`), and the simulator's opening verifying against its view
  (`mainZ2_verifies`).
-/

namespace Circuit

open ZKF

/-- The opened values of the groups `mk` at their query points. -/
def ovF {X Y : Type} (mk : List Nat) (pv : (List (List (List F × List EF) × List (List EF)) × X) × Y) :
    List (List (List F)) :=
  mk.map (fun k => (pv.1.1.getD k ([], [])).1.map Prod.fst)

/-- The values of the groups `mk`'s polynomials at their query points. -/
def opF (Ss : List (List F)) (mk : List Nat) (d : List (List (List F))) : List (List (List F)) :=
  (mk.zip d).map (fun p => p.2.map (fun poly => (Ss.getD p.1 []).map (fun s => fval s poly)))

/-- Polynomials through given values at the query points. -/
def sdF (Ss : List (List F)) (mk : List Nat) (o : List (List (List F))) : List (List (List F)) :=
  (mk.zip o).map (fun p => p.2.map (fun vals => finterp ((Ss.getD p.1 []).zip vals)))

theorem quot_open (α β : EF) (v : List EF) : ∀ (qs : List QGroup) (tss : List (List (List F))) (rs : List F) (k : Nat),
    k < qs.length → k < tss.length →
    ((quotPost qs α β v (openMulti (qs.map QGroup.ext) tss rs)).getD k ([], [])).1.map Prod.fst =
      ((mpolysMulti (qs.map QGroup.ext) tss rs).getD k []).map
        (fun p => ((qs.map (·.base.S)).getD k []).map (fun s => fval s p))
  | q :: qs, ts :: tss, rs, 0, _, _ => by
    show ((q.view α β v (openAll q.ext.T q.ext.R q.ext.S q.ext.Z q.ext.n ts (rs.take (ts.length * q.ext.n)))).1).map
        Prod.fst = (mpolys q.ext.T q.ext.R q.ext.n ts (rs.take (ts.length * q.ext.n))).map _
    unfold QGroup.view
    rw [openAll_eq_map, List.map_map, List.map_map]
    refine List.map_congr_left (fun p _ => ?_)
    show ((q.base.S ++ q.base.S.map q.nxt).map (fun s => fval s p)).take q.base.S.length = _
    rw [List.map_append, List.take_left' (by rw [List.length_map])]
    rfl
  | q :: qs, ts :: tss, rs, k + 1, hk, hk' => by
    have := quot_open α β v qs tss (rs.drop (ts.length * q.ext.n)) k (Nat.lt_of_succ_lt_succ hk)
      (Nat.lt_of_succ_lt_succ hk')
    exact this
  | [], _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, hk => absurd hk (Nat.not_lt_zero _)

theorem mpolysMulti_getD : ∀ (gs : List MGroup) (tss tss' : List (List (List F))) (rs : List F) (k : Nat),
    tss.map List.length = tss'.map List.length → tss.getD k [] = tss'.getD k [] →
    (mpolysMulti gs tss rs).getD k [] = (mpolysMulti gs tss' rs).getD k []
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], [], _, _, _, _ => rfl
  | _ :: _, [], _ :: _, _, _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, h, _ => nomatch h
  | g :: gs, ts :: tss, ts' :: tss', rs, 0, hl, he => by
    have h0 : ts = ts' := he
    subst h0; rfl
  | g :: gs, ts :: tss, ts' :: tss', rs, k + 1, hl, he => by
    simp only [List.map_cons, List.cons.injEq] at hl
    show (mpolysMulti gs tss (rs.drop (ts.length * g.n))).getD k [] =
      (mpolysMulti gs tss' (rs.drop (ts'.length * g.n))).getD k []
    rw [hl.1]
    exact mpolysMulti_getD gs tss tss' _ k hl.2 he

theorem zip_map_self {α β γ : Type} (g : α → β) (h : α × β → γ) :
    ∀ l : List α, (l.zip (l.map g)).map h = l.map (fun k => h (k, g k))
  | [] => rfl
  | a :: l => by show h (a, g a) :: (l.zip (l.map g)).map h = _; rw [zip_map_self g h l]; rfl

section
variable {V : Type} (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
  (qs : List QGroup) (ks : List Nat) (cols : (Nat → Tup) → EF → EF → List (List (List F))) (tabs : List QTab)
  (qdT : (Nat → Tup) → EF → EF → List F → List (List (List (List F) × List F))) (ncw : Nat) (αb : EF)
  (fri : EF → EF → List (EF → EF) → V) (mk : List Nat)

/-- The masks the PCS's randomness `ρ` gives its groups. -/
def msF (ρ : Nat) : List F :=
  ((digitsF (friN1 qs ks tabs + friN2 qs tabs ncw) ρ).take (friN1 qs ks tabs)).take (mtotal (qs.map QGroup.ext) ks)

/-- **The committed data**: the groups `mk`'s masked polynomials, at the
    challenges `0` (the main groups' columns do not depend on them). -/
def mainF (t : Nat → Tup) (ρ : Nat) : List (List (List F)) :=
  mk.map (fun k => (mpolysMulti (qs.map QGroup.ext) (cols t EF.zero EF.zero) (msF qs ks tabs ncw ρ)).getD k [])

/-- The simulator's: its zero columns' masked polynomials. -/
def mainZ (ρ : Nat) : List (List (List F)) :=
  mk.map (fun k => (mpolysMulti (qs.map QGroup.ext)
    (((qs.map QGroup.ext).zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
    (msF qs ks tabs ncw ρ)).getD k [])

/-- **The real view opens the committed data**: where the groups `mk`'s
    columns do not depend on the challenges, the view's openings at the
    query points are the committed polynomials' values there. -/
theorem pcsFri_ov (hmk : ∀ k ∈ mk, k < qs.length ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [])
    (hlen : ∀ t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length)
    (t : Nat → Tup) (α β : EF) (ρ : Nat) :
    ovF mk (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β ρ) =
      opF (qs.map (·.base.S)) mk (mainF qs ks cols tabs ncw mk t ρ) := by
  unfold ovF opF mainF
  rw [zip_map_self]
  refine List.map_congr_left (fun k hk => ?_)
  obtain ⟨h1, h2⟩ := hmk k hk
  have e : (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β ρ).1.1 =
      quotPost qs α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) (msF qs ks tabs ncw ρ)) :=
    rfl
  rw [e, quot_open α β _ qs (cols t α β) _ k h1 (h2 t α β).1,
    mpolysMulti_getD _ _ _ _ k (hlen t α β) (h2 t α β).2]

/-- **The simulated view opens the simulator's data**, whatever the
    challenges. -/
theorem psimFri_ov (hmk : ∀ k ∈ mk, k < qs.length) (hks : ks.length = qs.length) (α β : EF) (v : List EF) (ρ : Nat) :
    ovF mk (psimFri qs ks tabs ncw αb fri α β v ρ) = opF (qs.map (·.base.S)) mk (mainZ qs ks tabs ncw mk ρ) := by
  unfold ovF opF mainZ
  rw [zip_map_self]
  refine List.map_congr_left (fun k hk => ?_)
  have hzl : k < (((qs.map QGroup.ext).zip ks).map
      (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F)))).length := by
    rw [List.length_map, List.length_zip, List.length_map, hks, Nat.min_self]; exact hmk k hk
  exact quot_open α β v qs _ (msF qs ks tabs ncw ρ) k (hmk k hk) hzl
end

/-- **The interpolant takes each value, repeated points allowed**: through
    points whose repeats carry one value, each point's value. -/
theorem finterp_eval_cons : ∀ pts : List (F × F), (∀ p ∈ pts, ∀ q ∈ pts, p.1 = q.1 → p.2 = q.2) →
    ∀ p ∈ pts, fval p.1 (finterp pts) = p.2
  | [], _, _, h => nomatch h
  | (x, y) :: r, hc, p, hp => by
    have hcr : ∀ p ∈ r, ∀ q ∈ r, p.1 = q.1 → p.2 = q.2 := fun p hp q hq =>
      hc p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)
    show fval p.1 (fcadd (finterp r) (fcscale ((y - fval x (finterp r)) * finv (fval x (fvan (r.map Prod.fst))))
      (fvan (r.map Prod.fst)))) = p.2
    rw [fval_fcadd, fval_fcscale]
    rcases List.mem_cons.1 hp with rfl | hr
    · show fval x (finterp r) + (y - fval x (finterp r)) * finv (fval x (fvan (r.map Prod.fst))) *
        fval x (fvan (r.map Prod.fst)) = y
      by_cases hx : x ∈ r.map Prod.fst
      · obtain ⟨q, hq, e⟩ := List.mem_map.1 hx
        rw [fvan_root x _ hx, mul_zero', add_zero', ← e, finterp_eval_cons r hcr q hq]
        exact (hc (x, y) List.mem_cons_self q (List.mem_cons_of_mem _ hq) e.symm).symm
      · have hz := fvan_ne x (r.map Prod.fst) hx
        rw [mul_assoc', finv_mul hz, mul_one']
        exact fid (e := v 0 + (v 1 - v 0)) (e' := v 1) (by decide) [fval x (finterp r), y]
    · rw [finterp_eval_cons r hcr p hr, fvan_root p.1 _ (List.mem_map.2 ⟨p, hr, rfl⟩), mul_zero', add_zero']

/-- **Interpolation recovers the openings**: the polynomials through a
    datum's opened values open to the same values, the query points
    repeated or not. -/
theorem opF_sdF (Ss : List (List F)) (mk : List Nat) (φ : Nat → List (List F)) :
    opF Ss mk (sdF Ss mk (opF Ss mk (mk.map φ))) = opF Ss mk (mk.map φ) := by
  unfold opF sdF
  rw [zip_map_self, zip_map_self, zip_map_self]
  refine List.map_congr_left (fun k _ => ?_)
  dsimp only
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun p _ => ?_)
  show (Ss.getD k []).map (fun s => fval s (finterp ((Ss.getD k []).zip ((Ss.getD k []).map (fun s => fval s p))))) =
    (Ss.getD k []).map (fun s => fval s p)
  refine List.map_congr_left (fun s hs => ?_)
  have hc : ∀ a ∈ (Ss.getD k []).zip ((Ss.getD k []).map (fun s => fval s p)),
      ∀ b ∈ (Ss.getD k []).zip ((Ss.getD k []).map (fun s => fval s p)), a.1 = b.1 → a.2 = b.2 := by
    have key : ∀ a ∈ (Ss.getD k []).zip ((Ss.getD k []).map (fun s => fval s p)), a.2 = fval a.1 p := by
      intro a ha
      obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 ha
      rw [← e, List.getElem_zip]
      exact List.getElem_map _
    intro a ha b hb e
    rw [key a ha, key b hb, e]
  have hmem : (s, fval s p) ∈ (Ss.getD k []).zip ((Ss.getD k []).map (fun s => fval s p)) := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hs
    have := zip_mem (V := (Ss.getD k []).map (fun s => fval s p)) hi (by rw [List.length_map])
    simpa using this
  exact finterp_eval_cons _ hc _ hmem

-- ---------------------------------------------------------------------------
-- The committed leaf holds the codewords too
-- ---------------------------------------------------------------------------

/-- The opened values of the groups `mk` at their query points, the masked
    columns' and then the random codewords' (Plonky3 commits a group's
    codeword columns in its matrix, `hiding_pcs.rs`). -/
def ovF2 {X Y : Type} (Ss : List (List F)) (mk : List Nat)
    (pv : (List (List (List F × List EF) × List (List EF)) × X) × (List (List (List F × List EF)) × Y)) :
    List (List (List F)) :=
  mk.map (fun k => (pv.1.1.getD k ([], [])).1.map Prod.fst ++
    (pv.2.1.getD k []).map (fun o => o.1.take (Ss.getD k []).length))

theorem cw_open (ncw : Nat) : ∀ (qs : List QGroup) (ks : List Nat) (ct : List F) (tl : List Mat)
    (cl : List (List (List F))) (k : Nat), k < qs.length → ks.length = qs.length →
    ((List.zipWith (fun (m : Mat) C => openPolys m.S m.Z C) (traceInfo ncw (qs.map QGroup.ext) ks ++ tl)
        (traceCws ncw (qs.map QGroup.ext) ct ++ cl)).getD k []).map
        (fun o => o.1.take ((qs.map (·.base.S)).getD k []).length) =
      ((traceCws ncw (qs.map QGroup.ext) ct).getD k []).map
        (fun p => ((qs.map (·.base.S)).getD k []).map (fun s => fval s p))
  | q :: qs, kk :: ks, ct, tl, cl, 0, _, _ => by
    show ((openPolys q.ext.S q.ext.Z (cwPolys q.ext.dom q.ext.dom.length ncw (ct.take (ncw * q.ext.dom.length)))).map
        (fun o => o.1.take q.base.S.length)) = (cwPolys q.ext.dom q.ext.dom.length ncw
          (ct.take (ncw * q.ext.dom.length))).map (fun p => q.base.S.map (fun s => fval s p))
    unfold openPolys
    rw [List.map_map]
    refine List.map_congr_left (fun p _ => ?_)
    show ((q.base.S ++ q.base.S.map q.nxt).map (fun s => fval s p)).take q.base.S.length = _
    rw [List.map_append, List.take_left' (by rw [List.length_map])]
  | q :: qs, kk :: ks, ct, tl, cl, k + 1, hk, hl => by
    exact cw_open ncw qs ks (ct.drop (ncw * q.ext.dom.length)) tl cl k (Nat.lt_of_succ_lt_succ hk)
      (Nat.succ.inj hl)
  | [], _, _, _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, _, _, hl => nomatch hl

section
variable {V : Type} (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
  (qs : List QGroup) (ks : List Nat) (cols : (Nat → Tup) → EF → EF → List (List (List F))) (tabs : List QTab)
  (qdT : (Nat → Tup) → EF → EF → List F → List (List (List (List F) × List F))) (ncw : Nat) (αb : EF)
  (fri : EF → EF → List (EF → EF) → V) (mk : List Nat)

/-- The codeword randomness the PCS's randomness `ρ` gives the groups. -/
def ctF (ρ : Nat) : List F :=
  ((digitsF (friN1 qs ks tabs + friN2 qs tabs ncw) ρ).drop (friN1 qs ks tabs)).take (traceCw ncw (qs.map QGroup.ext))

/-- **The committed data, codewords included**: each group in `mk`, its
    masked polynomials and its codeword polynomials. -/
def mainF2 (t : Nat → Tup) (ρ : Nat) : List (List (List F)) :=
  mk.map (fun k => (mpolysMulti (qs.map QGroup.ext) (cols t EF.zero EF.zero) (msF qs ks tabs ncw ρ)).getD k [] ++
    (traceCws ncw (qs.map QGroup.ext) (ctF qs ks tabs ncw ρ)).getD k [])

/-- The simulator's: its zero columns' and the same codewords. -/
def mainZ2 (ρ : Nat) : List (List (List F)) :=
  mk.map (fun k => (mpolysMulti (qs.map QGroup.ext)
    (((qs.map QGroup.ext).zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
    (msF qs ks tabs ncw ρ)).getD k [] ++ (traceCws ncw (qs.map QGroup.ext) (ctF qs ks tabs ncw ρ)).getD k [])

theorem pcsFri_ov2 (hmk : ∀ k ∈ mk, k < qs.length ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [])
    (hlen : ∀ t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length)
    (hks : ks.length = qs.length) (t : Nat → Tup) (α β : EF) (ρ : Nat) :
    ovF2 (qs.map (·.base.S)) mk (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β ρ) =
      opF (qs.map (·.base.S)) mk (mainF2 qs ks cols tabs ncw mk t ρ) := by
  unfold ovF2 opF mainF2
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
  rw [e, e2, quot_open α β _ qs (cols t α β) _ k h1 (h2 t α β).1,
    mpolysMulti_getD _ _ _ _ k (hlen t α β) (h2 t α β).2, cw_open ncw qs ks _ _ _ k h1 hks]
  show _ = List.map _ (_ ++ _)
  rw [List.map_append]

theorem psimFri_ov2 (hmk : ∀ k ∈ mk, k < qs.length) (hks : ks.length = qs.length) (α β : EF) (v : List EF)
    (ρ : Nat) :
    ovF2 (qs.map (·.base.S)) mk (psimFri qs ks tabs ncw αb fri α β v ρ) =
      opF (qs.map (·.base.S)) mk (mainZ2 qs ks tabs ncw mk ρ) := by
  unfold ovF2 opF mainZ2
  rw [zip_map_self]
  refine List.map_congr_left (fun k hk => ?_)
  have hzl : k < (((qs.map QGroup.ext).zip ks).map
      (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F)))).length := by
    rw [List.length_map, List.length_zip, List.length_map, hks, Nat.min_self]; exact hmk k hk
  have e2 : (psimFri qs ks tabs ncw αb fri α β v ρ).2.1 =
      List.zipWith (fun (m : Mat) C => openPolys m.S m.Z C) (traceInfo ncw (qs.map QGroup.ext) ks ++ tabsInfo ncw tabs)
        (traceCws ncw (qs.map QGroup.ext) (ctF qs ks tabs ncw ρ) ++ tabsCws ncw tabs
          (((digitsF (friN1 qs ks tabs + friN2 qs tabs ncw) ρ).drop (friN1 qs ks tabs)).drop
            (traceCw ncw (qs.map QGroup.ext)))) := rfl
  rw [e2, cw_open ncw qs ks _ _ _ k (hmk k hk) hks]
  have q := quot_open α β v qs _ (msF qs ks tabs ncw ρ) k (hmk k hk) hzl
  show List.map Prod.fst (_ : List (List F × List EF) × List (List EF)).1 ++ _ = _
  rw [show (psimFri qs ks tabs ncw αb fri α β v ρ).1.1 = quotPost qs α β v (openMulti (qs.map QGroup.ext)
    (((qs.map QGroup.ext).zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
    (msF qs ks tabs ncw ρ)) from rfl, q, List.map_append]
end

/-- **The simulator's opening verifies against its view's values**: the
    values its simulated view shows at the query points are its data's
    openings, so any check the scheme passes on every honest commitment
    and opening passes on the simulator's against those values.  It says
    nothing of checks against the quotient or FRI. -/
theorem mainZ2_verifies {V Pp : Type} (qs : List QGroup) (ks : List Nat) (tabs : List QTab) (ncw : Nat) (αb : EF)
    (fri : EF → EF → List (EF → EF) → V) (mk : List Nat) (hmk : ∀ k ∈ mk, k < qs.length)
    (hks : ks.length = qs.length)
    (Com : List (List (List F)) → Nat → Nat) (Pf : List (List (List F)) → Nat → Pp)
    (Verify : Nat → List (List (List F)) → Pp → Bool)
    (hver : ∀ d σ, Verify (Com d σ) (opF (qs.map (·.base.S)) mk d) (Pf d σ) = true) (α β : EF) (v : List EF)
    (ρ σ : Nat) :
    let o := ovF2 (qs.map (·.base.S)) mk (psimFri qs ks tabs ncw αb fri α β v ρ)
    Verify (Com (sdF (qs.map (·.base.S)) mk o) σ) o (Pf (sdF (qs.map (·.base.S)) mk o) σ) = true := by
  intro o
  have ho : o = opF (qs.map (·.base.S)) mk (mainZ2 qs ks tabs ncw mk ρ) :=
    psimFri_ov2 qs ks tabs ncw αb fri mk hmk hks α β v ρ
  rw [ho]
  exact sim_opening_verifies Com Pf _ _ Verify hver _ (opF_sdF _ mk _) σ

end Circuit
