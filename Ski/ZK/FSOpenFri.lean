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
  (`sdF`), exact when they are distinct (`opF_sdF`).
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

/-- **Interpolation recovers the openings**: at distinct query points the
    polynomials through a datum's opened values open to the same values. -/
theorem opF_sdF (Ss : List (List F)) (mk : List Nat) (hnd : ∀ k ∈ mk, (Ss.getD k []).Nodup)
    (φ : Nat → List (List F)) :
    opF Ss mk (sdF Ss mk (opF Ss mk (mk.map φ))) = opF Ss mk (mk.map φ) := by
  unfold opF sdF
  rw [zip_map_self, zip_map_self, zip_map_self]
  refine List.map_congr_left (fun k hk => ?_)
  dsimp only
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun p _ => ?_)
  show (Ss.getD k []).map (fun s => fval s (finterp ((Ss.getD k []).zip ((Ss.getD k []).map (fun s => fval s p))))) =
    (Ss.getD k []).map (fun s => fval s p)
  refine List.map_congr_left (fun s hs => ?_)
  have hfst : ((Ss.getD k []).zip ((Ss.getD k []).map (fun s => fval s p))).map Prod.fst = Ss.getD k [] :=
    List.map_fst_zip (by rw [List.length_map]; exact Nat.le_refl _)
  have hmem : (s, fval s p) ∈ (Ss.getD k []).zip ((Ss.getD k []).map (fun s => fval s p)) := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hs
    have := zip_mem (V := (Ss.getD k []).map (fun s => fval s p)) hi (by rw [List.length_map])
    simpa using this
  exact finterp_eval _ (by rw [hfst]; exact hnd k hk) _ hmem

end Circuit
