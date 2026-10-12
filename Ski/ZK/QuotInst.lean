import Ski.ZK.QuotOpen

/-!
# The quotient tables of a circuit

`pcsCloseN_fri` takes the quotient tables (`QTab`) and asks
`TabsHonest`: every table's honest chunk data show its `CSet` targets.
This file builds a table from an AIR whose coordinate targets are read
from one group's openings (`airQTab`), with the honest data of its
masked columns (`airData`).  `tabsHonest_air` proves `TabsHonest` for
it at every trace, challenge, mask and transcript value, and
`pcsCloseN_fri_air` is the composed hiding PCS with that table.

The hypotheses are of three kinds.
- **At each trace** (`hsatT`): the group's columns are a table that
  meets `Sat`, with constraints in the window of offsets 0 and 1.
  `PCSCloseN` quantifies over every tuple assignment `t` and every
  challenge pair, so this is stronger than completeness, which gives
  `Sat` only for accepted runs.  A trace builder meets it when it falls
  back to one fixed accepting table on inputs it does not accept.
- **The group:** its trace points are `⟨g⟩` and its next-row map is
  `g ·`; its out-of-domain points are `ζ, g ζ`; its masks lie off the
  trace.
- **The quotient's domains and weights:**
  - the chunk domains are Plonky3's split (`splitD`);
  - the chunk count and degree are Plonky3's (`2^(lq+1)` chunks,
    `E.pdeg ≤ 2^lq`);
  - the weights are `cis_k / κ` (`hw`).

The weight lists `ws` are the base coordinates of the folding
challenge's powers: a fixed folding challenge, independent of the masks.
The theorem holds for each value, and the model does not sample it.
The theorem covers one quotient table, that of the group `gi`; a
circuit with several AIRs discharges each table alone and combines them
(`tabsHonest_cons`).
Fiat–Shamir and the Merkle commitments' hiding stay assumed, as in
`pcsCloseN_fri`.
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Plumbing: the targets see the chunk data only through its length
-- ---------------------------------------------------------------------------

theorem ppoly_hc : ∀ (L L' : List (List F × F × F × List F)), L.map (fun p => (p.1, p.2.1)) = L'.map (fun p => (p.1, p.2.1)) →
    rpoly.ppoly L = rpoly.ppoly L'
  | [], [], _ => rfl
  | (H, c, μ, q) :: L, (H', c', μ', q') :: L', h => by
    have e := List.cons.inj h
    have e1 : (H, c) = (H', c') := e.1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
    show fmul (vpoly H c) (rpoly.ppoly L) = fmul (vpoly H c) (rpoly.ppoly L')
    rw [ppoly_hc L L' e.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem chunksL_hc : ∀ (cs : List Chunk) (qs qs' : List (List F)), qs.length = cs.length → qs'.length = cs.length →
    (List.zipWith (fun (ch : Chunk) q => (ch.H, ch.c, ch.m, q)) cs qs).map (fun p => (p.1, p.2.1)) =
      (List.zipWith (fun (ch : Chunk) q => (ch.H, ch.c, ch.m, q)) cs qs').map (fun p => (p.1, p.2.1))
  | [], _, _, _, _ => by simp only [List.zipWith_nil_left]
  | _ :: _, [], _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, h => nomatch h
  | ch :: cs, _ :: qs, _ :: qs', h, h' => by
    simp only [List.zipWith_cons_cons, List.map_cons]
    rw [chunksL_hc cs qs qs' (Nat.succ.inj h) (Nat.succ.inj h')]

theorem ppoly_allL (cs : List Chunk) (Hl : List F) (cl : F) {qs qs' : List (List F)} (ql ql' : List F)
    (h : qs.length = cs.length) (h' : qs'.length = cs.length) :
    rpoly.ppoly (allL cs Hl cl qs ql) = rpoly.ppoly (allL cs Hl cl qs' ql') := by
  refine ppoly_hc _ _ ?_
  unfold allL
  rw [List.map_append, List.map_append, chunksL_hc cs qs qs' h h']
  rfl

/-- **The targets see the chunk data only through its length.** -/
theorem airTg_qs (cs : List Chunk) (Hl : List F) (cl : F) {qs qs' : List (List F)} (ql ql' : List F) (κ : F)
    (H ws : List F) (es : List E) (ρv : F → Atom → F) (h : qs.length = cs.length) (h' : qs'.length = cs.length) :
    airTg cs Hl cl qs ql κ H ws es ρv = airTg cs Hl cl qs' ql' κ H ws es ρv := by
  funext x; unfold airTg; rw [ppoly_allL cs Hl cl ql ql' h h']

theorem airTgE_qs (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) {qs qs' : List (List F)} (ql ql' : List F) (κ : F)
    (H ws : List F) (es : List E) (ρE : Atom → EF) (h : qs.length = cs.length) (h' : qs'.length = cs.length) :
    airTgE ζ cs Hl cl qs ql κ H ws es ρE = airTgE ζ cs Hl cl qs' ql' κ H ws es ρE := by
  unfold airTgE; rw [ppoly_allL cs Hl cl ql ql' h h']

-- ---------------------------------------------------------------------------
-- Plumbing: one group's openings and masked columns
-- ---------------------------------------------------------------------------

/-- **A group's openings are of its masked columns**, with one slice `r`
    of the randomness for both. -/
theorem openMulti_at : ∀ (gs : List MGroup) (tss : List (List (List F))) (rs : List F) (i : Nat)
    (hg : i < gs.length) (ht : i < tss.length), ∃ r,
    (openMulti gs tss rs).getD i [] = openAll gs[i].T gs[i].R gs[i].S gs[i].Z gs[i].n tss[i] r ∧
    (mpolysMulti gs tss rs).getD i [] = mpolys gs[i].T gs[i].R gs[i].n tss[i] r
  | [], _, _, _, hg, _ => absurd hg (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, ht => absurd ht (Nat.not_lt_zero _)
  | g :: gs, ts :: tss, rs, 0, _, _ => ⟨rs.take (ts.length * g.n), rfl, rfl⟩
  | g :: gs, ts :: tss, rs, i + 1, hg, ht =>
    openMulti_at gs tss (rs.drop (ts.length * g.n)) i (Nat.lt_of_succ_lt_succ hg) (Nat.lt_of_succ_lt_succ ht)

theorem mpolys_getD_len (T R : List F) (n : Nat) : ∀ (ts : List (List F)) (rs : List F) (i : Nat),
    ((mpolys T R n ts rs).getD i []).length ≤ T.length + R.length
  | [], _, _ => Nat.zero_le _
  | t :: ts, rs, 0 => by
    show (mcol T R t (rs.take n)).length ≤ _
    unfold mcol
    refine Nat.le_trans (finterp_length _) ?_
    rw [List.length_append, List.length_zip, List.length_zip]
    exact Nat.add_le_add (Nat.min_le_left _ _) (Nat.min_le_left _ _)
  | _ :: ts, rs, i + 1 => mpolys_getD_len T R n ts (rs.drop n) i

-- ---------------------------------------------------------------------------
-- One coordinate's honest chunks show the targets read from the openings
-- ---------------------------------------------------------------------------

/-- **One coordinate of an AIR's quotient, from static facts**: a table
    that meets `Sat`, committed with masks and opened in one view, and
    honest chunks of its quotient on Plonky3's split domains with
    Plonky3's weights, show the targets read from the openings.  The
    targets take the chunk data only through its length, so the
    placeholder `cs.map (fun _ => [])` stands for it. -/
theorem coord_shows {A : AirD} {Tb : Table} {g : F} {m : Nat} (hsat : Sat A Tb) (hh : Tb.h = m + 1)
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hgd : ∀ c ∈ A.cons, c.guarded = true) {ts : List (List F)} (hwin : ∀ c ∈ A.cons, c.win ts.length = true)
    (hts : ∀ i (hi : i < ts.length), (ts[i]).length = m + 1 ∧ ∀ r (hr : r < (ts[i]).length), (ts[i])[r] = Tb.main r i)
    {R : List F} (hR : R.length ≤ m + 1) {nR : Nat} (hnd : (cosetL 1 g (m + 1) ++ R).Nodup) (rs : List F)
    (preP : Nat → List F) (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hpre : ∀ r i, r < m + 1 → fval (fpow g r) (preP i) = Tb.pre r i)
    {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    {cs : List Chunk} {Hl : List F} {cl κ : F} (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {k lq D s : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (k + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hD : ∀ e ∈ A.cons, e.pdeg ≤ D) (hDlq : D ≤ 2 ^ lq)
    (hsd : ∀ e ∈ A.cons, e.sdeg ≤ s) (hs : s < m + 1) (hPsz : D * (2 * (m + 1) - 1) + s + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (w : List F) :
    let ρ := stdRho g (fun i => (mpolys (cosetL 1 g (m + 1)) R nR ts rs).getD i []) preP (selF g m) (selL g m) (selT g m)
    let Qp := fdivH (cosetL 1 g (m + 1)) (cpoly ρ w A.cons)
    let os := openAll (cosetL 1 g (m + 1)) R (S ++ S.map (g * ·)) [ζ, (EF.ofF g).mul ζ] nR ts rs
    Shows S ζ cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)
      (airTg cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w A.cons (ρOpen S os preP g m))
      (airTgE ζ cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w A.cons (ρOpenE os preP g m ζ)) := by
  intro ρ Qp os
  have hHlen : (cosetL 1 g (m + 1)).length = m + 1 := cosetL_length 1 g (m + 1)
  -- the leaves' sizes
  have hρ : ∀ a, a ≠ .trans → (ρ a).length ≤ 2 * (m + 1) := fun a ha => by
    cases a with
    | main o i =>
      show (fshift (fpow g o) ((mpolys (cosetL 1 g (m + 1)) R nR ts rs).getD i [])).length ≤ 2 * (m + 1)
      rw [fshift_length]
      have := mpolys_getD_len (cosetL 1 g (m + 1)) R nR ts rs i
      omega
    | pre o i => show (fshift _ _).length ≤ _; rw [fshift_length]; exact hpreL i
    | first =>
      show (fvan (cosetL (1 * g) g m)).length ≤ _
      have := fvan_length (cosetL (1 * g) g m); rw [cosetL_length] at this; omega
    | last =>
      show (fvan (cosetL 1 g m)).length ≤ _
      have := fvan_length (cosetL 1 g m); rw [cosetL_length] at this; omega
    | trans => exact absurd rfl ha
  have ht : (ρ .trans).length ≤ 2 := Nat.le_refl 2
  have hP : (cpoly ρ w A.cons).length ≤ P :=
    Nat.le_trans (cpoly_plen ρ (2 * (m + 1) - 1) D s (fun a ha => by have := hρ a ha; omega) ht w A.cons hD hsd) hPsz
  -- `QuotOK` on Plonky3's split domains
  have hq : QuotOK cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp) κ Qp := by
    have hlenq : (cs.map fun ch => chunkOf ch.H Qp).length = cs.length := List.length_map _
    have hd := (allL_doms Hl cl (chunkOf Hl Qp) Qp cs).trans hdom
    have hnd' := split_nodup hshift hhalf hN
    rw [← hd] at hnd'
    have hcne : ∀ p ∈ allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp), p.2.1 ≠ 0 := fun p hp => by
      rcases mem_allL hp with ⟨ch, hch, _, e⟩ | ⟨_, e⟩
      · rw [e]; exact hc ch hch
      · rw [e]; exact hcl
    refine quotOK_split hκ hshift hhalf hN hdom ?_
      (first_of_cis κ (fpow ω (cs.length + 1)) m hκ _ hcne (dis_of_nodup _ hnd').2 (hw _ _ hlenq))
    have := quot_fits ρ (m + 1) D lq s hρ ht w A.cons hD hsd hs hDlq _ hHlen
    rw [hL]; exact this
  have hsh := shows_open hsat hh hg hinj hgd hwin hts hnd preP hpre hζ hc hcl w hP hS (fvalE_fvan_ne ζ hζ _) hq
  have hl1 : (cs.map fun ch => chunkOf ch.H Qp).length = cs.length := List.length_map _
  have hl2 : (cs.map fun (_ : Chunk) => ([] : List F)).length = cs.length := List.length_map _
  rw [airTg_qs cs Hl cl _ _ κ _ w A.cons _ hl1 hl2, airTgE_qs ζ cs Hl cl _ _ κ _ w A.cons _ hl1 hl2] at hsh
  exact hsh

-- ---------------------------------------------------------------------------
-- The table
-- ---------------------------------------------------------------------------

/-- **An AIR's quotient table**: one `CSet` per weight list (the four base
    coordinates of the folding challenge's powers), each with targets read
    from group `gi`'s openings. -/
def airQTab (A : AirD) (g : F) (m : Nat) (preP : Nat → List F) (gi : Nat) (κ : F) (cs : List Chunk) (Hl : List F)
    (cl : F) (S : List F) (ζ : EF) (ws : List (List F)) : QTab :=
  ⟨cs, Hl, cl, S, ζ, m + 1, ws.map fun w =>
    (fun _ _ _ o x => airTg cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w A.cons
        (ρOpen S (o.getD gi []) preP g m) x,
     fun _ _ _ o => airTgE ζ cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w A.cons
        (ρOpenE (o.getD gi []) preP g m ζ))⟩

/-- **Its honest data**: each coordinate's quotient, interpolated on every
    chunk domain, over the group's masked columns `mp`. -/
def airData (A : AirD) (g : F) (m : Nat) (preP : Nat → List F) (cs : List Chunk) (Hl : List F) (ws : List (List F))
    (mp : List (List F)) : List (List (List F) × List F) :=
  ws.map fun w =>
    let Qp := fdivH (cosetL 1 g (m + 1))
      (cpoly (stdRho g (fun i => mp.getD i []) preP (selF g m) (selL g m) (selT g m)) w A.cons)
    (cs.map fun ch => chunkOf ch.H Qp, chunkOf Hl Qp)

theorem recOK_air {A : AirD} {g : F} {m : Nat} {preP : Nat → List F} {gi : Nat} {κ : F} {cs : List Chunk}
    {Hl : List F} {cl : F} {S : List F} {ζ : EF} (α β : EF) (v : List EF) (o : List (List (List F × List EF)))
    (mp : List (List F))
    (h : ∀ w, Shows S ζ cs Hl cl (cs.map fun ch => chunkOf ch.H (fdivH (cosetL 1 g (m + 1))
        (cpoly (stdRho g (fun i => mp.getD i []) preP (selF g m) (selL g m) (selT g m)) w A.cons)))
      (chunkOf Hl (fdivH (cosetL 1 g (m + 1))
        (cpoly (stdRho g (fun i => mp.getD i []) preP (selF g m) (selL g m) (selT g m)) w A.cons)))
      (airTg cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w A.cons (ρOpen S (o.getD gi []) preP g m))
      (airTgE ζ cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w A.cons (ρOpenE (o.getD gi []) preP g m ζ))) :
    ∀ ws : List (List F), RecOK (airQTab A g m preP gi κ cs Hl cl S ζ ws).sets (airData A g m preP cs Hl ws mp)
      (fun c => c.JS α β v o) (fun c => c.Jζ α β v o)
  | [] => trivial
  | w :: ws => ⟨⟨List.length_map _, h w⟩, recOK_air α β v o mp h ws⟩

/-- **An AIR's quotient table is honest**, at every trace, challenge and
    mask: `TabsHonest` for `airQTab` with the data `airData` of group
    `gi`'s masked columns, from the circuit's `Sat` at each trace and
    static facts about the group, the domains and the weights. -/
theorem tabsHonest_air {A : AirD} {g : F} {m : Nat} {preP : Nat → List F} {gi : Nat} {κ : F} {cs : List Chunk}
    {Hl : List F} {cl : F} {S : List F} {ζ : EF} {ws : List (List F)}
    {qs : List QGroup} {cols : (Nat → Tup) → EF → EF → List (List (List F))} {R : List F} {nR : Nat}
    (hgi : gi < qs.length) (hcl' : ∀ t α β, gi < (cols t α β).length)
    (hT : (qs[gi]'hgi).base.T = cosetL 1 g (m + 1)) (hRq : (qs[gi]'hgi).base.R = R) (hSq : (qs[gi]'hgi).base.S = S)
    (hZq : (qs[gi]'hgi).base.Z = [ζ, (EF.ofF g).mul ζ]) (hnq : (qs[gi]'hgi).base.n = nR)
    (hnxt : (qs[gi]'hgi).nxt = (g * ·))
    (hsatT : ∀ t α β, ∃ Tb : Table, Sat A Tb ∧ Tb.h = m + 1 ∧
      (∀ c ∈ A.cons, c.win ((cols t α β)[gi]'(hcl' t α β)).length = true) ∧
      (∀ i (hi : i < ((cols t α β)[gi]'(hcl' t α β)).length),
        (((cols t α β)[gi]'(hcl' t α β))[i]).length = m + 1 ∧
        ∀ r (hr : r < (((cols t α β)[gi]'(hcl' t α β))[i]).length),
          (((cols t α β)[gi]'(hcl' t α β))[i])[r] = Tb.main r i) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = Tb.pre r i))
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hgd : ∀ c ∈ A.cons, c.guarded = true) (hR : R.length ≤ m + 1) (hnd : (cosetL 1 g (m + 1) ++ R).Nodup)
    (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {k lq D s : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (k + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hD : ∀ e ∈ A.cons, e.pdeg ≤ D) (hDlq : D ≤ 2 ^ lq)
    (hsd : ∀ e ∈ A.cons, e.sdeg ≤ s) (hs : s < m + 1) (hPsz : D * (2 * (m + 1) - 1) + s + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (hok : ∀ c ∈ (airQTab A g m preP gi κ cs Hl cl S ζ ws).sets, c.OK)
    (hHn : ∀ ch ∈ cs, ch.H.Nodup) (hHln : Hl.Nodup) :
    ∀ t α β ms (v : List EF), TabsHonest
      (fun c => c.JS α β v (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β v (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      [airQTab A g m preP gi κ cs Hl cl S ζ ws]
      [airData A g m preP cs Hl ws ((mpolysMulti (qs.map QGroup.ext) (cols t α β) ms).getD gi [])] := by
  intro t α β ms v
  have hgi' : gi < (qs.map QGroup.ext).length := by rw [List.length_map]; exact hgi
  obtain ⟨r, ho, hm⟩ := openMulti_at (qs.map QGroup.ext) (cols t α β) ms gi hgi' (hcl' t α β)
  have hext : (qs.map QGroup.ext)[gi]'hgi' = QGroup.ext (qs[gi]'hgi) := List.getElem_map ..
  rw [hext] at ho hm
  have eS : (QGroup.ext (qs[gi]'hgi)).S = S ++ S.map (g * ·) := by
    show (qs[gi]'hgi).base.S ++ (qs[gi]'hgi).base.S.map (qs[gi]'hgi).nxt = _
    rw [hSq, hnxt]
  have eT : (QGroup.ext (qs[gi]'hgi)).T = cosetL 1 g (m + 1) := hT
  have eR : (QGroup.ext (qs[gi]'hgi)).R = R := hRq
  have eZ : (QGroup.ext (qs[gi]'hgi)).Z = [ζ, (EF.ofF g).mul ζ] := hZq
  have en : (QGroup.ext (qs[gi]'hgi)).n = nR := hnq
  rw [eS, eT, eR, eZ, en] at ho
  rw [eT, eR, en] at hm
  obtain ⟨Tb, hsat, hh, hwin, hts, hpre⟩ := hsatT t α β
  -- the domains' sizes, from the split
  have hdl : ∀ H ∈ cs.map (·.H) ++ [Hl], H.length = m + 1 := fun H hH => by
    rw [hdom] at hH; exact split_length hH
  refine ⟨⟨hok, fun ch hch => ⟨hdl _ (List.mem_append_left _ (List.mem_map_of_mem hch)), hHn ch hch⟩,
    hdl _ (List.mem_append_right _ List.mem_cons_self), hHln, ?_, fun d hd => ?_⟩, trivial⟩
  · refine recOK_air α β _ _ _ (fun w => ?_) ws
    rw [ho, hm]
    exact coord_shows hsat hh hg hinj hgd hwin hts hR hnd r preP hpreL hpre hζ hS hc hcl hκ hshift hhalf hN hdom hL
      hD hDlq hsd hs hPsz hw w
  · obtain ⟨w, _, rfl⟩ := List.mem_map.1 hd
    refine ⟨fun q hq => ?_, ?_⟩
    · obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hq
      have := chunkOf_length ch.H (fdivH (cosetL 1 g (m + 1)) (cpoly (stdRho g
        (fun i => ((mpolysMulti (qs.map QGroup.ext) (cols t α β) ms).getD gi []).getD i []) preP (selF g m) (selL g m)
        (selT g m)) w A.cons))
      rw [hdl _ (List.mem_append_left _ (List.mem_map_of_mem hch))] at this
      exact this
    · have := chunkOf_length Hl (fdivH (cosetL 1 g (m + 1)) (cpoly (stdRho g
        (fun i => ((mpolysMulti (qs.map QGroup.ext) (cols t α β) ms).getD gi []).getD i []) preP (selF g m) (selL g m)
        (selT g m)) w A.cons))
      rw [hdl _ (List.mem_append_right _ List.mem_cons_self)] at this
      exact this

/-- **The composed hiding PCS with an AIR's quotient table**: `pcsCloseN_fri`
    at the table `airQTab` with the data `airData`, its `TabsHonest`
    discharged by `tabsHonest_air`. -/
theorem pcsCloseN_fri_air {V : Type} {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hokq : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (hdet : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    {A : AirD} {g : F} {m : Nat} {preP : Nat → List F} {gi : Nat} {κ : F} {cs : List Chunk}
    {Hl : List F} {cl : F} {S : List F} {ζ : EF} {ws : List (List F)} {R : List F} {nR : Nat}
    (hgi : gi < qs.length) (hcl' : ∀ t α β, gi < (cols t α β).length)
    (hT : (qs[gi]'hgi).base.T = cosetL 1 g (m + 1)) (hRq : (qs[gi]'hgi).base.R = R) (hSq : (qs[gi]'hgi).base.S = S)
    (hZq : (qs[gi]'hgi).base.Z = [ζ, (EF.ofF g).mul ζ]) (hnq : (qs[gi]'hgi).base.n = nR)
    (hnxt : (qs[gi]'hgi).nxt = (g * ·))
    (hsatT : ∀ t α β, ∃ Tb : Table, Sat A Tb ∧ Tb.h = m + 1 ∧
      (∀ c ∈ A.cons, c.win ((cols t α β)[gi]'(hcl' t α β)).length = true) ∧
      (∀ i (hi : i < ((cols t α β)[gi]'(hcl' t α β)).length),
        (((cols t α β)[gi]'(hcl' t α β))[i]).length = m + 1 ∧
        ∀ r (hr : r < (((cols t α β)[gi]'(hcl' t α β))[i]).length),
          (((cols t α β)[gi]'(hcl' t α β))[i])[r] = Tb.main r i) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = Tb.pre r i))
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hgd : ∀ c ∈ A.cons, c.guarded = true) (hR : R.length ≤ m + 1) (hnd : (cosetL 1 g (m + 1) ++ R).Nodup)
    (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {k lq D s : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (k + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hD : ∀ e ∈ A.cons, e.pdeg ≤ D) (hDlq : D ≤ 2 ^ lq)
    (hsd : ∀ e ∈ A.cons, e.sdeg ≤ s) (hs : s < m + 1) (hPsz : D * (2 * (m + 1) - 1) + s + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (hok : ∀ c ∈ (airQTab A g m preP gi κ cs Hl cl S ζ ws).sets, c.OK)
    (hHn : ∀ ch ∈ cs, ch.H.Nodup) (hHln : Hl.Nodup) :
    PCSCloseN off (P ^ (friN1 qs ks [airQTab A g m preP gi κ cs Hl cl S ζ ws] +
        friN2 qs [airQTab A g m preP gi κ cs Hl cl S ζ ws] ncw)) tv
      (pcsFri off tv qs ks cols [airQTab A g m preP gi κ cs Hl cl S ζ ws]
        (fun t α β ms => [airData A g m preP cs Hl ws ((mpolysMulti (qs.map QGroup.ext) (cols t α β) ms).getD gi [])])
        ncw αb fri)
      (psimFri qs ks [airQTab A g m preP gi κ cs Hl cl S ζ ws] ncw αb fri) 0 :=
  pcsCloseN_fri hokq hks hcols hdet haw hncw off tv (fun t α β ms =>
    tabsHonest_air hgi hcl' hT hRq hSq hZq hnq hnxt hsatT hg hinj hgd hR hnd hpreL hζ hS hc hcl hκ hshift hhalf hN
      hdom hL hD hDlq hsd hs hPsz hw hok hHn hHln t α β ms _)

/-- **Tables combine**: `TabsHonest` for each table alone gives it for the
    list, so a circuit with several AIRs discharges one `airQTab` per AIR,
    each by `tabsHonest_air`. -/
theorem tabsHonest_cons {JS : CSet → F → F} {JE : CSet → EF} {T : QTab} {d : List (List (List F) × List F)}
    {Ts : List QTab} {ds : List (List (List (List F) × List F))} (h : TabsHonest JS JE [T] [d])
    (hs : TabsHonest JS JE Ts ds) : TabsHonest JS JE (T :: Ts) (d :: ds) :=
  ⟨h.1, hs⟩

end Circuit
