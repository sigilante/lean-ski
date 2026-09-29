import Ski.Circuit.ProbeMem

/-!
# Completeness of the probe circuit

A run of `Air.AcceptsP` from a loaded term, over a memory whose cells fit
and whose plan's parents come before their children, gives tables the
probe circuit's AIRs accept (`probe_complete`).  The buses balance
(`PRun.balancedP`): off the probe rows the probe CPU sends what the jet
CPU sends, whose messages balance as in the jet circuit; the probe
messages balance bus by bus.
-/

namespace Circuit

open B Air JetTable Mach

theorem probeSends_off (ρ : Atom → F) {bus : String} (v : List F) (h1 : bus ≠ "plan") (h2 : bus ≠ "popch")
    (h3 : bus ≠ "mem") (h4 : bus ≠ "segend") (h5 : bus ≠ "arg") (h6 : bus ≠ "pwch") : probeSendsAt ρ bus v = 0 := by
  unfold probeSendsAt
  simp only [probeInters, List.foldr_cons, List.foldr_nil]
  rw [if_neg (fun h => h1 h.1.symm), if_neg (fun h => h1 h.1.symm), if_neg (fun h => h2 h.1.symm),
    if_neg (fun h => h2 h.1.symm), if_neg (fun h => h3 h.1.symm), if_neg (fun h => h4 h.1.symm),
    if_neg (fun h => h4 h.1.symm), if_neg (fun h => h5 h.1.symm), if_neg (fun h => h6 h.1.symm),
    if_neg (fun h => h6 h.1.symm), if_neg (fun h => h3 h.1.symm)]
  decide

theorem pw_buses : ∀ I ∈ pwAir.inters, I.bus = "pwch" ∨ I.bus = "mem" := by
  intro I hI
  simp only [pwAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inl rfl
  · exact .inr rfl
  · exact .inr rfl

theorem sum_zero2 {a b c d : F} (h1 : a + c = 0) (h2 : b + d = 0) : (a + b) + (c + d) = 0 := by
  rw [show (a + b) + (c + d) = (a + c) + (b + d) from
    E.eval_eq_of_norm
      (e := .add (.add (.atom (.main 0 0)) (.atom (.main 0 1))) (.add (.atom (.main 0 2)) (.atom (.main 0 3))))
      (e' := .add (.add (.atom (.main 0 0)) (.atom (.main 0 2))) (.add (.atom (.main 0 1)) (.atom (.main 0 3))))
      (by decide) (at4 a b c d), h1, h2]
  decide

theorem sum_zero3 {a b c d e : F} (h1 : a + (c + e) = 0) (h2 : b + d = 0) : (a + b) + ((c + d) + e) = 0 := by
  rw [show (a + b) + ((c + d) + e) = (a + (c + e)) + (b + d) from
    E.eval_eq_of_norm
      (e := .add (.add (.atom (.main 0 0)) (.atom (.main 0 1))) (.add (.add (.atom (.main 0 2)) (.atom (.main 0 3)))
        (.atom (.main 0 4))))
      (e' := .add (.add (.atom (.main 0 0)) (.add (.atom (.main 0 2)) (.atom (.main 0 4))))
        (.add (.atom (.main 0 1)) (.atom (.main 0 3))))
      (by decide) (at5 a b c d e), h1, h2]
  decide

namespace PRun

variable {R : PRun} {t : Term} (hA : AcceptsP R.A (load t) R.roots R.jets R.plan R.p R.fld R.row)
  (hroots : RootsOK (load t).heap R.roots R.jets)
include hA hroots

/-- **The honest probe tables balance.** -/
theorem balancedP (hpar : ∀ c, 0 < c → c < R.n → (R.seg c).parent < c)
    (hlast : (R.seg (R.n - 1)).arity = 0) (la : Nat) {heap : List Cell}
    (hpre : R.A.take heap.length = heap) (hML : R.A.length < P) {K HP HW HX : Nat} (hK : R.last < K)
    (hHP : (R.popRowsP K).length ≤ HP) (hHW : (R.J.instwRows K).length ≤ HW) (hHX : (R.pwRows K).length ≤ HX) :
    Balanced (probeTables (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n la heap R.roots R.jets R.plan
      (R.cpuTableP K)
      (memTable5 R.A (cpuAirP (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n la) (progAir heap) popAir instwAir pwAir
        (R.cpuTableP K) (progTable heap) (R.popTableP K HP) (R.J.instwTable K HW) (R.pwTable K HX))
      (progTable heap) (provTable (rootsRows R.roots) (R.J.cntRoots K)) (provTable (hdrRows R.jets) (R.J.cntHdr K))
      (provTable (tmplRows R.jets) (R.J.cntTmpl K)) (R.popTableP K HP) (R.J.instwTable K HW)
      (provTable (planRows R.plan) (R.cntPlan K)) (R.pwTable K HX)) := by
  intro bus v
  simp only [probeTables, List.foldr_cons, List.foldr_nil, add_zero']
  have rt : rootsAir R.roots = providerAir "roots" 2 (rootsRows R.roots) := rfl
  have hd : hdrAir R.jets = providerAir "hdr" 7 (hdrRows R.jets) := rfl
  have tm : tmplAir R.jets = providerAir "tmpl" 11 (tmplRows R.jets) := rfl
  have pl : planAir R.plan = providerAir "plan" 7 (planRows R.plan) := rfl
  have zM : ∀ (T : Table), bus ≠ "mem" → tableSends memAir T bus v = 0 :=
    fun T h => sends_off (one_bus mem_bus (Ne.symm h))
  have zP : ∀ (T : Table), bus ≠ "mem" → tableSends (progAir heap) T bus v = 0 :=
    fun T h => sends_off (one_bus (prog_bus heap) (Ne.symm h))
  have zR : ∀ (T : Table), bus ≠ "roots" → tableSends (rootsAir R.roots) T bus v = 0 :=
    fun T h => by rw [rt]; exact sends_off (one_bus (prov_bus _ _ _) (Ne.symm h))
  have zH : ∀ (T : Table), bus ≠ "hdr" → tableSends (hdrAir R.jets) T bus v = 0 :=
    fun T h => by rw [hd]; exact sends_off (one_bus (prov_bus _ _ _) (Ne.symm h))
  have zT : ∀ (T : Table), bus ≠ "tmpl" → tableSends (tmplAir R.jets) T bus v = 0 :=
    fun T h => by rw [tm]; exact sends_off (one_bus (prov_bus _ _ _) (Ne.symm h))
  have zL : ∀ (T : Table), bus ≠ "plan" → tableSends (planAir R.plan) T bus v = 0 :=
    fun T h => by rw [pl]; exact sends_off (one_bus (prov_bus _ _ _) (Ne.symm h))
  have zO : ∀ (T : Table), bus ≠ "popch" → bus ≠ "mem" → bus ≠ "arg" → tableSends popAir T bus v = 0 :=
    fun T h1 h2 h3 => sends_off (off3 pop_buses (Ne.symm h1) (Ne.symm h2) (Ne.symm h3))
  have zW : ∀ (T : Table), bus ≠ "arg" → bus ≠ "wch" → bus ≠ "tmpl" → bus ≠ "mem" →
      tableSends instwAir T bus v = 0 :=
    fun T h1 h2 h3 h4 => sends_off (off4 instw_buses (Ne.symm h1) (Ne.symm h2) (Ne.symm h3) (Ne.symm h4))
  have zX : ∀ (T : Table), bus ≠ "pwch" → bus ≠ "mem" → tableSends pwAir T bus v = 0 :=
    fun T h1 h2 => sends_off (fun I hI e => by
      rcases pw_buses I hI with h | h
      · exact h1 (e.symm.trans h)
      · exact h2 (e.symm.trans h))
  have zJ : ∀ (T : Table), bus ≠ "mem" → bus ≠ "roots" → bus ≠ "hdr" → bus ≠ "popch" → bus ≠ "wch" →
      bus ≠ "arg" → tableSends (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) T bus v = 0 :=
    fun T h1 h2 h3 h4 h5 h6 => sends_off (off6 (cpuJ_buses _ _ _) (Ne.symm h1) (Ne.symm h2) (Ne.symm h3)
      (Ne.symm h4) (Ne.symm h5) (Ne.symm h6))
  have zQ : bus ≠ "plan" → bus ≠ "popch" → bus ≠ "mem" → bus ≠ "segend" → bus ≠ "arg" → bus ≠ "pwch" →
      (List.range K).foldr (fun i acc => probeSendsAt ((R.cpuTableP K).env i) bus v + acc) 0 = 0 :=
    fun h1 h2 h3 h4 h5 h6 => foldr_zero_all _ _ (fun i _ => probeSends_off _ v h1 h2 h3 h4 h5 h6)
  have zPP : bus ≠ "popch" → bus ≠ "mem" → bus ≠ "arg" →
      (List.range K).foldr (fun i acc => ((R.probePops i).map (rowSendsV popAir bus v)).foldr (· + ·) 0 + acc) 0 = 0 :=
    fun h1 h2 h3 => foldr_zero_all _ _ (fun i _ => by
      have z : ∀ l : List (List F), (l.map (rowSendsV popAir bus v)).foldr (· + ·) 0 = 0 := by
        intro l
        induction l with
        | nil => rfl
        | cons rw l ih =>
          rw [List.map_cons, List.foldr_cons, ih, add_zero']
          simp only [rowSendsV, popAir, popInters, List.foldr_cons, List.foldr_nil]
          rw [if_neg (fun h => h1 h.1.symm), if_neg (fun h => h1 h.1.symm), if_neg (fun h => h2 h.1.symm),
            if_neg (fun h => h3 h.1.symm)]
          decide
      exact z _)
  have split := fun (h : bus ≠ "mem") => cpuP_split hA (K := K) h v (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n la
  have pop := popP_split (R := R) hHP bus v
  rcases (inferInstance : Decidable (bus = "mem")) with hm | hm
  · rw [split hm, pop]
    rcases (inferInstance : Decidable (bus = "roots")) with hr | hr
    · rcases (inferInstance : Decidable (bus = "hdr")) with hh | hh
      · rcases (inferInstance : Decidable (bus = "tmpl")) with ht | ht
        · rcases (inferInstance : Decidable (bus = "popch")) with hp | hp
          · rcases (inferInstance : Decidable (bus = "wch")) with hw | hw
            · rcases (inferInstance : Decidable (bus = "arg")) with ha | ha
              · rcases (inferInstance : Decidable (bus = "plan")) with hl | hl
                · rcases (inferInstance : Decidable (bus = "segend")) with hg | hg
                  · rcases (inferInstance : Decidable (bus = "pwch")) with hx | hx
                    · rw [zJ _ hm hr hh hp hw ha, zQ hl hp hm hg ha hx, zM _ hm, zP _ hm, zR _ hr, zH _ hh, zT _ ht,
                        zO _ hp hm ha, zPP hp hm ha, zW _ ha hw ht hm, zL _ hl, zX _ hx hm]
                      decide
                    · subst hx
                      rw [zJ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), zero_add',
                        zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide), zT _ (by decide),
                        zO _ (by decide) (by decide) (by decide), zPP (by decide) (by decide) (by decide),
                        zW _ (by decide) (by decide) (by decide) (by decide), zL _ (by decide)]
                      simp only [zero_add']
                      exact bal_pwch hA hK hHX v
                  · subst hg
                    rw [zJ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), zero_add',
                      zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide), zT _ (by decide),
                      zO _ (by decide) (by decide) (by decide), zPP (by decide) (by decide) (by decide),
                      zW _ (by decide) (by decide) (by decide) (by decide), zL _ (by decide),
                      zX _ (by decide) (by decide)]
                    simp only [zero_add', add_zero']
                    exact bal_segend hA hpar hK v
                · subst hl
                  rw [zJ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), zero_add',
                    zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide), zT _ (by decide),
                    zO _ (by decide) (by decide) (by decide), zPP (by decide) (by decide) (by decide),
                    zW _ (by decide) (by decide) (by decide) (by decide), zX _ (by decide) (by decide)]
                  simp only [zero_add', add_zero']
                  exact bal_plan hA hK v
              · subst ha
                rw [zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide), zT _ (by decide),
                  zL _ (by decide), zX _ (by decide) (by decide)]
                simp only [zero_add', add_zero']
                exact sum_zero3 (R.J.bal_arg (HP := (R.J.popRows K).length) (Nat.le_refl _) hHW v)
                  (bal_arg_probe hA hpar hK v)
            · subst hw
              rw [zQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), add_zero',
                zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide), zT _ (by decide),
                zO _ (by decide) (by decide) (by decide), zPP (by decide) (by decide) (by decide),
                zL _ (by decide), zX _ (by decide) (by decide)]
              simp only [zero_add', add_zero']
              exact R.J.bal_wch hHW v
          · subst hp
            rw [zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide), zT _ (by decide),
              zW _ (by decide) (by decide) (by decide) (by decide), zL _ (by decide),
              zX _ (by decide) (by decide)]
            simp only [zero_add', add_zero']
            exact sum_zero2 (R.J.bal_popch (HP := (R.J.popRows K).length) (Nat.le_refl _) v)
              (bal_popch_probe hA hroots hK v)
        · subst ht
          rw [zJ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), zero_add',
            zQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide),
            zO _ (by decide) (by decide) (by decide), zPP (by decide) (by decide) (by decide),
            zL _ (by decide), zX _ (by decide) (by decide)]
          simp only [zero_add', add_zero']
          rw [add_comm']
          exact R.J.bal_tmpl hHW v
      · subst hh
        rw [zQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), add_zero',
          zM _ (by decide), zP _ (by decide), zR _ (by decide), zT _ (by decide),
          zO _ (by decide) (by decide) (by decide), zPP (by decide) (by decide) (by decide),
          zW _ (by decide) (by decide) (by decide) (by decide), zL _ (by decide), zX _ (by decide) (by decide)]
        simp only [zero_add', add_zero']
        exact R.J.bal_hdr v
    · subst hr
      rw [zQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), add_zero',
        zM _ (by decide), zP _ (by decide), zH _ (by decide), zT _ (by decide),
        zO _ (by decide) (by decide) (by decide), zPP (by decide) (by decide) (by decide),
        zW _ (by decide) (by decide) (by decide) (by decide), zL _ (by decide), zX _ (by decide) (by decide)]
      simp only [zero_add', add_zero']
      exact R.J.bal_roots v
  · subst hm
    rw [zR _ (by decide), zH _ (by decide), zT _ (by decide), zL _ (by decide)]
    simp only [zero_add']
    exact bal_mem5 hML (cpu_honestP hA hroots hK hlast la) (fun r hr I hI _ hc => prog_honest hpre r hr I hI hc)
      (pop_honestP hA hroots) (fun r hr I hI hb hc => R.J.instw_honest r hr I hI hb hc) (pw_honest hA hroots) v

end PRun

-- ---------------------------------------------------------------------------
-- The theorem
-- ---------------------------------------------------------------------------

open Mach Term

/-- **Completeness of the probe circuit.**  A run of the AIR with probe
    segments from a loaded term, for a plan whose parents come before their
    children and whose last segment has no fields, over a memory whose cells
    fit and whose tables fit the verifier's bounds (`2^21` rows each), gives
    tables that AIRs with the probe circuit's normal forms accept, with
    Plonky3's selectors; the memory and the rows' registers are the run's.
    The jet table must have rows, and the first row's stack is the loaded
    term's (a probe row ignores it). -/
theorem probe_complete {t : Term} {roots : List (Nat × Nat)} {jets : List Air.Jet} {plan : List Air.Seg}
    {Rs : List AirD} (hs : sameAirsB Rs (probeAirs t roots jets plan) = true)
    (hroots : RootsOK (load t).heap roots jets)
    (hprov : 0 < (rootsRows roots).length ∧ 0 < (hdrRows jets).length ∧ 0 < (tmplRows jets).length)
    (hprov27 : (rootsRows roots).length ≤ 2 ^ 27 ∧ (hdrRows jets).length ≤ 2 ^ 27 ∧
      (tmplRows jets).length ≤ 2 ^ 27 ∧ (planRows plan).length ≤ 2 ^ 27)
    (hpar : ∀ c s, 0 < c → plan[c]? = some s → s.parent < c)
    (hlast : ∀ s, plan.getLast? = some s → s.arity = 0)
    {A : List Cell} {p : Nat → Nat} {fld : Nat → List Nat} {row : Nat → Air.Row}
    (hA : AcceptsP A (load t) roots jets plan p fld row) (hstk0 : (row 0).stk = (load t).stk)
    (hfit : Fits A) (hlen : A.length ≤ 2 ^ 21)
    {K HP HW HX : Nat} (hK : p plan.length < K) (hK21 : K ≤ 2 ^ 21)
    (hHP : (PRun.popRowsP ⟨A, roots, jets, plan, p, fld, row⟩ K).length ≤ HP) (hHP0 : 0 < HP) (hHP21 : HP ≤ 2 ^ 21)
    (hHW : (JRun.instwRows (PRun.J ⟨A, roots, jets, plan, p, fld, row⟩) K).length ≤ HW) (hHW0 : 0 < HW)
    (hHW21 : HW ≤ 2 ^ 21)
    (hHX : (PRun.pwRows ⟨A, roots, jets, plan, p, fld, row⟩ K).length ≤ HX) (hHX0 : 0 < HX) (hHX21 : HX ≤ 2 ^ 21) :
    ∃ C Mm Pg Rt Hd Tm Po Iw Pl Pw, AcceptedP Rs [C, Mm, Pg, Rt, Hd, Tm, Po, Iw, Pl, Pw] ∧ C.h = K ∧
      Mm.h = A.length ∧ Po.h = HP ∧ Iw.h = HW ∧ Pw.h = HX ∧ memOf Mm = A ∧
      ∀ i, i ≤ p plan.length →
        C.main i HD = ofN (row i).hd ∧ C.main i STK = ofN (row i).stk ∧ C.main i CTR = ofN (row i).ctr := by
  let R : PRun := ⟨A, roots, jets, plan, p, fld, row⟩
  have hA' : AcceptsP R.A (load t) R.roots R.jets R.plan R.p R.fld R.row := hA
  have hn0 : 0 < R.n := hA.nonempty
  obtain ⟨_, hhd, hstk⟩ := load_fits t
  have hpre : A.take (load t).heap.length = (load t).heap := by rw [← hA.ctr0]; exact hA.heap0
  have hhl : (load t).heap.length ≤ A.length := by
    have := congrArg List.length hpre; rw [List.length_take] at this; omega
  have hA0 : 0 < A.length := by omega
  have hPP : P = 2013265921 := rfl
  have e1 : (row 0).hd = (load t).hd := hA.hd0
  have e3 : (row 0).ctr = (load t).heap.length := hA.ctr0
  have hl24 : R.A.length ≤ 2 ^ 24 := Nat.le_trans (show A.length ≤ 2 ^ 21 from hlen) (by decide)
  -- the plan's facts, as the run reads them
  have hpar' : ∀ c, 0 < c → c < R.n → (R.seg c).parent < c := fun c h0 hc => hpar c _ h0 (PRun.seg_get hA' hc)
  have hsl : plan.getLast? = some (R.seg (R.n - 1)) := by
    rw [List.getLast?_eq_getElem?]; exact PRun.seg_get hA' (Nat.sub_lt hn0 Nat.one_pos)
  have hlast' : (R.seg (R.n - 1)).arity = 0 := hlast _ hsl
  have hla : lastAtom plan = (R.seg (R.n - 1)).ctor + (R.seg (R.n - 1)).base := by
    unfold lastAtom; rw [hsl]; rfl
  have hKl : R.last < K := hK
  -- the tables
  let C := R.cpuTableP K
  let Pg := progTable (load t).heap
  let Po := R.popTableP K HP
  let Iw := R.J.instwTable K HW
  let Pw := R.pwTable K HX
  let Rt := provTable (rootsRows roots) (R.J.cntRoots K)
  let Hd := provTable (hdrRows jets) (R.J.cntHdr K)
  let Tm := provTable (tmplRows jets) (R.J.cntTmpl K)
  let Pl := provTable (planRows plan) (R.cntPlan K)
  let Mm := memTable5 A (cpuAirP (row 0).hd (row 0).stk (row 0).ctr plan.length (lastAtom plan)) (progAir (load t).heap)
    popAir instwAir pwAir C Pg Po Iw Pw
  have hPg : Pg.h ≤ 2 ^ 24 := programRows_length_le (by omega)
  have hcpu : Sat (cpuAirP (row 0).hd (row 0).stk (row 0).ctr plan.length (lastAtom plan)) C :=
    PRun.cpu_satP hA' hroots hKl hl24 hlast' hla
  have hbal := PRun.balancedP hA' hroots hpar' hlast' (lastAtom plan) hpre (show A.length < P by omega) hKl hHP hHW hHX
  have hpl0 : 0 < (planRows plan).length := by
    have := padCopies_length_ge (plan.zipIdx.map fun (s, j) =>
      [ofN j, ofN s.base, ofN s.k, ofN s.ctor, ofN s.arity, ofN s.parent, ofN s.field])
    rw [List.length_map, List.length_zipIdx] at this
    exact Nat.lt_of_lt_of_le hn0 this
  have hacc : Accepted (probeAirs t roots jets plan) [C, Mm, Pg, Rt, Hd, Tm, Po, Iw, Pl, Pw] := by
    have z : (probeAirs t roots jets plan).zip [C, Mm, Pg, Rt, Hd, Tm, Po, Iw, Pl, Pw] =
        probeTables (row 0).hd (row 0).stk (row 0).ctr plan.length (lastAtom plan) (load t).heap roots jets plan
          C Mm Pg Rt Hd Tm Po Iw Pl Pw := by
      rw [e1, hstk0, e3]; rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [z]
      intro q hq
      simp only [probeTables, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hcpu, .inl rfl⟩
      · exact ⟨mem5_sat A _ _ _ _ _ _ _ _ _ _ hA0, .inl rfl⟩
      · exact ⟨(prog_sat _ (by omega)).1, .inr (prog_sat _ (by omega)).2⟩
      · exact ⟨(prov_sat hprov.1).1, .inr (prov_sat hprov.1).2⟩
      · exact ⟨(prov_sat hprov.2.1).1, .inr (prov_sat hprov.2.1).2⟩
      · exact ⟨(prov_sat hprov.2.2).1, .inr (prov_sat hprov.2.2).2⟩
      · exact ⟨PRun.pop_satP hA' hroots hl24 hHP0, .inl rfl⟩
      · exact ⟨R.J.instw_sat hHW0, .inl rfl⟩
      · exact ⟨(prov_sat hpl0).1, .inr (prov_sat hpl0).2⟩
      · exact ⟨PRun.pw_satP hHX0, .inl rfl⟩
    · rw [z]; exact hbal
    · rw [z]
      unfold HeightsOK probeTables
      simp only [List.foldr_cons, List.foldr_nil]
      show 25 * K + (0 * A.length + (1 * Pg.h + (0 * Rt.h + (0 * Hd.h + (0 * Tm.h + (3 * HP + (6 * HW +
        (0 * Pl.h + (4 * HX + 0))))))))) < P
      omega
    · rw [z]
      intro q hq
      simp only [probeTables, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show K ≤ 2 ^ 27; omega
      · show A.length ≤ 2 ^ 27; omega
      · show Pg.h ≤ 2 ^ 27; omega
      · exact hprov27.1
      · exact hprov27.2.1
      · exact hprov27.2.2.1
      · show HP ≤ 2 ^ 27; omega
      · show HW ≤ 2 ^ 27; omega
      · exact hprov27.2.2.2
      · show HX ≤ 2 ^ 27; omega
  have hRs : AcceptedP Rs [C, Mm, Pg, Rt, Hd, Tm, Po, Iw, Pl, Pw] :=
    (acceptedP_iff_of (probe_guarded t roots jets plan) hs _).2 (accepted_transfer (sameAirsB_symm hs) hacc)
  refine ⟨C, Mm, Pg, Rt, Hd, Tm, Po, Iw, Pl, Pw, hRs, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · -- the memory decodes back
    apply List.ext_getElem?
    intro m
    unfold memOf
    rw [List.getElem?_map]
    rcases Nat.lt_or_ge m Mm.h with hm | hm
    · rw [List.getElem?_range hm, Option.map_some]
      have hm' : m < A.length := hm
      have hg : A.getD m .nil = A[m] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm']; rfl
      have hf := hfit _ (List.getElem_mem hm')
      show some (cellOf (ofN (cellTag (A.getD m .nil))) (ofN (cellFields (A.getD m .nil)).1)
        (ofN (cellFields (A.getD m .nil)).2)) = _
      rw [hg, cellOf_enc _ (by omega) (by omega), List.getElem?_eq_getElem hm']
    · rw [List.getElem?_eq_none (by rw [List.length_range]; exact hm), List.getElem?_eq_none hm]; rfl
  · -- the registers are the run's
    intro i hi
    have hq : R.J.rowQ i = row i := JRun.rowQ_lt (show i < R.last + 1 from Nat.lt_succ_of_le hi)
    have cr : ∀ c, c < 3 → C.main i c = Circuit.cpuCol A (row i) c := by
      intro c hc3
      show R.cpuColP K i c = _
      rw [PRun.regP hA' hc3, hq]
    exact ⟨cr HD (by decide), cr STK (by decide), cr CTR (by decide)⟩

end Circuit
