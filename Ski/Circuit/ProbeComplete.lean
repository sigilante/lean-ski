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

end Circuit
#print axioms Circuit.PRun.balancedP
