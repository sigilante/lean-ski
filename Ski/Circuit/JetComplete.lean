import Ski.Circuit.JetBal

/-!
# Completeness of the jet circuit

A run of `Air.AcceptsJ` from a loaded term, over a memory whose cells
point into it, within the jet verifier's heights, gives honest tables
that AIRs with the jet circuit's normal forms accept, with Plonky3's
selectors; they decode back to the memory and the run (`jet_complete`).
-/

namespace Circuit

open B Air JetTable Mach

theorem sends_off {X : AirD} {T : Table} {bus : String} {v : List F} (h : ∀ I ∈ X.inters, I.bus ≠ bus) :
    tableSends X T bus v = 0 :=
  fold_zero _ _ (fun _ _ => rowSends_nobus h)

theorem cpuJ_buses (hd0 stk0 ctr0 : Nat) : ∀ I ∈ (cpuAirJ hd0 stk0 ctr0).inters,
    I.bus = "mem" ∨ I.bus = "roots" ∨ I.bus = "hdr" ∨ I.bus = "popch" ∨ I.bus = "wch" ∨ I.bus = "arg" := by
  have h : (cpuAirJ hd0 stk0 ctr0).inters.all (fun I => I.bus == "mem" || I.bus == "roots" || I.bus == "hdr" ||
      I.bus == "popch" || I.bus == "wch" || I.bus == "arg") = true := rfl
  intro I hI
  have := List.all_eq_true.1 h I hI
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with (((((h | h) | h) | h) | h) | h) <;> simp only [h, true_or, or_true]

theorem pop_buses : ∀ I ∈ popAir.inters, I.bus = "popch" ∨ I.bus = "mem" ∨ I.bus = "arg" := by
  intro I hI
  simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem instw_buses : ∀ I ∈ instwAir.inters, I.bus = "arg" ∨ I.bus = "wch" ∨ I.bus = "tmpl" ∨ I.bus = "mem" := by
  intro I hI
  simp only [instwAir, instwInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))

theorem one_bus {X : AirD} {b : String} (h : ∀ I ∈ X.inters, I.bus = b) {bus : String} (hb : b ≠ bus) :
    ∀ I ∈ X.inters, I.bus ≠ bus := fun I hI e => hb (by rw [← h I hI, e])

theorem off3 {X : AirD} {a b c bus : String} (h : ∀ I ∈ X.inters, I.bus = a ∨ I.bus = b ∨ I.bus = c)
    (ha : a ≠ bus) (hb : b ≠ bus) (hc : c ≠ bus) : ∀ I ∈ X.inters, I.bus ≠ bus := by
  intro I hI e
  rcases h I hI with h | h | h
  · exact ha (h ▸ e)
  · exact hb (h ▸ e)
  · exact hc (h ▸ e)

theorem off4 {X : AirD} {a b c d bus : String} (h : ∀ I ∈ X.inters, I.bus = a ∨ I.bus = b ∨ I.bus = c ∨ I.bus = d)
    (ha : a ≠ bus) (hb : b ≠ bus) (hc : c ≠ bus) (hd : d ≠ bus) : ∀ I ∈ X.inters, I.bus ≠ bus := by
  intro I hI e
  rcases h I hI with h | h | h | h
  · exact ha (h ▸ e)
  · exact hb (h ▸ e)
  · exact hc (h ▸ e)
  · exact hd (h ▸ e)

theorem off6 {X : AirD} {a b c d f g bus : String}
    (h : ∀ I ∈ X.inters, I.bus = a ∨ I.bus = b ∨ I.bus = c ∨ I.bus = d ∨ I.bus = f ∨ I.bus = g)
    (ha : a ≠ bus) (hb : b ≠ bus) (hc : c ≠ bus) (hd : d ≠ bus) (hf : f ≠ bus) (hg : g ≠ bus) :
    ∀ I ∈ X.inters, I.bus ≠ bus := by
  intro I hI e
  rcases h I hI with h | h | h | h | h | h
  · exact ha (h ▸ e)
  · exact hb (h ▸ e)
  · exact hc (h ▸ e)
  · exact hd (h ▸ e)
  · exact hf (h ▸ e)
  · exact hg (h ▸ e)

theorem mem_bus : ∀ I ∈ memAir.inters, I.bus = "mem" := by
  intro I hI; simp only [memAir, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]
theorem prog_bus (heap : List Cell) : ∀ I ∈ (progAir heap).inters, I.bus = "mem" := by
  intro I hI; simp only [progAir, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]
theorem prov_bus (name : String) (w : Nat) (rows : List (List F)) : ∀ I ∈ (providerAir name w rows).inters, I.bus = name := by
  intro I hI; simp only [providerAir, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]

namespace JRun

variable (R : JRun)

/-- **The honest jet tables balance.** -/
theorem balanced {m0 : Mach} (hA : AcceptsJ R.A m0 R.roots R.jets R.k R.row) {heap : List Cell}
    (hpre : R.A.take heap.length = heap) (hML : R.A.length < P) {K HP HW : Nat}
    (hHP : (R.popRows K).length ≤ HP) (hHW : (R.instwRows K).length ≤ HW) :
    Balanced (jetTables (R.row 0).hd (R.row 0).stk (R.row 0).ctr heap R.roots R.jets (R.cpuTable K)
      (memTableJ R.A (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (progAir heap) popAir instwAir
        (R.cpuTable K) (progTable heap) (R.popTable K HP) (R.instwTable K HW))
      (progTable heap) (provTable (rootsRows R.roots) (R.cntRoots K)) (provTable (hdrRows R.jets) (R.cntHdr K))
      (provTable (tmplRows R.jets) (R.cntTmpl K)) (R.popTable K HP) (R.instwTable K HW)) := by
  intro bus v
  simp only [jetTables, List.foldr_cons, List.foldr_nil, add_zero']
  have rt : rootsAir R.roots = providerAir "roots" 2 (rootsRows R.roots) := rfl
  have hd : hdrAir R.jets = providerAir "hdr" 7 (hdrRows R.jets) := rfl
  have tm : tmplAir R.jets = providerAir "tmpl" 11 (tmplRows R.jets) := rfl
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
  have zO : ∀ (T : Table), bus ≠ "popch" → bus ≠ "mem" → bus ≠ "arg" → tableSends popAir T bus v = 0 :=
    fun T h1 h2 h3 => sends_off (off3 pop_buses (Ne.symm h1) (Ne.symm h2) (Ne.symm h3))
  have zW : ∀ (T : Table), bus ≠ "arg" → bus ≠ "wch" → bus ≠ "tmpl" → bus ≠ "mem" →
      tableSends instwAir T bus v = 0 :=
    fun T h1 h2 h3 h4 => sends_off (off4 instw_buses (Ne.symm h1) (Ne.symm h2) (Ne.symm h3) (Ne.symm h4))
  have zC : ∀ (T : Table), bus ≠ "mem" → bus ≠ "roots" → bus ≠ "hdr" → bus ≠ "popch" → bus ≠ "wch" →
      bus ≠ "arg" → tableSends (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) T bus v = 0 :=
    fun T h1 h2 h3 h4 h5 h6 => sends_off (off6 (cpuJ_buses _ _ _) (Ne.symm h1) (Ne.symm h2) (Ne.symm h3)
      (Ne.symm h4) (Ne.symm h5) (Ne.symm h6))
  rcases (inferInstance : Decidable (bus = "mem")) with hm | hm
  · rcases (inferInstance : Decidable (bus = "roots")) with hr | hr
    · rcases (inferInstance : Decidable (bus = "hdr")) with hh | hh
      · rcases (inferInstance : Decidable (bus = "tmpl")) with ht | ht
        · rcases (inferInstance : Decidable (bus = "popch")) with hp | hp
          · rcases (inferInstance : Decidable (bus = "wch")) with hw | hw
            · rcases (inferInstance : Decidable (bus = "arg")) with ha | ha
              · rw [zC _ hm hr hh hp hw ha, zM _ hm, zP _ hm, zR _ hr, zH _ hh, zT _ ht, zO _ hp hm ha,
                  zW _ ha hw ht hm]
                decide
              · subst ha
                rw [zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide), zT _ (by decide),
                  zero_add', zero_add', zero_add', zero_add', zero_add']
                exact R.bal_arg hA hHP hHW v
            · subst hw
              rw [zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide), zT _ (by decide),
                zO _ (by decide) (by decide) (by decide), zero_add', zero_add', zero_add', zero_add', zero_add',
                zero_add']
              exact R.bal_wch hA hHW v
          · subst hp
            rw [zM _ (by decide), zP _ (by decide), zR _ (by decide), zH _ (by decide), zT _ (by decide),
              zW _ (by decide) (by decide) (by decide) (by decide), zero_add', zero_add', zero_add', zero_add',
              zero_add', add_zero']
            exact R.bal_popch hA hHP v
        · subst ht
          rw [zC _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), zM _ (by decide),
            zP _ (by decide), zR _ (by decide), zH _ (by decide), zO _ (by decide) (by decide) (by decide),
            zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', add_comm']
          exact R.bal_tmpl hHW v
      · subst hh
        rw [zM _ (by decide), zP _ (by decide), zR _ (by decide), zT _ (by decide),
          zO _ (by decide) (by decide) (by decide), zW _ (by decide) (by decide) (by decide) (by decide),
          zero_add', zero_add', zero_add', add_zero', add_zero', add_zero']
        exact R.bal_hdr hA v
    · subst hr
      rw [zM _ (by decide), zP _ (by decide), zH _ (by decide), zT _ (by decide),
        zO _ (by decide) (by decide) (by decide), zW _ (by decide) (by decide) (by decide) (by decide),
        zero_add', zero_add', add_zero', add_zero', add_zero', add_zero']
      exact R.bal_roots hA v
  · subst hm
    rw [zR _ (by decide), zH _ (by decide), zT _ (by decide), zero_add', zero_add', zero_add']
    exact bal_mem4 hML (cpu := cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (C := R.cpuTable K)
      (fun r hr I hI hb hc => R.cpu_honestJ hA r hr I hI hb hc)
      (fun r hr I hI _ hc => prog_honest hpre r hr I hI hc)
      (fun r hr I hI hb hc => R.pop_honest r hr I hI hb hc)
      (fun r hr I hI hb hc => R.instw_honest r hr I hI hb hc) v

end JRun

end Circuit
