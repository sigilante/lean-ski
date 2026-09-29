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

-- ---------------------------------------------------------------------------
-- The other tables, the heights, and the registers
-- ---------------------------------------------------------------------------

theorem memJ_sat (A : List Cell) (cpu prog pop instw : AirD) (C Pg Po Iw : Table) (hA : 0 < A.length) :
    Sat memAir (memTableJ A cpu prog pop instw C Pg Po Iw) := by
  refine ⟨hA, fun e he m hm' => ?_⟩
  have hm : m < (memTableJ A cpu prog pop instw C Pg Po Iw).h := hm'
  simp only [memAir, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simp only [B.whenFirst, B.col, E.eval, env_first, env_main0 hm]
    split
    · next h0 => subst h0; exact mul_zero' _
    · exact zero_mul' _
  · simp only [B.whenTrans, B.eq, B.nxt, B.col, B.one, B.c, E.eval, env_trans, env_main1, env_main0 hm]
    split
    · exact zero_mul' _
    · next hne =>
      have hne' : ¬ (m + 1 = A.length) := hne
      have hm1 : m + 1 < A.length := by have : m < A.length := hm; omega
      show 1 * ((memTableJ A cpu prog pop instw C Pg Po Iw).main ((m + 1) % A.length) 0 - (ofN m + ofN 1)) = 0
      rw [Nat.mod_eq_of_lt hm1, one_mul', ofN_one, ofN_succ]
      exact sub_self' _

theorem prov_sat {name : String} {w : Nat} {rows : List (List F)} {cnt : List F → Nat} (h : 0 < rows.length) :
    Sat (providerAir name w rows) (provTable rows cnt) ∧ PreIs (providerAir name w rows) (provTable rows cnt) :=
  ⟨⟨h, fun _ hc => absurd hc List.not_mem_nil⟩, ⟨rfl, fun _ _ _ _ => rfl⟩⟩

theorem instRow_stk {A : List Cell} (hfit : Fits A) {J : Air.Jet} {r r' : Air.Row} (h : instRow A J r = some r') :
    r'.stk = r.stk ∨ r'.stk < A.length := by
  unfold instRow instRowG at h
  cases hp : popR (fun a => A[a]?) r.ctr J.xs.length r.stk with
  | none => rw [hp] at h; cases h
  | some q =>
    obtain ⟨ps, rest⟩ := q
    rw [hp] at h
    dsimp only at h
    split at h
    · have e : r'.stk = rest := by rw [← Option.some.inj h]
      obtain ⟨σ, ξ, h0, hk, _, hs⟩ := popsOf_spec (A := A) J.xs.length r.stk hp
      rcases Nat.eq_zero_or_pos J.xs.length with hz | hz
      · left; rw [e, ← hk, hz, h0]
      · right
        have := (hs (J.xs.length - 1) (by omega)).2
        rw [show J.xs.length - 1 + 1 = J.xs.length by omega, hk] at this
        obtain ⟨_, hget⟩ := rd_get this
        rw [e]
        exact (hfit _ (List.mem_of_getElem? hget)).2
    · cases h

/-- **Every stack pointer of a jetted run is in memory.** -/
theorem AcceptsJ.stk_le {A : List Cell} {m0 : Mach} {roots : List (Nat × Nat)} {jets : List Air.Jet} {k : Nat}
    {row : Nat → Air.Row} (hA : AcceptsJ A m0 roots jets k row) (hroots : RootsOK m0.heap roots jets)
    (hfit : Fits A) (h0 : m0.stk ≤ A.length) : ∀ i, i < k → (row i).stk ≤ A.length := by
  intro i
  induction i with
  | zero => intro _; rw [hA.stk0]; exact h0
  | succ i ih =>
    intro hi
    rcases hA.trans i hi with h | ⟨_, J, _, _, hI⟩ | h
    · exact step_stk hfit h (hA.reach hroots i (by omega)).2.1 (hA.reach hroots (i + 1) hi).2.1
    · rcases instRow_stk hfit hI with e | e
      · rw [e]; exact ih (by omega)
      · exact Nat.le_of_lt e
    · rw [h.2]; exact ih (by omega)

open Mach Term in
/-- **Completeness of the jet circuit**: a run the AIR with instantiation
    rows accepts from a loaded term with licensed roots, over a memory of at
    most `2^21` cells whose cells point into it, in at most `2^21` rows, with
    its pops and written cells within `2^21` rows each (the jet verifier's
    bound on its free heights), gives tables that AIRs with the jet circuit's
    normal forms accept, with Plonky3's selectors; they decode back to the
    memory and the run.  The jet table must have rows (the prover panics on
    an empty one) and fit two-adic heights. -/
theorem jet_complete {t : Term} {roots : List (Nat × Nat)} {jets : List Air.Jet} {Rs : List AirD}
    (hs : sameAirsB Rs (jetAirs t roots jets) = true) (hroots : RootsOK (load t).heap roots jets)
    (hprov : 0 < (rootsRows roots).length ∧ 0 < (hdrRows jets).length ∧ 0 < (tmplRows jets).length)
    (hprov27 : (rootsRows roots).length ≤ 2 ^ 27 ∧ (hdrRows jets).length ≤ 2 ^ 27 ∧
      (tmplRows jets).length ≤ 2 ^ 27)
    {A : List Cell} {k : Nat} {row : Nat → Air.Row} (hA : AcceptsJ A (load t) roots jets k row)
    (hfit : Fits A) (hlen : A.length ≤ 2 ^ 21)
    {K HP HW : Nat} (hkK : k ≤ K) (hK : K ≤ 2 ^ 21)
    (hHP : (JRun.popRows ⟨A, roots, jets, k, row⟩ K).length ≤ HP) (hHP0 : 0 < HP) (hHP21 : HP ≤ 2 ^ 21)
    (hHW : (JRun.instwRows ⟨A, roots, jets, k, row⟩ K).length ≤ HW) (hHW0 : 0 < HW) (hHW21 : HW ≤ 2 ^ 21) :
    ∃ C Mm Pg Rt Hd Tm Po Iw, AcceptedP Rs [C, Mm, Pg, Rt, Hd, Tm, Po, Iw] ∧ C.h = K ∧ Mm.h = A.length ∧
      Po.h = HP ∧ Iw.h = HW ∧ memOf Mm = A ∧ ∀ i, i < k → rowOf C i = row i := by
  let R : JRun := ⟨A, roots, jets, k, row⟩
  have hk0 := hA.pos
  obtain ⟨_, hhd, hstk⟩ := load_fits t
  have hpre : A.take (load t).heap.length = (load t).heap := by rw [← hA.ctr0]; exact hA.heap0
  have hhl : (load t).heap.length ≤ A.length := by
    have := congrArg List.length hpre; rw [List.length_take] at this; omega
  have hA0 : 0 < A.length := by omega
  have hPP : P = 2013265921 := rfl
  have e1 : (row 0).hd = (load t).hd := hA.hd0
  have e2 : (row 0).stk = (load t).stk := hA.stk0
  have e3 : (row 0).ctr = (load t).heap.length := hA.ctr0
  -- the tables
  let C := R.cpuTable K
  let Pg := progTable (load t).heap
  let Po := R.popTable K HP
  let Iw := R.instwTable K HW
  let Rt := provTable (rootsRows roots) (R.cntRoots K)
  let Hd := provTable (hdrRows jets) (R.cntHdr K)
  let Tm := provTable (tmplRows jets) (R.cntTmpl K)
  let Mm := memTableJ A (cpuAirJ (row 0).hd (row 0).stk (row 0).ctr) (progAir (load t).heap) popAir instwAir C Pg Po Iw
  have hPg : Pg.h ≤ 2 ^ 24 := programRows_length_le (by omega)
  have hl24 : R.A.length ≤ 2 ^ 24 := Nat.le_trans (show A.length ≤ 2 ^ 21 from hlen) (by decide)
  have hcpu : Sat (cpuAirJ (row 0).hd (row 0).stk (row 0).ctr) C := R.cpu_sat hA hroots hkK hl24
  have hbal := R.balanced hA hpre (show A.length < P by omega) hHP hHW (heap := (load t).heap)
  have hacc : Accepted (jetAirs t roots jets) [C, Mm, Pg, Rt, Hd, Tm, Po, Iw] := by
    have z : (jetAirs t roots jets).zip [C, Mm, Pg, Rt, Hd, Tm, Po, Iw] =
        jetTables (row 0).hd (row 0).stk (row 0).ctr (load t).heap roots jets C Mm Pg Rt Hd Tm Po Iw := by
      rw [e1, e2, e3]; rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [z]
      intro p hp
      simp only [jetTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hcpu, .inl rfl⟩
      · exact ⟨memJ_sat A _ _ _ _ _ _ _ _ hA0, .inl rfl⟩
      · exact ⟨(prog_sat _ (by omega)).1, .inr (prog_sat _ (by omega)).2⟩
      · exact ⟨(prov_sat hprov.1).1, .inr (prov_sat hprov.1).2⟩
      · exact ⟨(prov_sat hprov.2.1).1, .inr (prov_sat hprov.2.1).2⟩
      · exact ⟨(prov_sat hprov.2.2).1, .inr (prov_sat hprov.2.2).2⟩
      · exact ⟨R.pop_sat hA hroots hl24 hHP0, .inl rfl⟩
      · exact ⟨R.instw_sat hHW0, .inl rfl⟩
    · rw [z]; exact hbal
    · rw [z]
      unfold HeightsOK jetTables
      simp only [List.foldr_cons, List.foldr_nil]
      show 15 * K + (0 * A.length + (1 * Pg.h + (0 * Rt.h + (0 * Hd.h + (0 * Tm.h + (3 * HP + (6 * HW + 0))))))) < P
      omega
    · rw [z]
      intro p hp
      simp only [jetTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show K ≤ 2 ^ 27; omega
      · show A.length ≤ 2 ^ 27; omega
      · show Pg.h ≤ 2 ^ 27; omega
      · exact hprov27.1
      · exact hprov27.2.1
      · exact hprov27.2.2
      · show HP ≤ 2 ^ 27; omega
      · show HW ≤ 2 ^ 27; omega
  have hRs : AcceptedP Rs [C, Mm, Pg, Rt, Hd, Tm, Po, Iw] :=
    (acceptedP_iff_of (jet_guarded t roots jets) hs _).2 (accepted_transfer (sameAirsB_symm hs) hacc)
  refine ⟨C, Mm, Pg, Rt, Hd, Tm, Po, Iw, hRs, rfl, rfl, rfl, rfl, ?_, ?_⟩
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
  · -- the rows decode back
    intro i hi
    have hiK : i < K := by omega
    have hq : R.rowQ i = row i := JRun.rowQ_lt hi
    have hc : (row i).ctr ≤ A.length := (hA.reach hroots i hi).2.1
    have hst : (row i).stk ≤ A.length := AcceptsJ.stk_le hA hroots hfit (by omega) i hi
    have hh : (row i).hd < A.length := by
      cases hn : R.instAt i with
      | none =>
        have hv := JRun.base_valid hA hn
        rw [hq] at hv
        obtain ⟨cell, hrd, _⟩ := (shape hv).reads 0 (by decide) rfl
        have := (rd_get hrd).1
        show (row i).hd < A.length
        exact Nat.lt_of_lt_of_le this hc
      | some p =>
        obtain ⟨g, J⟩ := p
        obtain ⟨_, hm, _, _⟩ := JRun.instAt_some hn
        obtain ⟨_, _, _, htm, _⟩ := hroots _ g hm
        exact Nat.lt_of_lt_of_le (termAt_lt htm) hhl
    have cr : ∀ c, c < 3 → C.main i c = Circuit.cpuCol A (row i) c := by
      intro c hc3
      show R.cpuCol i c = _
      rw [R.col_reg i hc3 R.rowQ_inst, hq]
    show (⟨(C.main i HD).val, (C.main i STK).val, (C.main i CTR).val⟩ : Air.Row) = row i
    rw [cr HD (by decide), cr STK (by decide), cr CTR (by decide), cpuCol_hd, cpuCol_stk, cpuCol_ctr,
      val_ofN (by omega), val_ofN (by omega), val_ofN (by omega)]

end Circuit
