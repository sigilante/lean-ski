import Ski.Circuit.CompJCpuSat

/-!
# The composed circuit with jets: its buses balance on the honest tables

The provider tables carry their counts in column 0 only (`provTableCJ`),
so their blinding flags are clear; their rows are padded to `2^9`
(`bal_rootsCJ`, `bal_hdrCJ`, `bal_tmplCJ`, the jet circuit's `bal_roots`,
`bal_hdr`, `bal_tmpl` for those rows).
-/

namespace Circuit

open B Air JetTable Compose CompM Mach

theorem padCopiesMin_super {x : List F} : ∀ {rows : List (List F)}, x ∈ rows → x ∈ padCopiesMin rows
  | [], h => nomatch h
  | _ :: _, h => List.mem_append_left _ h

theorem padCopiesMin_len {w : Nat} : ∀ {rows : List (List F)}, (∀ x ∈ rows, x.length = w) →
    ∀ x ∈ padCopiesMin rows, x.length = w :=
  fun h x hx => h x (padCopiesMin_mem hx)

theorem rootsRowsCJ_len (roots : List (Nat × Nat)) : ∀ x ∈ rootsRowsCJ roots, x.length = 2 :=
  padCopiesMin_len (fun x hx => by obtain ⟨_, _, e⟩ := List.mem_map.1 hx; rw [← e]; rfl)

theorem hdrRowsCJ_len (jets : List Air.Jet) : ∀ x ∈ hdrRowsCJ jets, x.length = 7 :=
  padCopiesMin_len (fun x hx => by
    obtain ⟨⟨J, g⟩, _, e⟩ := List.mem_map.1 hx
    rw [← e]; show (_ ++ opCols _).length = 7; rw [List.length_append, opCols_len]; rfl)

theorem tmplRowsCJ_len (jets : List Air.Jet) : ∀ x ∈ tmplRowsCJ jets, x.length = 11 :=
  padCopiesMin_len (fun x hx => by
    obtain ⟨_, _, hv⟩ := List.mem_flatMap.1 hx
    obtain ⟨⟨cl, j⟩, _, e⟩ := List.mem_map.1 hv
    rw [← e]; exact tmplRow_len _ _ _)

/-- **A provider's table, its count in column 0 only.** -/
def provTableCJ (rows : List (List F)) (cnt : List F → Nat) : Table :=
  ⟨rows.length, fun q c => if c = 0 then (provTable rows cnt).main q 0 else 0, ofRows rows⟩

/-- **A blinded provider sends as the provider does**, off its blocks'
    buses. -/
theorem sends_provCJ {name : String} {w : Nat} {rows : List (List F)} {cnt : List F → Nat}
    {blocks : List (String × Bool)} {bus : String} (hb : ∀ b ∈ blocks, b.1 ≠ bus) (v : List F) :
    tableSends (withBlocks (providerAir name w rows) blocks) (provTableCJ rows cnt) bus v =
      tableSends (providerAir name w rows) (provTable rows cnt) bus v := by
  unfold tableSends
  apply foldr_range_congr
  intro q _
  rw [rowSends_withBlocks hb]
  have e0 : ((col 0).neg).eval ((provTableCJ rows cnt).env q) = ((col 0).neg).eval ((provTable rows cnt).env q) := by
    show -((provTableCJ rows cnt).main ((q + 0) % rows.length) 0) = -((provTable rows cnt).main ((q + 0) % rows.length) 0)
    rw [show (provTableCJ rows cnt).main ((q + 0) % rows.length) 0 =
      (provTable rows cnt).main ((q + 0) % rows.length) 0 by simp only [provTableCJ, ↓reduceIte]]
  have ep : ∀ e : E, e ∈ (List.range w).map prec →
      e.eval ((provTableCJ rows cnt).env q) = e.eval ((provTable rows cnt).env q) := by
    intro e he
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 he
    rfl
  unfold rowSends providerAir
  simp only [List.foldr_cons, List.foldr_nil]
  rw [List.map_congr_left ep]
  show (if _ then ((col 0).neg).eval _ else 0) + 0 = (if _ then ((col 0).neg).eval _ else 0) + 0
  rw [e0]

namespace JRun

variable (R : JRun)

/-- **`ROOTS` balances, its rows padded to `2^9`.** -/
theorem bal_rootsCJ {K : Nat} (v : List F) :
    tableSends (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (R.cpuTable K) "roots" v +
      tableSends (providerAir "roots" 2 (rootsRowsCJ R.roots)) (provTable (rootsRowsCJ R.roots) (R.cntRoots K)) "roots" v = 0 := by
  rw [prov_sends (rootsRowsCJ_len R.roots)]
  apply bal_lookup
  · unfold tableSends cntRoots
    show (List.range K).foldr _ 0 = _
    rw [← fold_ofN]
    apply foldr_range_congr K
    intro i hi
    rw [cpu_roots_gen]
    cases hn : R.instAt i with
    | none =>
      rw [ite_zero _ _ (by
        show R.cpuCol ((i + 0) % K) (SEL + 11) = 0
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
        unfold cpuCol; rw [hn]; simp only
        rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (Nat.ne_of_gt (kindOf_lt _ _))])]
      simp only; rfl
    | some p =>
      obtain ⟨g, J⟩ := p
      have cv := R.inst_cols hi hn
      rw [cv, cv, cv, show R.instCol i g J HD = ofN (R.row i).hd from rfl, show R.instCol i g J J_G = ofN g from rfl,
        show R.instCol i g J (SEL + 11) = 1 from rfl]
      simp only
      rw [ofN_ind]; rfl
  · intro hc
    obtain ⟨i, _, hp⟩ := sumTo_pos_ex hc
    cases hn : R.instAt i with
    | none => simp only [hn] at hp; exact absurd hp (Nat.lt_irrefl 0)
    | some p =>
      obtain ⟨g, J⟩ := p
      simp only [hn] at hp
      split at hp
      · next e =>
        rw [← e]
        exact padCopiesMin_super (List.mem_map.2 ⟨((R.row i).hd, g), (instAt_some hn).2.1, rfl⟩)
      · exact absurd hp (Nat.lt_irrefl 0)

/-- **`HDR` balances, its rows padded to `2^9`.** -/
theorem bal_hdrCJ {K : Nat} (v : List F) :
    tableSends (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (R.cpuTable K) "hdr" v +
      tableSends (providerAir "hdr" 7 (hdrRowsCJ R.jets)) (provTable (hdrRowsCJ R.jets) (R.cntHdr K)) "hdr" v = 0 := by
  rw [prov_sends (hdrRowsCJ_len R.jets)]
  apply bal_lookup
  · unfold tableSends cntHdr
    show (List.range K).foldr _ 0 = _
    rw [← fold_ofN]
    apply foldr_range_congr K
    intro i hi
    rw [cpu_hdr_gen]
    cases hn : R.instAt i with
    | none =>
      rw [ite_zero _ _ (by
        show R.cpuCol ((i + 0) % K) (SEL + 11) = 0
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
        unfold cpuCol; rw [hn]; simp only
        rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (Nat.ne_of_gt (kindOf_lt _ _))])]
      simp only; rfl
    | some p =>
      obtain ⟨g, J⟩ := p
      have cv := R.inst_cols hi hn
      rw [cv, cv, cv, cv, cv, cv, cv, cv, show R.instCol i g J (SEL + 11) = 1 from rfl]
      simp only
      rw [ofN_ind]
      show ind (_ = v) = ind (hdrRow J g = v)
      have e : [R.instCol i g J J_G, R.instCol i g J J_K, R.instCol i g J J_N, R.instCol i g J J_RL,
          R.instCol i g J J_RA, R.instCol i g J J_RG, R.instCol i g J J_RV] = hdrRow J g := by
        show [ofN g, ofN J.xs.length, ofN (symCells J J.body 0).1.length, (opCols (symCells J J.body 0).2).getD 0 0,
          (opCols (symCells J J.body 0).2).getD 1 0, (opCols (symCells J J.body 0).2).getD 2 0,
          (opCols (symCells J J.body 0).2).getD 3 0] = [ofN g, ofN J.xs.length, ofN (symCells J J.body 0).1.length] ++
          opCols (symCells J J.body 0).2
        cases (symCells J J.body 0).2 <;> rfl
      rw [e]
  · intro hc
    obtain ⟨i, _, hp⟩ := sumTo_pos_ex hc
    cases hn : R.instAt i with
    | none => simp only [hn] at hp; exact absurd hp (Nat.lt_irrefl 0)
    | some p =>
      obtain ⟨g, J⟩ := p
      simp only [hn] at hp
      split at hp
      · next e =>
        rw [← e]
        have hJ := (instAt_some hn).2.2.1
        obtain ⟨hg, hJg⟩ := List.getElem?_eq_some_iff.1 hJ
        exact padCopiesMin_super (List.mem_map.2 ⟨(J, g), List.mem_zipIdx_iff_getElem?.2 (by
          rw [List.getElem?_eq_getElem hg, hJg]), rfl⟩)
      · exact absurd hp (Nat.lt_irrefl 0)


/-- **`TMPL` balances, its rows padded to `2^9`.** -/
theorem bal_tmplCJ {K HW : Nat} (hHW : (R.instwRows K).length ≤ HW) (v : List F) :
    tableSends instwAir (R.instwTable K HW) "tmpl" v +
      tableSends (providerAir "tmpl" 11 (tmplRowsCJ R.jets)) (provTable (tmplRowsCJ R.jets) (R.cntTmpl K)) "tmpl" v = 0 := by
  rw [prov_sends (tmplRowsCJ_len R.jets)]
  apply bal_lookup
  · rw [show R.instwTable K HW = ⟨HW, ofRows (R.instwRows K), fun _ _ => 0⟩ from rfl,
      sends_rows instw_nowOnly instw_quiet hHW, instwRows, foldr_flatMap]
    unfold cntTmpl
    rw [← fold_ofN]
    apply foldr_range_congr K
    intro i _
    cases hn : R.instAt i with
    | none => unfold instwRowsAt; rw [hn]; rfl
    | some p =>
      obtain ⟨g, J⟩ := p
      rw [R.instwRowsAt_eq hn, foldr_map_range]
      rw [foldr_range_congr _ (fun j _ => instw_tmpl i (R.row i).ctr g j (R.ps i J) _ v)]
      simp only [← ofN_ind]
      rw [fold_ofN]
      rw [zipIdx_sum (symCells J J.body 0).1 (fun cl j => if tmplRow g j cl = v then 1 else 0) (0, none)]
  · intro hc
    obtain ⟨i, _, hp⟩ := sumTo_pos_ex hc
    cases hn : R.instAt i with
    | none => simp only [hn] at hp; exact absurd hp (Nat.lt_irrefl 0)
    | some p =>
      obtain ⟨g, J⟩ := p
      simp only [hn] at hp
      rw [zipIdx_sum (symCells J J.body 0).1 (fun cl j => if tmplRow g j cl = v then 1 else 0) (0, none)] at hp
      obtain ⟨j, hj, hq⟩ := sumTo_pos_ex hp
      split at hq
      · next e =>
        rw [← e]
        have hJ := (instAt_some hn).2.2.1
        obtain ⟨hg, hJg⟩ := List.getElem?_eq_some_iff.1 hJ
        apply padCopiesMin_super
        refine List.mem_flatMap.2 ⟨(J, g), List.mem_zipIdx_iff_getElem?.2 (by
          rw [List.getElem?_eq_getElem hg, hJg]), ?_⟩
        refine List.mem_map.2 ⟨((symCells J J.body 0).1.getD j (0, none), j), List.mem_zipIdx_iff_getElem?.2 ?_, rfl⟩
        skip
        rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      · exact absurd hq (Nat.lt_irrefl 0)


end JRun

-- ---------------------------------------------------------------------------
-- The CPU on the jet buses is the jet table's
-- ---------------------------------------------------------------------------

theorem jetInters_atomsCJ : jetInters.all (fun I => I.count.onlyAtoms PRun.atomJJ &&
    I.fields.all (·.onlyAtoms PRun.atomJJ)) = true := by decide

/-- The jet messages send nothing on a row with no instantiation selector
    and no root argument flag. -/
theorem jet_fold_zero {ρ : Atom → F} (h11 : ρ (.main 0 (SEL + 11)) = 0) (hra : ρ (.main 0 J_RA) = 0)
    (bus : String) (v : List F) :
    jetInters.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ) = v then
      I.count.eval ρ else 0) + acc) 0 = 0 := by
  apply foldr_zero_init
  intro I hI
  have hc : I.count.eval ρ = 0 := by
    simp only [jetInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sInst, B.col, E.eval, h11, hra] <;> decide
  split
  · exact hc
  · rfl

/-- Messages over shared atoms send the same under agreeing environments. -/
theorem fold_congr_atoms {ρ ρ' : Atom → F} (h : ∀ a, PRun.atomJJ a = true → ρ a = ρ' a) (bus : String)
    (v : List F) : ∀ L : List Inter, L.all (fun I => I.count.onlyAtoms PRun.atomJJ &&
      I.fields.all (·.onlyAtoms PRun.atomJJ)) = true →
    L.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ) = v then I.count.eval ρ else 0) + acc) 0 =
      L.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ') = v then I.count.eval ρ' else 0) + acc) 0
  | [], _ => rfl
  | I :: L, hL => by
    simp only [List.all_cons, Bool.and_eq_true] at hL
    obtain ⟨⟨hc, hf⟩, hL⟩ := hL
    simp only [List.foldr_cons]
    rw [fold_congr_atoms h bus v L hL, E.eval_congr h _ hc,
      List.map_congr_left (fun e he => E.eval_congr h e (List.all_eq_true.1 hf e he))]

namespace CRun

variable {R : CRun} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCJ R.A m0 R.jroots R.jets R.segRoots nilA R.n R.e R.row) (hroots : RootsOK m0.heap R.jroots R.jets)
  {K : Nat} (hK : R.e (R.n - 1) < K)
include hA hK

omit hA hK in
/-- **On the jet buses, the CPU sends what the jet table sends.** -/
theorem cpuCJ_jetSends {bus : String}
    (hb : bus ≠ "mem" ∧ bus ≠ "segs" ∧ bus ≠ "blind_a" ∧ bus ≠ "blind_b" ∧ bus ≠ "blind_c")
    (hd0 stk0 ctr0 hd1 stk1 ctr1 : Nat) (v : List F) :
    tableSends (cpuAirCJ hd0 stk0 ctr0 R.n nilA) (R.cpuTableCJ K) bus v =
      tableSends (cpuAirJ hd1 stk1 ctr1) (R.J.cpuTable K) bus v := by
  unfold tableSends
  apply foldr_range_congr
  intro i hi
  rw [cpuCJ_rowSends_jet hb, cpu_rowSends_jet hb.1]
  cases hr : isRestart R.e R.n i with
  | false =>
    exact fold_congr_atoms (R.env_agreeCJ hi hr) bus v jetInters jetInters_atomsCJ
  | true =>
    have hJ0 : R.J.instAt i = none := R.J_restart hr
    have hi' : i < K := hi
    rw [jet_fold_zero (ρ := (R.cpuTableCJ K).env i) (by
        show R.cpuColCJ ((i + 0) % K) (SEL + 11) = 0
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi', R.colCJ_sel hr (by decide) (by decide)])
      (by
        show R.cpuColCJ ((i + 0) % K) J_RA = 0
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi', R.colCJ_low (by decide) (.inl (by decide)),
          R.J_jet_restart hr (by decide) (by decide)]),
      jet_fold_zero (ρ := (R.J.cpuTable K).env i) (by
        show R.J.cpuCol ((i + 0) % K) (SEL + 11) = 0
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi']
        unfold JRun.cpuCol; rw [hJ0]; simp only
        rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (Nat.ne_of_gt (kindOf_lt _ _))])
      (by
        show R.J.cpuCol ((i + 0) % K) J_RA = 0
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi', R.J_jet_restart hr (by decide) (by decide)])]

-- ---------------------------------------------------------------------------
-- The CPU's memory messages are honest
-- ---------------------------------------------------------------------------

omit hA hK in
/-- The tags with the restart selector at `0` are the jet CPU's. -/
theorem tagsCJ_eval {ρ : Atom → F} (h0 : ρ (.main 0 RSJ) = 0) {j : Nat} (hj : j < 4) :
    (tagsCJ.getD j zero).eval ρ = (tags.getD j zero).eval ρ := by
  let σ : Atom → E := fun a => if a = .main 0 RSJ then .const 0 else .atom a
  have hσ : ∀ a, (σ a).eval ρ = ρ a := by
    intro a; show (if a = .main 0 RSJ then E.const 0 else .atom a).eval ρ = ρ a
    split
    · next e => rw [e, h0]; rfl
    · rfl
  rw [← E.eval_subst σ ρ hσ]
  apply E.eval_eq_of_norm
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

omit hA hK in
theorem reads_atomsJJ : ∀ j, j < 4 → (acts.getD j zero).onlyAtoms PRun.atomJJ = true ∧
    (addrs.getD j zero).onlyAtoms PRun.atomJJ = true ∧ (tags.getD j zero).onlyAtoms PRun.atomJJ = true ∧
    (fld (2 * j)).onlyAtoms PRun.atomJJ = true ∧ (fld (2 * j + 1)).onlyAtoms PRun.atomJJ = true := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

omit hA hK in
theorem writes_atomsJJ : writeInters.all (fun I => I.count.onlyAtoms PRun.atomJJ &&
    I.fields.all (·.onlyAtoms PRun.atomJJ)) = true := by decide

omit hA hK in
/-- A row with no instantiation agrees with the base honest table on the
    base columns but the selectors. -/
theorem agree_base {i : Nat} (hi : i < K) (hn : R.J.instAt i = none) :
    ∀ a, baseAtom a = true → (R.cpuTableCJ K).env i a = (Circuit.cpuTable R.A R.J.rowQ K).env i a := by
  intro a ha
  cases a with
  | main o c =>
    cases o with
    | zero =>
      simp only [baseAtom, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at ha
      show R.cpuColCJ ((i + 0) % K) c = Circuit.cpuCol R.A (R.J.rowQ ((i + 0) % K)) c
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi,
        R.colCJ_low (by unfold CPU_WIDTH JET_WIDTH at *; omega) (.inl (fun h => by rcases ha.2 with h' | h' <;> omega))]
      unfold JRun.cpuCol; rw [hn]; simp only; rw [if_pos ha.1]; rfl
    | succ o => simp [baseAtom] at ha
  | _ => simp [baseAtom] at ha

omit hA hK in
theorem reads_base : ∀ j, j < 4 → (addrs.getD j zero).onlyAtoms baseAtom = true ∧
    (fld (2 * j)).onlyAtoms baseAtom = true ∧ (fld (2 * j + 1)).onlyAtoms baseAtom = true := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

omit hK in
include hroots in
/-- **The CPU's memory messages are honest.** -/
theorem cpuCJ_honest (hd0 stk0 ctr0 : Nat) : HonestMem R.A (cpuAirCJ hd0 stk0 ctr0 R.n nilA) (R.cpuTableCJ K) := by
  intro r hr I hI hbus hc
  have hr' : r < K := hr
  have hJ : JOK R.J := hA.jok hroots
  change I ∈ cpuIntersCJ at hI
  cases hrs : isRestart R.e R.n r with
  | false =>
    have cong := E.eval_congr (R.env_agreeCJ hr' hrs)
    have h0 : (R.cpuTableCJ K).env r (.main 0 RSJ) = 0 := by
      show R.cpuColCJ ((r + 0) % K) RSJ = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hr', R.colCJ_rs, hrs]; rfl
    -- the jet table's message with the same count and fields
    have key : ∀ I0 : Inter, I0.count.eval ((R.cpuTableCJ K).env r) ≠ 0 → I0.bus = "mem" →
        ∀ I' ∈ cpuInters, I'.bus = "mem" → I'.count.eval ((R.cpuTableCJ K).env r) = I0.count.eval
        ((R.cpuTableCJ K).env r) → I'.count.onlyAtoms PRun.atomJJ = true →
        I'.fields.all (·.onlyAtoms PRun.atomJJ) = true →
        I'.fields.map (fun e => e.eval ((R.cpuTableCJ K).env r)) = I0.fields.map (fun e => e.eval ((R.cpuTableCJ K).env r)) →
        ∃ m, m < R.A.length ∧ I0.fields.map (fun e => e.eval ((R.cpuTableCJ K).env r)) = tupleOf R.A m := by
      intro I0 hc _ I' hI' hb' hcnt hca hfa hfl
      have hc' : I'.count.eval ((R.J.cpuTable K).env r) ≠ 0 := by
        rw [← cong _ hca, hcnt]; exact hc
      obtain ⟨m, hm, e⟩ := R.J.cpu_honestRow hJ hr' hrs I' (List.mem_append_left _ hI') hb' hc'
      refine ⟨m, hm, ?_⟩
      rw [← hfl]
      exact (List.map_congr_left (fun c hc'' => cong c (List.all_eq_true.1 hfa c hc''))).trans e
    have rd : ∀ j, j < 4 → (readInterCJ j).count.eval ((R.cpuTableCJ K).env r) ≠ 0 →
        ∃ m, m < R.A.length ∧ (readInterCJ j).fields.map (fun e => e.eval ((R.cpuTableCJ K).env r)) = tupleOf R.A m := by
      intro j hj hcj
      obtain ⟨a1, a2, a3, a4, a5⟩ := reads_atomsJJ j hj
      exact key (readInterCJ j) hcj rfl (readInter j) (by
          rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
            simp [cpuInters]) rfl rfl a1
        (by simp only [readInter, List.all_cons, List.all_nil, a2, a3, a4, a5, Bool.and_true])
        (by simp only [readInter, readInterCJ, List.map_cons, List.map_nil, tagsCJ_eval h0 hj])
    have wr : ∀ I ∈ writeInters, I.bus = "mem" → I.count.eval ((R.cpuTableCJ K).env r) ≠ 0 →
        ∃ m, m < R.A.length ∧ I.fields.map (fun e => e.eval ((R.cpuTableCJ K).env r)) = tupleOf R.A m := by
      intro I hw hb hcI
      have ha := List.all_eq_true.1 writes_atomsJJ I hw
      rw [Bool.and_eq_true] at ha
      exact key I hcI hb I (List.mem_append_right _ hw) hb rfl ha.1 ha.2 rfl
    rw [cpuIntersCJ_eq] at hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact rd 0 (by decide) hc
    · exact rd 1 (by decide) hc
    · exact rd 2 (by decide) hc
    · exact rd 3 (by decide) hc
    · exact wr _ (by simp [writeInters]) hbus hc
    · exact wr _ (by simp [writeInters]) hbus hc
    · exact wr _ (by simp [writeInters]) hbus hc
    · exact wr _ (by simp [writeInters]) hbus hc
    all_goals exact absurd hbus (by decide)
  | true =>
    obtain ⟨j0, hj0, hij⟩ := isRestart_iff.1 hrs
    have hlt : r < R.e (R.n - 1) := hA.restart_lt hrs
    have hq : R.J.rowQ r = R.row r := rowQ_J (R := R) (by omega)
    obtain ⟨hend1, hend2⟩ := hA.ends j0 (by omega)
    rw [hij] at hend1 hend2
    have hval : Valid R.A (R.J.rowQ r) := .inr (by rw [hq]; exact halt_K hend1 hend2)
    have hkind : kindOf R.A (R.J.rowQ r) = 5 := by rw [hq]; simp only [kindOf, hend1, hend2]
    have hk := R.kind_restart (K := K) hrs
    have hkb := cpu_kind (M := R.A) (row := R.J.rowQ) (k := K) hr' (shape hval)
    rw [hkind] at hkb
    obtain ⟨hf, _, hApp, hS, _⟩ := kind_factsCJ hr hk
    obtain ⟨hfb, _, _, _, _⟩ := kind_facts hr' hkb
    have cong := E.eval_congr (agree_base hr' (R.J_restart hrs))
    have rd : ∀ j, j < 4 → (readInterCJ j).count.eval ((R.cpuTableCJ K).env r) ≠ 0 →
        ∃ m, m < R.A.length ∧ (readInterCJ j).fields.map (fun e => e.eval ((R.cpuTableCJ K).env r)) = tupleOf R.A m := by
      intro j hj hc
      obtain ⟨b1, b2, b3⟩ := reads_base j hj
      have ea : actOfCJ 12 j = actOf 5 j := by
        unfold actOfCJ actOf
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
      have et : tagOfCJ 12 j = tagOf 5 j := by
        unfold tagOfCJ tagOf
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
      have hcb : (readInter j).count.eval ((Circuit.cpuTable R.A R.J.rowQ K).env r) ≠ 0 := by
        show (acts.getD j zero).eval _ ≠ 0
        rw [(hfb j hj).1, ← ea, ← (hf j hj).1]; exact hc
      obtain ⟨m, hm, e⟩ := cpu_honestAt (M := R.A) (row := R.J.rowQ) (k := K) hr' hval (readInter j)
        (by rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [cpuInters]) hcb
      refine ⟨m, hm, ?_⟩
      rw [← e]
      simp only [readInter, readInterCJ, List.map_cons, List.map_nil]
      rw [cong _ b1, cong _ b2, cong _ b3, (hf j hj).2, (hfb j hj).2, et]
    rw [cpuIntersCJ_eq] at hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact rd 0 (by decide) hc
    · exact rd 1 (by decide) hc
    · exact rd 2 (by decide) hc
    · exact rd 3 (by decide) hc
    · exact absurd hApp hc
    · exact absurd hS hc
    · exact absurd hS hc
    · exact absurd hS hc
    all_goals exact absurd hbus (by decide)

-- ---------------------------------------------------------------------------
-- The segment bus
-- ---------------------------------------------------------------------------

omit hA hK in
/-- A CPU row's `segs` message: the restart indicator, with the next
    segment's number and root. -/
theorem rowSegsCJ (hd0 stk0 ctr0 n' nilA' : Nat) {r : Nat} (hr : r < K) (v : List F) :
    rowSends (cpuAirCJ hd0 stk0 ctr0 n' nilA') (R.cpuTableCJ K) "segs" v r =
      if [ofN (cntS (rsI R.e R.n) r + 1), ofN (R.segRoots.getD (cntS (rsI R.e R.n) r + 1) 0)] = v
      then ofN (rsI R.e R.n r) else 0 := by
  have cv := cvCJ (R := R) hr
  unfold rowSends
  show cpuIntersCJ.foldr _ 0 = _
  rw [cpuIntersCJ_eq]
  have he := rowSends_one (T := R.cpuTableCJ K) (bus := "segs") (v := v) (r := r)
    ⟨"segs", 1, sRSJ, [.add (col CNTJ) one, col ROOTJ]⟩
    [readInterCJ 0, readInterCJ 1, readInterCJ 2, readInterCJ 3,
     ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩,
     ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩,
     ⟨"roots", 1, sInst, [col HD, col J_G]⟩,
     ⟨"hdr", 1, sInst, [col J_G, col J_K, col J_N, col J_RL, col J_RA, col J_RG, col J_RV]⟩,
     ⟨"popch", 1, sInst, [col J_CLK, col CTR, c 0, col STK]⟩,
     ⟨"popch", 1, .neg sInst, [col J_CLK, col CTR, col J_K, col J_REST]⟩,
     ⟨"wch", 1, sInst, [col J_CLK, col CTR, col J_G, c 0]⟩,
     ⟨"wch", 1, .neg sInst, [col J_CLK, col CTR, col J_G, col J_N]⟩,
     ⟨"arg", 1, col J_RA, [col J_CLK, col J_RV, col J_XROOT]⟩]
    [blindMsg "blind_a" BLAJ false, blindMsg "blind_b" BLBJ true, blindMsg "blind_c" BLCJ true]
    (by decide) (by decide)
  refine he.trans ?_
  have hf : List.map (fun x0 => x0.eval ((R.cpuTableCJ K).env r)) [.add (col CNTJ) one, col ROOTJ] =
      [ofN (cntS (rsI R.e R.n) r + 1), ofN (R.segRoots.getD (cntS (rsI R.e R.n) r + 1) 0)] := by
    simp only [List.map_cons, List.map_nil, E.eval, cv, B.one, B.c, ofN_one, R.colCJ_cnt, R.colCJ_root]
    rw [← ofN_one, ← ofN_add]
  have hc : sRSJ.eval ((R.cpuTableCJ K).env r) = ofN (rsI R.e R.n r) := by
    show (col RSJ).eval _ = _
    rw [cv, R.colCJ_rs]
    unfold rsI
    cases isRestart R.e R.n r
    · exact ofN_zero.symm
    · exact ofN_one.symm
  rw [hf, hc]
  by_cases hv : [ofN (cntS (rsI R.e R.n) r + 1), ofN (R.segRoots.getD (cntS (rsI R.e R.n) r + 1) 0)] = v
  · rw [if_pos ⟨rfl, hv⟩, if_pos hv]
  · rw [if_neg (fun h => hv h.2), if_neg hv]

/-- **The honest segment multiplicities**: segment `q`'s row receives one
    restart when `q ≥ 1`, and none for the first. -/
theorem segsCountCJ (hd0 stk0 ctr0 n' nilA' : Nat) (hn : R.segRoots.length = R.n) (hP : R.n < P) {q : Nat}
    (hq : q < R.n) :
    tableSends (cpuAirCJ hd0 stk0 ctr0 n' nilA') (R.cpuTableCJ K) "segs"
      [ofN q, ofN (R.segRoots.getD q 0)] = if 1 ≤ q then 1 else 0 := by
  have hmono := hA.emono
  -- which rows send to segment `q`
  have row_eq : ∀ r, r < K → rowSends (cpuAirCJ hd0 stk0 ctr0 n' nilA') (R.cpuTableCJ K) "segs"
      [ofN q, ofN (R.segRoots.getD q 0)] r = if 1 ≤ q ∧ r = R.e (q - 1) then 1 else 0 := by
    intro r hr
    rw [rowSegsCJ hd0 stk0 ctr0 n' nilA' hr]
    cases hrs : isRestart R.e R.n r with
    | false =>
      have h0 : rsI R.e R.n r = 0 := by unfold rsI; rw [hrs]; rfl
      rw [h0]
      have : ¬ (1 ≤ q ∧ r = R.e (q - 1)) := by
        rintro ⟨h1, rfl⟩
        have : isRestart R.e R.n (R.e (q - 1)) = true := isRestart_iff.2 ⟨q - 1, by omega, rfl⟩
        rw [this] at hrs; cases hrs
      rw [if_neg this]
      split <;> rfl
    | true =>
      obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hrs
      have h1 : rsI R.e R.n (R.e j) = 1 := by unfold rsI; rw [hrs]; rfl
      rw [h1, cntS_end hmono j (by omega)]
      by_cases hjq : j + 1 = q
      · subst hjq
        rw [if_pos rfl, if_pos ⟨by omega, by simp⟩]; rfl
      · have hne : [ofN (j + 1), ofN (R.segRoots.getD (j + 1) 0)] ≠ [ofN q, ofN (R.segRoots.getD q 0)] := by
          intro h
          have h' := congrArg List.head? h
          simp only [List.head?_cons, Option.some.injEq] at h'
          have := congrArg Fin.val h'
          rw [val_ofN (by omega), val_ofN (by omega)] at this
          exact hjq this
        rw [if_neg hne]
        have : ¬ (1 ≤ q ∧ R.e j = R.e (q - 1)) := by
          rintro ⟨h1, h2⟩
          rcases Nat.lt_trichotomy j (q - 1) with h | h | h
          · have := emono_lt hmono h (by omega); omega
          · omega
          · have := emono_lt hmono h (by omega); omega
        rw [if_neg this]
  unfold tableSends
  show (List.range K).foldr _ 0 = _
  have hcongr : (List.range K).foldr (fun r acc => rowSends (cpuAirCJ hd0 stk0 ctr0 n' nilA')
      (R.cpuTableCJ K) "segs" [ofN q, ofN (R.segRoots.getD q 0)] r + acc) 0 =
      (List.range K).foldr (fun r acc => (if 1 ≤ q ∧ r = R.e (q - 1) then (1 : F) else 0) + acc) 0 := by
    exact foldr_range_congr K row_eq
  rw [hcongr]
  by_cases h1 : 1 ≤ q
  · have hlt : R.e (q - 1) < K := Nat.lt_of_le_of_lt (emono_le hmono (a := q - 1) (b := R.n - 1) (by omega) (by omega)) hK
    rw [if_pos h1]
    refine Eq.trans ?_ (foldr_single K (R.e (q - 1)) hlt)
    simp only [h1, true_and]
  · rw [if_neg h1]
    have : ∀ l : List Nat, l.foldr (fun r acc => (if 1 ≤ q ∧ r = R.e (q - 1) then (1 : F) else 0) + acc) 0 = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons r l ih =>
        show _ + _ = 0
        rw [if_neg (fun h => h1 h.1), ih]
        exact zero_add' 0
    exact this _

/-- **The honest segment table is the public one.** -/
theorem segs_honestCJ (hd0 stk0 ctr0 n' nilA' : Nat) (hn : R.segRoots.length = R.n) (hP : R.n < P) :
    segsTableC R.segRoots (cpuAirCJ hd0 stk0 ctr0 n' nilA') (R.cpuTableCJ K) = segsPub R.segRoots := by
  unfold segsTableC segsPub
  congr 1
  funext q _
  by_cases hq : q < R.segRoots.length
  · rw [if_pos hq, segsCountCJ hA hK hd0 stk0 ctr0 n' nilA' hn hP (by omega)]
    by_cases h1 : 1 ≤ q
    · rw [if_pos h1, if_pos ⟨h1, hq⟩]
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  · rw [if_neg hq, if_neg (fun h => hq h.2)]


end CRun

end Circuit
