import Ski.Circuit.ProbeBal

/-!
# The honest probe tables' memory messages

Every `mem` message the probe CPU, POP and PW send is a memory cell's
tuple: a row within a segment reads and writes as the jet CPU does; a later
probe row reads the marker at its head and the nil below its fields; a probe
row writes the nil below its stack; PW writes the markers and their stack;
a probe POP row reads a stack cell.
-/

namespace Circuit

open B Air JetTable Mach

theorem cpuJ_inters_atoms : (cpuInters ++ jetInters).all
    (fun I => I.count.onlyAtoms PRun.atomJJ && I.fields.all (·.onlyAtoms PRun.atomJJ)) = true := by decide

theorem rd_some {M : List Cell} {c a : Nat} {cell : Cell} (h : rd M c a = some cell) : M[a]? = some cell := by
  unfold rd at h; split at h
  · exact h
  · cases h

namespace PRun

variable {R : PRun} {t : Term} (hA : AcceptsP R.A (load t) R.roots R.jets R.plan R.p R.fld R.row)
  (hroots : RootsOK (load t).heap R.roots R.jets)
include hA hroots

/-- The cell a probe row writes below its markers' stack is a nil. -/
theorem probe_nil {j : Nat} (hj : j < R.n) :
    R.A[(R.row (R.p j)).ctr + ((R.seg j).k + (R.seg j).k)]? = some .nil := by
  obtain ⟨hw, _⟩ := probe_spec hA hj
  have := wrs_get hw ((R.seg j).k + (R.seg j).k) (by rw [pcells_length]; omega)
  rw [this]
  have e := pcells_nil (R.seg j).base (R.seg j).k (R.row (R.p j)).ctr
  rw [List.getElem?_eq_getElem (by rw [pcells_length]; omega)] at e
  exact e

/-- **The probe CPU's memory messages are honest.** -/
theorem cpu_honestP {K : Nat} (hK : R.last < K) (hlast : (R.seg (R.n - 1)).arity = 0) (la : Nat) :
    HonestMem R.A (cpuAirP (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n la) (R.cpuTableP K) := by
  intro r (hr : r < K) I hI hbus hc
  have cv : ∀ c, (R.cpuTableP K).env r (.main 0 c) = R.cpuColP K r c := fun c => by
    show R.cpuColP K ((r + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hr]
  have hJ := jok hA hroots
  rcases List.mem_append.1 hI with hI | hI
  · -- the corpus and jet messages
    cases hp : R.isP r with
    | false =>
      have cong := E.eval_congr (env_agreeP hA hr hp)
      have ha := List.all_eq_true.1 cpuJ_inters_atoms I hI
      rw [Bool.and_eq_true, List.all_eq_true] at ha
      rw [cong _ ha.1] at hc
      obtain ⟨m, hm, e⟩ := R.J.cpu_honestRow hJ hr hp I hI hbus hc
      exact ⟨m, hm, Eq.trans (List.map_congr_left (fun c hc' => cong c (ha.2 c hc'))) e⟩
    | true =>
      obtain ⟨hsel, _, _⟩ := R.pr_sels hr hp
      have hk2 : (if r = 0 then 12 else 13) = 12 ∨ (if r = 0 then 12 else 13) = 13 := by
        split
        · exact .inl rfl
        · exact .inr rfl
      obtain ⟨ha0, ha, ht0, _, happ, hsS, _⟩ := probe_facts hr hsel hk2
      rcases List.mem_append.1 hI with hI | hI
      · simp only [cpuInters, writeInters, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hI
        rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · -- the head read, at a later probe row
          rcases Nat.decEq r 0 with h0 | h0
          · obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
            have hj0 : 0 < R.pcnt r := Nat.pos_of_ne_zero (fun e => h0 ((pr_zero hA hp).2 e))
            obtain ⟨hhead, _⟩ := later_end hA hjn hj0
            rw [hpj] at hhead
            obtain ⟨hm, ht⟩ := tuple_get (rd_some hhead)
            refine ⟨(R.row r).hd, hm, ?_⟩
            rw [ht]
            obtain ⟨rHD, _⟩ := pr_regs hA hK hp
            simp only [readInter, List.map_cons, List.map_nil]
            rw [ht0, if_neg h0, if_pos rfl]
            show [(col HD).eval _, ofN 6, (col (FLD + 0)).eval _, (col (FLD + 1)).eval _] = _
            rw [R.cvP hr, R.cvP hr, R.cvP hr, rHD, R.colP_base hp (by decide) (by decide),
              R.colP_base hp (by decide) (by decide), cpuCol_fld _ _ (by decide), cpuCol_fld _ _ (by decide),
              if_pos rfl, if_neg (by decide)]
            show [ofN (R.row r).hd, ofN 6, ofN (cellFields ((rd R.A (R.row r).ctr (R.row r).hd).getD .nil)).1,
              ofN (cellFields ((rd R.A (R.row r).ctr (R.row r).hd).getD .nil)).2] = _
            rw [hhead]; rfl
          · exact absurd (show (acts.getD 0 zero).eval _ = 0 by rw [ha0, if_pos h0, if_neg (by decide), ofN_zero]) hc
        · exact absurd (ha 1 (by decide) (by decide)) hc
        · exact absurd (ha 2 (by decide) (by decide)) hc
        · exact absurd (ha 3 (by decide) (by decide)) hc
        · exact absurd happ hc
        all_goals exact absurd hsS hc
      · simp only [jetInters, List.mem_cons, List.not_mem_nil, or_false] at hI
        rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd hbus (by decide)
  · -- the probe messages
    simp only [probeInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hbus (by decide)
    · exact absurd hbus (by decide)
    · exact absurd hbus (by decide)
    · exact absurd hbus (by decide)
    · -- the nil read
      have hNA : (col P_NILACT).eval ((R.cpuTableP K).env r) ≠ 0 := hc
      rw [R.cvP hr] at hNA
      have tnil : ∀ {m : Nat}, R.A[m]? = some .nil → m < R.A.length ∧ tupleOf R.A m = [ofN m, ofN 4, ofN 0, ofN 0] :=
        fun h => tuple_get h
      cases hp : R.isP r with
      | false =>
        rw [R.colP_high hp (by decide)] at hNA
        rcases Nat.decEq (r + 1) K with hl | hl
        · exact absurd (R.normX_zero (by decide) (.inl hl)) hNA
        · obtain ⟨_, hNAD, _⟩ := R.normX_last hl
          obtain ⟨hq, _⟩ := last_facts hA hroots hK hl hlast
          obtain ⟨rest, _, hpop, hnil⟩ := last_end hA
          rw [hlast] at hpop
          have hr' : rest = (R.row R.last).stk := by
            have e : (some ([], (R.row R.last).stk) : Option (List Nat × Nat)) = some (R.fld (R.n - 1), rest) := hpop
            exact (congrArg Prod.snd (Option.some.inj e)).symm
          rw [hr'] at hnil
          obtain ⟨hm, ht⟩ := tnil (rd_some hnil)
          refine ⟨(R.row R.last).stk, hm, ?_⟩
          rw [ht]
          show [(col P_NILADDR).eval _, ofN 4, ofN 0, ofN 0] = _
          rw [R.cvP hr, R.colP_high hp (by decide), hNAD, hq]
      | true =>
        rw [R.colP_x hp (by decide)] at hNA
        rcases Nat.decEq r 0 with h0 | h0
        · obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
          have hj0 : 0 < R.pcnt r := Nat.pos_of_ne_zero (fun e => h0 ((pr_zero hA hp).2 e))
          obtain ⟨_, _, hnil⟩ := later_end hA hjn hj0
          rw [hpj] at hnil
          obtain ⟨hm, ht⟩ := tnil (rd_some hnil)
          refine ⟨R.restE r, hm, ?_⟩
          rw [ht]
          show [(col P_NILADDR).eval _, ofN 4, ofN 0, ofN 0] = _
          rw [R.cvP hr, R.colP_x hp (by decide), R.probeX_niladdr r hj0]
        · exact absurd (R.probeX_first ((pr_zero hA hp).1 h0) (by decide) (by decide) (by decide)) hNA
    · exact absurd hbus (by decide)
    · exact absurd hbus (by decide)
    · exact absurd hbus (by decide)
    · exact absurd hbus (by decide)
    · exact absurd hbus (by decide)
    · -- the nil write
      cases hp : R.isP r with
      | false =>
        exfalso; apply hc
        show sPFirst.eval _ + sPLater.eval _ = 0
        simp only [sPFirst, sPLater, E.eval, B.col, cv]
        rw [R.colP_low hp (c := SEL + 12) (by decide), R.colP_low hp (c := SEL + 13) (by decide),
          R.J_sel_probe r (.inl rfl), R.J_sel_probe r (.inr rfl), add_zero']
      | true =>
        obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
        have hnil := probe_nil hA hroots hjn
        rw [hpj] at hnil
        obtain ⟨hm, ht⟩ := tuple_get hnil
        refine ⟨(R.row r).ctr + ((R.seg (R.pcnt r)).k + (R.seg (R.pcnt r)).k), hm, ?_⟩
        rw [ht]
        obtain ⟨_, rCTR, _⟩ := pr_regs hA hK hp
        show [(col CTR).eval _ + (col (S_BASE + 1)).eval _ * ofN 2, ofN 4, ofN 0, ofN 0] = _
        rw [R.cvP hr, R.cvP hr, rCTR, R.colP_x hp (by decide), R.probeX_s r (m := 1) (by decide)]
        show [ofN (R.row r).ctr + ofN (R.seg (R.pcnt r)).k * ofN 2, ofN 4, ofN 0, ofN 0] = _
        rw [← ofN_mul, Nat.mul_two, ← ofN_add]
        rfl

/-- **PW's memory messages are honest**: each writes a marker or its stack
    cell. -/
theorem pw_honest {K HW : Nat} : HonestMem R.A pwAir (R.pwTable K HW) := by
  intro q (hq : q < HW) I hI hbus hc
  have cv : ∀ c, (col c).eval ((R.pwTable K HW).env q) = ofRows (R.pwRows K) q c := by
    intro c; show ofRows (R.pwRows K) ((q + 0) % HW) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
  rcases JRun.ofRows_cases (R.pwRows K) q with ⟨rw, hmem, hrw⟩ | hz
  · obtain ⟨i, _, hm⟩ := List.mem_flatMap.1 hmem
    unfold pwRowsAt at hm
    split at hm
    · next hp =>
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hm
      have hb' := List.mem_range.1 hb
      obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
      obtain ⟨hw, _⟩ := probe_spec hA hjn
      rw [hpj] at hw
      have g : ∀ n, ofRows (R.pwRows K) q n = (pwRow i (R.row i).ctr (R.seg (R.pcnt i)).base (R.seg (R.pcnt i)).k b).getD n 0 :=
        fun n => by rw [hrw]
      simp only [pwAir, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl | rfl | rfl
      · exact absurd hbus (by decide)
      · exact absurd hbus (by decide)
      · have hat := wrs_get hw b (by rw [pcells_length]; omega)
        have e := pcells_atom (b := (R.seg (R.pcnt i)).base) (c := (R.row i).ctr) hb'
        rw [List.getElem?_eq_getElem (by rw [pcells_length]; omega)] at e
        rw [Option.some.inj e] at hat
        obtain ⟨hm', ht⟩ := tuple_get hat
        refine ⟨(R.row i).ctr + b, hm', ?_⟩
        rw [ht]
        simp only [List.map_cons, List.map_nil, E.eval, cv, g, B.c]
        show [ofN (R.row i).ctr + ofN b, ofN 6, ofN (R.seg (R.pcnt i)).base + ofN b, ofN 0] = _
        rw [← ofN_add, ← ofN_add]; rfl
      · have hat := wrs_get hw ((R.seg (R.pcnt i)).k + b) (by rw [pcells_length]; omega)
        have e := pcells_cons (b := (R.seg (R.pcnt i)).base) (c := (R.row i).ctr) hb'
        rw [List.getElem?_eq_getElem (by rw [pcells_length]; omega)] at e
        rw [Option.some.inj e, ← Nat.add_assoc] at hat
        obtain ⟨hm', ht⟩ := tuple_get hat
        refine ⟨(R.row i).ctr + (R.seg (R.pcnt i)).k + b, hm', ?_⟩
        rw [ht]
        simp only [List.map_cons, List.map_nil, E.eval, cv, g, B.c, B.one, ofN_one]
        show [ofN (R.row i).ctr + ofN (R.seg (R.pcnt i)).k + ofN b, ofN 5, ofN (R.row i).ctr + ofN b,
          ofN (R.row i).ctr + ofN (R.seg (R.pcnt i)).k + ofN b + 1] = _
        rw [← ofN_add, ← ofN_add, ← ofN_add, ← ofN_one, ← ofN_add]; rfl
    · cases hm
  · exfalso; apply hc
    simp only [pwAir, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl
    · show -(col 5).eval _ = 0; rw [cv, hz]; decide
    · show (col 5).eval _ = 0; rw [cv, hz]
    · show (col 5).eval _ = 0; rw [cv, hz]
    · show (col 5).eval _ = 0; rw [cv, hz]

/-- **POP's memory messages are honest**: each reads a stack cell. -/
theorem pop_honestP {K HP : Nat} : HonestMem R.A popAir (R.popTableP K HP) := by
  intro q (hq : q < HP) I hI hbus hc
  have cv : ∀ c, (col c).eval ((R.popTableP K HP).env q) = ofRows (R.popRowsP K) q c := by
    intro c; show ofRows (R.popRowsP K) ((q + 0) % HP) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
  simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl
  · exact absurd hbus (by decide)
  · exact absurd hbus (by decide)
  · rcases JRun.ofRows_cases (R.popRowsP K) q with ⟨rw, hmem, hrw⟩ | hz
    · obtain ⟨i, hi, hm⟩ := List.mem_flatMap.1 hmem
      have key : ∃ i' c j s x s' u, rw = popRow i' c j s x s' u ∧ R.A[s]? = some (.cons x s') := by
        rcases List.mem_append.1 hm with hm | hm
        · obtain ⟨i', g, J, j, s, x, s', _, hn, hget, rfl⟩ := R.J.popRows_mem (K := K)
            (List.mem_flatMap.2 ⟨i, hi, hm⟩)
          obtain ⟨_, hAs, _⟩ := R.J.pop_facts hn hget
          exact ⟨i', _, j, s, x, s', _, rfl, hAs⟩
        · obtain ⟨hp, h0, f, s, x, s', hget, rfl⟩ := probePops_mem hm
          obtain ⟨_, hAs, _⟩ := probePop_facts hA hroots hp h0 hget
          exact ⟨i, _, f, s, x, s', _, rfl, hAs⟩
      obtain ⟨i', c, j, s, x, s', u, rfl, hAs⟩ := key
      obtain ⟨hm', ht⟩ := tuple_get hAs
      obtain ⟨_, _, _, g3, g4, g5, _, _, _⟩ := JRun.popRow_get i' c j s x s' u
      refine ⟨s, hm', ?_⟩
      rw [ht]
      simp only [List.map_cons, List.map_nil, cv, hrw, g3, g4, g5, B.c, E.eval]
      rfl
    · exact absurd (by show (col 7).eval _ = 0; rw [cv, hz]) hc
  · exact absurd hbus (by decide)

end PRun

end Circuit
