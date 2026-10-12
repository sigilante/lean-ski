import Ski.Circuit.CompJBal
import Ski.Circuit.JetComplete
import Ski.Circuit.ProbeSat

/-!
# Completeness of the composed circuit with jets

**`compJ_complete_log`**: a jetted composed run within its budgets gives
honest tables that `compJAirs` accepts at the given heights; the program
and segment tables are the public ones.

The blinding blocks of the tables after the CPU carry clear flags, so each
blinded table sends as its base does (`sends_quiet_tail`); the CPU sends as
the jet circuit's CPU off the memory, segment and blinding buses
(`CRun.cpuCJ_jetSends`).  The balance then reuses the jet circuit's.
-/

namespace Circuit

open B Air JetTable Compose CompM Mach

-- ---------------------------------------------------------------------------
-- Quiet interactions and wide tables
-- ---------------------------------------------------------------------------

/-- **Interactions whose counts vanish send nothing.** -/
theorem sends_quiet_tail {X Y : AirD} {T : Table} (L : List Inter) (he : X.inters = Y.inters ++ L)
    (hz : ∀ r, r < T.h → ∀ I ∈ L, I.count.eval (T.env r) = 0) (bus : String) (v : List F) :
    tableSends X T bus v = tableSends Y T bus v := by
  unfold tableSends
  apply foldr_range_congr
  intro r hr
  unfold rowSends
  rw [he, List.foldr_append]
  congr 1
  apply foldr_zero_init
  intro I hI
  rw [hz r hr I hI]
  split <;> rfl

/-- A table clear past the AIR's own columns. -/
def Wide (A : AirD) (T : Table) : Prop := ∀ r, r < T.h → ∀ c, A.width ≤ c → T.main r c = 0

theorem wide_col {A : AirD} {T : Table} (hw : Wide A T) {r : Nat} (hr : r < T.h) {c : Nat} (hc : A.width ≤ c) :
    (col c).eval (T.env r) = 0 := by
  show T.main ((r + 0) % T.h) c = 0
  rw [Nat.add_zero, Nat.mod_eq_of_lt hr]
  exact hw r hr c hc

/-- **A wide table's blocks are quiet**: it sends as the base AIR does. -/
theorem sends_withBlocks_quiet {A : AirD} {blocks : List (String × Bool)} {T : Table} (hw : Wide A T)
    (bus : String) (v : List F) : tableSends (withBlocks A blocks) T bus v = tableSends A T bus v := by
  refine sends_quiet_tail _ (withBlocks_inters A blocks) (fun r hr I hI => ?_) bus v
  obtain ⟨⟨⟨b, send⟩, i⟩, _, rfl⟩ := List.mem_map.1 hI
  have hc := wide_col hw hr (c := A.width + 5 * i + 4) (by omega)
  cases send
  · show -((col (A.width + 5 * i + 4)).eval (T.env r)) = 0
    rw [hc]; exact neg_zero_eq
  · exact hc

/-- **A wide table satisfies the blocks' flags.** -/
theorem sat_withBlocks {A : AirD} {blocks : List (String × Bool)} {T : Table} (h : Sat A T) (hw : Wide A T) :
    Sat (withBlocks A blocks) T := by
  refine ⟨h.1, fun c hc r hr => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact h.2 c hc r hr
  · obtain ⟨⟨b, i⟩, _, rfl⟩ := List.mem_map.1 hc
    show (col (A.width + 5 * i + 4)).eval (T.env r) * ((col (A.width + 5 * i + 4)).eval (T.env r) - 1) = 0
    rw [wide_col hw hr (by omega)]
    exact zero_mul' _

/-- **A blinded table's memory messages are its base's.** -/
theorem honest_withBlocks {M : List Cell} {A : AirD} {blocks : List (String × Bool)} {T : Table}
    (hb : ∀ b ∈ blocks, b.1 ≠ "mem") (h : HonestMem M A T) : HonestMem M (withBlocks A blocks) T := by
  intro r hr I hI hbus hc
  rcases List.mem_append.1 hI with hI | hI
  · exact h r hr I hI hbus hc
  · obtain ⟨b, hbm, hbus', _⟩ := withBlocks_block_bus hI
    exact absurd (hbus' ▸ hbus) (hb b hbm)

/-- A table of rows no wider than `w` is clear from `w` on. -/
theorem ofRows_wide {rows : List (List F)} {w : Nat} (h : ∀ x ∈ rows, x.length ≤ w) (q : Nat) {c : Nat}
    (hc : w ≤ c) : ofRows rows q c = 0 := by
  unfold ofRows
  rcases Nat.lt_or_ge q rows.length with hq | hq
  · rw [List.getD_eq_getElem?_getD (l := rows), List.getElem?_eq_getElem hq, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_trans (h _ (List.getElem_mem hq)) hc)]
    rfl
  · rw [List.getD_eq_getElem?_getD (l := rows), List.getElem?_eq_none hq]
    rfl

theorem provCJ_wide {name : String} {w : Nat} {rows : List (List F)} {cnt : List F → Nat} :
    Wide (providerAir name w rows) (provTableCJ rows cnt) := by
  intro r _ c hc
  show (if c = 0 then _ else 0) = 0
  rw [if_neg (by show c ≠ 0; have : 1 ≤ c := hc; omega)]

/-- **A blinded provider is satisfied and preprocessed.** -/
theorem provCJ_sat {name : String} {w : Nat} {rows : List (List F)} {cnt : List F → Nat}
    {blocks : List (String × Bool)} (h : 0 < rows.length) :
    Sat (withBlocks (providerAir name w rows) blocks) (provTableCJ rows cnt) ∧
      PreIs (withBlocks (providerAir name w rows) blocks) (provTableCJ rows cnt) :=
  ⟨sat_withBlocks ⟨h, fun _ hc => absurd hc List.not_mem_nil⟩ provCJ_wide, ⟨rfl, fun _ _ _ _ => rfl⟩⟩

theorem sends_provCJ' {name : String} {w : Nat} {rows : List (List F)} {cnt : List F → Nat}
    {blocks : List (String × Bool)} (bus : String) (v : List F) :
    tableSends (withBlocks (providerAir name w rows) blocks) (provTableCJ rows cnt) bus v =
      tableSends (providerAir name w rows) (provTableCJ rows cnt) bus v :=
  sends_withBlocks_quiet provCJ_wide bus v

-- ---------------------------------------------------------------------------
-- The memory table
-- ---------------------------------------------------------------------------

/-- The memory's blinding message is quiet: it sends as `memAir`. -/
theorem sends_memC5 {A : List Cell} {cpu prog pop instw pw : AirD} {C Pg Po Iw Pw : Table} (bus : String)
    (v : List F) :
    tableSends memAirC (memTable5 A cpu prog pop instw pw C Pg Po Iw Pw) bus v =
      tableSends memAir (memTable5 A cpu prog pop instw pw C Pg Po Iw Pw) bus v := by
  refine sends_quiet_tail [⟨"blind_b", 1, .neg (col 9), blindFields 5⟩] rfl (fun r hr I hI => ?_) bus v
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  subst hI
  show -((memTable5 A cpu prog pop instw pw C Pg Po Iw Pw).main ((r + 0) % _) 9) = 0
  show -(if 9 = 0 then _ else if 9 = 1 then _ else if 9 = 2 then _ else if 9 = 3 then _ else if 9 = 4 then _
    else (0 : F)) = 0
  exact neg_zero_eq

theorem memC5_sat (A : List Cell) (cpu prog pop instw pw : AirD) (C Pg Po Iw Pw : Table) (hA : 0 < A.length) :
    Sat memAirC (memTable5 A cpu prog pop instw pw C Pg Po Iw Pw) := by
  have h := mem5_sat A cpu prog pop instw pw C Pg Po Iw Pw hA
  refine ⟨hA, fun c hc m hm' => ?_⟩
  have hm : m < (memTable5 A cpu prog pop instw pw C Pg Po Iw Pw).h := hm'
  simp only [memAirC, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact h.2 _ (by simp only [memAir, List.mem_cons, true_or]) m hm
  · exact h.2 _ (by simp only [memAir, List.mem_cons, true_or, or_true]) m hm
  · simp only [B.bool, B.col, B.one, B.c, E.eval, env_main0 hm]
    show (0 : F) * (0 - ofN 1) = 0
    exact zero_mul' _

-- ---------------------------------------------------------------------------
-- The segment bus, for any CPU
-- ---------------------------------------------------------------------------

/-- **`segs` balances**: the segment table receives each segment's tuple as
    often as the CPU sends it, for a CPU that sends only those tuples. -/
theorem bal_segsC {cpu : AirD} {C : Table} {roots : List Nat} (hR : roots.length < P) (hR0 : 0 < roots.length)
    (hcS : ∀ r, r < C.h → ∀ I ∈ cpu.inters, I.bus = "segs" → I.count.eval (C.env r) ≠ 0 →
      ∃ q, q < roots.length ∧ I.fields.map (fun c => c.eval (C.env r)) = [ofN q, ofN (roots.getD q 0)])
    (v : List F) :
    tableSends cpu C "segs" v + tableSends (segsAir roots) (segsTableC roots cpu C) "segs" v = 0 := by
  let Sg := segsTableC roots cpu C
  have hSgh : Sg.h = (segRows roots).length := rfl
  have hrow : ∀ q, q < Sg.h → rowSends (segsAir roots) Sg "segs" v q =
      if q < roots.length ∧ [ofN q, ofN (roots.getD q 0)] = v then -(tableSends cpu C "segs" v) else 0 := by
    intro q hq
    show (if "segs" = "segs" ∧ [(prec 0).eval (Sg.env q), (prec 1).eval (Sg.env q)] = v then
      -((col 0).eval (Sg.env q)) else 0) + 0 = _
    have e0 : (prec 0).eval (Sg.env q) = ((segRows roots).getD q []).getD 0 0 := by
      show Sg.pre ((q + 0) % Sg.h) 0 = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
    have e1 : (prec 1).eval (Sg.env q) = ((segRows roots).getD q []).getD 1 0 := by
      show Sg.pre ((q + 0) % Sg.h) 1 = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
    have em : (col 0).eval (Sg.env q) = if q < roots.length then
        tableSends cpu C "segs" [ofN q, ofN (roots.getD q 0)] else 0 := by
      rw [B.col, E.eval, env_main0 hq]; rfl
    rw [e0, e1, em, add_zero']
    rcases segRows_get hR0 (by rw [← hSgh]; exact hq) with ⟨hq', g⟩ | ⟨hq', g⟩
    · rw [g, if_pos hq']
      by_cases ht : [ofN q, ofN (roots.getD q 0)] = v
      · rw [if_pos ⟨rfl, ht⟩, if_pos ⟨hq', ht⟩, ht]
      · rw [if_neg (fun h => ht h.2), if_neg (fun h => ht h.2)]
    · have hn : ¬ (q < roots.length) := by omega
      simp only [hn, false_and, ↓reduceIte]
      split <;> first | exact neg_zero_eq | rfl
  cases hany : (List.range roots.length).any (fun q => decide ([ofN q, ofN (roots.getD q 0)] = v)) with
  | true =>
    obtain ⟨q0, hq0, e0⟩ := List.any_eq_true.1 hany
    have hq0 := List.mem_range.1 hq0
    have e0 := of_decide_eq_true e0
    have hsg : tableSends (segsAir roots) Sg "segs" v = -(tableSends cpu C "segs" v) := by
      show List.foldr (fun r acc => rowSends (segsAir roots) Sg "segs" v r + acc) 0 (List.range Sg.h) = _
      rw [fold_range_single _ Sg.h q0 (by rw [hSgh]; exact Nat.lt_of_lt_of_le hq0 (segRows_len roots)),
        hrow q0 (by rw [hSgh]; exact Nat.lt_of_lt_of_le hq0 (segRows_len roots)), if_pos ⟨hq0, e0⟩]
      intro q hq hne
      rw [hrow q hq, if_neg]
      rintro ⟨hql, e⟩
      rw [← e0] at e
      have := congrArg List.head? e
      simp only [List.head?_cons, Option.some.injEq] at this
      exact hne (ofN_inj (Nat.lt_trans hql hR) (Nat.lt_trans hq0 hR) this)
    rw [hsg]
    rw [add_comm']; exact neg_add_cancel' _
  | false =>
    have hno : ¬ ∃ q, q < roots.length ∧ v = [ofN q, ofN (roots.getD q 0)] := by
      rintro ⟨q, hq, e⟩
      have := List.any_eq_false.1 hany q (List.mem_range.2 hq)
      exact this (decide_eq_true e.symm)
    have h1 : tableSends cpu C "segs" v = 0 :=
      sends_zero_of (Q := fun w => ∃ q, q < roots.length ∧ w = [ofN q, ofN (roots.getD q 0)])
        (fun r hr I hI hb hc => by obtain ⟨q, hq, e⟩ := hcS r hr I hI hb hc; exact ⟨q, hq, e⟩) hno
    have h2 : tableSends (segsAir roots) Sg "segs" v = 0 := by
      show List.foldr (fun r acc => rowSends (segsAir roots) Sg "segs" v r + acc) 0 (List.range Sg.h) = 0
      apply fold_zero
      intro q hq
      rw [hrow q (List.mem_range.1 hq), if_neg (fun h => hno ⟨q, h.1, h.2.symm⟩)]
    rw [h1, h2]; decide

-- ---------------------------------------------------------------------------
-- The CPU's segment and blinding messages
-- ---------------------------------------------------------------------------

namespace CRun

variable {R : CRun} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCJ R.A m0 R.jroots R.jets R.segRoots nilA R.n R.e R.row)
  {K : Nat} (hK : R.e (R.n - 1) < K)

omit hA hK in
/-- **The CPU's blinding flags are clear**: it sends nothing on the
    blinding buses. -/
theorem cpuCJ_blindZero (hd0 stk0 ctr0 n' nilA' : Nat) {bus : String}
    (hb : bus = "blind_a" ∨ bus = "blind_b" ∨ bus = "blind_c") (v : List F) :
    tableSends (cpuAirCJ hd0 stk0 ctr0 n' nilA') (R.cpuTableCJ K) bus v = 0 := by
  apply sends_zero_of (Q := fun _ => False) _ id
  intro r hr I hI hbus hc
  have cv := cvCJ (R := R) (K := K) hr
  change I ∈ cpuIntersCJ at hI
  rw [cpuIntersCJ_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    apply hc; show -((col (BLAJ + 4)).eval _) = 0
    rw [cv, R.colCJ_blind (by decide) (by decide)]; exact neg_zero_eq
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    apply hc; show (col (BLBJ + 4)).eval _ = 0
    rw [cv, R.colCJ_blind (by decide) (by decide)]
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr =>
    apply hc; show (col (BLCJ + 4)).eval _ = 0
    rw [cv, R.colCJ_blind (by decide) (by decide)]
  all_goals (rcases hb with rfl | rfl | rfl <;> exact absurd hbus (by decide))

include hA in
/-- **The CPU's segment messages name segments.** -/
theorem cpuCJ_segsHonest (hd0 stk0 ctr0 n' nilA' : Nat) (hn : R.segRoots.length = R.n) :
    ∀ r, r < (R.cpuTableCJ K).h → ∀ I ∈ (cpuAirCJ hd0 stk0 ctr0 n' nilA').inters, I.bus = "segs" →
      I.count.eval ((R.cpuTableCJ K).env r) ≠ 0 →
      ∃ q, q < R.segRoots.length ∧ I.fields.map (fun c => c.eval ((R.cpuTableCJ K).env r)) =
        [ofN q, ofN (R.segRoots.getD q 0)] := by
  intro r hr I hI hbus hc
  have hr' : r < K := hr
  have cv := cvCJ (R := R) hr'
  change I ∈ cpuIntersCJ at hI
  rw [cpuIntersCJ_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
    cases hrs : isRestart R.e R.n r with
    | false =>
      exact absurd (show (col RSJ).eval ((R.cpuTableCJ K).env r) = 0 by rw [cv, R.colCJ_rs, hrs]; rfl) hc
    | true =>
      obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hrs
      refine ⟨j + 1, by omega, ?_⟩
      simp only [List.map_cons, List.map_nil, E.eval, cv, B.one, B.c, ofN_one, R.colCJ_cnt, R.colCJ_root,
        cntS_end hA.emono j (by omega)]
      rw [← ofN_one, ← ofN_add]
  all_goals exact absurd hbus (by decide)

end CRun

-- ---------------------------------------------------------------------------
-- POP and INSTW are wide
-- ---------------------------------------------------------------------------

namespace JRun

variable (R : JRun)

theorem pop_wide {K HP : Nat} : Wide popAir (R.popTable K HP) := by
  intro r _ c hc
  show ofRows (R.popRows K) r c = 0
  refine ofRows_wide (w := 8 + RANGE_BITS) (fun x hx => ?_) r hc
  obtain ⟨i, g, J, j, s, x', s', _, _, _, rfl⟩ := R.popRows_mem hx
  simp only [popRow, List.length_append, List.length_cons, List.length_nil, bitsOf_length]
  omega

theorem instw_wide {K HW : Nat} : Wide instwAir (R.instwTable K HW) := by
  intro r _ c hc
  show ofRows (R.instwRows K) r c = 0
  refine ofRows_wide (w := 18) (fun x hx => ?_) r hc
  obtain ⟨i, g, J, j, cl, _, _, _, rfl⟩ := R.instwRows_mem hx
  simp only [instwRow, List.length_append, List.length_cons, List.length_nil, tmplRow_len]
  omega

end JRun

-- ---------------------------------------------------------------------------
-- The balance
-- ---------------------------------------------------------------------------

namespace CRun

variable {R : CRun} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCJ R.A m0 R.jroots R.jets R.segRoots nilA R.n R.e R.row) (hroots : RootsOK m0.heap R.jroots R.jets)
  {K : Nat} (hK : R.e (R.n - 1) < K)

include hA hroots in
/-- **The honest tables of the composed circuit with jets balance.** -/
theorem balancedCJ (hd0 stk0 ctr0 : Nat) {heap : List Cell} {N W : Nat} {Pg Wt : Table}
    (hML : R.A.length < P) (hn : R.segRoots.length = R.n) (hnP : R.n < P)
    {HP HW : Nat} (hHP : (R.J.popRows K).length ≤ HP) (hHW : (R.J.instwRows K).length ≤ HW)
    (hp : HonestMem R.A (progAirC heap N W) Pg) (hw : HonestMem R.A (witAir N W) Wt)
    (hwZ : ∀ r, r < Wt.h → ∀ I ∈ (witAir N W).inters, I.bus ≠ "mem" → I.count.eval (Wt.env r) = 0) :
    Balanced (compJTables hd0 stk0 ctr0 R.n nilA heap N W R.segRoots R.jroots R.jets (R.cpuTableCJ K)
      (memTable5 R.A (cpuAirCJ hd0 stk0 ctr0 R.n nilA) (progAirC heap N W) popAirCJ instwAirCJ (witAir N W)
        (R.cpuTableCJ K) Pg (R.J.popTable K HP) (R.J.instwTable K HW) Wt)
      Pg Wt (segsTableC R.segRoots (cpuAirCJ hd0 stk0 ctr0 R.n nilA) (R.cpuTableCJ K))
      (provTableCJ (rootsRowsCJ R.jroots) (R.J.cntRoots K)) (provTableCJ (hdrRowsCJ R.jets) (R.J.cntHdr K))
      (provTableCJ (tmplRowsCJ R.jets) (R.J.cntTmpl K)) (R.J.popTable K HP) (R.J.instwTable K HW)) := by
  intro bus v
  simp only [compJTables, List.foldr_cons, List.foldr_nil, add_zero']
  have hR0 : 0 < R.segRoots.length := by have := hA.npos; omega
  let cpu := cpuAirCJ hd0 stk0 ctr0 R.n nilA
  let C := R.cpuTableCJ K
  let Po := R.J.popTable K HP
  let Iw := R.J.instwTable K HW
  let Mm := memTable5 R.A cpu (progAirC heap N W) popAirCJ instwAirCJ (witAir N W) C Pg Po Iw Wt
  let Sg := segsTableC R.segRoots cpu C
  let Rt := provTableCJ (rootsRowsCJ R.jroots) (R.J.cntRoots K)
  let Hd := provTableCJ (hdrRowsCJ R.jets) (R.J.cntHdr K)
  let Tm := provTableCJ (tmplRowsCJ R.jets) (R.J.cntTmpl K)
  -- the blinded tables send as their bases
  have ePo : tableSends popAirCJ Po bus v = tableSends popAir Po bus v :=
    sends_withBlocks_quiet R.J.pop_wide bus v
  have eIw : tableSends instwAirCJ Iw bus v = tableSends instwAir Iw bus v :=
    sends_withBlocks_quiet R.J.instw_wide bus v
  -- the tables off their buses
  have zM : bus ≠ "mem" → tableSends memAirC Mm bus v = 0 :=
    fun h => (sends_memC5 bus v).trans (sends_off (one_bus mem_bus (Ne.symm h)))
  have zP : bus ≠ "mem" → tableSends (progAirC heap N W) Pg bus v = 0 :=
    fun h => sends_nobus (fun I hI => by
      simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; exact fun e => h e.symm)
  have zWt : bus ≠ "mem" → tableSends (witAir N W) Wt bus v = 0 :=
    fun h => sends_zero_of (Q := fun _ => False) (fun r hr I hI hb hc => hc (hwZ r hr I hI (hb ▸ h))) id
  have zS : bus ≠ "segs" → tableSends (segsAir R.segRoots) Sg bus v = 0 :=
    fun h => sends_nobus (fun I hI => by
      simp only [segsAir, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; exact fun e => h e.symm)
  have zR : bus ≠ "roots" → tableSends (rootsAirCJ R.jroots) Rt bus v = 0 :=
    fun h => (sends_provCJ' bus v).trans (sends_off (one_bus (prov_bus _ _ _) (Ne.symm h)))
  have zH : bus ≠ "hdr" → tableSends (hdrAirCJ R.jets) Hd bus v = 0 :=
    fun h => (sends_provCJ' bus v).trans (sends_off (one_bus (prov_bus _ _ _) (Ne.symm h)))
  have zT : bus ≠ "tmpl" → tableSends (tmplAirCJ R.jets) Tm bus v = 0 :=
    fun h => (sends_provCJ' bus v).trans (sends_off (one_bus (prov_bus _ _ _) (Ne.symm h)))
  have zO : bus ≠ "popch" → bus ≠ "mem" → bus ≠ "arg" → tableSends popAirCJ Po bus v = 0 :=
    fun h1 h2 h3 => ePo.trans (sends_off (off3 pop_buses (Ne.symm h1) (Ne.symm h2) (Ne.symm h3)))
  have zW : bus ≠ "arg" → bus ≠ "wch" → bus ≠ "tmpl" → bus ≠ "mem" → tableSends instwAirCJ Iw bus v = 0 :=
    fun h1 h2 h3 h4 => eIw.trans (sends_off (off4 instw_buses (Ne.symm h1) (Ne.symm h2) (Ne.symm h3) (Ne.symm h4)))
  by_cases hm : bus = "mem"
  · -- the memory
    subst hm
    rw [zS (by decide), zR (by decide), zH (by decide), zT (by decide), sends_memC5]
    simp only [zero_add']
    have hperm : ∀ a b c : F, a + (b + c) = b + (c + a) := fun a b c => by rw [add_comm' a, add_assoc']
    rw [hperm (tableSends (witAir N W) Wt "mem" v)]
    exact bal_mem5 hML (cpuCJ_honest hA hroots hd0 stk0 ctr0) hp
      (honest_withBlocks (by decide) (R.J.pop_honest (K := K) (HP := HP)))
      (honest_withBlocks (by decide) (R.J.instw_honest (K := K) (HW := HW))) hw v
  rw [zM hm, zP hm, zWt hm]
  by_cases hs : bus = "segs"
  · -- the segments
    subst hs
    rw [zR (by decide), zH (by decide), zT (by decide), zO (by decide) (by decide) (by decide),
      zW (by decide) (by decide) (by decide) (by decide)]
    simp only [zero_add', add_zero']
    exact bal_segsC (by omega) hR0 (cpuCJ_segsHonest hA hd0 stk0 ctr0 R.n nilA hn) v
  rw [zS hs]
  by_cases hb : bus = "blind_a" ∨ bus = "blind_b" ∨ bus = "blind_c"
  · -- the CPU's blinding buses: every flag is clear
    rw [cpuCJ_blindZero hd0 stk0 ctr0 R.n nilA hb v]
    have h1 : bus ≠ "roots" ∧ bus ≠ "hdr" ∧ bus ≠ "tmpl" ∧ bus ≠ "popch" ∧ bus ≠ "arg" ∧ bus ≠ "wch" := by
      rcases hb with rfl | rfl | rfl <;> decide
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h1
    rw [zR h1, zH h2, zT h3, zO h4 hm h5, zW h5 h6 h3 hm]
    decide
  -- the jet buses: the CPU sends as the jet circuit's
  have hbs : bus ≠ "mem" ∧ bus ≠ "segs" ∧ bus ≠ "blind_a" ∧ bus ≠ "blind_b" ∧ bus ≠ "blind_c" :=
    ⟨hm, hs, fun h => hb (.inl h), fun h => hb (.inr (.inl h)), fun h => hb (.inr (.inr h))⟩
  rw [cpuCJ_jetSends hbs hd0 stk0 ctr0 (R.J.row 0).hd (R.J.row 0).stk (R.J.row 0).ctr v]
  have zC : bus ≠ "roots" → bus ≠ "hdr" → bus ≠ "popch" → bus ≠ "wch" → bus ≠ "arg" →
      tableSends (cpuAirJ (R.J.row 0).hd (R.J.row 0).stk (R.J.row 0).ctr) (R.J.cpuTable K) bus v = 0 :=
    fun h2 h3 h4 h5 h6 => sends_off (off6 (cpuJ_buses _ _ _) (Ne.symm hm) (Ne.symm h2) (Ne.symm h3)
      (Ne.symm h4) (Ne.symm h5) (Ne.symm h6))
  by_cases hr : bus = "roots"
  · subst hr
    rw [zH (by decide), zT (by decide), zO (by decide) (by decide) (by decide),
      zW (by decide) (by decide) (by decide) (by decide)]
    have e : tableSends (rootsAirCJ R.jroots) Rt "roots" v = tableSends (providerAir "roots" 2 (rootsRowsCJ R.J.roots))
        (provTable (rootsRowsCJ R.J.roots) (R.J.cntRoots K)) "roots" v := sends_provCJ (by decide) v
    rw [e]
    simp only [zero_add', add_zero']
    exact R.J.bal_rootsCJ v
  rw [zR hr]
  by_cases hh : bus = "hdr"
  · subst hh
    rw [zT (by decide), zO (by decide) (by decide) (by decide),
      zW (by decide) (by decide) (by decide) (by decide)]
    have e : tableSends (hdrAirCJ R.jets) Hd "hdr" v = tableSends (providerAir "hdr" 7 (hdrRowsCJ R.J.jets))
        (provTable (hdrRowsCJ R.J.jets) (R.J.cntHdr K)) "hdr" v := sends_provCJ (by decide) v
    rw [e]
    simp only [zero_add', add_zero']
    exact R.J.bal_hdrCJ v
  rw [zH hh]
  by_cases ht : bus = "tmpl"
  · subst ht
    rw [zC (by decide) (by decide) (by decide) (by decide) (by decide), zO (by decide) (by decide) (by decide),
      eIw]
    have e : tableSends (tmplAirCJ R.jets) Tm "tmpl" v = tableSends (providerAir "tmpl" 11 (tmplRowsCJ R.J.jets))
        (provTable (tmplRowsCJ R.J.jets) (R.J.cntTmpl K)) "tmpl" v := sends_provCJ (by decide) v
    rw [e]
    simp only [zero_add']
    rw [add_comm']
    exact R.J.bal_tmplCJ hHW v
  rw [zT ht]
  by_cases hpc : bus = "popch"
  · subst hpc
    rw [zW (by decide) (by decide) (by decide) (by decide), ePo]
    simp only [zero_add', add_zero']
    exact R.J.bal_popch hHP v
  by_cases hwc : bus = "wch"
  · subst hwc
    rw [zO (by decide) (by decide) (by decide), eIw]
    simp only [zero_add']
    exact R.J.bal_wch hHW v
  by_cases ha : bus = "arg"
  · subst ha
    rw [ePo, eIw]
    simp only [zero_add']
    exact R.J.bal_arg hHP hHW v
  rw [zC hr hh hpc hwc ha, zO hpc hm ha, zW ha hwc ht hm]
  decide

end CRun

-- ---------------------------------------------------------------------------
-- Completeness
-- ---------------------------------------------------------------------------

section

variable {A : List Cell} {m0 : Mach} {jroots : List (Nat × Nat)} {jets : List Air.Jet} {segRoots : List Nat}
  {nilA n : Nat} {e : Nat → Nat} {row : Nat → Air.Row}
  (hA : AcceptsCJ A m0 jroots jets segRoots nilA n e row) (hroots : RootsOK m0.heap jroots jets)
include hA hroots

/-- **Every stack pointer of a jetted composed run is in memory.** -/
theorem _root_.CompM.AcceptsCJ.stk_le (hfit : Fits A) (hnil : nilA ≤ A.length) :
    ∀ i, i ≤ e (n - 1) → (row i).stk ≤ A.length := by
  have hc := hA.ctr_le hroots
  intro i
  induction i with
  | zero => intro _; rw [hA.stk0]; exact hnil
  | succ i ih =>
    intro hi
    cases hr : isRestart e n i with
    | true =>
      obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
      rw [hA.restart j hj]; exact hnil
    | false =>
      rcases hA.trans i (by omega) (AcceptsCJ.notEnd hr) with h | ⟨_, J, _, _, hI⟩ | h
      · exact step_stk hfit h (hc i (by omega)) (hc (i + 1) hi)
      · rcases instRow_stk hfit hI with e' | e'
        · rw [e']; exact ih (by omega)
        · exact Nat.le_of_lt e'
      · rw [h.2]; exact ih (by omega)

/-- **Every head of a jetted composed run is in memory.** -/
theorem _root_.CompM.AcceptsCJ.hd_lt : ∀ i, i ≤ e (n - 1) → (row i).hd < A.length := by
  intro i hi
  let Rn : CRun := ⟨A, jroots, jets, segRoots, e, n, row⟩
  have hJ : JOK Rn.J := hA.jok hroots
  have hn := hA.npos
  have hc := hA.ctr_le hroots i hi
  have hq : Rn.J.rowQ i = row i := CRun.rowQ_J (R := Rn) hi
  have hlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length hA.heap0
    rw [List.length_take, hA.ctr0] at this
    omega
  cases hn' : Rn.J.instAt i with
  | some p =>
    obtain ⟨g, J⟩ := p
    obtain ⟨_, hm, _, _⟩ := JRun.instAt_some hn'
    obtain ⟨_, _, _, htm, _⟩ := hroots _ g hm
    exact Nat.lt_of_lt_of_le (termAt_lt htm) hlen
  | none =>
    have hv : Valid A (row i) := by
      cases hrs : isRestart e n i with
      | false =>
        have := JRun.base_valid hJ hn' hrs
        rwa [hq] at this
      | true =>
        obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hrs
        exact .inr (halt_K (hA.ends j (by omega)).1 (hA.ends j (by omega)).2)
    obtain ⟨cell, hrd, _⟩ := (shape hv).reads 0 (by decide) rfl
    exact Nat.lt_of_lt_of_le (rd_get hrd).1 hc

end

open Stmt Wit in
/-- **Completeness of the composed circuit with jets**, for any evaluation
    statement and a jet table licensed over its heap, at the heights a
    statement names: a jetted run from the composed machine of literal bits
    and a well-formed region, over a memory of `2^Lm` cells whose cells point
    into it, ending within `2^R` rows, its pops and written cells within
    `2^Lp` and `2^Li` rows, with at most `2^8` private cells and all four
    logarithms at most `20`, gives tables that AIRs with the normal forms of
    the composed circuit with jets accept, with Plonky3's selectors; the
    program and segment tables are the public ones, and the tables decode
    back to the memory and the run.  The jet table must have rows (the
    prover panics on an empty one) and fit two-adic heights. -/
theorem compJ_complete_log {R Lm Lp Li : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLp : Lp ≤ 20) (hLi : Li ≤ 20)
    {shp : BT} {Ps : List Term} {W : Nat} {roots : List (Nat × Nat)} {jets : List Air.Jet} {Rs : List AirD}
    (hs : sameAirsB Rs (compJAirs shp Ps W roots jets) = true)
    (hprov : 0 < (rootsRowsCJ roots).length ∧ 0 < (hdrRowsCJ jets).length ∧ 0 < (tmplRowsCJ jets).length)
    (hprov27 : (rootsRowsCJ roots).length ≤ 2 ^ 27 ∧ (hdrRowsCJ jets).length ≤ 2 ^ 27 ∧
      (tmplRowsCJ jets).length ≤ 2 ^ 27)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    (hroots : RootsOK (cMachine ρ shp region Ps).heap roots jets)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCJ A (cMachine ρ shp region Ps) roots jets (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e (Ps.length - 1) < 2 ^ R)
    (hHP : (JRun.popRows ⟨A, roots, jets, e (Ps.length - 1) + 1, row, isRestart e Ps.length⟩ (2 ^ R)).length ≤
      2 ^ Lp)
    (hHW : (JRun.instwRows ⟨A, roots, jets, e (Ps.length - 1) + 1, row, isRestart e Ps.length⟩ (2 ^ R)).length ≤
      2 ^ Li)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8) :
    ∃ C Mm Pg Wt Sg Rt Hd Tm Po Iw, AcceptedP Rs [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] ∧
      C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ Wt.h = 2 ^ 9 ∧ Po.h = 2 ^ Lp ∧ Iw.h = 2 ^ Li ∧
      Pg = progTableC (blankM shp W Ps).heap (BT.nleaves shp) W ∧ Sg = segsPub (blankRoots shp W Ps) ∧
      memOf Mm = A ∧ ∀ i, i ≤ e (Ps.length - 1) → rowOf C i = row i := by
  have hRb : 2 ^ R ≤ 1048576 := Nat.pow_le_pow_right (by decide) hR
  have hLb : 2 ^ Lm ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLm
  have hPb : 2 ^ Lp ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLp
  have hIb : 2 ^ Li ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLi
  have hP0 : 0 < 2 ^ Lp := Nat.two_pow_pos _
  have hI0 : 0 < 2 ^ Li := Nat.two_pow_pos _
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots', hlenm, htake, hpub⟩ :=
    cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have eR : (cHeap ρ shp region Ps).2 = blankRoots shp W Ps := hroots'
  have eN : (cHeap ρ shp region Ps).1.length = (blankM shp W Ps).stk := hstk
  rw [eR, eN] at hA
  obtain ⟨m0, hm0⟩ : ∃ m, cMachine ρ shp region Ps = m := ⟨_, rfl⟩
  rw [hm0] at hA htake hpub hlenm hroots
  have hn : 0 < Ps.length := hA.npos
  have hnR : (blankRoots shp W Ps).length = Ps.length := blankRoots_length _ _ _
  -- the memory holds the machine
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hpre : BT.nleaves shp + 3 + W ≤ m0.heap.length := by
    have := congrArg List.length htake
    simp only [List.length_take, List.length_append, slotHeap_length, hrl] at this
    omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hslot : ∀ k, k < BT.nleaves shp + 3 + W →
      A.getD k .nil = (slotHeap ρ (BT.nleaves shp) ++ region).getD k .nil := by
    intro k hk
    rw [hAm k (by omega)]
    have := congrArg (fun l => l[k]?) htake
    simp only [List.getElem?_take, if_pos (show k < BT.nleaves shp + 3 + region.length by omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hbits : ∀ i, i < BT.nleaves shp → A.getD (3 + i) .nil = .K ∨ A.getD (3 + i) .nil = .app 0 1 := by
    intro i hi
    rw [hslot (3 + i) (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [slotHeap_length]; omega)]
    unfold slotHeap
    rw [List.getElem?_append_right (by simp),
      show 3 + i - ([Cell.K, Cell.I, Cell.app 0 1] : List Cell).length = i by simp, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    cases ρ i
    · exact .inr rfl
    · exact .inl rfl
  have hreg : ∀ i, i < W → cellOK (3 + BT.nleaves shp + i) (A.getD (3 + BT.nleaves shp + i) .nil) = true := by
    intro i hi
    rw [hslot _ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [slotHeap_length]; omega), slotHeap_length,
      show 3 + BT.nleaves shp + i - (BT.nleaves shp + 3) = i by omega]
    have hri : i < region.length := by omega
    rw [List.getElem?_eq_getElem hri, Option.getD_some]
    have := hr i region[i] (List.getElem?_eq_getElem hri)
    rwa [show BT.nleaves shp + 3 + i = 3 + BT.nleaves shp + i by omega] at this
  -- the numbers
  have hPP : P = 2013265921 := rfl
  have hAl : A.length < P := by rw [hlen, hPP]; omega
  have hnK : Ps.length ≤ 2 ^ R := by
    have := emono_ge hA.emono (Ps.length - 1) (by omega); omega
  have hsmall : 3 + BT.nleaves shp + W ≤ 2 ^ 24 := by omega
  have hlenW : 3 + BT.nleaves shp + W ≤ A.length := by omega
  have hbl : (blankM shp W Ps).heap.length = m0.heap.length := hlenm.symm
  have hl24 : A.length ≤ 2 ^ 24 := by omega
  -- the run
  let Rn : CRun := ⟨A, roots, jets, blankRoots shp W Ps, e, Ps.length, row⟩
  have hA' : AcceptsCJ Rn.A m0 Rn.jroots Rn.jets Rn.segRoots (blankM shp W Ps).stk Rn.n Rn.e Rn.row := hA
  have hK' : Rn.e (Rn.n - 1) < 2 ^ R := hK
  have hJ : JOK Rn.J := hA.jok hroots
  -- the tables
  let cpu := cpuAirCJ (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length Ps.length
    (blankM shp W Ps).stk
  let C := Rn.cpuTableCJ (2 ^ R)
  let Pg := progTableC (blankM shp W Ps).heap (BT.nleaves shp) W
  let Wt := witTable A (BT.nleaves shp) W
  let Po := Rn.J.popTable (2 ^ R) (2 ^ Lp)
  let Iw := Rn.J.instwTable (2 ^ R) (2 ^ Li)
  let Mm := memTable5 A cpu (progAirC (blankM shp W Ps).heap (BT.nleaves shp) W) popAirCJ instwAirCJ
    (witAir (BT.nleaves shp) W) C Pg Po Iw Wt
  let Sg := segsTableC (blankRoots shp W Ps) cpu C
  let Rt := provTableCJ (rootsRowsCJ roots) (Rn.J.cntRoots (2 ^ R))
  let Hd := provTableCJ (hdrRowsCJ jets) (Rn.J.cntHdr (2 ^ R))
  let Tm := provTableCJ (tmplRowsCJ jets) (Rn.J.cntTmpl (2 ^ R))
  have hcpu : Sat cpu C := by
    have := CRun.cpuCJ_sat hA' hroots hK' hl24
    have eAir : cpuAirCJ (Rn.row 0).hd (Rn.row 0).stk (Rn.row 0).ctr Rn.n (blankM shp W Ps).stk = cpu := by
      show cpuAirCJ (row 0).hd (row 0).stk (row 0).ctr Ps.length _ = _
      rw [hA.hd0, hA.stk0, hA.ctr0, ← hbl]; rfl
    rw [eAir] at this
    exact this
  have hpubA : ∀ i, i < (blankM shp W Ps).heap.length →
      ¬ (3 ≤ i ∧ i < 3 + BT.nleaves shp + W) →
      i < A.length ∧ A.getD i .nil = (blankM shp W Ps).heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by omega
    refine ⟨by omega, ?_⟩
    have hor : i < 3 ∨ BT.nleaves shp + 3 + region.length ≤ i := by
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact .inl h3
      · refine .inr ?_
        have := Nat.le_of_not_lt (fun hlt => hp ⟨h3, hlt⟩)
        omega
    rw [hAm i hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hpub i hor]
    rfl
  have hbal : Balanced (compJTables (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length
      Ps.length (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W (blankRoots shp W Ps) roots jets
      C Mm Pg Wt Sg Rt Hd Tm Po Iw) :=
    CRun.balancedCJ hA' hroots _ _ _ hAl hnR (show Ps.length < P by omega) hHP hHW
      (fun r hr I hI _ hc => progC_honest hpubA r hr I hI hc)
      (witT_honest (a0 := 3) (fun _ => by decide) hbits hreg hlenW) witT_blindZero
  have hacc : Accepted (compJAirs shp Ps W roots jets) [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] := by
    have z : (compJAirs shp Ps W roots jets).zip [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] =
        compJTables (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length
          Ps.length (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
          (blankRoots shp W Ps) roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw := by
      have z0 : (compJAirs shp Ps W roots jets).zip [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] =
          compJTables (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length
            (blankRoots shp W Ps).length (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
            (blankRoots shp W Ps) roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw := rfl
      rw [z0, hnR]
    have hPg : Pg.h ≤ 2 ^ 24 := progRowsC_le (by omega)
    have hSg : Sg.h ≤ 2 ^ 24 := segRows_le (by rw [hnR]; omega)
    have hWt : Wt.h = 2 ^ 9 := witRows_len hNW
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [z]
      intro p hp
      simp only [compJTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hcpu, .inl rfl⟩
      · exact ⟨memC5_sat A _ _ _ _ _ _ _ _ _ _ (by omega), .inl rfl⟩
      · exact ⟨(progC_sat _ _ _).1, .inr (progC_sat _ _ _).2⟩
      · exact ⟨wit_sat (a0 := 3) (fun _ => by decide) hbits hreg hsmall, .inr ⟨rfl, fun _ _ _ _ => rfl⟩⟩
      · exact ⟨⟨segRows_pos _, fun c hc => nomatch hc⟩, .inr ⟨rfl, fun _ _ _ _ => rfl⟩⟩
      · exact ⟨(provCJ_sat hprov.1).1, .inr (provCJ_sat hprov.1).2⟩
      · exact ⟨(provCJ_sat hprov.2.1).1, .inr (provCJ_sat hprov.2.1).2⟩
      · exact ⟨(provCJ_sat hprov.2.2).1, .inr (provCJ_sat hprov.2.2).2⟩
      · exact ⟨sat_withBlocks (Rn.J.pop_sat hJ hl24 hP0) Rn.J.pop_wide, .inl rfl⟩
      · exact ⟨sat_withBlocks (Rn.J.instw_sat hI0) Rn.J.instw_wide, .inl rfl⟩
    · rw [z]; exact hbal
    · rw [z]
      unfold HeightsOK compJTables
      simp only [List.foldr_cons, List.foldr_nil]
      have hC : C.h = 2 ^ R := rfl
      have hMm : Mm.h = 2 ^ Lm := hlen
      have hPo : Po.h = 2 ^ Lp := rfl
      have hIw : Iw.h = 2 ^ Li := rfl
      have hRt : Rt.h ≤ 2 ^ 27 := hprov27.1
      have hHd : Hd.h ≤ 2 ^ 27 := hprov27.2.1
      have hTm : Tm.h ≤ 2 ^ 27 := hprov27.2.2
      show 19 * C.h + (1 * Mm.h + (1 * Pg.h + (2 * Wt.h + (0 * Sg.h + (1 * Rt.h + (2 * Hd.h + (2 * Tm.h +
        (5 * Po.h + (8 * Iw.h + 0))))))))) < P
      omega
    · rw [z]
      intro p hp
      simp only [compJTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show 2 ^ R ≤ 2 ^ 27; exact Nat.pow_le_pow_right (by decide) (by omega)
      · show A.length ≤ 2 ^ 27; omega
      · show Pg.h ≤ 2 ^ 27; omega
      · show Wt.h ≤ 2 ^ 27; omega
      · show Sg.h ≤ 2 ^ 27; omega
      · exact hprov27.1
      · exact hprov27.2.1
      · exact hprov27.2.2
      · show 2 ^ Lp ≤ 2 ^ 27; exact Nat.pow_le_pow_right (by decide) (by omega)
      · show 2 ^ Li ≤ 2 ^ 27; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hRs : AcceptedP Rs [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] :=
    (acceptedP_iff_of (compJ_guarded shp Ps W roots jets) hs _).2 (accepted_transfer (sameAirsB_symm hs) hacc)
  refine ⟨C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw, hRs, rfl, hlen, witRows_len hNW, rfl, rfl, rfl,
    CRun.segs_honestCJ hA' hK' _ _ _ _ _ hnR (show Ps.length < P by omega), ?_, ?_⟩
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
    have hnil : (blankM shp W Ps).stk ≤ A.length := by
      show (cHeap _ _ _ _).1.length ≤ _
      have : (cHeap (fun _ => false) shp (List.replicate W .S) Ps).1.length + 1 =
          (blankM shp W Ps).heap.length := by
        show _ = ((cHeap _ _ _ _).1 ++ [Cell.nil]).length; simp
      omega
    have hc := hA.ctr_le hroots i hi
    have hst := hA.stk_le hroots hfit hnil i hi
    have hh := hA.hd_lt hroots i hi
    have hq : Rn.J.rowQ i = row i := CRun.rowQ_J (R := Rn) hi
    show (⟨(Rn.cpuColCJ i HD).val, (Rn.cpuColCJ i STK).val, (Rn.cpuColCJ i CTR).val⟩ : Air.Row) = row i
    rw [Rn.colCJ_reg i (by decide), Rn.colCJ_reg i (by decide), Rn.colCJ_reg i (by decide), hq,
      cpuCol_hd, cpuCol_stk, cpuCol_ctr, val_ofN (by omega), val_ofN (by omega), val_ofN (by omega)]

open Stmt Wit in
/-- **Completeness for the verifier's jet table**: `compJ_complete_log`
    for a jet table the verifier's statement check accepts
    (`Air.jetStmtC`), whose roots are then licensed over the filled heap. -/
theorem compJStmt_complete_log {R Lm Lp Li : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLp : Lp ≤ 20) (hLi : Li ≤ 20)
    {shp : BT} {Ps : List Term} {W : Nat} {text : String} {tmpls : List (List Nat × OTerm)} {Rs : List AirD}
    (hj : jetStmtC text shp W Ps tmpls = true)
    (hs : sameAirsB Rs (compJAirs shp Ps W (jetTableC shp W Ps tmpls).1 (jetTableC shp W Ps tmpls).2) = true)
    (hprov : 0 < (rootsRowsCJ (jetTableC shp W Ps tmpls).1).length ∧
      0 < (hdrRowsCJ (jetTableC shp W Ps tmpls).2).length ∧ 0 < (tmplRowsCJ (jetTableC shp W Ps tmpls).2).length)
    (hprov27 : (rootsRowsCJ (jetTableC shp W Ps tmpls).1).length ≤ 2 ^ 27 ∧
      (hdrRowsCJ (jetTableC shp W Ps tmpls).2).length ≤ 2 ^ 27 ∧
      (tmplRowsCJ (jetTableC shp W Ps tmpls).2).length ≤ 2 ^ 27)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCJ A (cMachine ρ shp region Ps) (jetTableC shp W Ps tmpls).1 (jetTableC shp W Ps tmpls).2
      (cHeap ρ shp region Ps).2 (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e (Ps.length - 1) < 2 ^ R)
    (hHP : (JRun.popRows ⟨A, (jetTableC shp W Ps tmpls).1, (jetTableC shp W Ps tmpls).2, e (Ps.length - 1) + 1,
      row, isRestart e Ps.length⟩ (2 ^ R)).length ≤ 2 ^ Lp)
    (hHW : (JRun.instwRows ⟨A, (jetTableC shp W Ps tmpls).1, (jetTableC shp W Ps tmpls).2, e (Ps.length - 1) + 1,
      row, isRestart e Ps.length⟩ (2 ^ R)).length ≤ 2 ^ Li)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8) :
    ∃ C Mm Pg Wt Sg Rt Hd Tm Po Iw, AcceptedP Rs [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] ∧
      C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ Wt.h = 2 ^ 9 ∧ Po.h = 2 ^ Lp ∧ Iw.h = 2 ^ Li ∧
      Pg = progTableC (blankM shp W Ps).heap (BT.nleaves shp) W ∧ Sg = segsPub (blankRoots shp W Ps) ∧
      memOf Mm = A ∧ ∀ i, i ≤ e (Ps.length - 1) → rowOf C i = row i :=
  compJ_complete_log hR hLm hLp hLi hs hprov hprov27 hrl hr (jetStmtC_sound hj ρ region hrl) hA hfit hlen hK
    hHP hHW hNW

end Circuit
