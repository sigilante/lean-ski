import Ski.Circuit.JetKind
import Ski.Circuit.Flow
import Ski.Circuit.RowSound

/-!
# Soundness of the jet circuit

Tables accepted for the jet circuit of a term, with licensed roots and a
jet table whose numbers fit, are a run of `Air.AcceptsJ` over the decoded
memory (`jetExport_sound`), so by `Air.air_sound_jet` they end on a value
the term evaluates to.

- **Corpus rows.**  A row of the eleven kinds satisfies the corpus CPU's
  constraints (`rowSat_ofJ`), and its reads and writes are memory rows by
  the `mem` bus: `RowOK` applies, and it steps or halts.
- **Lookups.**  A message on `ROOTS`, `HDR`, `TMPL` or `ARG` with count `1`
  is a row of its provider (`provider_row`, `bus_hit_on`).
- **Chains.**  The `POPCH` and `WCH` buses are flows (`Ski/Circuit/Flow.lean`):
  an instantiation's chains are exactly one path each, of `k` POP rows
  and `n` INSTW rows, and no other POP row is active at its counter.
- **An instantiation row** is `Air.instRow` for the jet at a licensed root.
-/

namespace Circuit

open B Air JetTable

def jetTables (hd0 stk0 ctr0 : Nat) (heap : List Cell) (roots : List (Nat × Nat)) (jets : List Air.Jet)
    (C Mm Pg Rt Hd Tm Po Iw : Table) : List (AirD × Table) :=
  [(cpuAirJ hd0 stk0 ctr0, C), (memAir, Mm), (progAir heap, Pg), (rootsAir roots, Rt), (hdrAir jets, Hd),
   (tmplAir jets, Tm), (popAir, Po), (instwAir, Iw)]

/-- **What an accepted proof of the jet circuit gives.** -/
structure JetOK (hd0 stk0 ctr0 : Nat) (heap : List Cell) (roots : List (Nat × Nat)) (jets : List Air.Jet)
    (C Mm Pg Rt Hd Tm Po Iw : Table) : Prop where
  cpu : Sat (cpuAirJ hd0 stk0 ctr0) C
  mem : Sat memAir Mm
  po : Sat popAir Po
  iw : Sat instwAir Iw
  pgpre : PreIs (progAir heap) Pg
  rtpre : PreIs (rootsAir roots) Rt
  hdpre : PreIs (hdrAir jets) Hd
  tmpre : PreIs (tmplAir jets) Tm
  bal : Balanced (jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw)
  hts : HeightsOK (jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw)
  two : TwoAdic (jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw)

-- ---------------------------------------------------------------------------
-- The providers' rows
-- ---------------------------------------------------------------------------

theorem map_getD_self : ∀ x : List F, (List.range x.length).map (fun i => x.getD i 0) = x := by
  intro x
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

theorem padCopies_mem {x : List F} : ∀ {rows : List (List F)}, x ∈ padCopies rows → x ∈ rows
  | [], h => nomatch h
  | r :: rs, h => by
    rcases List.mem_append.1 h with h | h
    · exact h
    · rw [List.eq_of_mem_replicate h]; exact List.mem_cons_self

theorem padCopies_len {w : Nat} : ∀ {rows : List (List F)}, (∀ x ∈ rows, x.length = w) →
    ∀ x ∈ padCopies rows, x.length = w :=
  fun h x hx => h x (padCopies_mem hx)

/-- **A provider row that sends a tuple holds it.** -/
theorem provider_row {name : String} {w : Nat} {rows : List (List F)} {T : Table}
    (hpre : PreIs (providerAir name w rows) T) (hlen : ∀ x ∈ rows, x.length = w) {q : Nat} (hq : q < T.h)
    {v : List F} (h : rowSends (providerAir name w rows) T name v q ≠ 0) : v ∈ rows := by
  have hq' : q < rows.length := by rw [← show T.h = rows.length from hpre.1]; exact hq
  have hf : ((List.range w).map prec).map (fun e => e.eval (T.env q)) = v := by
    apply Decidable.byContradiction
    intro hne
    apply h
    simp only [rowSends, providerAir, List.foldr_cons, List.foldr_nil]
    rw [if_neg (fun h' => hne h'.2), add_zero']
  rw [← hf, List.map_map]
  have e : ∀ i, i < w → (fun e => E.eval (T.env q) e) (prec i) = rows[q].getD i 0 := by
    intro i hi
    show T.pre ((q + 0) % T.h) i = _
    rw [Nat.add_zero, Nat.mod_eq_of_lt hq, hpre.2 q i hq hi]
    show (rows.getD q []).getD i 0 = _
    rw [List.getD_eq_getElem?_getD (l := rows), List.getElem?_eq_getElem hq']; rfl
  have hx := hlen _ (List.getElem_mem hq')
  have : (List.range w).map ((fun e => E.eval (T.env q) e) ∘ prec) = (List.range w).map (fun i => rows[q].getD i 0) :=
    List.map_congr_left (fun i hi => e i (List.mem_range.1 hi))
  rw [this, ← hx, map_getD_self]
  exact List.getElem_mem hq'

theorem rootsRows_mem {roots : List (Nat × Nat)} {v : List F} (h : v ∈ rootsRows roots) :
    ∃ a g, (a, g) ∈ roots ∧ v = [ofN a, ofN g] := by
  obtain ⟨⟨a, g⟩, hm, e⟩ := List.mem_map.1 (padCopies_mem h)
  exact ⟨a, g, hm, e.symm⟩

theorem rootsRows_len (roots : List (Nat × Nat)) : ∀ x ∈ rootsRows roots, x.length = 2 :=
  padCopies_len (fun x hx => by obtain ⟨_, _, e⟩ := List.mem_map.1 hx; rw [← e]; rfl)

theorem opCols_len (o : Op) : (opCols o).length = 4 := by cases o <;> rfl

theorem hdrRows_mem {jets : List Air.Jet} {v : List F} (h : v ∈ hdrRows jets) :
    ∃ J g, jets[g]? = some J ∧ v = hdrRow J g := by
  obtain ⟨⟨J, g⟩, hm, e⟩ := List.mem_map.1 (padCopies_mem h)
  obtain ⟨_, hg, hJ⟩ := List.mem_zipIdx hm
  simp only [Nat.zero_add, Nat.sub_zero] at hg hJ
  exact ⟨J, g, by rw [List.getElem?_eq_getElem hg, hJ], e.symm⟩

theorem hdrRows_len (jets : List Air.Jet) : ∀ x ∈ hdrRows jets, x.length = 7 :=
  padCopies_len (fun x hx => by
    obtain ⟨⟨J, g⟩, _, e⟩ := List.mem_map.1 hx
    rw [← e]; show (_ ++ opCols _).length = 7; rw [List.length_append, opCols_len]; rfl)

theorem tmplRow_len (g j : Nat) (cl : Nat × Option (Op × Op)) : (tmplRow g j cl).length = 11 := by
  obtain ⟨tag, ops⟩ := cl
  cases ops with
  | some ab => obtain ⟨a, b⟩ := ab; simp only [tmplRow, List.length_append, opCols_len]; rfl
  | none => rfl

theorem tmplRows_mem {jets : List Air.Jet} {v : List F} (h : v ∈ tmplRows jets) :
    ∃ J g j cl, jets[g]? = some J ∧ (symCells J J.body 0).1[j]? = some cl ∧ v = tmplRow g j cl := by
  obtain ⟨⟨J, g⟩, hm, hv⟩ := List.mem_flatMap.1 (padCopies_mem h)
  obtain ⟨_, hg, hJ⟩ := List.mem_zipIdx hm
  simp only [Nat.zero_add, Nat.sub_zero] at hg hJ
  obtain ⟨⟨cl, j⟩, hm2, e⟩ := List.mem_map.1 hv
  obtain ⟨_, hj, hcl⟩ := List.mem_zipIdx hm2
  simp only [Nat.zero_add, Nat.sub_zero] at hj hcl
  exact ⟨J, g, j, cl, by rw [List.getElem?_eq_getElem hg, hJ], by rw [List.getElem?_eq_getElem hj, hcl], e.symm⟩

theorem tmplRows_len (jets : List Air.Jet) : ∀ x ∈ tmplRows jets, x.length = 11 :=
  padCopies_len (fun x hx => by
    obtain ⟨_, _, hv⟩ := List.mem_flatMap.1 hx
    obtain ⟨⟨cl, j⟩, _, e⟩ := List.mem_map.1 hv
    rw [← e]; exact tmplRow_len _ _ _)

/-- A row sends nothing on a bus its table has no message on. -/
theorem rowSends_nobus {A : AirD} {T : Table} {B : String} {v : List F} {q : Nat}
    (h : ∀ I ∈ A.inters, I.bus ≠ B) : rowSends A T B v q = 0 := by
  unfold rowSends
  apply fold_zero
  intro I hI
  rw [if_neg (fun h' => h I hI h'.1)]

/-- A column a table constrains to a bit is `0` or `1`. -/
theorem col_bit {A : AirD} {T : Table} (hs : Sat A T) {i : Nat} (hc : bool (col i) ∈ A.cons) {r : Nat}
    (hr : r < T.h) : T.main r i * (T.main r i - 1) = 0 := by
  have := hs.2 _ hc r hr
  simpa [B.bool, E.eval, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem bit_val_le {x : F} (h : x * (x - 1) = 0) : x.val ≤ 1 := by
  rcases val_of_bit h with e | e <;> omega

section

variable {hd0 stk0 ctr0 : Nat} {heap : List Cell} {roots : List (Nat × Nat)} {jets : List Air.Jet}
  {C Mm Pg Rt Hd Tm Po Iw : Table} (h : JetOK hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw)
include h

theorem JetOK.cpu_h : C.h ≤ 2 ^ 27 := h.two (cpuAirJ hd0 stk0 ctr0, C) (by simp [jetTables])
theorem JetOK.mem_h : Mm.h ≤ 2 ^ 27 := h.two (memAir, Mm) (by simp [jetTables])
theorem JetOK.hdr_h : Hd.h ≤ 2 ^ 27 := h.two (hdrAir jets, Hd) (by simp [jetTables])
theorem JetOK.tmpl_h : Tm.h ≤ 2 ^ 27 := h.two (tmplAir jets, Tm) (by simp [jetTables])
theorem JetOK.pop_h : Po.h ≤ 2 ^ 27 := h.two (popAir, Po) (by simp [jetTables])
theorem JetOK.instw_h : Iw.h ≤ 2 ^ 27 := h.two (instwAir, Iw) (by simp [jetTables])

/-- The CPU's corpus messages count `0` or `1`, on every row. -/
theorem JetOK.cpu_count {r : Nat} (hr : r < C.h) : ∀ I ∈ cpuInters, (I.count.eval (C.env r)).val ≤ 1 := by
  obtain ⟨k, hk, hsel⟩ := kind_ofJ h.cpu hr
  rcases Nat.lt_or_ge k 11 with h11 | h11
  · have e := hsel 11 (by decide)
    rw [if_neg (Nat.ne_of_gt h11)] at e
    exact cpu_countR (rowSat_ofJ h.cpu hr e) hr
  · have hk11 : k = 11 := Nat.le_antisymm (Nat.le_of_lt_succ hk) h11
    subst hk11
    obtain ⟨ha, _, happ, hS, _⟩ := inst_facts hr hsel
    have z : (0 : F).val ≤ 1 := by decide
    intro I hI
    simp only [cpuInters, writeInters, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show ((acts.getD 0 zero).eval _).val ≤ 1; rw [ha 0 (by decide)]; exact z
    · show ((acts.getD 1 zero).eval _).val ≤ 1; rw [ha 1 (by decide)]; exact z
    · show ((acts.getD 2 zero).eval _).val ≤ 1; rw [ha 2 (by decide)]; exact z
    · show ((acts.getD 3 zero).eval _).val ≤ 1; rw [ha 3 (by decide)]; exact z
    · show (sApp.eval _).val ≤ 1; rw [happ]; exact z
    all_goals (show (sS.eval _).val ≤ 1; rw [hS]; exact z)

theorem JetOK.inst_bit {r : Nat} (hr : r < C.h) : (C.main r (SEL + 11)).val ≤ 1 :=
  bit_val_le (sel_bitJ h.cpu hr (i := 11) (by decide))

omit h in
theorem cpuJ_weights : ∀ I ∈ cpuInters ++ jetInters, 1 ≤ I.weight := by
  have : (cpuInters ++ jetInters).all (fun I => decide (1 ≤ I.weight)) = true := by decide
  exact fun I hI => of_decide_eq_true (List.all_eq_true.1 this I hI)

/-- The CPU sends on `mem`, `roots`, `hdr` and `arg` with bits. -/
theorem JetOK.cpu_sender {bus : String} (hB : bus = "mem" ∨ bus = "roots" ∨ bus = "hdr" ∨ bus = "arg") :
    SenderOn bus (cpuAirJ hd0 stk0 ctr0, C) := by
  refine ⟨fun I hI _ => cpuJ_weights I hI, fun r hr I hI hbus => ?_⟩
  rcases List.mem_append.1 hI with hI | hI
  · exact h.cpu_count hr I hI
  · simp only [jetInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    have hsel := h.inst_bit hr
    have hra := bit_val_le (flag_bits h.cpu hr).2.1
    have ci : (sInst.eval (C.env r)).val ≤ 1 := by
      simp only [sInst, B.col, E.eval, env_main0 hr]; exact hsel
    have no : ∀ b : String, b ≠ "mem" → b ≠ "roots" → b ≠ "hdr" → b ≠ "arg" → b ≠ bus := by
      intro b h1 h2 h3 h4 e
      rcases hB with rfl | rfl | rfl | rfl
      · exact h1 e
      · exact h2 e
      · exact h3 e
      · exact h4 e
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ci
    · exact ci
    · exact absurd hbus (no "popch" (by decide) (by decide) (by decide) (by decide))
    · exact absurd hbus (no "popch" (by decide) (by decide) (by decide) (by decide))
    · exact absurd hbus (no "wch" (by decide) (by decide) (by decide) (by decide))
    · exact absurd hbus (no "wch" (by decide) (by decide) (by decide) (by decide))
    · show ((col J_RA).eval (C.env r)).val ≤ 1; rw [col_eval hr]; exact hra

/-- The program table sends on `mem` with bits. -/
theorem JetOK.prog_sender : SenderOn "mem" (progAir heap, Pg) := by
  refine ⟨fun I hI _ => by simp only [progAir, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]; decide,
    fun r hr I hI _ => ?_⟩
  simp only [progAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  subst hI
  show ((prec 4).eval _).val ≤ 1
  rw [prec_eval h.pgpre hr (by show 4 < 5; decide)]
  rcases programRows_row heap r with e | e <;> rw [show (progAir heap).pretrace = programRows heap from rfl, e] <;>
    decide

theorem JetOK.pop_act {q : Nat} (hq : q < Po.h) : Po.main q 7 * (Po.main q 7 - 1) = 0 :=
  col_bit h.po (by simp [popAir, popCons]) hq

theorem JetOK.instw_act {q : Nat} (hq : q < Iw.h) : Iw.main q 17 * (Iw.main q 17 - 1) = 0 :=
  col_bit h.iw (by simp [instwAir, instwCons]) hq

/-- POP sends on `mem` with bits. -/
theorem JetOK.pop_sender : SenderOn "mem" (popAir, Po) := by
  refine ⟨fun I hI hb => ?_, fun r hr I hI hb => ?_⟩
  · simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl <;> first | decide | exact absurd hb (by decide)
  · simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
    · show ((col 7).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le (h.pop_act hr)
    · exact absurd hb (by decide)

/-- INSTW sends on `mem`, `tmpl` and `arg` with bits. -/
theorem JetOK.instw_sender {bus : String} (hB : bus = "mem" ∨ bus = "tmpl" ∨ bus = "arg") :
    SenderOn bus (instwAir, Iw) := by
  refine ⟨fun I hI _ => ?_, fun r hr I hI hb => ?_⟩
  · simp only [instwAir, instwInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [instwAir, instwInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    have b6 := col_bit h.iw (i := 6) (by simp [instwAir, instwCons]) hr
    have b10 := col_bit h.iw (i := 10) (by simp [instwAir, instwCons]) hr
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl
    · show ((col 6).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le b6
    · show ((col 10).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le b10
    · rcases hB with rfl | rfl | rfl <;> exact absurd hb (by decide)
    · rcases hB with rfl | rfl | rfl <;> exact absurd hb (by decide)
    · show ((col 17).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le (h.instw_act hr)
    · show ((col 17).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le (h.instw_act hr)

/-- **A `mem` message with count `1` is a memory row.** -/
theorem JetOK.memHit {v : List F}
    (hit : ∃ p ∈ jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw,
      (p.1.name == "mem" || p.1.name == "roots" || p.1.name == "hdr" || p.1.name == "tmpl") = false ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit_on h.bal h.hts
    (fun p => p.1.name == "mem" || p.1.name == "roots" || p.1.name == "hdr" || p.1.name == "tmpl")
    (fun p hp hpr => by
      simp only [jetTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.cpu_sender (.inl rfl)
      · exact nomatch hpr
      · exact h.prog_sender
      · exact nomatch hpr
      · exact nomatch hpr
      · exact nomatch hpr
      · exact h.pop_sender
      · exact h.instw_sender (.inl rfl)) hit
  simp only [jetTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nomatch hpr
  · refine ⟨m, hm, ?_⟩
    have hm' : m < Mm.h := hm
    apply Decidable.byContradiction
    intro hv
    apply hne
    simp only [rowSends, memAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, B.col,
      E.eval, env_main0 hm']
    rw [if_neg (fun h' => hv h'.2), add_zero']
  · exact nomatch hpr
  · exact absurd (rowSends_nobus (fun I hI => by
      simp only [rootsAir, providerAir, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]; decide)) hne
  · exact absurd (rowSends_nobus (fun I hI => by
      simp only [hdrAir, providerAir, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]; decide)) hne
  · exact absurd (rowSends_nobus (fun I hI => by
      simp only [tmplAir, providerAir, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]; decide)) hne
  · exact nomatch hpr
  · exact nomatch hpr

/-- **The corpus rows are a corpus-CPU circuit's.** -/
theorem JetOK.row : RowOK hd0 stk0 ctr0 C Mm :=
  ⟨h.cpu.1, fun _ _ hr hk => rowSat_ofJ h.cpu hr (by rw [hk.2 11 (by decide), if_neg (Nat.ne_of_gt hk.1)]), mem_addr h.mem, h.mem_h, fun r hr I hI hbus hc =>
    h.memHit ⟨(cpuAirJ hd0 stk0 ctr0, C), by simp [jetTables], rfl, r, hr, I, List.mem_append_left _ hI, hbus,
      rfl, hc⟩⟩

/-- A memory message with count `1`, decoded: the cell at its address. -/
theorem JetOK.cell {a t x y : F}
    (hm : ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = [a, t, x, y]) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) := h.row.cell hm

/-- **A lookup on a provider's bus finds one of its rows.**  `B` is the
    provider's bus; the senders are the tables `sender` names. -/
theorem JetOK.lookup {bus : String} (sender : AirD × Table → Bool)
    (hs : ∀ p ∈ jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw, sender p = true → SenderOn bus p)
    {v : List F}
    (hit : ∃ p ∈ jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw, sender p = true ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = bus ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ p ∈ jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw, sender p = false ∧
      ∃ r, r < p.2.h ∧ rowSends p.1 p.2 bus v r ≠ 0 := by
  obtain ⟨p, hp, hpr, r, hr, hne⟩ := bus_hit_on h.bal h.hts (fun p => !sender p)
    (fun p hp hpr => hs p hp (by cases hq : sender p <;> simp_all))
    (by obtain ⟨p, hp, hsp, rest⟩ := hit; exact ⟨p, hp, by rw [hsp]; rfl, rest⟩)
  exact ⟨p, hp, by cases hq : sender p <;> simp_all, r, hr, hne⟩

omit h in
/-- The tables' names, for picking senders. -/
theorem jetTables_names {p : AirD × Table}
    (hp : p ∈ jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw) :
    p = (cpuAirJ hd0 stk0 ctr0, C) ∨ p = (memAir, Mm) ∨ p = (progAir heap, Pg) ∨ p = (rootsAir roots, Rt) ∨
      p = (hdrAir jets, Hd) ∨ p = (tmplAir jets, Tm) ∨ p = (popAir, Po) ∨ p = (instwAir, Iw) := by
  simp only [jetTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  exact hp

omit h in
theorem notBus {A : AirD} {T : Table} {bus : String} {v : List F} {q : Nat}
    (hA : A.inters.all (fun I => I.bus != bus) = true) : rowSends A T bus v q = 0 :=
  rowSends_nobus (fun I hI e => by
    have := List.all_eq_true.1 hA I hI
    rw [e] at this; exact absurd this (by simp))

/-- **An instantiation's root is listed.** -/
theorem JetOK.rootsHit {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) :
    ∃ a g, (a, g) ∈ roots ∧ C.main r HD = ofN a ∧ C.main r J_G = ofN g := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "roots") (fun p => p.1.name == "cpu")
    (fun p hp hs => by
      rcases jetTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.cpu_sender (.inr (.inl rfl))
      all_goals exact absurd hs (ne_true_of_eq_false rfl))
    (v := [C.main r HD, C.main r J_G])
    ⟨_, List.mem_cons_self, rfl, r, hr, ⟨"roots", 1, sInst, [col HD, col J_G]⟩,
      List.mem_append_right _ List.mem_cons_self, rfl,
      by simp only [List.map_cons, List.map_nil, col_eval hr],
      by simp only [sInst, col_eval hr, hi]⟩
  rcases jetTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · obtain ⟨a, g, hm, e⟩ := rootsRows_mem (provider_row h.rtpre (rootsRows_len roots) hq hne)
    simp only [List.cons.injEq, and_true] at e
    exact ⟨a, g, hm, e.1, e.2⟩
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne

/-- **An instantiation's header is its jet's.** -/
theorem JetOK.hdrHit {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) :
    ∃ J g, jets[g]? = some J ∧ [C.main r J_G, C.main r J_K, C.main r J_N, C.main r J_RL, C.main r J_RA,
      C.main r J_RG, C.main r J_RV] = hdrRow J g := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "hdr") (fun p => p.1.name == "cpu")
    (fun p hp hs => by
      rcases jetTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.cpu_sender (.inr (.inr (.inl rfl)))
      all_goals exact absurd hs (ne_true_of_eq_false rfl))
    (v := [C.main r J_G, C.main r J_K, C.main r J_N, C.main r J_RL, C.main r J_RA, C.main r J_RG, C.main r J_RV])
    ⟨_, List.mem_cons_self, rfl, r, hr,
      ⟨"hdr", 1, sInst, [col J_G, col J_K, col J_N, col J_RL, col J_RA, col J_RG, col J_RV]⟩,
      List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl,
      by simp only [List.map_cons, List.map_nil, col_eval hr],
      by simp only [sInst, col_eval hr, hi]⟩
  rcases jetTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · obtain ⟨J, g, hJ, e⟩ := hdrRows_mem (provider_row h.hdpre (hdrRows_len jets) hq hne)
    exact ⟨J, g, hJ, e⟩
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne

/-- **An active INSTW row's template is a row of its jet.** -/
theorem JetOK.tmplHit {w : Nat} (hw : w < Iw.h) (ha : Iw.main w 17 = 1) :
    ∃ J g j cl, jets[g]? = some J ∧ (symCells J J.body 0).1[j]? = some cl ∧
      (List.range 11).map (fun i => Iw.main w (2 + i)) = tmplRow g j cl := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "tmpl") (fun p => p.1.name == "instw")
    (fun p hp hs => by
      rcases jetTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact h.instw_sender (.inr (.inl rfl)) | exact absurd hs (ne_true_of_eq_false rfl))
    (v := (List.range 11).map (fun i => Iw.main w (2 + i)))
    ⟨(instwAir, Iw), by simp [jetTables], rfl, w, hw, ⟨"tmpl", 1, col 17, (List.range 11).map fun i => col (2 + i)⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))), rfl,
      by rw [List.map_map]; exact List.map_congr_left (fun i _ => col_eval hw _),
      by rw [col_eval hw, ha]⟩
  rcases jetTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact tmplRows_mem (provider_row h.tmpre (tmplRows_len jets) hq hne)
  · exact absurd (notBus rfl) hne
  · exact absurd hpr (ne_false_of_eq_true rfl)

/-- **An argument lookup finds an active POP row.** -/
theorem JetOK.argHit {v : List F}
    (hit : ∃ p ∈ jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw,
      (p.1.name == "cpu" || p.1.name == "instw") = true ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "arg" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ q, q < Po.h ∧ Po.main q 7 = 1 ∧ [Po.main q 0, Po.main q 2, Po.main q 4] = v := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "arg") (fun p => p.1.name == "cpu" || p.1.name == "instw")
    (fun p hp hs => by
      rcases jetTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact h.cpu_sender (.inr (.inr (.inr rfl)))
        | exact h.instw_sender (.inr (.inr rfl))
        | exact absurd hs (ne_true_of_eq_false rfl)) hit
  rcases jetTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · -- a POP row: its use count is nonzero, so it is active
    have hq' : q < Po.h := hq
    have cv := col_eval hq'
    have hf : [Po.main q 0, Po.main q 2, Po.main q 4] = v := by
      apply Decidable.byContradiction
      intro hv
      apply hne
      simp only [rowSends, popAir, popInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
      rw [if_neg (fun h' => absurd h'.1 (by decide)), if_neg (fun h' => absurd h'.1 (by decide)),
        if_neg (fun h' => absurd h'.1 (by decide)), if_neg (fun h' => hv (by rw [← h'.2, cv, cv, cv])),
        add_zero', add_zero', add_zero', add_zero']
    have huse : Po.main q 6 ≠ 0 := by
      intro h0
      apply hne
      simp only [rowSends, popAir, popInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
      rw [if_neg (fun h' => absurd h'.1 (by decide)), if_neg (fun h' => absurd h'.1 (by decide)),
        if_neg (fun h' => absurd h'.1 (by decide))]
      split
      · simp only [E.eval, cv, h0]; decide
      · decide
    have hc := h.po.2 (.mul (col 6) (.sub one (col 7))) (by simp [popAir, popCons]) q hq'
    simp only [E.eval, cv, B.one, B.c, ofN_one] at hc
    rcases mul_eq_zero hc with e | e
    · exact absurd e huse
    · exact ⟨q, hq', (sub_eq_zero e).symm, hf⟩
  · exact absurd hpr (ne_false_of_eq_true rfl)

end

-- ---------------------------------------------------------------------------
-- The template's shape, and the numbers that must fit
-- ---------------------------------------------------------------------------

/-- **A template cell is a leaf or an application.** -/
theorem symCells_cells (J : Air.Jet) : ∀ (body : OTerm) (off : Nat), ∀ cl ∈ (symCells J body off).1,
    (cl.2 = none ∧ cl.1 < 3) ∨ (cl.1 = 3 ∧ ∃ a b, cl.2 = some (a, b))
  | .S, _, cl, h => by simp only [symCells, List.mem_singleton] at h; subst h; exact .inl ⟨rfl, by decide⟩
  | .K, _, cl, h => by simp only [symCells, List.mem_singleton] at h; subst h; exact .inl ⟨rfl, by decide⟩
  | .I, _, cl, h => by simp only [symCells, List.mem_singleton] at h; subst h; exact .inl ⟨rfl, by decide⟩
  | .var _, _, cl, h => by simp only [symCells, List.not_mem_nil] at h
  | .app f a, off, cl, h => by
    unfold symCells at h
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exact symCells_cells J f off cl h
      · exact symCells_cells J a _ cl h
    · rw [List.mem_singleton] at h; subst h; exact .inr ⟨rfl, _, _, rfl⟩

/-- **A local root is a written cell.** -/
theorem symCells_root_local (J : Air.Jet) : ∀ (body : OTerm) (off j : Nat),
    (symCells J body off).2 = .local_ j → j < off + (symCells J body off).1.length
  | .S, off, j, h => by simp only [symCells, Op.local_.injEq] at h; subst h; show off < off + 1; omega
  | .K, off, j, h => by simp only [symCells, Op.local_.injEq] at h; subst h; show off < off + 1; omega
  | .I, off, j, h => by simp only [symCells, Op.local_.injEq] at h; subst h; show off < off + 1; omega
  | .var x, off, j, h => by
    show j < off + 0
    have e : (symCells J (.var x) off).2 = varOp J x := rfl
    rw [e] at h
    unfold varOp at h
    split at h <;> cases h
  | .app f a, off, j, h => by
    unfold symCells at h ⊢
    simp only [Op.local_.injEq] at h
    simp only [List.length_append, List.length_singleton]
    omega

theorem opSmall_val {o : Op} (h : opSmall o = true) :
    ∀ n, (o = .local_ n ∨ o = .arg n ∨ o = .glob n) → n < 2 ^ 24 := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;> exact of_decide_eq_true h

/-- `wrsG` holds when each cell is where it is written. -/
theorem wrsG_of {g : Nat → Option Cell} : ∀ (ws : List Cell) (c : Nat),
    (∀ j, (hj : j < ws.length) → g (c + j) = some ws[j]) → wrsG g c ws = true
  | [], _, _ => rfl
  | w :: ws, c, h => by
    show ((g c == some w) && wrsG g (c + 1) ws) = true
    have h0 := h 0 (by simp)
    rw [Nat.add_zero, show (w :: ws)[0] = w from rfl] at h0
    rw [h0, beq_iff_eq.2 rfl, Bool.true_and]
    exact wrsG_of ws (c + 1) (fun j hj => by
      have := h (j + 1) (by simp only [List.length_cons]; omega)
      rw [show c + (j + 1) = c + 1 + j by omega] at this
      exact this)

/-- A term read from a heap starts inside it. -/
theorem termAt_lt {heap : List Cell} : ∀ {f a : Nat} {u : Term}, Mach.termAt heap f a = some u → a < heap.length
  | 0, _, _, h => by cases h
  | f + 1, a, u, h => by
    unfold Mach.termAt at h
    cases ha : heap[a]? with
    | none => rw [ha] at h; cases h
    | some _ => exact (List.getElem?_eq_some_iff.1 ha).1

/-- Bits weighted by powers of two: a number below `2^n`. -/
theorem bitsVal_lt {T : Table} {r : Nat} (hr : r < T.h) (b : Nat) :
    ∀ n, n ≤ 24 → (∀ i, i < n → T.main r (b + i) * (T.main r (b + i) - 1) = 0) →
    (((List.range n).foldl (fun v i => E.add v (E.mul (col (b + i)) (c (2 ^ i)))) zero).eval (T.env r)).val < 2 ^ n
  | 0, _, _ => by show (0 : Nat) < 1; decide
  | n + 1, hn, hb => by
    have ih := bitsVal_lt hr b n (Nat.le_of_succ_le hn) (fun i hi => hb i (Nat.lt_succ_of_lt hi))
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize ((List.range n).foldl (fun v i => E.add v (E.mul (col (b + i)) (c (2 ^ i)))) zero) = X at ih ⊢
    simp only [E.eval, B.col, B.c, env_main0 hr]
    generalize X.eval (T.env r) = x at ih ⊢
    have hpow : 2 ^ (n + 1) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hn
    have hP : 2 ^ 24 < P := by decide
    rcases bit_of (hb n (Nat.lt_succ_self n)) with e | e <;> rw [e]
    · rw [zero_mul', add_zero']
      exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
    · rw [one_mul', val_add_nat (by rw [Nat.pow_succ] at hpow; omega), Nat.pow_succ]
      omega

-- ---------------------------------------------------------------------------
-- Chains: the flows of POPCH and WCH
-- ---------------------------------------------------------------------------

/-- Four atoms, for identities by normal forms. -/
def at4 (a b c d : F) : Atom → F
  | .main 0 0 => a | .main 0 1 => b | .main 0 2 => c | .main 0 3 => d | _ => 0

/-- `(a - b) + (X - Y) = (a + X) - (b + Y)`. -/
theorem sub_add_sub' (a b x y : F) : (a - b) + (x - y) = (a + x) - (b + y) :=
  E.eval_eq_of_norm
    (e := .add (.sub (.atom (.main 0 0)) (.atom (.main 0 1))) (.sub (.atom (.main 0 2)) (.atom (.main 0 3))))
    (e' := .sub (.add (.atom (.main 0 0)) (.atom (.main 0 2))) (.add (.atom (.main 0 1)) (.atom (.main 0 3))))
    (by decide) (at4 a b x y)

/-- `(a - b) + (y - x) = 0` gives `a + y = b + x`. -/
theorem bal_sub {a b x y : F} (h : (a - b) + (y - x) = 0) : a + y = b + x := by
  have e : a + y = ((a - b) + (y - x)) + (b + x) :=
    E.eval_eq_of_norm
      (e := .add (.atom (.main 0 0)) (.atom (.main 0 3)))
      (e' := .add (.add (.sub (.atom (.main 0 0)) (.atom (.main 0 1))) (.sub (.atom (.main 0 3)) (.atom (.main 0 2))))
        (.add (.atom (.main 0 1)) (.atom (.main 0 2))))
      (by decide) (at4 a b x y)
  rw [e, h, zero_add']

theorem fold_acc (f : Nat → F) (x : F) : ∀ l : List Nat,
    l.foldr (fun b acc => f b + acc) x = l.foldr (fun b acc => f b + acc) 0 + x
  | [] => (zero_add' x).symm
  | b :: l => by simp only [List.foldr_cons]; rw [fold_acc f x l, add_assoc']

/-- A sum of numbers, in the field. -/
theorem fold_ofN (a : Nat → Nat) : ∀ H, (List.range H).foldr (fun q acc => ofN (a q) + acc) 0 = ofN (sumTo H a)
  | 0 => rfl
  | H + 1 => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, fold_acc, fold_ofN a H, add_zero']
    show _ = ofN (sumTo H a + a H)
    rw [ofN_add]

theorem fold_sub (x y : Nat → F) : ∀ l : List Nat,
    l.foldr (fun q acc => (x q - y q) + acc) 0 =
      l.foldr (fun q acc => x q + acc) 0 - l.foldr (fun q acc => y q + acc) 0
  | [] => by show (0 : F) = 0 - 0; decide
  | q :: l => by simp only [List.foldr_cons]; rw [fold_sub x y l, sub_add_sub']

/-- A table sends nothing on a bus it has no message on. -/
theorem sends_nobus' {A : AirD} {T : Table} {bus : String} {v : List F}
    (hA : A.inters.all (fun I => I.bus != bus) = true) : tableSends A T bus v = 0 :=
  fold_zero _ _ (fun _ _ => notBus hA)

/-- A bit, gating a test, is an indicator. -/
theorem bit_ite {x : F} (hb : x * (x - 1) = 0) (P : Prop) [Decidable P] :
    (if P then x else 0) = ofN (if decide (x = 1) && decide P then 1 else 0) := by
  rcases bit_of hb with rfl | rfl
  · rw [show decide ((0 : F) = 1) = false from rfl, Bool.false_and,
      if_neg (show ¬ (false = true) from Bool.false_ne_true)]
    split <;> rfl
  · rw [show decide ((1 : F) = 1) = true from rfl, Bool.true_and]
    cases hp : decide P with
    | true => rw [if_pos (of_decide_eq_true hp), if_pos rfl]; rfl
    | false => rw [if_neg (of_decide_eq_false hp), if_neg (by decide)]; rfl

/-- A chain message, split into its key and its node. -/
theorem dec_msg (a b c d t u l s : F) :
    decide ([a, b, c, d] = [t, u, l, s]) = (decide (a = t) && decide (b = u) && decide ((c, [d]) = (l, [s]))) := by
  simp only [List.cons.injEq, Prod.mk.injEq, and_true, Bool.decide_and, Bool.and_assoc]

theorem foldr_zero_init {α : Type} (f : α → F) (x : F) : ∀ l : List α, (∀ a ∈ l, f a = 0) →
    l.foldr (fun a acc => f a + acc) x = x
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.foldr_cons]
    rw [h a List.mem_cons_self, foldr_zero_init f x l (fun b hb => h b (List.mem_cons_of_mem _ hb)), zero_add']

theorem foldr_range_congr {f g : Nat → F} : ∀ H, (∀ q, q < H → f q = g q) →
    (List.range H).foldr (fun q acc => f q + acc) 0 = (List.range H).foldr (fun q acc => g q + acc) 0
  | 0, _ => rfl
  | H + 1, h => by
    rw [List.range_succ, List.foldr_append, List.foldr_append, List.foldr_cons, List.foldr_cons, List.foldr_nil,
      List.foldr_nil, h H (Nat.lt_succ_self H), fold_acc, fold_acc g,
      foldr_range_congr H (fun q hq => h q (Nat.lt_succ_of_lt hq))]

theorem sumTo_le_one {f : Nat → Nat} (hf : ∀ q, f q ≤ 1) : ∀ H, sumTo H f ≤ H
  | 0 => Nat.le_refl 0
  | H + 1 => by
    show sumTo H f + f H ≤ H + 1
    have := sumTo_le_one hf H; have := hf H; omega

theorem sumTo_zero {f : Nat → Nat} (hf : ∀ q, f q = 0) : ∀ H, sumTo H f = 0
  | 0 => rfl
  | H + 1 => by show sumTo H f + f H = 0; rw [sumTo_zero hf H, hf H]

/-- The CPU's messages on a bus other than `mem` are its jet messages. -/
theorem cpu_rowSends_jet {hd0 stk0 ctr0 : Nat} {C : Table} {bus : String} (hb : bus ≠ "mem") (v : List F)
    (r : Nat) : rowSends (cpuAirJ hd0 stk0 ctr0) C bus v r =
      jetInters.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval (C.env r)) = v then
        I.count.eval (C.env r) else 0) + acc) 0 := by
  unfold rowSends
  show (cpuInters ++ jetInters).foldr _ 0 = _
  rw [List.foldr_append]
  apply foldr_zero_init
  intro I hI
  have hm : I.bus = "mem" := by
    have : cpuInters.all (fun I => I.bus == "mem") = true := by decide
    exact beq_iff_eq.1 (List.all_eq_true.1 this I hI)
  exact if_neg (fun (h' : I.bus = bus ∧ _) => hb (h'.1 ▸ hm))

theorem fold_single (f : Nat → F) : ∀ L m0, m0 < L → (∀ m, m < L → m ≠ m0 → f m = 0) →
    (List.range L).foldr (fun b acc => f b + acc) 0 = f m0
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | L + 1, m0, hm0, hz => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, fold_acc]
    rcases Nat.lt_or_ge m0 L with h | h
    · rw [fold_single f L m0 h (fun m hm hne => hz m (Nat.lt_succ_of_lt hm) hne),
        hz L (Nat.lt_succ_self L) (Nat.ne_of_gt h), add_zero', add_zero']
    · have e : m0 = L := Nat.le_antisymm (Nat.le_of_lt_succ hm0) h
      subst e
      rw [fold_zero f _ (fun m hm => hz m (Nat.lt_succ_of_lt (List.mem_range.1 hm))
        (Nat.ne_of_lt (List.mem_range.1 hm))), zero_add', add_zero']

/-- The chain's ends at an instantiation row, for instantiation counter `c'`. -/
def popStart (C : Table) (r0 : Nat) (c' : F) : Option Node :=
  if c' = C.main r0 CTR then some ((0 : F), [C.main r0 STK]) else none
def popEnd (C : Table) (r0 : Nat) (c' : F) : Option Node :=
  if c' = C.main r0 CTR then some (C.main r0 J_K, [C.main r0 J_REST]) else none

/-- A test on a four-element message, as a test on its node. -/
theorem msg_ite (t c0 c' a b l s : F) (x : F) :
    (if [t, c0, a, b] = [t, c', l, s] then x else 0) =
      if (if c' = c0 then some (a, [b]) else none) = some (l, [s]) then x else 0 := by
  rcases (inferInstance : Decidable (c' = c0)) with hc | hc
  · rw [if_neg hc, if_neg (show ¬ ((none : Option Node) = some (l, [s])) from fun e => by cases e),
      if_neg (show ¬ ([t, c0, a, b] = [t, c', l, s]) from
        fun e => hc (by simp only [List.cons.injEq] at e; exact e.2.1.symm))]
  · rw [if_pos hc, hc]
    cases hd : decide ((a, [b]) = (l, [s])) with
    | true =>
      have e := of_decide_eq_true hd
      simp only [Prod.mk.injEq, List.cons.injEq, and_true] at e
      rw [if_pos (show [t, c0, a, b] = [t, c0, l, s] by rw [e.1, e.2]),
        if_pos (show some (a, [b]) = some (l, [s]) by rw [e.1, e.2])]
    | false =>
      have e := of_decide_eq_false hd
      rw [if_neg (show ¬ ([t, c0, a, b] = [t, c0, l, s]) from
          fun h' => e (by simp only [List.cons.injEq] at h'; rw [h'.2.2.1, h'.2.2.2.1])),
        if_neg (show ¬ (some (a, [b]) = some (l, [s])) from fun h' => e (Option.some.inj h'))]

/-- The INSTW rows at counter `t`, instantiation counter `c0` and jet `g0`,
    as edges: from `(j, [])` to `(j + 1, [])`. -/
def wchEdges (Iw : Table) (t c0 g0 : F) : Edges :=
  ⟨Iw.h, fun q => decide (Iw.main q 17 = 1) && decide (Iw.main q 0 = t) && decide (Iw.main q 1 = c0) &&
      decide (Iw.main q 2 = g0),
    fun q => Iw.main q 3, fun _ => [], fun _ => []⟩

theorem dec_msgW (a b c d t u g l : F) :
    decide ([a, b, c, d] = [t, u, g, l]) =
      (decide (a = t) && decide (b = u) && decide (c = g) && decide ((d, ([] : List F)) = (l, []))) := by
  simp only [List.cons.injEq, Prod.mk.injEq, and_true, Bool.decide_and, Bool.and_assoc]

theorem msg_iteW (t c0 g0 a l : F) (x : F) :
    (if [t, c0, g0, a] = [t, c0, g0, l] then x else 0) =
      if (some (a, ([] : List F)) : Option Node) = some (l, []) then x else 0 := by
  cases hd : decide (a = l) with
  | true =>
    have e := of_decide_eq_true hd
    rw [if_pos (show [t, c0, g0, a] = [t, c0, g0, l] by rw [e]),
      if_pos (show (some (a, ([] : List F)) : Option Node) = some (l, []) by rw [e])]
  | false =>
    have e := of_decide_eq_false hd
    rw [if_neg (show ¬ ([t, c0, g0, a] = [t, c0, g0, l]) from
        fun h' => e (by simp only [List.cons.injEq] at h'; exact h'.2.2.2.1)),
      if_neg (show ¬ ((some (a, ([] : List F)) : Option Node) = some (l, [])) from
        fun h' => e (congrArg Prod.fst (Option.some.inj h')))]

/-- The POP rows at counter `t` and instantiation counter `c'`, as edges:
    from `(i, [s])` to `(i + 1, [s'])`. -/
def popEdges (Po : Table) (t c' : F) : Edges :=
  ⟨Po.h, fun q => decide (Po.main q 7 = 1) && decide (Po.main q 0 = t) && decide (Po.main q 1 = c'),
    fun q => Po.main q 2, fun q => [Po.main q 3], fun q => [Po.main q 5]⟩

section

variable {hd0 stk0 ctr0 : Nat} {heap : List Cell} {roots : List (Nat × Nat)} {jets : List Air.Jet}
  {C Mm Pg Rt Hd Tm Po Iw : Table} (h : JetOK hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw)
include h

/-- A POP row's chain messages: its outgoing edge less its incoming one. -/
theorem JetOK.pop_rowSends {q : Nat} (hq : q < Po.h) (t c' l s : F) :
    rowSends popAir Po "popch" [t, c', l, s] q =
      ofN (if (popEdges Po t c').act q && decide ((popEdges Po t c').outN q = (l, [s])) then 1 else 0) -
      ofN (if (popEdges Po t c').act q && decide ((popEdges Po t c').inN q = (l, [s])) then 1 else 0) := by
  have cv := col_eval hq
  have hb := h.pop_act hq
  simp only [rowSends, popAir, popInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, cv,
    B.one, B.c, ofN_one, true_and, false_and, ↓reduceIte, add_zero']
  rw [if_neg (show ¬ ("mem" = "popch" ∧ [Po.main q 3, ofN 5, Po.main q 4, Po.main q 5] = [t, c', l, s]) from
      fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "popch" ∧ [Po.main q 0, Po.main q 2, Po.main q 4] = [t, c', l, s]) from
      fun h' => absurd h'.1 (by decide)), add_zero', add_zero']
  have eneg : ∀ (P : Prop) [Decidable P] (x : F), (if P then -x else 0) = -(if P then x else 0) := by
    intro P _ x; split
    · rfl
    · decide
  rw [eneg, bit_ite hb, bit_ite hb, dec_msg, dec_msg, sub_eq_add_neg' _ _, add_comm']
  have ea : (popEdges Po t c').act q = (decide (Po.main q 7 = 1) && decide (Po.main q 0 = t) &&
      decide (Po.main q 1 = c')) := rfl
  have ei : (popEdges Po t c').inN q = (Po.main q 2, [Po.main q 3]) := rfl
  have eo : (popEdges Po t c').outN q = (Po.main q 2 + 1, [Po.main q 5]) := rfl
  rw [ea, ei, eo]
  simp only [Bool.and_assoc]

/-- The CPU's chain-start and chain-end messages on `POPCH`. -/
theorem JetOK.cpu_popch (r : Nat) (v : List F) : rowSends (cpuAirJ hd0 stk0 ctr0) C "popch" v r =
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), 0, C.env r (.main 0 STK)] = v then
      C.env r (.main 0 (SEL + 11)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_K), C.env r (.main 0 J_REST)] = v then
      -C.env r (.main 0 (SEL + 11)) else 0) := by
  rw [cpu_rowSends_jet (by decide)]
  simp only [jetInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col, B.c, sInst,
    true_and, ofN_zero]
  rw [if_neg (show ¬ ("roots" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

/-- **`POPCH` is a flow**: at an instantiation row's counter, with a supply
    where the row starts its pops and a demand where it ends them, when the
    instantiation counter is the row's. -/
theorem JetOK.popConserve {r0 : Nat} (hr0 : r0 < C.h) (hi : C.main r0 (SEL + 11) = 1) (c' : F) :
    (popEdges Po (ofN r0) c').Conserve (popStart C r0 c') (popEnd C r0 c') := by
  intro v
  obtain ⟨l, st⟩ := v
  have hCP : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  have hPo : Po.h < P := Nat.lt_of_le_of_lt h.pop_h (by decide)
  -- a node whose state is not one element carries nothing
  have zero_case : (∀ x : F, st ≠ [x]) →
      (popEdges Po (ofN r0) c').cntOut (l, st) + Edges.oneIf (popStart C r0 c') (l, st) =
        (popEdges Po (ofN r0) c').cntIn (l, st) + Edges.oneIf (popEnd C r0 c') (l, st) := by
    intro hst
    have z1 : (popEdges Po (ofN r0) c').cntOut (l, st) = 0 := sumTo_zero (fun q => by
      rw [show decide ((popEdges Po (ofN r0) c').outN q = (l, st)) = false from
        decide_eq_false (fun e => hst _ (congrArg Prod.snd e).symm), Bool.and_false]; rfl) _
    have z2 : (popEdges Po (ofN r0) c').cntIn (l, st) = 0 := sumTo_zero (fun q => by
      rw [show decide ((popEdges Po (ofN r0) c').inN q = (l, st)) = false from
        decide_eq_false (fun e => hst _ (congrArg Prod.snd e).symm), Bool.and_false]; rfl) _
    have o1 : Edges.oneIf (popStart C r0 c') (l, st) = 0 := by
      unfold Edges.oneIf popStart; split
      · exact if_neg (fun e => hst _ (congrArg Prod.snd (Option.some.inj e)).symm)
      · exact if_neg (fun e => by cases e)
    have o2 : Edges.oneIf (popEnd C r0 c') (l, st) = 0 := by
      unfold Edges.oneIf popEnd; split
      · exact if_neg (fun e => hst _ (congrArg Prod.snd (Option.some.inj e)).symm)
      · exact if_neg (fun e => by cases e)
    rw [z1, z2, o1, o2]
  match st with
  | [] => exact zero_case (fun _ e => by cases e)
  | _ :: _ :: _ => exact zero_case (fun _ e => by cases e)
  | [s] =>
    have hb := h.bal "popch" [ofN r0, c', l, s]
    simp only [jetTables, List.foldr_cons, List.foldr_nil] at hb
    rw [sends_nobus' (A := memAir) rfl, sends_nobus' (A := progAir heap) rfl, sends_nobus' (A := rootsAir roots) rfl,
      sends_nobus' (A := hdrAir jets) rfl, sends_nobus' (A := tmplAir jets) rfl, sends_nobus' (A := instwAir) rfl,
      zero_add', zero_add', zero_add', zero_add', zero_add', add_zero', add_zero'] at hb
    -- the POP rows
    have hpop : tableSends popAir Po "popch" [ofN r0, c', l, s] =
        ofN ((popEdges Po (ofN r0) c').cntOut (l, [s])) - ofN ((popEdges Po (ofN r0) c').cntIn (l, [s])) := by
      unfold tableSends
      rw [foldr_range_congr Po.h (fun q hq => h.pop_rowSends hq _ _ _ _), fold_sub, fold_ofN, fold_ofN]
      rfl
    -- the CPU: only the instantiation row sends at its counter
    have hcpu : tableSends (cpuAirJ hd0 stk0 ctr0) C "popch" [ofN r0, c', l, s] =
        ofN (Edges.oneIf (popStart C r0 c') (l, [s])) - ofN (Edges.oneIf (popEnd C r0 c') (l, [s])) := by
      unfold tableSends
      rw [fold_single _ C.h r0 hr0 (fun r hr hne => by
        rw [h.cpu_popch, env_main0 hr, env_main0 hr, clk_eq h.cpu r hr]
        have hne' : ofN r ≠ ofN r0 := fun e => hne (ofN_inj (Nat.lt_trans hr hCP) (Nat.lt_trans hr0 hCP) e)
        rw [if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)),
          if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)), add_zero'])]
      rw [h.cpu_popch]
      simp only [env_main0 hr0, clk_eq h.cpu r0 hr0, hi]
      rw [msg_ite, msg_ite]
      unfold Edges.oneIf popStart popEnd
      have ep : ∀ (o : Option Node), (if o = some (l, [s]) then (1 : F) else 0) =
          ofN (if o = some (l, [s]) then 1 else 0) := by
        intro o; split <;> rfl
      have en : ∀ (o : Option Node), (if o = some (l, [s]) then -(1 : F) else 0) =
          -ofN (if o = some (l, [s]) then 1 else 0) := by
        intro o; split
        · rfl
        · decide
      rw [ep, en, ← sub_eq_add_neg']
    rw [hcpu, hpop] at hb
    have e := bal_sub hb
    rw [← ofN_add, ← ofN_add] at e
    have b1 := sumTo_le_one (f := fun q => if (popEdges Po (ofN r0) c').act q &&
      decide ((popEdges Po (ofN r0) c').outN q = (l, [s])) then 1 else 0) (fun q => by split <;> decide) Po.h
    have b2 := sumTo_le_one (f := fun q => if (popEdges Po (ofN r0) c').act q &&
      decide ((popEdges Po (ofN r0) c').inN q = (l, [s])) then 1 else 0) (fun q => by split <;> decide) Po.h
    have o1 : Edges.oneIf (popStart C r0 c') (l, [s]) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have o2 : Edges.oneIf (popEnd C r0 c') (l, [s]) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have hP : Po.h + 1 < P := Nat.lt_of_le_of_lt (Nat.add_le_add_right h.pop_h 1) (by decide)
    have e' := ofN_inj (Nat.lt_of_le_of_lt (Nat.add_le_add o1 b1) (by rw [Nat.add_comm]; exact hP))
      (Nat.lt_of_le_of_lt (Nat.add_le_add o2 b2) (by rw [Nat.add_comm]; exact hP)) e
    show sumTo Po.h _ + _ = sumTo Po.h _ + _
    omega

/-- An INSTW row's chain messages: its outgoing edge less its incoming one. -/
theorem JetOK.instw_rowSends {q : Nat} (hq : q < Iw.h) (t c0 g0 l : F) :
    rowSends instwAir Iw "wch" [t, c0, g0, l] q =
      ofN (if (wchEdges Iw t c0 g0).act q && decide ((wchEdges Iw t c0 g0).outN q = (l, [])) then 1 else 0) -
      ofN (if (wchEdges Iw t c0 g0).act q && decide ((wchEdges Iw t c0 g0).inN q = (l, [])) then 1 else 0) := by
  have cv := col_eval hq
  have hb := h.instw_act hq
  simp only [rowSends, instwAir, instwInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval,
    cv, B.one, B.c, ofN_one, true_and, ↓reduceIte, add_zero']
  rw [if_neg (show ¬ ("arg" = "wch" ∧ [Iw.main q 0, Iw.main q 8, Iw.main q 15] = [t, c0, g0, l]) from
      fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "wch" ∧ [Iw.main q 0, Iw.main q 12, Iw.main q 16] = [t, c0, g0, l]) from
      fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("tmpl" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']
  have eneg : ∀ (P : Prop) [Decidable P] (x : F), (if P then -x else 0) = -(if P then x else 0) := by
    intro P _ x; split
    · rfl
    · decide
  rw [eneg, bit_ite hb, bit_ite hb, dec_msgW, dec_msgW, sub_eq_add_neg' _ _, add_comm']
  have ea : (wchEdges Iw t c0 g0).act q = (decide (Iw.main q 17 = 1) && decide (Iw.main q 0 = t) &&
      decide (Iw.main q 1 = c0) && decide (Iw.main q 2 = g0)) := rfl
  have ei : (wchEdges Iw t c0 g0).inN q = (Iw.main q 3, []) := rfl
  have eo : (wchEdges Iw t c0 g0).outN q = (Iw.main q 3 + 1, []) := rfl
  rw [ea, ei, eo]
  simp only [Bool.and_assoc]

/-- The CPU's chain-start and chain-end messages on `WCH`. -/
theorem JetOK.cpu_wch (r : Nat) (v : List F) : rowSends (cpuAirJ hd0 stk0 ctr0) C "wch" v r =
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_G), 0] = v then
      C.env r (.main 0 (SEL + 11)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_G), C.env r (.main 0 J_N)] = v then
      -C.env r (.main 0 (SEL + 11)) else 0) := by
  rw [cpu_rowSends_jet (by decide)]
  simp only [jetInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col, B.c, sInst,
    true_and, ofN_zero]
  rw [if_neg (show ¬ ("roots" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

/-- **`WCH` is a flow** at an instantiation row's key, from `0` to its
    cell count. -/
theorem JetOK.wchConserve {r0 : Nat} (hr0 : r0 < C.h) (hi : C.main r0 (SEL + 11) = 1) :
    (wchEdges Iw (ofN r0) (C.main r0 CTR) (C.main r0 J_G)).Conserve (some ((0 : F), []))
      (some (C.main r0 J_N, [])) := by
  intro v
  obtain ⟨l, st⟩ := v
  have hCP : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  let E' := wchEdges Iw (ofN r0) (C.main r0 CTR) (C.main r0 J_G)
  match st with
  | x :: xs =>
    have z1 : E'.cntOut (l, x :: xs) = 0 := sumTo_zero (fun q => by
      rw [show decide (E'.outN q = (l, x :: xs)) = false from decide_eq_false (fun e => by
        have := congrArg Prod.snd e; cases this), Bool.and_false]; rfl) _
    have z2 : E'.cntIn (l, x :: xs) = 0 := sumTo_zero (fun q => by
      rw [show decide (E'.inN q = (l, x :: xs)) = false from decide_eq_false (fun e => by
        have := congrArg Prod.snd e; cases this), Bool.and_false]; rfl) _
    have o1 : Edges.oneIf (some ((0 : F), [])) (l, x :: xs) = 0 :=
      if_neg (fun e => by have := congrArg Prod.snd (Option.some.inj e); cases this)
    have o2 : Edges.oneIf (some (C.main r0 J_N, [])) (l, x :: xs) = 0 :=
      if_neg (fun e => by have := congrArg Prod.snd (Option.some.inj e); cases this)
    show E'.cntOut _ + _ = E'.cntIn _ + _
    rw [z1, z2, o1, o2]
  | [] =>
    have hb := h.bal "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l]
    simp only [jetTables, List.foldr_cons, List.foldr_nil] at hb
    rw [sends_nobus' (A := memAir) rfl, sends_nobus' (A := progAir heap) rfl, sends_nobus' (A := rootsAir roots) rfl,
      sends_nobus' (A := hdrAir jets) rfl, sends_nobus' (A := tmplAir jets) rfl, sends_nobus' (A := popAir) rfl,
      zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', add_zero'] at hb
    have hiw : tableSends instwAir Iw "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l] =
        ofN (E'.cntOut (l, [])) - ofN (E'.cntIn (l, [])) := by
      unfold tableSends
      rw [foldr_range_congr Iw.h (fun q hq => h.instw_rowSends hq _ _ _ _), fold_sub, fold_ofN, fold_ofN]
      rfl
    have hcpu : tableSends (cpuAirJ hd0 stk0 ctr0) C "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l] =
        ofN (Edges.oneIf (some ((0 : F), [])) (l, [])) - ofN (Edges.oneIf (some (C.main r0 J_N, [])) (l, [])) := by
      unfold tableSends
      rw [fold_single _ C.h r0 hr0 (fun r hr hne => by
        rw [h.cpu_wch, env_main0 hr, env_main0 hr, clk_eq h.cpu r hr]
        have hne' : ofN r ≠ ofN r0 := fun e => hne (ofN_inj (Nat.lt_trans hr hCP) (Nat.lt_trans hr0 hCP) e)
        rw [if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)),
          if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)), add_zero'])]
      rw [h.cpu_wch]
      simp only [env_main0 hr0, clk_eq h.cpu r0 hr0, hi]
      rw [msg_iteW, msg_iteW]
      unfold Edges.oneIf
      have ep : ∀ (o : Option Node), (if o = some (l, []) then (1 : F) else 0) =
          ofN (if o = some (l, []) then 1 else 0) := by
        intro o; split <;> rfl
      have en : ∀ (o : Option Node), (if o = some (l, []) then -(1 : F) else 0) =
          -ofN (if o = some (l, []) then 1 else 0) := by
        intro o; split
        · rfl
        · decide
      rw [ep, en, ← sub_eq_add_neg']
    rw [hcpu, hiw] at hb
    have e := bal_sub hb
    rw [← ofN_add, ← ofN_add] at e
    have b1 : E'.cntOut (l, []) ≤ Iw.h := sumTo_le_one (fun q => by split <;> decide) Iw.h
    have b2 : E'.cntIn (l, []) ≤ Iw.h := sumTo_le_one (fun q => by split <;> decide) Iw.h
    have o1 : Edges.oneIf (some ((0 : F), [])) (l, []) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have o2 : Edges.oneIf (some (C.main r0 J_N, [])) (l, []) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have hP : Iw.h + 1 < P := Nat.lt_of_le_of_lt (Nat.add_le_add_right h.instw_h 1) (by decide)
    have e' := ofN_inj (Nat.lt_of_le_of_lt (Nat.add_le_add o1 b1) (by rw [Nat.add_comm]; exact hP))
      (Nat.lt_of_le_of_lt (Nat.add_le_add o2 b2) (by rw [Nat.add_comm]; exact hP)) e
    show E'.cntOut (l, []) + _ = E'.cntIn (l, []) + _
    omega

/-- **An active POP row reads a stack cell below its counter.** -/
theorem JetOK.popRead {q : Nat} (hq : q < Po.h) (ha : Po.main q 7 = 1) :
    (Po.main q 3).val < (Po.main q 1).val ∧
    rd (memOf Mm) (Po.main q 1).val (Po.main q 3).val = some (.cons (Po.main q 4).val (Po.main q 5).val) := by
  have cv := col_eval hq
  obtain ⟨hlt, hget⟩ := h.cell (h.memHit ⟨(popAir, Po), by simp [jetTables], rfl, q, hq,
    ⟨"mem", 1, col 7, [col 3, c 5, col 4, col 5]⟩,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl,
    by simp only [List.map_cons, List.map_nil, cv, B.c]; rfl, by rw [cv, ha]⟩)
  rw [show E.eval (Po.env q) (E.const (ofN 5)) = ofN 5 from rfl, cellOf_cons] at hget
  -- the range check: `c = s + 1 + v`, with no wrap
  have hc := h.po.2 (.mul (col 7) (.sub (.sub (.sub (col 1) (col 3)) one) popVal))
    (List.mem_append_right _ List.mem_cons_self) q hq
  simp only [E.eval, cv, ha, one_mul', B.one, B.c, ofN_one] at hc
  have e := sub_eq_zero hc
  have hv := bitsVal_lt hq 8 24 (Nat.le_refl _) (fun i hi => col_bit h.po (i := 8 + i)
    (by simp only [popAir, popCons, List.mem_append]; exact .inl (.inr (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))
    hq)
  have hv' : (popVal.eval (Po.env q)).val < 2 ^ 24 := hv
  have hm := h.mem_h
  have hctr : Po.main q 1 = (Po.main q 3 + 1) + popVal.eval (Po.env q) := by rw [← e, add_sub_cancel3]
  have h1 : (Po.main q 3 + 1).val = (Po.main q 3).val + 1 :=
    val_add_of_lt (by have : 2 ^ 27 + 2 ^ 24 + 8 < P := P_big; show _ + 1 < P; omega)
  have hval : (Po.main q 1).val = (Po.main q 3).val + 1 + (popVal.eval (Po.env q)).val := by
    rw [hctr, val_add_of_lt (by rw [h1]; have : 2 ^ 27 + 2 ^ 24 + 8 < P := P_big; omega), h1]
  refine ⟨by omega, ?_⟩
  unfold rd
  rw [if_pos (by omega), hget]

/-- **An instantiation's pops are one path of POP rows**, and they are the
    only active POP rows at its counter. -/
theorem JetOK.popPath {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) {k : Nat} (hk : k < 2 ^ 24)
    (hK : C.main r J_K = ofN k) :
    ∃ (e : Nat → Nat) (sF : Nat → F), sF 0 = C.main r STK ∧ sF k = C.main r J_REST ∧
      (∀ i, i < k → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = ofN r ∧
        Po.main (e i) 1 = C.main r CTR ∧ Po.main (e i) 2 = ofN i ∧ Po.main (e i) 3 = sF i ∧
        Po.main (e i) 5 = sF (i + 1)) ∧
      ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q := by
  have hH : Po.h < P := Nat.lt_of_le_of_lt h.pop_h (by decide)
  have hkP : k < P := Nat.lt_trans hk (by decide)
  have hc : (popEdges Po (ofN r) (C.main r CTR)).Conserve (some ((0 : F), [C.main r STK]))
      (some (ofN k, [C.main r J_REST])) := by
    have := h.popConserve hr hi (C.main r CTR)
    unfold popStart popEnd at this
    rw [if_pos rfl, if_pos rfl, hK] at this
    exact this
  obtain ⟨e, st, h0, hkst, hp, hu⟩ := Edges.path _ hH hkP hc
  refine ⟨e, fun i => (st i).headD 0, by show (st 0).headD 0 = _; rw [h0]; rfl,
    by show (st k).headD 0 = _; rw [hkst]; rfl, fun i hi => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hp i hi
    have ha : (decide (Po.main (e i) 7 = 1) && decide (Po.main (e i) 0 = ofN r) &&
        decide (Po.main (e i) 1 = C.main r CTR)) = true := h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    refine ⟨h1, ha.1.1, ha.1.2, ha.2, h3, ?_, ?_⟩
    · show Po.main (e i) 3 = (st i).headD 0
      have : [Po.main (e i) 3] = st i := h4
      rw [← this]; rfl
    · show Po.main (e i) 5 = (st (i + 1)).headD 0
      have : [Po.main (e i) 5] = st (i + 1) := h5
      rw [← this]; rfl
  · intro q hq ha hclk
    have hact : ∀ c' : F, Po.main q 1 = c' → (popEdges Po (ofN r) c').act q = true := by
      intro c' hc'
      show (decide (Po.main q 7 = 1) && decide (Po.main q 0 = ofN r) && decide (Po.main q 1 = c')) = true
      rw [decide_eq_true ha, decide_eq_true hclk, decide_eq_true hc']; rfl
    rcases (inferInstance : Decidable (Po.main q 1 = C.main r CTR)) with hc0 | hc0
    · exfalso
      have hcn := h.popConserve hr hi (Po.main q 1)
      unfold popStart popEnd at hcn
      rw [if_neg hc0, if_neg hc0] at hcn
      have hz := Edges.noFlow _ hH hcn q hq
      rw [hact (Po.main q 1) rfl] at hz
      cases hz
    · exact hu q hq (hact _ hc0)

/-- **The pops, read**: along the path, `popR` pops the POP rows' arguments. -/
theorem JetOK.popR_path {r k : Nat} {e : Nat → Nat} {sF : Nat → F}
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = ofN r ∧
        Po.main (e i) 1 = C.main r CTR ∧ Po.main (e i) 2 = ofN i ∧ Po.main (e i) 3 = sF i ∧
        Po.main (e i) 5 = sF (i + 1)) :
    ∀ m, m ≤ k → popR (fun a => (memOf Mm)[a]?) (C.main r CTR).val m (sF (k - m)).val =
      some ((List.range m).map (fun i => (Po.main (e (k - m + i)) 4).val), (sF k).val)
  | 0, _ => by show some ([], (sF (k - 0)).val) = _; rw [Nat.sub_zero]; rfl
  | m + 1, hm => by
    have hj : k - (m + 1) < k := by omega
    obtain ⟨h1, h2, _, h4, _, h6, h7⟩ := hp _ hj
    obtain ⟨_, hrd⟩ := h.popRead h1 h2
    rw [h4, h6, h7, show k - (m + 1) + 1 = k - m by omega] at hrd
    show (match rdG (fun a => (memOf Mm)[a]?) (C.main r CTR).val (sF (k - (m + 1))).val with
      | some (.cons x r') => (popR (fun a => (memOf Mm)[a]?) (C.main r CTR).val m r').map fun (p : List Nat × Nat) => (x :: p.1, p.2)
      | _ => none) = _
    rw [← rd_G, hrd]
    dsimp only
    rw [JetOK.popR_path hp m (Nat.le_of_succ_le hm)]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    show (Po.main (e (k - m + i)) 4).val = (Po.main (e (k - (m + 1) + (i + 1))) 4).val
    rw [show k - (m + 1) + (i + 1) = k - m + i by omega]

/-- **An argument lookup at an instantiation's counter finds its pops.** -/
theorem JetOK.argPath {r k : Nat} {e : Nat → Nat}
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 2 = ofN i)
    (hu : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q) {v x : F}
    (hit : ∃ p ∈ jetTables hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw,
      (p.1.name == "cpu" || p.1.name == "instw") = true ∧
      ∃ r', r' < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "arg" ∧
        I.fields.map (fun e => e.eval (p.2.env r')) = [ofN r, v, x] ∧ I.count.eval (p.2.env r') = 1) :
    ∃ i, i < k ∧ v = ofN i ∧ x = Po.main (e i) 4 := by
  obtain ⟨q, hq, ha, hf⟩ := h.argHit hit
  simp only [List.cons.injEq, and_true] at hf
  obtain ⟨i, hi, hiq⟩ := hu q hq ha hf.1
  subst hiq
  exact ⟨i, hi, by rw [← hf.2.1, (hp i hi).2], hf.2.2.symm⟩

/-- **An instantiation's writes are one path of INSTW rows.** -/
theorem JetOK.wchPath {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) {n : Nat} (hn : n < 2 ^ 24)
    (hN : C.main r J_N = ofN n) :
    ∃ w : Nat → Nat, ∀ j, j < n → w j < Iw.h ∧ Iw.main (w j) 17 = 1 ∧ Iw.main (w j) 0 = ofN r ∧
      Iw.main (w j) 1 = C.main r CTR ∧ Iw.main (w j) 2 = C.main r J_G ∧ Iw.main (w j) 3 = ofN j := by
  have hH : Iw.h < P := Nat.lt_of_le_of_lt h.instw_h (by decide)
  have hnP : n < P := Nat.lt_trans hn (by decide)
  have hc := h.wchConserve hr hi
  rw [hN] at hc
  obtain ⟨w, _, _, _, hp, _⟩ := Edges.path _ hH hnP hc
  refine ⟨w, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3, _, _⟩ := hp j hj
  have ha : (decide (Iw.main (w j) 17 = 1) && decide (Iw.main (w j) 0 = ofN r) &&
      decide (Iw.main (w j) 1 = C.main r CTR) && decide (Iw.main (w j) 2 = C.main r J_G)) = true := h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ⟨h1, ha.1.1.1, ha.1.1.2, ha.1.2, ha.2, h3⟩

omit h in
theorem getD_range_map (f : Nat → Nat) {k i : Nat} (hi : i < k) : ((List.range k).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

/-- **An INSTW operand resolves** as `Op.res` does: a written cell at the
    counter plus its offset, a popped argument, or a public address. -/
theorem JetOK.resolve {r k : Nat} {e : Nat → Nat}
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 2 = ofN i)
    (hu : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q) (hk : k < 2 ^ 24)
    {q : Nat} (hq : q < Iw.h) (hclk : Iw.main q 0 = ofN r)
    {fl fa fg v xc out : Nat} (hcons : eq (col out) (resolveE fl fa fg v xc) ∈ instwCons)
    (hI : (⟨"arg", 1, col fa, [col 0, col v, col xc]⟩ : Inter) ∈ instwInters)
    {o : Op} (hops : [Iw.main q fl, Iw.main q fa, Iw.main q fg, Iw.main q v] = opCols o) (hs : opSmall o = true)
    (hc : (Iw.main q 1).val < 2 ^ 27) :
    (Iw.main q out).val = o.res (Iw.main q 1).val ((List.range k).map (fun i => (Po.main (e i) 4).val)) := by
  have cv := col_eval hq
  have hr := h.iw.2 _ hcons q hq
  simp only [B.eq, resolveE, E.eval, cv] at hr
  have e0 := sub_eq_zero hr
  have hP : 2 ^ 27 + 2 ^ 24 < P := by decide
  cases o with
  | local_ j =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, h4, ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', add_zero', add_zero'] at e0
    have hj : j < 2 ^ 24 := of_decide_eq_true hs
    rw [e0, val_add_nat (by omega)]; rfl
  | arg i =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, ofN_one, ofN_zero, zero_mul', one_mul', zero_mul', zero_add', add_zero'] at e0
    have hi : i < 2 ^ 24 := of_decide_eq_true hs
    obtain ⟨i', hi', hv, hx⟩ := h.argPath (fun i hi => hp i hi) hu (v := Iw.main q v) (x := Iw.main q xc)
      ⟨(instwAir, Iw), by simp [jetTables], rfl, q, hq, _, hI, rfl,
        by simp only [List.map_cons, List.map_nil, cv, hclk], by rw [cv, h2]; rfl⟩
    rw [h4] at hv
    have := ofN_inj (Nat.lt_trans hi (by decide)) (Nat.lt_trans (Nat.lt_trans hi' hk) (by decide)) hv
    subst this
    rw [e0, hx]
    show _ = ((List.range k).map (fun i => (Po.main (e i) 4).val)).getD i 0
    rw [getD_range_map _ hi']
  | glob a =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, h4, ofN_one, ofN_zero, zero_mul', zero_mul', one_mul', zero_add', zero_add'] at e0
    have ha : a < 2 ^ 24 := of_decide_eq_true hs
    rw [e0, val_ofN (Nat.lt_trans ha (by decide))]; rfl

/-- **The instantiation's root resolves** as `Op.res` does. -/
theorem JetOK.rootRes {r k : Nat} {e : Nat → Nat} (hr : r < C.h)
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 2 = ofN i)
    (hu : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q) (hk : k < 2 ^ 24)
    {o : Op} (hops : [C.main r J_RL, C.main r J_RA, C.main r J_RG, C.main r J_RV] = opCols o)
    (hs : opSmall o = true) (hc : ∀ j, o = .local_ j → (C.main r CTR).val < 2 ^ 27) :
    (jetHd.eval (C.env r)).val = o.res (C.main r CTR).val ((List.range k).map (fun i => (Po.main (e i) 4).val)) := by
  have cv := col_eval hr
  simp only [jetHd, E.eval, cv]
  have hP : 2 ^ 27 + 2 ^ 24 < P := by decide
  cases o with
  | local_ j =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, h4, ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', add_zero', add_zero']
    have hj : j < 2 ^ 24 := of_decide_eq_true hs
    have hc' := hc j rfl
    rw [val_add_nat (by omega)]; rfl
  | arg i =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, ofN_one, ofN_zero, zero_mul', zero_mul', one_mul', zero_add', zero_add']
    have hi : i < 2 ^ 24 := of_decide_eq_true hs
    obtain ⟨i', hi', hv, hx⟩ := h.argPath (fun i hi => hp i hi) hu (v := C.main r J_RV) (x := C.main r J_XROOT)
      ⟨(cpuAirJ hd0 stk0 ctr0, C), by simp [jetTables], rfl, r, hr,
        ⟨"arg", 1, col J_RA, [col J_CLK, col J_RV, col J_XROOT]⟩,
        List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))), rfl,
        by simp only [List.map_cons, List.map_nil, cv, clk_eq h.cpu r hr], by rw [cv, h2]; rfl⟩
    rw [h4] at hv
    have := ofN_inj (Nat.lt_trans hi (by decide)) (Nat.lt_trans (Nat.lt_trans hi' hk) (by decide)) hv
    subst this
    rw [hx]
    show _ = ((List.range k).map (fun i => (Po.main (e i) 4).val)).getD i 0
    rw [getD_range_map _ hi']
  | glob a =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, h4, ofN_one, ofN_zero, zero_mul', zero_mul', one_mul', zero_add', add_zero']
    have ha : a < 2 ^ 24 := of_decide_eq_true hs
    rw [val_ofN (Nat.lt_trans ha (by decide))]; rfl

omit h in
theorem getD_range_mapF (f : Nat → F) {k i : Nat} (hi : i < k) : ((List.range k).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

/-- **The instantiation's cells are in memory**: at the counter plus `j`,
    the template's `j`-th cell, resolved. -/
theorem JetOK.cellAt {r k g : Nat} {J : Air.Jet} {e w : Nat → Nat} (hjl : jets.length ≤ 2 ^ 27)
    (hJ : jets[g]? = some J) (hG : C.main r J_G = ofN g)
    (hn : (symCells J J.body 0).1.length < 2 ^ 24)
    (hops : ((symCells J J.body 0).1.all fun cl => match cl.2 with
      | some (a, b) => opSmall a && opSmall b
      | none => true) = true)
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 2 = ofN i)
    (hu : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q) (hk : k < 2 ^ 24)
    (hw : ∀ j, j < (symCells J J.body 0).1.length → w j < Iw.h ∧ Iw.main (w j) 17 = 1 ∧
      Iw.main (w j) 0 = ofN r ∧ Iw.main (w j) 1 = C.main r CTR ∧ Iw.main (w j) 2 = C.main r J_G ∧
      Iw.main (w j) 3 = ofN j)
    (hc : (C.main r CTR).val < 2 ^ 27) {j : Nat} (hj : j < (symCells J J.body 0).1.length) :
    (memOf Mm)[(C.main r CTR).val + j]? =
      some (JetTable.cellOf (C.main r CTR).val ((List.range k).map (fun i => (Po.main (e i) 4).val))
        (symCells J J.body 0).1[j]) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw j hj
  have cv := col_eval h1
  have hP : 2 ^ 27 + 2 ^ 24 < P := by decide
  -- the template row
  obtain ⟨J', g', j', cl, hJ', hcl, hrow⟩ := h.tmplHit h1 h2
  have hx : ∀ i, i < 11 → Iw.main (w j) (2 + i) = (tmplRow g' j' cl).getD i 0 := fun i hi => by
    rw [← hrow, getD_range_mapF _ hi]
  have hg' : g' < jets.length := (List.getElem?_eq_some_iff.1 hJ').1
  have hg : g < jets.length := (List.getElem?_eq_some_iff.1 hJ).1
  obtain ⟨tag, ops⟩ := cl
  have t0 : (tmplRow g' j' (tag, ops)).getD 0 0 = ofN g' := by cases ops <;> rfl
  have t1 : (tmplRow g' j' (tag, ops)).getD 1 0 = ofN j' := by cases ops <;> rfl
  have t2 : (tmplRow g' j' (tag, ops)).getD 2 0 = ofN tag := by cases ops <;> rfl
  have e0 := hx 0 (by decide); rw [t0, h5, hG] at e0
  have egg := ofN_inj (Nat.lt_of_lt_of_le hg (Nat.le_trans hjl (by decide))) (Nat.lt_of_lt_of_le hg' (Nat.le_trans hjl (by decide))) e0
  subst egg
  rw [hJ] at hJ'
  cases hJ'
  have hj' : j' < (symCells J J.body 0).1.length := (List.getElem?_eq_some_iff.1 hcl).1
  have e1 := hx 1 (by decide); rw [t1, h6] at e1
  have ejj := ofN_inj (Nat.lt_trans (Nat.lt_trans hj hn) (by decide)) (Nat.lt_trans (Nat.lt_trans hj' hn) (by decide)) e1
  subst ejj
  have hclj : (symCells J J.body 0).1[j] = (tag, ops) := (List.getElem?_eq_some_iff.1 hcl).2
  rw [hclj]
  have e2 := hx 2 (by decide); rw [t2] at e2
  -- the write
  obtain ⟨_, hget⟩ := h.cell (h.memHit
    (v := [Iw.main (w j) 1 + Iw.main (w j) 3, Iw.main (w j) 4, Iw.main (w j) 13, Iw.main (w j) 14])
    ⟨(instwAir, Iw), by simp [jetTables], rfl, w j, h1,
    ⟨"mem", 1, col 17, [.add (col 1) (col 3), col 4, col 13, col 14]⟩,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))), rfl,
    by simp only [List.map_cons, List.map_nil, E.eval, cv], by rw [cv, h2]⟩)
  rw [h4, h6, val_add_nat (by omega), e2] at hget
  rw [hget]
  congr 1
  have hmem : ((tag, ops) : Nat × Option (Op × Op)) ∈ (symCells J J.body 0).1 := by
    rw [← hclj]; exact List.getElem_mem hj
  rcases symCells_cells J J.body 0 _ hmem with ⟨hno, htag⟩ | ⟨htag, oa, ob, hso⟩
  · -- a leaf: its operand columns are zero
    simp only at hno htag
    subst hno
    have z : ∀ i, 3 ≤ i → i < 11 → Iw.main (w j) (2 + i) = 0 := by
      intro i h3 h11
      rw [hx i h11]
      show ([ofN g, ofN j, ofN tag] ++ List.replicate 8 (ofN 0)).getD i 0 = 0
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
      simp only [List.length_cons, List.length_nil]
      rw [if_pos (by omega)]; rfl
    have ra := h.iw.2 _ (show eq (col 13) (resolveE 5 6 7 8 15) ∈ instwCons by simp [instwCons]) (w j) h1
    have rb := h.iw.2 _ (show eq (col 14) (resolveE 9 10 11 12 16) ∈ instwCons by simp [instwCons]) (w j) h1
    simp only [B.eq, resolveE, E.eval, cv, z 3 (by decide) (by decide), z 4 (by decide) (by decide),
      z 5 (by decide) (by decide), z 7 (by decide) (by decide), z 8 (by decide) (by decide),
      z 9 (by decide) (by decide), zero_mul', add_zero'] at ra rb
    rw [sub_eq_zero ra, sub_eq_zero rb]
    rcases (show tag = 0 ∨ tag = 1 ∨ tag = 2 by omega) with rfl | rfl | rfl <;> rfl
  · -- an application: its operands resolve
    simp only at htag hso
    subst htag hso
    have hs := List.all_eq_true.1 hops _ hmem
    simp only [Bool.and_eq_true] at hs
    have hA : [Iw.main (w j) 5, Iw.main (w j) 6, Iw.main (w j) 7, Iw.main (w j) 8] = opCols oa := by
      rw [hx 3 (by decide), hx 4 (by decide), hx 5 (by decide), hx 6 (by decide)]
      show [([ofN g, ofN j, ofN 3] ++ opCols oa ++ opCols ob).getD 3 0, _, _, _] = _
      cases oa <;> cases ob <;> rfl
    have hB : [Iw.main (w j) 9, Iw.main (w j) 10, Iw.main (w j) 11, Iw.main (w j) 12] = opCols ob := by
      rw [hx 7 (by decide), hx 8 (by decide), hx 9 (by decide), hx 10 (by decide)]
      show [([ofN g, ofN j, ofN 3] ++ opCols oa ++ opCols ob).getD 7 0, _, _, _] = _
      cases oa <;> cases ob <;> rfl
    have ea := h.resolve hp hu hk h1 h3 (show eq (col 13) (resolveE 5 6 7 8 15) ∈ instwCons by simp [instwCons])
      List.mem_cons_self hA hs.1 (by rw [h4]; exact hc)
    have eb := h.resolve hp hu hk h1 h3 (show eq (col 14) (resolveE 9 10 11 12 16) ∈ instwCons by simp [instwCons])
      (List.mem_cons_of_mem _ List.mem_cons_self) hB hs.2 (by rw [h4]; exact hc)
    rw [h4] at ea eb
    show Circuit.cellOf (ofN 3) _ _ = _
    rw [cellOf_app, ea, eb]
    rfl

omit h in
theorem padCopies_length_ge : ∀ rows : List (List F), rows.length ≤ (padCopies rows).length
  | [] => Nat.le_refl 0
  | r :: rs => by show _ ≤ ((r :: rs) ++ _).length; rw [List.length_append]; exact Nat.le_add_right _ _

omit h in
theorem programRows_length_ge (heap : List Cell) : heap.length ≤ (programRows heap).length := by
  unfold programRows
  rw [List.length_append, List.length_map, List.length_zipIdx]
  exact Nat.le_add_right _ _

theorem JetOK.prog_h : Pg.h ≤ 2 ^ 27 := h.two (progAir heap, Pg) (by simp [jetTables])

theorem JetOK.jets_le : jets.length ≤ 2 ^ 27 := by
  have e : Hd.h = (hdrRows jets).length := h.hdpre.1
  have hl : jets.length ≤ (hdrRows jets).length := by
    have := padCopies_length_ge (jets.zipIdx.map fun (J, g) => hdrRow J g)
    rw [List.length_map, List.length_zipIdx] at this
    exact this
  have := h.hdr_h
  omega

theorem JetOK.heap_le : heap.length ≤ 2 ^ 27 := by
  have e : Pg.h = (programRows heap).length := h.pgpre.1
  have := programRows_length_ge heap
  have := h.prog_h
  omega

/-- **An instantiation row is `Air.instRow`** for the jet at a listed root,
    given licensed roots and a jet table whose numbers fit. -/
theorem JetOK.inst {r : Nat} (hr1 : r + 1 < C.h) (hi : C.main r (SEL + 11) = 1)
    (hroots : RootsOK heap roots jets) (hfit : jets.all jetFitB = true) :
    ∃ g J, ((rowOf C r).hd, g) ∈ roots ∧ jets[g]? = some J ∧
      instRow (memOf Mm) J (rowOf C r) = some (rowOf C (r + 1)) := by
  have hr : r < C.h := Nat.lt_of_succ_lt hr1
  have hP : 2 ^ 27 + 2 ^ 24 < P := by decide
  -- the kind
  have hsel : SelsAre C r 11 := by
    obtain ⟨k, _, hs⟩ := kind_ofJ h.cpu hr
    have e := hs 11 (by decide); rw [hi] at e
    rcases Nat.decEq 11 k with hk | hk
    · rw [if_neg hk] at e; exact absurd e (by decide)
    · rw [← hk] at hs; exact hs
  obtain ⟨_, _, _, _, hnHd, hnStk, hnCtr⟩ := inst_facts hr hsel
  obtain ⟨m1, m2, m3⟩ := next_regsJ h.cpu hr hr1
  -- the root and the header
  obtain ⟨a, g1, hmem, hHD, hG1⟩ := h.rootsHit hr hi
  obtain ⟨J, g, hJ, hhdr⟩ := h.hdrHit hr hi
  obtain ⟨J1, hJ1, _, htm, _⟩ := hroots a g1 hmem
  have hjl := h.jets_le
  have hg1 : g1 < jets.length := (List.getElem?_eq_some_iff.1 hJ1).1
  have hg : g < jets.length := (List.getElem?_eq_some_iff.1 hJ).1
  simp only [hdrRow, List.cons_append, List.nil_append, List.cons.injEq] at hhdr
  obtain ⟨hG, hK, hN, hops⟩ := hhdr
  have e1 : g1 = g := ofN_inj (Nat.lt_of_lt_of_le hg1 (Nat.le_trans hjl (by decide)))
    (Nat.lt_of_lt_of_le hg (Nat.le_trans hjl (by decide))) (hG1.symm.trans hG)
  subst e1
  rw [hJ] at hJ1
  cases hJ1
  -- the jet's numbers fit
  have hfJ := List.all_eq_true.1 hfit J (List.mem_of_getElem? hJ)
  unfold jetFitB at hfJ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfJ
  obtain ⟨⟨⟨hkf, hnf⟩, hrf⟩, hcf⟩ := hfJ
  -- the head is the root's address
  have hhp := h.heap_le
  have ha : a < heap.length := termAt_lt htm
  have hhd : (rowOf C r).hd = a := by
    show (C.main r HD).val = a; rw [hHD, val_ofN (by omega)]
  refine ⟨g1, J, by rw [hhd]; exact hmem, hJ, ?_⟩
  -- the pops
  obtain ⟨e, sF, hs0, hsk, hp, hu⟩ := h.popPath hr hi hkf hK
  have hp' : ∀ i, i < J.xs.length → e i < Po.h ∧ Po.main (e i) 2 = ofN i :=
    fun i hi => ⟨(hp i hi).1, (hp i hi).2.2.2.2.1⟩
  have hpop := h.popR_path hp J.xs.length (Nat.le_refl _)
  rw [Nat.sub_self, hs0, hsk] at hpop
  simp only [Nat.zero_add] at hpop
  -- the writes
  obtain ⟨w, hw⟩ := h.wchPath hr hi hnf hN
  -- with a cell to write, the counter is an address
  have hc : 0 < (symCells J J.body 0).1.length → (C.main r CTR).val < 2 ^ 27 := by
    intro hn0
    obtain ⟨h1, h2, _, h4, _, h6⟩ := hw 0 hn0
    have cv := col_eval h1
    obtain ⟨hlt, _⟩ := h.cell (h.memHit
      (v := [Iw.main (w 0) 1 + Iw.main (w 0) 3, Iw.main (w 0) 4, Iw.main (w 0) 13, Iw.main (w 0) 14])
      ⟨(instwAir, Iw), by simp [jetTables], rfl, w 0, h1,
        ⟨"mem", 1, col 17, [.add (col 1) (col 3), col 4, col 13, col 14]⟩,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)))), rfl,
        by simp only [List.map_cons, List.map_nil, E.eval, cv], by rw [cv, h2]⟩)
    rw [h4, h6, ofN_zero, add_zero'] at hlt
    exact Nat.lt_of_lt_of_le hlt h.mem_h
  -- the instantiation
  unfold instRow instRowG
  show (match popR (fun a => (memOf Mm)[a]?) (C.main r CTR).val J.xs.length (C.main r STK).val with
    | some (ps, rest) =>
      let (cs, root) := icells (Mach.overrideN J.genv J.xs ps) (C.main r CTR).val J.body
      if wrsG (fun a => (memOf Mm)[a]?) (C.main r CTR).val cs then
        some (⟨root, rest, (C.main r CTR).val + cs.length⟩ : Air.Row) else none
    | none => none) = _
  rw [hpop]
  dsimp only
  have hic := symCells_icells J (C.main r CTR).val ((List.range J.xs.length).map (fun i => (Po.main (e i) 4).val))
    (by rw [List.length_map, List.length_range]) J.body 0
  rw [Nat.add_zero] at hic
  rw [← hic]
  dsimp only
  rw [if_pos (wrsG_of _ _ (fun j hj => by
    rw [List.length_map] at hj
    rw [List.getElem_map]
    exact h.cellAt hjl hJ hG hnf hcf hp' hu hkf hw (hc (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)) hj))]
  -- the next row
  show some _ = some (⟨(C.main (r + 1) HD).val, (C.main (r + 1) STK).val, (C.main (r + 1) CTR).val⟩ : Air.Row)
  rw [m1, m2, m3, hnHd, hnStk, hnCtr, hi, zero_add', zero_add', one_mul', one_mul', hN]
  congr 2
  · rw [h.rootRes hr hp' hu hkf hops hrf (fun j hj => hc (by
      have := symCells_root_local J J.body 0 j hj
      omega))]
  · rw [List.length_map]
    rcases Nat.eq_zero_or_pos (symCells J J.body 0).1.length with hz | hz
    · rw [hz, ofN_zero, add_zero', Nat.add_zero]
    · rw [val_add_nat (by have := hc hz; omega)]

theorem JetOK.first_regsJ (h0 : 0 < C.h) :
    C.main 0 HD = ofN hd0 ∧ C.main 0 STK = ofN stk0 ∧ C.main 0 CTR = ofN ctr0 := by
  have hf : C.env 0 .first = 1 := rfl
  have h1 := memJ_tail h.cpu h0 (x := whenFirst (eq (col HD) (c hd0))) (by simp)
  have h2 := memJ_tail h.cpu h0 (x := whenFirst (eq (col STK) (c stk0))) (by simp)
  have h3 := memJ_tail h.cpu h0 (x := whenFirst (eq (col CTR) (c ctr0))) (by simp)
  simp only [B.whenFirst, B.eq, B.col, B.c, E.eval, hf, one_mul', env_main0 h0] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

/-- **The table is a run of the AIR with instantiation rows** from the
    machine its first row and the memory's prefix name. -/
theorem JetOK.acceptsJ (hroots : RootsOK heap roots jets) (hfit : jets.all jetFitB = true) {m0 : Mach}
    (hheap : (memOf Mm).take ctr0 = m0.heap) (hhd : m0.hd = hd0) (hstk : m0.stk = stk0)
    (hctr : m0.heap.length = ctr0) (hP : hd0 < P ∧ stk0 < P ∧ ctr0 < P) :
    AcceptsJ (memOf Mm) m0 roots jets C.h (rowOf C) := by
  have h0 : 0 < C.h := h.cpu.1
  obtain ⟨e1, e2, e3⟩ := h.first_regsJ h0
  have ctr0' : (rowOf C 0).ctr = ctr0 := by show (C.main 0 CTR).val = _; rw [e3, val_ofN hP.2.2]
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ctr0']; exact hheap
  · show (C.main 0 HD).val = _; rw [e1, val_ofN hP.1, hhd]
  · show (C.main 0 STK).val = _; rw [e2, val_ofN hP.2.1, hstk]
  · rw [ctr0', hctr]
  · intro i hi
    have hi' : i < C.h := Nat.lt_of_succ_lt hi
    obtain ⟨k, hk, hsel⟩ := kind_ofJ h.cpu hi'
    rcases Nat.lt_or_ge k 11 with hk11 | hk11
    · have h11 : C.main i (SEL + 11) = 0 := by rw [hsel 11 (by decide), if_neg (Nat.ne_of_gt hk11)]
      have hs := rowSat_ofJ h.cpu hi' h11
      have hK : IsKind C i k := ⟨hk11, hsel⟩
      obtain ⟨_, _, _, _, n1, n2, n3⟩ := kind_facts hi' hK
      obtain ⟨m1, m2, m3⟩ := next_regs hs hi' hi
      have hnext : rowOf C (i + 1) = ⟨((nextHdOf k).eval (C.env i)).val,
          ((nextStkOf k).eval (C.env i)).val, ((nextCtrOf k).eval (C.env i)).val⟩ := by
        simp only [rowOf, m1, m2, m3, n1, n2, n3]
      rcases Nat.lt_or_ge k 4 with hk4 | hk4
      · exact .inl (by rw [hnext]; exact h.row.step hi' hK hk4)
      · refine .inr (.inr ⟨h.row.halt hi' hK hk4, ?_⟩)
        rw [hnext, nextHdOf_halt hk4, nextStkOf_halt hk4, nextCtrOf_halt hk4]
        simp only [rowOf, col_eval hi']
    · have hk' : k = 11 := Nat.le_antisymm (Nat.le_of_lt_succ hk) hk11
      subst hk'
      have h11 : C.main i (SEL + 11) = 1 := by rw [hsel 11 (by decide), if_pos rfl]
      exact .inr (.inl (h.inst hi h11 hroots hfit))
  · have hl : C.h - 1 < C.h := Nat.sub_lt h0 (by decide)
    have hla : C.env (C.h - 1) .last = 1 := by
      show (if C.h - 1 + 1 = C.h then 1 else 0) = 1; rw [if_pos (Nat.sub_add_cancel h0)]
    have hh := memJ_tail h.cpu hl (x := whenLast (eq halt one)) (by simp)
    simp only [B.whenLast, B.eq, E.eval, hla, one_mul', B.one, B.c, ofN_one] at hh
    have hh1 := sub_eq_zero hh
    obtain ⟨k, hk, hsel⟩ := kind_ofJ h.cpu hl
    rcases Nat.lt_or_ge k 11 with hk11 | hk11
    · have hK : IsKind C (C.h - 1) k := ⟨hk11, hsel⟩
      obtain ⟨_, hhalt, _⟩ := kind_facts hl hK
      rcases Nat.lt_or_ge k 4 with hk4 | hk4
      · rw [hhalt, if_neg (Nat.not_le_of_lt hk4)] at hh1
        exact absurd hh1 (by decide)
      · exact h.row.halt hl hK hk4
    · have hk' : k = 11 := Nat.le_antisymm (Nat.le_of_lt_succ hk) hk11
      subst hk'
      obtain ⟨_, hhalt, _⟩ := inst_facts hl hsel
      rw [hhalt] at hh1
      exact absurd hh1 (by decide)

end

section

open Mach Term

variable {t : Term} {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Pg Rt Hd Tm Po Iw : Table}
  (h : JetOK (load t).hd (load t).stk (load t).heap.length (load t).heap roots jets C Mm Pg Rt Hd Tm Po Iw)
include h

/-- The program table puts the loaded heap in the memory. -/
theorem JetOK.heap0 : (memOf Mm).take (load t).heap.length = (load t).heap := by
  obtain ⟨hfit, _, _⟩ := load_fits t
  have hP : (load t).heap.length < P := Nat.lt_of_le_of_lt h.heap_le (by decide)
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  split
  · next hi =>
    have hPg : i < Pg.h := by
      have e : Pg.h = (programRows (load t).heap).length := h.pgpre.1
      have := programRows_length (load t).heap
      omega
    have hc := hfit _ (List.getElem_mem hi)
    have hpre : ∀ j, j < 5 → (prec j).eval (Pg.env i) = ((programRows (load t).heap).getD i []).getD j 0 :=
      fun j hj => prec_eval h.pgpre hPg hj
    have hm := h.cell (h.memHit (v := [ofN i, ofN (cellTag (load t).heap[i]),
      ofN (cellFields (load t).heap[i]).1, ofN (cellFields (load t).heap[i]).2])
      ⟨(progAir (load t).heap, Pg), by simp [jetTables], rfl, i, hPg,
        ⟨"mem", 1, prec 4, [prec 0, prec 1, prec 2, prec 3]⟩, List.mem_cons_self, rfl,
        by simp only [List.map_cons, List.map_nil, hpre 0 (by decide), hpre 1 (by decide), hpre 2 (by decide),
          hpre 3 (by decide), programRows_get hi]; rfl,
        by rw [hpre 4 (by decide), programRows_get hi]; rfl⟩)
    rw [val_ofN (Nat.lt_trans hi hP), cellOf_enc _ (Nat.lt_trans hc.1 hP) (Nat.lt_trans hc.2 hP)] at hm
    rw [hm.2, List.getElem?_eq_getElem hi]
  · next hi => rw [List.getElem?_eq_none (Nat.le_of_not_lt hi)]

/-- **Soundness of the jet circuit, from its tables**: they are a run of
    the AIR with instantiation rows from the loaded term. -/
theorem JetOK.sound (hroots : RootsOK (load t).heap roots jets) (hfit : jets.all jetFitB = true) :
    AcceptsJ (memOf Mm) (load t) roots jets C.h (rowOf C) := by
  obtain ⟨_, hhd, hstk⟩ := load_fits t
  have hP : (load t).heap.length < P := Nat.lt_of_le_of_lt h.heap_le (by decide)
  exact h.acceptsJ hroots hfit h.heap0 rfl rfl rfl ⟨Nat.lt_trans hhd hP, Nat.lt_trans hstk hP, hP⟩

end

open Mach Term

/-- The jet circuit is guarded, for every term and jet table. -/
theorem jet_guarded (t : Term) (roots : List (Nat × Nat)) (jets : List Air.Jet) :
    ∀ A ∈ jetAirs t roots jets, A.cons.all E.guarded = true := by
  intro A hA
  simp only [jetAirs, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Acceptance of the jet circuit's data is `JetOK`. -/
theorem jetOK_of {t : Term} {roots : List (Nat × Nat)} {jets : List Air.Jet} {ts : List Table}
    (h : Accepted (jetAirs t roots jets) ts) :
    ∃ C Mm Pg Rt Hd Tm Po Iw, ts = [C, Mm, Pg, Rt, Hd, Tm, Po, Iw] ∧
      JetOK (load t).hd (load t).stk (load t).heap.length (load t).heap roots jets C Mm Pg Rt Hd Tm Po Iw := by
  obtain ⟨hl, hsat, hbal, hht, htwo⟩ := h
  match ts, hl with
  | [C, Mm, Pg, Rt, Hd, Tm, Po, Iw], _ =>
    have mem : ∀ A T, (A, T) ∈ jetTables (load t).hd (load t).stk (load t).heap.length (load t).heap roots jets
        C Mm Pg Rt Hd Tm Po Iw → Sat A T ∧ (A.pre = 0 ∨ PreIs A T) := fun A T hm => hsat (A, T) hm
    have pre : ∀ A T, (A, T) ∈ jetTables (load t).hd (load t).stk (load t).heap.length (load t).heap roots jets
        C Mm Pg Rt Hd Tm Po Iw → A.pre ≠ 0 → PreIs A T := by
      intro A T hm hp
      rcases (mem A T hm).2 with h0 | h0
      · exact absurd h0 hp
      · exact h0
    exact ⟨C, Mm, Pg, Rt, Hd, Tm, Po, Iw, rfl, ⟨(mem _ _ (by simp [jetTables])).1, (mem _ _ (by simp [jetTables])).1,
      (mem _ _ (by simp [jetTables])).1, (mem _ _ (by simp [jetTables])).1,
      pre _ _ (by simp [jetTables]) (by show (5 : Nat) ≠ 0; decide),
      pre _ _ (by simp [jetTables]) (by show (2 : Nat) ≠ 0; decide),
      pre _ _ (by simp [jetTables]) (by show (7 : Nat) ≠ 0; decide),
      pre _ _ (by simp [jetTables]) (by show (11 : Nat) ≠ 0; decide), hbal, hht, htwo⟩⟩

/-- **Soundness of the jet circuit.**  If Plonky3 accepts a proof against
    AIRs the same as the jet circuit for `t` and a jet table whose roots
    are licensed (`rootsOKB`, which the verifier's `jets statement` checks)
    and whose numbers fit (`jetFitB`, which `compare-jets` checks), then the
    tables are a run of the AIR with instantiation rows, and they end on a
    value `v` such that `t` evaluates in normal order to a value that
    weakly reduces to `v`, with `v`'s head combinator and arity. -/
theorem jetExport_sound {t : Term} {roots : List (Nat × Nat)} {jets : List Air.Jet}
    (hroots : rootsOKB (load t).heap roots jets = true) (hfit : jets.all jetFitB = true)
    {Rs : List AirD} {ts : List Table} (hs : sameAirsB Rs (jetAirs t roots jets) = true) (h : AcceptedP Rs ts) :
    ∃ C Mm Pg Rt Hd Tm Po Iw, ts = [C, Mm, Pg, Rt, Hd, Tm, Po, Iw] ∧
      AcceptsJ (memOf Mm) (load t) roots jets C.h (rowOf C) ∧
      ∃ v, decode (st (memOf Mm) (rowOf C (C.h - 1))) = some v ∧ Whnf v ∧
        (∃ v', Eval t v' ∧ WSteps v' v) ∧ (∃ v', Eval t v' ∧ chead v' = chead v) := by
  have hacc := accepted_transfer hs ((acceptedP_iff_of (jet_guarded t roots jets) hs ts).1 h)
  obtain ⟨C, Mm, Pg, Rt, Hd, Tm, Po, Iw, rfl, hok⟩ := jetOK_of hacc
  have hR := rootsOKB_sound hroots
  have hA := hok.sound hR hfit
  exact ⟨C, Mm, Pg, Rt, Hd, Tm, Po, Iw, rfl, hA, air_sound_jet hA hR⟩

end Circuit
