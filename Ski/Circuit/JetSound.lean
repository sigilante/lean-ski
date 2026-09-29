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
  ⟨h.cpu.1, fun _ hr h11 => rowSat_ofJ h.cpu hr h11, mem_addr h.mem, h.mem_h, fun r hr I hI hbus hc =>
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

end Circuit
