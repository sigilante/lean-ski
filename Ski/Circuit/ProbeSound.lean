import Ski.Circuit.ProbeKind
import Ski.Circuit.JetCore

/-!
# Soundness of the probe circuit

Tables accepted for the probe circuit of a term, its jet table and the
plan of an outcome are a run of `Air.AcceptsP` (`probeExport_sound`), so
the term decodes to the outcome (`Air.air_probe_decodes`).

- The rows that are not probe rows are the jet circuit's: a corpus row
  steps or halts (`RowOK`), and an instantiation is `Air.instRow`
  (`JetCore.inst`, from `ProbeOK.core`).
- The probe count starts at 0, grows by one on each probe row, is `n` on
  the last row, and a probe row looks up the plan's row at its count: so
  there are exactly `n` probe rows, the `j`-th at `p j`.
- A probe row writes the next segment's markers and their stack (the PW
  chain) and moves to the probed pointer: the loaded term's root for the
  first, else its parent's field, which `SEGEND` and `ARG` find among the
  parent's end row's pops.
- A later probe row, and the last row, end a segment: the atom at the head
  is its marker, its fields are popped (the POP chain), and a nil lies
  below them.
-/

namespace Circuit

open B Air JetTable Mach

def probeTables (hd0 stk0 ctr0 n la : Nat) (heap : List Cell) (roots : List (Nat × Nat)) (jets : List Air.Jet)
    (plan : List Air.Seg) (C Mm Pg Rt Hd Tm Po Iw Pl Pw : Table) : List (AirD × Table) :=
  [(cpuAirP hd0 stk0 ctr0 n la, C), (memAir, Mm), (progAir heap, Pg), (rootsAir roots, Rt), (hdrAir jets, Hd),
   (tmplAir jets, Tm), (popAir, Po), (instwAir, Iw), (planAir plan, Pl), (pwAir, Pw)]

/-- **What an accepted proof of the probe circuit gives.** -/
structure ProbeOK (hd0 stk0 ctr0 n la : Nat) (heap : List Cell) (roots : List (Nat × Nat)) (jets : List Air.Jet)
    (plan : List Air.Seg) (C Mm Pg Rt Hd Tm Po Iw Pl Pw : Table) : Prop where
  cpu : Sat (cpuAirP hd0 stk0 ctr0 n la) C
  mem : Sat memAir Mm
  po : Sat popAir Po
  iw : Sat instwAir Iw
  pw : Sat pwAir Pw
  pgpre : PreIs (progAir heap) Pg
  rtpre : PreIs (rootsAir roots) Rt
  hdpre : PreIs (hdrAir jets) Hd
  tmpre : PreIs (tmplAir jets) Tm
  plpre : PreIs (planAir plan) Pl
  bal : Balanced (probeTables hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw)
  hts : HeightsOK (probeTables hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw)
  two : TwoAdic (probeTables hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw)

theorem planRows_len (plan : List Air.Seg) : ∀ x ∈ planRows plan, x.length = 7 :=
  padCopies_len (fun x hx => by obtain ⟨_, _, e⟩ := List.mem_map.1 hx; rw [← e]; rfl)

theorem planRows_mem {plan : List Air.Seg} {v : List F} (h : v ∈ planRows plan) :
    ∃ j s, plan[j]? = some s ∧
      v = [ofN j, ofN s.base, ofN s.k, ofN s.ctor, ofN s.arity, ofN s.parent, ofN s.field] := by
  obtain ⟨⟨s, j⟩, hm, e⟩ := List.mem_map.1 (padCopies_mem h)
  obtain ⟨_, hj, hs⟩ := List.mem_zipIdx hm
  simp only [Nat.zero_add, Nat.sub_zero] at hj hs
  exact ⟨j, s, by rw [List.getElem?_eq_getElem hj, hs], e.symm⟩

/-- The probe CPU's messages weigh `1`, but the `SEGEND` provider's. -/
theorem cpuP_weights : ∀ I ∈ cpuInters ++ jetInters ++ probeInters, I.bus ≠ "segend" → 1 ≤ I.weight := by
  have : (cpuInters ++ jetInters ++ probeInters).all (fun I => I.bus == "segend" || decide (1 ≤ I.weight)) = true := by
    decide
  intro I hI hb
  have := List.all_eq_true.1 this I hI
  rw [Bool.or_eq_true] at this
  rcases this with h | h
  · exact absurd (beq_iff_eq.1 h) hb
  · exact of_decide_eq_true h

section

variable {hd0 stk0 ctr0 n la : Nat} {heap : List Cell} {roots : List (Nat × Nat)} {jets : List Air.Jet}
  {plan : List Air.Seg} {C Mm Pg Rt Hd Tm Po Iw Pl Pw : Table}
  (h : ProbeOK hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw)
include h

theorem ProbeOK.cpu_h : C.h ≤ 2 ^ 27 := h.two (cpuAirP hd0 stk0 ctr0 n la, C) (by simp [probeTables])
theorem ProbeOK.mem_h : Mm.h ≤ 2 ^ 27 := h.two (memAir, Mm) (by simp [probeTables])
theorem ProbeOK.prog_h : Pg.h ≤ 2 ^ 27 := h.two (progAir heap, Pg) (by simp [probeTables])
theorem ProbeOK.hdr_h : Hd.h ≤ 2 ^ 27 := h.two (hdrAir jets, Hd) (by simp [probeTables])
theorem ProbeOK.pop_h : Po.h ≤ 2 ^ 27 := h.two (popAir, Po) (by simp [probeTables])
theorem ProbeOK.instw_h : Iw.h ≤ 2 ^ 27 := h.two (instwAir, Iw) (by simp [probeTables])
theorem ProbeOK.plan_h : Pl.h ≤ 2 ^ 27 := h.two (planAir plan, Pl) (by simp [probeTables])
theorem ProbeOK.pw_h : Pw.h ≤ 2 ^ 27 := h.two (pwAir, Pw) (by simp [probeTables])

theorem ProbeOK.sel_bit {r : Nat} (hr : r < C.h) {i : Nat} (hi : i < NKINDS) : (C.main r (SEL + i)).val ≤ 1 :=
  bit_val_le (sel_bitP h.cpu hr hi)

/-- A probe row, as a number: `0` or `1`. -/
theorem ProbeOK.probe_bit {r : Nat} (hr : r < C.h) : (sProbe.eval (C.env r)).val ≤ 1 := by
  obtain ⟨k, _, hs⟩ := kind_ofP h.cpu hr
  simp only [sProbe, sPFirst, sPLater, E.eval, B.col, env_main0 hr]
  rw [hs 12 (by decide), hs 13 (by decide)]
  rcases Nat.decEq 12 k with h12 | h12 <;> rcases Nat.decEq 13 k with h13 | h13
  · rw [if_neg h12, if_neg h13]; decide
  · rw [if_neg h12, if_pos h13]; decide
  · rw [if_pos h12, if_neg h13]; decide
  · subst h12; exact absurd h13 (by decide)

/-- The CPU's corpus messages count `0` or `1`, on every row. -/
theorem ProbeOK.cpu_count {r : Nat} (hr : r < C.h) : ∀ I ∈ cpuInters, (I.count.eval (C.env r)).val ≤ 1 := by
  obtain ⟨k, hk, hsel⟩ := kind_ofP h.cpu hr
  have z : (0 : F).val ≤ 1 := by decide
  rcases Nat.lt_or_ge k 11 with h11 | h11
  · have e11 := hsel 11 (by decide)
    have e12 := hsel 12 (by decide)
    have e13 := hsel 13 (by decide)
    rw [if_neg (Nat.ne_of_gt h11)] at e11
    rw [if_neg (by omega)] at e12
    rw [if_neg (by omega)] at e13
    exact cpu_countR (rowSat_ofP h.cpu hr e11 e12 e13) hr
  · rcases (show k = 11 ∨ k = 12 ∨ k = 13 by unfold NKINDS at hk; omega) with rfl | rfl | rfl
    · obtain ⟨hacts, _, happ, hS, _⟩ := inst_facts hr hsel
      intro I hI
      simp only [cpuInters, writeInters, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hI
      rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show ((acts.getD 0 zero).eval _).val ≤ 1; rw [hacts 0 (by decide)]; exact z
      · show ((acts.getD 1 zero).eval _).val ≤ 1; rw [hacts 1 (by decide)]; exact z
      · show ((acts.getD 2 zero).eval _).val ≤ 1; rw [hacts 2 (by decide)]; exact z
      · show ((acts.getD 3 zero).eval _).val ≤ 1; rw [hacts 3 (by decide)]; exact z
      · show (sApp.eval _).val ≤ 1; rw [happ]; exact z
      all_goals (show (sS.eval _).val ≤ 1; rw [hS]; exact z)
    all_goals
      obtain ⟨h0, hj, _, _, happ, hS, _⟩ := probe_facts hr hsel (by omega)
      intro I hI
      simp only [cpuInters, writeInters, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hI
      rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show ((acts.getD 0 zero).eval _).val ≤ 1; rw [h0]; split <;> decide
      · show ((acts.getD 1 zero).eval _).val ≤ 1; rw [hj 1 (by decide) (by decide)]; exact z
      · show ((acts.getD 2 zero).eval _).val ≤ 1; rw [hj 2 (by decide) (by decide)]; exact z
      · show ((acts.getD 3 zero).eval _).val ≤ 1; rw [hj 3 (by decide) (by decide)]; exact z
      · show (sApp.eval _).val ≤ 1; rw [happ]; exact z
      all_goals (show (sS.eval _).val ≤ 1; rw [hS]; exact z)

theorem ProbeOK.nil_bit {r : Nat} (hr : r < C.h) : C.main r P_NILACT * (C.main r P_NILACT - 1) = 0 := by
  have := memP_probe h.cpu hr (x := bool (col P_NILACT)) (by simp [probeCons])
  simpa [B.bool, E.eval, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

/-- The CPU sends on `mem`, `roots`, `hdr`, `arg` and `plan` with bits. -/
theorem ProbeOK.cpu_sender {bus : String}
    (hB : bus = "mem" ∨ bus = "roots" ∨ bus = "hdr" ∨ bus = "arg" ∨ bus = "plan") :
    SenderOn bus (cpuAirP hd0 stk0 ctr0 n la, C) := by
  have hseg : bus ≠ "segend" := by rcases hB with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨fun I hI hb => cpuP_weights I hI (by rw [hb]; exact hseg), fun r hr I hI hbus => ?_⟩
  have cv := col_eval hr
  have c11 : (sInst.eval (C.env r)).val ≤ 1 := by
    simp only [sInst, B.col, E.eval, env_main0 hr]; exact h.sel_bit hr (by decide)
  have c13 : (sPLater.eval (C.env r)).val ≤ 1 := by
    simp only [sPLater, B.col, E.eval, env_main0 hr]; exact h.sel_bit hr (by decide)
  have cp := h.probe_bit hr
  have hra := bit_val_le (flag_bitsP h.cpu hr).2.1
  have hnil := bit_val_le (h.nil_bit hr)
  have no : ∀ b : String, b ≠ "mem" → b ≠ "roots" → b ≠ "hdr" → b ≠ "arg" → b ≠ "plan" → b ≠ bus := by
    intro b h1 h2 h3 h4 h5 e
    rcases hB with rfl | rfl | rfl | rfl | rfl
    · exact h1 e
    · exact h2 e
    · exact h3 e
    · exact h4 e
    · exact h5 e
  rcases List.mem_append.1 hI with hI | hI
  · rcases List.mem_append.1 hI with hI | hI
    · exact h.cpu_count hr I hI
    · simp only [jetInters, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact c11
      · exact c11
      · exact absurd hbus (no "popch" (by decide) (by decide) (by decide) (by decide) (by decide))
      · exact absurd hbus (no "popch" (by decide) (by decide) (by decide) (by decide) (by decide))
      · exact absurd hbus (no "wch" (by decide) (by decide) (by decide) (by decide) (by decide))
      · exact absurd hbus (no "wch" (by decide) (by decide) (by decide) (by decide) (by decide))
      · show ((col J_RA).eval (C.env r)).val ≤ 1; rw [cv]; exact hra
  · simp only [probeInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cp
    · exact c13
    · exact absurd hbus (no "popch" (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact absurd hbus (no "popch" (by decide) (by decide) (by decide) (by decide) (by decide))
    · show ((col P_NILACT).eval (C.env r)).val ≤ 1; rw [cv]; exact hnil
    · exact absurd hbus (no "segend" (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact absurd hbus (no "segend" (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact c13
    · exact absurd hbus (no "pwch" (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact absurd hbus (no "pwch" (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact cp

theorem ProbeOK.prog_sender : SenderOn "mem" (progAir heap, Pg) := by
  refine ⟨fun I hI _ => by simp only [progAir, List.mem_cons, List.not_mem_nil, or_false] at hI; rw [hI]; decide,
    fun r hr I hI _ => ?_⟩
  simp only [progAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  subst hI
  show ((prec 4).eval _).val ≤ 1
  rw [prec_eval h.pgpre hr (by show 4 < 5; decide)]
  rcases programRows_row heap r with e | e <;> rw [show (progAir heap).pretrace = programRows heap from rfl, e] <;>
    decide

theorem ProbeOK.pop_act {q : Nat} (hq : q < Po.h) : Po.main q 7 * (Po.main q 7 - 1) = 0 :=
  col_bit h.po (by simp [popAir, popCons]) hq

theorem ProbeOK.instw_act {q : Nat} (hq : q < Iw.h) : Iw.main q 17 * (Iw.main q 17 - 1) = 0 :=
  col_bit h.iw (by simp [instwAir, instwCons]) hq

theorem ProbeOK.pw_act {q : Nat} (hq : q < Pw.h) : Pw.main q 5 * (Pw.main q 5 - 1) = 0 :=
  col_bit h.pw (by simp [pwAir]) hq

theorem ProbeOK.pop_sender : SenderOn "mem" (popAir, Po) := by
  refine ⟨fun I hI hb => ?_, fun r hr I hI hb => ?_⟩
  · simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl <;> first | decide | exact absurd hb (by decide)
  · simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
    · show ((col 7).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le (h.pop_act hr)
    · exact absurd hb (by decide)

theorem ProbeOK.instw_sender {bus : String} (hB : bus = "mem" ∨ bus = "tmpl" ∨ bus = "arg") :
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

theorem ProbeOK.pw_sender : SenderOn "mem" (pwAir, Pw) := by
  refine ⟨fun I hI _ => ?_, fun r hr I hI hb => ?_⟩
  · simp only [pwAir, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl <;> decide
  · simp only [pwAir, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
    · show ((col 5).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le (h.pw_act hr)
    · show ((col 5).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le (h.pw_act hr)

omit h in
theorem probeTables_cases {p : AirD × Table}
    (hp : p ∈ probeTables hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw) :
    p = (cpuAirP hd0 stk0 ctr0 n la, C) ∨ p = (memAir, Mm) ∨ p = (progAir heap, Pg) ∨ p = (rootsAir roots, Rt) ∨
      p = (hdrAir jets, Hd) ∨ p = (tmplAir jets, Tm) ∨ p = (popAir, Po) ∨ p = (instwAir, Iw) ∨
      p = (planAir plan, Pl) ∨ p = (pwAir, Pw) := by
  simp only [probeTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  exact hp

/-- **A `mem` message with count `1` is a memory row.** -/
theorem ProbeOK.memHit {v : List F}
    (hit : ∃ p ∈ probeTables hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw,
      (p.1.name == "mem" || p.1.name == "roots" || p.1.name == "hdr" || p.1.name == "tmpl" ||
        p.1.name == "plan") = false ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := bus_hit_on h.bal h.hts
    (fun p => p.1.name == "mem" || p.1.name == "roots" || p.1.name == "hdr" || p.1.name == "tmpl" ||
      p.1.name == "plan")
    (fun p hp hpr => by
      rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.cpu_sender (.inl rfl)
      · exact nomatch hpr
      · exact h.prog_sender
      · exact nomatch hpr
      · exact nomatch hpr
      · exact nomatch hpr
      · exact h.pop_sender
      · exact h.instw_sender (.inl rfl)
      · exact nomatch hpr
      · exact h.pw_sender) hit
  rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact nomatch hpr
  · exact nomatch hpr
  · exact absurd (notBus rfl) hne
  · exact nomatch hpr

/-- **A lookup on a provider's bus finds one of its rows.** -/
theorem ProbeOK.lookup {bus : String} (sender : AirD × Table → Bool)
    (hs : ∀ p ∈ probeTables hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw,
      sender p = true → SenderOn bus p) {v : List F}
    (hit : ∃ p ∈ probeTables hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw,
      sender p = true ∧ ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = bus ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ p ∈ probeTables hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw, sender p = false ∧
      ∃ r, r < p.2.h ∧ rowSends p.1 p.2 bus v r ≠ 0 := by
  obtain ⟨p, hp, hpr, r, hr, hne⟩ := bus_hit_on h.bal h.hts (fun p => !sender p)
    (fun p hp hpr => hs p hp (by cases hq : sender p <;> simp_all))
    (by obtain ⟨p, hp, hsp, rest⟩ := hit; exact ⟨p, hp, by rw [hsp]; rfl, rest⟩)
  exact ⟨p, hp, by cases hq : sender p <;> simp_all, r, hr, hne⟩

end

end Circuit
