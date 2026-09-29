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

/-- **An instantiation's root is listed.** -/
theorem ProbeOK.rootsHit {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) :
    ∃ a g, (a, g) ∈ roots ∧ C.main r HD = ofN a ∧ C.main r J_G = ofN g := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "roots") (fun p => p.1.name == "cpu")
    (fun p hp hs => by
      rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.cpu_sender (.inr (.inl rfl))
      all_goals exact absurd hs (ne_true_of_eq_false rfl))
    (v := [C.main r HD, C.main r J_G])
    ⟨_, List.mem_cons_self, rfl, r, hr, ⟨"roots", 1, sInst, [col HD, col J_G]⟩,
      List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self), rfl,
      by simp only [List.map_cons, List.map_nil, col_eval hr],
      by simp only [sInst, col_eval hr, hi]⟩
  rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · obtain ⟨a, g, hm, e⟩ := rootsRows_mem (provider_row h.rtpre (rootsRows_len roots) hq hne)
    simp only [List.cons.injEq, and_true] at e
    exact ⟨a, g, hm, e.1, e.2⟩
  all_goals exact absurd (notBus rfl) hne

/-- **An instantiation's header is its jet's.** -/
theorem ProbeOK.hdrHit {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) :
    ∃ J g, jets[g]? = some J ∧ [C.main r J_G, C.main r J_K, C.main r J_N, C.main r J_RL, C.main r J_RA,
      C.main r J_RG, C.main r J_RV] = hdrRow J g := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "hdr") (fun p => p.1.name == "cpu")
    (fun p hp hs => by
      rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.cpu_sender (.inr (.inr (.inl rfl)))
      all_goals exact absurd hs (ne_true_of_eq_false rfl))
    (v := [C.main r J_G, C.main r J_K, C.main r J_N, C.main r J_RL, C.main r J_RA, C.main r J_RG, C.main r J_RV])
    ⟨_, List.mem_cons_self, rfl, r, hr,
      ⟨"hdr", 1, sInst, [col J_G, col J_K, col J_N, col J_RL, col J_RA, col J_RG, col J_RV]⟩,
      List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl,
      by simp only [List.map_cons, List.map_nil, col_eval hr],
      by simp only [sInst, col_eval hr, hi]⟩
  rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact hdrRows_mem (provider_row h.hdpre (hdrRows_len jets) hq hne)
  all_goals exact absurd (notBus rfl) hne

/-- **An active INSTW row's template is a row of its jet.** -/
theorem ProbeOK.tmplHit {w : Nat} (hw : w < Iw.h) (ha : Iw.main w 17 = 1) :
    ∃ J g j cl, jets[g]? = some J ∧ (symCells J J.body 0).1[j]? = some cl ∧
      (List.range 11).map (fun i => Iw.main w (2 + i)) = tmplRow g j cl := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "tmpl") (fun p => p.1.name == "instw")
    (fun p hp hs => by
      rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact h.instw_sender (.inr (.inl rfl)) | exact absurd hs (ne_true_of_eq_false rfl))
    (v := (List.range 11).map (fun i => Iw.main w (2 + i)))
    ⟨(instwAir, Iw), by simp [probeTables], rfl, w, hw, ⟨"tmpl", 1, col 17, (List.range 11).map fun i => col (2 + i)⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))), rfl,
      by rw [List.map_map]; exact List.map_congr_left (fun i _ => col_eval hw _),
      by rw [col_eval hw, ha]⟩
  rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact tmplRows_mem (provider_row h.tmpre (tmplRows_len jets) hq hne)
  · exact absurd (notBus rfl) hne
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne

/-- **An argument lookup finds an active POP row.** -/
theorem ProbeOK.argHit {v : List F}
    (hit : ∃ p ∈ probeTables hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw,
      (p.1.name == "cpu" || p.1.name == "instw") = true ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "arg" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ q, q < Po.h ∧ Po.main q 7 = 1 ∧ [Po.main q 0, Po.main q 2, Po.main q 4] = v := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "arg") (fun p => p.1.name == "cpu" || p.1.name == "instw")
    (fun p hp hs => by
      rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact h.cpu_sender (.inr (.inr (.inr (.inl rfl))))
        | exact h.instw_sender (.inr (.inr rfl))
        | exact absurd hs (ne_true_of_eq_false rfl)) hit
  rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · have hq' : q < Po.h := hq
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
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne

/-- **A probe row's plan lookup finds a segment of the plan.** -/
theorem ProbeOK.planHit {r : Nat} (hr : r < C.h) {I : Inter} (hI : I ∈ probeInters) (hbus : I.bus = "plan")
    (hc : I.count.eval (C.env r) = 1) :
    ∃ j s, plan[j]? = some s ∧ I.fields.map (fun e => e.eval (C.env r)) =
      [ofN j, ofN s.base, ofN s.k, ofN s.ctor, ofN s.arity, ofN s.parent, ofN s.field] := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "plan") (fun p => p.1.name == "cpu")
    (fun p hp hs => by
      rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.cpu_sender (.inr (.inr (.inr (.inr rfl))))
      all_goals exact absurd hs (ne_true_of_eq_false rfl))
    ⟨_, List.mem_cons_self, rfl, r, hr, I, List.mem_append_right _ hI, hbus, rfl, hc⟩
  rcases probeTables_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact planRows_mem (provider_row h.plpre (planRows_len plan) hq hne)
  · exact absurd (notBus rfl) hne

end

-- ---------------------------------------------------------------------------
-- Chains: POPCH at instantiations and later probe rows, WCH, PWCH
-- ---------------------------------------------------------------------------

theorem pop_rowSendsG {Po : Table} {q : Nat} (hq : q < Po.h) (hb : Po.main q 7 * (Po.main q 7 - 1) = 0)
    (t c' l s : F) :
    rowSends popAir Po "popch" [t, c', l, s] q =
      ofN (if (popEdges Po t c').act q && decide ((popEdges Po t c').outN q = (l, [s])) then 1 else 0) -
      ofN (if (popEdges Po t c').act q && decide ((popEdges Po t c').inN q = (l, [s])) then 1 else 0) := by
  have cv := col_eval hq
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

/-- An INSTW row's chain messages: its outgoing edge less its incoming one. -/
theorem instw_rowSendsG {Iw : Table} {q : Nat} (hq : q < Iw.h) (hb : Iw.main q 17 * (Iw.main q 17 - 1) = 0)
    (t c0 g0 l : F) :
    rowSends instwAir Iw "wch" [t, c0, g0, l] q =
      ofN (if (wchEdges Iw t c0 g0).act q && decide ((wchEdges Iw t c0 g0).outN q = (l, [])) then 1 else 0) -
      ofN (if (wchEdges Iw t c0 g0).act q && decide ((wchEdges Iw t c0 g0).inN q = (l, [])) then 1 else 0) := by
  have cv := col_eval hq
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


/-- The PW rows at counter `t`, counter `c0`, base `b0` and marker count
    `k0`, as edges: from `(i, [])` to `(i + 1, [])`. -/
def pwEdges (Pw : Table) (t c0 b0 k0 : F) : Edges :=
  ⟨Pw.h, fun q => decide (Pw.main q 5 = 1) && decide (Pw.main q 0 = t) && decide (Pw.main q 1 = c0) &&
      decide (Pw.main q 2 = b0) && decide (Pw.main q 3 = k0),
    fun q => Pw.main q 4, fun _ => [], fun _ => []⟩

theorem dec_msg5 (a b c d e t u x y l : F) :
    decide ([a, b, c, d, e] = [t, u, x, y, l]) =
      (decide (a = t) && decide (b = u) && decide (c = x) && decide (d = y) &&
        decide ((e, ([] : List F)) = (l, []))) := by
  simp only [List.cons.injEq, Prod.mk.injEq, and_true, Bool.decide_and, Bool.and_assoc]

theorem pw_rowSendsG {Pw : Table} {q : Nat} (hq : q < Pw.h) (hb : Pw.main q 5 * (Pw.main q 5 - 1) = 0)
    (t c0 b0 k0 l : F) :
    rowSends pwAir Pw "pwch" [t, c0, b0, k0, l] q =
      ofN (if (pwEdges Pw t c0 b0 k0).act q && decide ((pwEdges Pw t c0 b0 k0).outN q = (l, [])) then 1 else 0) -
      ofN (if (pwEdges Pw t c0 b0 k0).act q && decide ((pwEdges Pw t c0 b0 k0).inN q = (l, [])) then 1 else 0) := by
  have cv := col_eval hq
  simp only [rowSends, pwAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, cv,
    B.one, B.c, ofN_one, true_and, ↓reduceIte, add_zero']
  rw [if_neg (show ¬ ("mem" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [add_zero']
  have eneg : ∀ (P : Prop) [Decidable P] (x : F), (if P then -x else 0) = -(if P then x else 0) := by
    intro P _ x; split
    · rfl
    · decide
  rw [eneg, bit_ite hb, bit_ite hb, dec_msg5, dec_msg5, sub_eq_add_neg' _ _, add_comm']
  have ea : (pwEdges Pw t c0 b0 k0).act q = (decide (Pw.main q 5 = 1) && decide (Pw.main q 0 = t) &&
      decide (Pw.main q 1 = c0) && decide (Pw.main q 2 = b0) && decide (Pw.main q 3 = k0)) := rfl
  have ei : (pwEdges Pw t c0 b0 k0).inN q = (Pw.main q 4, []) := rfl
  have eo : (pwEdges Pw t c0 b0 k0).outN q = (Pw.main q 4 + 1, []) := rfl
  rw [ea, ei, eo]
  simp only [Bool.and_assoc]

/-- The probe CPU's messages on a bus other than `mem`: its jet and probe
    messages. -/
theorem cpuP_rowSends_off {hd0 stk0 ctr0 n la : Nat} {C : Table} {bus : String} (hb : bus ≠ "mem") (v : List F)
    (r : Nat) : rowSends (cpuAirP hd0 stk0 ctr0 n la) C bus v r =
      (jetInters ++ probeInters).foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval (C.env r)) = v then
        I.count.eval (C.env r) else 0) + acc) 0 := by
  unfold rowSends
  show (cpuInters ++ jetInters ++ probeInters).foldr _ 0 = _
  rw [List.append_assoc, List.foldr_append]
  apply foldr_zero_init
  intro I hI
  have hm : I.bus = "mem" := by
    have : cpuInters.all (fun I => I.bus == "mem") = true := by decide
    exact beq_iff_eq.1 (List.all_eq_true.1 this I hI)
  exact if_neg (fun (h' : I.bus = bus ∧ _) => hb (h'.1 ▸ hm))

theorem cpuP_popch {hd0 stk0 ctr0 n la : Nat} (C : Table) (r : Nat) (v : List F) :
    rowSends (cpuAirP hd0 stk0 ctr0 n la) C "popch" v r =
    ((if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), 0, C.env r (.main 0 STK)] = v then
      C.env r (.main 0 (SEL + 11)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_K), C.env r (.main 0 J_REST)] = v then
      -C.env r (.main 0 (SEL + 11)) else 0)) +
    ((if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), 0, C.env r (.main 0 STK)] = v then
      C.env r (.main 0 (SEL + 13)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 (E_BASE + 3)), C.env r (.main 0 E_REST)] = v
      then -C.env r (.main 0 (SEL + 13)) else 0)) := by
  rw [cpuP_rowSends_off (by decide), List.foldr_append]
  simp only [jetInters, probeInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col,
    B.c, sInst, sPLater, sProbe, sPFirst, true_and, ofN_zero, B.one, ofN_one]
  rw [if_neg (show ¬ ("roots" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("plan" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("plan" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']
  exact (add_assoc' _ _ _).symm

theorem cpuP_wch {hd0 stk0 ctr0 n la : Nat} (C : Table) (r : Nat) (v : List F) :
    rowSends (cpuAirP hd0 stk0 ctr0 n la) C "wch" v r =
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_G), 0] = v then
      C.env r (.main 0 (SEL + 11)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_G), C.env r (.main 0 J_N)] = v then
      -C.env r (.main 0 (SEL + 11)) else 0) := by
  rw [cpuP_rowSends_off (by decide), List.foldr_append]
  simp only [jetInters, probeInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col,
    B.c, sInst, sPLater, sProbe, sPFirst, true_and, ofN_zero, B.one, ofN_one]
  rw [if_neg (show ¬ ("roots" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("plan" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("plan" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

theorem cpuP_pwch {hd0 stk0 ctr0 n la : Nat} (C : Table) (r : Nat) (v : List F) :
    rowSends (cpuAirP hd0 stk0 ctr0 n la) C "pwch" v r =
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 S_BASE), C.env r (.main 0 (S_BASE + 1)),
        0] = v then C.env r (.main 0 (SEL + 12)) + C.env r (.main 0 (SEL + 13)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 S_BASE), C.env r (.main 0 (S_BASE + 1)),
        C.env r (.main 0 (S_BASE + 1))] = v then
      -(C.env r (.main 0 (SEL + 12)) + C.env r (.main 0 (SEL + 13))) else 0) := by
  rw [cpuP_rowSends_off (by decide), List.foldr_append]
  simp only [jetInters, probeInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col,
    B.c, sInst, sPLater, sProbe, sPFirst, true_and, ofN_zero, B.one, ofN_one]
  rw [if_neg (show ¬ ("roots" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("plan" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("plan" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

theorem msg_iteP (t c0 b0 k0 a l : F) (x : F) :
    (if [t, c0, b0, k0, a] = [t, c0, b0, k0, l] then x else 0) =
      if (some (a, ([] : List F)) : Option Node) = some (l, []) then x else 0 := by
  cases hd : decide (a = l) with
  | true =>
    have e := of_decide_eq_true hd
    rw [if_pos (show [t, c0, b0, k0, a] = [t, c0, b0, k0, l] by rw [e]),
      if_pos (show (some (a, ([] : List F)) : Option Node) = some (l, []) by rw [e])]
  | false =>
    have e := of_decide_eq_false hd
    rw [if_neg (fun h' => e (by simp only [List.cons.injEq] at h'; exact h'.2.2.2.2.1)),
      if_neg (fun h' => e (by simp only [Option.some.injEq, Prod.mk.injEq] at h'; exact h'.1))]

def popEndG (C : Table) (r0 : Nat) (c' K R : F) : Option Node :=
  if c' = C.main r0 CTR then some (K, [R]) else none

section

variable {hd0 stk0 ctr0 n la : Nat} {heap : List Cell} {roots : List (Nat × Nat)} {jets : List Air.Jet}
  {plan : List Air.Seg} {C Mm Pg Rt Hd Tm Po Iw Pl Pw : Table}
  (h : ProbeOK hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw)
include h

/-- The probe CPU's rows other than `r0` send nothing on `POPCH` at `r0`'s counter. -/
theorem ProbeOK.popch_other {r0 r : Nat} (hr0 : r0 < C.h) (hr : r < C.h) (hne : r ≠ r0) (c' l s : F) :
    rowSends (cpuAirP hd0 stk0 ctr0 n la) C "popch" [ofN r0, c', l, s] r = 0 := by
  have hCP : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  rw [cpuP_popch, env_main0 hr, clk_eqP h.cpu r hr]
  have hne' : ofN r ≠ ofN r0 := fun e => hne (ofN_inj (Nat.lt_trans hr hCP) (Nat.lt_trans hr0 hCP) e)
  have nf : ∀ (a b c : F), ¬ ([ofN r, a, b, c] = [ofN r0, c', l, s]) := fun a b c e => hne' (by
    simp only [List.cons.injEq] at e; exact e.1)
  rw [if_neg (nf _ _ _), if_neg (nf _ _ _), if_neg (nf _ _ _), if_neg (nf _ _ _), add_zero', add_zero']

/-- **`POPCH` is a flow** at a row that starts a chain from `(0, stk)` and
    ends it at `(K, R)`. -/
theorem ProbeOK.popConserveG {r0 : Nat} (hr0 : r0 < C.h) {K R : F}
    (hrow : ∀ v : List F, rowSends (cpuAirP hd0 stk0 ctr0 n la) C "popch" v r0 =
      (if [ofN r0, C.main r0 CTR, 0, C.main r0 STK] = v then 1 else 0) +
      (if [ofN r0, C.main r0 CTR, K, R] = v then -1 else 0)) (c' : F) :
    (popEdges Po (ofN r0) c').Conserve (popStart C r0 c') (popEndG C r0 c' K R) := by
  intro v
  obtain ⟨l, st⟩ := v
  have hPo : Po.h < P := Nat.lt_of_le_of_lt h.pop_h (by decide)
  have zero_case : (∀ x : F, st ≠ [x]) →
      (popEdges Po (ofN r0) c').cntOut (l, st) + Edges.oneIf (popStart C r0 c') (l, st) =
        (popEdges Po (ofN r0) c').cntIn (l, st) + Edges.oneIf (popEndG C r0 c' K R) (l, st) := by
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
    have o2 : Edges.oneIf (popEndG C r0 c' K R) (l, st) = 0 := by
      unfold Edges.oneIf popEndG; split
      · exact if_neg (fun e => hst _ (congrArg Prod.snd (Option.some.inj e)).symm)
      · exact if_neg (fun e => by cases e)
    rw [z1, z2, o1, o2]
  match st with
  | [] => exact zero_case (fun _ e => by cases e)
  | _ :: _ :: _ => exact zero_case (fun _ e => by cases e)
  | [s] =>
    have hb := h.bal "popch" [ofN r0, c', l, s]
    simp only [probeTables, List.foldr_cons, List.foldr_nil] at hb
    rw [sends_nobus' (A := memAir) rfl, sends_nobus' (A := progAir heap) rfl, sends_nobus' (A := rootsAir roots) rfl,
      sends_nobus' (A := hdrAir jets) rfl, sends_nobus' (A := tmplAir jets) rfl, sends_nobus' (A := instwAir) rfl,
      sends_nobus' (A := planAir plan) rfl, sends_nobus' (A := pwAir) rfl,
      zero_add', zero_add', zero_add', zero_add', zero_add', add_zero', add_zero', add_zero', add_zero'] at hb
    have hpop : tableSends popAir Po "popch" [ofN r0, c', l, s] =
        ofN ((popEdges Po (ofN r0) c').cntOut (l, [s])) - ofN ((popEdges Po (ofN r0) c').cntIn (l, [s])) := by
      unfold tableSends
      rw [foldr_range_congr Po.h (fun q hq => pop_rowSendsG hq (h.pop_act hq) _ _ _ _), fold_sub, fold_ofN, fold_ofN]
      rfl
    have hcpu : tableSends (cpuAirP hd0 stk0 ctr0 n la) C "popch" [ofN r0, c', l, s] =
        ofN (Edges.oneIf (popStart C r0 c') (l, [s])) - ofN (Edges.oneIf (popEndG C r0 c' K R) (l, [s])) := by
      unfold tableSends
      rw [fold_single _ C.h r0 hr0 (fun r hr hne => h.popch_other hr0 hr hne c' l s), hrow, msg_ite, msg_ite]
      unfold Edges.oneIf popStart popEndG
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
    have o2 : Edges.oneIf (popEndG C r0 c' K R) (l, [s]) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have hP : Po.h + 1 < P := Nat.lt_of_le_of_lt (Nat.add_le_add_right h.pop_h 1) (by decide)
    have e' := ofN_inj (Nat.lt_of_le_of_lt (Nat.add_le_add o1 b1) (by rw [Nat.add_comm]; exact hP))
      (Nat.lt_of_le_of_lt (Nat.add_le_add o2 b2) (by rw [Nat.add_comm]; exact hP)) e
    show sumTo Po.h _ + _ = sumTo Po.h _ + _
    omega

theorem ProbeOK.kindAt {r k : Nat} (hr : r < C.h) (hsel : C.main r (SEL + k) = 1) (hk : k < NKINDS) :
    SelsAre C r k := by
  obtain ⟨k', _, hs⟩ := kind_ofP h.cpu hr
  have e := hs k hk; rw [hsel] at e
  rcases Nat.decEq k k' with h1 | h1
  · rw [if_neg h1] at e; exact absurd e (by decide)
  · rw [← h1] at hs; exact hs

/-- **`POPCH` at an instantiation row.** -/
theorem ProbeOK.popConserve {r0 : Nat} (hr0 : r0 < C.h) (hi : C.main r0 (SEL + 11) = 1) (c' : F) :
    (popEdges Po (ofN r0) c').Conserve (popStart C r0 c') (popEnd C r0 c') := by
  have hs := h.kindAt hr0 hi (by decide)
  have h13 : C.main r0 (SEL + 13) = 0 := by rw [hs 13 (by decide), if_neg (by decide)]
  have := h.popConserveG hr0 (K := C.main r0 J_K) (R := C.main r0 J_REST) (fun v => by
    rw [cpuP_popch]
    have n13 : -C.main r0 (SEL + 13) = 0 := by rw [h13]; decide
    simp only [env_main0 hr0, clk_eqP h.cpu r0 hr0]
    rw [n13, h13, hi]
    simp only [ite_self, add_zero']) c'
  exact this

/-- **`POPCH` at a later probe row**: the ending segment's fields. -/
theorem ProbeOK.popConserveL {r0 : Nat} (hr0 : r0 < C.h) (hl : C.main r0 (SEL + 13) = 1) (c' : F) :
    (popEdges Po (ofN r0) c').Conserve (popStart C r0 c')
      (popEndG C r0 c' (C.main r0 (E_BASE + 3)) (C.main r0 E_REST)) := by
  have hs := h.kindAt hr0 hl (by decide)
  have h11 : C.main r0 (SEL + 11) = 0 := by rw [hs 11 (by decide), if_neg (by decide)]
  exact h.popConserveG hr0 (fun v => by
    rw [cpuP_popch]
    have n11 : -C.main r0 (SEL + 11) = 0 := by rw [h11]; decide
    simp only [env_main0 hr0, clk_eqP h.cpu r0 hr0]
    rw [n11, h11, hl]
    simp only [ite_self, zero_add']) c'

/-- **`WCH` is a flow** at an instantiation row's key, from `0` to its
    cell count. -/
theorem ProbeOK.wchConserve {r0 : Nat} (hr0 : r0 < C.h) (hi : C.main r0 (SEL + 11) = 1) :
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
    simp only [probeTables, List.foldr_cons, List.foldr_nil] at hb
    rw [sends_nobus' (A := memAir) rfl, sends_nobus' (A := progAir heap) rfl, sends_nobus' (A := rootsAir roots) rfl,
      sends_nobus' (A := hdrAir jets) rfl, sends_nobus' (A := tmplAir jets) rfl, sends_nobus' (A := popAir) rfl,
      sends_nobus' (A := planAir plan) rfl, sends_nobus' (A := pwAir) rfl,
      zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', add_zero', add_zero', add_zero'] at hb
    have hiw : tableSends instwAir Iw "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l] =
        ofN (E'.cntOut (l, [])) - ofN (E'.cntIn (l, [])) := by
      unfold tableSends
      rw [foldr_range_congr Iw.h (fun q hq => instw_rowSendsG hq (h.instw_act hq) _ _ _ _), fold_sub, fold_ofN,
        fold_ofN]
      rfl
    have hcpu : tableSends (cpuAirP hd0 stk0 ctr0 n la) C "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l] =
        ofN (Edges.oneIf (some ((0 : F), [])) (l, [])) - ofN (Edges.oneIf (some (C.main r0 J_N, [])) (l, [])) := by
      unfold tableSends
      rw [fold_single _ C.h r0 hr0 (fun r hr hne => by
        rw [cpuP_wch, env_main0 hr, env_main0 hr, clk_eqP h.cpu r hr]
        have hne' : ofN r ≠ ofN r0 := fun e => hne (ofN_inj (Nat.lt_trans hr hCP) (Nat.lt_trans hr0 hCP) e)
        rw [if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)),
          if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)), add_zero'])]
      rw [cpuP_wch]
      simp only [env_main0 hr0, clk_eqP h.cpu r0 hr0, hi]
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

/-- **`PWCH` is a flow** at a probe row's key, from `0` to the starting
    segment's arity. -/
theorem ProbeOK.pwConserve {r0 : Nat} (hr0 : r0 < C.h) (hp : C.main r0 (SEL + 12) + C.main r0 (SEL + 13) = 1) :
    (pwEdges Pw (ofN r0) (C.main r0 CTR) (C.main r0 S_BASE) (C.main r0 (S_BASE + 1))).Conserve
      (some ((0 : F), [])) (some (C.main r0 (S_BASE + 1), [])) := by
  intro v
  obtain ⟨l, st⟩ := v
  have hCP : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  let E' := pwEdges Pw (ofN r0) (C.main r0 CTR) (C.main r0 S_BASE) (C.main r0 (S_BASE + 1))
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
    have o2 : Edges.oneIf (some (C.main r0 (S_BASE + 1), [])) (l, x :: xs) = 0 :=
      if_neg (fun e => by have := congrArg Prod.snd (Option.some.inj e); cases this)
    show E'.cntOut _ + _ = E'.cntIn _ + _
    rw [z1, z2, o1, o2]
  | [] =>
    have hb := h.bal "pwch" [ofN r0, C.main r0 CTR, C.main r0 S_BASE, C.main r0 (S_BASE + 1), l]
    simp only [probeTables, List.foldr_cons, List.foldr_nil] at hb
    rw [sends_nobus' (A := memAir) rfl, sends_nobus' (A := progAir heap) rfl, sends_nobus' (A := rootsAir roots) rfl,
      sends_nobus' (A := hdrAir jets) rfl, sends_nobus' (A := tmplAir jets) rfl, sends_nobus' (A := popAir) rfl,
      sends_nobus' (A := instwAir) rfl, sends_nobus' (A := planAir plan) rfl,
      zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', add_zero'] at hb
    have hpw : tableSends pwAir Pw "pwch" [ofN r0, C.main r0 CTR, C.main r0 S_BASE, C.main r0 (S_BASE + 1), l] =
        ofN (E'.cntOut (l, [])) - ofN (E'.cntIn (l, [])) := by
      unfold tableSends
      rw [foldr_range_congr Pw.h (fun q hq => pw_rowSendsG hq (h.pw_act hq) _ _ _ _ _), fold_sub, fold_ofN,
        fold_ofN]
      rfl
    have hcpu : tableSends (cpuAirP hd0 stk0 ctr0 n la) C "pwch"
        [ofN r0, C.main r0 CTR, C.main r0 S_BASE, C.main r0 (S_BASE + 1), l] =
        ofN (Edges.oneIf (some ((0 : F), [])) (l, [])) -
          ofN (Edges.oneIf (some (C.main r0 (S_BASE + 1), [])) (l, [])) := by
      unfold tableSends
      rw [fold_single _ C.h r0 hr0 (fun r hr hne => by
        rw [cpuP_pwch, env_main0 hr, env_main0 hr, env_main0 hr, env_main0 hr, clk_eqP h.cpu r hr]
        have hne' : ofN r ≠ ofN r0 := fun e => hne (ofN_inj (Nat.lt_trans hr hCP) (Nat.lt_trans hr0 hCP) e)
        rw [if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)),
          if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)), add_zero'])]
      rw [cpuP_pwch]
      simp only [env_main0 hr0, clk_eqP h.cpu r0 hr0, hp]
      rw [msg_iteP, msg_iteP]
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
    rw [hcpu, hpw] at hb
    have e := bal_sub hb
    rw [← ofN_add, ← ofN_add] at e
    have b1 : E'.cntOut (l, []) ≤ Pw.h := sumTo_le_one (fun q => by split <;> decide) Pw.h
    have b2 : E'.cntIn (l, []) ≤ Pw.h := sumTo_le_one (fun q => by split <;> decide) Pw.h
    have o1 : Edges.oneIf (some ((0 : F), [])) (l, []) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have o2 : Edges.oneIf (some (C.main r0 (S_BASE + 1), [])) (l, []) ≤ 1 := by
      unfold Edges.oneIf; split <;> decide
    have hP : Pw.h + 1 < P := Nat.lt_of_le_of_lt (Nat.add_le_add_right h.pw_h 1) (by decide)
    have e' := ofN_inj (Nat.lt_of_le_of_lt (Nat.add_le_add o1 b1) (by rw [Nat.add_comm]; exact hP))
      (Nat.lt_of_le_of_lt (Nat.add_le_add o2 b2) (by rw [Nat.add_comm]; exact hP)) e
    show E'.cntOut (l, []) + _ = E'.cntIn (l, []) + _
    omega

theorem ProbeOK.jets_le : jets.length ≤ 2 ^ 27 := by
  have e : Hd.h = (hdrRows jets).length := h.hdpre.1
  have hl : jets.length ≤ (hdrRows jets).length := by
    have := padCopies_length_ge (jets.zipIdx.map fun (J, g) => hdrRow J g)
    rw [List.length_map, List.length_zipIdx] at this
    exact this
  have := h.hdr_h
  omega

theorem ProbeOK.heap_le : heap.length ≤ 2 ^ 27 := by
  have e : Pg.h = (programRows heap).length := h.pgpre.1
  have := programRows_length_ge heap
  have := h.prog_h
  omega

/-- **The probe circuit's instantiation rows are the jet circuit's**: an
    accepted probe proof gives the facts `JetCore` collects. -/
theorem ProbeOK.core : JetCore heap roots jets C Mm Po Iw := by
  refine ⟨h.po, h.iw, clk_eqP h.cpu, h.mem_h, h.pop_h, h.instw_h, mem_addr h.mem, h.jets_le, h.heap_le,
    fun q hq ha => ?_, fun w hw ha => ?_, fun v hv => ?_, fun w hw ha => h.tmplHit hw ha,
    fun r hr hi => h.rootsHit hr hi, fun r hr hi => h.hdrHit hr hi, fun r0 hr0 hi c' => h.popConserve hr0 hi c',
    fun r0 hr0 hi => h.wchConserve hr0 hi, fun r hr1 hi => ?_⟩
  · have cv := col_eval hq
    exact h.memHit ⟨(popAir, Po), by simp [probeTables], rfl, q, hq, ⟨"mem", 1, col 7, [col 3, c 5, col 4, col 5]⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl,
      by simp only [List.map_cons, List.map_nil, cv, B.c]; rfl, by rw [cv, ha]⟩
  · have cv := col_eval hw
    exact h.memHit ⟨(instwAir, Iw), by simp [probeTables], rfl, w, hw,
      ⟨"mem", 1, col 17, [.add (col 1) (col 3), col 4, col 13, col 14]⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))), rfl,
      by simp only [List.map_cons, List.map_nil, E.eval, cv], by rw [cv, ha]⟩
  · rcases hv with ⟨r, hr, ha, rfl⟩ | ⟨w, hw, ha, rfl⟩ | ⟨w, hw, ha, rfl⟩
    · have cv := col_eval hr
      exact h.argHit ⟨(cpuAirP hd0 stk0 ctr0 n la, C), by simp [probeTables], rfl, r, hr,
        ⟨"arg", 1, col J_RA, [col J_CLK, col J_RV, col J_XROOT]⟩,
        List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            List.mem_cons_self))))))), rfl,
        by simp only [List.map_cons, List.map_nil, cv], by rw [cv, ha]⟩
    · have cv := col_eval hw
      exact h.argHit ⟨(instwAir, Iw), by simp [probeTables], rfl, w, hw, ⟨"arg", 1, col 6, [col 0, col 8, col 15]⟩,
        List.mem_cons_self, rfl, by simp only [List.map_cons, List.map_nil, cv], by rw [cv, ha]⟩
    · have cv := col_eval hw
      exact h.argHit ⟨(instwAir, Iw), by simp [probeTables], rfl, w, hw, ⟨"arg", 1, col 10, [col 0, col 12, col 16]⟩,
        List.mem_cons_of_mem _ List.mem_cons_self, rfl, by simp only [List.map_cons, List.map_nil, cv],
        by rw [cv, ha]⟩
  · have hr : r < C.h := Nat.lt_of_succ_lt hr1
    have hsel := h.kindAt hr hi (by decide)
    obtain ⟨_, _, _, _, hnHd, hnStk, hnCtr⟩ := inst_facts hr hsel
    have hp : sProbe.eval (C.env r) = 0 := by
      simp only [sProbe, sPFirst, sPLater, E.eval, B.col, env_main0 hr]
      rw [hsel 12 (by decide), hsel 13 (by decide), if_neg (by decide), if_neg (by decide)]
      rfl
    obtain ⟨m1, m2, m3⟩ := next_regsP h.cpu hr hr1
    rw [m1, m2, m3, hnHd, hnStk, hnCtr, hi, hp, zero_add', zero_add', one_mul', one_mul', zero_mul', zero_mul',
      zero_mul', add_zero', add_zero', add_zero']
    exact ⟨rfl, rfl, rfl⟩

end

end Circuit
