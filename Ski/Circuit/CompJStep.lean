import Ski.Circuit.CompJKind
import Ski.Circuit.CompStep
import Ski.Circuit.ProbeSound

/-!
# The composed circuit with jets: its tables, and what their buses force

`CJOK`: what an accepted proof of the composed circuit with jets gives,
over its ten tables (`compJTables`).  The CPU, program, witness, POP and
INSTW tables send on the `mem` bus with counts `0` or `1`; the memory and
the segment, roots, header and template tables provide.  So a `mem`
message with count `1` is a memory row (`memHit`), a `segs` message a
segment row (`segHit`), and the jet lookups find their providers' rows
(`rootsHit`, `hdrHit`, `tmplHit`, `argHit`).  A blinded table's blocks are
on buses of their own, so they change nothing here (`rowSends_withBlocks`).

A row of the machine's kinds reads its cells, steps and halts as in the
composed circuit (`CJOK.read`, `step`, `halt`).
-/

namespace Circuit

open B Air JetTable

-- ---------------------------------------------------------------------------
-- Blinded tables
-- ---------------------------------------------------------------------------

theorem withBlocks_inters (A : AirD) (blocks : List (String × Bool)) :
    (withBlocks A blocks).inters = A.inters ++ blocks.zipIdx.map (fun ((bus, send), i) =>
      blindMsg bus (A.width + 5 * i) send) := rfl

theorem withBlocks_block_bus {A : AirD} {blocks : List (String × Bool)} {I : Inter}
    (h : I ∈ blocks.zipIdx.map (fun ((bus, send), i) => blindMsg bus (A.width + 5 * i) send)) :
    ∃ b ∈ blocks, I.bus = b.1 ∧ I.weight = 1 := by
  obtain ⟨⟨⟨bus, send⟩, i⟩, hm, e⟩ := List.mem_map.1 h
  subst e
  obtain ⟨_, hi, he⟩ := List.mem_zipIdx hm
  simp only [Nat.zero_add, Nat.sub_zero] at hi he
  exact ⟨(bus, send), he ▸ List.getElem_mem hi, rfl, rfl⟩

/-- **A blinded table satisfies its own constraints.** -/
theorem sat_of_withBlocks {A : AirD} {blocks : List (String × Bool)} {T : Table}
    (h : Sat (withBlocks A blocks) T) : Sat A T :=
  ⟨h.1, fun c hc r hr => h.2 c (List.mem_append_left _ hc) r hr⟩

theorem preIs_withBlocks {A : AirD} {blocks : List (String × Bool)} {T : Table}
    (h : PreIs (withBlocks A blocks) T) : PreIs A T := h

/-- **The blocks send nothing on another bus.** -/
theorem rowSends_withBlocks {A : AirD} {blocks : List (String × Bool)} {T : Table} {bus : String}
    (hb : ∀ b ∈ blocks, b.1 ≠ bus) (v : List F) (q : Nat) :
    rowSends (withBlocks A blocks) T bus v q = rowSends A T bus v q := by
  unfold rowSends
  rw [withBlocks_inters, List.foldr_append]
  congr 1
  apply foldr_zero_init
  intro I hI
  obtain ⟨b, hbm, hbus, _⟩ := withBlocks_block_bus hI
  exact if_neg (fun h' => hb b hbm (hbus ▸ h'.1))

theorem senderOn_withBlocks {A : AirD} {blocks : List (String × Bool)} {T : Table} {bus : String}
    (hb : ∀ b ∈ blocks, b.1 ≠ bus) (h : SenderOn bus (A, T)) : SenderOn bus (withBlocks A blocks, T) := by
  refine ⟨fun I hI hbus => ?_, fun r hr I hI hbus => ?_⟩
  · rcases List.mem_append.1 hI with hI | hI
    · exact h.1 I hI hbus
    · obtain ⟨b, hbm, hbus', _⟩ := withBlocks_block_bus hI
      exact absurd (hbus' ▸ hbus) (hb b hbm)
  · rcases List.mem_append.1 hI with hI | hI
    · exact h.2 r hr I hI hbus
    · obtain ⟨b, hbm, hbus', _⟩ := withBlocks_block_bus hI
      exact absurd (hbus' ▸ hbus) (hb b hbm)

theorem padCopiesMin_mem {x : List F} : ∀ {rows : List (List F)}, x ∈ padCopiesMin rows → x ∈ rows
  | [], h => nomatch h
  | r :: rs, h => by
    rcases List.mem_append.1 h with h | h
    · exact h
    · rw [List.eq_of_mem_replicate h]; exact List.mem_cons_self

/-- A table with no message on `bus` sends on it as a sender would. -/
theorem senderOn_nobus {p : AirD × Table} {bus : String} (h : ∀ I ∈ p.1.inters, I.bus ≠ bus) :
    SenderOn bus p :=
  ⟨fun I hI hb => absurd hb (h I hI), fun _ _ I hI hb => absurd hb (h I hI)⟩

-- ---------------------------------------------------------------------------
-- The tables
-- ---------------------------------------------------------------------------

/-- The composed circuit with jets: ten tables. -/
def compJTables (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat)
    (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Pg Wt Sg Rt Hd Tm Po Iw : Table) : List (AirD × Table) :=
  [(cpuAirCJ hd0 stk0 ctr0 n nilA, C), (memAirC, Mm), (progAirC heap N W, Pg), (witAir N W, Wt),
   (segsAir segRoots, Sg), (rootsAirCJ roots, Rt), (hdrAirCJ jets, Hd), (tmplAirCJ jets, Tm), (popAirCJ, Po),
   (instwAirCJ, Iw)]

/-- **What an accepted proof of the composed circuit with jets gives.** -/
structure CJOK (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat)
    (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Pg Wt Sg Rt Hd Tm Po Iw : Table) : Prop where
  cpu : Sat (cpuAirCJ hd0 stk0 ctr0 n nilA) C
  mem : Sat memAirC Mm
  prog : Sat (progAirC heap N W) Pg
  wit : Sat (witAir N W) Wt
  po : Sat popAirCJ Po
  iw : Sat instwAirCJ Iw
  pgpre : PreIs (progAirC heap N W) Pg
  wtpre : PreIs (witAir N W) Wt
  sgpre : PreIs (segsAir segRoots) Sg
  rtpre : PreIs (rootsAirCJ roots) Rt
  hdpre : PreIs (hdrAirCJ jets) Hd
  tmpre : PreIs (tmplAirCJ jets) Tm
  bal : Balanced (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw)
  hts : HeightsOK (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw)
  two : TwoAdic (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw)

theorem compJTables_names {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {segRoots : List Nat}
    {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Pg Wt Sg Rt Hd Tm Po Iw : Table} {p : AirD × Table}
    (hp : p ∈ compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw) :
    p = (cpuAirCJ hd0 stk0 ctr0 n nilA, C) ∨ p = (memAirC, Mm) ∨ p = (progAirC heap N W, Pg) ∨
      p = (witAir N W, Wt) ∨ p = (segsAir segRoots, Sg) ∨ p = (rootsAirCJ roots, Rt) ∨ p = (hdrAirCJ jets, Hd) ∨
      p = (tmplAirCJ jets, Tm) ∨ p = (popAirCJ, Po) ∨ p = (instwAirCJ, Iw) := by
  simp only [compJTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  exact hp

theorem cpuIntersCJ_eq : cpuIntersCJ =
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
     ⟨"arg", 1, col J_RA, [col J_CLK, col J_RV, col J_XROOT]⟩,
     ⟨"segs", 1, sRSJ, [.add (col CNTJ) one, col ROOTJ]⟩,
     blindMsg "blind_a" BLAJ false, blindMsg "blind_b" BLBJ true, blindMsg "blind_c" BLCJ true] := rfl

theorem cpuIntersCJ_weight : ∀ I ∈ cpuIntersCJ, 1 ≤ I.weight := by
  have : cpuIntersCJ.all (fun I => decide (1 ≤ I.weight)) = true := by decide
  exact fun I hI => of_decide_eq_true (List.all_eq_true.1 this I hI)

theorem actOfCJ_le (k j : Nat) : actOfCJ k j ≤ 1 := by
  unfold actOfCJ; split
  · split <;> decide
  · split
    · decide
    · exact actOf_le k j

section

variable {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {segRoots : List Nat}
  {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Pg Wt Sg Rt Hd Tm Po Iw : Table}

/-- **The CPU sends with bits** on `mem`, `segs`, `roots`, `hdr` and `arg`. -/
theorem cpu_senderCJ (hs : Sat (cpuAirCJ hd0 stk0 ctr0 n nilA) C) {B : String}
    (hB : B = "mem" ∨ B = "segs" ∨ B = "roots" ∨ B = "hdr" ∨ B = "arg") :
    SenderOn B (cpuAirCJ hd0 stk0 ctr0 n nilA, C) := by
  refine ⟨fun I hI _ => cpuIntersCJ_weight I hI, fun r hr I hI hbus => ?_⟩
  obtain ⟨k, hk⟩ := kind_ofCJ hs hr
  obtain ⟨hf, _, hApp, hS, _, hRS, hIn, _⟩ := kind_factsCJ hr hk
  have act : ∀ j, j < 4 → ((acts.getD j zero).eval (C.env r)).val ≤ 1 := fun j hj => by
    rw [(hf j hj).1]; exact ofN_le_one (actOfCJ_le k j)
  have hra := bit_val_le (flag_bitsCJ hs hr).2.1
  have no : ∀ b : String, b ≠ "mem" → b ≠ "segs" → b ≠ "roots" → b ≠ "hdr" → b ≠ "arg" → b ≠ B := by
    intro b h1 h2 h3 h4 h5 e
    rcases hB with rfl | rfl | rfl | rfl | rfl
    · exact h1 e
    · exact h2 e
    · exact h3 e
    · exact h4 e
    · exact h5 e
  change I ∈ cpuIntersCJ at hI
  rw [cpuIntersCJ_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact act 0 (by decide)
  · exact act 1 (by decide)
  · exact act 2 (by decide)
  · exact act 3 (by decide)
  · show (sApp.eval _).val ≤ 1; rw [hApp]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sS.eval _).val ≤ 1; rw [hS]; exact ite_le_one _
  · show (sInst.eval _).val ≤ 1; rw [hIn]; exact ite_le_one _
  · show (sInst.eval _).val ≤ 1; rw [hIn]; exact ite_le_one _
  · exact absurd hbus (no "popch" (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact absurd hbus (no "popch" (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact absurd hbus (no "wch" (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact absurd hbus (no "wch" (by decide) (by decide) (by decide) (by decide) (by decide))
  · show ((col J_RA).eval (C.env r)).val ≤ 1; rw [col_eval hr]; exact hra
  · show (sRSJ.eval _).val ≤ 1; rw [hRS]; exact ite_le_one _
  · exact absurd hbus (no "blind_a" (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact absurd hbus (no "blind_b" (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact absurd hbus (no "blind_c" (by decide) (by decide) (by decide) (by decide) (by decide))

theorem popCJ_sender (hpo : Sat popAirCJ Po) : SenderOn "mem" (popAirCJ, Po) := by
  refine senderOn_withBlocks (by decide) ⟨fun I hI hb => ?_, fun r hr I hI hb => ?_⟩
  · simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl <;> first | decide | exact absurd hb (by decide)
  · simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
    · show ((col 7).eval _).val ≤ 1; rw [col_eval hr]
      exact bit_val_le (col_bit (sat_of_withBlocks hpo) (by simp [popAir, popCons]) hr)
    · exact absurd hb (by decide)

theorem instwCJ_sender (hiw : Sat instwAirCJ Iw) {bus : String} (hB : bus = "mem" ∨ bus = "tmpl" ∨ bus = "arg") :
    SenderOn bus (instwAirCJ, Iw) := by
  have hb' : ∀ b ∈ [("blind_d", false), ("blind_e", true)], b.1 ≠ bus := by
    intro b hb e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hB with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> exact absurd e (by decide)
  have hiw' := sat_of_withBlocks hiw
  refine senderOn_withBlocks hb' ⟨fun I hI _ => ?_, fun r hr I hI hb => ?_⟩
  · simp only [instwAir, instwInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [instwAir, instwInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    have b6 := col_bit hiw' (i := 6) (by simp [instwAir, instwCons]) hr
    have b10 := col_bit hiw' (i := 10) (by simp [instwAir, instwCons]) hr
    have b17 := col_bit hiw' (i := 17) (by simp [instwAir, instwCons]) hr
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl
    · show ((col 6).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le b6
    · show ((col 10).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le b10
    · rcases hB with rfl | rfl | rfl <;> exact absurd hb (by decide)
    · rcases hB with rfl | rfl | rfl <;> exact absurd hb (by decide)
    · show ((col 17).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le b17
    · show ((col 17).eval _).val ≤ 1; rw [col_eval hr]; exact bit_val_le b17

variable (h : CJOK hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw)
include h

theorem CJOK.cpu_h : C.h ≤ 2 ^ 27 := h.two (cpuAirCJ hd0 stk0 ctr0 n nilA, C) (by simp [compJTables])
theorem CJOK.mem_h : Mm.h ≤ 2 ^ 27 := h.two (memAirC, Mm) (by simp [compJTables])
theorem CJOK.pop_h : Po.h ≤ 2 ^ 27 := h.two (popAirCJ, Po) (by simp [compJTables])
theorem CJOK.instw_h : Iw.h ≤ 2 ^ 27 := h.two (instwAirCJ, Iw) (by simp [compJTables])
theorem CJOK.sg_h : Sg.h ≤ 2 ^ 27 := h.two (segsAir segRoots, Sg) (by simp [compJTables])

theorem CJOK.pop_act {q : Nat} (hq : q < Po.h) : Po.main q 7 * (Po.main q 7 - 1) = 0 :=
  col_bit (sat_of_withBlocks h.po) (by simp [popAir, popCons]) hq

theorem CJOK.instw_act {q : Nat} (hq : q < Iw.h) : Iw.main q 17 * (Iw.main q 17 - 1) = 0 :=
  col_bit (sat_of_withBlocks h.iw) (by simp [instwAir, instwCons]) hq

/-- **A lookup on a provider's bus finds a row of a table outside
    `sender`.** -/
theorem CJOK.lookup {bus : String} (sender : AirD × Table → Bool)
    (hs : ∀ p ∈ compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw,
      sender p = true → SenderOn bus p)
    {v : List F}
    (hit : ∃ p ∈ compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw,
      sender p = true ∧ ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = bus ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ p ∈ compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw,
      sender p = false ∧ ∃ r, r < p.2.h ∧ rowSends p.1 p.2 bus v r ≠ 0 := by
  obtain ⟨p, hp, hpr, r, hr, hne⟩ := bus_hit_on h.bal h.hts (fun p => !sender p)
    (fun p hp hpr => hs p hp (by cases hq : sender p <;> simp_all))
    (by obtain ⟨p, hp, hsp, rest⟩ := hit; exact ⟨p, hp, by rw [hsp]; rfl, rest⟩)
  exact ⟨p, hp, by cases hq : sender p <;> simp_all, r, hr, hne⟩

/-- The `mem` senders. -/
def memSenderCJ (p : AirD × Table) : Bool :=
  p.1.name == "cpu" || p.1.name == "prog" || p.1.name == "wit" || p.1.name == "pop" || p.1.name == "instw"

/-- **A `mem` message with count `1` is a memory row.** -/
theorem CJOK.memHit {v : List F}
    (hit : ∃ p ∈ compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw,
      memSenderCJ p = true ∧ ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "mem" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := h.lookup memSenderCJ (fun p hp hs => by
    rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cpu_senderCJ h.cpu (.inl rfl)
    · exact absurd hs (ne_true_of_eq_false rfl)
    · exact (prog_senderC h.pgpre "mem").on
    · exact (wit_senderC h.wtpre (.inl rfl)).on
    · exact absurd hs (ne_true_of_eq_false rfl)
    · exact absurd hs (ne_true_of_eq_false rfl)
    · exact absurd hs (ne_true_of_eq_false rfl)
    · exact absurd hs (ne_true_of_eq_false rfl)
    · exact popCJ_sender h.po
    · exact instwCJ_sender h.iw (.inl rfl)) hit
  rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · refine ⟨m, hm, ?_⟩
    have hm' : m < Mm.h := hm
    apply Decidable.byContradiction
    intro hv
    apply hne
    simp only [rowSends, memAirC, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, B.col,
      E.eval, env_main0 hm']
    rw [if_neg (fun h' => hv h'.2), if_neg (fun h' => absurd h'.1 (by decide)), add_zero', add_zero']
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd hpr (ne_false_of_eq_true rfl)

/-- **A `segs` message with count `1` is a segment row.** -/
theorem CJOK.segHit {v : List F}
    (hit : ∃ p ∈ compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw,
      (p.1.name == "cpu") = true ∧ ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "segs" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ i, i < Sg.h ∧ [Sg.pre i 0, Sg.pre i 1] = v := by
  obtain ⟨p, hp, hpr, m, hm, hne⟩ := h.lookup (bus := "segs") (fun p => p.1.name == "cpu") (fun p hp hs => by
    rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cpu_senderCJ h.cpu (.inr (.inl rfl))
    all_goals exact absurd hs (ne_true_of_eq_false rfl)) hit
  rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · refine ⟨m, hm, ?_⟩
    have hm' : m < Sg.h := hm
    apply Decidable.byContradiction
    intro hv
    apply hne
    show (if "segs" = "segs" ∧ [(prec 0).eval (Sg.env m), (prec 1).eval (Sg.env m)] = v then _ else 0) + 0 = 0
    have e0 : (prec 0).eval (Sg.env m) = Sg.pre m 0 := by
      show Sg.pre ((m + 0) % Sg.h) 0 = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hm']
    have e1 : (prec 1).eval (Sg.env m) = Sg.pre m 1 := by
      show Sg.pre ((m + 0) % Sg.h) 1 = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hm']
    rw [e0, e1, if_neg (fun h' => hv h'.2), add_zero']
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne

theorem CJOK.cell {a t x y : F}
    (hm : ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = [a, t, x, y]) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) := by
  obtain ⟨m, hm, e⟩ := hm
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  have hmP : m < P := Nat.lt_of_lt_of_le hm (Nat.le_trans h.mem_h (by decide))
  rw [mem_addrC h.mem m hm] at e0
  rw [← e0, val_ofN hmP, memOf_get hm, e1, e2, e3]
  exact ⟨hm, rfl⟩

/-- A CPU `mem` message with count `1` is a memory cell. -/
theorem CJOK.sendC {r : Nat} (hr : r < C.h) {I : Inter} (hI : I ∈ cpuIntersCJ) (hbus : I.bus = "mem")
    {a t x y : F} (hf : I.fields.map (fun e => e.eval (C.env r)) = [a, t, x, y])
    (hc : I.count.eval (C.env r) = 1) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) :=
  h.cell (h.memHit ⟨_, List.mem_cons_self, rfl, r, hr, I, hI, hbus, hf, hc⟩)

-- ---------------------------------------------------------------------------
-- The jet lookups
-- ---------------------------------------------------------------------------

/-- **An instantiation's root is listed.** -/
theorem CJOK.rootsHit {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) :
    ∃ a g, (a, g) ∈ roots ∧ C.main r HD = ofN a ∧ C.main r J_G = ofN g := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "roots") (fun p => p.1.name == "cpu")
    (fun p hp hs => by
      rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cpu_senderCJ h.cpu (.inr (.inr (.inl rfl)))
      all_goals exact absurd hs (ne_true_of_eq_false rfl))
    (v := [C.main r HD, C.main r J_G])
    ⟨_, List.mem_cons_self, rfl, r, hr, ⟨"roots", 1, sInst, [col HD, col J_G]⟩,
      by rw [show (cpuAirCJ hd0 stk0 ctr0 n nilA).inters = cpuIntersCJ from rfl, cpuIntersCJ_eq]; simp only [List.mem_cons, true_or, or_true], rfl,
      by simp only [List.map_cons, List.map_nil, col_eval hr],
      by simp only [sInst, col_eval hr, hi]⟩
  rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · change rowSends (withBlocks (providerAir "roots" 2 (rootsRowsCJ roots)) [("blind_g", false)]) Rt "roots" _ q ≠ 0 at hne
    rw [rowSends_withBlocks (A := providerAir "roots" 2 (rootsRowsCJ roots)) (blocks := [("blind_g", false)]) (by decide)] at hne
    have hm := provider_row (preIs_withBlocks h.rtpre)
      (fun x hx => by
        obtain ⟨_, _, e⟩ := List.mem_map.1 (padCopiesMin_mem hx); rw [← e]; rfl) hq hne
    obtain ⟨⟨a, g⟩, hm, e⟩ := List.mem_map.1 (padCopiesMin_mem hm)
    simp only [List.cons.injEq, and_true] at e
    exact ⟨a, g, hm, e.1.symm, e.2.symm⟩
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne

/-- **An instantiation's header is its jet's.** -/
theorem CJOK.hdrHit {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) :
    ∃ J g, jets[g]? = some J ∧ [C.main r J_G, C.main r J_K, C.main r J_N, C.main r J_RL, C.main r J_RA,
      C.main r J_RG, C.main r J_RV] = hdrRow J g := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "hdr") (fun p => p.1.name == "cpu")
    (fun p hp hs => by
      rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cpu_senderCJ h.cpu (.inr (.inr (.inr (.inl rfl))))
      all_goals exact absurd hs (ne_true_of_eq_false rfl))
    (v := [C.main r J_G, C.main r J_K, C.main r J_N, C.main r J_RL, C.main r J_RA, C.main r J_RG, C.main r J_RV])
    ⟨_, List.mem_cons_self, rfl, r, hr,
      ⟨"hdr", 1, sInst, [col J_G, col J_K, col J_N, col J_RL, col J_RA, col J_RG, col J_RV]⟩,
      by rw [show (cpuAirCJ hd0 stk0 ctr0 n nilA).inters = cpuIntersCJ from rfl, cpuIntersCJ_eq]; simp only [List.mem_cons, true_or, or_true], rfl,
      by simp only [List.map_cons, List.map_nil, col_eval hr],
      by simp only [sInst, col_eval hr, hi]⟩
  rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · change rowSends (withBlocks (providerAir "hdr" 7 (hdrRowsCJ jets)) [("blind_f", false), ("blind_g", true)]) Hd "hdr" _ q ≠ 0 at hne
    rw [rowSends_withBlocks (A := providerAir "hdr" 7 (hdrRowsCJ jets)) (blocks := [("blind_f", false), ("blind_g", true)]) (by decide)] at hne
    have hm := provider_row (preIs_withBlocks h.hdpre)
      (fun x hx => by
        obtain ⟨⟨J, g⟩, _, e⟩ := List.mem_map.1 (padCopiesMin_mem hx)
        rw [← e]; show (_ ++ opCols _).length = 7; rw [List.length_append, opCols_len]; rfl) hq hne
    obtain ⟨⟨J, g⟩, hm, e⟩ := List.mem_map.1 (padCopiesMin_mem hm)
    obtain ⟨_, hg, hJ⟩ := List.mem_zipIdx hm
    simp only [Nat.zero_add, Nat.sub_zero] at hg hJ
    exact ⟨J, g, by rw [List.getElem?_eq_getElem hg, hJ], e.symm⟩
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne

/-- **An active INSTW row's template is a row of its jet.** -/
theorem CJOK.tmplHit {w : Nat} (hw : w < Iw.h) (ha : Iw.main w 17 = 1) :
    ∃ J g j cl, jets[g]? = some J ∧ (symCells J J.body 0).1[j]? = some cl ∧
      (List.range 11).map (fun i => Iw.main w (2 + i)) = tmplRow g j cl := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "tmpl") (fun p => p.1.name == "instw")
    (fun p hp hs => by
      rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact instwCJ_sender h.iw (.inr (.inl rfl)) | exact absurd hs (ne_true_of_eq_false rfl))
    (v := (List.range 11).map (fun i => Iw.main w (2 + i)))
    ⟨(instwAirCJ, Iw), by simp [compJTables], rfl, w, hw, ⟨"tmpl", 1, col 17, (List.range 11).map fun i => col (2 + i)⟩,
      List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))), rfl,
      by rw [List.map_map]; exact List.map_congr_left (fun i _ => col_eval hw _),
      by rw [col_eval hw, ha]⟩
  rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · change rowSends (withBlocks (providerAir "tmpl" 11 (tmplRowsCJ jets)) [("blind_e", false), ("blind_f", true)]) Tm "tmpl" _ q ≠ 0 at hne
    rw [rowSends_withBlocks (A := providerAir "tmpl" 11 (tmplRowsCJ jets)) (blocks := [("blind_e", false), ("blind_f", true)]) (by decide)] at hne
    have hm := provider_row (preIs_withBlocks h.tmpre)
      (fun x hx => by
        obtain ⟨_, _, hv⟩ := List.mem_flatMap.1 (padCopiesMin_mem hx)
        obtain ⟨⟨cl, j⟩, _, e⟩ := List.mem_map.1 hv
        rw [← e]; exact tmplRow_len _ _ _) hq hne
    obtain ⟨⟨J, g⟩, hm, hv⟩ := List.mem_flatMap.1 (padCopiesMin_mem hm)
    obtain ⟨_, hg, hJ⟩ := List.mem_zipIdx hm
    simp only [Nat.zero_add, Nat.sub_zero] at hg hJ
    obtain ⟨⟨cl, j⟩, hm2, e⟩ := List.mem_map.1 hv
    obtain ⟨_, hj, hcl⟩ := List.mem_zipIdx hm2
    simp only [Nat.zero_add, Nat.sub_zero] at hj hcl
    exact ⟨J, g, j, cl, by rw [List.getElem?_eq_getElem hg, hJ], by rw [List.getElem?_eq_getElem hj, hcl],
      e.symm⟩
  · exact absurd (notBus rfl) hne
  · exact absurd hpr (ne_false_of_eq_true rfl)

/-- **An argument lookup finds an active POP row.** -/
theorem CJOK.argHit {v : List F}
    (hit : ∃ p ∈ compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw,
      (p.1.name == "cpu" || p.1.name == "instw") = true ∧
      ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = "arg" ∧
        I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ q, q < Po.h ∧ Po.main q 7 = 1 ∧ [Po.main q 0, Po.main q 2, Po.main q 4] = v := by
  obtain ⟨p, hp, hpr, q, hq, hne⟩ := h.lookup (bus := "arg") (fun p => p.1.name == "cpu" || p.1.name == "instw")
    (fun p hp hs => by
      rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact cpu_senderCJ h.cpu (.inr (.inr (.inr (.inr rfl))))
        | exact instwCJ_sender h.iw (.inr (.inr rfl))
        | exact absurd hs (ne_true_of_eq_false rfl)) hit
  rcases compJTables_names hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hpr (ne_false_of_eq_true rfl)
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · exact absurd (notBus rfl) hne
  · -- a POP row: its use count is nonzero, so it is active
    change rowSends (withBlocks (popAir) [("blind_c", false), ("blind_d", true)]) Po "arg" _ q ≠ 0 at hne
    rw [rowSends_withBlocks (A := popAir) (blocks := [("blind_c", false), ("blind_d", true)]) (by decide)] at hne
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
    have hc := (sat_of_withBlocks h.po).2 (.mul (col 6) (.sub one (col 7))) (by simp [popAir, popCons]) q hq'
    simp only [E.eval, cv, B.one, B.c, ofN_one] at hc
    rcases mul_eq_zero hc with e | e
    · exact absurd e huse
    · exact ⟨q, hq', (sub_eq_zero e).symm, hf⟩
  · exact absurd hpr (ne_false_of_eq_true rfl)

-- ---------------------------------------------------------------------------
-- The machine's rows
-- ---------------------------------------------------------------------------

/-- A range check's value is below `2^24`. -/
theorem CJOK.rangeVal_lt {r : Nat} (hr : r < C.h) {j : Nat} (hj : j < 4) :
    ((rangeVal j).eval (C.env r)).val < 2 ^ 24 :=
  bitsVal_lt hr (BITS + j * RANGE_BITS) RANGE_BITS (Nat.le_refl _)
    (fun _ hi => range_bitCJ h.cpu hr hj hi)

/-- **An active read**: the address is below the counter, and the memory
    holds there a cell with the kind's tag and the row's fields. -/
theorem CJOK.read {r k : Nat} (hr : r < C.h) (hk : IsKindCJ C r k) {j : Nat} (hj : j < 4)
    (hact : actOfCJ k j = 1) :
    rd (memOf Mm) (C.main r CTR).val (C.main r (addrCol j)).val =
      some (cellOf (ofN (tagOfCJ k j)) (C.main r (FLD + 2 * j)) (C.main r (FLD + 2 * j + 1))) := by
  obtain ⟨hf, _⟩ := kind_factsCJ hr hk
  obtain ⟨ha, ht⟩ := hf j hj
  rw [hact, ofN_one] at ha
  have hadr : (addrs.getD j zero).eval (C.env r) = C.main r (addrCol j) := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [addrs, addrCol, fld, B.col, E.eval, env_main0 hr]
  have hI : readInterCJ j ∈ cpuIntersCJ := by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      (rw [cpuIntersCJ_eq]; simp only [List.mem_cons, true_or, or_true])
  obtain ⟨hlt, hget⟩ := h.sendC hr hI rfl
    (a := C.main r (addrCol j)) (t := ofN (tagOfCJ k j)) (x := C.main r (FLD + 2 * j))
    (y := C.main r (FLD + 2 * j + 1))
    (by simp only [readInterCJ, List.map_cons, List.map_nil, hadr, ht, fld, B.col, E.eval, env_main0 hr]; rfl)
    ha
  have hre := range_eqCJ h.cpu hr hj
  rw [ha, one_mul', hadr] at hre
  have e := sub_eq_zero hre
  have hctr : C.main r CTR = (C.main r (addrCol j) + 1) + (rangeVal j).eval (C.env r) := by
    rw [← e, add_sub_cancel3]
  have hv := h.rangeVal_lt hr hj
  have hm := h.mem_h
  have hb : (C.main r (addrCol j)).val + 1 + ((rangeVal j).eval (C.env r)).val < P := by
    have : 2 ^ 27 + 2 ^ 24 + 8 < P := P_big
    omega
  have h1 : (C.main r (addrCol j) + 1).val = (C.main r (addrCol j)).val + 1 :=
    val_add_of_lt (by show _ + 1 < P; omega)
  have hval : (C.main r CTR).val = (C.main r (addrCol j)).val + 1 + ((rangeVal j).eval (C.env r)).val := by
    rw [hctr, val_add_of_lt (by rw [h1]; exact hb), h1]
  unfold rd
  rw [if_pos (by omega), hget]

/-- **A stepping row steps**: to the registers its kind computes. -/
theorem CJOK.step {r k : Nat} (hr : r < C.h) (hk : IsKindCJ C r k) (hk4 : k < 4) :
    stepRow (memOf Mm) (rowOf C r) = some ⟨((nextHdOfCJ k).eval (C.env r)).val,
      ((nextStkOfCJ k).eval (C.env r)).val, ((nextCtrOfCJ k).eval (C.env r)).val⟩ := by
  obtain ⟨_, _, hApp, hS, _⟩ := kind_factsCJ hr hk
  have cv := col_eval hr
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · -- App: read the head; write the argument's stack cell
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val =
        some (.app (C.main r (FLD + 0)).val (C.main r (FLD + 1)).val) := h.read hr hk (j := 0) (by decide) rfl
    have w0 := h.sendC hr (I := ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩)
      (by rw [cpuIntersCJ_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
      (a := C.main r CTR) (t := ofN 5) (x := C.main r (FLD + 1)) (y := C.main r STK)
      (by simp only [List.map_cons, List.map_nil, fld, cv]; rfl) (by rw [hApp]; rfl)
    rw [cellOf_cons] at w0
    have hc1 : (C.main r CTR + 1).val = (C.main r CTR).val + 1 :=
      val_add_of_lt (by have := w0.1; have := h.mem_h; have := P_big; show _ + 1 < P; omega)
    simp only [stepRow, rowOf, stepG, r0, wrs, w0.2, beq_self_eq_true, Bool.and_true, ↓reduceIte,
      List.length_cons, List.length_nil, Option.some.injEq, Air.Row.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show _ = ((fld 0).eval _).val; rw [fld, cv]
    · show _ = ((col CTR).eval _).val; rw [cv]
    · show _ = ((E.add (col CTR) one).eval _).val
      simp only [E.eval, cv, B.one, B.c, ofN_one, hc1]
  · -- I: read the head and one stack cell
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .I :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    simp only [stepRow, rowOf, stepG, r0, r1, wrs, ↓reduceIte, List.length_nil, Nat.add_zero,
      Option.some.injEq, Air.Row.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show _ = ((fld 2).eval _).val; rw [fld, cv]
    · show _ = ((fld 3).eval _).val; rw [fld, cv]
    · show _ = ((col CTR).eval _).val; rw [cv]
  · -- K: read the head and two stack cells
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .K :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val =
        some (.cons (C.main r (FLD + 4)).val (C.main r (FLD + 5)).val) := h.read hr hk (j := 2) (by decide) rfl
    simp only [stepRow, rowOf, stepG, r0, r1, r2, wrs, ↓reduceIte, List.length_nil, Nat.add_zero,
      Option.some.injEq, Air.Row.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show _ = ((fld 2).eval _).val; rw [fld, cv]
    · show _ = ((fld 5).eval _).val; rw [fld, cv]
    · show _ = ((col CTR).eval _).val; rw [cv]
  · -- S: read the head and three stack cells; write three cells
    have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .S :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val =
        some (.cons (C.main r (FLD + 4)).val (C.main r (FLD + 5)).val) := h.read hr hk (j := 2) (by decide) rfl
    have r3 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 5)).val =
        some (.cons (C.main r (FLD + 6)).val (C.main r (FLD + 7)).val) := h.read hr hk (j := 3) (by decide) rfl
    have hs1 : sS.eval (C.env r) = 1 := by rw [hS]; rfl
    have w1 := h.sendC hr (I := ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩)
      (by rw [cpuIntersCJ_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
      (a := C.main r CTR) (t := ofN 3) (x := C.main r (FLD + 4)) (y := C.main r (FLD + 6))
      (by simp only [List.map_cons, List.map_nil, fld, cv]; rfl) hs1
    rw [cellOf_app] at w1
    have hm := h.mem_h
    have hPb := P_big
    have hc1 : (C.main r CTR + 1).val = (C.main r CTR).val + 1 :=
      val_add_of_lt (by have := w1.1; show _ + 1 < P; omega)
    have hc2 : (C.main r CTR + ofN 2).val = (C.main r CTR).val + 1 + 1 := by
      rw [val_add_nat (by have := w1.1; omega)]
    have hc3 : (C.main r CTR + ofN 3).val = (C.main r CTR).val + 3 := by
      rw [val_add_nat (by have := w1.1; omega)]
    have w2 := h.sendC hr (I := ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩)
      (by rw [cpuIntersCJ_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
      (a := C.main r CTR + 1) (t := ofN 5) (x := C.main r CTR) (y := C.main r (FLD + 7))
      (by simp only [List.map_cons, List.map_nil, fld, E.eval, cv, B.one, B.c, ofN_one]) hs1
    rw [cellOf_cons, hc1] at w2
    have w3 := h.sendC hr (I := ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩)
      (by rw [cpuIntersCJ_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
      (a := C.main r CTR + ofN 2) (t := ofN 5) (x := C.main r (FLD + 6)) (y := C.main r CTR + 1)
      (by simp only [List.map_cons, List.map_nil, fld, E.eval, cv, B.one, B.c, ofN_one]) hs1
    rw [cellOf_cons, hc2, hc1] at w3
    simp only [stepRow, rowOf, stepG, r0, r1, r2, r3, wrs, w1.2, w2.2, w3.2, beq_self_eq_true,
      Bool.and_true, ↓reduceIte, List.length_cons, List.length_nil, Option.some.injEq, Air.Row.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show _ = ((fld 2).eval _).val; rw [fld, cv]
    · show _ = ((E.add (col CTR) (c 2)).eval _).val
      simp only [E.eval, cv, B.c, hc2]
    · show _ = ((E.add (col CTR) (c 3)).eval _).val
      simp only [E.eval, cv, B.c, hc3]

/-- **A halting row halts**: its reads show a combinator short of
    arguments, or an atom. -/
theorem CJOK.halt {r k : Nat} (hr : r < C.h) (hk : IsKindCJ C r k) (hk4 : 4 ≤ k) (hk11 : k < 11) :
    haltRow (memOf Mm) (rowOf C r) = true := by
  rcases (show k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .I :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val = some .nil :=
      h.read hr hk (j := 1) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .K :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val = some .nil :=
      h.read hr hk (j := 1) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .K :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val = some .nil :=
      h.read hr hk (j := 2) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1, r2]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .S :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val = some .nil :=
      h.read hr hk (j := 1) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .S :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val = some .nil :=
      h.read hr hk (j := 2) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1, r2]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some .S :=
      h.read hr hk (j := 0) (by decide) rfl
    have r1 : rd (memOf Mm) (C.main r CTR).val (C.main r STK).val =
        some (.cons (C.main r (FLD + 2)).val (C.main r (FLD + 3)).val) := h.read hr hk (j := 1) (by decide) rfl
    have r2 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 3)).val =
        some (.cons (C.main r (FLD + 4)).val (C.main r (FLD + 5)).val) := h.read hr hk (j := 2) (by decide) rfl
    have r3 : rd (memOf Mm) (C.main r CTR).val (C.main r (FLD + 5)).val = some .nil :=
      h.read hr hk (j := 3) (by decide) rfl
    simp only [haltRow, rowOf, r0, short, r1, r2, r3]
  · have r0 : rd (memOf Mm) (C.main r CTR).val (C.main r HD).val = some (.atom (C.main r (FLD + 0)).val) :=
      h.read hr hk (j := 0) (by decide) rfl
    simp only [haltRow, rowOf, r0]

end

end Circuit
