import Ski.Circuit.CompPHonest

/-!
# The circuit with the Poseidon2 jet: the honest CPU's messages

The honest CPU's `mem` messages are memory cells' tuples
(`P2Run.cpuP_honest`).  Off the jet rows the CPU is the composed one, its
selector `P2SEL` clear, so its reads are the composed CPU's
(`actsP_off`, `tagsP_off`, `cpuC_honest`).  On a jet row the selectors are
fixed (`jetSub`): it reads the atom at the head and two stack cells, and
looks up the slots, as the jet's row requires (`p2Row_inv`).
-/

namespace Circuit

open B Air Compose CompM Mach

/-- `P2SEL` cleared. -/
def p2Off (a : Atom) : E := if a = .main 0 P2SEL then c 0 else .atom a

/-- A jet row's selectors: the kinds and the restart clear, `P2SEL` set. -/
def jetSub : Atom → E
  | .main 0 k => if SEL ≤ k ∧ k < SEL + NKINDS then c 0 else if k = RS then c 0
      else if k = P2SEL then c 1 else .atom (.main 0 k)
  | a => .atom a

theorem actsP_off : ∀ j, j < 4 → ((actsP.getD j zero).subst p2Off).norm = (acts.getD j zero).norm := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem tagsP_off : ∀ j, j < 4 → ((tagsP.getD j zero).subst p2Off).norm = (tagsC.getD j zero).norm := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

/-- On a jet row the reads' activities are `1, 1, 1, 0`. -/
theorem actsP_jet : ((actsP.getD 0 zero).subst jetSub).norm = (c 1).norm ∧
    ((actsP.getD 1 zero).subst jetSub).norm = (c 1).norm ∧ ((actsP.getD 2 zero).subst jetSub).norm = (c 1).norm ∧
    ((actsP.getD 3 zero).subst jetSub).norm = (c 0).norm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- On a jet row the reads' tags are an atom's and two stack cells'. -/
theorem tagsP_jet : ((tagsP.getD 0 zero).subst jetSub).norm = (c 6).norm ∧
    ((tagsP.getD 1 zero).subst jetSub).norm = (c 5).norm ∧ ((tagsP.getD 2 zero).subst jetSub).norm = (c 5).norm := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem sel_jet : (sApp.subst jetSub).norm = (c 0).norm ∧ (sS.subst jetSub).norm = (c 0).norm ∧
    (sP2.subst jetSub).norm = (c 1).norm ∧ (sRS.subst jetSub).norm = (c 0).norm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem cpuIntersP2_now : cpuIntersP2.all (fun I => I.count.onlyAtoms nowAtom &&
    I.fields.all (·.onlyAtoms nowAtom)) = true := by decide

theorem tupleOf_of_rd {A : List Cell} {c a : Nat} {cell : Cell} (h : rd A c a = some cell) :
    a < A.length ∧ tupleOf A a = [ofN a, ofN (cellTag cell), ofN (cellFields cell).1, ofN (cellFields cell).2] := by
  obtain ⟨_, hg⟩ := rd_get h
  refine ⟨(List.getElem?_eq_some_iff.1 hg).1, ?_⟩
  unfold tupleOf
  rw [List.getD_eq_getElem?_getD, hg]
  rfl

namespace P2Run

variable {R : P2Run} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCP R.A m0 [] [] R.J R.root R.segRoots nilA R.n R.e R.row) {K : Nat} (hK : R.e (R.n - 1) < K)
include hA hK

/-- **The honest CPU's `mem` messages are memory cells' tuples.** -/
theorem cpuP_honest (hd0 stk0 ctr0 n' nilA' J' root' : Nat) :
    HonestMem R.A (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) := by
  intro r hr' I hI hbus hc
  have hr : r < K := hr'
  have hR := runC hA hK
  change I ∈ cpuIntersP2 at hI
  have hnow := List.all_eq_true.1 cpuIntersP2_now I hI
  rw [Bool.and_eq_true, List.all_eq_true] at hnow
  cases hj : R.jetAt r with
  | false =>
    -- the composed CPU's message, with the same count and tuple
    let ρC := (cpuTableC R.A R.row R.e R.n R.segRoots K).env r
    have cong : ∀ e : E, e.onlyAtoms nowAtom = true → e.eval ((R.cpuTableP K).env r) = e.eval ρC :=
      E.eval_congr (R.cpuP_env_plain hr hj)
    have h0 : ρC (.main 0 P2SEL) = 0 := by
      show (cpuTableC R.A R.row R.e R.n R.segRoots K).main ((r + 0) % K) P2SEL = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hr]
      show cpuColC R.A R.row R.e R.n R.segRoots r (ROOT + 1) = 0
      unfold cpuColC
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    have hσ : ∀ a, (p2Off a).eval ρC = ρC a := by
      intro a
      unfold p2Off
      split
      · next e => rw [e, h0]; rfl
      · rfl
    have off : ∀ e e' : E, e.onlyAtoms nowAtom = true → (e.subst p2Off).norm = e'.norm →
        e.eval ((R.cpuTableP K).env r) = e'.eval ρC := fun e e' he hn => by
      rw [cong e he, ← E.eval_subst p2Off ρC hσ e]
      exact E.eval_eq_of_norm hn ρC
    have key : ∀ I' ∈ cpuIntersC, I'.bus = "mem" → I'.count.eval ρC = I.count.eval ((R.cpuTableP K).env r) →
        I'.fields.map (fun e => e.eval ρC) = I.fields.map (fun e => e.eval ((R.cpuTableP K).env r)) →
        ∃ m, m < R.A.length ∧ I.fields.map (fun e => e.eval ((R.cpuTableP K).env r)) = tupleOf R.A m := by
      intro I' hI' hb hcnt hfl
      obtain ⟨m, hm, e⟩ := cpuC_honest hR r hr I' hI' hb (by rw [hcnt]; exact hc)
      exact ⟨m, hm, hfl ▸ e⟩
    have fl : ∀ e ∈ I.fields, e.eval ((R.cpuTableP K).env r) = e.eval ρC := fun e he => cong e (hnow.2 e he)
    rw [cpuIntersP2_eq] at hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    have rd : ∀ j, j < 4 → I = readInterP j →
        ∃ m, m < R.A.length ∧ I.fields.map (fun e => e.eval ((R.cpuTableP K).env r)) = tupleOf R.A m := by
      intro j hj e
      subst e
      refine key (readInterC j) (by
          rw [cpuIntersC_eq]
          rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
            simp only [List.mem_cons, true_or, or_true]) rfl
        (off _ _ hnow.1 (actsP_off j hj)).symm ?_
      simp only [readInterC, readInterP, List.map_cons, List.map_nil]
      rw [fl (addrs.getD j zero) (by simp [readInterP]), fl (fld (2 * j)) (by simp [readInterP]),
        fl (fld (2 * j + 1)) (by simp [readInterP]),
        off (tagsP.getD j zero) (tagsC.getD j zero) (hnow.2 _ (by simp [readInterP])) (tagsP_off j hj)]
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact rd 0 (by decide) rfl
    · exact rd 1 (by decide) rfl
    · exact rd 2 (by decide) rfl
    · exact rd 3 (by decide) rfl
    all_goals first
      | exact absurd hbus (by decide)
      | (exfalso; apply hc
         show (col P2SEL).eval _ = 0
         rw [R.cpuP_col hr, R.cpuColP_plain hj]
         show cpuColC R.A R.row R.e R.n R.segRoots r (ROOT + 1) = 0
         unfold cpuColC
         rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)])
      | (refine key _ (by rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
            (cong _ hnow.1).symm (List.map_congr_left (fun e he => (fl e he).symm)))
  | true =>
    obtain ⟨hrs, _, hp2⟩ := jetAt_spec hj
    obtain ⟨hhd, k, s1, rest, bs, hstk, hs1, hslots, _, _, _, _⟩ := p2Row_inv hp2
    let ρ := (R.cpuTableP K).env r
    have cv : ∀ c, ρ (.main 0 c) = R.cpuColP r c := fun c => by
      show (R.cpuTableP K).main ((r + 0) % K) c = _
      rw [Nat.add_zero, Nat.mod_eq_of_lt hr]; rfl
    have hP : P2SEL = ROOT + 1 := rfl
    have hsel : ∀ c, SEL ≤ c → c < SEL + NKINDS → ρ (.main 0 c) = 0 := fun c h1 h2 => by
      rw [cv]; unfold cpuColP
      rw [if_neg (by unfold P2SEL ROOT RS CPU_WIDTH BITS FLD SEL NKINDS RANGE_BITS at *; omega), if_pos ⟨hj, h1, h2⟩]
    have hRS : ρ (.main 0 RS) = 0 := by
      rw [cv]; unfold cpuColP
      rw [if_neg (by decide), if_neg (fun h => by have := h.2.2; revert this; decide),
        if_neg (fun h => by have := h.2.2; revert this; decide), cpuColC_rs]
      unfold rsI; rw [hrs]; rfl
    have hp1 : ρ (.main 0 P2SEL) = 1 := by
      rw [cv]; unfold cpuColP; rw [if_pos rfl, hj]; rfl
    have hσ : ∀ a, (jetSub a).eval ρ = ρ a := by
      intro a
      cases a with
      | main o c =>
        cases o with
        | zero =>
          simp only [jetSub]
          by_cases h1 : SEL ≤ c ∧ c < SEL + NKINDS
          · rw [if_pos h1, hsel c h1.1 h1.2]; rfl
          · rw [if_neg h1]
            by_cases h2 : c = RS
            · rw [if_pos h2, h2, hRS]; rfl
            · rw [if_neg h2]
              by_cases h3 : c = P2SEL
              · rw [if_pos h3, h3, hp1]; rfl
              · rw [if_neg h3]; rfl
        | succ o => rfl
      | _ => rfl
    have ev : ∀ e e' : E, (e.subst jetSub).norm = e'.norm → e.eval ρ = e'.eval ρ := fun e e' hn => by
      rw [← E.eval_subst jetSub ρ hσ e]; exact E.eval_eq_of_norm hn ρ
    have base : ∀ c, c < BITS → ¬ (SEL ≤ c ∧ c < SEL + NKINDS) → (col c).eval ρ = cpuCol R.A (R.rowQ r) c := by
      intro c hc hs
      show ρ (.main 0 c) = _
      rw [cv]; unfold cpuColP
      have hb : BITS = 25 := rfl
      rw [if_neg (by unfold P2SEL ROOT RS CPU_WIDTH at *; omega), if_neg (fun h => hs ⟨h.2.1, h.2.2⟩),
        if_neg (fun h => by have := h.2.1; omega)]
      unfold cpuColC
      rw [if_pos (by unfold CPU_WIDTH at *; omega), if_neg (fun h => hs ⟨h.1, h.2.1⟩)]
      rfl
    have fl : ∀ i, i < 8 → (fld i).eval ρ =
        if i % 2 = 0 then ofN (fieldsAt R.A (R.rowQ r) (i / 2)).1 else ofN (fieldsAt R.A (R.rowQ r) (i / 2)).2 :=
      fun i hi => by
        rw [fld, base _ (by unfold BITS; omega) (fun h => by unfold FLD at h; omega), cpuCol_fld _ _ hi]
    have f0 : fieldsAt R.A (R.rowQ r) 0 = (R.J, 0) := by simp only [fieldsAt, addrAt, hhd]; rfl
    have f1 : fieldsAt R.A (R.rowQ r) 1 = (k, s1) := by simp only [fieldsAt, addrAt, hstk]; rfl
    have f2 : fieldsAt R.A (R.rowQ r) 2 = (R.root, rest) := by
      simp only [fieldsAt, addrAt, hstk, Option.getD_some, cellFields, hs1]
    obtain ⟨sl0, sl1, sl2⟩ : (R.A.take (R.rowQ r).ctr)[0]? = some .K ∧ (R.A.take (R.rowQ r).ctr)[1]? = some .I ∧
        (R.A.take (R.rowQ r).ctr)[2]? = some (.app 0 1) := by
      unfold P2Jet.slotsOK at hslots
      simp only [Bool.and_eq_true, beq_iff_eq] at hslots
      exact ⟨hslots.1.1, hslots.1.2, hslots.2⟩
    obtain ⟨_, _, _, h3⟩ := actsP_jet
    obtain ⟨t0, t1, t2⟩ := tagsP_jet
    obtain ⟨zA, zS, _, _⟩ := sel_jet
    have hd : (col HD).eval ρ = ofN (R.rowQ r).hd := base HD (by decide) (by decide)
    have st : (col STK).eval ρ = ofN (R.rowQ r).stk := base STK (by decide) (by decide)
    have slot : ∀ a cell, (R.A.take (R.rowQ r).ctr)[a]? = some cell →
        ∃ m, m < R.A.length ∧ [ofN a, ofN (cellTag cell), ofN (cellFields cell).1, ofN (cellFields cell).2] =
          tupleOf R.A m := fun a cell h => by
      obtain ⟨ha, e⟩ := tupleOf_of_rd (rd_of_take h)
      exact ⟨a, ha, e.symm⟩
    rw [cpuIntersP2_eq] at hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · -- the atom at the head
      obtain ⟨hm, e⟩ := tupleOf_of_rd hhd
      refine ⟨_, hm, ?_⟩
      simp only [readInterP, List.map_cons, List.map_nil, addrs, List.getD_cons_zero]
      rw [e, hd, ev _ _ t0, fl 0 (by decide), fl 1 (by decide), f0]; rfl
    · -- the first stack cell
      obtain ⟨hm, e⟩ := tupleOf_of_rd hstk
      refine ⟨_, hm, ?_⟩
      simp only [readInterP, List.map_cons, List.map_nil, addrs, List.getD_cons_zero, List.getD_cons_succ]
      rw [e, st, ev _ _ t1, fl 2 (by decide), fl 3 (by decide), f1]; rfl
    · -- the second
      obtain ⟨hm, e⟩ := tupleOf_of_rd hs1
      refine ⟨_, hm, ?_⟩
      simp only [readInterP, List.map_cons, List.map_nil, addrs, List.getD_cons_zero, List.getD_cons_succ]
      rw [e, ev _ _ t2, fl 3 (by decide), fl 4 (by decide), fl 5 (by decide), f1, f2]; rfl
    · exact absurd (ev _ _ h3) hc
    · exact absurd (ev _ _ zA) hc
    · exact absurd (ev _ _ zS) hc
    · exact absurd (ev _ _ zS) hc
    · exact absurd (ev _ _ zS) hc
    · exact absurd hbus (by decide)
    · exact slot 0 .K sl0
    · exact slot 1 .I sl1
    · exact slot 2 (.app 0 1) sl2
    all_goals exact absurd hbus (by decide)

end P2Run


-- ---------------------------------------------------------------------------
-- The CPU's segment, blinding and chain messages
-- ---------------------------------------------------------------------------

namespace P2Run

variable (R : P2Run)

/-- The restart, segment and root columns are the composed CPU's on every
    row, as are the blinding flags. -/
theorem cpuColP_hi {i c : Nat} (hc : CPU_WIDTH ≤ c) (hp : c ≠ P2SEL) :
    R.cpuColP i c = cpuColC R.A R.row R.e R.n R.segRoots i c := by
  unfold cpuColP
  rw [if_neg hp, if_neg (fun h => by have := h.2.2; unfold CPU_WIDTH BITS FLD SEL NKINDS RANGE_BITS at *; omega),
    if_neg (fun h => by have := h.2.2; omega)]

/-- **The CPU sends on `segs` as the composed CPU does.** -/
theorem cpuP_segs (hd0 stk0 ctr0 n' nilA' J' root' : Nat) (K : Nat) (v : List F) :
    tableSends (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) "segs" v =
      tableSends (cpuAirC hd0 stk0 ctr0 n' nilA') (cpuTableC R.A R.row R.e R.n R.segRoots K) "segs" v := by
  unfold tableSends
  apply foldr_range_congr
  intro r hr
  unfold rowSends
  show cpuIntersP2.foldr _ 0 = cpuIntersC.foldr _ 0
  rw [cpuIntersP2_eq, cpuIntersC_eq]
  have e1 := rowSends_one (T := R.cpuTableP K) (bus := "segs") (v := v) (r := r)
    ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩
    [readInterP 0, readInterP 1, readInterP 2, readInterP 3,
     ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩,
     ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩]
    [⟨"mem", 1, sP2, [c 0, c 1, c 0, c 0]⟩, ⟨"mem", 1, sP2, [c 1, c 2, c 0, c 0]⟩,
     ⟨"mem", 1, sP2, [c 2, c 3, c 0, c 1]⟩, ⟨"p2i", 1, sP2, [col CTR, c 0, c 0]⟩,
     ⟨"p2i", 1, .neg sP2, [col CTR, c P2_BITS, c 0]⟩, ⟨"p2o", 1, sP2, [col CTR, c 0, fld 5, c 0, c 0, c 1]⟩,
     ⟨"p2o", 1, .neg sP2, [col CTR, c P2_BITS, fld 5, c 0, c 0, c 1]⟩, blindMsg "blind_c" (P2SEL + 1) true,
     ⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩, ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩]
    (by decide) (by decide)
  have e2 := rowSends_one (T := cpuTableC R.A R.row R.e R.n R.segRoots K) (bus := "segs") (v := v) (r := r)
    ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩
    [readInterC 0, readInterC 1, readInterC 2, readInterC 3,
     ⟨"mem", 1, sApp, [col CTR, c 5, fld 1, col STK]⟩,
     ⟨"mem", 1, sS, [col CTR, c 3, fld 4, fld 6]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) one, c 5, col CTR, fld 7]⟩,
     ⟨"mem", 1, sS, [.add (col CTR) (c 2), c 5, fld 6, .add (col CTR) one]⟩]
    [⟨"blind_a", 1, .neg (col (BLA + 4)), blindFields BLA⟩, ⟨"blind_b", 1, col (BLB + 4), blindFields BLB⟩]
    (by decide) (by decide)
  refine e1.trans (Eq.trans ?_ e2.symm)
  have cv : ∀ c, c = RS ∨ c = CNT ∨ c = ROOT → (col c).eval ((R.cpuTableP K).env r) =
      (col c).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env r) := by
    intro c hc
    show (R.cpuTableP K).main ((r + 0) % K) c = (cpuTableC R.A R.row R.e R.n R.segRoots K).main ((r + 0) % K) c
    exact R.cpuColP_hi (by rcases hc with rfl | rfl | rfl <;> decide) (by rcases hc with rfl | rfl | rfl <;> decide)
  have hf : List.map (fun e => E.eval ((R.cpuTableP K).env r) e) [E.add (col CNT) one, col ROOT] =
      List.map (fun e => E.eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env r) e) [E.add (col CNT) one, col ROOT] := by
    simp only [List.map_cons, List.map_nil]
    show [(col CNT).eval _ + _, (col ROOT).eval _] = [(col CNT).eval _ + _, (col ROOT).eval _]
    rw [cv CNT (.inr (.inl rfl)), cv ROOT (.inr (.inr rfl))]
    rfl
  have hc : sRS.eval ((R.cpuTableP K).env r) = sRS.eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env r) :=
    cv RS (.inl rfl)
  simp only [hf, hc]

/-- **The CPU's segment table is the composed CPU's.** -/
theorem segsTableP (hd0 stk0 ctr0 n' nilA' J' root' : Nat) (K : Nat) :
    segsTableC R.segRoots (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) =
      segsTableC R.segRoots (cpuAirC hd0 stk0 ctr0 n' nilA') (cpuTableC R.A R.row R.e R.n R.segRoots K) := by
  unfold segsTableC
  simp only [R.cpuP_segs hd0 stk0 ctr0 n' nilA' J' root' K]

/-- **The CPU sends nothing on the blinding buses.** -/
theorem cpuP_blindZero (hd0 stk0 ctr0 n' nilA' J' root' : Nat) (K : Nat) {bus : String}
    (hb : bus = "blind_a" ∨ bus = "blind_b" ∨ bus = "blind_c") (v : List F) :
    tableSends (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) bus v = 0 := by
  apply sends_zero_of (Q := fun _ => False) _ id
  intro r hr I hI hbus hc
  have hr' : r < K := hr
  change I ∈ cpuIntersP2 at hI
  rw [cpuIntersP2_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  have z : ∀ c, c = BLA + 4 ∨ c = BLB + 4 ∨ c = P2SEL + 1 + 4 → (col c).eval ((R.cpuTableP K).env r) = 0 := by
    intro c hc
    rw [R.cpuP_col hr', R.cpuColP_hi (by rcases hc with rfl | rfl | rfl <;> decide)
      (by rcases hc with rfl | rfl | rfl <;> decide)]
    rcases hc with rfl | rfl | rfl
    · exact cpuColC_blind _ (.inl rfl)
    · exact cpuColC_blind _ (.inr rfl)
    · show cpuColC R.A R.row R.e R.n R.segRoots r (ROOT + 6) = 0
      unfold cpuColC
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals first
    | (rcases hb with rfl | rfl | rfl <;> exact absurd hbus (by decide))
    | (apply hc; show (col (P2SEL + 1 + 4)).eval _ = 0; exact z _ (.inr (.inr rfl)))
    | (apply hc; show -((col (BLA + 4)).eval _) = 0; rw [z _ (.inl rfl)]; exact neg_zero_eq)
    | (apply hc; show (col (BLB + 4)).eval _ = 0; exact z _ (.inr (.inl rfl)))

end P2Run

end Circuit
