import Ski.Circuit.CompDHonest
import Ski.Circuit.CompPBal

/-!
# The circuit with the `dec` jet: the honest CPU's messages

The honest CPU's `mem` messages are memory cells' tuples
(`DRun.cpuD_honest`): off the jet rows its reads are the composed CPU's
(`tagsD_off`, `cpuC_honest`); on a jet row the selectors are fixed
(`jetSubD`), and it reads the atom at the head, the stack cell, and looks up
the slots.  Its `segs` messages are the segments' rows (`cpuD_segsHonest`),
and it sends nothing on the blinding buses (`cpuD_blindZero`).  On the
jet's buses it sends, on each jet row, its subject's need on `decn` and
receives the result on `decx` (`cpuD_decn`, `cpuD_decx`).
-/

namespace Circuit

open B Air Compose CompM Mach

/-- `DECSEL` cleared. -/
def decOff (a : Atom) : E := if a = .main 0 DECSEL then c 0 else .atom a

/-- A jet row's selectors: the kinds and the restart clear, `DECSEL` set. -/
def jetSubD : Atom → E
  | .main 0 k => if SEL ≤ k ∧ k < SEL + NKINDS then c 0 else if k = RS then c 0
      else if k = DECSEL then c 1 else .atom (.main 0 k)
  | a => .atom a

theorem tagsD_off : ∀ j, j < 4 → ((tagsD.getD j zero).subst decOff).norm = (tagsC.getD j zero).norm := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

/-- On a jet row the reads' activities are `1, 1, 0, 0`. -/
theorem actsD_jet : ((acts.getD 0 zero).subst jetSubD).norm = (c 1).norm ∧
    ((acts.getD 1 zero).subst jetSubD).norm = (c 1).norm ∧ ((acts.getD 2 zero).subst jetSubD).norm = (c 0).norm ∧
    ((acts.getD 3 zero).subst jetSubD).norm = (c 0).norm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- On a jet row the reads' tags are an atom's and a stack cell's. -/
theorem tagsD_jet : ((tagsD.getD 0 zero).subst jetSubD).norm = (c 6).norm ∧
    ((tagsD.getD 1 zero).subst jetSubD).norm = (c 5).norm := by
  refine ⟨?_, ?_⟩ <;> decide

theorem selD_jet : (sApp.subst jetSubD).norm = (c 0).norm ∧ (sS.subst jetSubD).norm = (c 0).norm ∧
    (sDec.subst jetSubD).norm = (c 1).norm ∧ (sRS.subst jetSubD).norm = (c 0).norm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem cpuIntersD_now : cpuIntersD.all (fun I => I.count.onlyAtoms nowAtom &&
    I.fields.all (·.onlyAtoms nowAtom)) = true := by decide

namespace DRun

/-- On a jet row, the honest row's selectors are the jet's. -/
theorem jet_env {R : DRun} {K r : Nat} (hr : r < K) (hj : R.jetAt r = true) :
    ∀ a, (jetSubD a).eval ((R.cpuTableD K).env r) = (R.cpuTableD K).env r a := by
  obtain ⟨hrs, _, _⟩ := jetAt_spec hj
  have cv : ∀ c, (R.cpuTableD K).env r (.main 0 c) = R.cpuColD r c := fun c => by
    show (R.cpuTableD K).main ((r + 0) % K) c = _
    rw [Nat.add_zero, Nat.mod_eq_of_lt hr]; rfl
  have e1 : SEL = 3 := rfl
  have e2 : NKINDS = 14 := rfl
  have e3 : DECSEL = 134 := rfl
  have hsel : ∀ c, SEL ≤ c → c < SEL + NKINDS → (R.cpuTableD K).env r (.main 0 c) = 0 := fun c h1 h2 => by
    rw [cv]; unfold cpuColD
    have h2' := h2
    rw [e1, e2] at h2'
    rw [if_neg (by rw [e3]; omega), if_pos ⟨hj, h1, h2⟩]
  have hRS : (R.cpuTableD K).env r (.main 0 RS) = 0 := by
    rw [cv, R.colD_rs]; unfold rsI; rw [hrs]; rfl
  have hp1 : (R.cpuTableD K).env r (.main 0 DECSEL) = 1 := by
    rw [cv, R.colD_sel, hj]; rfl
  intro a
  cases a with
  | main o c =>
    cases o with
    | zero =>
      simp only [jetSubD]
      by_cases h1 : SEL ≤ c ∧ c < SEL + NKINDS
      · rw [if_pos h1, hsel c h1.1 h1.2]; rfl
      · rw [if_neg h1]
        by_cases h2 : c = RS
        · rw [if_pos h2, h2, hRS]; rfl
        · rw [if_neg h2]
          by_cases h3 : c = DECSEL
          · rw [if_pos h3, h3, hp1]; rfl
          · rw [if_neg h3]; rfl
    | succ o => rfl
  | _ => rfl

theorem jet_ev {R : DRun} {K r : Nat} (hr : r < K) (hj : R.jetAt r = true) (e e' : E)
    (hn : (e.subst jetSubD).norm = e'.norm) : e.eval ((R.cpuTableD K).env r) = e'.eval ((R.cpuTableD K).env r) := by
  rw [← E.eval_subst jetSubD _ (jet_env hr hj) e]; exact E.eval_eq_of_norm hn _

/-- On a jet row, the columns below the range checks but the kinds are the
    base CPU's. -/
theorem jet_base {R : DRun} {K r : Nat} (hr : r < K) (hj : R.jetAt r = true) (c : Nat) (hc : c < BITS)
    (hs : ¬ (SEL ≤ c ∧ c < SEL + NKINDS)) : (col c).eval ((R.cpuTableD K).env r) = cpuCol R.A (R.rowQ r) c := by
  rw [R.cpuD_col hr]
  have hb : BITS = 25 := rfl
  have hw : CPU_WIDTH = 121 := rfl
  have hd : DECSEL = 134 := rfl
  have hdr : DROOT = 140 := rfl
  rw [hb] at hc
  rw [R.colD_eq r (by rw [hd]; omega) hs (fun h => by have := h.1; rw [hb] at this; omega)
    (by rw [hdr]; omega)]
  unfold cpuColC
  rw [if_pos (by rw [hw]; omega), if_neg (fun h => hs ⟨h.1, h.2.1⟩)]
  rfl

theorem jet_fld {R : DRun} {K r : Nat} (hr : r < K) (hj : R.jetAt r = true) {i : Nat} (hi : i < 8) :
    (fld i).eval ((R.cpuTableD K).env r) =
      if i % 2 = 0 then ofN (fieldsAt R.A (R.rowQ r) (i / 2)).1 else ofN (fieldsAt R.A (R.rowQ r) (i / 2)).2 := by
  rw [fld, jet_base hr hj _ (by unfold BITS FLD; omega) (fun h => by unfold FLD SEL NKINDS at *; omega),
    cpuCol_fld _ _ hi]

variable {R : DRun} {m0 : Mach} {nilA : Nat} (hA : R.Honest m0 nilA) {K : Nat} (hK : R.e (R.n - 1) < K)
include hA hK

/-- **The honest CPU's `mem` messages are memory cells' tuples.** -/
theorem cpuD_honest (hd0 stk0 ctr0 n' nilA' J' : Nat) :
    HonestMem R.A (cpuAirDec hd0 stk0 ctr0 n' nilA' J') (R.cpuTableD K) := by
  intro r hr' I hI hbus hc
  have hr : r < K := hr'
  have hR := runC hA hK
  change I ∈ cpuIntersD at hI
  have hnow := List.all_eq_true.1 cpuIntersD_now I hI
  rw [Bool.and_eq_true, List.all_eq_true] at hnow
  cases hj : R.jetAt r with
  | false =>
    let ρC := (cpuTableC R.A R.row R.e R.n R.segRoots K).env r
    have cong : ∀ e : E, e.onlyAtoms nowAtom = true → e.eval ((R.cpuTableD K).env r) = e.eval ρC :=
      E.eval_congr (R.cpuD_env_plain hr hj)
    have h0 : ρC (.main 0 DECSEL) = 0 := by
      show (cpuTableC R.A R.row R.e R.n R.segRoots K).main ((r + 0) % K) DECSEL = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hr]
      exact R.cpuColC_hi (i := r) (Nat.le_refl _)
    have hσ : ∀ a, (decOff a).eval ρC = ρC a := by
      intro a
      unfold decOff
      split
      · next e => rw [e, h0]; rfl
      · rfl
    have off : ∀ e e' : E, e.onlyAtoms nowAtom = true → (e.subst decOff).norm = e'.norm →
        e.eval ((R.cpuTableD K).env r) = e'.eval ρC := fun e e' he hn => by
      rw [cong e he, ← E.eval_subst decOff ρC hσ e]
      exact E.eval_eq_of_norm hn ρC
    have key : ∀ I' ∈ cpuIntersC, I'.bus = "mem" → I'.count.eval ρC = I.count.eval ((R.cpuTableD K).env r) →
        I'.fields.map (fun e => e.eval ρC) = I.fields.map (fun e => e.eval ((R.cpuTableD K).env r)) →
        ∃ m, m < R.A.length ∧ I.fields.map (fun e => e.eval ((R.cpuTableD K).env r)) = tupleOf R.A m := by
      intro I' hI' hb hcnt hfl
      obtain ⟨m, hm, e⟩ := cpuC_honest hR r hr I' hI' hb (by rw [hcnt]; exact hc)
      exact ⟨m, hm, hfl ▸ e⟩
    have fl : ∀ e ∈ I.fields, e.eval ((R.cpuTableD K).env r) = e.eval ρC := fun e he => cong e (hnow.2 e he)
    rw [cpuIntersD_eq] at hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    have rd : ∀ j, j < 4 → I = readInterD j →
        ∃ m, m < R.A.length ∧ I.fields.map (fun e => e.eval ((R.cpuTableD K).env r)) = tupleOf R.A m := by
      intro j hj e
      subst e
      refine key (readInterC j) (by
          rw [cpuIntersC_eq]
          rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
            simp only [List.mem_cons, true_or, or_true]) rfl
        (cong _ hnow.1).symm ?_
      simp only [readInterC, readInterD, List.map_cons, List.map_nil]
      rw [fl (addrs.getD j zero) (by simp [readInterD]), fl (fld (2 * j)) (by simp [readInterD]),
        fl (fld (2 * j + 1)) (by simp [readInterD]),
        off (tagsD.getD j zero) (tagsC.getD j zero) (hnow.2 _ (by simp [readInterD])) (tagsD_off j hj)]
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact rd 0 (by decide) rfl
    · exact rd 1 (by decide) rfl
    · exact rd 2 (by decide) rfl
    · exact rd 3 (by decide) rfl
    all_goals first
      | exact absurd hbus (by decide)
      | (exfalso; apply hc
         show (col DECSEL).eval _ = 0
         rw [R.cpuD_col hr, R.cpuColD_plain hj]
         exact R.cpuColC_hi (i := r) (Nat.le_refl _))
      | (refine key _ (by rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true]) rfl
            (cong _ hnow.1).symm (List.map_congr_left (fun e he => (fl e he).symm)))
  | true =>
    obtain ⟨p, rest, hhd, hstk, _, hslots⟩ := R.jet_rowD hj
    let ρ := (R.cpuTableD K).env r
    have ev := jet_ev (R := R) hr hj
    have fl : ∀ i, i < 8 → (fld i).eval ((R.cpuTableD K).env r) =
        if i % 2 = 0 then ofN (fieldsAt R.A (R.rowQ r) (i / 2)).1 else ofN (fieldsAt R.A (R.rowQ r) (i / 2)).2 :=
      fun i hi => jet_fld hr hj hi
    have f0 : fieldsAt R.A (R.rowQ r) 0 = (R.J, 0) := by simp only [fieldsAt, addrAt, hhd]; rfl
    have f1 : fieldsAt R.A (R.rowQ r) 1 = (p, rest) := by simp only [fieldsAt, addrAt, hstk]; rfl
    obtain ⟨sl0, sl1, sl2⟩ : (R.A.take (R.rowQ r).ctr)[0]? = some .K ∧ (R.A.take (R.rowQ r).ctr)[1]? = some .I ∧
        (R.A.take (R.rowQ r).ctr)[2]? = some (.app 0 1) := by
      unfold DecJet.slotsOK at hslots
      simp only [Bool.and_eq_true, beq_iff_eq] at hslots
      exact ⟨hslots.1.1, hslots.1.2, hslots.2⟩
    obtain ⟨_, _, h2, h3⟩ := actsD_jet
    obtain ⟨t0, t1⟩ := tagsD_jet
    obtain ⟨zA, zS, _, _⟩ := selD_jet
    have hd : (col HD).eval ρ = ofN (R.rowQ r).hd := jet_base hr hj HD (by decide) (by decide)
    have st : (col STK).eval ρ = ofN (R.rowQ r).stk := jet_base hr hj STK (by decide) (by decide)
    have slot : ∀ a cell, (R.A.take (R.rowQ r).ctr)[a]? = some cell →
        ∃ m, m < R.A.length ∧ [ofN a, ofN (cellTag cell), ofN (cellFields cell).1, ofN (cellFields cell).2] =
          tupleOf R.A m := fun a cell h => by
      obtain ⟨ha, e⟩ := tupleOf_of_rd (rd_of_take h)
      exact ⟨a, ha, e.symm⟩
    rw [cpuIntersD_eq] at hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · obtain ⟨hm, e⟩ := tupleOf_of_rd hhd
      refine ⟨_, hm, ?_⟩
      simp only [readInterD, List.map_cons, List.map_nil, addrs, List.getD_cons_zero]
      rw [e, hd, ev _ _ t0, fl 0 (by decide), fl 1 (by decide), f0]; rfl
    · obtain ⟨hm, e⟩ := tupleOf_of_rd hstk
      refine ⟨_, hm, ?_⟩
      simp only [readInterD, List.map_cons, List.map_nil, addrs, List.getD_cons_zero, List.getD_cons_succ]
      rw [e, st, ev _ _ t1, fl 2 (by decide), fl 3 (by decide), f1]; rfl
    · exact absurd (ev _ _ h2) hc
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

/-- **The honest CPU's `segs` messages are the segments' rows.** -/
theorem cpuD_segsHonest (hd0 stk0 ctr0 n' nilA' J' : Nat) (hn : R.segRoots.length = R.n) :
    ∀ r, r < (R.cpuTableD K).h → ∀ I ∈ (cpuAirDec hd0 stk0 ctr0 n' nilA' J').inters, I.bus = "segs" →
      I.count.eval ((R.cpuTableD K).env r) ≠ 0 →
      ∃ q, q < R.segRoots.length ∧
        I.fields.map (fun c => c.eval ((R.cpuTableD K).env r)) = [ofN q, ofN (R.segRoots.getD q 0)] := by
  intro r hr' I hI hbus hc
  have hr : r < K := hr'
  have hR := runC hA hK
  change I ∈ cpuIntersD at hI
  rw [cpuIntersD_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first | exact absurd hbus (by decide) | skip
  have cv : ∀ c, c = RS ∨ c = CNT ∨ c = ROOT → (col c).eval ((R.cpuTableD K).env r) =
      (col c).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env r) := by
    intro c hc'
    show (R.cpuTableD K).main ((r + 0) % K) c = (cpuTableC R.A R.row R.e R.n R.segRoots K).main ((r + 0) % K) c
    rw [Nat.add_zero, Nat.mod_eq_of_lt hr]
    exact R.colD_eq r (by rcases hc' with rfl | rfl | rfl <;> decide) (by rcases hc' with rfl | rfl | rfl <;> decide)
      (by rcases hc' with rfl | rfl | rfl <;> decide) (by rcases hc' with rfl | rfl | rfl <;> decide)
  obtain ⟨q, hq, e⟩ := cpuC_segsHonest hR hn r hr ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩
    (by rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true]) rfl (by
      show (col RS).eval _ ≠ 0
      rw [← cv RS (.inl rfl)]; exact hc)
  refine ⟨q, hq, ?_⟩
  rw [← e]
  simp only [List.map_cons, List.map_nil]
  show [(col CNT).eval _ + _, (col ROOT).eval _] = [(col CNT).eval _ + _, (col ROOT).eval _]
  rw [cv CNT (.inr (.inl rfl)), cv ROOT (.inr (.inr rfl))]
  rfl

omit hA hK in
/-- **The CPU's blinding messages are quiet.** -/
theorem cpuD_blindQuiet (hd0 stk0 ctr0 n' nilA' J' : Nat) {r : Nat} (hr : r < K) {I : Inter}
    (hI : I ∈ (cpuAirDec hd0 stk0 ctr0 n' nilA' J').inters)
    (hb : I.bus = "blind_a" ∨ I.bus = "blind_b" ∨ I.bus = "blind_c") :
    I.count.eval ((R.cpuTableD K).env r) = 0 := by
  change I ∈ cpuIntersD at hI
  rw [cpuIntersD_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | (rcases hb with h | h | h <;> exact absurd h (by decide))
    | skip
  · show (col (DECSEL + 1 + 4)).eval _ = 0
    rw [R.cpuD_col hr, R.colD_block r (by decide) (by decide)]
  · show -((col (BLA + 4)).eval _) = 0
    rw [R.cpuD_col hr, R.colD_blind r (.inl rfl)]; exact neg_zero_eq
  · show (col (BLB + 4)).eval _ = 0
    rw [R.cpuD_col hr, R.colD_blind r (.inr rfl)]

end DRun

namespace DRun

-- ---------------------------------------------------------------------------
-- The CPU on the jet's buses
-- ---------------------------------------------------------------------------

/-- A jet row's need, sent on `decn`: the counter and the subject. -/
def decnT (R : DRun) (r : Nat) : List F := [ofN (R.rowQ r).ctr, ofN (fieldsAt R.A (R.rowQ r) 1).1, 0]

/-- A jet row's result, received on `decx`: the counter, the result's root
    and the next counter. -/
def decxT (R : DRun) (r : Nat) : List F := [ofN (R.rowQ r).ctr, ofN (R.rowQ (r + 1)).hd, ofN (R.rowQ (r + 1)).ctr]

/-- **What the honest CPU sends on a bus other than `mem` and `segs`**: per
    jet row, its need on `decn` and, received, its result on `decx`. -/
def jetSendsD (R : DRun) (K : Nat) (B : String) (v : List F) : F :=
  (List.range K).foldr (fun r acc => (if R.jetAt r then
    (if B = "decn" ∧ R.decnT r = v then 1 else 0) + (if B = "decx" ∧ R.decxT r = v then -1 else 0) else 0) + acc) 0

/-- **The honest CPU on the other buses** sends `jetSendsD`. -/
theorem cpuD_jetSends (R : DRun) (hd0 stk0 ctr0 n' nilA' J' K : Nat) {B : String} (hBm : B ≠ "mem")
    (hBs : B ≠ "segs") (v : List F) :
    tableSends (cpuAirDec hd0 stk0 ctr0 n' nilA' J') (R.cpuTableD K) B v = jetSendsD R K B v := by
  unfold tableSends jetSendsD
  apply foldr_range_congr
  intro r hr0
  have hr : r < K := hr0
  have cv := R.cpuD_col hr
  have zb1 : (col (DECSEL + 1 + 4)).eval ((R.cpuTableD K).env r) = 0 := by
    rw [cv, R.colD_block r (by decide) (by decide)]
  have zb2 : (col (BLA + 4)).eval ((R.cpuTableD K).env r) = 0 := by rw [cv, R.colD_blind r (.inl rfl)]
  have zb3 : (col (BLB + 4)).eval ((R.cpuTableD K).env r) = 0 := by rw [cv, R.colD_blind r (.inr rfl)]
  have hm : ("mem" = B) = False := propext ⟨fun h => hBm h.symm, False.elim⟩
  have hs : ("segs" = B) = False := propext ⟨fun h => hBs h.symm, False.elim⟩
  unfold rowSends
  show cpuIntersD.foldr _ 0 = _
  rw [cpuIntersD_eq]
  simp only [List.foldr_cons, List.foldr_nil, readInterD, blindMsg, hm, hs, false_and, ↓reduceIte, zero_add',
    add_zero', E.eval, zb1, zb2, zb3, neg_zero_eq, ite_self]
  have hsel : sDec.eval ((R.cpuTableD K).env r) = bF (R.jetAt r) := by
    show (col DECSEL).eval _ = _; rw [cv, R.colD_sel]
  rw [hsel]
  cases hj : R.jetAt r with
  | false =>
    simp only [bF, Bool.false_eq_true, ↓reduceIte, ite_self, neg_zero_eq, zero_add', add_zero']
  | true =>
    simp only [bF, ↓reduceIte]
    have e1 : List.map (fun e => E.eval ((R.cpuTableD K).env r) e) [col CTR, fld 2, c 0] = R.decnT r := by
      simp only [List.map_cons, List.map_nil, decnT]
      rw [cv, R.colD_ctr, jet_fld hr hj (i := 2) (by decide)]
      rfl
    have e2 : List.map (fun e => E.eval ((R.cpuTableD K).env r) e) [col CTR, col DROOT, col DCTR] = R.decxT r := by
      simp only [List.map_cons, List.map_nil, decxT]
      rw [cv, cv, cv, R.colD_ctr, R.colD_droot, R.colD_dctr, if_pos hj, if_pos hj]
    rw [e1, e2]
    simp only [@eq_comm _ "decn" B, @eq_comm _ "decx" B]

end DRun

end Circuit
