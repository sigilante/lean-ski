import Ski.Circuit.CompPTrace

/-!
# The honest tables of the circuit with the Poseidon2 jet balance

**`P2Run.balancedP`**: the honest tables of a run of the circuit with the
Poseidon2 jet balance with the public program, segment and level tables,
the level table's multiplicities those of the run's jet calls
(`idxPub (calls K)`).

- `mem`: every sender's lookups are memory cells' tuples
  (`HonestMem`): the CPU's (`cpuP_honest`), P2IN's slots
  (`pin_honest`, the slots literal), P2OUT's stack cells (`pout_honest`,
  the jet's row's writes), the program's and the witness table's.
- `segs`: the CPU sends as the composed CPU (`segsTableP`).
- `p2i`, `p2o`: each call's chain telescopes between the CPU's messages.
- `p2v`, `p2w`: each call's element values meet the Poseidon2 row's
  inputs and outputs.
- `p2idx`: each call looks up every level twice.
- the blinding buses: every flag is clear.
-/

namespace Circuit

open B Air Compose CompM Mach

-- ---------------------------------------------------------------------------
-- Tables of rows
-- ---------------------------------------------------------------------------

/-- **A table of rows whose memory messages are cells' tuples is honest.** -/
theorem honest_ofRows {M : List Cell} {A : AirD} (hA : NowOnly A) (hz : ZeroQuiet A) {rows : List (List F)}
    {H : Nat}
    (hrows : ∀ rw ∈ rows, ∀ I ∈ A.inters, I.bus = "mem" → I.count.eval (envOf rw) ≠ 0 →
      ∃ m, m < M.length ∧ I.fields.map (fun e => e.eval (envOf rw)) = tupleOf M m) :
    HonestMem M A ⟨H, ofRows rows, fun _ _ => 0⟩ := by
  intro q hq I hI hbus hc
  have ag : ∀ a, nowAtom a = true →
      (Table.env ⟨H, ofRows rows, fun _ _ => 0⟩ q) a = envOf (rows.getD q []) a := by
    intro a ha
    cases a with
    | main o c =>
      cases o with
      | zero => show ofRows rows ((q + 0) % H) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
      | succ o => simp [nowAtom] at ha
    | _ => simp [nowAtom] at ha
  have cong := E.eval_congr ag
  obtain ⟨hcA, hfA⟩ := hA I hI
  rw [cong _ hcA] at hc
  rcases Nat.lt_or_ge q rows.length with hl | hl
  · have hm : rows.getD q [] ∈ rows := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; exact List.getElem_mem hl
    obtain ⟨m, hm', e⟩ := hrows _ hm I hI hbus hc
    exact ⟨m, hm', by rw [List.map_congr_left (fun x hx => cong x (hfA x hx))]; exact e⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at hc
    exact absurd (hz I hI) hc

theorem bitsAt_get {H : List Cell} : ∀ {as : List Nat} {bs : List Bool}, P2Jet.bitsAt H as = some bs →
    ∀ t, t < as.length → P2Jet.boolAt H (as.getD t 0) = some (bs.getD t false)
  | [], _, _, t, ht => absurd ht (Nat.not_lt_zero _)
  | a :: as, bs, h, t, ht => by
    unfold P2Jet.bitsAt at h
    cases ha : P2Jet.boolAt H a with
    | none => rw [ha] at h; cases h
    | some b =>
      cases hr : P2Jet.bitsAt H as with
      | none => rw [ha, hr] at h; cases h
      | some bs' =>
        rw [ha, hr] at h
        cases h
        cases t with
        | zero => exact ha
        | succ t => exact bitsAt_get hr t (by simp only [List.length_cons] at ht; omega)

/-- **Consecutive stack cells, popped**: the `j`-th is at `s - j`, over the
    next below it, the last over the rest. -/
theorem consec_cells {H : List Cell} : ∀ (n s : Nat) {ps : List Nat} {r : Nat},
    P2Jet.consecFrom H s n = true → popN H (n + 1) s = some (ps, r) →
    ∀ j, j ≤ n → j ≤ s ∧ H[s - j]? = some (.cons (ps.getD j 0) (if j = n then r else s - j - 1))
  | 0, s, ps, r, _, hp, j, hj => by
    have hj0 : j = 0 := by omega
    subst hj0
    unfold popN at hp
    cases hc : H[s]? with
    | none => rw [hc] at hp; cases hp
    | some c =>
      rw [hc] at hp
      cases c with
      | cons x r' =>
        simp only [popN, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨Nat.zero_le _, by simp [hc]⟩
      | _ => cases hp
  | n + 1, s, ps, r, hcon, hp, j, hj => by
    unfold P2Jet.consecFrom at hcon
    cases hc : H[s]? with
    | none => rw [hc] at hcon; cases hcon
    | some c =>
      rw [hc] at hcon
      cases c with
      | cons x s' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hcon
        obtain ⟨hs', hrest⟩ := hcon
        unfold popN at hp
        rw [hc] at hp
        dsimp only at hp
        cases hq : popN H (n + 1) s' with
        | none => rw [hq] at hp; cases hp
        | some q =>
          obtain ⟨ps', r'⟩ := q
          rw [hq] at hp
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          cases j with
          | zero =>
            refine ⟨Nat.zero_le _, ?_⟩
            have e : s - 0 - 1 = s' := by omega
            simp only [Nat.sub_zero, hc, List.getD_cons_zero, if_neg (show ¬ (0 = n + 1) by omega)]
            rw [← e, Nat.sub_zero]
          | succ j =>
            obtain ⟨h1, h2⟩ := consec_cells n s' hrest hq j (by omega)
            refine ⟨by omega, ?_⟩
            rw [show s - (j + 1) = s' - j by omega, h2]
            simp only [List.getD_cons_succ]
            by_cases hjn : j = n
            · rw [if_pos hjn, if_pos (by omega)]
            · rw [if_neg hjn, if_neg (by omega), show s' - j - 1 = s - (j + 1) - 1 by omega]
      | _ => cases hcon

theorem ptrBits_getD : ∀ {ps : List Nat} {bs : List Bool}, P2Jet.ptrBits ps = some bs →
    ∀ j, j < ps.length → ps.getD j 0 = P2Jet.bitPtr (bs.getD j false)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | p :: ps, bs, h, j, hj => by
    unfold P2Jet.ptrBits at h
    cases hp : P2Jet.ptrBit p with
    | none => rw [hp] at h; cases h
    | some b =>
      cases hq : P2Jet.ptrBits ps with
      | none => rw [hp, hq] at h; cases h
      | some bs' =>
        rw [hp, hq] at h
        cases h
        cases j with
        | zero => exact P2Jet.ptrBit_eq hp
        | succ j => exact ptrBits_getD hq j (by simp only [List.length_cons] at hj; omega)

theorem pushR_get : ∀ (L : List Bool) (c prev m : Nat), m < L.length →
    (P2Jet.pushR c prev L)[m]? = some (.cons (P2Jet.bitPtr (L.getD m false)) (if m = 0 then prev else c + m - 1))
  | [], _, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | b :: L, c, prev, m, hm => by
    cases m with
    | zero => rfl
    | succ m =>
      show (P2Jet.pushR (c + 1) c L)[m]? = _
      rw [pushR_get L (c + 1) c m (by simp only [List.length_cons] at hm; omega)]
      congr 2
      cases m with
      | zero => show c = c + 1 - 1; omega
      | succ m => rw [if_neg (by omega), if_neg (by omega)]; omega

namespace P2Run

variable {R : P2Run} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCP R.A m0 [] [] R.J R.root R.segRoots nilA R.n R.e R.row) {K : Nat} (hK : R.e (R.n - 1) < K)

omit hA hK in
theorem pinRows_mem {K : Nat} {rw : List F} (h : rw ∈ R.pinRows K) :
    ∃ i, i < K ∧ R.jetAt i = true ∧ ∃ l, l < P2_BITS ∧
      rw = pinRow (R.rowQ i).ctr (R.jbits i) (R.jetSAt i) (R.js1 i) (R.jrest i) l := by
  obtain ⟨i, hi, hrw⟩ := List.mem_flatMap.1 h
  unfold pinRowsAt at hrw
  cases hj : R.jetAt i with
  | false => rw [hj] at hrw; nomatch hrw
  | true =>
    rw [hj] at hrw
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hrw
    exact ⟨i, List.mem_range.1 hi, hj, l, List.mem_range.1 hl, rfl⟩

omit hA hK in
theorem poutRows_mem {K : Nat} {rw : List F} (h : rw ∈ R.poutRows K) :
    ∃ i, i < K ∧ R.jetAt i = true ∧ ∃ l, l < P2_BITS ∧
      rw = poutRow (R.rowQ i).ctr (R.jrest i) (P2Jet.outBits (R.jbits i)) l := by
  obtain ⟨i, hi, hrw⟩ := List.mem_flatMap.1 h
  unfold poutRowsAt at hrw
  cases hj : R.jetAt i with
  | false => rw [hj] at hrw; nomatch hrw
  | true =>
    rw [hj] at hrw
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hrw
    exact ⟨i, List.mem_range.1 hi, hj, l, List.mem_range.1 hl, rfl⟩

omit hA hK in
theorem p2Rows_mem {K : Nat} {rw : List F} (h : rw ∈ R.p2Rows K) :
    ∃ i, i < K ∧ R.jetAt i = true ∧ rw = p2RowT (R.rowQ i).ctr (Poseidon2SKI.valsB (R.jbits i)) := by
  obtain ⟨i, hi, hrw⟩ := List.mem_flatMap.1 h
  unfold p2RowsAt at hrw
  cases hj : R.jetAt i with
  | false => rw [hj] at hrw; nomatch hrw
  | true =>
    rw [hj] at hrw
    exact ⟨i, List.mem_range.1 hi, hj, List.mem_singleton.1 hrw⟩

omit hA hK in
/-- A comb jet row's facts, in its own terms: the bits at the slots, the
    stack below. -/
theorem jetC_facts {i : Nat} (hj : R.jetCAt i = true) :
    P2Jet.bitsAt (R.A.take (R.rowQ i).ctr) P2Jet.slotAddrs = some (R.jbits i) ∧ (R.jbits i).length = 496 ∧
      wrs R.A (R.rowQ i).ctr (P2Jet.pushR (R.rowQ i).ctr (R.jrest i) (P2Jet.outBits (R.jbits i)).reverse) = true := by
  have hs : R.jetSAt i = false := by
    cases h : R.jetSAt i
    · rfl
    · exact (R.not_jetC_jetS hj h).elim
  obtain ⟨_, _, hp2⟩ := jetCAt_spec hj
  obtain ⟨_, k, s1, rest, bs, hstk, hs1, _, hbits, hbl, hw, _⟩ := p2Row_inv hp2
  have hjb : R.jbits i = bs := by unfold jbits; rw [hs, hbits]; rfl
  have hjr : R.jrest i = rest := by
    unfold jrest
    rw [hs]
    simp only [fieldsAt, addrAt, hstk, Option.getD_some, cellFields, hs1, Bool.false_eq_true, if_false]
  rw [hjb, hjr]
  exact ⟨hbits, hbl, hw⟩

omit hA hK in
/-- A stack jet row's facts: the 496 inputs in consecutive cells down from
    `s₁`, over the stack below, and the outputs' writes. -/
theorem jetS_facts {i : Nat} (hj : R.jetSAt i = true) :
    (∀ l, l < P2_BITS → (R.A.take (R.rowQ i).ctr)[spAt (R.js1 i) l]? =
        some (.cons (P2Jet.bitPtr ((R.jbits i).getD l false)) (spnAt (R.js1 i) (R.jrest i) l))) ∧
      (R.jbits i).length = 496 ∧
      wrs R.A (R.rowQ i).ctr (P2Jet.pushR (R.rowQ i).ctr (R.jrest i) (P2Jet.outBits (R.jbits i)).reverse) = true := by
  obtain ⟨_, _, hp2⟩ := jetSAt_spec hj
  obtain ⟨_, k, ps, rest, bs, hpop, _, hrun, hbits, hbl, hw, _⟩ := p2RowS_inv hp2
  have hpop' := hpop
  unfold popN at hpop'
  cases hc : (R.A.take (R.rowQ i).ctr)[(R.rowQ i).stk]? with
  | none => rw [hc] at hpop'; cases hpop'
  | some c =>
    rw [hc] at hpop'
    cases c with
    | cons x s1 =>
      dsimp only at hpop'
      cases hq : popN (R.A.take (R.rowQ i).ctr) 496 s1 with
      | none => rw [hq] at hpop'; cases hpop'
      | some q =>
        obtain ⟨ps', r'⟩ := q
        rw [hq] at hpop'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at hpop'
        obtain ⟨⟨_, hps⟩, hr⟩ := hpop'
        subst hps; subst hr
        have hcon : P2Jet.consecFrom (R.A.take (R.rowQ i).ctr) s1 495 = true := by
          unfold P2Jet.stackRun at hrun; rw [hc] at hrun; exact hrun
        have hstk : rd R.A (R.rowQ i).ctr (R.rowQ i).stk = some (.cons x s1) := rd_of_take hc
        have hjs : R.js1 i = s1 := by
          unfold js1; simp only [fieldsAt, addrAt, hstk, Option.getD_some, cellFields]
        have hjr : R.jrest i = r' := by
          unfold jrest; rw [if_pos hj, hpop]; rfl
        have hjb : R.jbits i = bs := by
          unfold jbits; rw [if_pos hj, hpop]
          simp only [Option.getD_some, List.tail_cons, hbits]
        have hpl : ps'.length = 496 := popN_len hq
        rw [hjs, hjr, hjb]
        refine ⟨fun l hl => ?_, hbl, hw⟩
        obtain ⟨_, hcell⟩ := consec_cells 495 s1 hcon hq l (by unfold P2_BITS at hl; omega)
        unfold spAt spnAt
        rw [hcell, ptrBits_getD hbits l (by rw [hpl]; exact hl)]
        by_cases h : l = 495
        · rw [if_pos h, if_pos (by unfold P2_BITS; omega)]
        · rw [if_neg h, if_neg (by unfold P2_BITS; omega)]
    | _ => cases hpop'

omit hA hK in
/-- A jet row's facts, either mode: the bits' length and the outputs'
    writes. -/
theorem jet_facts {i : Nat} (hj : R.jetAt i = true) :
    (R.jbits i).length = 496 ∧
      wrs R.A (R.rowQ i).ctr (P2Jet.pushR (R.rowQ i).ctr (R.jrest i) (P2Jet.outBits (R.jbits i)).reverse) = true := by
  unfold jetAt at hj
  rcases Bool.or_eq_true _ _ ▸ hj with hc | hs
  · exact (R.jetC_facts hc).2
  · exact (R.jetS_facts hs).2

end P2Run


namespace P2Run

variable {R : P2Run}

theorem slot_get {l : Nat} (hl : l < 496) : P2Jet.slotAddrs.getD l 0 = 3 + l := by
  rw [List.getD_eq_getElem?_getD, P2Jet.slotAddrs, List.getElem?_range' hl, Option.getD_some, Nat.one_mul]

/-- **P2IN's lookups are memory cells'**: on the comb the slots, literal; on
    the stack the inputs' cells. -/
theorem pin_honest {K H : Nat}
    (hbits : ∀ i, i < 496 → R.A.getD (3 + i) .nil = .K ∨ R.A.getD (3 + i) .nil = .app 0 1) :
    HonestMem R.A p2inAir (R.pinTable K H) := by
  refine honest_ofRows pin_nowOnly pin_quiet (fun rw hrw I hI hbus _ => ?_)
  obtain ⟨i, _, hj, l, hl, rfl⟩ := pinRows_mem hrw
  simp only [p2inAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd hbus (by decide) | skip
  simp only [List.map_cons, List.map_nil, E.eval, B.col, envOf_get]
  rw [pinRow_mem]
  cases hs : R.jetSAt i
  · -- on the comb: the slot's cell
    have hc : R.jetCAt i = true := by
      unfold jetAt at hj; rw [hs, Bool.or_false] at hj; exact hj
    obtain ⟨hbits', _, _⟩ := R.jetC_facts hc
    have hb := bitsAt_get hbits' l (by rw [P2Jet.slotAddrs, List.length_range']; exact hl)
    rw [slot_get hl] at hb
    obtain ⟨cell, hcell, hce⟩ : ∃ cell, R.A[3 + l]? = some cell ∧
        cell = if (R.jbits i).getD l false then .K else .app 0 1 := by
      rcases P2Jet.boolAt_cases hb with ⟨hb1, hk⟩ | ⟨hb0, f, x, hfx, _, _⟩
      · rw [List.getElem?_take] at hk
        split at hk
        · exact ⟨_, hk, by rw [hb1]; rfl⟩
        · cases hk
      · rw [List.getElem?_take] at hfx
        split at hfx
        · refine ⟨_, hfx, ?_⟩
          rw [hb0]
          have hg : R.A.getD (3 + l) .nil = .app f x := by rw [List.getD_eq_getElem?_getD, hfx]; rfl
          rcases hbits l hl with h | h
          · rw [hg] at h; cases h
          · rw [hg] at h; rw [h]; rfl
        · cases hfx
    have hlen : 3 + l < R.A.length := (List.getElem?_eq_some_iff.1 hcell).1
    refine ⟨3 + l, hlen, ?_⟩
    unfold tupleOf
    rw [List.getD_eq_getElem?_getD, hcell, hce, Nat.add_comm]
    unfold pinMem
    simp only [Bool.false_eq_true, if_false]
    cases (R.jbits i).getD l false <;> rfl
  · -- on the stack: the input's cell
    obtain ⟨hcells, _, _⟩ := R.jetS_facts hs
    have hcell := hcells l hl
    rw [List.getElem?_take] at hcell
    split at hcell
    · have hlen : spAt (R.js1 i) l < R.A.length := (List.getElem?_eq_some_iff.1 hcell).1
      refine ⟨spAt (R.js1 i) l, hlen, ?_⟩
      unfold tupleOf
      rw [List.getD_eq_getElem?_getD, hcell]
      unfold pinMem
      simp only [if_true]
      cases (R.jbits i).getD l false <;> rfl
    · cases hcell

/-- **P2OUT's lookups are the stack cells the jet wrote.** -/
theorem pout_honest {K H : Nat} : HonestMem R.A p2outAir (R.poutTable K H) := by
  refine honest_ofRows pout_nowOnly pout_quiet (fun rw hrw I hI hbus _ => ?_)
  obtain ⟨i, _, hj, l, hl, rfl⟩ := poutRows_mem hrw
  have hl : l < 496 := hl
  obtain ⟨hbl, hw⟩ := jet_facts hj
  generalize hc : (R.rowQ i).ctr = c at hw ⊢
  generalize hr : R.jrest i = rest at hw ⊢
  generalize hob : P2Jet.outBits (R.jbits i) = ob at hw ⊢
  have hobl : ob.length = 496 := by rw [← hob]; exact outBits_length _ hbl
  have hm : 495 - l < (P2Jet.pushR c rest ob.reverse).length := by
    rw [P2Jet.pushR_length, List.length_reverse, hobl]; omega
  have hcell := wrs_get hw (495 - l) hm
  have hp := pushR_get ob.reverse c rest (495 - l) (by rw [List.length_reverse, hobl]; omega)
  rw [List.getElem?_eq_getElem hm, Option.some.injEq] at hp
  rw [hp] at hcell
  have hrev : ob.reverse.getD (495 - l) false = ob.getD l false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [hobl]; omega), hobl,
      show 496 - 1 - (495 - l) = l by omega]
  rw [hrev] at hcell
  have ha : c + (495 - l) = c + (P2_BITS - 1) - l := by unfold P2_BITS; omega
  rw [ha] at hcell
  have hlen : c + (P2_BITS - 1) - l < R.A.length := (List.getElem?_eq_some_iff.1 hcell).1
  simp only [p2outAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd hbus (by decide) | skip
  refine ⟨_, hlen, ?_⟩
  unfold tupleOf
  rw [List.getD_eq_getElem?_getD, hcell]
  simp only [List.map_cons, List.map_nil, E.eval, B.col, B.c, envOf_get]
  show [ofN (c + (P2_BITS - 1) - l), ofN 5, ofN (P2Jet.bitPtr (ob.getD l false)),
    ofN (if l = P2_BITS - 1 then rest else c + (P2_BITS - 1) - l - 1)] = _
  have hprev : (if 495 - l = 0 then rest else c + (P2_BITS - 1) - l - 1) =
      (if l = P2_BITS - 1 then rest else c + (P2_BITS - 1) - l - 1) := by
    by_cases h : l = 495
    · rw [if_pos (by omega), if_pos (by unfold P2_BITS; omega)]
    · rw [if_neg (by omega), if_neg (by unfold P2_BITS; omega)]
  rw [← hprev]
  rfl

end P2Run


-- ---------------------------------------------------------------------------
-- The witness table on the circuit's rows
-- ---------------------------------------------------------------------------

theorem witRowsP_pad {N W q : Nat} (hq : N + W ≤ q) (hl : q < (witRowsP N W).length) :
    (witRowsP N W).getD q [] = [ofN 0, ofN 0, ofN 0] := by
  unfold witRowsP at *
  simp only [List.length_append, List.length_map, List.length_range, List.length_replicate] at hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
  simp only [List.length_append, List.length_map, List.length_range]
  rw [if_pos (by omega)]
  rfl

section

variable {A : List Cell} {N W : Nat}
  (hbits : ∀ i, i < N → A.getD (3 + i) .nil = .K ∨ A.getD (3 + i) .nil = .app 0 1)
  (hreg : ∀ i, i < W → Wit.cellOK (3 + N + i) (A.getD (3 + N + i) .nil) = true)
  (hlen : 3 + N + W ≤ A.length)

include hbits hreg hlen in
/-- **The witness table's lookups are its cells'**, on the circuit's rows. -/
theorem witTP_honest : HonestMem A (witAirP N W) (witTableP A N W) := by
  intro q hq I hI hbus hc
  have pv : ∀ j, (prec j).eval ((witTableP A N W).env q) = ((witRowsP N W).getD q []).getD j 0 := fun j => by
    show (witTableP A N W).pre ((q + 0) % _) j = _
    rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
  have ev : ∀ c, (col c).eval ((witTableP A N W).env q) = witColG 3 A N W q c := fun c => by
    show (witTableP A N W).main ((q + 0) % _) c = _
    rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
  simp only [witAirP, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl
  · rcases Nat.lt_or_ge q (N + W) with hact | hact
    · obtain ⟨hok, _⟩ := wit_cell (a0 := 3) (fun _ => by decide) hbits hreg hact
      obtain ⟨vf, va, vb, _, _⟩ := witCol_active (a0 := 3) (A := A) hact
      have hpre := witRowsP_get (N := N) (W := W) hact
      refine ⟨3 + q, by omega, ?_⟩
      simp only [List.map_cons, List.map_nil, E.eval, pv, hpre, ev, B.c, vf 1 (by decide), vf 2 (by decide),
        vf 3 (by decide), va, vb]
      unfold tupleOf
      generalize A.getD (3 + q) .nil = cell at hok ⊢
      rcases cellOK_cases hok with rfl | rfl | rfl | ⟨x, y, rfl, _, _⟩
      · rfl
      · rfl
      · rfl
      · rfl
    · exfalso; apply hc
      show (prec 1).eval _ = 0
      rw [pv, witRowsP_pad hact hq]; rfl
  · exact absurd hbus (by decide)

end

theorem witTP_blindZero {A : List Cell} {N W : Nat} : ∀ r, r < (witTableP A N W).h →
    ∀ I ∈ (witAirP N W).inters, I.bus ≠ "mem" → I.count.eval ((witTableP A N W).env r) = 0 := by
  intro q hq I hI hb
  simp only [witAirP, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl
  · exact absurd rfl hb
  · show (witTableP A N W).main ((q + 0) % _) (WT_BLIND + 4) = 0
    rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
    show witColG 3 A N W q (WT_BLIND + 4) = 0
    unfold witColG
    split
    · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    · rfl


-- ---------------------------------------------------------------------------
-- The CPU's chain messages
-- ---------------------------------------------------------------------------

/-- A row's sends on a bus are those of the interactions on the bus. -/
theorem foldr_sends_filter (ρ : Atom → F) (bus : String) (v : List F) : ∀ L : List Inter,
    L.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ) = v then I.count.eval ρ else 0) + acc) 0 =
    (L.filter (fun I => decide (I.bus = bus))).foldr
      (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ) = v then I.count.eval ρ else 0) + acc) 0
  | [] => rfl
  | I :: L => by
    rw [List.filter_cons]
    by_cases h : I.bus = bus
    · rw [if_pos (decide_eq_true h), List.foldr_cons, List.foldr_cons, foldr_sends_filter ρ bus v L]
    · rw [if_neg (by rw [decide_eq_false h]; exact Bool.false_ne_true), List.foldr_cons, if_neg (fun h' => h h'.1),
        zero_add', foldr_sends_filter ρ bus v L]

theorem cpuIntersP2_p2i : cpuIntersP2.filter (fun I => decide (I.bus = "p2i")) =
    [⟨"p2i", 1, sP2, [col CTR, c 0, c 0, col P2MODE, col P2SP0]⟩,
     ⟨"p2i", 1, .neg sP2, [col CTR, c P2_BITS, c 0, col P2MODE, col P2REST]⟩] := rfl

theorem cpuIntersP2_p2o : cpuIntersP2.filter (fun I => decide (I.bus = "p2o")) =
    [⟨"p2o", 1, sP2, [col CTR, c 0, col P2REST, c 0, c 0, c 1]⟩,
     ⟨"p2o", 1, .neg sP2, [col CTR, c P2_BITS, col P2REST, c 0, c 0, c 1]⟩] := rfl

namespace P2Run

variable (R : P2Run)

theorem cpuP_ctr {K i : Nat} (hi : i < K) : (col CTR).eval ((R.cpuTableP K).env i) = ofN (R.rowQ i).ctr := by
  rw [R.cpuP_col hi]
  unfold cpuColP
  rw [if_neg (by decide), if_neg (fun h => by have := h.2.1; revert this; decide),
    if_neg (fun h => by have := h.2.1; revert this; decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), cpuColC_reg _ (.inr (.inr rfl))]
  rfl

theorem cpuP_mode {K i : Nat} (hi : i < K) : (col P2MODE).eval ((R.cpuTableP K).env i) = bF (R.jetSAt i) := by
  rw [R.cpuP_col hi]
  unfold cpuColP
  rw [if_neg (by decide), if_neg (fun h => by have := h.2.2; revert this; decide),
    if_neg (fun h => by have := h.2.2; revert this; decide), if_pos rfl]

theorem cpuP_rest {K i : Nat} (hi : i < K) :
    (col P2REST).eval ((R.cpuTableP K).env i) = if R.jetAt i then ofN (R.jrest i) else 0 := by
  rw [R.cpuP_col hi]
  unfold cpuColP
  rw [if_neg (by decide), if_neg (fun h => by have := h.2.2; revert this; decide),
    if_neg (fun h => by have := h.2.2; revert this; decide), if_neg (by decide), if_pos rfl]

theorem cpuP_sp0 {K i : Nat} (hi : i < K) :
    (col P2SP0).eval ((R.cpuTableP K).env i) =
      if R.jetSAt i then ofN (R.js1 i) else if R.jetAt i then ofN (R.jrest i) else 0 := by
  rw [R.cpuP_col hi]
  unfold cpuColP
  rw [if_neg (by decide), if_neg (fun h => by have := h.2.2; revert this; decide),
    if_neg (fun h => by have := h.2.2; revert this; decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]

theorem cpuP_sel {K i : Nat} (hi : i < K) : sP2.eval ((R.cpuTableP K).env i) = bF (R.jetAt i) := by
  show (col P2SEL).eval _ = _
  rw [R.cpuP_col hi]
  unfold cpuColP; rw [if_pos rfl]

/-- **The CPU's `p2i` messages**: a jet row starts its call's input chain
    and ends it. -/
theorem cpuP_p2i (hd0 stk0 ctr0 n' nilA' J' root' : Nat) {K i : Nat} (hi : i < K) (v : List F) :
    rowSends (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) "p2i" v i =
      if R.jetAt i then
        ind ([ofN (R.rowQ i).ctr, 0, 0, bF (R.jetSAt i), ofN (if R.jetSAt i then R.js1 i else R.jrest i)] = v) -
          ind ([ofN (R.rowQ i).ctr, ofN P2_BITS, 0, bF (R.jetSAt i), ofN (R.jrest i)] = v)
      else 0 := by
  unfold rowSends
  show cpuIntersP2.foldr _ 0 = _
  rw [foldr_sends_filter, cpuIntersP2_p2i]
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.c, true_and, add_zero']
  rw [show (col CTR).eval ((R.cpuTableP K).env i) = _ from R.cpuP_ctr hi]
  rw [show (col P2MODE).eval ((R.cpuTableP K).env i) = _ from R.cpuP_mode hi,
    show (col P2SP0).eval ((R.cpuTableP K).env i) = _ from R.cpuP_sp0 hi,
    show (col P2REST).eval ((R.cpuTableP K).env i) = _ from R.cpuP_rest hi]
  rw [R.cpuP_sel hi]
  have hsp : (if R.jetSAt i then ofN (R.js1 i) else if R.jetAt i then ofN (R.jrest i) else (0 : F)) =
      if R.jetAt i then ofN (if R.jetSAt i then R.js1 i else R.jrest i) else
        (if R.jetSAt i then ofN (R.js1 i) else 0) := by
    cases h1 : R.jetSAt i <;> cases h2 : R.jetAt i <;> rfl
  rw [hsp]
  cases R.jetAt i
  · show (if _ then (0 : F) else 0) + (if _ then -(0 : F) else 0) = 0
    rw [ite_zero _ _ rfl, ite_neg_zero _ _ rfl, zero_add']
  · show (if _ then (1 : F) else 0) + (if _ then -(1 : F) else 0) = _
    rw [ite_one _ 1 rfl, ite_neg_one _ 1 rfl, sub_eq_add_neg']
    rfl

/-- **The CPU's `p2o` messages.** -/
theorem cpuP_p2o (hd0 stk0 ctr0 n' nilA' J' root' : Nat) {K i : Nat} (hi : i < K) (v : List F) :
    rowSends (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) "p2o" v i =
      if R.jetAt i then ind ([ofN (R.rowQ i).ctr, 0, ofN (R.jrest i), 0, 0, 1] = v) -
        ind ([ofN (R.rowQ i).ctr, ofN P2_BITS, ofN (R.jrest i), 0, 0, 1] = v) else 0 := by
  unfold rowSends
  show cpuIntersP2.foldr _ 0 = _
  rw [foldr_sends_filter, cpuIntersP2_p2o]
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.c, true_and, add_zero']
  rw [show (col CTR).eval ((R.cpuTableP K).env i) = _ from R.cpuP_ctr hi]
  rw [show (col P2REST).eval ((R.cpuTableP K).env i) = _ from R.cpuP_rest hi]
  rw [R.cpuP_sel hi]
  cases R.jetAt i
  · show (if _ then (0 : F) else 0) + (if _ then -(0 : F) else 0) = 0
    rw [ite_zero _ _ rfl, ite_neg_zero _ _ rfl, zero_add']
  · show (if _ then (1 : F) else 0) + (if _ then -(1 : F) else 0) = _
    rw [ite_one _ 1 rfl, ite_neg_one _ 1 rfl, sub_eq_add_neg']
    rfl

end P2Run


-- ---------------------------------------------------------------------------
-- The jet tables' sends
-- ---------------------------------------------------------------------------

/-- **An output element's bits read back as the permutation's output.** -/
theorem chunk_out (bs : List Bool) (hbl : bs.length = 496) {e : Nat} (he : e < 16) :
    BitArith.val (Poseidon2SKI.chunk (P2Jet.outBits bs) e) =
      (Poseidon2.permute (Poseidon2SKI.valsB bs)).getD e 0 := by
  have hs : (Poseidon2SKI.valsB bs).length = 16 := Poseidon2SKI.valsB_length bs
  have hY := Poseidon2SKI.permute_len _ hs
  have hc : Poseidon2SKI.chunk (P2Jet.outBits bs) e =
      BitArith.bitsOf 31 ((Poseidon2.permute (Poseidon2SKI.valsB bs)).getD e 0) := by
    unfold Poseidon2SKI.chunk P2Jet.outBits
    rw [← Poseidon2SKI.range_map_getD false (BitArith.bitsOf 31 ((Poseidon2.permute (Poseidon2SKI.valsB bs)).getD e 0)),
      Poseidon2SKI.bitsOf_length]
    apply List.map_congr_left
    intro j hj
    exact flatMap_bits_getD _ e j (by rw [hY]; exact he) (List.mem_range.1 hj)
  rw [hc, BitArith.val_bitsOf]
  have hlt : (Poseidon2.permute (Poseidon2SKI.valsB bs)).getD e 0 < Poseidon2.p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hY]; exact he)]
    exact P2Air.permute_lt _ hs _ (List.getElem_mem _)
  exact Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide))

namespace P2Run

variable (R : P2Run)

theorem pin_wide {K H : Nat} : Wide p2inAir (R.pinTable K H) := by
  intro r _ c hc
  show ofRows (R.pinRows K) r c = 0
  refine ofRows_wide (w := 22) (fun x hx => ?_) r hc
  obtain ⟨i, _, _, l, _, rfl⟩ := R.pinRows_mem hx
  exact Nat.le_refl _

theorem pout_wide {K H : Nat} : Wide p2outAir (R.poutTable K H) := by
  intro r _ c hc
  show ofRows (R.poutRows K) r c = 0
  refine ofRows_wide (w := 23) (fun x hx => ?_) r hc
  obtain ⟨i, _, _, l, _, rfl⟩ := R.poutRows_mem hx
  exact Nat.le_refl _

theorem p2_wide {K H : Nat} : Wide P2Air.p2Air (R.p2Table K H) := by
  intro r _ c hc
  show ofRows (R.p2Rows K ++ List.replicate (H - (R.p2Rows K).length) p2Pad) r c = 0
  refine ofRows_wide (w := 652) (fun x hx => ?_) r hc
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨i, _, _, rfl⟩ := R.p2Rows_mem hx
    rw [p2RowT_len _ _ (Poseidon2SKI.valsB_length _)]
    exact Nat.le_refl _
  · rw [List.eq_of_mem_replicate hx, p2Pad_len]
    exact Nat.le_refl _

/-- P2IN sends, call by call. -/
theorem pin_sendsT {K H : Nat} (hH : (R.pinRows K).length ≤ H) (bus : String) (v : List F) :
    tableSends p2inAirB (R.pinTable K H) bus v = (List.range K).foldr (fun i acc =>
      (if R.jetAt i then (((List.range P2_BITS).map (pinRow (R.rowQ i).ctr (R.jbits i) (R.jetSAt i) (R.js1 i)
        (R.jrest i))).map (rowSendsV p2inAir bus v)).foldr (· + ·) 0 else 0) + acc) 0 := by
  rw [show tableSends p2inAirB (R.pinTable K H) bus v = tableSends p2inAir (R.pinTable K H) bus v from
      sends_withBlocks_quiet R.pin_wide bus v, show R.pinTable K H = ⟨H, ofRows (R.pinRows K), fun _ _ => 0⟩ from rfl,
    sends_rows pin_nowOnly pin_quiet hH, pinRows, foldr_flatMap]
  refine foldr_range_congr K (fun i _ => ?_)
  unfold pinRowsAt
  cases R.jetAt i <;> rfl

/-- P2OUT sends, call by call. -/
theorem pout_sendsT {K H : Nat} (hH : (R.poutRows K).length ≤ H) (bus : String) (v : List F) :
    tableSends p2outAirB (R.poutTable K H) bus v = (List.range K).foldr (fun i acc =>
      (if R.jetAt i then (((List.range P2_BITS).map (poutRow (R.rowQ i).ctr (R.jrest i)
        (P2Jet.outBits (R.jbits i)))).map (rowSendsV p2outAir bus v)).foldr (· + ·) 0 else 0) + acc) 0 := by
  rw [show tableSends p2outAirB (R.poutTable K H) bus v = tableSends p2outAir (R.poutTable K H) bus v from
      sends_withBlocks_quiet R.pout_wide bus v, show R.poutTable K H = ⟨H, ofRows (R.poutRows K), fun _ _ => 0⟩ from rfl,
    sends_rows pout_nowOnly pout_quiet hH, poutRows, foldr_flatMap]
  refine foldr_range_congr K (fun i _ => ?_)
  unfold poutRowsAt
  cases R.jetAt i <;> rfl

/-- The Poseidon2 table sends, call by call. -/
theorem p2_sendsT {K H : Nat} (hH : (R.p2Rows K).length ≤ H) (bus : String) (v : List F) :
    tableSends p2AirB (R.p2Table K H) bus v = (List.range K).foldr (fun i acc =>
      (if R.jetAt i then rowSendsV P2Air.p2Air bus v (p2RowT (R.rowQ i).ctr (Poseidon2SKI.valsB (R.jbits i)))
        else 0) + acc) 0 := by
  have hH' : (R.p2Rows K ++ List.replicate (H - (R.p2Rows K).length) p2Pad).length ≤ H := by
    rw [List.length_append, List.length_replicate]; omega
  have hz : ((List.replicate (H - (R.p2Rows K).length) p2Pad).map (rowSendsV P2Air.p2Air bus v)).foldr
      (· + ·) (0 : F) = 0 := by
    generalize H - (R.p2Rows K).length = m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.replicate_succ, List.map_cons, List.foldr_cons, ih, p2Pad_sends]; exact add_zero' 0
  rw [show tableSends p2AirB (R.p2Table K H) bus v = tableSends P2Air.p2Air (R.p2Table K H) bus v from
      sends_withBlocks_quiet R.p2_wide bus v,
    show R.p2Table K H = ⟨H, ofRows (R.p2Rows K ++ List.replicate (H - (R.p2Rows K).length) p2Pad),
      fun _ _ => 0⟩ from rfl,
    sends_rows p2_nowOnly p2_quiet hH', List.map_append, List.foldr_append, hz, p2Rows, foldr_flatMap]
  refine foldr_range_congr K (fun i _ => ?_)
  unfold p2RowsAt
  cases R.jetAt i
  · rfl
  · show rowSendsV P2Air.p2Air bus v _ + 0 = _
    rw [add_zero']; rfl

/-- The CPU sends, row by row. -/
theorem cpu_sendsT (hd0 stk0 ctr0 n' nilA' J' root' K : Nat) (bus : String) (v : List F) :
    tableSends (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) bus v =
      (List.range K).foldr (fun i acc => rowSends (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) bus v i
        + acc) 0 := rfl

theorem cancel4 (a b : F) : (a - b) + (b - a) = 0 :=
  E.eval_eq_of_norm (e := .add (.sub (.atom (.main 0 0)) (.atom (.main 0 1))) (.sub (.atom (.main 0 1)) (.atom (.main 0 0))))
    (e' := .const 0) (by decide) (at4 a b 0 0)

/-- **`p2i` balances**: each call's input chain telescopes between the CPU's
    messages. -/
theorem bal_p2i (hd0 stk0 ctr0 n' nilA' J' root' : Nat) {K H : Nat} (hH : (R.pinRows K).length ≤ H) (v : List F) :
    tableSends (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) "p2i" v +
      tableSends p2inAirB (R.pinTable K H) "p2i" v = 0 := by
  rw [cpu_sendsT, R.pin_sendsT hH, fold_add2]
  apply foldr_zero_all
  intro i hi
  rw [R.cpuP_p2i hd0 stk0 ctr0 n' nilA' J' root' (List.mem_range.1 hi), pin_p2i_call]
  cases R.jetAt i
  · exact zero_add' 0
  · exact cancel4 _ _

/-- **`p2o` balances.** -/
theorem bal_p2o (hd0 stk0 ctr0 n' nilA' J' root' : Nat) {K H : Nat} (hH : (R.poutRows K).length ≤ H) (v : List F) :
    tableSends (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root') (R.cpuTableP K) "p2o" v +
      tableSends p2outAirB (R.poutTable K H) "p2o" v = 0 := by
  rw [cpu_sendsT, R.pout_sendsT hH, fold_add2]
  apply foldr_zero_all
  intro i hi
  rw [R.cpuP_p2o hd0 stk0 ctr0 n' nilA' J' root' (List.mem_range.1 hi), pout_p2o_call]
  cases R.jetAt i
  · exact zero_add' 0
  · exact cancel4 _ _

theorem sum_neg (f : Nat → F) (k : Nat) :
    (List.range k).foldr (fun e acc => f e + acc) 0 + (List.range k).foldr (fun e acc => -f e + acc) 0 = 0 := by
  rw [fold_add2]
  apply foldr_zero_all
  intro e _
  rw [add_comm']; exact neg_add_cancel' _

/-- **`p2v` balances**: each call's input elements are the Poseidon2 row's
    inputs. -/
theorem bal_p2v {K HI HP : Nat} (hI : (R.pinRows K).length ≤ HI) (hP : (R.p2Rows K).length ≤ HP) (v : List F) :
    tableSends p2inAirB (R.pinTable K HI) "p2v" v + tableSends p2AirB (R.p2Table K HP) "p2v" v = 0 := by
  rw [R.pin_sendsT hI, R.p2_sendsT hP, fold_add2]
  apply foldr_zero_all
  intro i _
  cases hj : R.jetAt i
  · exact zero_add' 0
  · show _ + _ = (0 : F)
    simp only [if_true]
    rw [pin_p2v_call, p2_sends_v _ _ (Poseidon2SKI.valsB_length _)]
    have hv : ∀ e, e < 16 → (Poseidon2SKI.valsB (R.jbits i)).getD e 0 =
        BitArith.val (Poseidon2SKI.chunk (R.jbits i) e) :=
      fun e he => getD_map_range _ _ he
    have h2 : (List.range 16).foldr (fun e acc =>
        -ind ([ofN (R.rowQ i).ctr, ofN e, ofN ((Poseidon2SKI.valsB (R.jbits i)).getD e 0)] = v) + acc) 0 =
        (List.range 16).foldr (fun e acc =>
        -ind ([ofN (R.rowQ i).ctr, ofN e, ofN (BitArith.val (Poseidon2SKI.chunk (R.jbits i) e))] = v) + acc) 0 :=
      foldr_range_congr 16 (fun e he => by rw [hv e he])
    rw [h2]
    exact sum_neg _ 16

/-- **`p2w` balances**: each call's output elements are the Poseidon2 row's
    outputs. -/
theorem bal_p2w {K HO HP : Nat} (hO : (R.poutRows K).length ≤ HO) (hP : (R.p2Rows K).length ≤ HP) (v : List F) :
    tableSends p2outAirB (R.poutTable K HO) "p2w" v + tableSends p2AirB (R.p2Table K HP) "p2w" v = 0 := by
  rw [R.pout_sendsT hO, R.p2_sendsT hP, fold_add2]
  apply foldr_zero_all
  intro i _
  cases hj : R.jetAt i
  · exact zero_add' 0
  · show _ + _ = (0 : F)
    simp only [if_true]
    obtain ⟨hbl, _⟩ := R.jet_facts hj
    rw [pout_p2w_call, p2_sends_w _ _ (Poseidon2SKI.valsB_length _)]
    rw [foldr_range_congr 16 (g := fun e => -ind ([ofN (R.rowQ i).ctr, ofN e,
      ofN ((Poseidon2.permute (Poseidon2SKI.valsB (R.jbits i))).getD e 0)] = v)) (fun e he => by rw [chunk_out _ hbl he])]
    rw [add_comm']
    exact sum_neg _ 16

end P2Run




namespace P2Run

variable (R : P2Run)

theorem calls_succ (K : Nat) : R.calls (K + 1) = R.calls K + (if R.jetAt K then 1 else 0) := by
  unfold calls
  rw [List.range_succ, List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  congr 1
  cases R.jetAt K <;> rfl

/-- **The calls, counted**: a sum over the rows of the jet rows' terms. -/
theorem calls_sum (S : F) : ∀ K, (List.range K).foldr (fun i acc => (if R.jetAt i then S else 0) + acc) 0 =
    ofN (R.calls K) * S
  | 0 => (zero_mul' S).symm
  | K + 1 => by
    rw [foldr_range_last (fun i => if R.jetAt i then S else 0) K, calls_sum S K, calls_succ, ofN_add, right_distrib']
    congr 1
    cases R.jetAt K
    · exact (zero_mul' S).symm
    · exact (one_mul' S).symm

/-- P2IN's level lookups: every level, once per call. -/
theorem pin_idx {K HI : Nat} (hI : (R.pinRows K).length ≤ HI) (v : List F) :
    tableSends p2inAirB (R.pinTable K HI) "p2idx" v =
      ofN (R.calls K) * (List.range P2_BITS).foldr (fun q acc => ind (idxRow q = v) + acc) 0 := by
  rw [R.pin_sendsT hI, ← calls_sum]
  refine foldr_range_congr K (fun i _ => ?_)
  cases R.jetAt i
  · exact (if_neg (by decide)).trans (if_neg (by decide)).symm
  · rw [if_pos rfl, if_pos rfl]; exact pin_idx_call _ _ _ _ _ v

/-- P2OUT's level lookups: every level, once per call. -/
theorem pout_idx {K HO : Nat} (hO : (R.poutRows K).length ≤ HO) (v : List F) :
    tableSends p2outAirB (R.poutTable K HO) "p2idx" v =
      ofN (R.calls K) * (List.range P2_BITS).foldr (fun q acc => ind (idxRow q = v) + acc) 0 := by
  rw [R.pout_sendsT hO, ← calls_sum]
  refine foldr_range_congr K (fun i _ => ?_)
  cases R.jetAt i
  · exact (if_neg (by decide)).trans (if_neg (by decide)).symm
  · rw [if_pos rfl, if_pos rfl]; exact pout_idx_call _ _ _ v

end P2Run


namespace P2Run

variable {R : P2Run}

/-- **The CPU's `segs` messages name segments**, as the composed CPU's. -/
theorem cpuP_segsHonest {K : Nat} (hR : RunC R.A R.n R.e R.row K) (hn : R.segRoots.length = R.n)
    (hd0 stk0 ctr0 n' nilA' J' root' : Nat) :
    ∀ r, r < (R.cpuTableP K).h → ∀ I ∈ (cpuAirP2 hd0 stk0 ctr0 n' nilA' J' root').inters, I.bus = "segs" →
      I.count.eval ((R.cpuTableP K).env r) ≠ 0 →
      ∃ q, q < R.segRoots.length ∧ I.fields.map (fun c => c.eval ((R.cpuTableP K).env r)) =
        [ofN q, ofN (R.segRoots.getD q 0)] := by
  intro r hr I hI hbus hc
  have hr' : r < K := hr
  change I ∈ cpuIntersP2 at hI
  rw [cpuIntersP2_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  have cv : ∀ c, c = RS ∨ c = CNT ∨ c = ROOT → (col c).eval ((R.cpuTableP K).env r) =
      (col c).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env r) := by
    intro c hc
    show (R.cpuTableP K).main ((r + 0) % K) c = (cpuTableC R.A R.row R.e R.n R.segRoots K).main ((r + 0) % K) c
    rw [Nat.add_zero, Nat.mod_eq_of_lt hr']
    exact R.cpuColP_hi (by rcases hc with rfl | rfl | rfl <;> decide) (by rcases hc with rfl | rfl | rfl <;> decide)
      (by rcases hc with rfl | rfl | rfl <;> decide)
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals first | exact absurd hbus (by decide) | skip
  have hc' : sRS.eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env r) ≠ 0 := by
    have := cv RS (.inl rfl)
    show (col RS).eval _ ≠ 0
    rw [← this]; exact hc
  obtain ⟨q, hq, e⟩ := cpuC_segsHonest hR hn r hr' ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩
    (by rw [cpuIntersC_eq]; simp only [List.mem_cons, true_or, or_true]) rfl hc'
  refine ⟨q, hq, ?_⟩
  rw [← e]
  simp only [List.map_cons, List.map_nil]
  show [(col CNT).eval _ + _, (col ROOT).eval _] = [(col CNT).eval _ + _, (col ROOT).eval _]
  rw [cv CNT (.inr (.inl rfl)), cv ROOT (.inr (.inr rfl))]
  rfl

end P2Run

end Circuit
