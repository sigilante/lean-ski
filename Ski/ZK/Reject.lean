import Ski.ZK.CompP

/-!
# Rejecting the non-generic challenges

`transcript_zkN` charges a fraction `P^2/P^4` for the challenges `β` in
`F(x^2)`, where a tuple's LogUp term is not a bijection and the tree does
not hide the terminals.  Whether `β` is one of them is public: its `x^1`
and `x^3` coefficients are zero (`generic_iff`).  So the verifier rejects
a proof whose `β` is non-generic, and the honest prover, on drawing one,
proves again from a fresh seed (`bench/plonky3/src/reject.rs`).  The
transcripts then range over the generic `β` only, and the simulator draws
from the same range.

`transcript_zkG` counts the draws whose `β` passes the verifier's test
`genB`, real and simulated, and drops the `P^2/P^4` term: the two counts
are within `M/P^4 + ε/NR` of the `Q4 · Q4 · NR · Q4^m` draws, of which
`Q4 · (Q4 - P^2) · NR · Q4^m` are counted.  Its instances are each hiding
circuit's: the composed (`comp_transcriptG`), Sudoku (`sud_transcriptG`),
hidden-term (`wit_transcriptG`), with jets (`compJ_transcriptG`) and with
the Poseidon2 jet (`compP_transcriptG`).
-/

namespace Circuit

open ZKF

/-- **The verifier's test of `β`**: a coefficient at `x^1` or `x^3`. -/
def genB (β : EF) : Bool := decide (β.x1 ≠ 0) || decide (β.x3 ≠ 0)

theorem genB_iff (β : EF) : genB β = true ↔ Generic β := by
  rw [generic_iff]
  unfold genB
  cases h1 : decide (β.x1 ≠ 0) <;> cases h3 : decide (β.x3 ≠ 0)
  · exact ⟨fun h => Bool.noConfusion h, fun h => h.elim (fun h => absurd (decide_eq_true h) (by rw [h1]; decide))
      (fun h => absurd (decide_eq_true h) (by rw [h3]; decide))⟩
  · exact ⟨fun _ => .inr (of_decide_eq_true h3), fun _ => rfl⟩
  · exact ⟨fun _ => .inl (of_decide_eq_true h1), fun _ => rfl⟩
  · exact ⟨fun _ => .inl (of_decide_eq_true h1), fun _ => rfl⟩

theorem sumTo_sumN_zero (NR m : Nat) : (sumTo NR fun _ => sumN m fun _ => indB false) = 0 := by
  rw [sumTo_congr _ fun _ _ => sumN_const m (indB false), sumTo_const]
  rfl

/-- **The transcript is simulatable at every generic challenge**: as
    `transcript_zkN`, counting only the draws whose `β` passes the
    verifier's test (`genB`), real and simulated alike, and without the
    `P^2/P^4` term. -/
theorem transcript_zkG {PV PB : Type} {off : EF → String → EF} {NR M ε m : Nat}
    {bus : Nat → String} {sg : Nat → Bool} {par : Nat → Nat} (hpar : ∀ k, par (k + 1) ≤ k)
    {tabs : (Nat → Tup) → List (AirD × Table)}
    {tv : (String → EF) → EF → (Nat → Tup) → List EF} {tp : (String → EF) → EF → EF}
    {pb : (String → EF) → EF → PB}
    {pcs : (Nat → Tup) → EF → EF → Nat → PV} {psim : EF → EF → List EF → Nat → PV}
    {xu : (String → EF) → EF → Nat → EF}
    (hchain : ∀ pre β t, tv pre β t = viewT β (fun k => pre (bus k)) sg par (m + 1) (xu pre β) t)
    (hsum : ∀ pre β, sumL (xu pre β) (List.range (m + 1)) = EF.zero.sub (tp pre β))
    (hM : ∀ t, (allEntries (tabs t)).length ≤ M)
    (hpcs : PCSCloseN off NR tv pcs psim ε) (E : TViewN PV PB → Bool) :
    tsumN NR m (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (simVN off pb bus sg par (m + 1) tp psim α β r t))) +
        Q4 * (NR * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * ε)) ∧
    tsumN NR m (fun α β r t => indB (genB β && E (simVN off pb bus sg par (m + 1) tp psim α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * ε)) := by
  let U := tsumN NR m (fun α β r t => indB (genB β && E (some (pcs t α β r, α, β,
    tv (prefixOf α (off β)) β t, pb (prefixOf α (off β)) β))))
  let S := tsumN NR m (fun α β r t => indB (genB β && E (simVN off pb bus sg par (m + 1) tp psim α β r t)))
  let Rl := tsumN NR m (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t)))
  let Ab := tsumN NR m (fun α β r t => indB (Aborts (prefixOf α (off β)) β (tabs t)))
  -- 1. the abort moves the count by at most the aborting draws
  have hRU : Rl ≤ U + Ab := by
    show Rl ≤ U + Ab
    rw [← tsumN_add]
    refine tsumN_mono fun α β r t => ?_
    unfold realVN
    cases Aborts (prefixOf α (off β)) β (tabs t)
    · simp only [Bool.false_eq_true, if_false]; exact Nat.le_add_right _ _
    · simp only [if_true]
      have := indB_le (genB β && E none)
      show indB (genB β && E none) ≤ _ + 1
      omega
  have hUR : U ≤ Rl + Ab := by
    show U ≤ Rl + Ab
    rw [← tsumN_add]
    refine tsumN_mono fun α β r t => ?_
    unfold realVN
    cases Aborts (prefixOf α (off β)) β (tabs t)
    · simp only [Bool.false_eq_true, if_false]; exact Nat.le_add_right _ _
    · simp only [if_true]
      have := indB_le (genB β && E (some (pcs t α β r, α, β, tv (prefixOf α (off β)) β t,
        pb (prefixOf α (off β)) β)))
      show _ ≤ _ + 1
      omega
  -- 2. the aborting draws: at most `M` values of `α` for each of the rest
  have hAb : Ab ≤ Q4 * (NR * (Q4 ^ m * M)) := by
    show tsumN NR m _ ≤ _
    unfold tsumN
    rw [sumTo_exch _ Q4 Q4]
    refine sumTo_le_const (fun j => ?_) Q4
    rw [sumTo_exch _ NR Q4]
    refine sumTo_le_const (fun r => ?_) NR
    rw [sumTo_sumN m Q4]
    refine sumN_le_const m (fun t => ?_)
    exact Nat.le_trans (abort_count (off (efOf j)) (efOf j) (tabs t)) (hM _)
  -- 3. the challenges: none counted at a non-generic `β`; at a generic one
  --    the PCS within `ε`, then equal
  let D := Q4 ^ m * ε
  have per : ∀ i j,
      realInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (pcs := pcs)
          (fun v => genB (efOf j) && E v) (efOf i) (efOf j) ≤
        (sumTo NR fun r => sumN m fun t =>
          indB (genB (efOf j) && E (simVN off pb bus sg par (m + 1) tp psim (efOf i) (efOf j) r t))) + D ∧
      (sumTo NR fun r => sumN m fun t =>
          indB (genB (efOf j) && E (simVN off pb bus sg par (m + 1) tp psim (efOf i) (efOf j) r t))) ≤
        realInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (pcs := pcs)
          (fun v => genB (efOf j) && E v) (efOf i) (efOf j) + D := by
    intro i j
    cases hg : genB (efOf j)
    · unfold realInN
      simp only [Bool.false_and]
      rw [sumTo_sumN_zero]
      exact ⟨Nat.zero_le _, Nat.zero_le _⟩
    · have hd : Generic (efOf j) := (genB_iff _).1 hg
      have hp := inner_pcsN (tv := tv) (pb := pb) (m := m) hpcs (fun v => genB (efOf j) && E v) (efOf i) (efOf j)
      have hc := inner_chainN (off := off) (NR := NR) (pb := pb) (psim := psim) hpar hchain hsum
        (fun v => genB (efOf j) && E v) (α := efOf i) hd
      rw [hc, hg] at hp
      exact hp
  have hsumD : (sumTo Q4 fun _ => sumTo Q4 fun _ => D) = Q4 * (Q4 * (Q4 ^ m * ε)) := by
    rw [sumTo_const, sumTo_const]
  have hUS : U ≤ S + Q4 * (Q4 * (Q4 ^ m * ε)) := by
    show tsumN NR m _ ≤ tsumN NR m _ + _
    unfold tsumN
    rw [← hsumD, ← sumTo_add]
    refine sumTo_mono _ fun i _ => ?_
    rw [← sumTo_add]
    refine sumTo_mono _ fun j _ => ?_
    have := (per i j).1
    unfold realInN at this
    exact this
  have hSU : S ≤ U + Q4 * (Q4 * (Q4 ^ m * ε)) := by
    show tsumN NR m _ ≤ tsumN NR m _ + _
    unfold tsumN
    rw [← hsumD, ← sumTo_add]
    refine sumTo_mono _ fun i _ => ?_
    rw [← sumTo_add]
    refine sumTo_mono _ fun j _ => ?_
    have := (per i j).2
    unfold realInN at this
    exact this
  exact ⟨by omega, by omega⟩

-- ---------------------------------------------------------------------------
-- The circuits
-- ---------------------------------------------------------------------------

/-- **The composed proof's transcript at every generic challenge**
    (formulas and predicates alike): `comp_transcriptN`, with `β` tested. -/
theorem comp_transcriptG {PV : Type} (off : EF → String → EF) (NR ε : Nat)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat} {C Mm Wt : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt (segsPub roots)))
    (h : Unblinded WT_BLIND C Mm Wt)
    (hpcs : PCSCloseN off NR (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) pcs psim ε)
    (E : TViewN PV (EF × EF) → Bool) :
    let tabs := fun t : Nat → Tup => compTables hd0 stk0 ctr0 n nilA heap N W roots
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableC heap N W)
      (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
    let tv := fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t
    let pb := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W),
      terminal pre β (segsAir roots) (segsPub roots))
    let tp := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))
    let M := (allEntries (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt
      (segsPub roots))).length
    tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 tp psim α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * ε)) ∧
    tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 tp psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * ε)) :=
  transcript_zkG (m := 2) chainPar_ok
    (xu := fun pre β => chainBase ⟨terminal pre β (witAir N W) Wt, terminal pre β (cpuAirC hd0 stk0 ctr0 n nilA) C,
      terminal pre β memAirC Mm⟩)
    (fun pre β t => by
      rw [chainBus_pre, chain_viewT, ← comp_chain pre β hd0 stk0 ctr0 n nilA N W h (t 1) (t 0)]; rfl)
    (fun pre β => by rw [chainBase_sum]; exact comp_sum pre β hb)
    (fun t => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

/-- The Sudoku proof's published private terminals, in the tree's order. -/
def sudViewN (pre : String → EF) (β : EF) (hd0 stk0 ctr0 : Nat) (C Mm Wt : Table) (t : Nat → Tup) : List EF :=
  enc3 (sudView pre β hd0 stk0 ctr0 C Mm Wt (t 1) (t 0))

/-- **The Sudoku proof's transcript at every generic challenge**. -/
theorem sud_transcriptG {PV : Type} (off : EF → String → EF) (NR ε : Nat)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
    {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Wt : Table}
    (hb : Balanced (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)) (h : Unblinded 1 C Mm Wt)
    (hpcs : PCSCloseN off NR (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) pcs psim ε)
    (E : TViewN PV EF → Bool) :
    let tabs := fun t : Nat → Tup => sudTables hd0 stk0 ctr0 heap ((C.setBlind BLA (t 1)).setBlind BLB (t 0))
      (Mm.setBlind 5 (t 0)) (progTableS heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS heap) (progTableS heap)
    let M := (allEntries (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)).length
    tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * ε)) ∧
    tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * ε)) :=
  transcript_zkG (m := 2) chainPar_ok
    (xu := fun pre β => chainBase ⟨terminal pre β witAirS Wt,
      terminal pre β (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) C, terminal pre β memAirC Mm⟩)
    (fun pre β t => by
      rw [chainBus_pre, chain_viewT, ← sud_chain pre β hd0 stk0 ctr0 h (t 1) (t 0)]; rfl)
    (fun pre β => by rw [chainBase_sum]; exact sud_sum pre β hb)
    (fun t => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

/-- The hidden-term proof's published private terminals, in the tree's
    order. -/
def witViewN (pre : String → EF) (β : EF) (hd0 stk0 ctr0 W : Nat) (C Mm Wt : Table) (t : Nat → Tup) : List EF :=
  enc3 (witView pre β hd0 stk0 ctr0 W C Mm Wt (t 1) (t 0))

/-- **The hidden-term proof's transcript at every generic challenge**. -/
theorem wit_transcriptG {PV : Type} (off : EF → String → EF) (NR ε : Nat)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
    {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat} {C Mm Wt : Table}
    (hb : Balanced (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)) (h : Unblinded WT_BLIND C Mm Wt)
    (hpcs : PCSCloseN off NR (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) pcs psim ε)
    (E : TViewN PV EF → Bool) :
    let tabs := fun t : Nat → Tup => witTables hd0 stk0 ctr0 heap W ((C.setBlind BLA (t 1)).setBlind BLB (t 0))
      (Mm.setBlind 5 (t 0)) (progTableW heap W) (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirW heap W) (progTableW heap W)
    let M := (allEntries (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)).length
    tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * ε)) ∧
    tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * ε)) :=
  transcript_zkG (m := 2) chainPar_ok
    (xu := fun pre β => chainBase ⟨terminal pre β (witAirW W) Wt,
      terminal pre β (cpuAirW hd0 stk0 ctr0) C, terminal pre β memAirC Mm⟩)
    (fun pre β t => by
      rw [chainBus_pre, chain_viewT, ← wit_chain pre β hd0 stk0 ctr0 W h (t 1) (t 0)]; rfl)
    (fun pre β => by rw [chainBase_sum]; exact wit_sum pre β hb)
    (fun t => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

/-- **The transcript with jets at every generic challenge**: `compJ_transcript`, with `β` tested. -/
theorem compJ_transcriptG {PV : Type} (off : EF → String → EF) (NR ε : Nat)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {segRoots : List Nat}
    {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Wt Rt Hd Tm Po Iw : Table}
    (hb : Balanced (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm (progTableC heap N W) Wt
      (segsPub segRoots) Rt Hd Tm Po Iw))
    (h : UnblindedCJ roots jets C Mm Wt Rt Hd Tm Po Iw)
    (hpcs : PCSCloseN off NR (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets
      C Mm Wt Rt Hd Tm Po Iw t) pcs psim ε)
    (E : TViewN PV (EF × EF) → Bool) :
    let tabs := fun t : Nat → Tup => compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets
      (((C.setBlind BLAJ (t 1)).setBlind BLBJ (t 0)).setBlind BLCJ (t 2)) (Mm.setBlind 5 (t 0))
      (progTableC heap N W) (Wt.setBlind WT_BLIND (t 1)) (segsPub segRoots) (Rt.setBlind 1 (t 6))
      ((Hd.setBlind 1 (t 5)).setBlind 6 (t 6)) ((Tm.setBlind 1 (t 4)).setBlind 6 (t 5))
      ((Po.setBlind popAir.width (t 2)).setBlind (popAir.width + 5) (t 3))
      ((Iw.setBlind instwAir.width (t 3)).setBlind (instwAir.width + 5) (t 4))
    let tv := fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t
    let pb := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W),
      terminal pre β (segsAir segRoots) (segsPub segRoots))
    let tp := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W)).add
      (terminal pre β (segsAir segRoots) (segsPub segRoots))
    let M := (allEntries (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm (progTableC heap N W)
      Wt (segsPub segRoots) Rt Hd Tm Po Iw)).length
    tsumN NR 7 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR 7 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 8 tp psim α β r t))) +
        Q4 * (NR * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * ε)) ∧
    tsumN NR 7 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 8 tp psim α β r t))) ≤
      tsumN NR 7 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * ε)) :=
  transcript_zkG (m := 7) jetPar_ok
    (xu := fun pre β => cjBase pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw)
    (fun pre β t => compJ_chain pre β hd0 stk0 ctr0 n nilA N W h t)
    (fun pre β => compJ_sum pre β hb)
    (fun t => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

/-- **The transcript with the Poseidon2 jet at every generic challenge**: `compP_transcript`, with `β` tested. -/
theorem compP_transcriptG {PV : Type} (off : EF → String → EF) (NR ε calls : Nat)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
    {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
    {C Mm Wt Pi Po Pp : Table}
    (hb : Balanced (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm (progTableC heap N W) Wt
      (segsPub roots) Pi Po Pp (idxPub calls)))
    (h : UnblindedCP C Mm Wt Pi Po Pp)
    (hpcs : PCSCloseN off NR (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t)
      pcs psim ε)
    (E : TViewN PV ((EF × EF) × EF) → Bool) :
    let tabs := fun t : Nat → Tup => compPTables hd0 stk0 ctr0 n nilA J root heap N W roots
      (((C.setBlind BLA (t 1)).setBlind BLB (t 0)).setBlind (P2SEL + 1) (t 2)) (Mm.setBlind 5 (t 0))
      (progTableC heap N W) (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
      ((Pi.setBlind p2inAir.width (t 2)).setBlind (p2inAir.width + 5) (t 3))
      ((Po.setBlind p2outAir.width (t 3)).setBlind (p2outAir.width + 5) (t 4))
      (Pp.setBlind P2Air.p2Air.width (t 4)) (idxPub calls)
    let tv := fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t
    let pb := fun pre β => ((terminal pre β (progAirC heap N W) (progTableC heap N W),
      terminal pre β (segsAir roots) (segsPub roots)), terminal pre β p2idxAir (idxPub calls))
    let tp := fun pre β => ((terminal pre β (progAirC heap N W) (progTableC heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))).add (terminal pre β p2idxAir (idxPub calls))
    let M := (allEntries (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm (progTableC heap N W)
      Wt (segsPub roots) Pi Po Pp (idxPub calls))).length
    tsumN NR 5 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR 5 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 6 tp psim α β r t))) +
        Q4 * (NR * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * ε)) ∧
    tsumN NR 5 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 6 tp psim α β r t))) ≤
      tsumN NR 5 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * ε)) :=
  transcript_zkG (m := 5) jetPar_ok
    (xu := fun pre β => cpBase pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp)
    (fun pre β t => compP_chain pre β hd0 stk0 ctr0 n nilA J root N W h t)
    (fun pre β => compP_sum pre β hb)
    (fun t => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

end Circuit
