import Ski.ZK.CompP
import Ski.Circuit.CompPComplete
import Ski.P2Once

/-!
# The honest tables meet the zero-knowledge theorem's hypotheses

**`P2Run.honest_zkP`**: the tables an honest prover builds from a run of
the circuit with the Poseidon2 jet (`Ski/Circuit/CompPHonest.lean`) balance
with the public program, segment and level tables, the level table's
multiplicities those of the run's jet calls (`balancedP`), and carry clear
blinding flags: `compP_transcript`'s hypotheses.  An honest run of one
verifier in the frame, as `p2pre h` and `p2commit c pat` are, calls the jet
once (`calls_one`), so its tables meet them with the level table `idxPub 1`
(`honest_zk_p2pre`, `honest_zk_p2commit`).  The same tables satisfy each
AIR's constraints, so the circuit accepts them (`compPG_complete_log`,
`Ski/Circuit/CompPCompleteFinal.lean`).
-/

namespace Circuit

open B Air Compose CompM Mach

theorem foldr_ite_mul (P : Nat → Prop) [DecidablePred P] (a : F) : ∀ l : List Nat,
    l.foldr (fun q acc => (if P q then a else 0) + acc) 0 = a * l.foldr (fun q acc => ind (P q) + acc) 0
  | [] => (mul_zero' a).symm
  | q :: l => by
    simp only [List.foldr_cons]
    rw [foldr_ite_mul P a l, left_distrib']
    congr 1
    unfold ind; split
    · exact (mul_one' a).symm
    · exact (mul_zero' a).symm

/-- The level table's 512 rows: the 496 levels, padded to a power of two. -/
theorem idxPub_h (calls : Nat) : (idxPub calls).h = 512 := by
  unfold idxPub; dsimp only; exact idxRows_length

/-- **The public level table receives every level `2 · calls` times.** -/
theorem idx_sends (calls : Nat) (v : List F) :
    tableSends p2idxAir (idxPub calls) "p2idx" v =
      -ofN (2 * calls) * (List.range P2_BITS).foldr (fun q acc => ind (idxRow q = v) + acc) 0 := by
  have hh := idxPub_h calls
  have hrow : ∀ q, q < (idxPub calls).h → rowSends p2idxAir (idxPub calls) "p2idx" v q =
      if q < P2_BITS then (if idxRow q = v then -ofN (2 * calls) else 0) else 0 := by
    intro q hq
    have hq' : q < 512 := by rw [← hh]; exact hq
    have ev : ∀ j, (prec j).eval ((idxPub calls).env q) = (idxRows.getD q []).getD j 0 := fun j => by
      show (idxPub calls).pre ((q + 0) % (idxPub calls).h) j = _
      rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; unfold idxPub; dsimp only
    have ec : (col 0).eval ((idxPub calls).env q) = if q < P2_BITS then ofN (2 * calls) else 0 := by
      show (idxPub calls).main ((q + 0) % (idxPub calls).h) 0 = _
      rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; unfold idxPub; dsimp only
    have hpre : ((List.range 6).map prec).map (fun e => e.eval ((idxPub calls).env q)) =
        idxRow (if q < P2_BITS then q else 0) := by
      show [(prec 0).eval _, (prec 1).eval _, (prec 2).eval _, (prec 3).eval _, (prec 4).eval _, (prec 5).eval _] = _
      rw [ev 0, ev 1, ev 2, ev 3, ev 4, ev 5, idxRows_get hq']; rfl
    show (if "p2idx" = "p2idx" ∧ ((List.range 6).map prec).map (fun e => e.eval ((idxPub calls).env q)) = v
      then (E.neg (col 0)).eval ((idxPub calls).env q) else 0) + 0 = _
    rw [hpre, ite_and_one, add_zero']
    show (if _ = v then -((col 0).eval ((idxPub calls).env q)) else 0) = _
    rw [ec]
    by_cases h : q < P2_BITS
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      split
      · exact neg_zero_eq
      · rfl
  unfold tableSends
  rw [foldr_range_congr _ hrow, hh, ← foldr_ite_mul]
  rw [foldr_range_split _ P2_BITS 512 (by decide) (fun q h1 _ => if_neg (by omega))]
  exact foldr_range_congr P2_BITS (fun q hq => if_pos hq)

namespace P2Run

variable {R : P2Run}

/-- **`p2idx` balances**: each call looks up every level twice, from P2IN
    and P2OUT, and the public table receives `2 · calls` of each. -/
theorem bal_p2idx {K HI HO : Nat} (hI : (R.pinRows K).length ≤ HI) (hO : (R.poutRows K).length ≤ HO) (v : List F) :
    tableSends p2inAirB (R.pinTable K HI) "p2idx" v + (tableSends p2outAirB (R.poutTable K HO) "p2idx" v +
      tableSends p2idxAir (idxPub (R.calls K)) "p2idx" v) = 0 := by
  have h1 := R.pin_idx hI v
  have h2 := R.pout_idx hO v
  have h3 := idx_sends (R.calls K) v
  generalize (List.range P2_BITS).foldr (fun q acc => ind (idxRow q = v) + acc) 0 = S at h1 h2 h3
  rw [h1, h2, h3, ofN_mul]
  exact E.eval_eq_of_norm
    (e := .add (.mul (.atom (.main 0 0)) (.atom (.main 0 1))) (.add (.mul (.atom (.main 0 0)) (.atom (.main 0 1)))
      (.mul (.neg (.mul (.const (ofN 2)) (.atom (.main 0 0)))) (.atom (.main 0 1)))))
    (e' := .const 0) (by decide) (at4 (ofN (R.calls K)) _ 0 0)

end P2Run


-- ---------------------------------------------------------------------------
-- The buses each table uses
-- ---------------------------------------------------------------------------

theorem pin_buses : ∀ I ∈ p2inAir.inters, I.bus = "p2idx" ∨ I.bus = "p2i" ∨ I.bus = "mem" ∨ I.bus = "p2v" := by
  intro I hI
  simp only [p2inAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))

theorem pout_buses : ∀ I ∈ p2outAir.inters, I.bus = "p2idx" ∨ I.bus = "p2o" ∨ I.bus = "mem" ∨ I.bus = "p2w" := by
  intro I hI
  simp only [p2outAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))

theorem p2_buses : ∀ I ∈ P2Air.p2Air.inters, I.bus = "p2v" ∨ I.bus = "p2w" := by
  intro I hI
  rw [p2Air_inters] at hI
  rcases List.mem_append.1 hI with hI | hI <;> obtain ⟨e, _, rfl⟩ := List.mem_map.1 hI
  · exact .inl rfl
  · exact .inr rfl

theorem cpuP_off (hd0 stk0 ctr0 n nilA J root : Nat) {C : Table} {bus : String} (v : List F)
    (h1 : bus ≠ "mem") (h2 : bus ≠ "segs") (h3 : bus ≠ "p2i") (h4 : bus ≠ "p2o") (h5 : bus ≠ "blind_c")
    (h6 : bus ≠ "blind_a") (h7 : bus ≠ "blind_b") :
    tableSends (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C bus v = 0 := by
  apply sends_off
  intro I hI
  change I ∈ cpuIntersP2 at hI
  rw [cpuIntersP2_eq] at hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4 | exact Ne.symm h5 | exact Ne.symm h6 | exact Ne.symm h7

-- ---------------------------------------------------------------------------
-- The balance
-- ---------------------------------------------------------------------------

namespace P2Run

variable {R : P2Run} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCP R.A m0 [] [] R.J R.root R.segRoots nilA R.n R.e R.row) {K : Nat} (hK : R.e (R.n - 1) < K)

include hA hK in
/-- **The honest tables of the circuit with the Poseidon2 jet balance**:
    with the public program, segment and level tables, the level table's
    multiplicities those of the run's `calls K` jet calls. -/
theorem balancedP (hd0 stk0 ctr0 J root : Nat) {heap : List Cell} {N W : Nat} {HI HO HP : Nat}
    (hML : R.A.length < P) (hn : R.segRoots.length = R.n) (hnP : R.n < P)
    (hHI : (R.pinRows K).length ≤ HI) (hHO : (R.poutRows K).length ≤ HO) (hHP : (R.p2Rows K).length ≤ HP)
    (hpub : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + N + W) → i < R.A.length ∧ R.A.getD i .nil = heap.getD i .nil)
    (hbits : ∀ i, i < N → R.A.getD (3 + i) .nil = .K ∨ R.A.getD (3 + i) .nil = .app 0 1) (h496 : 496 ≤ N)
    (hreg : ∀ i, i < W → Wit.cellOK (3 + N + i) (R.A.getD (3 + N + i) .nil) = true)
    (hlenW : 3 + N + W ≤ R.A.length) :
    Balanced (compPTables hd0 stk0 ctr0 R.n nilA J root heap N W R.segRoots (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n nilA J root) (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (progTableC heap N W) (witTableP R.A N W) (segsPub R.segRoots) (R.pinTable K HI) (R.poutTable K HO)
      (R.p2Table K HP) (idxPub (R.calls K))) := by
  intro bus v
  simp only [compPTables, List.foldr_cons, List.foldr_nil, add_zero']
  have hR := runC hA hK
  have hR0 : 0 < R.segRoots.length := by have := hA.npos; omega
  let cpu := cpuAirP2 hd0 stk0 ctr0 R.n nilA J root
  let C := R.cpuTableP K
  let Pi := R.pinTable K HI
  let Po := R.poutTable K HO
  let Pp := R.p2Table K HP
  let Wt := witTableP R.A N W
  let Mm := memTable5 R.A cpu (progAirC heap N W) p2inAirB p2outAirB (witAirP N W) C (progTableC heap N W) Pi Po Wt
  -- the blinded tables send as their bases
  have ePi : tableSends p2inAirB Pi bus v = tableSends p2inAir Pi bus v := sends_withBlocks_quiet R.pin_wide bus v
  have ePo : tableSends p2outAirB Po bus v = tableSends p2outAir Po bus v := sends_withBlocks_quiet R.pout_wide bus v
  have ePp : tableSends p2AirB Pp bus v = tableSends P2Air.p2Air Pp bus v := sends_withBlocks_quiet R.p2_wide bus v
  -- the tables off their buses
  have zM : bus ≠ "mem" → tableSends memAirC Mm bus v = 0 :=
    fun h => (sends_memC5 bus v).trans (sends_off (one_bus mem_bus (Ne.symm h)))
  have zP : bus ≠ "mem" → tableSends (progAirC heap N W) (progTableC heap N W) bus v = 0 :=
    fun h => sends_nobus (fun I hI => by
      simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; exact fun e => h e.symm)
  have zW : bus ≠ "mem" → tableSends (witAirP N W) Wt bus v = 0 :=
    fun h => sends_zero_of (Q := fun _ => False) (fun r hr I hI hb hc => hc (witTP_blindZero r hr I hI (hb ▸ h))) id
  have zS : bus ≠ "segs" → tableSends (segsAir R.segRoots) (segsPub R.segRoots) bus v = 0 :=
    fun h => sends_nobus (fun I hI => by
      simp only [segsAir, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; exact fun e => h e.symm)
  have zI : bus ≠ "p2idx" → bus ≠ "p2i" → bus ≠ "mem" → bus ≠ "p2v" → tableSends p2inAirB Pi bus v = 0 :=
    fun h1 h2 h3 h4 => ePi.trans (sends_off (off4 pin_buses (Ne.symm h1) (Ne.symm h2) (Ne.symm h3) (Ne.symm h4)))
  have zO : bus ≠ "p2idx" → bus ≠ "p2o" → bus ≠ "mem" → bus ≠ "p2w" → tableSends p2outAirB Po bus v = 0 :=
    fun h1 h2 h3 h4 => ePo.trans (sends_off (off4 pout_buses (Ne.symm h1) (Ne.symm h2) (Ne.symm h3) (Ne.symm h4)))
  have zQ : bus ≠ "p2v" → bus ≠ "p2w" → tableSends p2AirB Pp bus v = 0 :=
    fun h1 h2 => ePp.trans (sends_off (fun I hI e => by
      rcases p2_buses I hI with h | h
      · exact h1 (e.symm.trans h)
      · exact h2 (e.symm.trans h)))
  have zX : bus ≠ "p2idx" → tableSends p2idxAir (idxPub (R.calls K)) bus v = 0 :=
    fun h => sends_nobus (fun I hI => by
      simp only [p2idxAir, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; exact fun e => h e.symm)
  by_cases hm : bus = "mem"
  · -- the memory
    subst hm
    rw [zS (by decide), zQ (by decide) (by decide), zX (by decide), sends_memC5]
    simp only [zero_add', add_zero']
    have hperm : ∀ a b c : F, a + (b + c) = b + (c + a) := fun a b c => by rw [add_comm' a, add_assoc']
    rw [hperm (tableSends (witAirP N W) Wt "mem" v)]
    exact bal_mem5 hML (cpuP_honest hA hK hd0 stk0 ctr0 R.n nilA J root)
      (fun r hr I hI _ hc => progC_honest hpub r hr I hI hc)
      (honest_withBlocks (by decide) (pin_honest (fun i hi => hbits i (by omega))))
      (honest_withBlocks (by decide) pout_honest)
      (witTP_honest hbits hreg hlenW) v
  rw [zM hm, zP hm, zW hm]
  by_cases hs : bus = "segs"
  · -- the segments
    subst hs
    rw [zI (by decide) (by decide) (by decide) (by decide), zO (by decide) (by decide) (by decide) (by decide),
      zQ (by decide) (by decide), zX (by decide)]
    simp only [zero_add', add_zero']
    have hsg : segsPub R.segRoots = segsTableC R.segRoots cpu C :=
      ((R.segsTableP hd0 stk0 ctr0 R.n nilA J root K).trans
        (segs_honest hR hd0 stk0 ctr0 R.n nilA hn hnP)).symm
    rw [hsg]
    exact bal_segsC (by omega) hR0 (cpuP_segsHonest hR hn hd0 stk0 ctr0 R.n nilA J root) v
  rw [zS hs]
  by_cases hb : bus = "blind_a" ∨ bus = "blind_b" ∨ bus = "blind_c"
  · -- the blinding buses: every flag is clear
    rw [R.cpuP_blindZero hd0 stk0 ctr0 R.n nilA J root K hb v]
    have h1 : bus ≠ "p2idx" ∧ bus ≠ "p2i" ∧ bus ≠ "p2v" ∧ bus ≠ "p2o" ∧ bus ≠ "p2w" := by
      rcases hb with rfl | rfl | rfl <;> decide
    obtain ⟨h1, h2, h3, h4, h5⟩ := h1
    rw [zI h1 h2 hm h3, zO h1 h4 hm h5, zQ h3 h5, zX h1]
    decide
  have hb' : bus ≠ "blind_a" ∧ bus ≠ "blind_b" ∧ bus ≠ "blind_c" :=
    ⟨fun h => hb (.inl h), fun h => hb (.inr (.inl h)), fun h => hb (.inr (.inr h))⟩
  by_cases hi : bus = "p2i"
  · subst hi
    rw [zO (by decide) (by decide) (by decide) (by decide), zQ (by decide) (by decide), zX (by decide)]
    simp only [zero_add', add_zero']
    exact R.bal_p2i hd0 stk0 ctr0 R.n nilA J root hHI v
  by_cases ho : bus = "p2o"
  · subst ho
    rw [zI (by decide) (by decide) (by decide) (by decide), zQ (by decide) (by decide), zX (by decide)]
    simp only [zero_add', add_zero']
    exact R.bal_p2o hd0 stk0 ctr0 R.n nilA J root hHO v
  rw [cpuP_off hd0 stk0 ctr0 R.n nilA J root v hm hs hi ho hb'.2.2 hb'.1 hb'.2.1, zero_add', zero_add', zero_add',
    zero_add', zero_add']
  by_cases hv : bus = "p2v"
  · subst hv
    rw [zO (by decide) (by decide) (by decide) (by decide), zX (by decide), zero_add', add_zero']
    exact R.bal_p2v hHI hHP v
  by_cases hw : bus = "p2w"
  · subst hw
    rw [zI (by decide) (by decide) (by decide) (by decide), zX (by decide), zero_add', add_zero']
    exact R.bal_p2w hHO hHP v
  rw [zQ hv hw, zero_add']
  by_cases hx : bus = "p2idx"
  · subst hx
    exact R.bal_p2idx hHI hHO v
  rw [zI hx hi hm hv, zO hx ho hm hw, zX hx]
  decide

end P2Run


namespace P2Run

variable {R : P2Run} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCP R.A m0 [] [] R.J R.root R.segRoots nilA R.n R.e R.row) {K : Nat} (hK : R.e (R.n - 1) < K)

omit hA hK in
theorem witTP_flag {A : List Cell} {N W : Nat} (r : Nat) : (witTableP A N W).main r (WT_BLIND + 4) = 0 := by
  show witColG 3 A N W r (WT_BLIND + 4) = 0
  unfold witColG
  split
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  · rfl

omit hA hK in
theorem cpuP_flag {K r c : Nat} (hc : c = BLA + 4 ∨ c = BLB + 4 ∨ c = P2SEL + 1 + 4) : (R.cpuTableP K).main r c = 0 := by
  show R.cpuColP r c = 0
  rw [R.cpuColP_hi (by rcases hc with rfl | rfl | rfl <;> decide) (by rcases hc with rfl | rfl | rfl <;> decide)]
  rcases hc with rfl | rfl | rfl
  · exact cpuColC_blind _ (.inl rfl)
  · exact cpuColC_blind _ (.inr rfl)
  · show cpuColC R.A R.row R.e R.n R.segRoots r (ROOT + 6) = 0
    unfold cpuColC
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]

include hA hK in
/-- **The honest tables meet `compP_transcript`'s hypotheses**: they
    balance with the public program, segment and level tables, the level
    table's multiplicities those of the run's jet calls (`balancedP`), and
    their blinding flags are clear.  The layout: `N ≥ 496` literal bit
    cells and `W` well-formed region cells from address `3`, the public
    cells the statement's (`hpub`).  `J` and `root` enter only the CPU's
    constraints, not its messages, so the balance holds for any. -/
theorem honest_zkP (hd0 stk0 ctr0 J root : Nat) {heap : List Cell} {N W : Nat} {HI HO HP : Nat}
    (hML : R.A.length < P) (hn : R.segRoots.length = R.n) (hnP : R.n < P)
    (hHI : (R.pinRows K).length ≤ HI) (hHO : (R.poutRows K).length ≤ HO) (hHP : (R.p2Rows K).length ≤ HP)
    (hHI0 : 0 < HI) (hHO0 : 0 < HO) (hHP0 : 0 < HP)
    (hpub : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + N + W) → i < R.A.length ∧ R.A.getD i .nil = heap.getD i .nil)
    (hbits : ∀ i, i < N → R.A.getD (3 + i) .nil = .K ∨ R.A.getD (3 + i) .nil = .app 0 1) (h496 : 496 ≤ N)
    (hreg : ∀ i, i < W → Wit.cellOK (3 + N + i) (R.A.getD (3 + N + i) .nil) = true)
    (hlenW : 3 + N + W ≤ R.A.length) :
    Balanced (compPTables hd0 stk0 ctr0 R.n nilA J root heap N W R.segRoots (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n nilA J root) (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (progTableC heap N W) (witTableP R.A N W) (segsPub R.segRoots) (R.pinTable K HI) (R.poutTable K HO)
      (R.p2Table K HP) (idxPub (R.calls K))) ∧
    UnblindedCP (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n nilA J root) (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (witTableP R.A N W) (R.pinTable K HI) (R.poutTable K HO) (R.p2Table K HP) := by
  refine ⟨balancedP hA hK hd0 stk0 ctr0 J root hML hn hnP hHI hHO hHP hpub hbits h496 hreg hlenW, ?_⟩
  have hWt : 0 < (witTableP R.A N W).h := by
    have := witRowsP_length N W
    show 0 < (witRowsP N W).length
    omega
  exact {
    hc := show 0 < K by omega
    hm := show 0 < R.A.length by omega
    hw := hWt
    hpi := hHI0
    hpo := hHO0
    hp2 := hHP0
    za := fun r _ => cpuP_flag (.inl rfl)
    zb := fun r _ => cpuP_flag (.inr (.inl rfl))
    zc := fun r _ => cpuP_flag (.inr (.inr rfl))
    zm := fun _ _ => rfl
    zw := fun r _ => witTP_flag r
    wpi := R.pin_wide
    wpo := R.pout_wide
    wp2 := R.p2_wide }

end P2Run


-- ---------------------------------------------------------------------------
-- One call
-- ---------------------------------------------------------------------------

theorem filter_one (p : Nat → Bool) {r0 : Nat} (hp : ∀ i, p i = true ↔ i = r0) :
    ∀ K, r0 < K → ((List.range K).filter p).length = 1
  | 0, h => absurd h (Nat.not_lt_zero _)
  | K + 1, h => by
    rw [List.range_succ, List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
    rcases Nat.lt_or_ge r0 K with hl | hge
    · rw [filter_one p hp K hl]
      have : p K = false := by
        cases hk : p K
        · rfl
        · exact absurd ((hp K).1 hk) (by omega)
      rw [this]; rfl
    · have hK : r0 = K := by omega
      have hz : ((List.range K).filter p).length = 0 := by
        rw [filter_nil' (fun i hi => by
          cases hpi : p i
          · rfl
          · have := (hp i).1 hpi
            have := List.mem_range.1 hi
            omega)]
        rfl
      rw [hz, (hp K).2 hK.symm]; rfl

namespace P2Run

variable {R : P2Run}

/-- **An honest run of one verifier in the frame calls the jet once**: its
    `calls` is `1`, so the public level table is `idxPub 1`.  The verifiers
    of `p2pre h` and `p2commit c pat` are in the frame
    (`P2Once.verifierO_eq`, `P2Once.verifierC_eq`). -/
theorem calls_one {ρ : Nat → Bool} {shp : BT} {region : List Cell} {V : OTerm} {G U : OTerm → Prop}
    (hp : P2Once.Part R.J G U) {g : OTerm} (hg : G g) (hV : V = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ g)
    {bs₀ : List Bool} (hb0 : P2Jet.bitsAt (cMachineO ρ shp region [V]).heap P2Jet.slotAddrs = some bs₀)
    (ho0 : otermAt (cMachineO ρ shp region [V]).heap ((cMachineO ρ shp region [V]).heap.length + 1) R.root =
      some (Poseidon2SKI.combT bs₀).toO)
    (hr : ∀ i c, region[i]? = some c → Wit.cellOK (BT.nleaves shp + 3 + i) c = true)
    (hseg : R.segRoots = (cHeapO ρ shp region [V]).2) (hn : R.n = 1)
    (hA : AcceptsCP R.A (cMachineO ρ shp region [V]) [] [] R.J R.root R.segRoots (cHeapO ρ shp region [V]).1.length
      R.n R.e R.row) {K : Nat} (hK : R.e 0 < K) :
    R.calls K = 1 := by
  have hA' := hA
  rw [hseg, hn] at hA'
  have hnr : ∀ i, isRestart R.e R.n i = false := fun i => by
    cases h : isRestart R.e R.n i
    · rfl
    · obtain ⟨j, hj, _⟩ := isRestart_iff.1 h; omega
  have he : R.e (R.n - 1) = R.e 0 := by rw [hn]
  obtain ⟨r0, hr0, hs0, hu⟩ := P2Once.once_of hp hg hV hb0 ho0 hr hA' R.jetAt (fun i hi => by
    cases hj : R.jetAt i with
    | false => exact .inl ⟨rfl, plain_row hA (by rw [he]; exact hi) (hnr i) hj⟩
    | true =>
      obtain ⟨_, hlt, hp2⟩ := jetAt_spec hj
      rw [rowQ_of_le (by omega), rowQ_of_le (by omega)] at hp2
      exact .inr ⟨rfl, hp2⟩)
  unfold calls
  refine filter_one R.jetAt (fun i => ⟨fun h => ?_, fun h => h ▸ hs0⟩) K (by omega)
  have := (jetAt_spec h).2.1
  exact hu i (by rw [← he]; exact this) h

end P2Run


namespace P2Run

variable {R : P2Run}

/-- **An honest run of one verifier in the frame meets `compP_transcript`'s
    hypotheses with the level table `idxPub 1`**: over the comb of 496 bits
    and the region, its tables balance with the public tables and one call,
    and their flags are clear. -/
theorem honest_zk_one {ρ : Nat → Bool} {region : List Cell} {V : OTerm} {G U : OTerm → Prop}
    (hp : P2Once.Part R.J G U) {g : OTerm} (hg : G g) (hV : V = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ g)
    (hroot : R.root = combRoot ρ (combBT 496) region)
    (hr : ∀ i c, region[i]? = some c → Wit.cellOK (496 + 3 + i) c = true)
    (hseg : R.segRoots = (cHeapO ρ (combBT 496) region [V]).2) (hn : R.n = 1)
    (hA : AcceptsCP R.A (cMachineO ρ (combBT 496) region [V]) [] [] R.J R.root R.segRoots
      (cHeapO ρ (combBT 496) region [V]).1.length R.n R.e R.row) {K : Nat} (hK : R.e 0 < K)
    (hd0 stk0 ctr0 J root : Nat) {heap : List Cell} {N W : Nat} {HI HO HP : Nat}
    (hML : R.A.length < P) (hnP : R.n < P)
    (hHI : (R.pinRows K).length ≤ HI) (hHO : (R.poutRows K).length ≤ HO) (hHP : (R.p2Rows K).length ≤ HP)
    (hHI0 : 0 < HI) (hHO0 : 0 < HO) (hHP0 : 0 < HP)
    (hpub : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + N + W) → i < R.A.length ∧ R.A.getD i .nil = heap.getD i .nil)
    (hbits : ∀ i, i < N → R.A.getD (3 + i) .nil = .K ∨ R.A.getD (3 + i) .nil = .app 0 1) (h496 : 496 ≤ N)
    (hreg : ∀ i, i < W → Wit.cellOK (3 + N + i) (R.A.getD (3 + N + i) .nil) = true)
    (hlenW : 3 + N + W ≤ R.A.length) :
    Balanced (compPTables hd0 stk0 ctr0 R.n (cHeapO ρ (combBT 496) region [V]).1.length J root heap N W R.segRoots
      (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n (cHeapO ρ (combBT 496) region [V]).1.length J root)
        (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (progTableC heap N W) (witTableP R.A N W) (segsPub R.segRoots) (R.pinTable K HI) (R.poutTable K HO)
      (R.p2Table K HP) (idxPub 1)) ∧
    UnblindedCP (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n (cHeapO ρ (combBT 496) region [V]).1.length J root)
        (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (witTableP R.A N W) (R.pinTable K HI) (R.poutTable K HO) (R.p2Table K HP) := by
  obtain ⟨hb0, ho0⟩ := comb_heap ρ region [V]
  rw [← hroot] at ho0
  have hN : BT.nleaves (combBT 496) = 496 := combBT_nleaves 496 (by decide)
  have hc := R.calls_one hp hg hV hb0 ho0 (by rw [hN]; exact hr) hseg hn hA hK
  have hK' : R.e (R.n - 1) < K := by rw [hn]; exact hK
  rw [← hc]
  exact honest_zkP hA hK' hd0 stk0 ctr0 J root hML (by rw [hseg, hn]; rfl) hnP hHI hHO hHP hHI0 hHO0 hHP0
    hpub hbits h496 hreg hlenW

/-- **The honest tables of `p2pre h` meet `compP_transcript`'s hypotheses with
    the level table `idxPub 1`.** -/
theorem honest_zk_p2pre (h : Nat) (hJ : R.J = ComposedPText.JP2)
    (hroot : R.root = combRoot ρ (combBT 496) region)
    (hr : ∀ i c, region[i]? = some c → Wit.cellOK (496 + 3 + i) c = true)
    (hseg : R.segRoots = (cHeapO ρ (combBT 496) region [ComposedPText.verifierO h]).2) (hn : R.n = 1)
    (hA : AcceptsCP R.A (cMachineO ρ (combBT 496) region [ComposedPText.verifierO h]) [] [] R.J R.root R.segRoots
      (cHeapO ρ (combBT 496) region [ComposedPText.verifierO h]).1.length R.n R.e R.row) {K : Nat} (hK : R.e 0 < K)
    (hd0 stk0 ctr0 J root : Nat) {heap : List Cell} {N W : Nat} {HI HO HP : Nat}
    (hML : R.A.length < P) (hnP : R.n < P)
    (hHI : (R.pinRows K).length ≤ HI) (hHO : (R.poutRows K).length ≤ HO) (hHP : (R.p2Rows K).length ≤ HP)
    (hHI0 : 0 < HI) (hHO0 : 0 < HO) (hHP0 : 0 < HP)
    (hpub : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + N + W) → i < R.A.length ∧ R.A.getD i .nil = heap.getD i .nil)
    (hbits : ∀ i, i < N → R.A.getD (3 + i) .nil = .K ∨ R.A.getD (3 + i) .nil = .app 0 1) (h496 : 496 ≤ N)
    (hreg : ∀ i, i < W → Wit.cellOK (3 + N + i) (R.A.getD (3 + N + i) .nil) = true)
    (hlenW : 3 + N + W ≤ R.A.length) :
    Balanced (compPTables hd0 stk0 ctr0 R.n (cHeapO ρ (combBT 496) region [ComposedPText.verifierO h]).1.length J root heap N W R.segRoots
      (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n (cHeapO ρ (combBT 496) region [ComposedPText.verifierO h]).1.length J root)
        (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (progTableC heap N W) (witTableP R.A N W) (segsPub R.segRoots) (R.pinTable K HI) (R.poutTable K HO)
      (R.p2Table K HP) (idxPub 1)) ∧
    UnblindedCP (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n (cHeapO ρ (combBT 496) region [ComposedPText.verifierO h]).1.length J root)
        (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (witTableP R.A N W) (R.pinTable K HI) (R.poutTable K HO) (R.p2Table K HP) := by
  have hV : ComposedPText.verifierO h = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.var R.J ⬝ₒ ComposedPText.checkO h) := by rw [hJ]; exact P2Once.verifierO_eq h
  exact honest_zk_one (G := P2Once.GP R.J) (U := P2Once.UP R.J) (P2Once.partP R.J) ⟨ComposedPText.checkO h, P2Once.checkO_free h R.J, rfl⟩ hV hroot hr hseg hn hA hK hd0 stk0 ctr0 J root hML hnP
    hHI hHO hHP hHI0 hHO0 hHP0 hpub hbits h496 hreg hlenW

/-- **The honest tables of `p2commit c pat` meet `compP_transcript`'s
    hypotheses with the level table `idxPub 1`.** -/
theorem honest_zk_p2commit (c : List Nat) (pat : List (Option Bool)) (hJ : R.J = ComposedPText.JP2)
    (hroot : R.root = combRoot ρ (combBT 496) region)
    (hr : ∀ i c, region[i]? = some c → Wit.cellOK (496 + 3 + i) c = true)
    (hseg : R.segRoots = (cHeapO ρ (combBT 496) region [ComposedPText.verifierC c pat]).2) (hn : R.n = 1)
    (hA : AcceptsCP R.A (cMachineO ρ (combBT 496) region [ComposedPText.verifierC c pat]) [] [] R.J R.root R.segRoots
      (cHeapO ρ (combBT 496) region [ComposedPText.verifierC c pat]).1.length R.n R.e R.row) {K : Nat} (hK : R.e 0 < K)
    (hd0 stk0 ctr0 J root : Nat) {heap : List Cell} {N W : Nat} {HI HO HP : Nat}
    (hML : R.A.length < P) (hnP : R.n < P)
    (hHI : (R.pinRows K).length ≤ HI) (hHO : (R.poutRows K).length ≤ HO) (hHP : (R.p2Rows K).length ≤ HP)
    (hHI0 : 0 < HI) (hHO0 : 0 < HO) (hHP0 : 0 < HP)
    (hpub : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + N + W) → i < R.A.length ∧ R.A.getD i .nil = heap.getD i .nil)
    (hbits : ∀ i, i < N → R.A.getD (3 + i) .nil = .K ∨ R.A.getD (3 + i) .nil = .app 0 1) (h496 : 496 ≤ N)
    (hreg : ∀ i, i < W → Wit.cellOK (3 + N + i) (R.A.getD (3 + N + i) .nil) = true)
    (hlenW : 3 + N + W ≤ R.A.length) :
    Balanced (compPTables hd0 stk0 ctr0 R.n (cHeapO ρ (combBT 496) region [ComposedPText.verifierC c pat]).1.length J root heap N W R.segRoots
      (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n (cHeapO ρ (combBT 496) region [ComposedPText.verifierC c pat]).1.length J root)
        (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (progTableC heap N W) (witTableP R.A N W) (segsPub R.segRoots) (R.pinTable K HI) (R.poutTable K HO)
      (R.p2Table K HP) (idxPub 1)) ∧
    UnblindedCP (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n (cHeapO ρ (combBT 496) region [ComposedPText.verifierC c pat]).1.length J root)
        (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (witTableP R.A N W) (R.pinTable K HI) (R.poutTable K HO) (R.p2Table K HP) := by
  have hV : ComposedPText.verifierC c pat = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.var R.J ⬝ₒ ComposedPText.checkC c) ⬝ₒ ComposedPText.patO pat) := by rw [hJ]; exact P2Once.verifierC_eq c pat
  exact honest_zk_one (G := P2Once.GC R.J) (U := P2Once.UC R.J) (P2Once.partC R.J) ⟨ComposedPText.checkC c, ComposedPText.patO pat, P2Commit.checkC_closed c R.J, P2Commit.patO_closed R.J pat, rfl⟩ hV hroot hr hseg hn hA hK hd0 stk0 ctr0 J root hML hnP
    hHI hHO hHP hHI0 hHO0 hHP0 hpub hbits h496 hreg hlenW

end P2Run

end Circuit
