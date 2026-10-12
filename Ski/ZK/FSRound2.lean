import Ski.ZK.FSRounds

/-!
# The second round under Fiat–Shamir: `ζ` hashed

The second round hashes a second commitment, of data the prover computes
after the LogUp challenges (its permutation columns and quotient
chunks), into the out-of-domain point `ζ`.  `pc_two`: summed over every
generic `ζ`, the transcript bound at each `ζ` and two hiding commitments
give the two-round public-coin bound `fs_zk2` asks; `sud_fs2` applies it
to the Sudoku proof.

Scope.  Both commitments hide perfectly and neither is opened in the
view (`ComHides`, as `Ski/ZK/FSInst.lean` for the first round); the FRI
challenge and the query points stay fixed parameters; one proof per
oracle; generic `β` and `ζ`.
-/

namespace Circuit

open ZKF B Air Stmt Mach Sudoku SudokuText

-- ---------------------------------------------------------------------------
-- The randomness does not depend on `ζ`
-- ---------------------------------------------------------------------------

theorem mtotal_congr : ∀ (gs gs' : List MGroup) (ks : List Nat), gs.map MGroup.n = gs'.map MGroup.n →
    mtotal gs ks = mtotal gs' ks
  | [], [], _, _ => rfl
  | g :: gs, g' :: gs', k :: ks, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    show k * g.n + mtotal gs ks = k * g'.n + mtotal gs' ks
    rw [h.1, mtotal_congr gs gs' ks h.2]
  | _ :: _, _ :: _, [], _ => rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

theorem traceCw_congr (ncw : Nat) : ∀ (gs gs' : List MGroup), gs.map MGroup.dom = gs'.map MGroup.dom →
    traceCw ncw gs = traceCw ncw gs'
  | [], [], _ => rfl
  | g :: gs, g' :: gs', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    show ncw * g.dom.length + traceCw ncw gs = ncw * g'.dom.length + traceCw ncw gs'
    rw [h.1, traceCw_congr ncw gs gs' h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem tabsCr_congr : ∀ (ts ts' : List QTab), ts.map (fun T => (T.tg.length, T.cs.length, T.h)) =
    ts'.map (fun T => (T.tg.length, T.cs.length, T.h)) → tabsCr ts = tabsCr ts'
  | [], [], _ => rfl
  | T :: ts, T' :: ts', h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    show T.tg.length * (T.cs.length * T.h) + tabsCr ts = T'.tg.length * (T'.cs.length * T'.h) + tabsCr ts'
    rw [h.1.1, h.1.2.1, h.1.2.2, tabsCr_congr ts ts' h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem tabsCw_congr (ncw : Nat) : ∀ (ts ts' : List QTab), ts.map (fun T => (T.tg.length, T.cs.length, T.h)) =
    ts'.map (fun T => (T.tg.length, T.cs.length, T.h)) → tabsCw ncw ts = tabsCw ncw ts'
  | [], [], _ => rfl
  | T :: ts, T' :: ts', h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    show ncw * ((T.cs.length + 1) * T.h) + ncw * (T.cs.length * T.h) + tabsCw ncw ts =
      ncw * ((T'.cs.length + 1) * T'.h) + ncw * (T'.cs.length * T'.h) + tabsCw ncw ts'
    rw [h.1.2.1, h.1.2.2, tabsCw_congr ncw ts ts' h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

set_option maxRecDepth 100000 in
/-- **The Sudoku PCS's randomness does not depend on `ζ`.** -/
theorem sudNR_zeta (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (tp : Nat)
    (S16 S10 SP : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) (ncw : Nat) :
    sudNR off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp ncw =
      sudNR off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ' qv wm wc ww wp ncw := by
  have ht : ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst).map
        (fun T => (T.tg.length, T.cs.length, T.h)) =
      ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ' qv wm wc ww wp).map Prod.fst).map
        (fun T => (T.tg.length, T.cs.length, T.h)) := by
    simp only [sudTs, bbTab, airQTabG, List.map_cons, List.map_nil, List.length_map]
  have hn : ((sudGroups tp S16 S10 SP ζ qv).map QGroup.ext).map MGroup.n =
      ((sudGroups tp S16 S10 SP ζ' qv).map QGroup.ext).map MGroup.n := rfl
  have hd : ((sudGroups tp S16 S10 SP ζ qv).map QGroup.ext).map MGroup.dom =
      ((sudGroups tp S16 S10 SP ζ' qv).map QGroup.ext).map MGroup.dom := rfl
  unfold sudNR friN1 friN2
  rw [mtotal_congr _ _ _ hn, tabsCr_congr _ _ ht, traceCw_congr ncw _ _ hd, tabsCw_congr ncw _ _ ht]

/-- **Two hiding commitments beside a transcript**, at one second
    challenge. -/
theorem pc_two_core {PV PB D1 D2 : Type} {NR m e1 e2 NS1 NS2 : Nat}
    (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (hc1 : ComHides NS1 Com1) (Com2 : D2 → Nat → Nat) (hc2 : ComHides NS2 Com2)
    (main1 : (Nat → Tup) → Nat → D1) (main2 : Nat → (Nat → Tup) → Nat → D2) (d1 : D1) (d2 : D2)
    (F : Nat → Nat → Nat → TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c1 => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r =>
      sumN m (fun t => indB (genB (efOf (c1 % Q4)) && F c1 (Com1 (main1 t r) σ1)
        (Com2 (main2 c1 t r) σ2) (rv (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t))))))) ≤
    sumTo (Q4 * Q4) (fun c1 => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r =>
      sumN m (fun t => indB (genB (efOf (c1 % Q4)) && F c1 (Com1 d1 σ1) (Com2 d2 σ2)
        (sv (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t))))))) + NS1 * (NS2 * (e1 + e2)) := by
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  -- the second commitment, then the first, swapped for fixed data
  have sw : ∀ c1, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c1 % Q4)) && F c1 (Com1 (main1 t r) σ1) (Com2 (main2 c1 t r) σ2)
        (rv (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t)))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c1 % Q4)) && F c1 (Com1 d1 σ1) (Com2 d2 σ2)
          (rv (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t)))))) := fun c1 => by
    rw [sumTo_congr _ (fun σ1 _ => com_swap Com2 hc2 (main2 c1) d2
      (fun r t cm => genB (efOf (c1 % Q4)) && F c1 (Com1 (main1 t r) σ1) cm (rv (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t)))]
    rw [sumTo_exch _ NS2 NS1]
    exact sumTo_congr _ (fun σ2 _ => com_swap Com1 hc1 main1 d1
      (fun r t cm => genB (efOf (c1 % Q4)) && F c1 cm (Com2 d2 σ2) (rv (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t)))
  have ex : ∀ (v : EF → EF → Nat → (Nat → Tup) → TViewN PV PB),
      sumTo (Q4 * Q4) (fun c1 => sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c1 % Q4)) && F c1 (Com1 d1 σ1) (Com2 d2 σ2) (v (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t))))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && F (efIdx β + Q4 * efIdx α) (Com1 d1 σ1) (Com2 d2 σ2) (v α β r t))))) := fun v => by
    rw [sumTo_exch _ NS2 (Q4 * Q4)]
    refine sumTo_congr _ (fun σ2 _ => ?_)
    rw [sumTo_exch _ NS1 (Q4 * Q4)]
    exact sumTo_congr _ (fun σ1 _ => csum_tsumN v (fun c w => F c (Com1 d1 σ1) (Com2 d2 σ2) w))
  have exS : sumTo (Q4 * Q4) (fun c1 => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r =>
      sumN m (fun t => indB (genB (efOf (c1 % Q4)) && F c1 (Com1 d1 σ1) (Com2 d2 σ2)
        (sv (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t))))))) =
      sumTo (Q4 * Q4) (fun c1 => sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c1 % Q4)) && F c1 (Com1 d1 σ1) (Com2 d2 σ2) (sv (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t))))))) :=
    sumTo_congr _ (fun c1 _ => sumTo_exch _ NS2 NS1)
  rw [sumTo_congr _ (fun c1 _ => sw c1), ex rv, exS, ex sv]
  calc sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && F (efIdx β + Q4 * efIdx α) (Com1 d1 σ1) (Com2 d2 σ2) (rv α β r t)))))
      ≤ sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && F (efIdx β + Q4 * efIdx α) (Com1 d1 σ1) (Com2 d2 σ2) (sv α β r t))) + (e1 + e2))) :=
        sumTo_mono _ (fun σ2 _ => sumTo_mono _ (fun σ1 _ => (tsumN_ab rv sv hrv hsv h1' h2' _).1))
    _ = _ := by
      simp only [sumTo_add, sumTo_const, Nat.mul_add]
      ac_rfl

/-- **Two hiding commitments beside a transcript, summed over a second
    challenge**: where the transcript bound holds at each guarded second
    challenge `c₂`, the count with the commitments of the prover's data is
    within `K₂ · NS₁ · NS₂ · (e1 + e2)` of the count with fixed data. -/
theorem pc_two {PV PB D1 D2 : Type} {NR m e1 e2 NS1 NS2 K2 : Nat}
    (rv sv : Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Bool)
    (hrv : ∀ c2 α β r t, rv c2 α β r t = none ∨ ∃ p x y, rv c2 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 α β r t, ∃ p x y, sv c2 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) + e1 + e2)
    (h2 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (hc1 : ComHides NS1 Com1) (Com2 : D2 → Nat → Nat) (hc2 : ComHides NS2 Com2)
    (main1 : (Nat → Tup) → Nat → D1) (main2 : Nat → (Nat → Tup) → Nat → D2) (d1 : D1) (d2 : D2)
    (F : Nat → Nat → Nat → Nat → TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r =>
      sumN m (fun t => indB ((genB (efOf (c1 % Q4)) && gz c2) && F c1 c2 (Com1 (main1 t r) σ1)
        (Com2 (main2 c1 t r) σ2) (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t)))))))) ≤
    sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r =>
      sumN m (fun t => indB ((genB (efOf (c1 % Q4)) && gz c2) && F c1 c2 (Com1 d1 σ1) (Com2 d2 σ2)
        (sv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) r t)))))))) + K2 * (NS1 * (NS2 * (e1 + e2))) := by
  rw [sumTo_exch _ K2 (Q4 * Q4), sumTo_exch _ K2 (Q4 * Q4), ← sumTo_const (NS1 * (NS2 * (e1 + e2))) K2, ← sumTo_add]
  refine sumTo_mono _ (fun c2 _ => ?_)
  cases hg : gz c2
  · simp only [Bool.and_false, Bool.false_and]
    exact Nat.le_add_right _ _
  · simp only [Bool.and_true]
    exact pc_two_core (rv c2) (sv c2) (hrv c2) (hsv c2) (h1 c2 hg) (h2 c2 hg) Com1 hc1 Com2 hc2 main1 main2 d1 d2
      (fun c1 a b v => F c1 c2 a b v)


-- ---------------------------------------------------------------------------
-- The Sudoku proof, `ζ` hashed
-- ---------------------------------------------------------------------------

set_option maxRecDepth 100000 in
/-- **The Sudoku proof under Fiat–Shamir over two rounds**, in the
    programmable random-oracle model: the LogUp challenges are the first
    oracle table's answer at the commitment `Com1` of the prover's first
    message, `ζ` the second table's at the commitment `Com2` of its
    second (any data it computes after the LogUp challenges).  `Q4² · Q4`
    times the real count is within `(Q4²)^n1 · Q4^n2 · Q4 · NS1 · NS2 ·
    err` of the simulator's, which commits to fixed data, draws both
    challenges, simulates at them and programs both tables.  Neither
    commitment is opened in the view; the FRI challenge and the query
    points stay fixed. -/
theorem sud_fs2 {V Wv D1 D2 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    {S16 S10 SP : List F} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F))
    (hS16 : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz16 : 2 * S16.length + 8 ≤ 2 ^ 16) (hsz : 2 * S10.length + 8 ≤ 2 ^ 10)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hncw : 4 ≤ ncw) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS1 NS2 n1 n2 : Nat} (Com1 : D1 → Nat → Nat) (hc1 : ComHides NS1 Com1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (Com2 : D2 → Nat → Nat) (hc2 : ComHides NS2 Com2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (main1 : (Nat → Tup) → Nat → D1) (main2 : Nat → (Nat → Tup) → Nat → D2) (d1 : D1) (d2 : D2)
    (E : Nat → Nat → Nat → Nat → TViewN (SudPV (V × Wv)) EF → Bool) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP EF.zero qv wm wc ww wp ncw
    let pcsZ := fun (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ
      qv wm wc ww wp ncw αb (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psimZ := fun (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP
      ζ qv wm wc ww wp ncw αb (friX fri Rb Ro (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ2, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1
    let rv := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      realVN off tabs tv tp (pcsZ (efOf c2)) (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2
    let sv := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ (efOf c2)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
        x.2.2.1 x.2.2.2
    let gd := fun (c1 c2 : Nat) => genB (efOf (c1 % Q4)) && genB (efOf c2)
    let err := Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0))
    (Q4 * Q4) * (Q4 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (Q4 ^ n2) (fun H2 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget Q4 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rv (rget (Q4 * Q4) (m1 x) H1) (rget Q4 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (Q4 ^ n2) (fun H2 => sumTo (Q4 * Q4) (fun c1 => sumTo Q4 (fun c2 =>
      sm (fun x => indB (gd c1 c2 && E (rset (Q4 * Q4) (Com1 d1 x.1) H1 c1) (rset Q4 (Com2 d2 x.2.1) H2 c2)
        (Com1 d1 x.1) (Com2 d2 x.2.1) (sv c1 c2 x))))))) +
      (Q4 * Q4) ^ n1 * (Q4 ^ n2 * (Q4 * (NS1 * (NS2 * err)))) := by
  intro blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv tp M sm m1 m2 rv sv gd err
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sms, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨hP23, hPg⟩ := sud_prog_height hc hA hlen
  rw [← htp] at hP23 hPg
  have hb : ∀ c2, genB (efOf c2) = true →
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (realVN off tabs tv tp (pcsZ (efOf c2)) α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (simVN off tp chainBus (fun _ => false) chainPar 3 tp
            (psimZ (efOf c2)) α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (simVN off tp chainBus (fun _ => false) chainPar 3 tp
            (psimZ (efOf c2)) α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (realVN off tabs tv tp (pcsZ (efOf c2)) α β r t))) +
            Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c2 hg => by
    have hgz := (genB_iff _).1 hg
    have hpcs := sud_pcsX (heap := blank.heap) (ζ := efOf c2) off sc sms sw (rfl : C.h = 2 ^ 16) hlen
      (rfl : Wt.h = 2 ^ 10) (by omega) hPg qv wm wc ww wp hS16 hS10 hSP hsz16 hsz hszP (generic_ofF_ne hgz)
      (mz_generic hgz) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
    rw [sudNR_zeta off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c2) EF.zero qv
      wm wc ww wp ncw] at hpcs
    exact ⟨fun E' => (sud_transcriptG off NR 0 (pcsZ (efOf c2)) (psimZ (efOf c2)) hbal hun hpcs E').1,
      fun E' => (sud_transcriptG off NR 0 (pcsZ (efOf c2)) (psimZ (efOf c2)) hbal hun hpcs E').2⟩
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN 2 (fun t =>
      sumTo N (fun i => f i (σ1, σ2, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2) (NR := NR) (m := 2) (N := N)
      (fun i σ2 r t => f i (σ1, σ2, r, t)))]
    exact sumTo_exch _ N NS1
  exact fs_zk2 (K1 := Q4 * Q4) (K2 := Q4) (n1 := n1) (n2 := n2) (Nat.mul_pos Q4_pos Q4_pos) Q4_pos sm hsm m1 m2
    (fun x => hr1 _ _) (fun _ x => hr2 _ _) (fun _ _ x => Com1 d1 x.1) (fun _ _ x => Com2 d2 x.2.1) rv sv gd
    (fun F => pc_two (fun c2 α β r t => realVN off tabs tv tp (pcsZ (efOf c2)) α β r t)
      (fun c2 α β r t => simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ (efOf c2)) α β r t)
      (fun c2 => genB (efOf c2)) (fun c2 α β r t => realVN_cases _ _ _ _ _ α β r t)
      (fun c2 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) (fun c2 hg => (hb c2 hg).1) (fun c2 hg => (hb c2 hg).2)
      Com1 hc1 Com2 hc2 main1 main2 d1 d2 F) E

end Circuit
