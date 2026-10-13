import Ski.ZK.FSOpen3Inst
import Ski.Circuit.ProbeBal

/-!
# The query points under Fiat–Shamir

Plonky3 draws its query points from the transcript after every
commitment.  The committed data do not read the query points: the masked
polynomials read a group's trace and mask points and its size, never `S`
(`SameData`, `sud_same_d`, `sud_data_q`).  So the points are a fourth
challenge: the commitments stay as they are, and the views open them at
the drawn points.  Hashing a fourth table at the third message turns a
bound that holds at every fourth challenge into the Fiat–Shamir bound with
the fourth table programmed (`fs_last`, `fs_lastR`); over `fs_open3U` it
gives four rounds with every commitment opened (`fs_open4`, `fs_open4R`),
and the Sudoku proof with its query points hashed (`sud_fs_open4`).  The
FRI challenge is decoded from the same fourth challenge; the draws where
it fails the verifier's test enter the bound as their whole count
(`fs_lastG`, `fs_lastGR`).  The query hash's input is any function `φ` of
the commitments' transcript; with a proof-of-work nonce ground against a
table of its own, independent of the query table, the bound holds at every
such table and summed over them (`fs_pow`, a usage note rather than one
composed theorem).  The lookup nonce, before the LogUp challenges, enters
the same way through the first commitment (`ComHides.post`,
`ComPfHides.post`).
-/

namespace Circuit

open ZKF

/-- **Shapes without the query points**: what the committed data read. -/
structure SameData (qs qs' : List QGroup) (tabs tabs' : List QTab) : Prop where
  trn : (qs.map QGroup.ext).map (fun g => (g.T, g.R, g.n)) = (qs'.map QGroup.ext).map (fun g => (g.T, g.R, g.n))
  dom : (qs.map QGroup.ext).map MGroup.dom = (qs'.map QGroup.ext).map MGroup.dom
  shape : tabs.map tShape = tabs'.map tShape

theorem SameData.hn {qs qs' : List QGroup} {tabs tabs' : List QTab}
    (h : SameData qs qs' tabs tabs') : (qs.map QGroup.ext).map MGroup.n = (qs'.map QGroup.ext).map MGroup.n := by
  have := congrArg (List.map (fun x : List F × List F × Nat => x.2.2)) h.trn
  simp only [List.map_map] at this ⊢
  exact this

theorem SameData.ht {qs qs' : List QGroup} {tabs tabs' : List QTab}
    (h : SameData qs qs' tabs tabs') :
    tabs.map (fun T => (T.tg.length, T.cs.length, T.h)) = tabs'.map (fun T => (T.tg.length, T.cs.length, T.h)) := by
  have := congrArg (List.map (fun x : Nat × List Chunk × List F × F × Nat => (x.2.2.2.2, x.2.1.length, x.1))) h.shape
  simp only [List.map_map] at this
  exact this

theorem SameData.n1 {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab}
    (h : SameData qs qs' tabs tabs') : friN1 qs ks tabs = friN1 qs' ks tabs' := by
  unfold friN1; rw [mtotal_congr _ _ ks h.hn, tabsCr_congr tabs tabs' h.ht]

theorem SameData.n2 {qs qs' : List QGroup} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameData qs qs' tabs tabs') : friN2 qs tabs ncw = friN2 qs' tabs' ncw := by
  unfold friN2; rw [traceCw_congr ncw _ _ h.dom, tabsCw_congr ncw tabs tabs' h.ht]

theorem SameData.ms {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameData qs qs' tabs tabs') (ρ : Nat) : msF qs ks tabs ncw ρ = msF qs' ks tabs' ncw ρ := by
  unfold msF; rw [h.n1, h.n2, mtotal_congr _ _ ks h.hn]

theorem SameData.ct {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameData qs qs' tabs tabs') (ρ : Nat) : ctF qs ks tabs ncw ρ = ctF qs' ks tabs' ncw ρ := by
  unfold ctF; rw [h.n1, h.n2, traceCw_congr ncw _ _ h.dom]

theorem SameData.cr {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameData qs qs' tabs tabs') (ρ : Nat) : crF qs ks tabs ncw ρ = crF qs' ks tabs' ncw ρ := by
  unfold crF; rw [h.n1, h.n2, mtotal_congr _ _ ks h.hn]

theorem SameData.cc {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameData qs qs' tabs tabs') (ρ : Nat) : ccF qs ks tabs ncw ρ = ccF qs' ks tabs' ncw ρ := by
  unfold ccF; rw [h.n1, h.n2, traceCw_congr ncw _ _ h.dom]

/-- **The committed data read the shape only.** -/
theorem SameData.dataF2 {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameData qs qs' tabs tabs') (cols : (Nat → Tup) → EF → EF → List (List (List F))) (mk : List Nat)
    (t : Nat → Tup) (ρ : Nat) : mainF2 qs ks cols tabs ncw mk t ρ = mainF2 qs' ks cols tabs' ncw mk t ρ := by
  unfold mainF2; rw [h.ms, h.ct, mpolysMulti_congr _ _ _ _ h.trn, traceCws_congr ncw _ _ _ h.dom]

theorem SameData.dataP2 {qs qs' : List QGroup} {ks : List Nat} {tabs tabs' : List QTab} {ncw : Nat}
    (h : SameData qs qs' tabs tabs') (cols : (Nat → Tup) → EF → EF → List (List (List F))) (mk : List Nat)
    (t : Nat → Tup) (α β : EF) (ρ : Nat) :
    mainP2 qs ks cols tabs ncw mk t α β ρ = mainP2 qs' ks cols tabs' ncw mk t α β ρ := by
  unfold mainP2; rw [h.ms, h.ct, mpolysMulti_congr _ _ _ _ h.trn, traceCws_congr ncw _ _ _ h.dom]

section
open B Air Stmt Mach Sudoku SudokuText

/-- The Sudoku quotient data read neither the query points nor `ζ`, without an abort. -/
theorem sud_data_q (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (tp : Nat)
    (S16 S10 SP S16' S10' SP' : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) (t : Nat → Tup) (α β : EF) (ms : List F)
    (h : Aborts (prefixOf α (off β)) β (sudTabs hd0 stk0 ctr0 heap C Mm Wt t) = false) :
    (sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map (fun p => p.2 t α β ms) =
      (sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16' S10' SP' ζ' qv wm wc ww wp).map (fun p => p.2 t α β ms) := by
  have hg : ∀ tss rs, mpolysMulti ((sudGroups tp S16 S10 SP ζ qv).map QGroup.ext) tss rs =
      mpolysMulti ((sudGroups tp S16' S10' SP' ζ' qv).map QGroup.ext) tss rs := fun tss rs =>
    mpolysMulti_congr _ _ _ _ rfl
  simp only [sudTs, bbData, List.map_cons, List.map_nil, h, if_true, hg]

set_option maxRecDepth 100000 in
/-- **The Sudoku PCS's data shape reads neither the query points, nor `ζ`,
    nor the weights beyond their lengths.** -/
theorem sud_same_d (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (tp : Nat)
    (S16 S10 SP S16' S10' SP' : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wm' wc' ww' wp' : List (EF → EF → List F))
    (hm : wm.length = wm'.length) (hc : wc.length = wc'.length) (hw : ww.length = ww'.length)
    (hp : wp.length = wp'.length) :
    SameData (sudGroups tp S16 S10 SP ζ qv) (sudGroups tp S16' S10' SP' ζ' qv)
      ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst)
      ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16' S10' SP' ζ' qv wm' wc' ww' wp').map Prod.fst) where
  trn := rfl
  dom := rfl
  shape := by
    simp only [sudTs, bbTab, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hm, hc, hw, hp]
end

/-- **One more round, innermost**: a fourth table hashed at a message `M`,
    over a bound that holds at every fourth challenge `c4` for every event
    `G` of the message and the view.  `K4 K` times the real count with the
    fourth challenge read from the table is at most the simulator's, which
    programs the fourth table at its own message, plus `K4^n4 K4 ε`. -/
theorem fs_last {Y Vw : Type} {K4 n4 K ε : Nat} (hK4 : 0 < K4) (sm : (Y → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → Y → Nat), sm (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm (f i)))
    (M : Y → Nat) (hM : ∀ y, M y < n4) (rv : Nat → Y → Vw) (Sim : Nat → (Nat → Vw → Bool) → Nat)
    (hb : ∀ c4 (G : Nat → Vw → Bool), K * sm (fun y => indB (G (M y) (rv c4 y))) ≤ Sim c4 G + ε)
    (E : Nat → Nat → Nat → Vw → Bool) :
    K4 * (K * sumTo (K4 ^ n4) (fun H4 => sm (fun y => indB (E H4 (M y) (rget K4 (M y) H4) (rv (rget K4 (M y) H4) y))))) ≤
      sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim c4 (fun m v => E (rset K4 m H4 c4) m c4 v))) +
        K4 ^ n4 * (K4 * ε) := by
  rw [Nat.mul_left_comm, fs_real hK4 sm hsm M hM rv E, sumTo_mul]
  calc sumTo (K4 ^ n4) (fun H4 => K * sumTo K4 (fun c4 => sm (fun y => indB (E (rset K4 (M y) H4 c4) (M y) c4 (rv c4 y)))))
      ≤ sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim c4 (fun m v => E (rset K4 m H4 c4) m c4 v) + ε)) :=
        sumTo_mono _ (fun H4 _ => by
          rw [sumTo_mul]
          exact sumTo_mono _ (fun c4 _ => hb c4 (fun m v => E (rset K4 m H4 c4) m c4 v)))
    _ = _ := by simp only [sumTo_add, sumTo_const]

/-- **`fs_last` the other way.** -/
theorem fs_lastR {Y Vw : Type} {K4 n4 K ε : Nat} (hK4 : 0 < K4) (sm : (Y → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → Y → Nat), sm (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm (f i)))
    (M : Y → Nat) (hM : ∀ y, M y < n4) (rv : Nat → Y → Vw) (Sim : Nat → (Nat → Vw → Bool) → Nat)
    (hb : ∀ c4 (G : Nat → Vw → Bool), Sim c4 G ≤ K * sm (fun y => indB (G (M y) (rv c4 y))) + ε)
    (E : Nat → Nat → Nat → Vw → Bool) :
    sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim c4 (fun m v => E (rset K4 m H4 c4) m c4 v))) ≤
      K4 * (K * sumTo (K4 ^ n4) (fun H4 => sm (fun y => indB (E H4 (M y) (rget K4 (M y) H4) (rv (rget K4 (M y) H4) y))))) +
        K4 ^ n4 * (K4 * ε) := by
  rw [Nat.mul_left_comm, fs_real hK4 sm hsm M hM rv E, sumTo_mul]
  calc sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim c4 (fun m v => E (rset K4 m H4 c4) m c4 v)))
      ≤ sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 =>
          K * sm (fun y => indB (E (rset K4 (M y) H4 c4) (M y) c4 (rv c4 y))) + ε)) :=
        sumTo_mono _ (fun H4 _ => sumTo_mono _ (fun c4 _ => hb c4 (fun m v => E (rset K4 m H4 c4) m c4 v)))
    _ = _ := by simp only [sumTo_add, sumTo_const, sumTo_mul]

/-- **The uniformly decoded FRI challenge**: decoded as `efOf (c4 % Q4)`
    from `Q4 k` fourth challenges, `P²` in every `Q4` fail the verifier's
    test (`genB_count`). -/
theorem genB_count_mod (k : Nat) : sumTo (Q4 * k) (fun c4 => indB (!genB (efOf (c4 % Q4)))) = k * (P * P) := by
  rw [sumTo_split Q4 _ k]
  have e : ∀ q, sumTo Q4 (fun r => indB (!genB (efOf ((r + Q4 * q) % Q4)))) = P * P := fun q => by
    rw [← genB_count]
    refine sumTo_congr _ (fun r hr => ?_)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  rw [sumTo_congr _ (fun q _ => e q), sumTo_const]

/-- **`fs_last` with excluded fourth challenges**: the bound holds at the
    fourth challenges `g4` admits; the others, at most `B4` of the `K4`, enter
    as their whole count `K sm 1`. -/
theorem fs_lastG {Y Vw : Type} {K4 n4 K ε B4 : Nat} (hK4 : 0 < K4) (sm : (Y → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → Y → Nat), sm (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm (f i)))
    (M : Y → Nat) (hM : ∀ y, M y < n4) (rv : Nat → Y → Vw) (Sim : Nat → (Nat → Vw → Bool) → Nat)
    (g4 : Nat → Bool) (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hb : ∀ c4, g4 c4 = true → ∀ G : Nat → Vw → Bool, K * sm (fun y => indB (G (M y) (rv c4 y))) ≤ Sim c4 G + ε)
    (E : Nat → Nat → Nat → Vw → Bool) :
    K4 * (K * sumTo (K4 ^ n4) (fun H4 => sm (fun y => indB (E H4 (M y) (rget K4 (M y) H4) (rv (rget K4 (M y) H4) y))))) ≤
      sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim c4 (fun m v => E (rset K4 m H4 c4) m c4 v))) +
        K4 ^ n4 * (K4 * ε + B4 * (K * sm (fun _ => 1))) := by
  have hone : ∀ f : Y → Nat, (∀ y, f y ≤ 1) → K * sm f ≤ K * sm (fun _ => 1) := fun f hf =>
    Nat.mul_le_mul_left _ (sm_mono sm hsm hf)
  rw [Nat.mul_left_comm, fs_real hK4 sm hsm M hM rv E, sumTo_mul]
  calc sumTo (K4 ^ n4) (fun H4 => K * sumTo K4 (fun c4 => sm (fun y => indB (E (rset K4 (M y) H4 c4) (M y) c4 (rv c4 y)))))
      ≤ sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim c4 (fun m v => E (rset K4 m H4 c4) m c4 v) + ε +
          indB (!g4 c4) * (K * sm (fun _ => 1)))) :=
        sumTo_mono _ (fun H4 _ => by
          rw [sumTo_mul]
          refine sumTo_mono _ (fun c4 _ => ?_)
          cases hg : g4 c4
          · rw [Bool.not_false, show indB true = 1 from rfl, Nat.one_mul]
            exact Nat.le_trans (hone _ (fun y => indB_le _)) (Nat.le_add_left _ _)
          · rw [Bool.not_true, show indB false = 0 from rfl, Nat.zero_mul, Nat.add_zero]
            exact hb c4 hg (fun m v => E (rset K4 m H4 c4) m c4 v))
    _ ≤ _ := by
      simp only [sumTo_add, sumTo_const, sumTo_mul_right]
      rw [Nat.mul_add (K4 ^ n4), ← Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hB4)) _

/-- **`fs_lastG` the other way**: at an excluded fourth challenge the
    simulator's count is at most its whole count `K sm 1`. -/
theorem fs_lastGR {Y Vw : Type} {K4 n4 K ε B4 : Nat} (hK4 : 0 < K4) (sm : (Y → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → Y → Nat), sm (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm (f i)))
    (M : Y → Nat) (hM : ∀ y, M y < n4) (rv : Nat → Y → Vw) (Sim : Nat → (Nat → Vw → Bool) → Nat)
    (g4 : Nat → Bool) (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hS1 : ∀ c4 (G : Nat → Vw → Bool), Sim c4 G ≤ K * sm (fun _ => 1))
    (hb : ∀ c4, g4 c4 = true → ∀ G : Nat → Vw → Bool, Sim c4 G ≤ K * sm (fun y => indB (G (M y) (rv c4 y))) + ε)
    (E : Nat → Nat → Nat → Vw → Bool) :
    sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim c4 (fun m v => E (rset K4 m H4 c4) m c4 v))) ≤
      K4 * (K * sumTo (K4 ^ n4) (fun H4 => sm (fun y => indB (E H4 (M y) (rget K4 (M y) H4) (rv (rget K4 (M y) H4) y))))) +
        K4 ^ n4 * (K4 * ε + B4 * (K * sm (fun _ => 1))) := by
  rw [Nat.mul_left_comm, fs_real hK4 sm hsm M hM rv E, sumTo_mul]
  calc sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 => Sim c4 (fun m v => E (rset K4 m H4 c4) m c4 v)))
      ≤ sumTo (K4 ^ n4) (fun H4 => sumTo K4 (fun c4 =>
          K * sm (fun y => indB (E (rset K4 (M y) H4 c4) (M y) c4 (rv c4 y))) + ε +
          indB (!g4 c4) * (K * sm (fun _ => 1)))) :=
        sumTo_mono _ (fun H4 _ => sumTo_mono _ (fun c4 _ => by
          cases hg : g4 c4
          · rw [Bool.not_false, show indB true = 1 from rfl, Nat.one_mul]
            exact Nat.le_trans (hS1 c4 _) (Nat.le_add_left _ _)
          · rw [Bool.not_true, show indB false = 0 from rfl, Nat.zero_mul, Nat.add_zero]
            exact hb c4 hg (fun m v => E (rset K4 m H4 c4) m c4 v)))
    _ ≤ _ := by
      simp only [sumTo_add, sumTo_const, sumTo_mul_right, ← sumTo_mul]
      rw [Nat.mul_add (K4 ^ n4), ← Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hB4)) _

/-- **Hiding survives post-processing**: a function of a hiding
    commitment hides.  The lookup proof-of-work nonce precedes the LogUp
    challenges, so the first hash reads the commitment with its nonce,
    `g c := (c, nonce c)`, a function of the commitment for each
    proof-of-work table; the theorems then apply to `g ∘ Com1`, and `fs_pow`
    sums over the tables. -/
theorem ComHides.post {D C C' : Type} {NS : Nat} {Com : D → Nat → C} (h : ComHides NS Com) (g : C → C') :
    ComHides NS (fun d σ => g (Com d σ)) :=
  fun d d' E => h d d' (fun c => E (g c))

theorem ComPfHides.post {D O Pp : Type} {NS : Nat} {Com : D → Nat → Nat} {Pf : D → Nat → Pp} {op : D → O}
    (h : ComPfHides NS Com Pf op) (g : Nat → Nat) : ComPfHides NS (fun d σ => g (Com d σ)) Pf op :=
  fun d d' hd E => h d d' hd (fun c p => E (g c) p)

/-- **A table nobody programs**, such as the proof-of-work oracle's: a
    bound at every such table holds summed over the tables, for a
    distinguisher that reads the table.  Used with `fs_open4` at
    `φ m := (m, nonce m)`, the nonce a total function of the table and `m`
    with one bound `N4` for every table; the proof-of-work table is assumed
    independent of the query table (Plonky3 grinds and samples on one
    duplex challenger, modelled here as independent components on one
    input). -/
theorem fs_pow {NP e : Nat} (A B : Nat → Nat) (h : ∀ HP, A HP ≤ B HP + e) :
    sumTo NP A ≤ sumTo NP B + NP * e := by
  rw [← sumTo_const e NP, ← sumTo_add]
  exact sumTo_mono _ (fun HP _ => h HP)

/-- **Fiat–Shamir over four rounds, every commitment opened**: `fs_open3U`
    with the query points a fourth challenge `c4`, hashed into a fourth
    table at `φ` of the third message: any function of the commitments'
    transcript, such as the transcript with the proof-of-work nonce ground
    against a table of its own.  The
    commitments do not read `c4`; the views, their opened values, the
    opening proofs (Merkle paths at the drawn indices) and the simulator's
    openings do.  Each commitment hides given its openings and opening
    proof at every `c4`; the transcript bounds `h1`, `h2` hold at the `c4`
    the guard `g4` admits, and the others, at most `B4`, enter the bound
    as their whole count.  Unguarded; one proof per oracle. -/
theorem fs_open4 {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 K4 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φ : Nat → Nat) {N4 : Nat} (hφ : ∀ m, φ m < N4)
    (rv sv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (g4 : Nat → Bool) {B4 : Nat} (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hrv : ∀ c4 c2 c3 α β r t, rv c4 c2 c3 α β r t = none ∨ ∃ p x y, rv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c4 c2 c3 α β r t, ∃ p x y, sv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1 : Nat → D1 → Nat → P1) (op1 : Nat → D1 → O1) (sd1 : Nat → O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ∀ c4, ComPfHides NS1 Com1 (Pf1 c4) (op1 c4)) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : Nat → TViewN PV PB → Option O1) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : Nat → TViewN PV PB → Option O3) (hov3 : ∀ c4, ov3 c4 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r))
    (hvo1 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 c4 (main1 t r)))
    (hvo2 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 c4 (main2 c t r)))
    (hvo3 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
      indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
        (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) ≤
    sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x)) H4 c4)
          (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4 (fun _ => 1))) := by
  intro sm m1 m2 m3 rvo s1 s2 s3 svo sm4 r1 r2 Mq r3
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2 * NS3) (NR := NR) (m := m) (N := N)
      (fun i σ r t => f i (σ1, σ, r, t)))]
    exact sumTo_exch _ N NS1
  have hc23 : ∀ d σ, comPair NS2 n2 Com2 Com3 d σ < n2 * n3 := fun d σ => by
    unfold comPair; exact pair_lt (hr2 _ _) (hr3 _ _)
  have hsm4 : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat),
      sm4 (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm4 (f i)) := fun N f => by
    show sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => sumTo N (fun i => f i (H1, H2, H3, x)))))) = _
    simp only [hsm N]
    rw [sumTo_congr _ (fun H1 _ => sumTo_congr _ (fun H2 _ => sumTo_exch _ N (K3 ^ (n1 * (n2 * n3)))))]
    rw [sumTo_congr _ (fun H1 _ => sumTo_exch _ N (K2 ^ (n1 * n2)))]
    exact sumTo_exch _ N ((Q4 * Q4) ^ n1)
  refine fs_lastG (K := Q4 * Q4 * (K2 * K3)) (n4 := N4) hK4 sm4 hsm4 Mq
    (fun y => hφ _)
    (fun c4 y => (y.1, y.2.1, y.2.2.1, m1 y.2.2.2, m2 (r1 y) y.2.2.2, m3 (r1 y) (r2 y) y.2.2.2, rvo c4 (r1 y) (r2 y) (r3 y) y.2.2.2))
    (fun c4 G => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3)))
      (fun H3 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (G (φ (s3 c4 c1 c2 c3 x)) (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1, rset K2 (s2 c4 c1 c2 c3 x) H2 c2,
          rset K3 (s3 c4 c1 c2 c3 x) H3 c3, s1 c4 c1 c2 c3 x, s2 c4 c1 c2 c3 x, s3 c4 c1 c2 c3 x, svo c4 c1 c2 c3 x))))))))))
    g4 hB4 (fun c4 hg4 G => ?_) (fun H4 _ c4 v => E v.1 v.2.1 v.2.2.1 H4 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2.1 v.2.2.2.2.2.2)
  have h3 := fs_open3U hK2 hK3 (rv c4) (sv c4) gz hgz (hrv c4) (hsv c4) (fun c2 c3 hg => h1 c4 c2 c3 hg4 hg) (fun c2 c3 hg => h2 c4 c2 c3 hg4 hg)
    Com1 (Pf1 c4) (op1 c4) (sd1 c4) d1 hc1 (hp1 c4) hr1 (ov1 c4) (hov1 c4) main1 (hsd1 c4)
    Com2 (Pf2 c4) (op2 c4) (sd2 c4) d2 hc2 (hp2 c4) hr2 (ov2 c4) (hov2 c4) main2 (hsd2 c4)
    Com3 (Pf3 c4) (op3 c4) (sd3 c4) d3 hc3 (hp3 c4) hr3 (ov3 c4) (hov3 c4) main3 (hsd3 c4)
    (hvo1 c4) (hvo2 c4) (hvo3 c4) (sop1 c4) (sop2 c4) (sop3 c4) (hsvo1 c4) (hsvo2 c4) (hsvo3 c4)
    (fun H1 H2 H3 a b c v => G (φ c) (H1, H2, H3, a, b, c, v))
  rw [Nat.mul_assoc, Nat.mul_assoc K2]
  exact h3

/-- **`fs_open4` the other way.** -/
theorem fs_open4R {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 K4 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φ : Nat → Nat) {N4 : Nat} (hφ : ∀ m, φ m < N4)
    (rv sv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (g4 : Nat → Bool) {B4 : Nat} (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hrv : ∀ c4 c2 c3 α β r t, rv c4 c2 c3 α β r t = none ∨ ∃ p x y, rv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c4 c2 c3 α β r t, ∃ p x y, sv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1 : Nat → D1 → Nat → P1) (op1 : Nat → D1 → O1) (sd1 : Nat → O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ∀ c4, ComPfHides NS1 Com1 (Pf1 c4) (op1 c4)) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : Nat → TViewN PV PB → Option O1) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : Nat → TViewN PV PB → Option O3) (hov3 : ∀ c4, ov3 c4 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r))
    (hvo1 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 c4 (main1 t r)))
    (hvo2 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 c4 (main2 c t r)))
    (hvo3 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x)) H4 c4)
          (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) ≤
      K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
      indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
        (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4 (fun _ => 1))) := by
  intro sm m1 m2 m3 rvo s1 s2 s3 svo sm4 r1 r2 Mq r3
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2 * NS3) (NR := NR) (m := m) (N := N)
      (fun i σ r t => f i (σ1, σ, r, t)))]
    exact sumTo_exch _ N NS1
  have hc23 : ∀ d σ, comPair NS2 n2 Com2 Com3 d σ < n2 * n3 := fun d σ => by
    unfold comPair; exact pair_lt (hr2 _ _) (hr3 _ _)
  have hsm4 : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat),
      sm4 (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm4 (f i)) := fun N f => by
    show sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => sumTo N (fun i => f i (H1, H2, H3, x)))))) = _
    simp only [hsm N]
    rw [sumTo_congr _ (fun H1 _ => sumTo_congr _ (fun H2 _ => sumTo_exch _ N (K3 ^ (n1 * (n2 * n3)))))]
    rw [sumTo_congr _ (fun H1 _ => sumTo_exch _ N (K2 ^ (n1 * n2)))]
    exact sumTo_exch _ N ((Q4 * Q4) ^ n1)
  have hS1 : ∀ c4 (G : Nat → Nat × Nat × Nat × Nat × Nat × Nat × Option P1 × Option (P2 × P3) × TViewN PV PB → Bool), sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3)))
      (fun H3 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (G (φ (s3 c4 c1 c2 c3 x)) (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1, rset K2 (s2 c4 c1 c2 c3 x) H2 c2,
          rset K3 (s3 c4 c1 c2 c3 x) H3 c3, s1 c4 c1 c2 c3 x, s2 c4 c1 c2 c3 x, s3 c4 c1 c2 c3 x, svo c4 c1 c2 c3 x))))))))) ≤
      Q4 * Q4 * (K2 * K3) * sm4 (fun _ => 1) := by
    intro c4 G
    have hsm1 : ∀ f : Nat × Nat × Nat × (Nat → Tup) → Nat, (∀ x, f x ≤ 1) → sm f ≤ sm (fun _ => 1) :=
      fun f hf => sm_mono sm hsm hf
    refine Nat.le_trans (m := sumTo ((Q4 * Q4) ^ n1) (fun _ => sumTo (K2 ^ (n1 * n2)) (fun _ =>
      sumTo (K3 ^ (n1 * (n2 * n3))) (fun _ => sumTo (Q4 * Q4) (fun _ => sumTo K2 (fun _ => sumTo K3 (fun _ =>
        sm (fun _ => 1)))))))) ?_ (Nat.le_of_eq ?_)
    · refine sumTo_mono _ fun H1 _ => sumTo_mono _ fun H2 _ => sumTo_mono _ fun H3 _ =>
        sumTo_mono _ fun c1 _ => sumTo_mono _ fun c2 _ => sumTo_mono _ fun c3 _ => ?_
      exact hsm1 (fun x => indB (G (φ (s3 c4 c1 c2 c3 x)) (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1,
        rset K2 (s2 c4 c1 c2 c3 x) H2 c2, rset K3 (s3 c4 c1 c2 c3 x) H3 c3, s1 c4 c1 c2 c3 x, s2 c4 c1 c2 c3 x,
        s3 c4 c1 c2 c3 x, svo c4 c1 c2 c3 x))) (fun x => indB_le _)
    simp only [sm4, sumTo_const]
    generalize sm (fun _ => 1) = z
    ac_rfl
  refine fs_lastGR (K := Q4 * Q4 * (K2 * K3)) (n4 := N4) hK4 sm4 hsm4 Mq
    (fun y => hφ _)
    (fun c4 y => (y.1, y.2.1, y.2.2.1, m1 y.2.2.2, m2 (r1 y) y.2.2.2, m3 (r1 y) (r2 y) y.2.2.2, rvo c4 (r1 y) (r2 y) (r3 y) y.2.2.2))
    (fun c4 G => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3)))
      (fun H3 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (G (φ (s3 c4 c1 c2 c3 x)) (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1, rset K2 (s2 c4 c1 c2 c3 x) H2 c2,
          rset K3 (s3 c4 c1 c2 c3 x) H3 c3, s1 c4 c1 c2 c3 x, s2 c4 c1 c2 c3 x, s3 c4 c1 c2 c3 x, svo c4 c1 c2 c3 x))))))))))
    g4 hB4 hS1 (fun c4 hg4 G => ?_) (fun H4 _ c4 v => E v.1 v.2.1 v.2.2.1 H4 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2.1 v.2.2.2.2.2.2)
  have h3 := fs_open3R hK2 hK3 (rv c4) (sv c4) gz hgz (hrv c4) (hsv c4) (fun c2 c3 hg => h1 c4 c2 c3 hg4 hg) (fun c2 c3 hg => h2 c4 c2 c3 hg4 hg)
    Com1 (Pf1 c4) (op1 c4) (sd1 c4) d1 hc1 (hp1 c4) hr1 (ov1 c4) (hov1 c4) main1 (hsd1 c4)
    Com2 (Pf2 c4) (op2 c4) (sd2 c4) d2 hc2 (hp2 c4) hr2 (ov2 c4) (hov2 c4) main2 (hsd2 c4)
    Com3 (Pf3 c4) (op3 c4) (sd3 c4) d3 hc3 (hp3 c4) hr3 (ov3 c4) (hov3 c4) main3 (hsd3 c4)
    (hvo1 c4) (hvo2 c4) (hvo3 c4) (sop1 c4) (sop2 c4) (sop3 c4) (hsvo1 c4) (hsvo2 c4) (hsvo3 c4)
    (fun H1 H2 H3 a b c v => G (φ c) (H1, H2, H3, a, b, c, v))
  rw [Nat.mul_assoc, Nat.mul_assoc K2]
  exact h3





section
open B Air Stmt Mach Sudoku SudokuText

set_option maxRecDepth 100000 in
/-- **The Sudoku proof over four Fiat–Shamir rounds, the query points
    hashed**: `sud_fs_open3` with the query points a fourth challenge `c4`,
    drawn from a fourth table at a function `φ` of the commitments'
    transcript (which may carry a proof-of-work nonce ground against a
    table of its own, independent of the query table: `fs_pow`) and
    decoded by
    `S16 S10 SP` (`fs_open4`, `fs_open4R`).  The opening proofs (`Pf`, the
    Merkle paths at the drawn indices) and FRI's openings and randomness
    (`fri`, `Rb`, `Ro`) read `c4`; the committed data do not
    (`sud_same_d`, `sud_data_q`).  Assumed at every `c4`: the decoding
    admissible (off the trace domains, few enough points), and each
    commitment hiding given its openings and opening proof there.  Both
    ways, both counts unguarded, the non-generic `β` and `ζ` in the bound.
    Assumed besides `sud_fs_open3`'s: the fourth table's input is the
    commitments' transcript, without the opened values or FRI's layer
    commitments.  The FRI challenge is hashed
    too, decoded from `c4` by `αd`; the draws where it fails the verifier's
    test, at most `B4` of the `K4`, enter the bound as their whole count
    (decoded uniformly, `P²` in every `Q4`: `genB_count_mod`).
    FRI's folding challenges are read from `c4` through `Rb`, as one draw
    with the query points, not each hashed after its layer. -/
theorem sud_fs_open4 {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    (S16 S10 SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Nat) {N4 : Nat} (hφ : ∀ m, φ m < N4)
    (hS16 : ∀ c4, ∀ x ∈ S16 c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ c4, ∀ x ∈ S10 c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz16 : ∀ c4, 2 * (S16 c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ c4, 2 * (S10 c4).length + 8 ≤ 2 ^ 10)
    (hszP : ∀ c4, 2 * (SP c4).length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V)
    (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ∀ c4, ComPfHides NS1 Com1 (Pf1 c4) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (sudSsT (S16 c4) (S10 c4) (SP c4)) d.1, opCw (sudSsC tP (S16 c4) (S10 c4) (SP c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF → Bool) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    (K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x)) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))) ∧
    (sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x)) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) ≤
        K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
          (K2 * (Q4 * (NS1 * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1)))) := by
  intro blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv tp M q0 qZ Ss ks cols tqZ qdZ SsT SsC mk1 mk2 main1 main2 main3 vS sop1 sop2 sop3 ov1 ov2 ov3 rvF svF op3 sd3
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sms, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨hP23, hPg⟩ := sud_prog_height hc hA hlen
  rw [← htp] at hP23 hPg
  have hSw := fun (c4 c2 c3 : Nat) => sud_same_w off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSz := fun (c4 c2 c3 : Nat) => sud_same_w off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) ncw rfl rfl rfl rfl
  have hS0 := fun (c4 c2 : Nat) => sud_same_w off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) EF.zero EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSd := fun (c4 c2 c3 : Nat) => sud_same_d off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (S16 0) (S10 0) (SP 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSdz := fun (c4 c2 c3 : Nat) => sud_same_d off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (S16 0) (S10 0) (SP 0) (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) rfl rfl rfl rfl
  have hb : ∀ c4 c2 c3, genB (αd c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c4 c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c4 c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgz := (genB_iff _).1 hg
    have hgα := (genB_iff _).1 hg4
    have hpcs := sud_pcsX (heap := blank.heap) (ζ := efOf c3) off sc sms sw (rfl : C.h = 2 ^ 16) hlen
      (rfl : Wt.h = 2 ^ 10) (by omega) hPg qv (wm c2) (wc c2) (ww c2) (wp c2) (hS16 c4) (hS10 c4) (hSP c4) (hsz16 c4) (hsz c4) (hszP c4)
      (generic_ofF_ne hgz) (mz_generic hgz) (fri c4) (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 (Rb c4) (Ro c4)
    have hNR : sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) ncw = sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw := by
      unfold sudNR; rw [(hSd c4 c2 c3).n1, (hSd c4 c2 c3).n2]
    rw [hNR] at hpcs
    exact ⟨fun E' => (sud_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').1,
      fun E' => (sud_transcriptG off NR 0 (pcsZ c4 c2 (efOf c3)) (psimZ c4 c2 (efOf c3)) hbal hun hpcs E').2⟩
  have hlen8 : ∀ (c4 : Nat) (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg
          (S16 c4) (S10 c4) (SP c4) ζ qv t α β).2,
        (sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg
          (S16 c4) (S10 c4) (SP c4) ζ qv t EF.zero EF.zero).2]
  have hmk1 : ∀ k ∈ mk1, k < 8 ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk1, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 8 := by rcases hk' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, sudCols_main off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2 : ∀ k ∈ mk2, k < 8 ∧ ∀ t α β, k < (cols t α β).length := by
    intro k hk
    simp only [mk2, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hkn : k < 8 := by rcases hk with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun _ _ _ => hkn⟩
  have hvo1 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk1 (main1 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1 c4 (realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk1 hmk1 (hlen8 c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSd c4 c2 c3).dataF2 cols mk1 t (r % NR0), (hSw c4 c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo2 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (Ss c4) mk2 (main2 c t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2 c4 (realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ovP off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSd c4 c2 c3).dataP2 cols mk2 t _ _ (r % NR0), (hSw c4 c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo3 : ∀ c4 c2 c3 c r t, rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rvF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3 c4 (realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab' : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t)
        · rfl
        · exact absurd h hab
      have e0 := pcsFri_ovR2 off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw (αd c4)
        (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      have e := congrArg Prod.snd e0
      rw [(hSz c4 c2 c3).tS, (hSz c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdz c4 c2 c3).shape,
        tabsCws_congr ncw _ _ _ (hSdz c4 c2 c3).shape, (hSdz c4 c2 c3).cr (r % NR0), (hSdz c4 c2 c3).cc (r % NR0),
        (hSdz c4 c2 c3).ms (r % NR0), (hS0 c4 c2).tS, (hS0 c4 c2).iS,
        sud_data_q off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (S16 0) (S10 0) (SP 0) (efOf c3) EF.zero
          qv (wm c2) (wc c2) (ww c2) (wp c2) t _ _ _ hab'] at e
      exact .inr (congrArg some e)
  have hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (αd c4) _ mk1
      (fun k hk => (hmk1 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop2 c4 c2 c3 c r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (αd c4) _ mk2
      (fun k hk => (hmk2 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (svF c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop3 c4 c2 c3 c r t) := by
    intro c4 c2 c3 c r t
    have e0 := psimFri_ovR2 (sudGroups tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv) ks ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ncw (αd c4) (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) mk2
      (fun k hk => (hmk2 k hk).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vS (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0)
    have e := congrArg Prod.snd e0
    rw [(hSw c4 c2 c3).tS, (hSw c4 c2 c3).iS] at e
    exact congrArg some e
  have hsd1 : ∀ c4 t r, opF (Ss c4) mk1 (sdF (Ss c4) mk1 (opF (Ss c4) mk1 (main1 t r))) = opF (Ss c4) mk1 (main1 t r) :=
    fun c4 t r => opF_sdF _ _ _
  have hsd2 : ∀ c4 c t r, opF (Ss c4) mk2 (sdF (Ss c4) mk2 (opF (Ss c4) mk2 (main2 c t r))) =
      opF (Ss c4) mk2 (main2 c t r) :=
    fun c4 c t r => opF_sdF _ _ _
  have hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r) := fun c4 c c' t r =>
    congrArg Prod.snd (op2_sd2 (Ss c4) [] (SsT c4) (SsC c4) (fun _ => []) (main3 c c' t r).1 (main3 c c' t r).2)
  have hp3' : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4) := by
    intro c4
    have e1 : SsT c4 = sudSsT (S16 c4) (S10 c4) (SP c4) := sud_SsT off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0)
    have e2 : SsC c4 = sudSsC tP (S16 c4) (S10 c4) (SP c4) := sud_SsC off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    show ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (SsT c4) d.1, opCw (SsC c4) d.2))
    rw [e1, e2]; exact hp3 c4
  have hgz : sumTo K2 (fun _ => sumTo Q4 (fun c3 => indB (!genB (efOf c3)))) ≤ K2 * (P * P) := by
    rw [genB_count, sumTo_const]; exact Nat.le_refl _
  exact ⟨fs_open4 hK2 Q4_pos hK4 φ hφ rvF svF (fun c2 c3 => genB (efOf c3)) hgz (fun c4 => genB (αd c4)) hB4
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).2)
    Com1 Pf1 (fun c4 => opF (Ss c4) mk1) (fun c4 => sdF (Ss c4) mk1) d1 hc1 hp1 hr1 ov1 (fun _ => rfl) main1 hsd1
    Com2 Pf2 (fun c4 => opF (Ss c4) mk2) (fun c4 => sdF (Ss c4) mk2) d2 hc2 hp2 hr2 ov2 (fun _ => rfl) main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 (fun _ => rfl) main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E,
    fs_open4R hK2 Q4_pos hK4 φ hφ rvF svF (fun c2 c3 => genB (efOf c3)) hgz (fun c4 => genB (αd c4)) hB4
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hb c4 c2 c3 hg4 hg).2)
    Com1 Pf1 (fun c4 => opF (Ss c4) mk1) (fun c4 => sdF (Ss c4) mk1) d1 hc1 hp1 hr1 ov1 (fun _ => rfl) main1 hsd1
    Com2 Pf2 (fun c4 => opF (Ss c4) mk2) (fun c4 => sdF (Ss c4) mk2) d2 hc2 hp2 hr2 ov2 (fun _ => rfl) main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 (fun _ => rfl) main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E⟩

end

end Circuit
