import Ski.ZK.MaskPCS
import Ski.ZK.Reject

/-!
# Masked columns of several heights

`masks_hide` and `pcsCloseN_masked` take columns of one height `n`.  A
proof's tables have several (the CPU's `2^R` rows, the memory's `2^Lm`,
the witness table's `2^9`), and Plonky3 masks each table's columns over
its own trace domain.  Here the columns come in groups, one per height,
each with its own trace points `T`, mask points `R`, query points `S` and
out-of-domain points `Z` (`MGroup`), and each meeting `masks_hide`'s
conditions (`MGroup.OK`).  The masks of different groups are independent,
so the openings of all the groups have one joint distribution whatever
the columns hold (`masks_hide_multi`), and the PCS whose view is those
openings meets `PCSCloseN` with `ε = 0` (`pcsCloseN_multi`).

Composed with the transcript theorems, the masked trace openings become a
proved part of every hiding circuit's simulated view: `transcript_zkG`
over that PCS has no PCS term (`transcript_zkG_masked`).  The scope is
`MaskPCS.lean`'s: the column openings, in the public-coin model, with the
points fixed before the masks.  `Ski/ZK/MaskQuot.lean` adds the
quotient's recombined values at the query points; the quotient's chunks, the random
codewords, FRI and the Merkle salts stay assumed.
-/

namespace Circuit

open ZKF

/-- **A group of columns of one height**: the trace points `T`, the mask
    points `R`, the query points `S`, the out-of-domain points `Z`, and
    the height `n`. -/
structure MGroup where
  T : List F
  R : List F
  S : List F
  Z : List EF
  n : Nat

/-- What `masks_hide` asks of a group: `n` trace and `n` mask points, all
    distinct, the queries off the trace, the out-of-domain points off `F`,
    and `|S| + 4|Z| ≤ n`. -/
def MGroup.OK (g : MGroup) : Prop :=
  g.T.length = g.n ∧ g.R.length = g.n ∧ (g.T ++ g.R).Nodup ∧ (∀ x ∈ g.T, x ∉ g.S) ∧
    (∀ z ∈ g.Z, ∀ x : F, EF.ofF x ≠ z) ∧ g.S.length + 4 * g.Z.length ≤ g.n

/-- The mask values the groups use: each group's column count times its
    height. -/
def mtotal : List MGroup → List Nat → Nat
  | g :: gs, k :: ks => k * g.n + mtotal gs ks
  | _, _ => 0

/-- The columns fit the groups: one list of columns a group, each column
    of the group's height. -/
def Shaped : List MGroup → List (List (List F)) → Prop
  | [], [] => True
  | g :: gs, ts :: tss => (∀ c ∈ ts, c.length = g.n) ∧ Shaped gs tss
  | _, _ => False

/-- **The openings of every group**, the randomness split group by group. -/
def openMulti : List MGroup → List (List (List F)) → List F → List (List (List F × List EF))
  | g :: gs, ts :: tss, rs => openAll g.T g.R g.S g.Z g.n ts (rs.take (ts.length * g.n)) ::
      openMulti gs tss (rs.drop (ts.length * g.n))
  | _, _, _ => []

/-- **Random rows hide the columns of every height at once**: columns of
    the groups' shapes open with one joint distribution whatever they
    hold. -/
theorem masks_hide_multi : ∀ (gs : List MGroup) (tss tss' : List (List (List F))),
    (∀ g ∈ gs, g.OK) → Shaped gs tss → Shaped gs tss' → tss.map List.length = tss'.map List.length →
    ∀ E : List (List (List F × List EF)) → Bool,
    vsum (mtotal gs (tss.map List.length)) (fun rs => if E (openMulti gs tss rs) then 1 else 0) =
      vsum (mtotal gs (tss.map List.length)) (fun rs => if E (openMulti gs tss' rs) then 1 else 0)
  | [], [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _, _, _ => nomatch h
  | [], [], _ :: _, _, _, h, _, _ => nomatch h
  | _ :: _, [], _, _, h, _, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, h, _, _ => nomatch h
  | g :: gs, ts :: tss, ts' :: tss', hok, ⟨h1, hs⟩, ⟨h2, hs'⟩, hl, E => by
    obtain ⟨hT, hR, hTR, hTS, hZ, hn⟩ := hok g List.mem_cons_self
    have hok' : ∀ g ∈ gs, g.OK := fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    simp only [List.map_cons, List.cons.injEq] at hl
    obtain ⟨hl1, hl2⟩ := hl
    let o : List (List F) → List F → List (List F × List EF) := fun u x => openAll g.T g.R g.S g.Z g.n u x
    have split : ∀ (u : List (List F)) (us : List (List (List F))) (x y : List F), x.length = u.length * g.n →
        openMulti (g :: gs) (u :: us) (x ++ y) = o u x :: openMulti gs us y := by
      intro u us x y hx
      show openAll g.T g.R g.S g.Z g.n u ((x ++ y).take (u.length * g.n)) ::
        openMulti gs us ((x ++ y).drop (u.length * g.n)) = _
      rw [List.take_left' hx, List.drop_left' hx]
    let b := mtotal gs (tss.map List.length)
    show vsum (ts.length * g.n + b) _ = vsum (ts.length * g.n + b) _
    rw [vsum_append b, vsum_append b]
    calc vsum (ts.length * g.n) (fun x => vsum b (fun y => if E (openMulti (g :: gs) (ts :: tss) (x ++ y)) then 1 else 0))
        = vsum (ts.length * g.n) (fun x => vsum b (fun y => if E (o ts x :: openMulti gs tss y) then 1 else 0)) :=
          vsum_congr _ (fun x hx => vsum_congr _ (fun y _ => by rw [split ts tss x y hx]))
      _ = vsum (ts.length * g.n) (fun x => vsum b (fun y => if E (o ts x :: openMulti gs tss' y) then 1 else 0)) :=
          vsum_congr _ (fun x _ => masks_hide_multi gs tss tss' hok' hs hs' hl2 (fun L => E (o ts x :: L)))
      _ = vsum b (fun y => vsum (ts.length * g.n) (fun x => if E (o ts x :: openMulti gs tss' y) then 1 else 0)) :=
          vsum_comm _ _ _
      _ = vsum b (fun y => vsum (ts.length * g.n) (fun x => if E (o ts' x :: openMulti gs tss' y) then 1 else 0)) :=
          vsum_congr _ (fun y _ => masks_hide hT hR hTR hTS hZ hn ts ts' hl1 h1 h2
            (fun L => E (L :: openMulti gs tss' y)))
      _ = vsum (ts.length * g.n) (fun x => vsum b (fun y => if E (o ts' x :: openMulti gs tss' y) then 1 else 0)) :=
          (vsum_comm _ _ _).symm
      _ = vsum (ts.length * g.n) (fun x => vsum b (fun y => if E (openMulti (g :: gs) (ts' :: tss') (x ++ y)) then 1 else 0)) :=
          vsum_congr _ (fun x hx => vsum_congr _ (fun y _ => by rw [split ts' tss' x y (by rw [hx, hl1])]))

section
variable (gs : List MGroup) (ks : List Nat) (cols : (Nat → Tup) → EF → EF → List (List (List F)))

/-- **The masked PCS over several heights**: the openings of every
    group's columns, the randomness `r`'s digits. -/
def pcsMulti (t : Nat → Tup) (α β : EF) (r : Nat) : List (List (List F × List EF)) :=
  openMulti gs (cols t α β) (digitsF (mtotal gs ks) r)

/-- **Its simulator**: zero columns of the same shapes under the same
    masks; it uses nothing. -/
def psimMulti (_ _ : EF) (_ : List EF) (r : Nat) : List (List (List F × List EF)) :=
  openMulti gs ((gs.zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n 0))) (digitsF (mtotal gs ks) r)
end

theorem shaped_zero : ∀ (gs : List MGroup) (ks : List Nat), ks.length = gs.length →
    Shaped gs ((gs.zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n 0))) ∧
      ((gs.zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F)))).map List.length = ks
  | [], [], _ => ⟨trivial, rfl⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | g :: gs, k :: ks, h => by
    have ih := shaped_zero gs ks (by simp only [List.length_cons] at h; omega)
    refine ⟨⟨fun c hc => by rw [List.eq_of_mem_replicate hc, List.length_replicate], ih.1⟩, ?_⟩
    show (List.replicate k (List.replicate g.n (0 : F))).length ::
      ((gs.zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F)))).map List.length = k :: ks
    rw [List.length_replicate, ih.2]

/-- **The masked PCS over several heights hides exactly**: with every
    group meeting `masks_hide`'s conditions and the columns of the groups'
    shapes, `ks` columns a group, the PCS's view has the simulator's
    distribution for every tuple assignment and challenges: `PCSCloseN`
    with `ε = 0`. -/
theorem pcsCloseN_multi {gs : List MGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ g ∈ gs, g.OK) (hks : ks.length = gs.length)
    (hcols : ∀ t α β, Shaped gs (cols t α β) ∧ (cols t α β).map List.length = ks)
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF) :
    PCSCloseN off (P ^ mtotal gs ks) tv (pcsMulti gs ks cols) (psimMulti gs ks) 0 := by
  intro t α β F
  have key : sumTo (P ^ mtotal gs ks) (fun r => indB (F (pcsMulti gs ks cols t α β r))) =
      sumTo (P ^ mtotal gs ks) (fun r => indB (F (psimMulti gs ks α β (tv (prefixOf α (off β)) β t) r))) := by
    unfold pcsMulti psimMulti
    rw [sumTo_digitsF (mtotal gs ks) (fun rs => indB (F (openMulti gs (cols t α β) rs))),
      sumTo_digitsF (mtotal gs ks) (fun rs => indB (F (openMulti gs
        ((gs.zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n 0))) rs)))]
    obtain ⟨hsh, hl⟩ := hcols t α β
    obtain ⟨hz, hzl⟩ := shaped_zero gs ks hks
    have h := masks_hide_multi gs (cols t α β) _ hok hsh hz (by rw [hl, hzl]) F
    rw [hl] at h
    exact h
  rw [key]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- **The transcript over the masked PCS**: `transcript_zkG` with the
    masked column openings of every height as the PCS's view, which
    `pcsCloseN_multi` simulates exactly; no PCS term remains. -/
theorem transcript_zkG_masked {PB : Type} {off : EF → String → EF} {M m : Nat}
    {bus : Nat → String} {sg : Nat → Bool} {par : Nat → Nat} (hpar : ∀ k, par (k + 1) ≤ k)
    {tabs : (Nat → Tup) → List (AirD × Table)}
    {tv : (String → EF) → EF → (Nat → Tup) → List EF} {tp : (String → EF) → EF → EF}
    {pb : (String → EF) → EF → PB} {xu : (String → EF) → EF → Nat → EF}
    (hchain : ∀ pre β t, tv pre β t = viewT β (fun k => pre (bus k)) sg par (m + 1) (xu pre β) t)
    (hsum : ∀ pre β, sumL (xu pre β) (List.range (m + 1)) = EF.zero.sub (tp pre β))
    (hM : ∀ t, (allEntries (tabs t)).length ≤ M)
    {gs : List MGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ g ∈ gs, g.OK) (hks : ks.length = gs.length)
    (hcols : ∀ t α β, Shaped gs (cols t α β) ∧ (cols t α β).map List.length = ks)
    (E : TViewN (List (List (List F × List EF))) PB → Bool) :
    tsumN (P ^ mtotal gs ks) m (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsMulti gs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) m (fun α β r t =>
        indB (genB β && E (simVN off pb bus sg par (m + 1) tp (psimMulti gs ks) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * 0)) ∧
    tsumN (P ^ mtotal gs ks) m (fun α β r t =>
        indB (genB β && E (simVN off pb bus sg par (m + 1) tp (psimMulti gs ks) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) m (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsMulti gs ks cols) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * 0)) :=
  transcript_zkG hpar hchain hsum hM (pcsCloseN_multi hok hks hcols off tv) E

/-- `comp_transcriptG` over the masked PCS of several heights (`pcsCloseN_multi`): no PCS term. -/
theorem comp_transcriptG_masked (off : EF → String → EF)
    {gs : List MGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ g ∈ gs, g.OK) (hks : ks.length = gs.length)
    (hcols : ∀ t α β, Shaped gs (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat} {C Mm Wt : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt (segsPub roots)))
    (h : Unblinded WT_BLIND C Mm Wt)
    (E : TViewN (List (List (List F × List EF))) (EF × EF) → Bool) :
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
    tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsMulti gs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 tp (psimMulti gs ks) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 tp (psimMulti gs ks) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsMulti gs ks cols) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) :=
  comp_transcriptG off (P ^ mtotal gs ks) 0 (pcsMulti gs ks cols) (psimMulti gs ks) hb h
    (pcsCloseN_multi hok hks hcols off _) E

/-- `sud_transcriptG` over the masked PCS of several heights (`pcsCloseN_multi`): no PCS term. -/
theorem sud_transcriptG_masked (off : EF → String → EF)
    {gs : List MGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ g ∈ gs, g.OK) (hks : ks.length = gs.length)
    (hcols : ∀ t α β, Shaped gs (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Wt : Table}
    (hb : Balanced (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)) (h : Unblinded 1 C Mm Wt)
    (E : TViewN (List (List (List F × List EF))) EF → Bool) :
    let tabs := fun t : Nat → Tup => sudTables hd0 stk0 ctr0 heap ((C.setBlind BLA (t 1)).setBlind BLB (t 0))
      (Mm.setBlind 5 (t 0)) (progTableS heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS heap) (progTableS heap)
    let M := (allEntries (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)).length
    tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsMulti gs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimMulti gs ks) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimMulti gs ks) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsMulti gs ks cols) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) :=
  sud_transcriptG off (P ^ mtotal gs ks) 0 (pcsMulti gs ks cols) (psimMulti gs ks) hb h
    (pcsCloseN_multi hok hks hcols off _) E

/-- `wit_transcriptG` over the masked PCS of several heights (`pcsCloseN_multi`): no PCS term. -/
theorem wit_transcriptG_masked (off : EF → String → EF)
    {gs : List MGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ g ∈ gs, g.OK) (hks : ks.length = gs.length)
    (hcols : ∀ t α β, Shaped gs (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat} {C Mm Wt : Table}
    (hb : Balanced (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)) (h : Unblinded WT_BLIND C Mm Wt)
    (E : TViewN (List (List (List F × List EF))) EF → Bool) :
    let tabs := fun t : Nat → Tup => witTables hd0 stk0 ctr0 heap W ((C.setBlind BLA (t 1)).setBlind BLB (t 0))
      (Mm.setBlind 5 (t 0)) (progTableW heap W) (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirW heap W) (progTableW heap W)
    let M := (allEntries (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)).length
    tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsMulti gs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimMulti gs ks) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimMulti gs ks) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsMulti gs ks cols) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) :=
  wit_transcriptG off (P ^ mtotal gs ks) 0 (pcsMulti gs ks cols) (psimMulti gs ks) hb h
    (pcsCloseN_multi hok hks hcols off _) E

/-- `compJ_transcriptG` over the masked PCS of several heights (`pcsCloseN_multi`): no PCS term. -/
theorem compJ_transcriptG_masked (off : EF → String → EF)
    {gs : List MGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ g ∈ gs, g.OK) (hks : ks.length = gs.length)
    (hcols : ∀ t α β, Shaped gs (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {segRoots : List Nat}
    {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Wt Rt Hd Tm Po Iw : Table}
    (hb : Balanced (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm (progTableC heap N W) Wt
      (segsPub segRoots) Rt Hd Tm Po Iw))
    (h : UnblindedCJ roots jets C Mm Wt Rt Hd Tm Po Iw)
    (E : TViewN (List (List (List F × List EF))) (EF × EF) → Bool) :
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
    tsumN (P ^ mtotal gs ks) 7 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsMulti gs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 7 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 8 tp (psimMulti gs ks) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * 0)) ∧
    tsumN (P ^ mtotal gs ks) 7 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 8 tp (psimMulti gs ks) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 7 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsMulti gs ks cols) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * 0)) :=
  compJ_transcriptG off (P ^ mtotal gs ks) 0 (pcsMulti gs ks cols) (psimMulti gs ks) hb h
    (pcsCloseN_multi hok hks hcols off _) E

/-- `compP_transcriptG` over the masked PCS of several heights (`pcsCloseN_multi`): no PCS term. -/
theorem compP_transcriptG_masked (off : EF → String → EF) (calls : Nat)
    {gs : List MGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ g ∈ gs, g.OK) (hks : ks.length = gs.length)
    (hcols : ∀ t α β, Shaped gs (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
    {C Mm Wt Pi Po Pp : Table}
    (hb : Balanced (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm (progTableC heap N W) Wt
      (segsPub roots) Pi Po Pp (idxPub calls)))
    (h : UnblindedCP C Mm Wt Pi Po Pp)
    (E : TViewN (List (List (List F × List EF))) ((EF × EF) × EF) → Bool) :
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
    tsumN (P ^ mtotal gs ks) 5 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsMulti gs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 5 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 6 tp (psimMulti gs ks) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * 0)) ∧
    tsumN (P ^ mtotal gs ks) 5 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 6 tp (psimMulti gs ks) α β r t))) ≤
      tsumN (P ^ mtotal gs ks) 5 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsMulti gs ks cols) α β r t))) +
        Q4 * (P ^ mtotal gs ks * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * 0)) :=
  compP_transcriptG off (P ^ mtotal gs ks) 0 calls (pcsMulti gs ks cols) (psimMulti gs ks) hb h
    (pcsCloseN_multi hok hks hcols off _) E

end Circuit
