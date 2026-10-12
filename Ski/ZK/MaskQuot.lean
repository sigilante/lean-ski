import Ski.ZK.MaskMulti

/-!
# The quotient's recombined values hide too

Under hiding Plonky3 commits each quotient chunk at its trace's own height
(the chunks' domains, `<< is_zk`, are the trace's extended domain), so a
query opens the chunks at the trace's own point `s`, and they recombine
there to the quotient `Q(s)`.  That is the constraints' combination of the
masked columns at `s` and at the next row `g s`, with the challenges and
the published LogUp terminals (the last-row constraint reads them),
divided by the trace domain's vanishing polynomial.  The quotient at the
out-of-domain point is the same function of the openings at `ζ` and
`g ζ`, which `masks_hide` already covers.

So the recombined values are a function of the column openings at
`S ++ g S` and of the terminals the simulator is given.  A group whose
masks cover those points, `2|S| + 4|Z| ≤ n` (`QGroup.OK`), opens its
columns there with one distribution whatever they hold, and so does
anything computed from the openings and the terminals
(`PCSCloseN.post`).  The PCS whose view is every group's column openings
at `S` and `Z` and its quotient values at `S` meets `PCSCloseN` with
`ε = 0` (`pcsCloseN_quot`); the transcript theorems then hold over it
with no PCS term (`transcript_zkG_quot`, `comp_transcriptG_quot` and the
others).  At `q` queries, `|S| = q` and `|Z| = 2` (`ζ` and `g ζ`), so
the masks must cover `2q + 8` points; Plonky3's `HidingFriPcs` asks
`2(q + 8)`, and `ski-air mask-margin` checks both.

Scope.  The view holds the recombined value `Q(s)`, a function of the
chunks' values; Plonky3's proof opens each chunk, at `s` and at `ζ`,
and those values are not in this view.  Assumed: the chunks' split and
randomization (that the chunks' values reveal no more than `Q(s)`), the
randomization polynomial (opened at `ζ` and at every query point), the
random codeword columns, FRI's layers, Merkle paths and salts, and Fiat–Shamir.  The points and
the constraint-folding challenge are fixed before the masks, in the
public-coin model (`QGroup.qv` is one function for each value of that
challenge).  That the recombined chunks give `Q(s)` as this function is
read from Plonky3's source (`get_quotient_ldes`, the batch verifier's
quotient domains), not proved.
-/

namespace Circuit

open ZKF

/-- **Post-processing keeps the simulation**: a view computed from the
    PCS's view, the challenges and the published terminals by any
    function is within `ε` of the same function of the simulator's. -/
theorem PCSCloseN.post {PV PW : Type} {off : EF → String → EF} {NR : Nat}
    {tv : (String → EF) → EF → (Nat → Tup) → List EF} {pcs : (Nat → Tup) → EF → EF → Nat → PV}
    {psim : EF → EF → List EF → Nat → PV} {ε : Nat} (h : PCSCloseN off NR tv pcs psim ε)
    (post : EF → EF → List EF → PV → PW) :
    PCSCloseN off NR tv (fun t α β r => post α β (tv (prefixOf α (off β)) β t) (pcs t α β r))
      (fun α β v r => post α β v (psim α β v r)) ε :=
  fun t α β F => h t α β (fun w => F (post α β (tv (prefixOf α (off β)) β t) w))

/-- **A group with a quotient**: a group of columns of one height
    (`base`), the next-row map `nxt` (multiplication by the trace
    domain's generator), and the quotient's value at a query point `s`
    from the challenges, the published terminals and the columns' values
    at `s` and `nxt s`, one entry a table of the group. -/
structure QGroup where
  base : MGroup
  nxt : F → F
  qv : EF → EF → List EF → F → List F → List F → List EF

/-- The group the masks must cover: the query points and their next
    rows. -/
def QGroup.ext (q : QGroup) : MGroup :=
  { q.base with S := q.base.S ++ q.base.S.map q.nxt }

/-- What the quotient asks of a group: `n` trace and `n` mask points, all
    distinct, every query point and its next row off the trace, the
    out-of-domain points off `F`, and `2|S| + 4|Z| ≤ n`. -/
def QGroup.OK (q : QGroup) : Prop :=
  q.base.T.length = q.base.n ∧ q.base.R.length = q.base.n ∧ (q.base.T ++ q.base.R).Nodup ∧
    (∀ x ∈ q.base.T, x ∉ q.base.S ∧ x ∉ q.base.S.map q.nxt) ∧
    (∀ z ∈ q.base.Z, ∀ x : F, EF.ofF x ≠ z) ∧
    2 * q.base.S.length + 4 * q.base.Z.length ≤ q.base.n

theorem QGroup.ext_OK {q : QGroup} (h : q.OK) : q.ext.OK := by
  obtain ⟨hT, hR, hTR, hTS, hZ, hn⟩ := h
  refine ⟨hT, hR, hTR, fun x hx hS => ?_, hZ, ?_⟩
  · obtain ⟨h1, h2⟩ := hTS x hx
    rcases List.mem_append.1 hS with hS | hS
    · exact h1 hS
    · exact h2 hS
  · show (q.base.S ++ q.base.S.map q.nxt).length + 4 * q.base.Z.length ≤ q.base.n
    rw [List.length_append, List.length_map]
    omega

/-- Every column's value at the `i`-th opened point. -/
def colsAt (os : List (List F × List EF)) (i : Nat) : List F := os.map (fun o => o.1.getD i 0)

/-- **A group's view with its quotient**: each column's openings at the
    group's own `S` and `Z`, and the quotient's value at each point of
    `S`, from the terminals and the columns at that point and at its next
    row. -/
def QGroup.view (q : QGroup) (α β : EF) (v : List EF) (os : List (List F × List EF)) :
    List (List F × List EF) × List (List EF) :=
  (os.map (fun o => (o.1.take q.base.S.length, o.2)),
    (List.range q.base.S.length).map fun j =>
      q.qv α β v (q.base.S.getD j 0) (colsAt os j) (colsAt os (q.base.S.length + j)))

/-- The masked polynomials of the columns, the masks split as `openAll`
    splits them. -/
def mpolys (T R : List F) (n : Nat) : List (List F) → List F → List (List F)
  | [], _ => []
  | t :: ts, rs => mcol T R t (rs.take n) :: mpolys T R n ts (rs.drop n)

theorem colsAt_openAll (T R S : List F) (Z : List EF) (n : Nat) (k : Nat) (hk : k < S.length) :
    ∀ (ts : List (List F)) (rs : List F),
      colsAt (openAll T R S Z n ts rs) k = (mpolys T R n ts rs).map (fval S[k])
  | [], _ => rfl
  | t :: ts, rs => by
    show (mopen T R S t (rs.take n)).getD k 0 :: colsAt (openAll T R S Z n ts (rs.drop n)) k =
      fval S[k] (mcol T R t (rs.take n)) :: (mpolys T R n ts (rs.drop n)).map (fval S[k])
    rw [colsAt_openAll T R S Z n k hk ts (rs.drop n)]
    unfold mopen
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_map]; exact hk),
      Option.getD_some, List.getElem_map]

/-- **The view reads the quotient from the columns**: over the openings
    at `S ++ nxt S`, the view's `j`-th quotient value is `qv` of the
    terminals and every masked column at `S[j]` and at `nxt S[j]`. -/
theorem QGroup.view_quot (q : QGroup) (α β : EF) (v : List EF) (ts : List (List F)) (rs : List F)
    (j : Nat) (hj : j < q.base.S.length) :
    ((q.view α β v (openAll q.base.T q.base.R q.ext.S q.base.Z q.base.n ts rs)).2)[j]'(by
        simp only [QGroup.view, List.length_map, List.length_range]; exact hj) =
      q.qv α β v q.base.S[j] ((mpolys q.base.T q.base.R q.base.n ts rs).map (fval q.base.S[j]))
        ((mpolys q.base.T q.base.R q.base.n ts rs).map (fval (q.nxt q.base.S[j]))) := by
  have hS : q.ext.S = q.base.S ++ q.base.S.map q.nxt := rfl
  have hl : q.ext.S.length = q.base.S.length + q.base.S.length := by
    rw [hS, List.length_append, List.length_map]
  simp only [QGroup.view, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
    colsAt_openAll _ _ _ _ _ _ (by omega), colsAt_openAll _ _ _ _ _ _ (by omega)]
  have e1 : q.ext.S[j]'(by omega) = q.base.S[j] := by
    simp only [hS]
    rw [List.getElem_append_left hj]
  have e2 : q.ext.S[q.base.S.length + j]'(by omega) = q.nxt q.base.S[j] := by
    simp only [hS]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, List.getElem_map]
  rw [e1, e2]

/-- The view of every group, from every group's openings. -/
def quotPost (qs : List QGroup) (α β : EF) (v : List EF) (oss : List (List (List F × List EF))) :
    List (List (List F × List EF) × List (List EF)) :=
  (qs.zip oss).map fun p => p.1.view α β v p.2

section
variable (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
  (qs : List QGroup) (ks : List Nat) (cols : (Nat → Tup) → EF → EF → List (List (List F)))

/-- **The masked PCS with its quotients**: every group's column openings
    at `S` and `Z` and its quotient values at `S`, computed from the
    published terminals and the openings at `S ++ nxt S` under the masks
    `r`'s digits. -/
def pcsQuot (t : Nat → Tup) (α β : EF) (r : Nat) : List (List (List F × List EF) × List (List EF)) :=
  quotPost qs α β (tv (prefixOf α (off β)) β t) (pcsMulti (qs.map QGroup.ext) ks cols t α β r)
end

section
variable (qs : List QGroup) (ks : List Nat)

/-- **Its simulator**: the same computation from the terminals and zero
    columns under the same masks. -/
def psimQuot (α β : EF) (v : List EF) (r : Nat) : List (List (List F × List EF) × List (List EF)) :=
  quotPost qs α β v (psimMulti (qs.map QGroup.ext) ks α β v r)
end

/-- **The masked PCS hides its quotients' recombined values exactly**:
    with every group's masks covering its query points and their next
    rows (`QGroup.OK`), and the columns of the groups' shapes, the view of
    the column openings and the quotient values has the simulator's
    distribution for every tuple assignment and challenges: `PCSCloseN`
    with `ε = 0`. -/
theorem pcsCloseN_quot {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF) :
    PCSCloseN off (P ^ mtotal (qs.map QGroup.ext) ks) tv (pcsQuot off tv qs ks cols) (psimQuot qs ks) 0 :=
  (pcsCloseN_multi (gs := qs.map QGroup.ext)
    (fun g hg => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
      exact QGroup.ext_OK (hok q hq))
    (by rw [hks, List.length_map]) hcols off tv).post (quotPost qs)

/-- **The transcript over the masked PCS with its quotients**:
    `transcript_zkG` with the column openings and the quotient values of
    every height as the PCS's view, which `pcsCloseN_quot` simulates
    exactly; no PCS term remains. -/
theorem transcript_zkG_quot {PB : Type} {off : EF → String → EF} {M m : Nat}
    {bus : Nat → String} {sg : Nat → Bool} {par : Nat → Nat} (hpar : ∀ k, par (k + 1) ≤ k)
    {tabs : (Nat → Tup) → List (AirD × Table)}
    {tv : (String → EF) → EF → (Nat → Tup) → List EF} {tp : (String → EF) → EF → EF}
    {pb : (String → EF) → EF → PB} {xu : (String → EF) → EF → Nat → EF}
    (hchain : ∀ pre β t, tv pre β t = viewT β (fun k => pre (bus k)) sg par (m + 1) (xu pre β) t)
    (hsum : ∀ pre β, sumL (xu pre β) (List.range (m + 1)) = EF.zero.sub (tp pre β))
    (hM : ∀ t, (allEntries (tabs t)).length ≤ M)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (E : TViewN (List (List (List F × List EF) × List (List EF))) PB → Bool) :
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) m (fun α β r t =>
        indB (genB β && E (realVN off tabs tv pb (pcsQuot off tv qs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) m (fun α β r t =>
        indB (genB β && E (simVN off pb bus sg par (m + 1) tp (psimQuot qs ks) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * 0)) ∧
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) m (fun α β r t =>
        indB (genB β && E (simVN off pb bus sg par (m + 1) tp (psimQuot qs ks) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) m (fun α β r t =>
        indB (genB β && E (realVN off tabs tv pb (pcsQuot off tv qs ks cols) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * 0)) :=
  transcript_zkG hpar hchain hsum hM (pcsCloseN_quot hok hks hcols off tv) E

/-- `comp_transcriptG` over the masked PCS with its quotients (`pcsCloseN_quot`): no PCS term. -/
theorem comp_transcriptG_quot (off : EF → String → EF)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat} {C Mm Wt : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt (segsPub roots)))
    (h : Unblinded WT_BLIND C Mm Wt)
    (E : TViewN (List (List (List F × List EF) × List (List EF))) (EF × EF) → Bool) :
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
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsQuot off (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) qs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 tp (psimQuot qs ks) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 tp (psimQuot qs ks) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsQuot off (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) qs ks cols) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) :=
  comp_transcriptG off (P ^ mtotal (qs.map QGroup.ext) ks) 0 (pcsQuot off (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) qs ks cols) (psimQuot qs ks) hb h
    (pcsCloseN_quot hok hks hcols off _) E

/-- `sud_transcriptG` over the masked PCS with its quotients (`pcsCloseN_quot`): no PCS term. -/
theorem sud_transcriptG_quot (off : EF → String → EF)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Wt : Table}
    (hb : Balanced (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)) (h : Unblinded 1 C Mm Wt)
    (E : TViewN (List (List (List F × List EF) × List (List EF))) EF → Bool) :
    let tabs := fun t : Nat → Tup => sudTables hd0 stk0 ctr0 heap ((C.setBlind BLA (t 1)).setBlind BLB (t 0))
      (Mm.setBlind 5 (t 0)) (progTableS heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS heap) (progTableS heap)
    let M := (allEntries (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)).length
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsQuot off (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) qs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimQuot qs ks) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimQuot qs ks) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsQuot off (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) qs ks cols) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) :=
  sud_transcriptG off (P ^ mtotal (qs.map QGroup.ext) ks) 0 (pcsQuot off (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) qs ks cols) (psimQuot qs ks) hb h
    (pcsCloseN_quot hok hks hcols off _) E

/-- `wit_transcriptG` over the masked PCS with its quotients (`pcsCloseN_quot`): no PCS term. -/
theorem wit_transcriptG_quot (off : EF → String → EF)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat} {C Mm Wt : Table}
    (hb : Balanced (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)) (h : Unblinded WT_BLIND C Mm Wt)
    (E : TViewN (List (List (List F × List EF) × List (List EF))) EF → Bool) :
    let tabs := fun t : Nat → Tup => witTables hd0 stk0 ctr0 heap W ((C.setBlind BLA (t 1)).setBlind BLB (t 0))
      (Mm.setBlind 5 (t 0)) (progTableW heap W) (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirW heap W) (progTableW heap W)
    let M := (allEntries (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)).length
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsQuot off (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) qs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimQuot qs ks) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimQuot qs ks) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsQuot off (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) qs ks cols) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) :=
  wit_transcriptG off (P ^ mtotal (qs.map QGroup.ext) ks) 0 (pcsQuot off (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) qs ks cols) (psimQuot qs ks) hb h
    (pcsCloseN_quot hok hks hcols off _) E

/-- `compJ_transcriptG` over the masked PCS with its quotients (`pcsCloseN_quot`): no PCS term. -/
theorem compJ_transcriptG_quot (off : EF → String → EF)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {segRoots : List Nat}
    {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Wt Rt Hd Tm Po Iw : Table}
    (hb : Balanced (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm (progTableC heap N W) Wt
      (segsPub segRoots) Rt Hd Tm Po Iw))
    (h : UnblindedCJ roots jets C Mm Wt Rt Hd Tm Po Iw)
    (E : TViewN (List (List (List F × List EF) × List (List EF))) (EF × EF) → Bool) :
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
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 7 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsQuot off (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t) qs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 7 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 8 tp (psimQuot qs ks) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * 0)) ∧
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 7 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 8 tp (psimQuot qs ks) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 7 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsQuot off (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t) qs ks cols) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * 0)) :=
  compJ_transcriptG off (P ^ mtotal (qs.map QGroup.ext) ks) 0 (pcsQuot off (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t) qs ks cols) (psimQuot qs ks) hb h
    (pcsCloseN_quot hok hks hcols off _) E

/-- `compP_transcriptG` over the masked PCS with its quotients (`pcsCloseN_quot`): no PCS term. -/
theorem compP_transcriptG_quot (off : EF → String → EF) (calls : Nat)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
    {C Mm Wt Pi Po Pp : Table}
    (hb : Balanced (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm (progTableC heap N W) Wt
      (segsPub roots) Pi Po Pp (idxPub calls)))
    (h : UnblindedCP C Mm Wt Pi Po Pp)
    (E : TViewN (List (List (List F × List EF) × List (List EF))) ((EF × EF) × EF) → Bool) :
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
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 5 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsQuot off (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t) qs ks cols) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 5 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 6 tp (psimQuot qs ks) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * 0)) ∧
    tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 5 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 6 tp (psimQuot qs ks) α β r t))) ≤
      tsumN (P ^ mtotal (qs.map QGroup.ext) ks) 5 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsQuot off (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t) qs ks cols) α β r t))) +
        Q4 * (P ^ mtotal (qs.map QGroup.ext) ks * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * 0)) :=
  compP_transcriptG off (P ^ mtotal (qs.map QGroup.ext) ks) 0 calls (pcsQuot off (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t) qs ks cols) (psimQuot qs ks) hb h
    (pcsCloseN_quot hok hks hcols off _) E

end Circuit
