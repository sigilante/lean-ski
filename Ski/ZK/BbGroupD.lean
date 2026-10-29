import Ski.ZK.SudInst

/-!
# A BabyBear trace group at constraint degree `D`

`tabsHonest_bb` for an AIR whose constraints have Plonky3 degree at most
`D` (`AirP3D D`; `AirP3` is `AirP3D 2`), over `2^(lq+1)` quotient chunks
with `D ≤ 2^lq`.  Plonky3 commits `2^(⌈log₂ D⌉ + 1)` chunks to a hiding
proof's table of degree `D`: a degree-3 table, such as the Poseidon2
jet's (the S-box `x³`), has eight (`lq = 2`) where a degree-2 table has
four, as the released `p2pre` proof's openings show (eight chunks for its
P2OUT and Poseidon2 tables, four for the rest).  `tabsHonest_gen`
(`Ski/ZK/QuotTwo.lean`) holds at every `D` and `lq` with `D ≤ 2^lq`; the
lemmas here carry `D` through the corpus wrappers (`tabsHonest_corpusD`,
`tabsHonest_corpus_iteD`) and the BabyBear group (`tabsHonest_bbD`), and
`bbTabL`, `bbDataL` are `bbTab`, `bbData` at any `lq` (`bbTab_L`,
`bbData_L`: `lq = 1`).
-/

namespace Circuit

open ZKF

/-- **What the hiding PCS asks of an AIR at constraint degree `D`**:
    `AirP3` with the constraints' Plonky3 degree at most `D`. -/
def AirP3D (D : Nat) (A : AirD) : Bool := A.cons.all (E.p3ok A.width D 1) && (corpusLs A).all (lupOkB A.width)

theorem airP3D_two (A : AirD) : AirP3D 2 A = AirP3 A := rfl

theorem p3D_facts {D : Nat} {A : AirD} (h : AirP3D D A = true) :
    (∀ c ∈ A.cons, c.guarded = true) ∧ (∀ c ∈ A.cons, c.win A.width = true) ∧
    (∀ e ∈ A.cons, e.pdeg ≤ D) ∧ (∀ e ∈ A.cons, e.sdeg ≤ 1) := by
  have h1 := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).1
  exact ⟨fun c hc => (p3ok_spec (h1 c hc)).1, fun c hc => (p3ok_spec (h1 c hc)).2.1,
    fun c hc => (p3ok_spec (h1 c hc)).2.2.1, fun c hc => (p3ok_spec (h1 c hc)).2.2.2⟩

/-- An `AirP3D` AIR's lookups are those of an `AirP3` AIR: its LogUp
    constraints are the same whatever `D`. -/
theorem airP3_lup_of_D {D : Nat} {A : AirD} (h : AirP3D D A = true) :
    AirP3 (⟨A.name, A.width, A.pre, [], A.inters, A.pretrace⟩ : AirD) = true := by
  unfold AirP3
  simp only [List.all_nil, Bool.true_and]
  exact (Bool.and_eq_true_iff.1 h).2

theorem corpus_plainD {D : Nat} {A : AirD} (hP : AirP3D D A = true) :
    ∀ I ∈ A.inters, (∀ e ∈ I.fields, Plain A.width 1 e) ∧ Plain A.width 2 I.count :=
  corpus_plain (A := ⟨A.name, A.width, A.pre, [], A.inters, A.pretrace⟩) (airP3_lup_of_D hP)

/-- **A degree-`D` AIR with its LogUp constraints**: every constraint
    guarded, in the window, of Plonky3 degree at most `D` (LogUp's at most
    2) and with at most one transition factor. -/
theorem corpus_withLup_shapeD {D : Nat} {A : AirD} (hP : AirP3D D A = true) (hD2 : 2 ≤ D) (αs : Nat → EF)
    (β T : EF) :
    ∀ c ∈ (withLup A αs β T A.width (corpusLs A)).cons,
      CShape (A.width + 4 * ((corpusLs A).length + 1)) D 1 c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨hgd, hwin, hD, hsd⟩ := p3D_facts hP
    exact ⟨hgd c hc, win_mono (by omega) c (hwin c hc), hD c hc, hsd c hc⟩
  · have h := base_lup_shape (A := ⟨A.name, A.width, A.pre, [], A.inters, A.pretrace⟩) (airP3_lup_of_D hP) αs β T c hc
    exact ⟨h.1, h.2.1, Nat.le_trans h.2.2.1 hD2, h.2.2.2⟩

/-- **The quotient's degree fits the field**: `D (2 (m + 1) - 1) + 2 ≤ P`
    for a table of `2^(tb+1)` rows, `D ≤ 2^lq` and `tb + lq + 1 ≤ 26`. -/
theorem bb_psz {D lq tb m : Nat} (hDlq : D ≤ 2 ^ lq) (hk : tb + lq + 1 ≤ 26) (hm : m + 1 = 2 ^ (tb + 1)) :
    D * (2 * (m + 1) - 1) + 1 + 1 ≤ P := by
  have e : 2 ^ (tb + 2) = 2 ^ (tb + 1) * 2 := Nat.pow_succ ..
  have h0 : 2 * (m + 1) - 1 ≤ 2 ^ (tb + 2) := by rw [e, ← hm]; omega
  have h1 : D * (2 * (m + 1) - 1) ≤ 2 ^ lq * 2 ^ (tb + 2) := Nat.mul_le_mul hDlq h0
  have h2 : 2 ^ lq * 2 ^ (tb + 2) ≤ 2 ^ 27 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : (2 : Nat) ^ 27 + 2 ≤ P := by decide
  omega

/-- **A BabyBear table's quotient table at `2^(lq+1)` chunks.** -/
def bbTabL (off : EF → String → EF) (A : AirD) (tm : EF → EF → List EF → EF) (tb lq m : Nat) (P0 : Table)
    (gm gp : Nat) (S : List F) (ζ : EF) (ws : List (EF → EF → List F)) : QTab :=
  airQTabG (lupAF off A tm) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) [gm, gp] (bbκ tb lq m)
    (bbCs tb lq m) (bbHl tb lq m) (bbCl tb lq m) S ζ ws

/-- **Its data**: the honest chunks where the proof does not abort, the
    canonical ones elsewhere. -/
def bbDataL (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF) (A : AirD)
    (tm : EF → EF → List EF → EF) (tb lq m : Nat)
    (P0 : Table) (gm gp : Nat) (S : List F) (ζ : EF) (ws : List (EF → EF → List F)) (qs : List QGroup)
    (cols : (Nat → Tup) → EF → EF → List (List (List F))) (tabs : (Nat → Tup) → List (AirD × Table))
    (t : Nat → Tup) (α β : EF) (ms : List F) : List (List (List F) × List F) :=
  if Aborts (prefixOf α (off β)) β (tabs t) = false then
    airData (withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β (tv (prefixOf α (off β)) β t))
      A.width (corpusLs A)) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) (bbCs tb lq m) (bbHl tb lq m)
      ws α β (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) [gm, gp])
  else canonData (bbTabL off A tm tb lq m P0 gm gp S ζ ws).sets α β (tv (prefixOf α (off β)) β t)
    (openMulti (qs.map QGroup.ext) (cols t α β) ms)

theorem bbTab_L (off : EF → String → EF) (A : AirD) (tm : EF → EF → List EF → EF) (tb m : Nat) (P0 : Table)
    (gm gp : Nat) (S : List F) (ζ : EF) (ws : List (EF → EF → List F)) :
    bbTab off A tm tb m P0 gm gp S ζ ws = bbTabL off A tm tb 1 m P0 gm gp S ζ ws := rfl

theorem bbData_L (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF) (A : AirD)
    (tm : EF → EF → List EF → EF) (tb m : Nat) (P0 : Table) (gm gp : Nat) (S : List F) (ζ : EF)
    (ws : List (EF → EF → List F)) (qs : List QGroup) (cols : (Nat → Tup) → EF → EF → List (List (List F)))
    (tabs : (Nat → Tup) → List (AirD × Table)) :
    bbData off tv A tm tb m P0 gm gp S ζ ws qs cols tabs = bbDataL off tv A tm tb 1 m P0 gm gp S ζ ws qs cols tabs :=
  rfl

/-- **A corpus AIR's quotient table with its LogUp constraints is honest**
    (for an AIR with at least one lookup, as p3 commits no permutation
    trace for one without):
    `tabsHonest_gen` over its main group `gm` and permutation group `gp`,
    the constraints the AIR's and LogUp's at each lookup's bus prefix and
    the transcript's terminal, at the challenges where `good` holds (no
    message of nonzero count has a vanishing denominator; elsewhere the
    prover aborts, and `pcsCloseN_fri_gen` sends the canonical chunks),
    from the builder's facts (`hb`) and the static facts of the groups,
    the domains and the weights. -/
theorem tabsHonest_corpusD {D : Nat} {A : AirD} (hP : AirP3D D A = true) (hD2 : 2 ≤ D) {g : F} {m gm gp : Nat} {tm : EF → EF → List EF → EF}
    {preP : Nat → List F} {κ : F} {cs : List Chunk} {Hl : List F} {cl : F} {S : List F} {ζ : EF}
    {ws : List (EF → EF → List F)} {qs : List QGroup} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (pre : EF → EF → String → EF) (vt : (Nat → Tup) → EF → EF → List EF) (tab : (Nat → Tup) → EF → EF → Table)
    (good : (Nat → Tup) → EF → EF → Prop) (hgl : ∀ t α β, good t α β → goodLup A pre tab t α β)
    (hgrp : ∀ j ∈ [gm, gp], ∃ hj : j < qs.length, (qs[j]'hj).base.T = cosetL 1 g (m + 1) ∧ (qs[j]'hj).base.S = S ∧
      (qs[j]'hj).base.Z = [ζ, (EF.ofF g).mul ζ] ∧ (qs[j]'hj).nxt = (g * ·) ∧
      (cosetL 1 g (m + 1) ++ (qs[j]'hj).base.R).Nodup ∧ (qs[j]'hj).base.R.length ≤ m + 1)
    (hcl' : ∀ t α β, ∀ j ∈ [gm, gp], j < (cols t α β).length)
    (hb : ∀ t α β, Sat A (tab t α β) ∧ (tab t α β).h = m + 1 ∧
      (cols t α β).getD gm [] = mainCols (tab t α β) A.width ∧
      (cols t α β).getD gp [] = permCols (tab t α β) (busAlphas (pre α β) A) β (corpusLs A) ∧
      tm α β (vt t α β) = terminal (pre α β) β A (tab t α β) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = (tab t α β).pre r i))
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {kk lq : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ kk) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (kk + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hDlq : D ≤ 2 ^ lq) (hs : 1 < m + 1)
    (hPsz : D * (2 * (m + 1) - 1) + 1 + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (hok : ∀ c ∈ (airQTabG (fun α β v => withLup A (busAlphas (pre α β) A) β (tm α β v) A.width (corpusLs A))
      g m preP [gm, gp] κ cs Hl cl S ζ ws).sets, c.OK)
    (hHn : ∀ ch ∈ cs, ch.H.Nodup) (hHln : Hl.Nodup) :
    ∀ t α β ms, good t α β → TabsHonest
      (fun c => c.JS α β (vt t α β) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (vt t α β) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      [airQTabG (fun α β v => withLup A (busAlphas (pre α β) A) β (tm α β v) A.width (corpusLs A))
        g m preP [gm, gp] κ cs Hl cl S ζ ws]
      [airData (withLup A (busAlphas (pre α β) A) β (tm α β (vt t α β)) A.width (corpusLs A)) g m preP cs Hl
        ws α β (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) [gm, gp])] := by
  obtain ⟨hgd, hwin, _, _⟩ := p3D_facts hP
  have shape := fun α β (v : List EF) => corpus_withLup_shapeD hP hD2 (busAlphas (pre α β) A) β (tm α β v)
  exact tabsHonest_gen (AF := fun α β v => withLup A (busAlphas (pre α β) A) β (tm α β v) A.width (corpusLs A))
    vt good hgrp hcl' (hsatT_lup pre cols vt preP g good hwin (corpus_plainD hP)
      (fun t α β hgood => by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb t α β
        exact ⟨tab t α β, h1, h2, h3, h4, h5, hgl t α β hgood, h6⟩)) hg hinj
    (fun α β v c hc => (shape α β v c hc).1) hpreL hζ hS hc hcl hκ hshift hhalf hN hdom hL
    (fun α β v c hc => (shape α β v c hc).2.2.1) hDlq (fun α β v c hc => (shape α β v c hc).2.2.2) hs hPsz hw hok
    hHn hHln

/-- **A corpus AIR's table is honest at every challenge**: the honest
    chunks where the proof does not abort, the canonical ones elsewhere. -/
theorem tabsHonest_corpus_iteD
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    {D : Nat} {A : AirD} (hP : AirP3D D A = true) (hD2 : 2 ≤ D) {g : F} {m gm gp : Nat} {tm : EF → EF → List EF → EF}
    {preP : Nat → List F} {κ : F} {cs : List Chunk} {Hl : List F} {cl : F} {S : List F} {ζ : EF}
    {ws : List (EF → EF → List F)} {qs : List QGroup} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (tab : (Nat → Tup) → Table) (tabs : (Nat → Tup) → List (AirD × Table)) (hmem : ∀ t, (A, tab t) ∈ tabs t)
    (hgrp : ∀ j ∈ [gm, gp], ∃ hj : j < qs.length, (qs[j]'hj).base.T = cosetL 1 g (m + 1) ∧ (qs[j]'hj).base.S = S ∧
      (qs[j]'hj).base.Z = [ζ, (EF.ofF g).mul ζ] ∧ (qs[j]'hj).nxt = (g * ·) ∧
      (cosetL 1 g (m + 1) ++ (qs[j]'hj).base.R).Nodup ∧ (qs[j]'hj).base.R.length ≤ m + 1)
    (hcl' : ∀ t α β, ∀ j ∈ [gm, gp], j < (cols t α β).length)
    (hb : ∀ t α β, Sat A (tab t) ∧ (tab t).h = m + 1 ∧
      (cols t α β).getD gm [] = mainCols (tab t) A.width ∧
      (cols t α β).getD gp [] = permCols (tab t) (busAlphas (prefixOf α (off β)) A) β (corpusLs A) ∧
      tm α β (tv (prefixOf α (off β)) β t) = terminal (prefixOf α (off β)) β A (tab t) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = (tab t).pre r i))
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {kk lq : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ kk) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (kk + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hDlq : D ≤ 2 ^ lq) (hs : 1 < m + 1)
    (hPsz : D * (2 * (m + 1) - 1) + 1 + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (hok : ∀ c ∈ (airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β v) A.width
      (corpusLs A)) g m preP [gm, gp] κ cs Hl cl S ζ ws).sets, c.OK)
    (hHn : ∀ ch ∈ cs, ch.H.Nodup) (hHln : Hl.Nodup) :
    ∀ t α β ms, TabsHonest
      (fun c => c.JS α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      [airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β v) A.width
        (corpusLs A)) g m preP [gm, gp] κ cs Hl cl S ζ ws]
      [if Aborts (prefixOf α (off β)) β (tabs t) = false then
          airData (withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β (tv (prefixOf α (off β)) β t))
            A.width (corpusLs A)) g m preP cs Hl ws α β (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) [gm, gp])
          else canonData (airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β v)
            A.width (corpusLs A)) g m preP [gm, gp] κ cs Hl cl S ζ ws).sets α β (tv (prefixOf α (off β)) β t)
            (openMulti (qs.map QGroup.ext) (cols t α β) ms)] := by
  intro t α β ms
  by_cases hab : Aborts (prefixOf α (off β)) β (tabs t) = false
  · rw [if_pos hab]
    exact tabsHonest_corpusD hP hD2 (fun α β => prefixOf α (off β)) (fun t α β => tv (prefixOf α (off β)) β t)
      (fun t _ _ => tab t) (fun t α β => Aborts (prefixOf α (off β)) β (tabs t) = false)
      (fun t α β h => goodLup_of_noAbort (ts := fun t _ _ => tabs t) (hmem t) h)
      hgrp hcl' hb hg hinj hpreL hζ hS hc hcl hκ hshift hhalf hN hdom hL hDlq hs hPsz hw hok hHn hHln t α β ms hab
  · rw [if_neg hab]
    have hdl : ∀ H ∈ cs.map (·.H) ++ [Hl], H.length = m + 1 := fun H hH => by
      rw [hdom] at hH; exact split_length hH
    exact tabsHonest_canon α β _ _ hok
      (fun ch hch => ⟨hdl _ (List.mem_append_left _ (List.mem_map_of_mem hch)), hHn ch hch⟩)
      (hdl _ (List.mem_append_right _ List.mem_cons_self)) hHln

/-- **One private table over BabyBear, honest at every challenge**:
    `tabsHonest_corpus_ite` with the trace groups `bbGroup`, Plonky3's
    chunks and the preprocessed columns interpolated, every domain and
    chunk fact and the groups' shape discharged.  Left: the AIR's check
    (`AirP3`); the run's tables, columns and terminal (`hb`); one fixed
    preprocessed table `P0` every `tab t` shares (`hpre0`); the groups
    list with `bbGroup` at `gm` and `gp` (`hqm`, `hqp`, `hcl'`); the
    transcript's tables (`hmem`); the height `m + 1 = 2^(tb+1)` with
    `1 ≤ lq` and `tb + lq + 1 ≤ 26`; and the query and out-of-domain
    points (`hSoff`, which `lde_off_trace` gives for Plonky3's queries,
    `|S| + 4 ≤ m + 1`, `ζ ∉ F`, `(mz ζ).det ≠ 0`). -/
theorem tabsHonest_bbD (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    {D : Nat} {A : AirD} (hP : AirP3D D A = true) (hD2 : 2 ≤ D) {tb lq m gm gp : Nat} {tm : EF → EF → List EF → EF} (ht : tb ≤ 25) (hlq : 1 ≤ lq)
    (hk : tb + lq + 1 ≤ 26) (hDlq : D ≤ 2 ^ lq) (hm : m + 1 = 2 ^ (tb + 1))
    {S : List F} {ζ : EF} {ws : List (EF → EF → List F)} {qs : List QGroup}
    {cols : (Nat → Tup) → EF → EF → List (List (List F))} {qv1 qv2 : EF → EF → List EF → F → List F → List F → List EF}
    (hqm : ∃ h : gm < qs.length, qs[gm]'h = bbGroup tb S ζ qv1)
    (hqp : ∃ h : gp < qs.length, qs[gp]'h = bbGroup tb S ζ qv2)
    (tab : (Nat → Tup) → Table) (P0 : Table) (hpre0 : ∀ t, (tab t).pre = P0.pre)
    (tabs : (Nat → Tup) → List (AirD × Table)) (hmem : ∀ t, (A, tab t) ∈ tabs t)
    (hcl' : ∀ t α β, ∀ j ∈ [gm, gp], j < (cols t α β).length)
    (hb : ∀ t α β, Sat A (tab t) ∧ (tab t).h = m + 1 ∧
      (cols t α β).getD gm [] = mainCols (tab t) A.width ∧
      (cols t α β).getD gp [] = permCols (tab t) (busAlphas (prefixOf α (off β)) A) β (corpusLs A) ∧
      tm α β (tv (prefixOf α (off β)) β t) = terminal (prefixOf α (off β)) β A (tab t))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hdet : (mz ζ).det ≠ 0)
    (hSoff : ∀ x ∈ S, x ∉ cosetL 1 (bbGen (tb + 1)) (m + 1)) (hS4 : S.length + 4 ≤ m + 1) :
    ∀ t α β ms, TabsHonest
      (fun c => c.JS α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      [airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β v) A.width
        (corpusLs A)) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) [gm, gp] (bbκ tb lq m) (bbCs tb lq m)
        (bbHl tb lq m) (bbCl tb lq m) S ζ ws]
      [if Aborts (prefixOf α (off β)) β (tabs t) = false then
          airData (withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β (tv (prefixOf α (off β)) β t))
            A.width (corpusLs A)) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) (bbCs tb lq m) (bbHl tb lq m)
            ws α β (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) [gm, gp])
          else canonData (airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β v)
            A.width (corpusLs A)) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) [gm, gp] (bbκ tb lq m)
            (bbCs tb lq m) (bbHl tb lq m) (bbCl tb lq m) S ζ ws).sets α β (tv (prefixOf α (off β)) β t)
            (openMulti (qs.map QGroup.ext) (cols t α β) ms)] := by
  obtain ⟨hg, hinj⟩ := bb_trace tb (by omega)
  rw [← hm] at hg hinj
  have hch := bb_chunks (tb := tb) (lq := lq) hk
  simp only [← hm] at hch
  obtain ⟨hshift, hhalf, hN, hdom, hL, hc, hcl, hκ, hw, hm0, hHn, hHln⟩ := hch
  have hpre := fun i => preInterp_spec P0 (g := bbGen (tb + 1)) (m := m) hinj i
  have hpos : 2 ≤ 2 ^ (tb + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (tb + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hbig : 2 ^ (tb + 1) ≤ 2 ^ 26 := Nat.pow_le_pow_right (by decide) (by omega)
  refine tabsHonest_corpus_iteD off tv hP hD2 (tm := tm) (lq := lq) tab tabs hmem (fun j hj => ?_) hcl'
    (fun t α β => ?_) hg hinj (fun i => by have := (hpre i).1; omega) hζ
    (fun x hx => fvan_ne x _ (hSoff x hx)) hc hcl hκ hshift hhalf hN hdom hL
    hDlq (by omega)
    (bb_psz hDlq hk hm) hw
    (airQTabG_ok hζ hdet hS4 (fun ch hch => ⟨hc ch hch, hm0 ch hch⟩) hcl) hHn hHln
  · rcases List.mem_cons.1 hj with rfl | hj
    · obtain ⟨h, e⟩ := hqm
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := bbGroup_hgrp ht S ζ qv1
      rw [← hm] at e1 e5 e6
      exact ⟨h, by rw [e]; exact e1, by rw [e]; exact e2, by rw [e]; exact e3, by rw [e]; exact e4,
        by rw [e]; exact e5, by rw [e]; exact e6⟩
    · rcases List.mem_singleton.1 hj with rfl
      obtain ⟨h, e⟩ := hqp
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := bbGroup_hgrp ht S ζ qv2
      rw [← hm] at e1 e5 e6
      exact ⟨h, by rw [e]; exact e1, by rw [e]; exact e2, by rw [e]; exact e3, by rw [e]; exact e4,
        by rw [e]; exact e5, by rw [e]; exact e6⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hb t α β
    exact ⟨h1, h2, h3, h4, h5, fun r i hr => by rw [hpre0]; exact (hpre i).2 r hr⟩

end Circuit
