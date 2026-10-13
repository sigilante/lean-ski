import Ski.ZK.QuotP3

/-!
# Quotient tables over several groups

Plonky3's quotient folds an AIR's own constraints and its LogUp
constraints.  The LogUp constraints read the permutation trace, which
is committed as a second group.  Both groups sit on the same trace
domain and are opened at the same query points and at `ζ, g ζ`.  This
file reads a table's leaves from several such groups at once: their
openings, concatenated, are honest openings of the concatenated column
polynomials (`HonestOpen`, `honest_append`).  The targets read from them
are then the honest targets (`airTg_open_gen`, `airTgE_open_gen`).

The constraints are a family `AF α β v`: Plonky3's LogUp constraints
have coefficients in the challenges `α, β` and a last-row constraint on
the prover's terminal, a transcript value.  An extension constraint
enters through its coordinates (`eq4`, `Ski/ZK/QuotFold.lean`), the
challenges and terminal as constants.  `tabsHonest_gen` asks `Sat` only
at the transcript's own values `v = vt t α β`, and `pcsCloseN_fri_gen`
takes them from the transcript.  Column `i` below the first group's
width reads the first group, and the others read the next groups in
order (Plonky3 flattens permutation column `c` to base columns
`4c, …, 4c + 3`).  Every group is opened at `ζ` and `g ζ`, which
over-approximates Plonky3's main-trace openings when the AIR reads no
next row.
-/

namespace Circuit

open ZKF

/-- **Honest openings** of column polynomials `ps` at the points `S'` and
    `Z`. -/
def HonestOpen (S' : List F) (Z : List EF) (os : List (List F × List EF)) (ps : List (List F)) : Prop :=
  os = ps.map fun p => (S'.map fun s => fval s p, Z.map fun z => fvalE z p)

theorem openAll_honest (T R S' : List F) (Z : List EF) (n : Nat) : ∀ (ts : List (List F)) (rs : List F),
    HonestOpen S' Z (openAll T R S' Z n ts rs) (mpolys T R n ts rs)
  | [], _ => rfl
  | t :: ts, rs => by
    unfold HonestOpen
    show (mopen T R S' t (rs.take n), _) :: openAll T R S' Z n ts (rs.drop n) =
      _ :: (mpolys T R n ts (rs.drop n)).map _
    rw [openAll_honest T R S' Z n ts (rs.drop n)]
    rfl

/-- **Groups opened at the same points concatenate.** -/
theorem honest_append {S' : List F} {Z : List EF} {os1 os2 : List (List F × List EF)} {ps1 ps2 : List (List F)}
    (h1 : HonestOpen S' Z os1 ps1) (h2 : HonestOpen S' Z os2 ps2) : HonestOpen S' Z (os1 ++ os2) (ps1 ++ ps2) := by
  unfold HonestOpen at *; rw [h1, h2, List.map_append]

theorem colsAt_honest {S' : List F} {Z : List EF} {os : List (List F × List EF)} {ps : List (List F)}
    (h : HonestOpen S' Z os ps) (k : Nat) (hk : k < S'.length) : colsAt os k = ps.map (fval S'[k]) := by
  unfold HonestOpen at h; subst h
  unfold colsAt
  rw [List.map_map]
  refine List.map_congr_left (fun p _ => ?_)
  show (S'.map fun s => fval s p).getD k 0 = fval S'[k] p
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_map]; exact hk), Option.getD_some,
    List.getElem_map]

theorem snd_honest {S' : List F} {Z : List EF} {os : List (List F × List EF)} {ps : List (List F)}
    (h : HonestOpen S' Z os ps) (i : Nat) (hi : i < ps.length) :
    (os.getD i ([], [])).2 = Z.map fun z => fvalE z (ps.getD i []) := by
  unfold HonestOpen at h; subst h
  rw [getD_map_lt _ _ [] ps i hi]

/-- **The leaves from honest openings**, of any column polynomials. -/
theorem ρOpen_honest_gen {S : List F} {Z : List EF} {os : List (List F × List EF)} {ps : List (List F)} {g : F} {m : Nat}
    (h : HonestOpen (S ++ S.map (g * ·)) Z os ps) (preP : Nat → List F) {x : F} (hx : x ∈ S) (a : Atom)
    (ha : ∀ o i, a = .main o i → o ≤ 1 ∧ i < ps.length) :
    ρOpen S os preP g m x a =
      fval x (stdRho g (fun i => ps.getD i []) preP (selF g m) (selL g m) (selT g m) a) := by
  obtain ⟨hk, hSk⟩ := idxIn_spec hx
  have hlen : (S ++ S.map (g * ·)).length = S.length + S.length := by rw [List.length_append, List.length_map]
  cases a with
  | main o i =>
    obtain ⟨ho, hi⟩ := ha o i rfl
    rw [(fval_stdRho x g _ preP _ _ _ o i).1]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ho with rfl | rfl
    · show (colsAt os (idxIn x S)).getD i 0 = _
      rw [colsAt_honest h _ (by rw [hlen]; omega), getD_map_lt _ _ [] _ i hi, List.getElem_append_left hk, hSk]
      show _ = fval (1 * x) _; rw [one_mul']
    · show (colsAt os (S.length + idxIn x S)).getD i 0 = _
      rw [colsAt_honest h _ (by rw [hlen]; omega), getD_map_lt _ _ [] _ i hi,
        List.getElem_append_right (Nat.le_add_right _ _), List.getElem_map]
      simp only [Nat.add_sub_cancel_left, hSk]
      show _ = fval (1 * g * x) _; rw [one_mul']
  | pre o i => exact ((fval_stdRho x g _ preP _ _ _ o i).2).symm
  | first => rfl
  | last => rfl
  | trans => rfl

theorem ρOpenE_honest_gen {S' : List F} {ζ : EF} {os : List (List F × List EF)} {ps : List (List F)} {g : F} {m : Nat}
    (h : HonestOpen S' [ζ, (EF.ofF g).mul ζ] os ps) (preP : Nat → List F) (a : Atom)
    (ha : ∀ o i, a = .main o i → o ≤ 1 ∧ i < ps.length) :
    ρOpenE os preP g m ζ a =
      fvalE ζ (stdRho g (fun i => ps.getD i []) preP (selF g m) (selL g m) (selT g m) a) := by
  cases a with
  | main o i =>
    obtain ⟨ho, hi⟩ := ha o i rfl
    rw [(fvalE_stdRho ζ g _ preP _ _ _ o i).1]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ho with rfl | rfl
    · show (os.getD i ([], [])).2.getD 0 EF.zero = _
      rw [snd_honest h i hi]
      show _ = fvalE ((EF.ofF 1).mul ζ) _
      rw [show EF.ofF 1 = EF.one from rfl, EF.one_mul]; rfl
    · show (os.getD i ([], [])).2.getD 1 EF.zero = _
      rw [snd_honest h i hi]
      show _ = fvalE ((EF.ofF (1 * g)).mul ζ) _
      rw [one_mul']; rfl
  | pre o i => rfl
  | first => rfl
  | last => rfl
  | trans => rfl

/-- **The targets read from honest openings are the honest targets**, for
    any column polynomials and constraints in the window. -/
theorem airTg_open_gen {S : List F} {Z : List EF} {os : List (List F × List EF)} {ps : List (List F)} {g : F} {m : Nat}
    (h : HonestOpen (S ++ S.map (g * ·)) Z os ps) (preP : Nat → List F) (cs : List Chunk) (Hl : List F) (cl : F)
    (qs : List (List F)) (ql : List F) (κ : F) (H ws : List F) (es : List E) (hw : ∀ e ∈ es, e.win ps.length = true)
    {x : F} (hx : x ∈ S) :
    airTg cs Hl cl qs ql κ H ws es (ρOpen S os preP g m) x =
      airTg cs Hl cl qs ql κ H ws es
        (fun x a => fval x (stdRho g (fun i => ps.getD i []) preP (selF g m) (selL g m) (selT g m) a)) x := by
  have e : es.map (·.eval (ρOpen S os preP g m x)) =
      es.map (·.eval (fun a => fval x (stdRho g (fun i => ps.getD i []) preP (selF g m) (selL g m) (selT g m) a))) :=
    List.map_congr_left (fun e he => eval_win (fun a ha => ρOpen_honest_gen h preP hx a ha) e (hw e he))
  unfold airTg; rw [e]

theorem airTgE_open_gen {S' : List F} {ζ : EF} {os : List (List F × List EF)} {ps : List (List F)} {g : F} {m : Nat}
    (h : HonestOpen S' [ζ, (EF.ofF g).mul ζ] os ps) (preP : Nat → List F) (cs : List Chunk) (Hl : List F) (cl : F)
    (qs : List (List F)) (ql : List F) (κ : F) (H ws : List F) (es : List E) (hw : ∀ e ∈ es, e.win ps.length = true) :
    airTgE ζ cs Hl cl qs ql κ H ws es (ρOpenE os preP g m ζ) =
      airTgE ζ cs Hl cl qs ql κ H ws es
        (fun a => fvalE ζ (stdRho g (fun i => ps.getD i []) preP (selF g m) (selL g m) (selT g m) a)) := by
  have e : es.map (·.evalE (ρOpenE os preP g m ζ)) =
      es.map (·.evalE (fun a => fvalE ζ (stdRho g (fun i => ps.getD i []) preP (selF g m) (selL g m) (selT g m) a))) :=
    List.map_congr_left (fun e he => evalE_win (fun a ha => ρOpenE_honest_gen h preP a ha) e (hw e he))
  unfold airTgE; rw [e]

/-- **One coordinate, over any honestly opened column polynomials**: as
    `coord_shows`, with the column polynomials `ps` (several groups'
    masked columns, concatenated) interpolating the table on `⟨g⟩`, of at
    most `2(m+1)` coefficients, and honestly opened as `os`. -/
theorem coord_shows_gen {A : AirD} {Tb : Table} {g : F} {m : Nat} (hsat : Sat A Tb) (hh : Tb.h = m + 1)
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hgd : ∀ c ∈ A.cons, c.guarded = true) {ps : List (List F)} (hwin : ∀ c ∈ A.cons, c.win ps.length = true)
    (hps : ∀ r i, i < ps.length → r < m + 1 → fval (fpow g r) (ps.getD i []) = Tb.main r i)
    (hpsL : ∀ p ∈ ps, p.length ≤ 2 * (m + 1))
    (preP : Nat → List F) (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hpre : ∀ r i, r < m + 1 → fval (fpow g r) (preP i) = Tb.pre r i)
    {S : List F} {ζ : EF} {os : List (List F × List EF)}
    (hO : HonestOpen (S ++ S.map (g * ·)) [ζ, (EF.ofF g).mul ζ] os ps)
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    {cs : List Chunk} {Hl : List F} {cl κ : F} (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {k lq D s : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (k + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hD : ∀ e ∈ A.cons, e.pdeg ≤ D) (hDlq : D ≤ 2 ^ lq)
    (hsd : ∀ e ∈ A.cons, e.sdeg ≤ s) (hs : s < m + 1) (hPsz : D * (2 * (m + 1) - 1) + s + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (w : List F) :
    let ρ := stdRho g (fun i => ps.getD i []) preP (selF g m) (selL g m) (selT g m)
    let Qp := fdivH (cosetL 1 g (m + 1)) (cpoly ρ w A.cons)
    Shows S ζ cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp)
      (airTg cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w A.cons (ρOpen S os preP g m))
      (airTgE ζ cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w A.cons (ρOpenE os preP g m ζ)) := by
  intro ρ Qp
  have hHlen : (cosetL 1 g (m + 1)).length = m + 1 := cosetL_length 1 g (m + 1)
  have hgetL : ∀ i, (ps.getD i []).length ≤ 2 * (m + 1) := fun i => by
    rw [List.getD_eq_getElem?_getD]
    by_cases hi : i < ps.length
    · rw [List.getElem?_eq_getElem hi, Option.getD_some]; exact hpsL _ (List.getElem_mem hi)
    · rw [List.getElem?_eq_none (by omega)]; exact Nat.zero_le _
  have hρ : ∀ a, a ≠ .trans → (ρ a).length ≤ 2 * (m + 1) := fun a ha => by
    cases a with
    | main o i =>
      show (fshift (fpow g o) (ps.getD i [])).length ≤ 2 * (m + 1)
      rw [fshift_length]; exact hgetL i
    | pre o i => show (fshift _ _).length ≤ _; rw [fshift_length]; exact hpreL i
    | first =>
      show (fvan (cosetL (1 * g) g m)).length ≤ _
      have := fvan_length (cosetL (1 * g) g m); rw [cosetL_length] at this; omega
    | last =>
      show (fvan (cosetL 1 g m)).length ≤ _
      have := fvan_length (cosetL 1 g m); rw [cosetL_length] at this; omega
    | trans => exact absurd rfl ha
  have ht : (ρ .trans).length ≤ 2 := Nat.le_refl 2
  have hP : (cpoly ρ w A.cons).length ≤ P :=
    Nat.le_trans (cpoly_plen ρ (2 * (m + 1) - 1) D s (fun a ha => by have := hρ a ha; omega) ht w A.cons hD hsd) hPsz
  have hq : QuotOK cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp) κ Qp := by
    have hlenq : (cs.map fun ch => chunkOf ch.H Qp).length = cs.length := List.length_map _
    have hd := (allL_doms Hl cl (chunkOf Hl Qp) Qp cs).trans hdom
    have hnd' := split_nodup hshift hhalf hN
    rw [← hd] at hnd'
    have hcne : ∀ p ∈ allL cs Hl cl (cs.map fun ch => chunkOf ch.H Qp) (chunkOf Hl Qp), p.2.1 ≠ 0 := fun p hp => by
      rcases mem_allL hp with ⟨ch, hch, _, e⟩ | ⟨_, e⟩
      · rw [e]; exact hc ch hch
      · rw [e]; exact hcl
    refine quotOK_split hκ hshift hhalf hN hdom ?_
      (first_of_cis κ (fpow ω (cs.length + 1)) m hκ _ hcne (dis_of_nodup _ hnd').2 (hw _ _ hlenq))
    have := quot_fits ρ (m + 1) D lq s hρ ht w A.cons hD hsd hs hDlq _ hHlen
    rw [hL]; exact this
  -- the table cut to the columns' count, interpolated by `ps`
  have hmain : ∀ r i, r < m + 1 → fval (fpow g r) (ps.getD i []) = (Tb.cut ps.length).main r i := fun r i hr => by
    show _ = if i < ps.length then Tb.main r i else 0
    by_cases hi : i < ps.length
    · rw [if_pos hi]; exact hps r i hi hr
    · rw [if_neg hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  have hsh := shows_sat (sat_cut hsat hwin) hh hg hinj hgd _ preP hmain hpre hζ hc hcl w hP hS
    (fvalE_fvan_ne ζ hζ _) hq
  have hl1 : (cs.map fun ch => chunkOf ch.H Qp).length = cs.length := List.length_map _
  have hl2 : (cs.map fun (_ : Chunk) => ([] : List F)).length = cs.length := List.length_map _
  have hsh' := shows_congr hsh (fun x hx => (airTg_open_gen hO preP cs Hl cl _ _ κ _ w A.cons hwin hx).symm)
    (airTgE_open_gen hO preP cs Hl cl _ _ κ _ w A.cons hwin).symm
  rw [airTg_qs cs Hl cl _ _ κ _ w A.cons _ hl1 hl2, airTgE_qs ζ cs Hl cl _ _ κ _ w A.cons _ hl1 hl2] at hsh'
  exact hsh'

-- ---------------------------------------------------------------------------
-- Several groups' columns, concatenated
-- ---------------------------------------------------------------------------

/-- Groups `gis`' entries of `o`, concatenated. -/
def catAt {α : Type} (o : List (List α)) : List Nat → List α
  | [] => []
  | j :: js => o.getD j [] ++ catAt o js

/-- **Column polynomials interpolating columns**: `ps[i]` takes `ts[i]`'s
    values on `T`, column by column. -/
def ColsOn (T : List F) (ps ts : List (List F)) : Prop :=
  ps.length = ts.length ∧ ∀ i (h1 : i < ps.length) (h2 : i < ts.length) r (hr : r < T.length) (hr' : r < (ts[i]).length),
    fval T[r] (ps[i]) = (ts[i])[r]

theorem colsOn_append {T : List F} {ps1 ts1 ps2 ts2 : List (List F)} (h1 : ColsOn T ps1 ts1) (h2 : ColsOn T ps2 ts2) :
    ColsOn T (ps1 ++ ps2) (ts1 ++ ts2) := by
  refine ⟨by rw [List.length_append, List.length_append, h1.1, h2.1], fun i hi hi' r hr hr' => ?_⟩
  by_cases hl : i < ps1.length
  · have hl' : i < ts1.length := by rw [← h1.1]; exact hl
    simp only [List.getElem_append_left hl, List.getElem_append_left hl'] at hr' ⊢
    exact h1.2 i hl hl' r hr hr'
  · have hl' : ts1.length ≤ i := by rw [← h1.1]; omega
    have hl2 : ps1.length ≤ i := by omega
    simp only [List.getElem_append_right hl2, List.getElem_append_right hl'] at hr' ⊢
    simp only [h1.1]
    rw [List.length_append] at hi hi'
    exact h2.2 (i - ts1.length) (by rw [h2.1]; omega) (by omega) r hr hr'

theorem colsOn_mpolys {T R : List F} {n : Nat} (hnd : (T ++ R).Nodup) : ∀ (ts : List (List F)) (rs : List F),
    (∀ t ∈ ts, t.length = T.length) → ColsOn T (mpolys T R n ts rs) ts
  | [], _, _ => ⟨rfl, fun _ h _ => absurd h (Nat.not_lt_zero _)⟩
  | t :: ts, rs, hl => by
    have ih := colsOn_mpolys (n := n) hnd ts (rs.drop n) (fun t' ht' => hl t' (List.mem_cons_of_mem _ ht'))
    refine ⟨by show (mpolys T R n ts _).length + 1 = ts.length + 1; rw [ih.1], fun i hi hi' r hr hr' => ?_⟩
    cases i with
    | zero =>
      show fval T[r] (mcol T R t (rs.take n)) = t[r]
      exact mcol_on_T (hl t List.mem_cons_self).symm hnd hr
    | succ i =>
      exact ih.2 i (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi') r hr hr'

theorem honest_cat {S' : List F} {Z : List EF} (o : List (List (List F × List EF))) (mp : List (List (List F))) :
    ∀ gis : List Nat, (∀ j ∈ gis, HonestOpen S' Z (o.getD j []) (mp.getD j [])) →
    HonestOpen S' Z (catAt o gis) (catAt mp gis)
  | [], _ => rfl
  | j :: js, hj => honest_append (hj j List.mem_cons_self) (honest_cat o mp js (fun j' h => hj j' (List.mem_cons_of_mem _ h)))

theorem colsOn_cat {T : List F} (mp ts : List (List (List F))) :
    ∀ gis : List Nat, (∀ j ∈ gis, ColsOn T (mp.getD j []) (ts.getD j [])) → ColsOn T (catAt mp gis) (catAt ts gis)
  | [], _ => ⟨rfl, fun _ h _ => absurd h (Nat.not_lt_zero _)⟩
  | j :: js, hj => colsOn_append (hj j List.mem_cons_self) (colsOn_cat mp ts js (fun j' h => hj j' (List.mem_cons_of_mem _ h)))

theorem mem_catAt {α : Type} {o : List (List α)} {x : α} : ∀ {gis : List Nat}, x ∈ catAt o gis → ∃ j ∈ gis, x ∈ o.getD j []
  | [], h => nomatch h
  | j :: js, h => by
    rcases List.mem_append.1 h with h | h
    · exact ⟨j, List.mem_cons_self, h⟩
    · obtain ⟨j', hj', hx⟩ := mem_catAt h
      exact ⟨j', List.mem_cons_of_mem _ hj', hx⟩

theorem mem_getD_catAt {α : Type} {o : List (List α)} {x : α} {gis : List Nat} {j : Nat} (hj : j ∈ gis)
    (hx : x ∈ o.getD j []) : x ∈ catAt o gis := by
  induction gis with
  | nil => nomatch hj
  | cons j' js ih =>
    rcases List.mem_cons.1 hj with rfl | hj
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (ih hj)

theorem mpolys_mem_len (T R : List F) (n : Nat) : ∀ (ts : List (List F)) (rs : List F), ∀ p ∈ mpolys T R n ts rs,
    p.length ≤ T.length + R.length
  | [], _, _, h => nomatch h
  | t :: ts, rs, p, h => by
    rcases List.mem_cons.1 h with rfl | h
    · unfold mcol
      refine Nat.le_trans (finterp_length _) ?_
      rw [List.length_append, List.length_zip, List.length_zip]
      exact Nat.add_le_add (Nat.min_le_left _ _) (Nat.min_le_left _ _)
    · exact mpolys_mem_len T R n ts (rs.drop n) p h

-- ---------------------------------------------------------------------------
-- The table over several groups
-- ---------------------------------------------------------------------------

/-- **An AIR's quotient table over the groups `gis`**: as `airQTab`, the
    leaves read from the groups' openings concatenated and the
    constraints `AF α β v` taken at the challenges and transcript values. -/
def airQTabG (AF : EF → EF → List EF → AirD) (g : F) (m : Nat) (preP : Nat → List F) (gis : List Nat) (κ : F) (cs : List Chunk)
    (Hl : List F) (cl : F) (S : List F) (ζ : EF) (ws : List (EF → EF → List F)) : QTab :=
  ⟨cs, Hl, cl, S, ζ, m + 1, ws.map fun w =>
    (fun α β v o x => airTg cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) (w α β) (AF α β v).cons
        (ρOpen S (catAt o gis) preP g m) x,
     fun α β v o => airTgE ζ cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) (w α β) (AF α β v).cons
        (ρOpenE (catAt o gis) preP g m ζ))⟩

theorem recOK_airG {AF : EF → EF → List EF → AirD} {g : F} {m : Nat} {preP : Nat → List F} {gis : List Nat} {κ : F} {cs : List Chunk}
    {Hl : List F} {cl : F} {S : List F} {ζ : EF} (α β : EF) (v : List EF) (o : List (List (List F × List EF)))
    (mp : List (List F))
    (h : ∀ w, Shows S ζ cs Hl cl (cs.map fun ch => chunkOf ch.H (fdivH (cosetL 1 g (m + 1))
        (cpoly (stdRho g (fun i => mp.getD i []) preP (selF g m) (selL g m) (selT g m)) w (AF α β v).cons)))
      (chunkOf Hl (fdivH (cosetL 1 g (m + 1))
        (cpoly (stdRho g (fun i => mp.getD i []) preP (selF g m) (selL g m) (selT g m)) w (AF α β v).cons)))
      (airTg cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w (AF α β v).cons (ρOpen S (catAt o gis) preP g m))
      (airTgE ζ cs Hl cl (cs.map fun _ => []) [] κ (cosetL 1 g (m + 1)) w (AF α β v).cons (ρOpenE (catAt o gis) preP g m ζ))) :
    ∀ ws : List (EF → EF → List F), RecOK (airQTabG AF g m preP gis κ cs Hl cl S ζ ws).sets
      (airData (AF α β v) g m preP cs Hl ws α β mp) (fun c => c.JS α β v o) (fun c => c.Jζ α β v o)
  | [] => trivial
  | w :: ws => ⟨⟨List.length_map _, h (w α β)⟩, recOK_airG α β v o mp h ws⟩

/-- **An AIR's quotient table over several groups is honest**, at every
    trace, challenge, mask and transcript value: the groups `gis` (an
    AIR's main trace and its permutation trace) share the trace domain
    `⟨g⟩`, the query points and `ζ, g ζ`, and at each trace their columns,
    concatenated, are a table that meets `Sat` for the constraints
    `AF α β v` at the transcript's values `v = vt t α β`: the AIR's own,
    which may include its LogUp constraints over base coordinates, which
    depend on the challenges and the terminal.  `Sat` at every `t, α, β` is stronger
    than completeness (`fallback`). -/
theorem tabsHonest_gen {AF : EF → EF → List EF → AirD} {g : F} {m : Nat} {preP : Nat → List F} {gis : List Nat} {κ : F} {cs : List Chunk}
    {Hl : List F} {cl : F} {S : List F} {ζ : EF} {ws : List (EF → EF → List F)}
    {qs : List QGroup} {cols : (Nat → Tup) → EF → EF → List (List (List F))} (vt : (Nat → Tup) → EF → EF → List EF)
    (good : (Nat → Tup) → EF → EF → Prop)
    (hgrp : ∀ j ∈ gis, ∃ hj : j < qs.length, (qs[j]'hj).base.T = cosetL 1 g (m + 1) ∧ (qs[j]'hj).base.S = S ∧
      (qs[j]'hj).base.Z = [ζ, (EF.ofF g).mul ζ] ∧ (qs[j]'hj).nxt = (g * ·) ∧
      (cosetL 1 g (m + 1) ++ (qs[j]'hj).base.R).Nodup ∧ (qs[j]'hj).base.R.length ≤ m + 1)
    (hcl' : ∀ t α β, ∀ j ∈ gis, j < (cols t α β).length)
    (hsatT : ∀ t α β, good t α β → ∃ Tb : Table, Sat (AF α β (vt t α β)) Tb ∧ Tb.h = m + 1 ∧
      (∀ c ∈ (AF α β (vt t α β)).cons, c.win (catAt (cols t α β) gis).length = true) ∧
      (∀ col ∈ catAt (cols t α β) gis, col.length = m + 1) ∧
      (∀ i (hi : i < (catAt (cols t α β) gis).length) r (hr : r < ((catAt (cols t α β) gis)[i]).length),
        ((catAt (cols t α β) gis)[i])[r] = Tb.main r i) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = Tb.pre r i))
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hgd : ∀ α β v, ∀ c ∈ (AF α β v).cons, c.guarded = true) (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {k lq D s : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (k + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hD : ∀ α β v, ∀ e ∈ (AF α β v).cons, e.pdeg ≤ D) (hDlq : D ≤ 2 ^ lq)
    (hsd : ∀ α β v, ∀ e ∈ (AF α β v).cons, e.sdeg ≤ s) (hs : s < m + 1) (hPsz : D * (2 * (m + 1) - 1) + s + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (hok : ∀ c ∈ (airQTabG AF g m preP gis κ cs Hl cl S ζ ws).sets, c.OK)
    (hHn : ∀ ch ∈ cs, ch.H.Nodup) (hHln : Hl.Nodup) :
    ∀ t α β ms, good t α β → TabsHonest
      (fun c => c.JS α β (vt t α β) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (vt t α β) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      [airQTabG AF g m preP gis κ cs Hl cl S ζ ws]
      [airData (AF α β (vt t α β)) g m preP cs Hl ws α β
        (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) gis)] := by
  intro t α β ms hgood
  let v := vt t α β
  let o := openMulti (qs.map QGroup.ext) (cols t α β) ms
  let mp := mpolysMulti (qs.map QGroup.ext) (cols t α β) ms
  obtain ⟨Tb, hsat, hh, hwin, hlen, hval, hpre⟩ := hsatT t α β hgood
  have hHlen : (cosetL 1 g (m + 1)).length = m + 1 := cosetL_length 1 g (m + 1)
  -- each group: honest openings and interpolating masked columns, with one mask slice
  have hgroup : ∀ j ∈ gis, ∃ R : List F, R.length ≤ m + 1 ∧
      HonestOpen (S ++ S.map (g * ·)) [ζ, (EF.ofF g).mul ζ] (o.getD j []) (mp.getD j []) ∧
      ColsOn (cosetL 1 g (m + 1)) (mp.getD j []) ((cols t α β).getD j []) ∧
      ∀ p ∈ mp.getD j [], p.length ≤ (cosetL 1 g (m + 1)).length + R.length := fun j hj => by
    obtain ⟨hjq, hT, hSq, hZ, hnx, hnd, hRl⟩ := hgrp j hj
    have hj' : j < (qs.map QGroup.ext).length := by rw [List.length_map]; exact hjq
    obtain ⟨r, ho, hm⟩ := openMulti_at (qs.map QGroup.ext) (cols t α β) ms j hj' (hcl' t α β j hj)
    have hext : (qs.map QGroup.ext)[j]'hj' = QGroup.ext (qs[j]'hjq) := List.getElem_map ..
    rw [hext] at ho hm
    have eS : (QGroup.ext (qs[j]'hjq)).S = S ++ S.map (g * ·) := by
      show (qs[j]'hjq).base.S ++ (qs[j]'hjq).base.S.map (qs[j]'hjq).nxt = _
      rw [hSq, hnx]
    have eT : (QGroup.ext (qs[j]'hjq)).T = cosetL 1 g (m + 1) := hT
    have eZ : (QGroup.ext (qs[j]'hjq)).Z = [ζ, (EF.ofF g).mul ζ] := hZ
    have eR : (QGroup.ext (qs[j]'hjq)).R = (qs[j]'hjq).base.R := rfl
    have eget : (cols t α β).getD j [] = (cols t α β)[j]'(hcl' t α β j hj) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hcl' t α β j hj), Option.getD_some]
    rw [eS, eT, eZ, eR] at ho
    rw [eT, eR] at hm
    refine ⟨(qs[j]'hjq).base.R, hRl, ?_, ?_, ?_⟩
    · show HonestOpen _ _ (o.getD j []) (mp.getD j [])
      rw [show o.getD j [] = _ from ho, show mp.getD j [] = _ from hm]
      exact openAll_honest _ _ _ _ _ _ _
    · show ColsOn _ (mp.getD j []) _
      rw [show mp.getD j [] = _ from hm, eget]
      exact colsOn_mpolys hnd _ r (fun col hcol => by
        rw [hHlen]; exact hlen col (mem_getD_catAt hj (by rw [eget]; exact hcol)))
    · intro p hp
      rw [show mp.getD j [] = _ from hm] at hp
      exact mpolys_mem_len _ _ _ _ _ p hp
  have hO : HonestOpen (S ++ S.map (g * ·)) [ζ, (EF.ofF g).mul ζ] (catAt o gis) (catAt mp gis) :=
    honest_cat o mp gis (fun j hj => by obtain ⟨_, _, h1, _, _⟩ := hgroup j hj; exact h1)
  have hC : ColsOn (cosetL 1 g (m + 1)) (catAt mp gis) (catAt (cols t α β) gis) :=
    colsOn_cat mp (cols t α β) gis (fun j hj => by obtain ⟨_, _, _, h2, _⟩ := hgroup j hj; exact h2)
  have hps : ∀ r i, i < (catAt mp gis).length → r < m + 1 →
      fval (fpow g r) ((catAt mp gis).getD i []) = Tb.main r i := fun r i hi hr => by
    have hi' : i < (catAt (cols t α β) gis).length := by rw [← hC.1]; exact hi
    have hr' : r < ((catAt (cols t α β) gis)[i]).length := by rw [hlen _ (List.getElem_mem hi')]; exact hr
    have := hC.2 i hi hi' r (by rw [hHlen]; exact hr) hr'
    rw [cosetL_getElem g (m + 1) 1 r, one_mul'] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, this]
    exact hval i hi' r hr'
  have hpsL : ∀ p ∈ catAt mp gis, p.length ≤ 2 * (m + 1) := fun p hp => by
    obtain ⟨j, hj, hpj⟩ := mem_catAt hp
    obtain ⟨R, hRl, _, _, hL'⟩ := hgroup j hj
    have := hL' p hpj; omega
  have hwin' : ∀ c ∈ (AF α β v).cons, c.win (catAt mp gis).length = true := fun c hc' => by rw [hC.1]; exact hwin c hc'
  have hdl : ∀ H ∈ cs.map (·.H) ++ [Hl], H.length = m + 1 := fun H hH => by
    rw [hdom] at hH; exact split_length hH
  refine ⟨⟨hok, fun ch hch => ⟨hdl _ (List.mem_append_left _ (List.mem_map_of_mem hch)), hHn ch hch⟩,
    hdl _ (List.mem_append_right _ List.mem_cons_self), hHln, ?_, fun d hd => ?_⟩, trivial⟩
  · exact recOK_airG α β _ o _ (fun w => coord_shows_gen hsat hh hg hinj (hgd α β v) hwin' hps hpsL preP hpreL hpre hO
      hζ hS hc hcl hκ hshift hhalf hN hdom hL (hD α β v) hDlq (hsd α β v) hs hPsz hw w) ws
  · obtain ⟨w, _, rfl⟩ := List.mem_map.1 hd
    refine ⟨fun q hq => ?_, ?_⟩
    · obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hq
      have := chunkOf_length ch.H (fdivH (cosetL 1 g (m + 1)) (cpoly (stdRho g
        (fun i => (catAt mp gis).getD i []) preP (selF g m) (selL g m) (selT g m)) (w α β) (AF α β v).cons))
      rw [hdl _ (List.mem_append_left _ (List.mem_map_of_mem hch))] at this
      exact this
    · have := chunkOf_length Hl (fdivH (cosetL 1 g (m + 1)) (cpoly (stdRho g
        (fun i => (catAt mp gis).getD i []) preP (selF g m) (selL g m) (selT g m)) (w α β) (AF α β v).cons))
      rw [hdl _ (List.mem_append_right _ List.mem_cons_self)] at this
      exact this

/-- **The canonical data are honest**: at any challenges, transcript
    values and openings, the canonical chunks built from a table's
    targets (`canonData`) meet `TabsHonest`. -/
theorem tabsHonest_canon {T : QTab} (α β : EF) (v : List EF) (o : List (List (List F × List EF)))
    (hok : ∀ c ∈ T.sets, c.OK) (hH : ∀ ch ∈ T.cs, ch.H.length = T.h ∧ ch.H.Nodup) (hHl : T.Hl.length = T.h)
    (hHln : T.Hl.Nodup) :
    TabsHonest (fun c => c.JS α β v o) (fun c => c.Jζ α β v o) [T] [canonData T.sets α β v o] := by
  obtain ⟨rc, sc⟩ := recOK_canon α β v o T.sets hok
  refine ⟨⟨hok, hH, hHl, hHln, rc, fun d hd => ?_⟩, trivial⟩
  obtain ⟨c, hc, h1, h2⟩ := sc d hd
  have hch : c.h = T.h := by
    unfold QTab.sets at hc; obtain ⟨_, _, rfl⟩ := List.mem_map.1 hc; rfl
  rw [hch] at h1 h2
  exact ⟨h1, h2⟩

/-- **The composed hiding PCS with a table over several groups**:
    `pcsCloseN_fri` at `airQTabG`, its constraints taken at the
    challenges and the transcript's values.  Where `good` holds (no
    message of nonzero count has a vanishing denominator) the data are
    the honest chunks, `TabsHonest` by `tabsHonest_gen`; elsewhere, where
    Plonky3's prover aborts, the canonical chunks (`tabsHonest_canon`). -/
theorem pcsCloseN_fri_gen {V : Type} {ks : List Nat} {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    (good : (Nat → Tup) → EF → EF → Prop) [∀ t α β, Decidable (good t α β)]
    {AF : EF → EF → List EF → AirD} {g : F} {m : Nat} {preP : Nat → List F} {gis : List Nat} {κ : F} {cs : List Chunk}
    {Hl : List F} {cl : F} {S : List F} {ζ : EF} {ws : List (EF → EF → List F)}
    {qs : List QGroup} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hgrp : ∀ j ∈ gis, ∃ hj : j < qs.length, (qs[j]'hj).base.T = cosetL 1 g (m + 1) ∧ (qs[j]'hj).base.S = S ∧
      (qs[j]'hj).base.Z = [ζ, (EF.ofF g).mul ζ] ∧ (qs[j]'hj).nxt = (g * ·) ∧
      (cosetL 1 g (m + 1) ++ (qs[j]'hj).base.R).Nodup ∧ (qs[j]'hj).base.R.length ≤ m + 1)
    (hcl' : ∀ t α β, ∀ j ∈ gis, j < (cols t α β).length)
    (hsatT : ∀ t α β, good t α β → ∃ Tb : Table, Sat (AF α β (tv (prefixOf α (off β)) β t)) Tb ∧ Tb.h = m + 1 ∧
      (∀ c ∈ (AF α β (tv (prefixOf α (off β)) β t)).cons, c.win (catAt (cols t α β) gis).length = true) ∧
      (∀ col ∈ catAt (cols t α β) gis, col.length = m + 1) ∧
      (∀ i (hi : i < (catAt (cols t α β) gis).length) r (hr : r < ((catAt (cols t α β) gis)[i]).length),
        ((catAt (cols t α β) gis)[i])[r] = Tb.main r i) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = Tb.pre r i))
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hgd : ∀ α β v, ∀ c ∈ (AF α β v).cons, c.guarded = true) (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {k lq D s : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ k) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (k + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hD : ∀ α β v, ∀ e ∈ (AF α β v).cons, e.pdeg ≤ D) (hDlq : D ≤ 2 ^ lq)
    (hsd : ∀ α β v, ∀ e ∈ (AF α β v).cons, e.sdeg ≤ s) (hs : s < m + 1) (hPsz : D * (2 * (m + 1) - 1) + s + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (hok : ∀ c ∈ (airQTabG AF g m preP gis κ cs Hl cl S ζ ws).sets, c.OK)
    (hHn : ∀ ch ∈ cs, ch.H.Nodup) (hHln : Hl.Nodup)  (hokq : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (hdet : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw) :
    PCSCloseN off (P ^ (friN1 qs ks [airQTabG AF g m preP gis κ cs Hl cl S ζ ws] +
        friN2 qs [airQTabG AF g m preP gis κ cs Hl cl S ζ ws] ncw)) tv
      (pcsFri off tv qs ks cols [airQTabG AF g m preP gis κ cs Hl cl S ζ ws]
        (fun t α β ms => [if good t α β then airData (AF α β (tv (prefixOf α (off β)) β t)) g m preP cs Hl ws α β
          (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) gis)
          else canonData (airQTabG AF g m preP gis κ cs Hl cl S ζ ws).sets α β (tv (prefixOf α (off β)) β t)
            (openMulti (qs.map QGroup.ext) (cols t α β) ms)])
        ncw αb fri)
      (psimFri qs ks [airQTabG AF g m preP gis κ cs Hl cl S ζ ws] ncw αb fri) 0 :=
  pcsCloseN_fri hokq hks hcols hdet haw hncw off tv (fun t α β ms => by
    by_cases hg' : good t α β
    · rw [if_pos hg']
      exact tabsHonest_gen (fun t α β => tv (prefixOf α (off β)) β t) good hgrp hcl' hsatT hg hinj hgd hpreL hζ hS hc
        hcl hκ hshift hhalf hN hdom hL hD hDlq hsd hs hPsz hw hok hHn hHln t α β ms hg'
    · rw [if_neg hg']
      have hdl : ∀ H ∈ cs.map (·.H) ++ [Hl], H.length = m + 1 := fun H hH => by
        rw [hdom] at hH; exact split_length hH
      exact tabsHonest_canon α β _ _ hok
        (fun ch hch => ⟨hdl _ (List.mem_append_left _ (List.mem_map_of_mem hch)), hHn ch hch⟩)
        (hdl _ (List.mem_append_right _ List.mem_cons_self)) hHln)

end Circuit
