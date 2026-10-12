import Ski.ZK.QuotFold
import Ski.ZK.QuotSat

/-!
# The targets from the opened values

`shows_sat` gives the honest chunks' targets `airTg`, `airTgE` over the
column polynomials.  The `CSet` targets of `pcsCloseN_chunks` are
functions of the groups' openings at `S ++ g S` and `Z` (`openMulti`
over `QGroup.ext`): the verifier sees the openings at `S` and `ζ, g ζ`,
and the simulator samples them jointly with those at `g S`
(`MaskQuot`).  This file reads the targets from that joint sample and
shows they agree with the honest ones.  At `ζ` the reading uses only
the verifier's openings.

A quotient group opens its masked columns at `S ++ g S` and at the
out-of-domain points `ζ, g ζ` (`QGroup.ext`, `openAll`).  A leaf at row
offset 0 or 1 at a query point `x = S[k]` is then the opened value at
index `k` or `|S| + k`, and at `ζ` the opening at `ζ` or `g ζ`
(`ρOpen`, `ρOpenE`).  The preprocessed columns and the selectors are
public polynomials.  For honest openings and constraints whose offsets
are 0 or 1 (`E.win`), these leaves are the column polynomials' values
(`ρOpen_honest`, `ρOpenE_honest`), so the targets read from the
openings are the honest targets (`airTg_open`, `airTgE_open`).
-/

namespace Circuit

open ZKF

/-- The first index of `x` in `S`. -/
def idxIn (x : F) : List F → Nat
  | [] => 0
  | y :: ys => if y = x then 0 else idxIn x ys + 1

theorem idxIn_spec {x : F} : ∀ {S : List F}, x ∈ S → ∃ h : idxIn x S < S.length, S[idxIn x S] = x
  | [], hx => nomatch hx
  | y :: ys, hx => by
    by_cases hy : y = x
    · have e : idxIn x (y :: ys) = 0 := if_pos hy
      exact ⟨by rw [e]; exact Nat.succ_pos _, by simp only [e]; exact hy⟩
    · have e : idxIn x (y :: ys) = idxIn x ys + 1 := if_neg hy
      have hx' : x ∈ ys := (List.mem_cons.1 hx).resolve_left (fun h => hy h.symm)
      obtain ⟨h1, h2⟩ := idxIn_spec hx'
      exact ⟨by rw [e]; exact Nat.succ_lt_succ h1, by simp only [e]; exact h2⟩

/-- Every main leaf at offset 0 or 1 and column below `w`. -/
def E.win (w : Nat) : E → Bool
  | .atom (.main o i) => decide (o ≤ 1) && decide (i < w)
  | .atom _ => true
  | .const _ => true
  | .add a b | .sub a b | .mul a b => a.win w && b.win w
  | .neg a => a.win w

/-- Two leaf assignments agreeing on the window give one value. -/
theorem eval_win {w : Nat} {ρ ρ' : Atom → F}
    (h : ∀ a, (∀ o i, a = .main o i → o ≤ 1 ∧ i < w) → ρ a = ρ' a) : ∀ e : E, e.win w = true → e.eval ρ = e.eval ρ'
  | .atom (.main o i), hw => by
    have := Bool.and_eq_true_iff.1 hw
    exact h _ (fun o' i' e => by
      cases e; exact ⟨of_decide_eq_true this.1, of_decide_eq_true this.2⟩)
  | .atom (.pre o i), _ => h _ (fun _ _ e => nomatch e)
  | .atom .first, _ => h _ (fun _ _ e => nomatch e)
  | .atom .last, _ => h _ (fun _ _ e => nomatch e)
  | .atom .trans, _ => h _ (fun _ _ e => nomatch e)
  | .const _, _ => rfl
  | .add a b, hw => by
    have := Bool.and_eq_true_iff.1 hw
    show _ + _ = _ + _; rw [eval_win h a this.1, eval_win h b this.2]
  | .sub a b, hw => by
    have := Bool.and_eq_true_iff.1 hw
    show _ - _ = _ - _; rw [eval_win h a this.1, eval_win h b this.2]
  | .mul a b, hw => by
    have := Bool.and_eq_true_iff.1 hw
    show _ * _ = _ * _; rw [eval_win h a this.1, eval_win h b this.2]
  | .neg a, hw => by show -_ = -_; rw [eval_win h a hw]

theorem evalE_win {w : Nat} {ρ ρ' : Atom → EF}
    (h : ∀ a, (∀ o i, a = .main o i → o ≤ 1 ∧ i < w) → ρ a = ρ' a) : ∀ e : E, e.win w = true → e.evalE ρ = e.evalE ρ'
  | .atom (.main o i), hw => by
    have := Bool.and_eq_true_iff.1 hw
    exact h _ (fun o' i' e => by
      cases e; exact ⟨of_decide_eq_true this.1, of_decide_eq_true this.2⟩)
  | .atom (.pre o i), _ => h _ (fun _ _ e => nomatch e)
  | .atom .first, _ => h _ (fun _ _ e => nomatch e)
  | .atom .last, _ => h _ (fun _ _ e => nomatch e)
  | .atom .trans, _ => h _ (fun _ _ e => nomatch e)
  | .const _, _ => rfl
  | .add a b, hw => by
    have := Bool.and_eq_true_iff.1 hw
    show EF.add _ _ = EF.add _ _; rw [evalE_win h a this.1, evalE_win h b this.2]
  | .sub a b, hw => by
    have := Bool.and_eq_true_iff.1 hw
    show EF.sub _ _ = EF.sub _ _; rw [evalE_win h a this.1, evalE_win h b this.2]
  | .mul a b, hw => by
    have := Bool.and_eq_true_iff.1 hw
    show EF.mul _ _ = EF.mul _ _; rw [evalE_win h a this.1, evalE_win h b this.2]
  | .neg a, hw => by show EF.mul _ _ = EF.mul _ _; rw [evalE_win h a hw]

/-- **The leaves from the openings** at a query point `x ∈ S`: main column
    `i` at offset 0 or 1 is the opened value at index `k` or `|S| + k` of
    the points `S ++ g S`, `k` the index of `x`; the preprocessed columns
    and the selectors are public polynomials. -/
def ρOpen (S : List F) (os : List (List F × List EF)) (preP : Nat → List F) (g : F) (m : Nat) (x : F) : Atom → F
  | .main 0 i => (colsAt os (idxIn x S)).getD i 0
  | .main 1 i => (colsAt os (S.length + idxIn x S)).getD i 0
  | .main _ _ => 0
  | .pre o i => fval (fpow g o * x) (preP i)
  | .first => fval x (selF g m)
  | .last => fval x (selL g m)
  | .trans => fval x (selT g m)

/-- The leaves from the out-of-domain openings: index 0 and 1, the
    openings at `ζ` and `g ζ` when they were taken at `[ζ, g ζ]`. -/
def ρOpenE (os : List (List F × List EF)) (preP : Nat → List F) (g : F) (m : Nat) (ζ : EF) : Atom → EF
  | .main 0 i => ((os.getD i ([], [])).2).getD 0 EF.zero
  | .main 1 i => ((os.getD i ([], [])).2).getD 1 EF.zero
  | .main _ _ => EF.zero
  | .pre o i => fvalE ζ (fshift (fpow g o) (preP i))
  | .first => fvalE ζ (selF g m)
  | .last => fvalE ζ (selL g m)
  | .trans => fvalE ζ (selT g m)

theorem getD_map_lt {α β : Type} (f : α → β) (d : β) (da : α) : ∀ (l : List α) (i : Nat), i < l.length →
    (l.map f).getD i d = f (l.getD i da)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => getD_map_lt f d da l i (Nat.lt_of_succ_lt_succ h)

theorem openAll_snd (T R S : List F) (Z : List EF) (n : Nat) : ∀ (ts : List (List F)) (rs : List F) (i : Nat),
    i < ts.length → ((openAll T R S Z n ts rs).getD i ([], [])).2 =
      Z.map (fun z => fvalE z ((mpolys T R n ts rs).getD i []))
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: ts, rs, i + 1, h => openAll_snd T R S Z n ts (rs.drop n) i (Nat.lt_of_succ_lt_succ h)

/-- **The leaves from honest openings are the column polynomials'**: at
    `x ∈ S`, every leaf in the window, over the masked columns `mpolys`. -/
theorem ρOpen_honest {T R S : List F} {Z : List EF} {n : Nat} {ts : List (List F)} {rs : List F} {g : F} {m : Nat}
    (preP : Nat → List F) {x : F} (hx : x ∈ S) (a : Atom) (ha : ∀ o i, a = .main o i → o ≤ 1 ∧ i < ts.length) :
    ρOpen S (openAll T R (S ++ S.map (g * ·)) Z n ts rs) preP g m x a =
      fval x (stdRho g (fun i => (mpolys T R n ts rs).getD i []) preP (selF g m) (selL g m) (selT g m) a) := by
  obtain ⟨hk, hSk⟩ := idxIn_spec hx
  have hlen : (S ++ S.map (g * ·)).length = S.length + S.length := by rw [List.length_append, List.length_map]
  cases a with
  | main o i =>
    obtain ⟨ho, hi⟩ := ha o i rfl
    have hi' : i < (mpolys T R n ts rs).length := by rw [mpolys_length]; exact hi
    rw [(fval_stdRho x g _ preP _ _ _ o i).1]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ho with rfl | rfl
    · show (colsAt _ (idxIn x S)).getD i 0 = _
      rw [colsAt_openAll T R _ Z n _ (by rw [hlen]; omega) ts rs, getD_map_lt _ _ [] _ i hi',
        List.getElem_append_left hk, hSk]
      show _ = fval (1 * x) _; rw [one_mul']
    · show (colsAt _ (S.length + idxIn x S)).getD i 0 = _
      rw [colsAt_openAll T R _ Z n _ (by rw [hlen]; omega) ts rs, getD_map_lt _ _ [] _ i hi',
        List.getElem_append_right (Nat.le_add_right _ _), List.getElem_map]
      simp only [Nat.add_sub_cancel_left, hSk]
      show _ = fval (1 * g * x) _; rw [one_mul']
  | pre o i => exact ((fval_stdRho x g _ preP _ _ _ o i).2).symm
  | first => rfl
  | last => rfl
  | trans => rfl

/-- At `ζ`: the openings at `ζ` and `g ζ` are the column polynomials'. -/
theorem ρOpenE_honest {T R S : List F} {n : Nat} {ts : List (List F)} {rs : List F} {g : F} {m : Nat}
    (preP : Nat → List F) (ζ : EF) (a : Atom) (ha : ∀ o i, a = .main o i → o ≤ 1 ∧ i < ts.length) :
    ρOpenE (openAll T R S [ζ, (EF.ofF g).mul ζ] n ts rs) preP g m ζ a =
      fvalE ζ (stdRho g (fun i => (mpolys T R n ts rs).getD i []) preP (selF g m) (selL g m) (selT g m) a) := by
  cases a with
  | main o i =>
    obtain ⟨ho, hi⟩ := ha o i rfl
    rw [(fvalE_stdRho ζ g _ preP _ _ _ o i).1]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ho with rfl | rfl
    · show ((openAll T R S _ n ts rs).getD i ([], [])).2.getD 0 EF.zero = _
      rw [openAll_snd T R S _ n ts rs i hi]
      show _ = fvalE ((EF.ofF 1).mul ζ) _
      rw [show EF.ofF 1 = EF.one from rfl, EF.one_mul]; rfl
    · show ((openAll T R S _ n ts rs).getD i ([], [])).2.getD 1 EF.zero = _
      rw [openAll_snd T R S _ n ts rs i hi]
      show _ = fvalE ((EF.ofF (1 * g)).mul ζ) _
      rw [one_mul']; rfl
  | pre o i => rfl
  | first => rfl
  | last => rfl
  | trans => rfl

/-- **The targets read from the openings are the honest targets**, at
    every query point, for constraints in the window. -/
theorem airTg_open {T R S : List F} {Z : List EF} {n : Nat} {ts : List (List F)} {rs : List F} {g : F} {m : Nat}
    (preP : Nat → List F) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F)
    (H ws : List F) (es : List E) (hw : ∀ e ∈ es, e.win ts.length = true) {x : F} (hx : x ∈ S) :
    airTg cs Hl cl qs ql κ H ws es (ρOpen S (openAll T R (S ++ S.map (g * ·)) Z n ts rs) preP g m) x =
      airTg cs Hl cl qs ql κ H ws es
        (fun x a => fval x (stdRho g (fun i => (mpolys T R n ts rs).getD i []) preP (selF g m) (selL g m) (selT g m) a)) x := by
  have e : es.map (·.eval (ρOpen S (openAll T R (S ++ S.map (g * ·)) Z n ts rs) preP g m x)) =
      es.map (·.eval (fun a => fval x (stdRho g (fun i => (mpolys T R n ts rs).getD i []) preP (selF g m) (selL g m)
        (selT g m) a))) :=
    List.map_congr_left (fun e he => eval_win (fun a ha => ρOpen_honest preP hx a ha) e (hw e he))
  unfold airTg; rw [e]

theorem airTgE_open {T R S : List F} {n : Nat} {ts : List (List F)} {rs : List F} {g : F} {m : Nat}
    (preP : Nat → List F) (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F)
    (H ws : List F) (es : List E) (hw : ∀ e ∈ es, e.win ts.length = true) :
    airTgE ζ cs Hl cl qs ql κ H ws es (ρOpenE (openAll T R S [ζ, (EF.ofF g).mul ζ] n ts rs) preP g m ζ) =
      airTgE ζ cs Hl cl qs ql κ H ws es
        (fun a => fvalE ζ (stdRho g (fun i => (mpolys T R n ts rs).getD i []) preP (selF g m) (selL g m) (selT g m) a)) := by
  have e : es.map (·.evalE (ρOpenE (openAll T R S [ζ, (EF.ofF g).mul ζ] n ts rs) preP g m ζ)) =
      es.map (·.evalE (fun a => fvalE ζ (stdRho g (fun i => (mpolys T R n ts rs).getD i []) preP (selF g m) (selL g m)
        (selT g m) a))) :=
    List.map_congr_left (fun e he => evalE_win (fun a ha => ρOpenE_honest preP ζ a ha) e (hw e he))
  unfold airTgE; rw [e]

-- ---------------------------------------------------------------------------
-- The whole: a committed, opened table
-- ---------------------------------------------------------------------------

/-- **A masked column interpolates its values on the trace points.** -/
theorem mcol_on_T {T R t r : List F} (ht : T.length = t.length) (hr : R.length = r.length) (hnd : (T ++ R).Nodup)
    {i : Nat} (hi : i < T.length) : fval T[i] (mcol T R t r) = t[i]'(ht ▸ hi) := by
  unfold mcol
  have hfst : (T.zip t ++ R.zip r).map Prod.fst = T ++ R := by
    rw [List.map_append, map_fst_zip' ht, map_fst_zip' hr]
  exact finterp_eval _ (by rw [hfst]; exact hnd) (T[i], t[i]'(ht ▸ hi)) (List.mem_append_left _ (zip_mem hi ht))

theorem mpolys_getD (T R : List F) (n : Nat) : ∀ (ts : List (List F)) (rs : List F) (i : Nat), i < ts.length →
    (mpolys T R n ts rs).getD i [] = mcol T R (ts.getD i []) ((rs.drop (i * n)).take n)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, rs, 0, _ => by rw [Nat.zero_mul]; rfl
  | _ :: ts, rs, i + 1, h => by
    show (mpolys T R n ts (rs.drop n)).getD i [] = mcol T R (ts.getD i []) ((rs.drop ((i + 1) * n)).take n)
    rw [mpolys_getD T R n ts (rs.drop n) i (Nat.lt_of_succ_lt_succ h), List.drop_drop, Nat.succ_mul, Nat.add_comm n]

theorem cosetL_getElem (g : F) : ∀ (n : Nat) (s : F) (r : Nat) (h : r < (cosetL s g n).length),
    (cosetL s g n)[r] = s * fpow g r
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, 0, _ => by show s = s * 1; rw [mul_one']
  | n + 1, s, r + 1, h => by
    show (cosetL (s * g) g n)[r]'(Nat.lt_of_succ_lt_succ h) = s * fpow g (r + 1)
    rw [cosetL_getElem g n (s * g) r, mul_assoc', fpow_succ']

/-- The table with its main columns at and past `w` zero. -/
def Table.cut (Tb : Table) (w : Nat) : Table := ⟨Tb.h, fun r i => if i < w then Tb.main r i else 0, Tb.pre⟩

/-- **Cutting a table to its width keeps `Sat`** for constraints in the window. -/
theorem sat_cut {A : AirD} {Tb : Table} {w : Nat} (h : Sat A Tb) (hw : ∀ c ∈ A.cons, c.win w = true) :
    Sat A (Tb.cut w) := by
  refine ⟨h.1, fun c hc r hr => ?_⟩
  rw [eval_win (ρ' := Tb.env r) (fun a ha => ?_) c (hw c hc)]
  · exact h.2 c hc r hr
  · cases a with
    | main o i =>
      show (if i < w then Tb.main ((r + o) % Tb.h) i else 0) = _
      rw [if_pos (ha o i rfl).2]; rfl
    | pre o i => rfl
    | first => rfl
    | last => rfl
    | trans => rfl

/-- **An honest table's quotient chunks show the targets read from its
    openings**: a table of `m + 1` rows on `⟨g⟩` that meets `Sat`, whose
    `w` main columns `ts` are committed with masks on `R` and opened, in
    one view, at `S ++ g S` and `ζ, g ζ`, and whose quotient chunks are honest
    (`QuotOK` of the quotient of the masked columns), shows `airTg` and
    `airTgE` over `ρOpen` and `ρOpenE`.  These are functions of the
    openings at `S ++ g S` and `ζ, g ζ` and of public data: the
    constraints, `ws`, `g`, `m`, the preprocessed polynomials, the chunk
    domains `cs`, `Hl`, `cl`, the scale `κ` and `|qs|`. -/
theorem shows_open {A : AirD} {Tb : Table} {g : F} {m : Nat} (hsat : Sat A Tb) (hh : Tb.h = m + 1)
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hgd : ∀ c ∈ A.cons, c.guarded = true) {ts : List (List F)} (hwin : ∀ c ∈ A.cons, c.win ts.length = true)
    (hts : ∀ i (hi : i < ts.length), (ts[i]).length = m + 1 ∧ ∀ r (hr : r < (ts[i]).length), (ts[i])[r] = Tb.main r i)
    {R : List F} {n : Nat} (hR : R.length = n) (hnd : (cosetL 1 g (m + 1) ++ R).Nodup) {rs : List F}
    (hrs : ts.length * n ≤ rs.length) (preP : Nat → List F)
    (hpre : ∀ r i, r < m + 1 → fval (fpow g r) (preP i) = Tb.pre r i)
    {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) {cs : List Chunk} {Hl : List F} {cl : F}
    {qs : List (List F)} {ql : List F} {κ : F} (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (ws : List F)
    (hP : (cpoly (stdRho g (fun i => (mpolys (cosetL 1 g (m + 1)) R n ts rs).getD i []) preP (selF g m) (selL g m)
      (selT g m)) ws A.cons).length ≤ P)
    (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0) (hZ : fvalE ζ (fvan (cosetL 1 g (m + 1))) ≠ EF.zero)
    (hq : QuotOK cs Hl cl qs ql κ (fdivH (cosetL 1 g (m + 1)) (cpoly (stdRho g
      (fun i => (mpolys (cosetL 1 g (m + 1)) R n ts rs).getD i []) preP (selF g m) (selL g m) (selT g m)) ws A.cons))) :
    Shows S ζ cs Hl cl qs ql
      (airTg cs Hl cl qs ql κ (cosetL 1 g (m + 1)) ws A.cons
        (ρOpen S (openAll (cosetL 1 g (m + 1)) R (S ++ S.map (g * ·)) [ζ, (EF.ofF g).mul ζ] n ts rs) preP g m))
      (airTgE ζ cs Hl cl qs ql κ (cosetL 1 g (m + 1)) ws A.cons
        (ρOpenE (openAll (cosetL 1 g (m + 1)) R (S ++ S.map (g * ·)) [ζ, (EF.ofF g).mul ζ] n ts rs) preP g m ζ)) := by
  have hT : (cosetL 1 g (m + 1)).length = m + 1 := cosetL_length 1 g (m + 1)
  have hmain : ∀ r i, r < m + 1 →
      fval (fpow g r) ((mpolys (cosetL 1 g (m + 1)) R n ts rs).getD i []) = (Tb.cut ts.length).main r i := by
    intro r i hr
    show _ = if i < ts.length then Tb.main r i else 0
    by_cases hi : i < ts.length
    · rw [if_pos hi, mpolys_getD _ _ _ ts rs i hi]
      obtain ⟨hl, hv⟩ := hts i hi
      have hrl : ((rs.drop (i * n)).take n).length = n := by
        rw [List.length_take, List.length_drop]
        have : (i + 1) * n ≤ ts.length * n := Nat.mul_le_mul_right n hi
        rw [Nat.succ_mul] at this
        omega
      have hti : (ts.getD i []).length = (cosetL 1 g (m + 1)).length := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hl, hT]
      have := mcol_on_T (t := ts.getD i []) hti.symm (hR.trans hrl.symm) hnd (i := r) (by rw [hT]; exact hr)
      rw [cosetL_getElem g (m + 1) 1 r, one_mul'] at this
      rw [this]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact hv r (by rw [hl]; exact hr)
    · rw [if_neg hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [mpolys_length]; omega)]
      rfl
  have hs := shows_sat (sat_cut hsat hwin) hh hg hinj hgd _ preP hmain hpre hζ hc hcl ws hP hS hZ hq
  exact shows_congr hs (fun x hx => (airTg_open preP cs Hl cl qs ql κ _ ws A.cons hwin hx).symm)
    (airTgE_open preP ζ cs Hl cl qs ql κ _ ws A.cons hwin).symm

end Circuit
