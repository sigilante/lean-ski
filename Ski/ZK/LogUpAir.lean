import Ski.ZK.QuotTwo

/-!
# LogUp's constraints, as constraints

`tabsHonest_gen` takes an AIR family `AF α β v` whose constraints may
include LogUp's.  This file writes them as p3-lookup's `LogUpGadget`
does (`eval_fraction`, `eval_accumulator`).  The permutation trace's
column 0 is the accumulator and column `c + 1` is lookup `c`'s fraction.
Each is an extension column, flattened to four base columns after the
AIR's own columns.
- **fraction**, every row: `(α - comb_β(elements)) · f_c - m_c = 0`, with
  `comb_β` Plonky3's fold `acc · β + e`;
- **first row:** `acc = 0`;
- **transition:** `acc' - acc - Σ_c f_c = 0`;
- **last row:** `terminal - acc - Σ_c f_c = 0`.

The challenges and the terminal enter as constants, so the constraints
are a family in `α, β` and the terminal (`lupCons`).  Their coordinates
(`eq4`) are base constraints.

`lup_sat` is LogUp's completeness, row by row: the honest fractions
`f_c = m_c / (α - comb_β)` and the running sum as the accumulator, with
the terminal the total, meet every constraint on a table whose rows
have no vanishing denominator.

Scope.  Each lookup has one tuple and no flags, and all lookups share
one challenge pair, as the corpus's do.
-/

namespace Circuit

open ZKF

/-- A base expression in the extension. -/
def QE (e : E) : Q := ⟨e, k 0, k 0, k 0⟩

/-- An extension constant. -/
def QC (c : EF) : Q := ⟨k c.x0, k c.x1, k c.x2, k c.x3⟩

/-- The extension column at base columns `i, …, i + 3`, row offset `o`. -/
def QV (i o : Nat) : Q :=
  ⟨.atom (.main o i), .atom (.main o (i + 1)), .atom (.main o (i + 2)), .atom (.main o (i + 3))⟩

/-- A selector times an extension expression, coordinate by coordinate:
    the guarded shape. -/
def Q.sel (s : Atom) (q : Q) : Q :=
  ⟨.mul (.atom s) q.q0, .mul (.atom s) q.q1, .mul (.atom s) q.q2, .mul (.atom s) q.q3⟩

/-- Plonky3's tuple combination, `fold (acc · β + e)` from zero. -/
def comb (β : EF) (es : List E) : Q := es.foldl (fun acc e => (QE e).add (acc.mul (QC β))) (QC EF.zero)

/-- `Σ_c f_c`, the fractions at base columns `fis`. -/
def sumQ (o : Nat) : List Nat → Q
  | [] => QC EF.zero
  | i :: is => (QV i o).add (sumQ o is)

/-- **A lookup's fraction constraint**: `(α - comb_β(es)) · f - m`. -/
def fracQ (α β : EF) (es : List E) (m : E) (fi : Nat) : Q :=
  (((QC α).sub (comb β es)).mul (QV fi 0)).sub (QE m)

/-- **LogUp's constraints** for the lookups `Ls`, the accumulator at base
    column `w` and lookup `c`'s fraction at `w + 4 (c + 1)`. -/
def lupCons (α β terminal : EF) (w : Nat) (Ls : List (List E × E)) : List Q :=
  let fis := (List.range Ls.length).map fun c => w + 4 * (c + 1)
  (List.range Ls.length).zipWith (fun c L => fracQ α β L.1 L.2 (w + 4 * (c + 1))) Ls ++
  [Q.sel .first (QV w 0),
   Q.sel .trans (((QV w 1).sub (QV w 0)).sub (sumQ 0 fis)),
   Q.sel .last (((QC terminal).sub (QV w 0)).sub (sumQ 0 fis))]

-- ---------------------------------------------------------------------------
-- Values
-- ---------------------------------------------------------------------------

theorem QE_eval (ρ : Atom → F) (e : E) : (QE e).eval ρ = EF.ofF (e.eval ρ) := rfl
theorem QC_eval (ρ : Atom → F) (c : EF) : (QC c).eval ρ = c := rfl

theorem sel_eval (ρ : Atom → F) (s : Atom) (q : Q) : (Q.sel s q).eval ρ = (EF.ofF (ρ s)).mul (q.eval ρ) := by
  refine EF.ext ?_ ?_ ?_ ?_
  · rw [ofF_mul_x0]; rfl
  · rw [ofF_mul_x1]; rfl
  · rw [ofF_mul_x2]; rfl
  · rw [ofF_mul_x3]; rfl

/-- The combination's value: Plonky3's fold over the elements' values. -/
def combV (β : EF) (vs : List F) : EF := vs.foldl (fun acc v => (EF.ofF v).add (acc.mul β)) EF.zero

theorem comb_eval_aux (ρ : Atom → F) (β : EF) : ∀ (es : List E) (q : Q),
    (es.foldl (fun acc e => (QE e).add (acc.mul (QC β))) q).eval ρ =
      (es.map (·.eval ρ)).foldl (fun acc v => (EF.ofF v).add (acc.mul β)) (q.eval ρ)
  | [], _ => rfl
  | e :: es, q => by
    rw [List.foldl_cons, comb_eval_aux ρ β es, List.map_cons, List.foldl_cons]
    rfl

theorem comb_eval (ρ : Atom → F) (β : EF) (es : List E) : (comb β es).eval ρ = combV β (es.map (·.eval ρ)) :=
  comb_eval_aux ρ β es (QC EF.zero)

theorem fracQ_eval (ρ : Atom → F) (α β : EF) (es : List E) (m : E) (fi : Nat) :
    (fracQ α β es m fi).eval ρ =
      ((α.sub (combV β (es.map (·.eval ρ)))).mul ((QV fi 0).eval ρ)).sub (EF.ofF (m.eval ρ)) := by
  show ((((QC α).sub (comb β es)).eval ρ).mul ((QV fi 0).eval ρ)).sub ((QE m).eval ρ) = _
  rw [show ((QC α).sub (comb β es)).eval ρ = ((QC α).eval ρ).sub ((comb β es).eval ρ) from rfl, comb_eval]
  rfl

/-- **A constraint over the extension vanishes coordinate by coordinate.** -/
theorem eq4_zero (ρ : Atom → F) (q : Q) (h : q.eval ρ = EF.zero) :
    q.q0.eval ρ = 0 ∧ q.q1.eval ρ = 0 ∧ q.q2.eval ρ = 0 ∧ q.q3.eval ρ = 0 :=
  ⟨congrArg EF.x0 h, congrArg EF.x1 h, congrArg EF.x2 h, congrArg EF.x3 h⟩

-- ---------------------------------------------------------------------------
-- The honest permutation trace
-- ---------------------------------------------------------------------------

/-- An extension element's coordinate. -/
def coordOf (x : EF) : Nat → F
  | 0 => x.x0
  | 1 => x.x1
  | 2 => x.x2
  | _ => x.x3

section
variable (Tb : Table) (α β : EF) (Ls : List (List E × E))

/-- **Lookup `c`'s honest fraction** at row `r`: `m / (α - comb_β)`. -/
def fV (c r : Nat) : EF :=
  (EF.ofF ((Ls.getD c ([], .const 0)).2.eval (Tb.env r))).mul
    (α.sub (combV β ((Ls.getD c ([], .const 0)).1.map (·.eval (Tb.env r))))).inv

/-- `Σ_c f_c` at row `r`, over the lookups `cs`. -/
def fsum (r : Nat) : List Nat → EF
  | [] => EF.zero
  | c :: cs => (fV Tb α β Ls c r).add (fsum r cs)

/-- **The honest accumulator**: the running sum of the rows before. -/
def accV : Nat → EF
  | 0 => EF.zero
  | r + 1 => (accV r).add (fsum Tb α β Ls r (List.range Ls.length))

/-- The permutation column `j` at row `r`: the accumulator, then each fraction. -/
def permV (j r : Nat) : EF := if j = 0 then accV Tb α β Ls r else fV Tb α β Ls (j - 1) r

/-- **The table with its honest permutation columns** after the AIR's `w`
    columns, each extension column as four base columns. -/
def withPerm (w : Nat) : Table :=
  ⟨Tb.h, fun r i => if i < w then Tb.main r i else coordOf (permV Tb α β Ls ((i - w) / 4) r) ((i - w) % 4), Tb.pre⟩
end

theorem QV_eval_perm (Tb : Table) (α β : EF) (Ls : List (List E × E)) (w j o r : Nat) :
    (QV (w + 4 * j) o).eval ((withPerm Tb α β Ls w).env r) = permV Tb α β Ls j ((r + o) % Tb.h) := by
  have hc : ∀ kk, kk < 4 → (withPerm Tb α β Ls w).main ((r + o) % Tb.h) (w + 4 * j + kk) =
      coordOf (permV Tb α β Ls j ((r + o) % Tb.h)) kk := fun kk hk => by
    show (if w + 4 * j + kk < w then _ else _) = _
    rw [if_neg (by omega), show (w + 4 * j + kk - w) / 4 = j by omega, show (w + 4 * j + kk - w) % 4 = kk by omega]
  refine EF.ext ?_ ?_ ?_ ?_
  · exact hc 0 (by decide)
  · exact hc 1 (by decide)
  · exact hc 2 (by decide)
  · exact hc 3 (by decide)

theorem env_perm_lt (Tb : Table) (α β : EF) (Ls : List (List E × E)) (w r : Nat) (e : E) (he : e.win w = true) :
    e.eval ((withPerm Tb α β Ls w).env r) = e.eval (Tb.env r) :=
  eval_win (fun a ha => by
    cases a with
    | main o i =>
      show (if i < w then _ else _) = _
      rw [if_pos (ha o i rfl).2]; rfl
    | pre o i => rfl
    | first => rfl
    | last => rfl
    | trans => rfl) e he

theorem sumQ_eval (Tb : Table) (α β : EF) (Ls : List (List E × E)) (w r : Nat) (hr : r < Tb.h) :
    ∀ cs : List Nat, (sumQ 0 (cs.map fun c => w + 4 * (c + 1))).eval ((withPerm Tb α β Ls w).env r) =
      fsum Tb α β Ls r cs
  | [] => rfl
  | c :: cs => by
    show ((QV (w + 4 * (c + 1)) 0).eval _).add ((sumQ 0 (cs.map _)).eval _) = (fV Tb α β Ls c r).add (fsum Tb α β Ls r cs)
    rw [QV_eval_perm, sumQ_eval Tb α β Ls w r hr cs]
    simp only [Nat.add_zero, Nat.mod_eq_of_lt hr]
    unfold permV
    rw [if_neg (by omega), show c + 1 - 1 = c by omega]

theorem frac_cancel (D M : EF) (hD : D ≠ EF.zero) : (D.mul (M.mul D.inv)).sub M = EF.zero := by
  rw [EF.mul_comm M, ← EF.mul_assoc, EF.mul_inv hD, EF.one_mul, EF.sub_self]

theorem acc_step (a b : EF) : ((a.add b).sub a).sub b = EF.zero :=
  EF.ext (fid (e := (v 0 + v 1 - v 0) - v 1) (e' := .const 0) (by decide) [a.x0, b.x0])
    (fid (e := (v 0 + v 1 - v 0) - v 1) (e' := .const 0) (by decide) [a.x1, b.x1])
    (fid (e := (v 0 + v 1 - v 0) - v 1) (e' := .const 0) (by decide) [a.x2, b.x2])
    (fid (e := (v 0 + v 1 - v 0) - v 1) (e' := .const 0) (by decide) [a.x3, b.x3])

theorem ofF1_mul (x : EF) : (EF.ofF 1).mul x = x := by rw [show EF.ofF 1 = EF.one from rfl, EF.one_mul]

/-- **Every LogUp constraint holds on the honest table**: on every row, each
    constraint of `lupCons` with the terminal the total sum, when the
    lookups' tuples and multiplicities are in the AIR's window and no
    denominator vanishes. -/
theorem lup_rows (Tb : Table) (α β : EF) (Ls : List (List E × E)) (w : Nat)
    (hwin : ∀ L ∈ Ls, (∀ e ∈ L.1, e.win w = true) ∧ L.2.win w = true)
    (hden : ∀ c, c < Ls.length → ∀ r, r < Tb.h →
      α.sub (combV β ((Ls.getD c ([], .const 0)).1.map (·.eval (Tb.env r)))) ≠ EF.zero) :
    ∀ q ∈ lupCons α β (accV Tb α β Ls Tb.h) w Ls, ∀ r, r < Tb.h →
      q.eval ((withPerm Tb α β Ls w).env r) = EF.zero := by
  intro q hq r hr
  have hmod : r % Tb.h = r := Nat.mod_eq_of_lt hr
  rcases List.mem_append.1 hq with hq | hq
  · -- a fraction
    obtain ⟨c, hc, L, hL, rfl⟩ : ∃ c, c < Ls.length ∧ ∃ L, Ls.getD c ([], .const 0) = L ∧
        q = fracQ α β L.1 L.2 (w + 4 * (c + 1)) := by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
      rw [List.length_zipWith, List.length_range, Nat.min_self] at hi
      refine ⟨i, hi, Ls[i], ?_, ?_⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      · rw [List.getElem_zipWith, List.getElem_range]
    subst hL
    have hmem : Ls.getD c ([], .const 0) ∈ Ls := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]; exact List.getElem_mem hc
    obtain ⟨hes, hm⟩ := hwin _ hmem
    rw [fracQ_eval, QV_eval_perm]
    simp only [Nat.add_zero, hmod]
    rw [env_perm_lt Tb α β Ls w r _ hm,
      List.map_congr_left (fun e he => env_perm_lt Tb α β Ls w r e (hes e he))]
    show _ = EF.zero
    unfold permV
    rw [if_neg (by omega), show c + 1 - 1 = c by omega]
    exact frac_cancel _ _ (hden c hc r hr)
  · have hfs : (sumQ 0 ((List.range Ls.length).map fun c => w + 4 * (c + 1))).eval
        ((withPerm Tb α β Ls w).env r) = fsum Tb α β Ls r (List.range Ls.length) := sumQ_eval Tb α β Ls w r hr _
    have hacc : ∀ o, (QV w o).eval ((withPerm Tb α β Ls w).env r) = accV Tb α β Ls ((r + o) % Tb.h) := fun o => by
      have := QV_eval_perm Tb α β Ls w 0 o r
      rw [Nat.mul_zero, Nat.add_zero] at this
      rw [this]; rfl
    rcases List.mem_cons.1 hq with rfl | hq
    · -- first row: the accumulator is zero
      rw [sel_eval, hacc]
      simp only [Nat.add_zero, hmod]
      show (EF.ofF (if r = 0 then 1 else 0)).mul _ = _
      by_cases h0 : r = 0
      · rw [if_pos h0, h0]; exact EF.mul_zero _
      · rw [if_neg h0]; exact EF.ofF_zero_mul _
    rcases List.mem_cons.1 hq with rfl | hq
    · -- transition: the accumulator adds the row's fractions
      rw [sel_eval]
      show (EF.ofF (if r + 1 = (withPerm Tb α β Ls w).h then 0 else 1)).mul _ = _
      by_cases hl : r + 1 = (withPerm Tb α β Ls w).h
      · rw [if_pos hl]; exact EF.ofF_zero_mul _
      · rw [if_neg hl, ofF1_mul]
        have hl' : r + 1 < Tb.h := by have : (withPerm Tb α β Ls w).h = Tb.h := rfl; omega
        show (((QV w 1).eval _).sub ((QV w 0).eval _)).sub ((sumQ 0 _).eval _) = _
        rw [hacc, hacc, hfs]
        simp only [Nat.add_zero, hmod, Nat.mod_eq_of_lt hl']
        exact acc_step _ _
    rcases List.mem_cons.1 hq with rfl | hq
    · -- last row: the terminal is the total
      rw [sel_eval]
      show (EF.ofF (if r + 1 = (withPerm Tb α β Ls w).h then 1 else 0)).mul _ = _
      by_cases hl : r + 1 = (withPerm Tb α β Ls w).h
      · rw [if_pos hl, ofF1_mul]
        have hl' : Tb.h = r + 1 := hl.symm
        show (((QC _).eval _).sub ((QV w 0).eval _)).sub ((sumQ 0 _).eval _) = _
        rw [QC_eval, hacc, hfs]
        simp only [Nat.add_zero, hmod]
        rw [hl']
        exact acc_step _ _
      · rw [if_neg hl]; exact EF.ofF_zero_mul _
    · nomatch hq

theorem mem_eq4 {e : E} : ∀ {qs : List Q}, e ∈ eq4 qs → ∃ q ∈ qs, e = q.q0 ∨ e = q.q1 ∨ e = q.q2 ∨ e = q.q3
  | [], h => nomatch h
  | q :: qs, h => by
    rcases List.mem_cons.1 h with h | h
    · exact ⟨q, List.mem_cons_self, .inl h⟩
    rcases List.mem_cons.1 h with h | h
    · exact ⟨q, List.mem_cons_self, .inr (.inl h)⟩
    rcases List.mem_cons.1 h with h | h
    · exact ⟨q, List.mem_cons_self, .inr (.inr (.inl h))⟩
    rcases List.mem_cons.1 h with h | h
    · exact ⟨q, List.mem_cons_self, .inr (.inr (.inr h))⟩
    obtain ⟨q', hq', e'⟩ := mem_eq4 h
    exact ⟨q', List.mem_cons_of_mem _ hq', e'⟩

/-- An AIR with LogUp's constraints over its permutation columns. -/
def withLup (A : AirD) (α β terminal : EF) (w : Nat) (Ls : List (List E × E)) : AirD :=
  { A with cons := A.cons ++ eq4 (lupCons α β terminal w Ls) }

/-- **LogUp's completeness, row by row**: a table that meets `Sat` for an
    AIR whose `w` columns hold every constraint's and lookup's leaves,
    with the honest permutation columns appended, meets `Sat` for the AIR
    with LogUp's constraints, the terminal the total, when no denominator
    vanishes. -/
theorem lup_sat {A : AirD} {Tb : Table} (h : Sat A Tb) (α β : EF) (Ls : List (List E × E)) (w : Nat)
    (hA : ∀ c ∈ A.cons, c.win w = true)
    (hwin : ∀ L ∈ Ls, (∀ e ∈ L.1, e.win w = true) ∧ L.2.win w = true)
    (hden : ∀ c, c < Ls.length → ∀ r, r < Tb.h →
      α.sub (combV β ((Ls.getD c ([], .const 0)).1.map (·.eval (Tb.env r)))) ≠ EF.zero) :
    Sat (withLup A α β (accV Tb α β Ls Tb.h) w Ls) (withPerm Tb α β Ls w) := by
  refine ⟨h.1, fun c hc r hr => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · rw [env_perm_lt Tb α β Ls w r c (hA c hc)]; exact h.2 c hc r hr
  · obtain ⟨q, hq, e⟩ := mem_eq4 hc
    have := eq4_zero _ q (lup_rows Tb α β Ls w hwin hden q hq r hr)
    rcases e with rfl | rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2.1
    · exact this.2.2.2

end Circuit
