import Ski.Circuit.BaseComplete

/-!
# Plonky3's selectors, as they are

Plonky3 does not evaluate its first-row, last-row and transition
selectors to `0` and `1`: on the trace domain the first-row selector is
the domain size on row 0, the last-row selector a nonzero value on the
last row, the transition selector `x - g⁻¹`, nonzero off the last row;
each is `0` elsewhere.  `SatP` reads the constraints with **any**
selectors of that zero pattern (`Sels`), so it covers Plonky3's own.

For AIRs whose constraints use a selector only as a factor of the whole
constraint (`guarded`, decided on the data), `SatP` is `Sat`
(`satP_iff`).  The corpus circuit's constraints are guarded (`base_guarded`),
and AIRs with the same normal forms satisfy the same constraints under any
selectors (`satP_transfer`), so for the Rust AIRs, acceptance with Plonky3's
selectors is acceptance as `Accepted` states it (`acceptedP_iff`), and
soundness and completeness hold with them (`export_sound_P`,
`export_complete_P`).
-/

namespace Circuit

open B Air Mach

/-- Selector values on a table of height `h`, with Plonky3's zero pattern. -/
structure Sels (h : Nat) where
  first : Nat → F
  last : Nat → F
  trans : Nat → F
  first_zero : ∀ r, first r = 0 ↔ r ≠ 0
  last_zero : ∀ r, last r = 0 ↔ r + 1 ≠ h
  trans_zero : ∀ r, trans r = 0 ↔ r + 1 = h

/-- The leaves' values at row `r` with selectors `σ`. -/
def Table.envP (T : Table) (σ : Sels T.h) (r : Nat) : Atom → F
  | .main o i => T.main ((r + o) % T.h) i
  | .pre o i => T.pre ((r + o) % T.h) i
  | .first => σ.first r
  | .last => σ.last r
  | .trans => σ.trans r

/-- **Every constraint vanishes on every row**, with selectors `σ`. -/
def SatP (A : AirD) (T : Table) (σ : Sels T.h) : Prop :=
  0 < T.h ∧ ∀ c ∈ A.cons, ∀ r, r < T.h → c.eval (T.envP σ r) = 0

def Atom.isSel : Atom → Bool
  | .first | .last | .trans => true
  | _ => false

/-- No selector in the expression. -/
def E.selFree : E → Bool
  | .atom a => !a.isSel
  | .const _ => true
  | .add a b | .sub a b | .mul a b => a.selFree && b.selFree
  | .neg a => a.selFree

/-- A selector only as a factor of the whole constraint. -/
def E.guarded : E → Bool
  | .mul (.atom s) b => (s.isSel && b.selFree) || (!s.isSel && b.selFree)
  | e => e.selFree

theorem E.eval_selFree {ρ ρ' : Atom → F} (h : ∀ a, a.isSel = false → ρ a = ρ' a) :
    ∀ e : E, e.selFree = true → e.eval ρ = e.eval ρ'
  | .atom a, he => by simp only [E.selFree, Bool.not_eq_true'] at he; exact h a he
  | .const _, _ => rfl
  | .add a b, he | .sub a b, he | .mul a b, he => by
    simp only [E.selFree, Bool.and_eq_true] at he
    simp only [E.eval, E.eval_selFree h a he.1, E.eval_selFree h b he.2]
  | .neg a, he => by simp only [E.selFree] at he; simp only [E.eval, E.eval_selFree h a he]

theorem envP_agree (T : Table) (σ : Sels T.h) (r : Nat) :
    ∀ a, a.isSel = false → T.envP σ r a = T.env r a
  | .main _ _, _ => rfl
  | .pre _ _, _ => rfl

/-- A selector's value is zero exactly when its `0`/`1` value is. -/
theorem sel_zero_iff (T : Table) (σ : Sels T.h) (r : Nat) :
    ∀ s, s.isSel = true → (T.envP σ r s = 0 ↔ T.env r s = 0) ∧ (T.env r s = 0 ∨ T.env r s = 1)
  | .first, _ => by
    simp only [Table.envP, Table.env, σ.first_zero]
    by_cases h : r = 0 <;> simp [h] <;> decide
  | .last, _ => by
    simp only [Table.envP, Table.env, σ.last_zero]
    by_cases h : r + 1 = T.h <;> simp [h] <;> decide
  | .trans, _ => by
    simp only [Table.envP, Table.env, σ.trans_zero]
    by_cases h : r + 1 = T.h <;> simp [h] <;> decide

/-- **A guarded constraint vanishes with any selectors of the pattern
    exactly when it vanishes with `0`/`1` selectors.** -/
theorem guarded_iff (T : Table) (σ : Sels T.h) (r : Nat) :
    ∀ e : E, e.guarded = true → (e.eval (T.envP σ r) = 0 ↔ e.eval (T.env r) = 0)
  | .mul (.atom s) b, he => by
    simp only [E.guarded, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at he
    have hb : b.selFree = true := by rcases he with h | h <;> exact h.2
    have eb := E.eval_selFree (envP_agree T σ r) b hb
    simp only [E.eval, eb]
    cases hs : s.isSel with
    | false => rw [envP_agree T σ r s hs]
    | true =>
      obtain ⟨hz, h01⟩ := sel_zero_iff T σ r s hs
      constructor
      · intro h
        rcases mul_eq_zero h with h | h
        · rw [hz.1 h, zero_mul']
        · rw [h, mul_zero']
      · intro h
        rcases h01 with h0 | h1
        · rw [hz.2 h0, zero_mul']
        · rw [h1, one_mul'] at h; rw [h, mul_zero']
  | .atom a, he => by
    rw [E.eval_selFree (envP_agree T σ r) _ (by simpa [E.guarded] using he)]
  | .const _, _ => Iff.rfl
  | .add a b, he | .sub a b, he | .neg a, he => by
    rw [E.eval_selFree (envP_agree T σ r) _ (by simpa [E.guarded] using he)]
  | .mul (.const c) b, he | .mul (.add x y) b, he | .mul (.sub x y) b, he | .mul (.mul x y) b, he
  | .mul (.neg x) b, he => by
    rw [E.eval_selFree (envP_agree T σ r) _ (by simpa [E.guarded] using he)]

/-- **For guarded AIRs, Plonky3's reading is `Sat`.** -/
theorem satP_iff {A : AirD} (hg : A.cons.all E.guarded = true) (T : Table) (σ : Sels T.h) :
    SatP A T σ ↔ Sat A T := by
  have hg' := List.all_eq_true.1 hg
  constructor
  · rintro ⟨hh, hc⟩
    exact ⟨hh, fun c hc' r hr => (guarded_iff T σ r c (hg' c hc')).1 (hc c hc' r hr)⟩
  · rintro ⟨hh, hc⟩
    exact ⟨hh, fun c hc' r hr => (guarded_iff T σ r c (hg' c hc')).2 (hc c hc' r hr)⟩

/-- **AIRs with the same normal forms satisfy the same constraints under
    any selectors.** -/
theorem satP_transfer {a b : AirD} (h : sameAirB a b = true) (T : Table) (σ : Sels T.h) :
    SatP a T σ ↔ SatP b T σ := by
  unfold sameAirB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hcons := h.1.1.2
  have hc : ∀ ρ, a.cons.map (fun e => e.eval ρ) = b.cons.map (fun e => e.eval ρ) := map_norm_eval hcons
  have hl : a.cons.length = b.cons.length := by simpa using congrArg List.length hcons
  have key : ∀ (xs ys : List E), xs.length = ys.length → (∀ ρ, xs.map (fun e => e.eval ρ) = ys.map (fun e => e.eval ρ)) →
      ∀ ρ, (∀ c ∈ xs, c.eval ρ = 0) → ∀ c ∈ ys, c.eval ρ = 0 := by
    intro xs ys hl hm ρ hx c hcy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcy
    have e := congrArg (fun l => l[i]?) (hm ρ)
    simp only [List.getElem?_map] at e
    rw [List.getElem?_eq_getElem (by omega : i < xs.length), List.getElem?_eq_getElem hi] at e
    simp only [Option.map_some, Option.some.injEq] at e
    rw [← e]; exact hx _ (List.getElem_mem _)
  constructor
  · rintro ⟨hh, hs⟩
    exact ⟨hh, fun c hcb r hr => key a.cons b.cons hl hc _ (fun c' hc' => hs c' hc' r hr) c hcb⟩
  · rintro ⟨hh, hs⟩
    exact ⟨hh, fun c hca r hr => key b.cons a.cons hl.symm (fun ρ => (hc ρ).symm) _
      (fun c' hc' => hs c' hc' r hr) c hca⟩

/-- **The corpus circuit is guarded**, for every term. -/
theorem base_guarded (t : Term) : ∀ A ∈ baseAirs t, A.cons.all E.guarded = true := by
  intro A hA
  simp only [baseAirs, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl <;> rfl

/-- **What an accepted proof gives, with Plonky3's selectors**: as
    `Accepted`, the constraints read with some selectors of Plonky3's zero
    pattern. -/
def AcceptedP (As : List AirD) (ts : List Table) : Prop :=
  As.length = ts.length ∧
    (∀ p ∈ As.zip ts, (∃ σ : Sels p.2.h, SatP p.1 p.2 σ) ∧ (p.1.pre = 0 ∨ PreIs p.1 p.2)) ∧
    Balanced (As.zip ts) ∧ HeightsOK (As.zip ts) ∧ TwoAdic (As.zip ts)

/-- Selectors of Plonky3's pattern exist on every nonempty table. -/
def sels01 (h : Nat) : Sels h :=
  ⟨fun r => if r = 0 then 1 else 0, fun r => if r + 1 = h then 1 else 0, fun r => if r + 1 = h then 0 else 1,
   fun r => by by_cases e : r = 0 <;> simp [e] <;> decide,
   fun r => by by_cases e : r + 1 = h <;> simp [e] <;> decide,
   fun r => by by_cases e : r + 1 = h <;> simp [e] <;> decide⟩

theorem zip_same : ∀ {Rs Ls : List AirD} {ts : List Table}, sameAirsB Rs Ls = true →
    ∀ p ∈ Rs.zip ts, ∃ l ∈ Ls, sameAirB p.1 l = true
  | [], [], _, _, _, h => nomatch h
  | r :: Rs, l :: Ls, [], _, _, h => nomatch h
  | r :: Rs, l :: Ls, T :: ts, hs, p, hp => by
    simp only [sameAirsB, Bool.and_eq_true] at hs
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨l, List.mem_cons_self, hs.1⟩
    · obtain ⟨l', hl', e⟩ := zip_same hs.2 p hp
      exact ⟨l', List.mem_cons_of_mem _ hl', e⟩

/-- **With Plonky3's selectors or with `0`/`1` ones, AIRs with the corpus
    circuit's normal forms accept the same tables.** -/
theorem acceptedP_iff {t : Term} {Rs : List AirD} (hs : sameAirsB Rs (baseAirs t) = true) (ts : List Table) :
    AcceptedP Rs ts ↔ Accepted Rs ts := by
  have pair : ∀ p ∈ Rs.zip ts, ∀ σ : Sels p.2.h, SatP p.1 p.2 σ ↔ Sat p.1 p.2 := by
    intro p hp σ
    obtain ⟨l, hl, e⟩ := zip_same hs p hp
    rw [satP_transfer e, satP_iff (base_guarded t l hl), ← (sameAirB_sound e).1]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, fun p hp => ?_, h3, h4, h5⟩
    obtain ⟨⟨σ, hσ⟩, hpre⟩ := h2 p hp
    exact ⟨(pair p hp σ).1 hσ, hpre⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, fun p hp => ?_, h3, h4, h5⟩
    exact ⟨⟨sels01 _, (pair p hp _).2 (h2 p hp).1⟩, (h2 p hp).2⟩

/-- **Soundness with Plonky3's selectors.** -/
theorem export_sound_P {t : Term} {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (baseAirs t) = true) (h : AcceptedP Rs ts) :
    ∃ C Mm Pg, ts = [C, Mm, Pg] ∧ Accepts (memOf Mm) t C.h (rowOf C) ∧
      ∃ v, decode (st (memOf Mm) (rowOf C (C.h - 1))) = some v ∧ Eval t v :=
  export_sound hs ((acceptedP_iff hs ts).1 h)

/-- **Completeness with Plonky3's selectors**: the honest tables' constraints
    vanish with every selectors of Plonky3's pattern, Plonky3's own among
    them. -/
theorem export_complete_P {t v : Term} {Rs : List AirD} (hs : sameAirsB Rs (baseAirs t) = true) (he : Eval t v) :
    ∃ (n : Nat) (M : List Cell), ∀ k L, n < k → VHeight k → M.length ≤ L → VHeight L →
      ∃ C Mm Pg, AcceptedP Rs [C, Mm, Pg] ∧
        (∀ p ∈ Rs.zip [C, Mm, Pg], ∀ σ : Sels p.2.h, SatP p.1 p.2 σ) ∧ C.h = k ∧ Mm.h = L ∧
        memOf Mm = M ++ List.replicate (L - M.length) .nil ∧
        decode (st (memOf Mm) (rowOf C (k - 1))) = some v := by
  obtain ⟨n, M, h⟩ := export_complete hs he
  refine ⟨n, M, fun k L hk hkV hML hLV => ?_⟩
  obtain ⟨C, Mm, Pg, hacc, rest⟩ := h k L hk hkV hML hLV
  refine ⟨C, Mm, Pg, (acceptedP_iff hs _).2 hacc, fun p hp σ => ?_, rest⟩
  obtain ⟨l, hl, e⟩ := zip_same hs p hp
  rw [satP_transfer e, satP_iff (base_guarded t l hl), ← (sameAirB_sound e).1]
  exact (hacc.2.1 p hp).1

end Circuit
