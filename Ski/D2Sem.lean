import Ski.D2Base
import Ski.InfNF
open Term

/-!
# Depth-2 prefixes of `t^∞` are computed by the 373-element S-model `D`

`Pre d t P`: `P` is the depth-`d` prefix of `t^∞` in the sense of `notes/checks/s4/s4lib.py`
(`pi`): an item at depth `e ≤ d` is shown to depth `d - e`, and the head `S` of a head normal
form is always shown.  It refines S3's `InfNF.NF` (`pre_nf`), which cuts the head as well.

Everything here is relative to `Checks`, the kernel-checked table conditions; `Ski/D2.lean`
discharges them.

* `slaw`, `wsteps_foldD`: `D` is an S-model, so `foldD` is invariant under reduction;
* `fold_eq`: S1's block is `φD (foldD t)`;
* `pre1`, `pre2`: the depth-1 and depth-2 prefixes are functions of `foldD t`;
* `pre_exists`, `pre_bwd`, `pre_nf`: prefixes exist at every depth, are stable under head
  expansion, and truncate to `NF`.
-/

namespace D2
open HnfS HnfSound InfNF TopTerm

/-- The kernel-checked table conditions (`D2Base`). -/
structure Checks : Prop where
  slaw : ∀ k, k < 2984 → slawChunk k = true
  cols : ∀ c, c < 373 → colsRow c = true
  closed : ∀ a, a < 373 → closedRow a = true
  hom : ∀ a, a < 373 → homRow a = true
  out2 : ∀ e, e < 373 → out2Row e = true

/-! ## Table facts -/

theorem τ_lt (C : Checks) {a b : Nat} (ha : a < 373) (hb : b < 373) : τ a b < 373 := by
  have h := C.closed a ha
  simp only [closedRow, force_eq, allB_spec] at h
  exact Nat.le_of_ble_eq_true (h b hb)

theorem col_eq (C : Checks) {c y : Nat} (hc : c < 373) (hy : y < 373) : get (colN c) y = τ y c := by
  have h := C.cols c hc
  simp only [colsRow, force_eq] at h
  have h2 := colsIn_spec h y (by rw [rows_len]; exact hy)
  rw [Nat.zero_add] at h2
  exact h2

/-- `D` is an S-model: all 373³ = 51,895,117 triples. -/
theorem slaw (C : Checks) {a b c : Nat} (ha : a < 373) (hb : b < 373) (hc : c < 373) :
    τ (τ (τ 0 a) b) c = τ (τ a c) (τ b c) := by
  have h := C.slaw (a * 8 + c / 47) (by omega)
  have e1 : (a * 8 + c / 47) / 8 = a := by omega
  have e2 : (a * 8 + c / 47) % 8 = c / 47 := by omega
  simp only [slawChunk, e1, e2, slawPart, force_eq, allB_spec] at h
  have h2 := h (c % 47) (Nat.mod_lt _ (by decide))
  rw [Nat.div_add_mod c 47] at h2
  have e4 : Nat.ble 373 c = false := by
    cases hh : Nat.ble 373 c with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true hh) (by omega)
  simp only [e4, Bool.false_or, slawIn, allB_spec] at h2
  have h3 : get (colN c) (τ (τ 0 a) b) = τ (τ a c) (get (colN c) b) := Nat.eq_of_beq_eq_true (h2 b hb)
  rw [col_eq C hc (τ_lt C (τ_lt C (by decide) ha) hb), col_eq C hc hb] at h3
  exact h3

theorem hom (C : Checks) {a b : Nat} (ha : a < 373) (hb : b < 373) :
    φD (τ a b) = β (φD a) (φD b) := by
  have h := C.hom a ha
  simp only [homRow, force_eq, allB_spec] at h
  exact Nat.eq_of_beq_eq_true (h b hb)

theorem outC_lt (d : Nat) : outC d < 16 := Nat.lt_succ_of_le Nat.and_le_right

theorem outS : outC 0 = 0 := by
  have h := out1B_eq
  simp only [out1B, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem out_one {e : Nat} (he : e < 373) : outC (τ 0 e) = 4 + outC e / 4 := by
  have h := out1B_eq
  simp only [out1B, Bool.and_eq_true, allB_spec] at h
  exact Nat.eq_of_beq_eq_true (h.2 e he)

theorem out_two (C : Checks) {e f : Nat} (he : e < 373) (hf : f < 373) :
    outC (τ (τ 0 e) f) = 8 + outC f / 4 := by
  have h := C.out2 e he
  simp only [out2Row, force_eq, allB_spec] at h
  exact Nat.eq_of_beq_eq_true (h f hf)

theorem out_bot {d : Nat} (hd : d < 373) (hφ : φD d = 36) :
    outC d / 4 = 3 ∧ ∀ e, e < 373 → outC (τ d e) = 12 + outC e / 4 := by
  have h := botB_eq
  simp only [botB, allB_spec] at h
  have h1 := h d hd
  rw [hφ] at h1
  have e0 : (Nat.beq 36 36 == false) = false := by decide
  simp only [e0, Bool.false_or, Bool.and_eq_true, force_eq, allB_spec] at h1
  exact ⟨Nat.eq_of_beq_eq_true h1.1, fun e he => Nat.eq_of_beq_eq_true (h1.2 e he)⟩

/-! ## The fold -/

/-- The value of a term in `D` (`K` and `I` are sent to `0`; only pure S-terms matter). -/
def foldD : Term → Nat
  | .S => 0
  | .app f x => τ (foldD f) (foldD x)
  | _ => 0

theorem foldD_lt (C : Checks) {t : Term} (ht : PureS t) : foldD t < 373 := by
  induction ht with
  | S => decide
  | app _ _ ihf ihx => exact τ_lt C ihf ihx

theorem wstep_foldD (C : Checks) {t t' : Term} (h : WStep t t') (ht : PureS t) :
    foldD t' = foldD t := by
  induction h with
  | S f g x =>
    obtain ⟨h1, hx⟩ := ht.app_inv
    obtain ⟨h2, hg⟩ := h1.app_inv
    obtain ⟨_, hf⟩ := h2.app_inv
    simp only [foldD]
    exact (slaw C (foldD_lt C hf) (foldD_lt C hg) (foldD_lt C hx)).symm
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | left x _ ih => simp only [foldD, ih ht.app_inv.1]
  | right f _ ih => simp only [foldD, ih ht.app_inv.2]

/-- `foldD` is invariant under reduction. -/
theorem wsteps_foldD (C : Checks) {t u : Term} (h : WSteps t u) (ht : PureS t) :
    foldD u = foldD t := by
  induction h with
  | refl => rfl
  | step h1 _ ih =>
    have hp := (HnfS.wstep_pure h1 ht).1
    exact (ih hp).trans (wstep_foldD C h1 ht)

theorem steps_foldD (C : Checks) {t u : Term} (ht : PureS t) (h : Steps t u) : foldD u = foldD t :=
  wsteps_foldD C (Steps.weak h) ht

/-- S1's 38-block model is a quotient of `D`. -/
theorem fold_eq (C : Checks) {t : Term} (ht : PureS t) : fold t = φD (foldD t) := by
  induction ht with
  | S => exact phi0.symm
  | @app f x hf hx ihf ihx =>
    simp only [fold, foldD]
    rw [hom C (foldD_lt C hf) (foldD_lt C hx), ihf, ihx]

/-! ## Prefixes -/

/-- The depth-`d` prefix of `t^∞` by the rules of S3's Prop. "compute", with the head of a head
normal form always shown.  `Steps` is head reduction, so `a`, `b`, `w` are literal spine items.
In `bot` any stage with an hnf-less function part may be used. -/
inductive Pre : Nat → Term → PT → Prop
  | zero (t : Term) : Pre 0 t .hole
  | leaf (d : Nat) : Pre (d + 1) S .S
  | one {d : Nat} {t a : Term} {Pa : PT} : Steps t (S ⬝ a) → Pre d a Pa →
      Pre (d + 1) t (.app .S Pa)
  | two {d : Nat} {t a b : Term} {Pa Pb : PT} : Steps t (S ⬝ a ⬝ b) → Pre (d - 1) a Pa →
      Pre d b Pb → Pre (d + 1) t (.app (.app .S Pa) Pb)
  | bot {d : Nat} {t f w : Term} {Pf Pw : PT} : Steps t (f ⬝ w) → fold f = 36 →
      Pre d f Pf → Pre d w Pw → Pre (d + 1) t (.app Pf Pw)

/-- Depth-1 prefixes, by code: `S`, `S ·`, `S · ·`, no head normal form. -/
def pt1 : Nat → PT
  | 0 => .S
  | 1 => .app .S .hole
  | 2 => .app (.app .S .hole) .hole
  | _ => .app .hole .hole

/-- Depth-2 prefixes, by output code. -/
def pt2 (c : Nat) : PT :=
  match c / 4 with
  | 0 => .S
  | 1 => .app .S (pt1 (c % 4))
  | 2 => .app (.app .S .hole) (pt1 (c % 4))
  | _ => .app (.app .hole .hole) (pt1 (c % 4))

/-- The depth-1 and depth-2 outputs of an element of `D`. -/
def out1 (d : Nat) : PT := pt1 (outC d / 4)
def out2 (d : Nat) : PT := pt2 (outC d)

theorem k4 {k : Nat} (h : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

theorem pt2_one {k : Nat} (h : k < 4) : pt2 (4 + k) = .app .S (pt1 k) := by
  rcases k4 h with rfl | rfl | rfl | rfl <;> rfl
theorem pt2_two {k : Nat} (h : k < 4) : pt2 (8 + k) = .app (.app .S .hole) (pt1 k) := by
  rcases k4 h with rfl | rfl | rfl | rfl <;> rfl
theorem pt2_bot {k : Nat} (h : k < 4) : pt2 (12 + k) = .app (.app .hole .hole) (pt1 k) := by
  rcases k4 h with rfl | rfl | rfl | rfl <;> rfl

theorem q4 (d : Nat) : outC d / 4 < 4 := by have := outC_lt d; omega

/-- **Depth 1.**  The depth-1 prefix is `out1 (foldD t)`. -/
theorem pre1 (C : Checks) {t : Term} {P : PT} (ht : PureS t) (h : Pre 1 t P) :
    P = out1 (foldD t) := by
  unfold out1
  cases h with
  | leaf =>
    show PT.S = pt1 (outC 0 / 4)
    rw [outS]; rfl
  | @one _ _ a Pa hs ha =>
    cases ha
    have hp := steps_pure ht hs
    have e : foldD t = τ 0 (foldD a) := (steps_foldD C ht hs).symm
    have q := q4 (foldD a)
    rw [e, out_one (foldD_lt C hp.app_inv.2), show (4 + outC (foldD a) / 4) / 4 = 1 by omega]
    rfl
  | @two _ _ a b Pa Pb hs ha hb =>
    cases ha; cases hb
    have hp := steps_pure ht hs
    have e : foldD t = τ (τ 0 (foldD a)) (foldD b) := (steps_foldD C ht hs).symm
    have q := q4 (foldD b)
    rw [e, out_two C (foldD_lt C hp.app_inv.1.app_inv.2) (foldD_lt C hp.app_inv.2),
      show (8 + outC (foldD b) / 4) / 4 = 2 by omega]
    rfl
  | @bot _ _ f w Pf Pw hs hb hf hw =>
    cases hf; cases hw
    have hp := steps_pure ht hs
    have e : foldD t = τ (foldD f) (foldD w) := (steps_foldD C ht hs).symm
    have hφ : φD (foldD f) = 36 := by rw [← fold_eq C hp.app_inv.1]; exact hb
    have q := q4 (foldD w)
    rw [e, (out_bot (foldD_lt C hp.app_inv.1) hφ).2 _ (foldD_lt C hp.app_inv.2),
      show (12 + outC (foldD w) / 4) / 4 = 3 by omega]
    rfl

/-- **Depth 2.**  The depth-2 prefix of `t^∞` is `out2 (foldD t)`. -/
theorem pre2 (C : Checks) {t : Term} {P : PT} (ht : PureS t) (h : Pre 2 t P) :
    P = out2 (foldD t) := by
  unfold out2
  cases h with
  | leaf =>
    show PT.S = pt2 (outC 0)
    rw [outS]; rfl
  | @one _ _ a Pa hs ha =>
    have hp := steps_pure ht hs
    have e : foldD t = τ 0 (foldD a) := (steps_foldD C ht hs).symm
    rw [e, out_one (foldD_lt C hp.app_inv.2), pt2_one (q4 _), pre1 C hp.app_inv.2 ha]
    rfl
  | @two _ _ a b Pa Pb hs ha hb =>
    cases ha
    have hp := steps_pure ht hs
    have e : foldD t = τ (τ 0 (foldD a)) (foldD b) := (steps_foldD C ht hs).symm
    rw [e, out_two C (foldD_lt C hp.app_inv.1.app_inv.2) (foldD_lt C hp.app_inv.2), pt2_two (q4 _),
      pre1 C hp.app_inv.2 hb]
    rfl
  | @bot _ _ f w Pf Pw hs hb hf hw =>
    have hp := steps_pure ht hs
    have e : foldD t = τ (foldD f) (foldD w) := (steps_foldD C ht hs).symm
    have hφ : φD (foldD f) = 36 := by rw [← fold_eq C hp.app_inv.1]; exact hb
    have ob := out_bot (foldD_lt C hp.app_inv.1) hφ
    rw [e, ob.2 _ (foldD_lt C hp.app_inv.2), pt2_bot (q4 _), pre1 C hp.app_inv.1 hf,
      pre1 C hp.app_inv.2 hw]
    unfold out1
    rw [ob.1]
    rfl

/-! ## Existence, and the link to `NF` -/

theorem pre_bwd {d : Nat} {t u : Term} {P : PT} (ht : PureS t) (hs : Steps t u) (h : Pre d u P) :
    Pre d t P := by
  cases h with
  | zero => exact .zero t
  | leaf d =>
    rcases steps_two ht hs with rfl | ⟨a, b, c, e⟩
    · exact .leaf d
    · cases e
  | one h ha => exact .one (hs.trans h) ha
  | two h ha hb => exact .two (hs.trans h) ha hb
  | bot h hb hf hw => exact .bot (hs.trans h) hb hf hw

/-- Every prefix exists (from `TopTerm.reach_all`). -/
theorem pre_exists : ∀ (d : Nat) {t : Term}, PureS t → ∃ P, Pre d t P := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    cases d with
    | zero => intro t _; exact ⟨_, .zero t⟩
    | succ d =>
      intro t ht
      have hr := reach_all ht
      induction hr with
      | @hnf u hu =>
        rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
        · exact ⟨_, .leaf d⟩
        · obtain ⟨Pa, ha⟩ := ih d (Nat.lt_succ_self d) ht.app_inv.2
          exact ⟨_, .one (.refl _) ha⟩
        · obtain ⟨Pa, ha⟩ := ih (d - 1) (by omega) ht.app_inv.1.app_inv.2
          obtain ⟨Pb, hb⟩ := ih d (Nat.lt_succ_self d) ht.app_inv.2
          exact ⟨_, .two (.refl _) ha hb⟩
      | @bot f w hf hb =>
        obtain ⟨Pf, h1⟩ := ih d (Nat.lt_succ_self d) hf
        obtain ⟨Pw, h2⟩ := ih d (Nat.lt_succ_self d) ht.app_inv.2
        exact ⟨_, .bot (.refl _) hb h1 h2⟩
      | @step t t' s _ ih' =>
        obtain ⟨P, hP⟩ := ih' (HnfS.wstep_pure s.weak ht).1
        exact ⟨P, pre_bwd ht (.single s) hP⟩

theorem trunc_zero (P : PT) : PT.trunc 0 P = .hole := by cases P <;> rfl

theorem nf_S (d : Nat) : NF d S (PT.trunc d .S) := by
  cases d with
  | zero => exact .zero _
  | succ d => exact .leaf d

/-- `Pre` refines S3's `NF`: cutting a `Pre`-prefix at depth `d` gives the `NF`-prefix. -/
theorem pre_nf {d : Nat} {t : Term} {P : PT} (h : Pre d t P) : NF d t (P.trunc d) := by
  induction h with
  | zero t => rw [trunc_zero]; exact .zero t
  | leaf d => exact .leaf d
  | @one d t a Pa hs _ ih =>
    exact .node hs (.inr (.inr (.inl ⟨a, rfl⟩))) (nf_S d) ih
  | @two d t a b Pa Pb hs _ _ iha ihb =>
    refine .node hs (.inr (.inr (.inr ⟨a, b, rfl⟩))) ?_ ihb
    cases d with
    | zero => rw [trunc_zero]; exact .zero _
    | succ d => exact .node (.refl _) (.inr (.inr (.inl ⟨a, rfl⟩))) (nf_S d) iha
  | bot hs hb _ _ ihf ihw => exact .node hs (.inl hb) ihf ihw

/-- The depth-2 prefix exists, is unique, and is `out2 (foldD t)`. -/
theorem pre2_iff (C : Checks) {t : Term} {P : PT} (ht : PureS t) :
    Pre 2 t P ↔ P = out2 (foldD t) := by
  refine ⟨pre2 C ht, ?_⟩
  rintro rfl
  obtain ⟨Q, hQ⟩ := pre_exists 2 ht
  exact pre2 C ht hQ ▸ hQ

/-- S3's depth-2 prefix `NF 2` is `out2 (foldD t)` cut at depth 2. -/
theorem nf2 (C : Checks) {t : Term} {P : PT} (ht : PureS t) (h : NF 2 t P) :
    P = (out2 (foldD t)).trunc 2 :=
  nf_unique ht h (pre_nf ((pre2_iff C ht).mpr rfl))

end D2
