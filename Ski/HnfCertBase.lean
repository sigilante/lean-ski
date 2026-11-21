import Ski.HnfCertRun
import Ski.HnfCertLaws
open Term

/-!
# The certificate checker's tables, read on terms

`pst t = cls t * 64 + fold t` is the product state code of a closed pure-S term.  It is a
homomorphism onto `dxN`; it lies in `REACH`; the exact-size, minimum-size and hnf-shape tables
are correct for it.  Every finite fact is a `decide +kernel` check.
-/

namespace HnfCert
open HnfS HnfSound HnfProd HnfCertLaws

def pst (t : Term) : Nat := cls t * 64 + fold t

theorem γN_eq : ∀ a, a < 39 → ∀ b, b < 39 → γN a b = HnfProd.γ a b := by decide +kernel
theorem βN_eq : ∀ a, a < 38 → ∀ b, b < 38 → βN a b = HnfS.β a b := by decide +kernel

theorem pst_div {t : Term} (ht : PureS t) : pst t / 64 = cls t := by
  have := fold_lt ht; unfold pst; omega
theorem pst_mod {t : Term} (ht : PureS t) : pst t % 64 = fold t := by
  have := fold_lt ht; unfold pst; omega

theorem pst_S : pst S = 0 := rfl

theorem pst_app {f x : Term} (hf : PureS f) (hx : PureS x) : pst (f ⬝ x) = dxN (pst f) (pst x) := by
  unfold dxN
  rw [pst_div hf, pst_div hx, pst_mod hf, pst_mod hx, γN_eq _ (cls_lt hf) _ (cls_lt hx),
    βN_eq _ (fold_lt hf) _ (fold_lt hx)]
  simp [pst, cls, fold]

theorem accN_pst {t : Term} (ht : PureS t) : accN (pst t) = true ↔ cls t ≠ 37 := by
  simp [accN, pst_div ht]

/-- A code of block 0 is the code of `S` only. -/
theorem eq_S_of_pst {t : Term} (ht : PureS t) (h : pst t = 0) : t = S := by
  apply fold_eq_zero ht
  have := pst_mod ht; rw [h] at this; omega

theorem pst_wsteps {t u : Term} (h : WSteps t u) (ht : PureS t) : pst u = pst t := by
  have ⟨hu, hf⟩ := HnfS.fold_wsteps h ht
  unfold pst; rw [hf, wsteps_cls h ht]

/-! ## Reachable and accepted codes -/

theorem reach_eq : REACH = reachPairs.map (fun p => p.1 * 64 + p.2) := by decide +kernel

theorem pst_reach {t : Term} (ht : PureS t) : pst t ∈ REACH := by
  rw [reach_eq]
  exact List.mem_map.mpr ⟨_, pair_mem ht, rfl⟩

theorem accs_eq : ACCS = REACH.filter accN := by decide +kernel

theorem pst_accs {t : Term} (ht : PureS t) (hc : cls t ≠ 37) : pst t ∈ ACCS := by
  rw [accs_eq, List.mem_filter]
  exact ⟨pst_reach ht, (accN_pst ht).mpr hc⟩

/-! ## Exact sizes -/

def exactOK (x y : Nat) : Bool :=
  match exactB (HnfS.β x y) with
  | none => true
  | some v => match exactB x, exactB y with
    | some a, some b => a + b == v
    | _, _ => false

theorem exactOK_all : ∀ x, x < 38 → ∀ y, y < 38 → exactOK x y = true := by decide +kernel
theorem exact_S : exactB 0 = some 1 := by decide +kernel

/-- A block in the exact table holds terms of that size only. -/
theorem exact_size {t : Term} (ht : PureS t) : ∀ {v}, exactB (fold t) = some v → tsz t = v := by
  induction ht with
  | S => intro v h; rw [show fold S = 0 from rfl, exact_S] at h; cases h; rfl
  | @app f x hf hx ihf ihx =>
    intro v h
    have hok := exactOK_all _ (fold_lt hf) _ (fold_lt hx)
    simp only [fold] at h
    simp only [exactOK, h] at hok
    revert hok
    cases ef : exactB (fold f) <;> cases ex : exactB (fold x) <;> simp
    intro hv
    simp only [tsz, ihf ef, ihx ex]; omega

/-! ## Minimum sizes -/

def minRow (a : Nat) : Bool := REACH.all (fun b => decide (minsz (dxN a b) ≤ minsz a + minsz b))
/-- The minimum-size table is sub-additive on reachable codes (checked in `HnfCertK*` chunks). -/
def MinOK : Prop := REACH.all minRow = true

theorem minsz_S : minsz 0 = 1 := by decide +kernel

theorem minsz_le (hMin : MinOK) {t : Term} (ht : PureS t) : minsz (pst t) ≤ tsz t := by
  induction ht with
  | S => rw [pst_S, minsz_S]; exact Nat.le_refl _
  | @app f x hf hx ihf ihx =>
    have h := hMin
    simp only [MinOK, minRow, List.all_eq_true] at h
    have := h _ (pst_reach hf) _ (pst_reach hx)
    simp only [decide_eq_true_eq] at this
    rw [pst_app hf hx]; simp only [tsz]; omega

/-! ## Split preimages -/

def splitRow (p : Nat) : Bool :=
  ACCS.all fun q => !accN (dxN p q) || (splits (dxN p q)).contains (p, q)
/-- The split table lists every accepted preimage pair of an accepted code (checked in chunks). -/
def SplitsOK : Prop := ACCS.all splitRow = true

theorem splits_complete (hSp : SplitsOK) {p q : Nat} (hp : p ∈ ACCS) (hq : q ∈ ACCS)
    (h : accN (dxN p q) = true) : (p, q) ∈ splits (dxN p q) := by
  have hh := hSp; simp only [SplitsOK, splitRow, List.all_eq_true] at hh
  have := hh p hp q hq
  simp only [h, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
  exact this

/-! ## hnf shapes -/

deriving instance DecidableEq for Shape

def shapeRow (a : Nat) : Bool := ACCS.all (fun b => (unf (dxN (dxN 0 a) b)).contains (.s2 a b))
/-- The hnf-shape table is complete on accepted codes (the `s2` part is checked in chunks). -/
def ShapesOK : Prop := ACCS.all shapeRow = true

theorem shapes01 : (unf 0).contains .s0 && ACCS.all (fun a => (unf (dxN 0 a)).contains (.s1 a)) = true := by
  decide +kernel

theorem unf_s0 : Shape.s0 ∈ unf 0 := by
  have h := shapes01; simp only [Bool.and_eq_true, List.contains_iff_mem] at h
  exact h.1
theorem unf_s1 {a : Nat} (ha : a ∈ ACCS) : Shape.s1 a ∈ unf (dxN 0 a) := by
  have h := shapes01; simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact (of_decide_eq_true h.2) a ha
theorem unf_s2 (hSh : ShapesOK) {a b : Nat} (ha : a ∈ ACCS) (hb : b ∈ ACCS) :
    Shape.s2 a b ∈ unf (dxN (dxN 0 a) b) := by
  have h := hSh; simp only [ShapesOK, shapeRow, List.all_eq_true, List.contains_iff_mem] at h
  exact h a ha b hb

end HnfCert
