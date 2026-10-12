import Ski.ZK.QuotP3
import Ski.Circuit.Selectors

/-!
# The corpus circuit's AIR facts

`pcsCloseN_fri_bb` asks of an AIR's constraints that they be guarded,
with main leaves at offsets 0 and 1 below the AIR's width, of Plonky3
degree at most `D`, and with at most `s` transition factors.  For the
corpus circuit (`baseAirs`) the kernel checks these for every term:
`D = 2` and `s = 1`.  Plonky3's chunk count is then `lq = 1`, four
chunks (`get_log_num_quotient_chunks` with `is_zk`: `log2_ceil 2`).
Plonky3's degree also counts the LogUp constraints.  p3-lookup's formula
for one interaction, `max(1 + deg(elements), deg(multiplicity))`, is read
from its source; the kernel checks that its value is at most 2 on every
interaction (`base_lup`).
-/

namespace Circuit

open B

/-- What `pcsCloseN_fri_bb` asks of an AIR's constraints, as one check. -/
def E.p3ok (w D s : Nat) (e : E) : Bool := e.guarded && e.win w && decide (e.pdeg ≤ D) && decide (e.sdeg ≤ s)

theorem p3ok_spec {w D s : Nat} {e : E} (h : e.p3ok w D s = true) :
    e.guarded = true ∧ e.win w = true ∧ e.pdeg ≤ D ∧ e.sdeg ≤ s := by
  simp only [E.p3ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

set_option maxRecDepth 100000 in
/-- **The corpus circuit's constraints**, for every term: guarded, in the
    window of their AIR's width, Plonky3 degree at most `2`, at most one
    transition factor. -/
theorem base_p3ok (t : Term) : ∀ A ∈ baseAirs t, A.cons.all (E.p3ok A.width 2 1) = true := by
  intro A hA
  simp only [baseAirs, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl <;> rfl

theorem base_facts (t : Term) {A : AirD} (hA : A ∈ baseAirs t) :
    (∀ c ∈ A.cons, c.guarded = true) ∧ (∀ c ∈ A.cons, c.win A.width = true) ∧
    (∀ e ∈ A.cons, e.pdeg ≤ 2) ∧ (∀ e ∈ A.cons, e.sdeg ≤ 1) := by
  have h := List.all_eq_true.1 (base_p3ok t A hA)
  exact ⟨fun c hc => (p3ok_spec (h c hc)).1, fun c hc => (p3ok_spec (h c hc)).2.1,
    fun c hc => (p3ok_spec (h c hc)).2.2.1, fun c hc => (p3ok_spec (h c hc)).2.2.2⟩

/-- **The composed hiding PCS for a corpus AIR over BabyBear**:
    `pcsCloseN_fri_bb` with the AIR facts checked by the kernel
    (`base_facts`): Plonky3 degree `2`, so `lq = 1` and four chunks on the
    quotient domain of `2^(tb+3)` points, `31 · ⟨bbGen (tb+3)⟩`, for
    `tb ≤ 24`.  Left: the group's trace and mask points and next row
    (`hT`, `hRq`, `hZq`, `hnxt`, Plonky3's interleaving), a table meeting
    `Sat` with the AIR's width at each trace, the preprocessed columns'
    size, the query points (off the trace, `|S| + 4 ≤ m + 1`) and the
    out-of-domain point (`ζ` generating the extension). -/
theorem pcsCloseN_fri_base {V : Type} {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hokq : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (hdet : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    (term : Term) {A : AirD} (hA : A ∈ baseAirs term)
    {preP : Nat → List F} {gi : Nat} {S : List F} {ζ : EF} {ws : List (EF → EF → List F)} {nR : Nat}
    {tb m : Nat} (ht : tb ≤ 24) (hm : m + 1 = 2 ^ (tb + 1))
    (hgi : gi < qs.length) (hcl' : ∀ t α β, gi < (cols t α β).length)
    (hT : (qs[gi]'hgi).base.T = cosetL 1 (bbGen (tb + 1)) (m + 1))
    (hRq : (qs[gi]'hgi).base.R = cosetL (bbGen (tb + 2)) (bbGen (tb + 1)) (m + 1)) (hSq : (qs[gi]'hgi).base.S = S)
    (hZq : (qs[gi]'hgi).base.Z = [ζ, (EF.ofF (bbGen (tb + 1))).mul ζ]) (hnq : (qs[gi]'hgi).base.n = nR)
    (hnxt : (qs[gi]'hgi).nxt = (bbGen (tb + 1) * ·))
    (hsatT : ∀ t' α β, ∃ Tb : Table, Sat A Tb ∧ Tb.h = m + 1 ∧
      ((cols t' α β)[gi]'(hcl' t' α β)).length = A.width ∧
      (∀ i (hi : i < ((cols t' α β)[gi]'(hcl' t' α β)).length),
        (((cols t' α β)[gi]'(hcl' t' α β))[i]).length = m + 1 ∧
        ∀ r (hr : r < (((cols t' α β)[gi]'(hcl' t' α β))[i]).length),
          (((cols t' α β)[gi]'(hcl' t' α β))[i])[r] = Tb.main r i) ∧
      (∀ r i, r < m + 1 → fval (fpow (bbGen (tb + 1)) r) (preP i) = Tb.pre r i))
    (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 (bbGen (tb + 1)) (m + 1))) ≠ 0)
    (hdetζ : (mz ζ).det ≠ 0) (hS4 : S.length + 4 ≤ m + 1) :
    PCSCloseN off (P ^ (friN1 qs ks [airQTab A (bbGen (tb + 1)) m preP gi (p3κ 31 (bbGen (tb + 3)) 3 (m + 1))
        (p3cs 31 (bbGen (tb + 3)) 3 (m + 1)) (p3dom 31 (bbGen (tb + 3)) 3 (m + 1) 3) (p3c 31 (bbGen (tb + 3)) (m + 1) 3)
        S ζ ws] +
      friN2 qs [airQTab A (bbGen (tb + 1)) m preP gi (p3κ 31 (bbGen (tb + 3)) 3 (m + 1))
        (p3cs 31 (bbGen (tb + 3)) 3 (m + 1)) (p3dom 31 (bbGen (tb + 3)) 3 (m + 1) 3) (p3c 31 (bbGen (tb + 3)) (m + 1) 3)
        S ζ ws] ncw)) tv
      (pcsFri off tv qs ks cols [airQTab A (bbGen (tb + 1)) m preP gi (p3κ 31 (bbGen (tb + 3)) 3 (m + 1))
        (p3cs 31 (bbGen (tb + 3)) 3 (m + 1)) (p3dom 31 (bbGen (tb + 3)) 3 (m + 1) 3) (p3c 31 (bbGen (tb + 3)) (m + 1) 3)
        S ζ ws]
        (fun t α β ms => [airData A (bbGen (tb + 1)) m preP (p3cs 31 (bbGen (tb + 3)) 3 (m + 1))
          (p3dom 31 (bbGen (tb + 3)) 3 (m + 1) 3) ws α β ((mpolysMulti (qs.map QGroup.ext) (cols t α β) ms).getD gi [])])
        ncw αb fri)
      (psimFri qs ks [airQTab A (bbGen (tb + 1)) m preP gi (p3κ 31 (bbGen (tb + 3)) 3 (m + 1))
        (p3cs 31 (bbGen (tb + 3)) 3 (m + 1)) (p3dom 31 (bbGen (tb + 3)) 3 (m + 1) 3) (p3c 31 (bbGen (tb + 3)) (m + 1) 3)
        S ζ ws] ncw αb fri) 0 := by
  obtain ⟨hgd, hwin, hD, hsd⟩ := base_facts term hA
  have hm26 : m + 1 ≤ 2 ^ 25 := by rw [hm]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hm1 : 1 ≤ m := by
    have : 2 ≤ 2 ^ (tb + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (tb + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hN : (3 + 1) * (m + 1) = 2 ^ (tb + 2 + 1) := by
    have e : 2 ^ (tb + 2 + 1) = 2 ^ (tb + 1) * 2 ^ 2 := by
      rw [← Nat.pow_add]
    rw [e, ← hm, Nat.mul_comm]
  refine pcsCloseN_fri_bb hokq hks hcols hdet haw hncw off tv (tb := tb) (l := 3) (k := tb + 2) (lq := 1) (D := 2)
    (s := 1) (m := m) (by omega) hm (by omega) hN rfl hgi hcl' hT hRq hSq hZq hnq hnxt
    (fun t' α β => by
      obtain ⟨Tb, h1, h2, h3, h4, h5⟩ := hsatT t' α β
      exact ⟨Tb, h1, h2, fun c hc => by rw [h3]; exact hwin c hc, h4, h5⟩)
    hgd hpreL hζ hS hD (by decide) hsd (by omega) (by show 2 * (2 * (m + 1) - 1) + 1 + 1 ≤ 2013265921; omega) hdetζ hS4

/-- **A LogUp interaction's constraint degree**, as p3-lookup's
    `constraint_degree_with_transition` computes it for one interaction:
    `max(1 + deg(elements), deg(multiplicity))`, the degrees Plonky3's
    (`E.pdeg`). -/
def Inter.lupDeg (I : Inter) : Nat := max (1 + (I.fields.map E.pdeg).foldl max 0) I.count.pdeg

set_option maxRecDepth 100000 in
/-- **The corpus circuit's LogUp interactions have degree at most 2**, for
    every term.  Plonky3's degree is the maximum of the constraints'
    (`base_p3ok`), the fraction pins' (this theorem), the accumulator's (2,
    fixed by p3-lookup) and the AIR's declared hint (none).  At 2,
    `lq = log2_ceil 2 = 1`, and same-bus packing keeps the degree within
    that budget.  p3-lookup's formula, the accumulator's degree and the
    absent hint are read from the source; assumed: each `Inter` is one
    unflagged p3 `Lookup`. -/
theorem base_lup (t : Term) : ∀ A ∈ baseAirs t, A.inters.all (fun I => decide (I.lupDeg ≤ 2)) = true := by
  intro A hA
  simp only [baseAirs, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl <;> rfl

end Circuit
