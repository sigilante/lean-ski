import Ski.ZK.QuotPoly
import Ski.ZK.Chain

/-!
# The base coordinates folded back

`air_quot` works one base coordinate `k` at a time: the weights are
coordinate `k` of the folding challenge's powers `αʲ`.  Plonky3's
verifier recombines the four coordinates in the extension's basis
`1, X, X², X³` and compares the result with the folded constraints over
`Z_H`.  `fold_back` shows the coordinates recombine to the full fold:
`Σ_k e_k Σ_j (αʲ)_k c_j = Σ_j αʲ c_j`, for base values `c_j` read in the
extension.  So the four per-coordinate targets at `ζ`, recombined, are
the verifier's `Σ_j αʲ c_j(ζ) / Z_H(ζ)` (`airTgE_back`).
-/

namespace Circuit

open ZKF

/-- The basis `1, X, X², X³` of the extension. -/
def bE1 : EF := ⟨0, 1, 0, 0⟩
def bE2 : EF := ⟨0, 0, 1, 0⟩
def bE3 : EF := ⟨0, 0, 0, 1⟩

/-- `A₀ + X A₁ + X² A₂ + X³ A₃`. -/
def recomb (A0 A1 A2 A3 : EF) : EF := A0.add ((bE1.mul A1).add ((bE2.mul A2).add (bE3.mul A3)))

/-- `Σ_j w_j v_j` with weights in the extension. -/
def foldEE : List EF → List EF → EF
  | w :: ws, v :: vs => (w.mul v).add (foldEE ws vs)
  | _, _ => EF.zero

theorem recomb_zero : recomb EF.zero EF.zero EF.zero EF.zero = EF.zero := by decide

/-- One step: a weight's four coordinates, each times `v`, recombine to `w v`. -/
theorem recomb_step (w v A0 A1 A2 A3 : EF) :
    recomb (((EF.ofF w.x0).mul v).add A0) (((EF.ofF w.x1).mul v).add A1) (((EF.ofF w.x2).mul v).add A2)
      (((EF.ofF w.x3).mul v).add A3) = (w.mul v).add (recomb A0 A1 A2 A3) := by
  let c0 : Q := ⟨(Q.var 0).q0, k 0, k 0, k 0⟩
  let c1 : Q := ⟨(Q.var 0).q1, k 0, k 0, k 0⟩
  let c2 : Q := ⟨(Q.var 0).q2, k 0, k 0, k 0⟩
  let c3 : Q := ⟨(Q.var 0).q3, k 0, k 0, k 0⟩
  let b1 : Q := ⟨k 0, k 1, k 0, k 0⟩
  let b2 : Q := ⟨k 0, k 0, k 1, k 0⟩
  let b3 : Q := ⟨k 0, k 0, k 0, k 1⟩
  exact Q.eq_of_norm
    (p := ((c0.mul (Q.var 1)).add (Q.var 2)).add ((b1.mul ((c1.mul (Q.var 1)).add (Q.var 3))).add
      ((b2.mul ((c2.mul (Q.var 1)).add (Q.var 4))).add (b3.mul ((c3.mul (Q.var 1)).add (Q.var 5))))))
    (q := ((Q.var 0).mul (Q.var 1)).add ((Q.var 2).add ((b1.mul (Q.var 3)).add ((b2.mul (Q.var 4)).add (b3.mul (Q.var 5))))))
    (by decide) (env8 w v A0 A1 A2 A3 EF.zero EF.zero)

/-- **The coordinates fold back**: `Σ_k e_k Σ_j (w_j)_k v_j = Σ_j w_j v_j`. -/
theorem fold_back : ∀ (ws vs : List EF),
    recomb (foldVE (ws.map (·.x0)) vs) (foldVE (ws.map (·.x1)) vs) (foldVE (ws.map (·.x2)) vs)
      (foldVE (ws.map (·.x3)) vs) = foldEE ws vs
  | [], _ => recomb_zero
  | _ :: _, [] => recomb_zero
  | w :: ws, v :: vs => by
    show recomb (((EF.ofF w.x0).mul v).add _) (((EF.ofF w.x1).mul v).add _) (((EF.ofF w.x2).mul v).add _)
      (((EF.ofF w.x3).mul v).add _) = (w.mul v).add (foldEE ws vs)
    rw [recomb_step, fold_back ws vs]

theorem recomb_mul (A0 A1 A2 A3 I : EF) :
    recomb (A0.mul I) (A1.mul I) (A2.mul I) (A3.mul I) = (recomb A0 A1 A2 A3).mul I := by
  let b1 : Q := ⟨k 0, k 1, k 0, k 0⟩
  let b2 : Q := ⟨k 0, k 0, k 1, k 0⟩
  let b3 : Q := ⟨k 0, k 0, k 0, k 1⟩
  exact Q.eq_of_norm
    (p := ((Q.var 0).mul (Q.var 4)).add ((b1.mul ((Q.var 1).mul (Q.var 4))).add
      ((b2.mul ((Q.var 2).mul (Q.var 4))).add (b3.mul ((Q.var 3).mul (Q.var 4))))))
    (q := ((Q.var 0).add ((b1.mul (Q.var 1)).add ((b2.mul (Q.var 2)).add (b3.mul (Q.var 3))))).mul (Q.var 4))
    (by decide) (env8 A0 A1 A2 A3 I EF.zero EF.zero EF.zero)

/-- **The four coordinates' targets at `ζ` recombine to the verifier's
    check**: with the weights of coordinate `k` the `k`-th coordinates of
    `αs`, the recombined targets are `Σ_j αʲ c_j(ζ)` over `Z_H(ζ) κ ∏_j v_j(ζ)`. -/
theorem airTgE_back (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F)
    (H : List F) (αs : List EF) (es : List E) (ρE : Atom → EF) :
    recomb (airTgE ζ cs Hl cl qs ql κ H (αs.map (·.x0)) es ρE) (airTgE ζ cs Hl cl qs ql κ H (αs.map (·.x1)) es ρE)
      (airTgE ζ cs Hl cl qs ql κ H (αs.map (·.x2)) es ρE) (airTgE ζ cs Hl cl qs ql κ H (αs.map (·.x3)) es ρE) =
    (foldEE αs (es.map (·.evalE ρE))).mul
      ((fvalE ζ (fvan H)).mul ((EF.ofF κ).mul (fvalE ζ (rpoly.ppoly (allL cs Hl cl qs ql))))).inv := by
  unfold airTgE
  rw [recomb_mul, fold_back]

end Circuit
