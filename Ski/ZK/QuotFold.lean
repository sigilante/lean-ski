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
`Σ_j αʲ c_j(ζ) / Z_H(ζ)`, the folded constraints the verifier divides
by `Z_H(ζ)`, times the model's chunk normalization `1 / (κ ∏_j v_j(ζ))`
(`airTgE_back`).

Plonky3 folds a constraint over the extension, such as LogUp's, in the
extension (`assert_zero_ext`, `ext_alpha_powers`).  Such a constraint is
a `Q`, four base expressions `q_m`.  Since each `q_m` is a base value,
coordinate `k` of `αʲ Σ_m X^m q_m` is `Σ_m (αʲ X^m)_k q_m`.  So the
model folds the coordinates `eq4` with the weights `wq`, and they fold
back to `αʲ` times the constraint's value (`fold_ext`, `airTgE_ext`).
Base and extension constraints in one sequence of powers recombine to
the sum of the two folds (`airTgE_mixed`).  A constraint whose value
vanishes on `H` vanishes coordinate by coordinate (`hvan_eq4`).
Challenges enter such a constraint as constants, fixed before the
quotient, in the public-coin model.
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

-- ---------------------------------------------------------------------------
-- Constraints over the extension, through their base coordinates
-- ---------------------------------------------------------------------------

/-- Each weight `w` for its constraint's four coordinates: `w, w X, w X², w X³`. -/
def wq : List EF → List EF
  | w :: ws => w :: bE1.mul w :: bE2.mul w :: bE3.mul w :: wq ws
  | [] => []

/-- An extension constraint's four coordinates, evaluated. -/
def vq (ρE : Atom → EF) : List Q → List EF
  | q :: qs => q.q0.evalE ρE :: q.q1.evalE ρE :: q.q2.evalE ρE :: q.q3.evalE ρE :: vq ρE qs
  | [] => []

/-- The constraints' coordinates as base expressions. -/
def eq4 : List Q → List E
  | q :: qs => q.q0 :: q.q1 :: q.q2 :: q.q3 :: eq4 qs
  | [] => []

theorem vq_eq (ρE : Atom → EF) : ∀ qs : List Q, vq ρE qs = (eq4 qs).map (·.evalE ρE)
  | [] => rfl
  | q :: qs => by
    show _ :: _ :: _ :: _ :: vq ρE qs = _ :: _ :: _ :: _ :: (eq4 qs).map _
    rw [vq_eq ρE qs]

theorem wq_step (w a0 a1 a2 a3 R : EF) :
    (w.mul a0).add (((bE1.mul w).mul a1).add (((bE2.mul w).mul a2).add (((bE3.mul w).mul a3).add R))) =
      (w.mul (recomb a0 a1 a2 a3)).add R := by
  let b1 : Q := ⟨k 0, k 1, k 0, k 0⟩
  let b2 : Q := ⟨k 0, k 0, k 1, k 0⟩
  let b3 : Q := ⟨k 0, k 0, k 0, k 1⟩
  exact Q.eq_of_norm
    (p := ((Q.var 0).mul (Q.var 1)).add (((b1.mul (Q.var 0)).mul (Q.var 2)).add (((b2.mul (Q.var 0)).mul (Q.var 3)).add
      (((b3.mul (Q.var 0)).mul (Q.var 4)).add (Q.var 5)))))
    (q := ((Q.var 0).mul ((Q.var 1).add ((b1.mul (Q.var 2)).add ((b2.mul (Q.var 3)).add (b3.mul (Q.var 4)))))).add
      (Q.var 5))
    (by decide) (env8 w a0 a1 a2 a3 R EF.zero EF.zero)

/-- **An extension constraint's coordinates fold to the constraint**: with
    weights `w X^m` on coordinate `m`, the base fold is the fold of the
    extension values `Σ_m X^m q_m`. -/
theorem fold_ext (ρE : Atom → EF) : ∀ (ws : List EF) (qs : List Q), ws.length = qs.length →
    foldEE (wq ws) (vq ρE qs) =
      foldEE ws (qs.map fun q => recomb (q.q0.evalE ρE) (q.q1.evalE ρE) (q.q2.evalE ρE) (q.q3.evalE ρE))
  | [], [], _ => rfl
  | w :: ws, q :: qs, h => by
    show (w.mul _).add (((bE1.mul w).mul _).add (((bE2.mul w).mul _).add (((bE3.mul w).mul _).add
      (foldEE (wq ws) (vq ρE qs))))) = (w.mul _).add _
    rw [wq_step, fold_ext ρE ws qs (Nat.succ.inj h)]

/-- **The extension constraints' targets at `ζ` recombine to the verifier's
    check**: coordinate `k`'s weights are coordinate `k` of `αʲ X^m`, and
    the four targets recombine to `Σ_j αʲ c_j(ζ)`, `c_j = Σ_m X^m q_{j,m}(ζ)`,
    over the common denominator. -/
theorem airTgE_ext (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F)
    (H : List F) (αs : List EF) (cons : List Q) (hl : αs.length = cons.length) (ρE : Atom → EF) :
    recomb (airTgE ζ cs Hl cl qs ql κ H ((wq αs).map (·.x0)) (eq4 cons) ρE)
      (airTgE ζ cs Hl cl qs ql κ H ((wq αs).map (·.x1)) (eq4 cons) ρE)
      (airTgE ζ cs Hl cl qs ql κ H ((wq αs).map (·.x2)) (eq4 cons) ρE)
      (airTgE ζ cs Hl cl qs ql κ H ((wq αs).map (·.x3)) (eq4 cons) ρE) =
    (foldEE αs (cons.map fun q => recomb (q.q0.evalE ρE) (q.q1.evalE ρE) (q.q2.evalE ρE) (q.q3.evalE ρE))).mul
      ((fvalE ζ (fvan H)).mul ((EF.ofF κ).mul (fvalE ζ (rpoly.ppoly (allL cs Hl cl qs ql))))).inv := by
  rw [airTgE_back, ← vq_eq, fold_ext ρE αs cons hl]

/-- **An extension constraint vanishes coordinate by coordinate**: `hvan`
    for the coordinates `eq4 cons` from each constraint's value vanishing. -/
theorem hvan_eq4 (ρ : Atom → List F) (H : List F) :
    ∀ cons : List Q, (∀ q ∈ cons, ∀ x ∈ H, q.eval (fun a => fval x (ρ a)) = EF.zero) →
      ∀ e ∈ eq4 cons, ∀ x ∈ H, e.eval (fun a => fval x (ρ a)) = 0
  | [], _, _, he, _, _ => nomatch he
  | q :: cons, h, e, he, x, hx => by
    have hq := h q List.mem_cons_self x hx
    have h0 := congrArg EF.x0 hq; have h1 := congrArg EF.x1 hq
    have h2 := congrArg EF.x2 hq; have h3 := congrArg EF.x3 hq
    rcases List.mem_cons.1 he with rfl | he
    · exact h0
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    rcases List.mem_cons.1 he with rfl | he
    · exact h2
    rcases List.mem_cons.1 he with rfl | he
    · exact h3
    exact hvan_eq4 ρ H cons (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) e he x hx

theorem foldEE_append : ∀ (w1 v1 w2 v2 : List EF), w1.length = v1.length →
    foldEE (w1 ++ w2) (v1 ++ v2) = (foldEE w1 v1).add (foldEE w2 v2)
  | [], [], w2, v2, _ => by show foldEE w2 v2 = EF.zero.add _; rw [EF.zero_add]
  | w :: w1, v :: v1, w2, v2, h => by
    show (w.mul v).add (foldEE (w1 ++ w2) (v1 ++ v2)) = ((w.mul v).add (foldEE w1 v1)).add _
    rw [foldEE_append w1 v1 w2 v2 (Nat.succ.inj h), EF.add_assoc]

/-- **Base and extension constraints in one fold**: Plonky3 draws one
    power of `α` for each constraint, base or extension.  With the base
    constraints `esb` weighted by `αb` and the extension constraints
    `cons` by `αe`, the four coordinates' targets recombine to the sum of
    the two folds over the common denominator. -/
theorem airTgE_mixed (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F)
    (H : List F) (αb αe : List EF) (esb : List E) (cons : List Q) (hb : αb.length = esb.length)
    (he : αe.length = cons.length) (ρE : Atom → EF) :
    recomb (airTgE ζ cs Hl cl qs ql κ H ((αb ++ wq αe).map (·.x0)) (esb ++ eq4 cons) ρE)
      (airTgE ζ cs Hl cl qs ql κ H ((αb ++ wq αe).map (·.x1)) (esb ++ eq4 cons) ρE)
      (airTgE ζ cs Hl cl qs ql κ H ((αb ++ wq αe).map (·.x2)) (esb ++ eq4 cons) ρE)
      (airTgE ζ cs Hl cl qs ql κ H ((αb ++ wq αe).map (·.x3)) (esb ++ eq4 cons) ρE) =
    ((foldEE αb (esb.map (·.evalE ρE))).add
      (foldEE αe (cons.map fun q => recomb (q.q0.evalE ρE) (q.q1.evalE ρE) (q.q2.evalE ρE) (q.q3.evalE ρE)))).mul
      ((fvalE ζ (fvan H)).mul ((EF.ofF κ).mul (fvalE ζ (rpoly.ppoly (allL cs Hl cl qs ql))))).inv := by
  rw [airTgE_back, List.map_append, foldEE_append _ _ _ _ (by rw [List.length_map]; exact hb), ← vq_eq,
    fold_ext ρE αe cons he]

end Circuit
