import Ski.ZK.MaskSplit

/-!
# Plonky3's selector weights

`quotOK_of_coset` asks `κ μ_k ∏_{j ≠ k} v_j(s_k) = 1` at each domain's
first point `s_k`.  Plonky3 defines `cis_k = 1 / ∏_{j ≠ k} Z_j(s_k)`
(`get_zp_cis`), `κ = cis_l` and `μ_k = cis_k / cis_l` (`mul_coeffs`).
This file shows those weights meet the hypothesis.  The product is
nonzero at `s_k` because `s_k` lies in no other domain and every scale
is nonzero (`opv_ne`).  So `cis_k` is the product's inverse
(`first_of_cis`).
-/

namespace Circuit

open ZKF

/-- **`∏_{j ≠ k} v_j` is nonzero on chunk `k`'s domain** when the domains
    are disjoint and the scales nonzero. -/
theorem opv_ne {x : F} : ∀ (L : List (List F × F × F × List F)) (k : Nat) (hk : k < L.length),
    (∀ p ∈ L, p.2.1 ≠ 0) → (∀ j (hj : j < L.length), j ≠ k → x ∉ (L[j]'hj).1) → opv x L k ≠ 0
  | [], _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: L, 0, _, hc, hd =>
    ppoly_val_ne x L (fun p hp => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
      exact mul_ne_zero' (hc _ (List.mem_cons_of_mem _ hp))
        (fvan_ne x _ (hd (j + 1) (Nat.succ_lt_succ hj) (Nat.succ_ne_zero j))))
  | (H, c, μ, q) :: L, k + 1, hk, hc, hd => by
    show c * fval x (fvan H) * opv x L k ≠ 0
    exact mul_ne_zero' (mul_ne_zero' (hc _ List.mem_cons_self) (fvan_ne x H (hd 0 (Nat.succ_pos _) (Nat.succ_ne_zero k).symm)))
      (opv_ne L k (Nat.lt_of_succ_lt_succ hk) (fun p hp => hc p (List.mem_cons_of_mem _ hp))
        (fun j hj hjk => hd (j + 1) (Nat.succ_lt_succ hj) (fun e => hjk (Nat.succ.inj e))))

theorem cis_c (κ fo fk o : F) : κ * (fo * fk) * o = (κ * fk) * (o * fo) :=
  fid (e := v 0 * (v 1 * v 2) * v 3) (e' := (v 0 * v 2) * (v 3 * v 1)) (by decide) [κ, fo, fk, o]

theorem cis_step (κ o : F) (hκ : κ ≠ 0) (ho : o ≠ 0) : κ * (finv o * finv κ) * o = 1 := by
  rw [cis_c, mul_finv hκ, mul_finv ho, one_mul']

/-- **Plonky3's weights normalize the selectors at each first point**: with
    `μ_k = cis_k / κ`, `cis_k = 1 / ∏_{j ≠ k} v_j(s_k)`, the hypothesis of
    `quotOK_of_coset` holds, for domains `cosetL s g (n + 1)` that are
    disjoint, with nonzero scales. -/
theorem first_of_cis (κ g : F) (n : Nat) (hκ : κ ≠ 0) (L : List (List F × F × F × List F))
    (hc : ∀ p ∈ L, p.2.1 ≠ 0)
    (hdis : ∀ k j (hk : k < L.length) (hj : j < L.length), j ≠ k → ∀ x ∈ (L[k]'hk).1, x ∉ (L[j]'hj).1)
    (hw : ∀ k (hk : k < L.length), ∀ s, (L[k]'hk).1 = cosetL s g (n + 1) →
      (L[k]'hk).2.2.1 = finv (opv s L k) * finv κ) :
    ∀ k (hk : k < L.length), ∀ s, (L[k]'hk).1 = cosetL s g (n + 1) → κ * (L[k]'hk).2.2.1 * opv s L k = 1 := by
  intro k hk s hs
  have hsk : s ∈ (L[k]'hk).1 := by rw [hs]; exact List.mem_cons_self
  rw [hw k hk s hs]
  exact cis_step κ _ hκ (opv_ne L k hk hc (fun j hj hjk => hdis k j hk hj hjk s hsk))

end Circuit
