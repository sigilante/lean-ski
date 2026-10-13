import Ski.ZK.PreOpen

/-!
# The masked column is Plonky3's interleaved column

Plonky3's hiding PCS randomizes a trace of `n` rows by interleaving a
random row after each trace row (`HidingFriPcs::commit`:
`with_random_cols`, then a reshape to half the width,
`p3-fri-0.8.0/src/hiding_pcs.rs:247-251`), committing a `2n`-row matrix
over the subgroup `⟨ω⟩` of order `2n` (`natural_domain_for_degree`,
shift 1).  The trace rows sit at the even points, `ω^(2i) = g^i`, the
trace domain `⟨g⟩` for `g = ω²`; the random rows at the odd points
`ω · g^i` (`coset_ileave`).

The model commits a column as `mcol T R t r`, the interpolant of the
trace values `t` at the trace points `T` and the masks `r` at the mask
points `R`.  With `T = cosetL 1 g n` and `R = cosetL ω g n`, the groups'
`hT` and `hRq` (`bbGroup`), it is the interpolant of the interleaved
column over `⟨ω⟩`, coefficient by coefficient (`ileave_mcol_coef`), so at
every point of `F` and of the extension, and over BabyBear for every
trace height (`bb_ileave_mcol`).  This covers the trace's `w` columns; the
`k` all-random codeword columns the commit adds are a separate matter
(`Ski/ZK/MaskFri.lean`).  So the masked columns the model
opens are Plonky3's committed polynomials.

Read from Plonky3's source, not proved: that the hiding PCS interleaves
(trace rows even, random rows odd) and commits the `2n`-row matrix over
`⟨ω⟩`.
-/

namespace Circuit

open ZKF

/-- Two lists interleaved: `a₀ b₀ a₁ b₁ …`. -/
def ileave {α : Type} : List α → List α → List α
  | a :: as, b :: bs => a :: b :: ileave as bs
  | as, [] => as
  | [], bs => bs

theorem ileave_perm {α : Type} : ∀ (a b : List α), (ileave a b).Perm (a ++ b)
  | a :: as, b :: bs => by
    show (a :: b :: ileave as bs).Perm (a :: (as ++ b :: bs))
    exact List.Perm.cons a ((List.Perm.cons b (ileave_perm as bs)).trans List.perm_middle.symm)
  | [], [] => List.Perm.refl _
  | a :: as, [] => by show (a :: as).Perm _; rw [List.append_nil]
  | [], _ :: _ => List.Perm.refl _

theorem zip_ileave {α β : Type} : ∀ (a b : List α) (c d : List β), a.length = c.length → b.length = d.length →
    a.length = b.length → (ileave a b).zip (ileave c d) = ileave (a.zip c) (b.zip d)
  | [], [], [], [], _, _, _ => rfl
  | x :: a, y :: b, z :: c, w :: d, h1, h2, h3 => by
    show (x, z) :: (y, w) :: (ileave a b).zip (ileave c d) = (x, z) :: (y, w) :: ileave (a.zip c) (b.zip d)
    rw [zip_ileave a b c d (by simpa using h1) (by simpa using h2) (by simpa using h3)]
  | [], _ :: _, _, _, _, _, h3 => nomatch h3
  | _ :: _, [], _, _, _, _, h3 => nomatch h3
  | [], [], _ :: _, _, h1, _, _ => nomatch h1
  | [], [], [], _ :: _, _, h2, _ => nomatch h2
  | _ :: _, _ :: _, [], _, h1, _, _ => nomatch h1
  | _ :: _, _ :: _, _ :: _, [], _, h2, _ => nomatch h2

theorem ileave_length {α : Type} (a b : List α) : (ileave a b).length = a.length + b.length := by
  rw [(ileave_perm a b).length_eq, List.length_append]

theorem mem_zip_of {L V : List F} (hl : L.length = V.length) {x : F} (hx : x ∈ L) : ∃ v, (x, v) ∈ L.zip V := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  exact ⟨V[i]'(hl ▸ hi), zip_mem hi hl⟩

/-- **The `2n` points split into even and odd**: `s ω^i` for `i < 2n` is
    `s g^j` at `i = 2j` and `s ω g^j` at `i = 2j + 1`, for `g = ω²`. -/
theorem coset_ileave (ω : F) : ∀ (n : Nat) (s : F),
    cosetL s ω (2 * n) = ileave (cosetL s (ω * ω) n) (cosetL (s * ω) (ω * ω) n)
  | 0, _ => rfl
  | n + 1, s => by
    show cosetL s ω (2 * n + 1 + 1) = _
    show s :: s * ω :: cosetL (s * ω * ω) ω (2 * n) =
      s :: s * ω :: ileave (cosetL (s * (ω * ω)) (ω * ω) n) (cosetL (s * ω * (ω * ω)) (ω * ω) n)
    rw [coset_ileave ω n (s * ω * ω), mul_assoc' s ω ω,
      show s * (ω * ω) * ω = s * ω * (ω * ω) by rw [mul_assoc', mul_assoc', mul_assoc', mul_comm' ω ω]]

/-- **The interleaved column is the masked column, coefficientwise**: on
    the `2n` distinct points `⟨ω⟩`, the interpolant of the trace values
    interleaved with the masks and `mcol` over the trace points `⟨ω²⟩` and
    the mask points `ω⟨ω²⟩` differ by zero coefficients, so they agree at
    every point of `F` and of the extension. -/
theorem ileave_mcol_coef (ω : F) (n : Nat) (hnd : (cosetL 1 ω (2 * n)).Nodup) {t r : List F} (ht : t.length = n)
    (hr : r.length = n) :
    FZero (fcdiff (finterp ((cosetL 1 ω (2 * n)).zip (ileave t r)))
      (mcol (cosetL 1 (ω * ω) n) (cosetL ω (ω * ω) n) t r)) := by
  have hc := coset_ileave ω n 1
  rw [one_mul'] at hc
  have hlT := cosetL_length 1 (ω * ω) n
  have hlR := cosetL_length ω (ω * ω) n
  have hz : (cosetL 1 ω (2 * n)).zip (ileave t r) =
      ileave ((cosetL 1 (ω * ω) n).zip t) ((cosetL ω (ω * ω) n).zip r) := by
    rw [hc]; exact zip_ileave _ _ _ _ (by rw [hlT, ht]) (by rw [hlR, hr]) (by rw [hlT, hlR])
  have hp := ileave_perm ((cosetL 1 (ω * ω) n).zip t) ((cosetL ω (ω * ω) n).zip r)
  rw [← hz] at hp
  have hl1 : (cosetL 1 ω (2 * n)).length = (ileave t r).length := by
    rw [cosetL_length, ileave_length, ht, hr]; omega
  have hnd1 : ((cosetL 1 ω (2 * n)).zip (ileave t r)).map Prod.fst = cosetL 1 ω (2 * n) := by
    rw [List.map_fst_zip]; omega
  have hnd2 : ((cosetL 1 (ω * ω) n).zip t ++ (cosetL ω (ω * ω) n).zip r).map Prod.fst |>.Nodup := by
    have := (hp.map Prod.fst).nodup_iff.1 (by rw [hnd1]; exact hnd)
    exact this
  have hlen1 := finterp_length ((cosetL 1 ω (2 * n)).zip (ileave t r))
  have hlen2 := finterp_length ((cosetL 1 (ω * ω) n).zip t ++ (cosetL ω (ω * ω) n).zip r)
  have hz1 : ((cosetL 1 ω (2 * n)).zip (ileave t r)).length = 2 * n := by
    rw [List.length_zip, ← hl1, cosetL_length, Nat.min_self]
  have hz2 : ((cosetL 1 (ω * ω) n).zip t ++ (cosetL ω (ω * ω) n).zip r).length = 2 * n := by
    rw [← hp.length_eq, hz1]
  refine fagree_zero (N := 2 * n) (by omega) (by unfold mcol; omega) (cosetL 1 ω (2 * n)) hnd (cosetL_length _ _ _)
    (fun x hx => ?_)
  obtain ⟨v, hv⟩ := mem_zip_of hl1 hx
  rw [finterp_eval _ (by rw [hnd1]; exact hnd) _ hv]
  unfold mcol
  rw [finterp_eval _ hnd2 _ (hp.mem_iff.1 hv)]

/-- **The interleaved column is the masked column** at every point of `F`. -/
theorem ileave_mcol (ω : F) (n : Nat) (hnd : (cosetL 1 ω (2 * n)).Nodup) {t r : List F} (ht : t.length = n)
    (hr : r.length = n) (y : F) :
    fval y (finterp ((cosetL 1 ω (2 * n)).zip (ileave t r))) =
      fval y (mcol (cosetL 1 (ω * ω) n) (cosetL ω (ω * ω) n) t r) := by
  have := fval_fzero y _ (ileave_mcol_coef ω n hnd ht hr)
  rw [fval_fcdiff] at this
  exact sub_eq_zero this

/-- **Over BabyBear, every group's masked column is the interleaved
    column**: for a trace of `2^(tb+1)` rows, `bbGroup`'s trace points
    `⟨bbGen (tb+1)⟩` and mask points `bbGen (tb+2) · ⟨bbGen (tb+1)⟩` hold
    Plonky3's even and odd rows over `⟨bbGen (tb+2)⟩`, and the two
    interpolants differ by zero coefficients. -/
theorem bb_ileave_mcol (tb : Nat) (htb : tb ≤ 25) {t r : List F} (ht : t.length = 2 ^ (tb + 1))
    (hr : r.length = 2 ^ (tb + 1)) :
    FZero (fcdiff (finterp ((cosetL 1 (bbGen (tb + 2)) (2 * 2 ^ (tb + 1))).zip (ileave t r)))
      (mcol (cosetL 1 (bbGen (tb + 1)) (2 ^ (tb + 1))) (cosetL (bbGen (tb + 2)) (bbGen (tb + 1)) (2 ^ (tb + 1)))
        t r)) := by
  have hsq : bbGen (tb + 2) * bbGen (tb + 2) = bbGen (tb + 1) :=
    of_decide_eq_true (List.all_eq_true.1 bbGen_chain.1 tb (List.mem_range.2 (by omega)))
  have hc := coset_ileave (bbGen (tb + 2)) (2 ^ (tb + 1)) 1
  rw [one_mul', hsq] at hc
  have hnd : (cosetL 1 (bbGen (tb + 2)) (2 * 2 ^ (tb + 1))).Nodup := by
    rw [hc]; exact (ileave_perm _ _).nodup_iff.2 (bb_masks tb htb)
  have := ileave_mcol_coef (bbGen (tb + 2)) (2 ^ (tb + 1)) hnd ht hr
  rw [hsq] at this
  exact this

end Circuit
