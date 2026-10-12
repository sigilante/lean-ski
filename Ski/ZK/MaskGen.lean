import Ski.ZK.MaskFri

/-!
# The challenges the hiding needs: all but `P²` of the `P⁴`

`pcsCloseN_fri` asks that `1, αb, αb², αb³` be independent over `F`
(`(mz αb).det ≠ 0`, `apow αb w ≠ 0`), and every quotient column that
`1, ζ, ζ², ζ³` be, with `ζ` off `F` (`CSet.OK`).  Each is `Generic`
(`Ski/ZK/Comb.lean`): `mz β` lists the same powers as `combMat β`, the
columns reversed, an even permutation (`M4.det_rev`, `mz_det_eq`), so
`Generic β` gives all three (`mz_generic`, `generic_ofF_ne`,
`generic_apow_ne`).  `Generic β` holds exactly when `β` lies outside
`F(x²)` (`generic_iff`), for all but `P²` of the `P⁴` challenges
(`nongeneric_count`): a uniform draw fails with probability `P^-2`, about
`2^-62`.  `pcsCloseN_fri_generic` states the hiding with `Generic αb`.
-/

namespace Circuit

open ZKF

theorem M4.det_rev (m : M4) : m.det = Mat4.det ⟨m.a03, m.a02, m.a01, m.a00, m.a13, m.a12, m.a11, m.a10, m.a23, m.a22, m.a21, m.a20, m.a33, m.a32, m.a31, m.a30⟩ :=
  fid (e := (v 3 * v 6 * v 9 * v 12) - (v 3 * v 6 * v 8 * v 13) - (v 3 * v 5 * v 10 * v 12) + (v 3 * v 5 * v 8 * v 14) + (v 3 * v 4 * v 10 * v 13) - (v 3 * v 4 * v 9 * v 14) - (v 2 * v 7 * v 9 * v 12) + (v 2 * v 7 * v 8 * v 13) + (v 2 * v 5 * v 11 * v 12) - (v 2 * v 5 * v 8 * v 15) - (v 2 * v 4 * v 11 * v 13) + (v 2 * v 4 * v 9 * v 15) + (v 1 * v 7 * v 10 * v 12) - (v 1 * v 7 * v 8 * v 14) - (v 1 * v 6 * v 11 * v 12) + (v 1 * v 6 * v 8 * v 15) + (v 1 * v 4 * v 11 * v 14) - (v 1 * v 4 * v 10 * v 15) - (v 0 * v 7 * v 10 * v 13) + (v 0 * v 7 * v 9 * v 14) + (v 0 * v 6 * v 11 * v 13) - (v 0 * v 6 * v 9 * v 15) - (v 0 * v 5 * v 11 * v 14) + (v 0 * v 5 * v 10 * v 15)) (e' := det4E) (by decide)
    [m.a03, m.a02, m.a01, m.a00, m.a13, m.a12, m.a11, m.a10, m.a23, m.a22, m.a21, m.a20, m.a33, m.a32, m.a31, m.a30, EF.zero.x0, EF.zero.x1, EF.zero.x2, EF.zero.x3, 0]

theorem bpow_one' (β : EF) : bpow β 1 = β := EF.one_mul β

theorem bpow_two' (β : EF) : bpow β 2 = β.mul β := by
  show (bpow β 1).mul β = _; rw [bpow_one']

theorem bpow_three' (β : EF) : bpow β 3 = (β.mul β).mul β := by
  show (bpow β 2).mul β = _; rw [bpow_two']

/-- **`mz β` and `combMat β` have one determinant**. -/
theorem mz_det_eq (β : EF) : (mz β).det = (combMat β).det := by
  rw [M4.det_rev]
  unfold combMat
  rw [bpow_three', bpow_two', bpow_one']
  rfl

theorem mz_generic {β : EF} (h : Generic β) : (mz β).det ≠ 0 := by
  rw [mz_det_eq]; exact h

theorem generic_ofF_ne {β : EF} (h : Generic β) : ∀ x : F, EF.ofF x ≠ β := by
  intro x e
  rcases (generic_iff β).1 h with h1 | h3
  · exact h1 (by rw [← e]; rfl)
  · exact h3 (by rw [← e]; rfl)

theorem generic_ne_zero {β : EF} (h : Generic β) : β ≠ EF.zero := by
  intro e
  rcases (generic_iff β).1 h with h1 | h3
  · exact h1 (by rw [e]; rfl)
  · exact h3 (by rw [e]; rfl)

theorem generic_apow_ne {β : EF} (h : Generic β) : ∀ w, apow β w ≠ EF.zero
  | 0 => EF.one_ne_zero
  | w + 1 => fun e => (EF.mul_eq_zero e).elim (generic_ne_zero h) (generic_apow_ne h w)

/-- **The hiding with a generic batching challenge**: `pcsCloseN_fri` with
    `Generic αb` in place of its two conditions. -/
theorem pcsCloseN_fri_generic {V : Type} {qs : List QGroup} {ks : List Nat}
    {cols : (Nat → Tup) → EF → EF → List (List (List F))} {qtabs : List QTab}
    {qdT : (Nat → Tup) → EF → EF → List F → List (List (List (List F) × List F))} {ncw : Nat}
    {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (hg : Generic αb) (hncw : 4 ≤ ncw)
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    (htab : ∀ t α β ms, TabsHonest
      (fun c => c.JS α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms)) qtabs (qdT t α β ms)) :
    PCSCloseN off (P ^ (friN1 qs ks qtabs + friN2 qs qtabs ncw)) tv
      (pcsFri off tv qs ks cols qtabs qdT ncw αb fri) (psimFri qs ks qtabs ncw αb fri) 0 :=
  pcsCloseN_fri hok hks hcols (mz_generic hg) (generic_apow_ne hg) hncw off tv htab

/-- **A quotient column's `ζ` conditions from `Generic ζ`**. -/
theorem cset_ok_of_generic {c : CSet} (hg : Generic c.ζ) (hn : c.S.length + 4 ≤ c.h)
    (hcs : ∀ ch ∈ c.cs, ch.c ≠ 0 ∧ ch.m ≠ 0) (hcl : c.cl ≠ 0) : c.OK :=
  ⟨generic_ofF_ne hg, mz_generic hg, hn, hcs, hcl⟩

end Circuit
