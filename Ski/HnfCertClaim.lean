import Ski.HnfCertRunSound2
open Term

/-!
# Soundness of the claims, and hypothesis (A) from the checker

`claims_sound`: if `checkClaim` holds for every claim (and the two table facts `MinOK`,
`ShapesOK`), every instance of every claim is not productive.  `minimalPairs_of_checks` adds
`rootsCovered` and yields `HnfQ5.MinimalPairs`.
-/

namespace HnfCert
open HnfS HnfSound HnfProd HnfCertLaws HnfB0 HnfQ5

/-! ## Variable occurrences -/

def occ : CT → Term → List Term
  | .S, _ => []
  | .V _, u => [u]
  | .A l r, .app a b => occ l a ++ occ r b
  | .A _ _, _ => []

theorem occ_len : ∀ {c : CT} {u : Term}, Inst c u → (occ c u).length = c.vars.length
  | .S, _, _ => rfl
  | .V _, _, _ => rfl
  | .A _ _, _, ⟨_, _, rfl, ha, hb⟩ => by simp [occ, CT.vars, occ_len ha, occ_len hb]

theorem occ_mem : ∀ {c : CT} {u : Term}, Inst c u → ∀ j, j < c.vars.length →
    ∃ w, (occ c u)[j]? = some w ∧ c.vars[j]? = some (pst w) ∧ PureS w ∧ Sub w u
  | .S, _, _, j, hj => by simp [CT.vars] at hj
  | .V s, u, h, j, hj => by
    simp only [CT.vars, List.length_singleton] at hj
    have : j = 0 := by omega
    subst this; exact ⟨u, rfl, by simp [CT.vars, h.2], h.1, .refl u⟩
  | .A l r, _, ⟨a, b, rfl, ha, hb⟩, j, hj => by
    simp only [CT.vars, List.length_append] at hj
    by_cases hjl : j < l.vars.length
    · obtain ⟨w, h1, h2, h3, h4⟩ := occ_mem ha j hjl
      refine ⟨w, ?_, ?_, h3, .left b h4⟩
      · simp only [occ]; rw [List.getElem?_append_left (by rw [occ_len ha]; exact hjl)]; exact h1
      · simp only [CT.vars]; rw [List.getElem?_append_left hjl]; exact h2
    · obtain ⟨w, h1, h2, h3, h4⟩ := occ_mem hb (j - l.vars.length) (by omega)
      refine ⟨w, ?_, ?_, h3, .right a h4⟩
      · simp only [occ]; rw [List.getElem?_append_right (by rw [occ_len ha]; omega), occ_len ha]; exact h1
      · simp only [CT.vars]; rw [List.getElem?_append_right (by omega)]; exact h2

/-! ## Root sizes -/

def szAt (L : List Term) (j : Nat) : Int := if j < L.length then tsz (L.getD j S) else 0
def szOf (L : List Term) : Sz := ⟨szAt L 0, szAt L 1, szAt L 2, szAt L 3, szAt L 4⟩

def comp (s : Sz) : Nat → Int
  | 0 => s.s0 | 1 => s.s1 | 2 => s.s2 | 3 => s.s3 | 4 => s.s4 | _ => 0

theorem eval_unit (s : Sz) : ∀ i, i < 5 → (Form.unit i).eval s = comp s i
  | 0, _ => by simp [Form.unit, Form.eval, comp]
  | 1, _ => by simp [Form.unit, Form.eval, comp]
  | 2, _ => by simp [Form.unit, Form.eval, comp]
  | 3, _ => by simp [Form.unit, Form.eval, comp]
  | 4, _ => by simp [Form.unit, Form.eval, comp]
  | n + 5, h => by omega

theorem comp_szOf (L : List Term) : ∀ i, i < 5 → comp (szOf L) i = szAt L i
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
  | n + 5, h => by omega

theorem toRT_spec (L : List Term) : ∀ (c : CT) (u : Term) (i : Nat), Inst c u →
    i + c.vars.length ≤ 5 → i + c.vars.length ≤ L.length →
    (∀ j, j < c.vars.length → L.getD (i + j) S = (occ c u).getD j S) →
    (toRT c i).2 = i + c.vars.length ∧ InstR (szOf L) (toRT c i).1 u ∧
      ∃ g, (toRT c i).1.sz = some g ∧ g.eval (szOf L) = tsz u
  | .S, u, i, h, _, _, _ => by
    subst h; refine ⟨rfl, rfl, Form.const 1, rfl, ?_⟩; rw [eval_const]; rfl
  | .V s, u, i, h, h5, hL, hocc => by
    simp only [CT.vars, List.length_singleton] at h5 hL
    have hu0 : L.getD i S = u := by simpa [occ] using hocc 0 (by simp [CT.vars])
    have hfix : ∀ g : Form, (match exactB (s % 64) with | some v => Form.const v | none => Form.unit i) = g →
        g.eval (szOf L) = tsz u := by
      intro g hg
      cases hv : exactB (s % 64) with
      | some v =>
        rw [hv] at hg; subst hg; rw [eval_const]
        rw [← h.2, pst_mod h.1] at hv; rw [exact_size h.1 hv]
      | none =>
        rw [hv] at hg; subst hg
        rw [eval_unit _ i (by omega), comp_szOf _ i (by omega)]
        simp only [szAt, show i < L.length by omega, if_true, hu0]
    refine ⟨rfl, ⟨h.1, h.2, ?_⟩, _, rfl, hfix _ rfl⟩
    intro g hg; simp only [Option.some.injEq] at hg; rw [hfix g hg]; exact Int.le_refl _
  | .A l r, _, i, ⟨a, b, rfl, ha, hb⟩, h5, hL, hocc => by
    simp only [CT.vars, List.length_append] at h5 hL hocc
    have hla := occ_len ha
    obtain ⟨e1, i1, g1, hg1, ev1⟩ := toRT_spec L l a i ha (by omega) (by omega) (by
      intro j hj; rw [hocc j (by omega)]; simp only [occ]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [hla]; exact hj)])
    obtain ⟨e2, i2, g2, hg2, ev2⟩ := toRT_spec L r b (toRT l i).2 hb (by rw [e1]; omega) (by rw [e1]; omega) (by
      intro j hj; rw [e1, show i + l.vars.length + j = i + (l.vars.length + j) by omega,
        hocc (l.vars.length + j) (by omega)]
      simp only [occ]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hla]; omega), hla, show l.vars.length + j - l.vars.length = j by omega])
    refine ⟨by simp only [toRT, CT.vars, List.length_append]; rw [e2, e1]; omega, ?_, ?_⟩
    · simp only [toRT]; exact mkA_inst i1 i2
    · refine ⟨g1.add g2, ?_, ?_⟩
      · simp only [toRT, mkA, RT.sz, hg1, hg2, oadd]
      · rw [eval_add, ev1, ev2]; simp [tsz]

theorem mins_le {c : CT} {u : Term} (hMin : MinOK) (h : Inst c u) :
    MinsLe (minsOf c.vars) (szOf (occ c u)) := by
  have key : ∀ j, minAt c.vars j ≤ szAt (occ c u) j := by
    intro j
    simp only [minAt, szAt, occ_len h]
    split
    · rename_i hj
      obtain ⟨w, h1, h2, h3, _⟩ := occ_mem h j hj
      have e1 : c.vars.getD j 0 = pst w := by rw [List.getD_eq_getElem?_getD, h2]; rfl
      have e2 : (occ c u).getD j S = w := by rw [List.getD_eq_getElem?_getD, h1]; rfl
      rw [e1, e2]; exact Int.ofNat_le.mpr (minsz_le hMin h3)
    · exact Int.le_refl _
  exact ⟨key 0, key 1, key 2, key 3, key 4⟩

/-! ## Replacing an occurrence -/

theorem replaceK_none (new : CT) : ∀ c : CT, replaceK new c none = (c, none)
  | .S => rfl
  | .V _ => rfl
  | .A l r => by simp only [replaceK, replaceK_none new l, replaceK_none new r]

theorem replaceK_spec (new : CT) : ∀ (c : CT) (u : Term) (i : Nat), Inst c u →
    (∀ w, (occ c u)[i]? = some w → Inst new w) →
    Inst (replaceK new c (some i)).1 u ∧
      (replaceK new c (some i)).2 = (if i < c.vars.length then none else some (i - c.vars.length))
  | .S, _, _, h, _ => ⟨h, by simp [replaceK, CT.vars]⟩
  | .V s, u, 0, h, hw => ⟨hw u rfl, by simp [replaceK, CT.vars]⟩
  | .V s, u, i + 1, h, _ => ⟨h, by simp [replaceK, CT.vars]⟩
  | .A l r, _, i, ⟨a, b, rfl, ha, hb⟩, hw => by
    have hla := occ_len ha
    by_cases hi : i < l.vars.length
    · obtain ⟨i1, e1⟩ := replaceK_spec new l a i ha (by
        intro w hw'; apply hw; simp only [occ]; rw [List.getElem?_append_left (by rw [hla]; exact hi)]; exact hw')
      simp only [hi, if_true] at e1
      refine ⟨?_, ?_⟩
      · simp only [replaceK, e1, replaceK_none]; exact ⟨a, b, rfl, i1, hb⟩
      · simp only [replaceK, e1, replaceK_none, CT.vars, List.length_append]
        rw [if_pos (by omega)]
    · obtain ⟨i1, e1⟩ := replaceK_spec new l a i ha (by
        intro w hw'
        have : (occ l a).length ≤ i := by rw [hla]; omega
        simp [List.getElem?_eq_none this] at hw')
      simp only [hi, if_false] at e1
      obtain ⟨i2, e2⟩ := replaceK_spec new r b (i - l.vars.length) hb (by
        intro w hw'; apply hw; simp only [occ]
        rw [List.getElem?_append_right (by rw [hla]; omega), hla]; exact hw')
      refine ⟨?_, ?_⟩
      · simp only [replaceK, e1]; exact ⟨a, b, rfl, i1, i2⟩
      · simp only [replaceK, e1, e2, CT.vars, List.length_append]
        by_cases h2 : i - l.vars.length < r.vars.length
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]; congr 1; omega

/-! ## The main induction -/

theorem split_sound (hSp : SplitsOK) {c : Claim} {u : Term} {k : Nat} (hc : checkClaim c = true)
    (hk : c.split = some k) (hu : Inst c.term u)
    (ih : ∀ d ∈ CLAIMS, Inst d.term u → (d.stratum < c.stratum ∨ (d.stratum = c.stratum ∧ d.rank < c.rank)) →
      ¬ Prod u) : ¬ Prod u := by
  simp only [checkClaim, hk, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hσ0, hσacc⟩, hklt⟩, hall⟩ := hc
  obtain ⟨w, hw1, hw2, hwp, _⟩ := occ_mem hu k hklt
  have hσ : c.term.vars.getD k 0 = pst w := by rw [List.getD_eq_getElem?_getD, hw2]; rfl
  rw [hσ] at hσ0 hσacc hall
  have hcw : cls w ≠ 37 := (accN_pst hwp).mp hσacc
  cases hwp with
  | S => exact absurd pst_S hσ0
  | @app p q hp hq =>
    have hc2 := cls_args hp hq hcw
    have hpa := pst_accs hp hc2.1; have hqa := pst_accs hq hc2.2
    have hmem : (pst p, pst q) ∈ splits (pst (p ⬝ q)) := by
      rw [pst_app hp hq] at hσacc ⊢; exact splits_complete hSp hpa hqa hσacc
    obtain ⟨d, hd, hcond⟩ := hall _ hmem
    obtain ⟨hdc, hdt⟩ := lookup_sound hd
    have hinst : Inst d.term u := by
      rw [hdt]
      exact (replaceK_spec _ c.term u k hu (by
        intro w' hw'; rw [hw1] at hw'; cases hw'
        exact ⟨p, q, rfl, inst_mkV hp, inst_mkV hq⟩)).1
    exact ih d hdc hinst hcond

theorem claims_sound (hAll : ∀ c ∈ CLAIMS, checkClaim c = true) (hMin : MinOK) (hSh : ShapesOK)
    (hSp : SplitsOK) :
    ∀ c ∈ CLAIMS, ∀ u, Inst c.term u → ¬ Prod u := by
  suffices H : ∀ S N R, ∀ c ∈ CLAIMS, c.stratum = S → c.rank = R → ∀ u, Inst c.term u → tsz u = N → ¬ Prod u by
    intro c hc u hu; exact H _ _ _ c hc rfl rfl u hu rfl
  intro S
  refine Nat.strongRecOn S ?_
  intro S ihS N
  refine Nat.strongRecOn N ?_
  intro N ihN R
  refine Nat.strongRecOn R ?_
  intro R ihR c hc hS hR u hu hN
  have IH : ∀ d ∈ CLAIMS, ∀ v, Inst d.term v →
      (d.stratum < c.stratum ∨ (d.stratum = c.stratum ∧ (tsz v < N ∨ (tsz v = N ∧ d.rank < c.rank)))) →
      ¬ Prod v := by
    intro d hd v hv hlt
    rcases hlt with h1 | ⟨h2, h3 | ⟨h4, h5⟩⟩
    · exact ihS d.stratum (hS ▸ h1) (tsz v) d.rank d hd rfl rfl v hv rfl
    · exact ihN (tsz v) h3 d.rank d hd (h2.trans hS) rfl v hv rfl
    · exact ihR d.rank (hR ▸ h5) d hd (h2.trans hS) rfl v hv h4
  have hck := hAll c hc
  cases hsp : c.split with
  | some k =>
    exact split_sound hSp hck hsp hu (fun d hd hv h => IH d hd u hv (by
      rcases h with h | ⟨h1, h2⟩
      · exact .inl h
      · exact .inr ⟨h1, .inr ⟨hN, h2⟩⟩))
  | none =>
    simp only [checkClaim, hsp, Bool.and_eq_true, decide_eq_true_eq] at hck
    obtain ⟨h5, hck⟩ := hck
    obtain ⟨_, hinst, g, hg, hev⟩ := toRT_spec (occ c.term u) c.term u 0 hu (by omega)
      (by rw [occ_len hu]; omega) (by intro j _; simp)
    rw [hg] at hck
    simp only at hck
    split at hck
    · rename_i hs' hrun
      exact run_sound (cx := ⟨c.stratum, c.rank, g, minsOf c.term.vars⟩) (N := N)
        ⟨by simp only; rw [hev, hN], mins_le hMin hu, IH⟩ hSh _ _ _ _ _ hrun u hinst
    · cases hck

/-- **(A) from the checker.** -/
theorem minimalPairs_of_checks (hAll : ∀ c ∈ CLAIMS, checkClaim c = true) (hMin : MinOK)
    (hSh : ShapesOK) (hSp : SplitsOK) (hRoots : rootsCovered = true) : MinimalPairs := by
  intro u v hu hv hcu hcv hc hf hP
  simp only [rootsCovered, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at hRoots
  have hpu := pst_accs hu hcu; have hpv := pst_accs hv hcv
  rcases hRoots _ hpu _ hpv with (hacc | h36) | hne
  · rw [← pst_app hu hv] at hacc; exact absurd hc ((accN_pst (.app hu hv)).mp hacc)
  · rw [← pst_app hu hv, pst_mod (.app hu hv)] at h36; exact hf h36
  · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨hdc, hdt⟩ := lookup_sound hd
    have hinst : Inst d.term (u ⬝ v) := by rw [hdt]; exact ⟨u, v, rfl, inst_mkV hu, inst_mkV hv⟩
    exact claims_sound hAll hMin hSh hSp d hdc _ hinst hP

end HnfCert
