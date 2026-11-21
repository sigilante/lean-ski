import Ski.HnfCertSem
open Term

/-!
# Soundness of a replayed run

`run_sound`: if `run cx fuel dl t hs = some hs'`, every instance of `t` is not productive, given
the induction hypothesis for claims that are lower in (stratum, size, rank).
-/

namespace HnfCert
open HnfS HnfSound HnfProd HnfCertLaws HnfB0 HnfQ5

def Prod (u : Term) : Prop := ∀ k, Pk k u

theorem np_of_sub {m t : Term} (ht : PureS t) (hs : Sub m t) (hm : ¬ Prod m) : ¬ Prod t :=
  fun hP => hm fun k => prod_sub k ht hs hP

theorem np_of_wsteps {t t' : Term} (ht : PureS t) (hw : WSteps t t') (h : ¬ Prod t') : ¬ Prod t :=
  fun hP => h fun k => (pk_wsteps k ht hw).mp (hP k)

theorem wsteps_foldl {a b : Term} (h : WSteps a b) (w : List Term) :
    WSteps (w.foldl Term.app a) (w.foldl Term.app b) := by
  induction h with
  | refl => exact .refl _
  | step h1 _ ih => exact .step (wstep_foldl h1 w) ih

theorem sub_foldl_head (h : Term) : ∀ (vs : List Term), Sub h (vs.foldl Term.app h) := by
  intro vs
  induction vs generalizing h with
  | nil => exact .refl _
  | cons v vs ih =>
    simp only [List.foldl]
    have := ih (h ⬝ v)
    exact (Sub.left v (.refl h)).trans this

theorem sub_foldl_arg {v : Term} : ∀ {vs : List Term} (h : Term), v ∈ vs → Sub v (vs.foldl Term.app h)
  | [], _, hm => by simp at hm
  | w :: ws, h, hm => by
    simp only [List.foldl]
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (Sub.right h (.refl v)).trans (sub_foldl_head _ ws)
    · exact sub_foldl_arg (h ⬝ w) hm

/-! ## Closing rules -/

theorem hasBot_sound {sz : Sz} : ∀ {t : RT} {u : Term}, InstR sz t u → t.hasBot = true →
    ∃ s, Sub s u ∧ fold s = 36
  | .S, _, _, hb => by simp [RT.hasBot] at hb
  | .V _ _, u, h, hb => by
    simp only [RT.hasBot, beq_iff_eq] at hb
    refine ⟨u, .refl u, ?_⟩
    rw [← pst_mod h.1, h.2.1]; exact hb
  | .A l r s, _, ⟨a, b, rfl, ha, hb', hs⟩, hb => by
    simp only [RT.hasBot, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with (h36 | hl) | hr
    · refine ⟨a ⬝ b, .refl _, ?_⟩
      rw [← pst_mod (.app ha.pure hb'.pure), ← hs]; exact h36
    · obtain ⟨s', h1, h2⟩ := hasBot_sound ha hl; exact ⟨s', .left b h1, h2⟩
    · obtain ⟨s', h1, h2⟩ := hasBot_sound hb' hr; exact ⟨s', .right a h1, h2⟩

theorem gen_sound {sz : Sz} : ∀ {t : RT} {u : Term}, InstR sz t u → Inst t.gen u
  | .S, _, h => h
  | .V _ _, u, h => by simp only [RT.gen]; rw [← h.2.1]; exact inst_mkV h.1
  | .A l r s, _, ⟨a, b, rfl, ha, hb, hs⟩ => by
    simp only [RT.gen]
    split
    · rw [hs]; exact inst_mkV (.app ha.pure hb.pure)
    · exact ⟨a, b, rfl, gen_sound ha, gen_sound hb⟩

theorem find_sub : ∀ (T : CBST) (k : Nat) {d : Claim}, d ∈ T.find k → d ∈ T.toList
  | .leaf, _, _, h => by simp [CBST.find] at h
  | .node k' items l r, k, d, h => by
    simp only [CBST.find] at h
    simp only [CBST.toList, List.mem_append]
    split at h
    · exact .inl (.inr h)
    · split at h
      · exact .inl (.inl (find_sub l k h))
      · exact .inr (find_sub r k h)

theorem lookup_sound {t : CT} {d : Claim} (h : d ∈ lookup t) : d ∈ CLAIMS ∧ d.term = t := by
  simp only [lookup, List.mem_filter, beq_iff_eq] at h
  exact ⟨find_sub _ _ h.1, h.2⟩

/-! ## Grades -/

structure MinsLe (mins sz : Sz) : Prop where
  h0 : mins.s0 ≤ sz.s0
  h1 : mins.s1 ≤ sz.s1
  h2 : mins.s2 ≤ sz.s2
  h3 : mins.s3 ≤ sz.s3
  h4 : mins.s4 ≤ sz.s4

theorem grade_sound {f : Option Form} {root : Form} {mins sz : Sz} (hm : MinsLe mins sz) :
    (grade f root mins = 2 → ∃ g, f = some g ∧ g.eval sz ≤ root.eval sz - 1) ∧
    (grade f root mins = 1 → ∃ g, f = some g ∧ g.eval sz ≤ root.eval sz) := by
  cases f with
  | none => simp [grade]
  | some g =>
    simp only [grade]
    split
    · simp
    · rename_i hneg
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at hneg
      obtain ⟨⟨⟨⟨d0, d1⟩, d2⟩, d3⟩, d4⟩ := hneg
      have p0 := Int.mul_le_mul_of_nonneg_left hm.h0 (Int.sub_nonneg.mpr d0)
      have p1 := Int.mul_le_mul_of_nonneg_left hm.h1 (Int.sub_nonneg.mpr d1)
      have p2 := Int.mul_le_mul_of_nonneg_left hm.h2 (Int.sub_nonneg.mpr d2)
      have p3 := Int.mul_le_mul_of_nonneg_left hm.h3 (Int.sub_nonneg.mpr d3)
      have p4 := Int.mul_le_mul_of_nonneg_left hm.h4 (Int.sub_nonneg.mpr d4)
      simp only [Form.eval, Int.sub_mul] at p0 p1 p2 p3 p4 ⊢
      constructor
      · intro h2; refine ⟨g, rfl, ?_⟩
        split at h2
        · rename_i hmn; omega
        · split at h2 <;> simp at h2
      · intro h1; refine ⟨g, rfl, ?_⟩
        split at h1
        · simp at h1
        · split at h1
          · rename_i _ hmn; omega
          · simp at h1

end HnfCert
