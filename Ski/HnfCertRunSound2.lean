import Ski.HnfCertRunSound
open Term

namespace HnfCert
open HnfS HnfSound HnfProd HnfCertLaws HnfB0 HnfQ5

/-- What a run of a claim may assume: the root form is the root size `N`, the minimum sizes are
lower bounds, and every claim lower in (stratum, size, rank) holds. -/
structure RunEnv (cx : Ctx) (sz : Sz) (N : Nat) : Prop where
  root : cx.root.eval sz = N
  mins : MinsLe cx.mins sz
  ih : ∀ d ∈ CLAIMS, ∀ v, Inst d.term v →
    (d.stratum < cx.stratum ∨ (d.stratum = cx.stratum ∧ (tsz v < N ∨ (tsz v = N ∧ d.rank < cx.rank)))) →
    ¬ Prod v

variable {cx : Ctx} {sz : Sz} {N : Nat}

theorem claimOK_sound (E : RunEnv cx sz N) {ct : CT} {v : Term} {fa : Option Form}
    (h : claimOK cx (grade fa cx.root cx.mins) ct = true) (hv : Inst ct v)
    (hb : ∀ g, fa = some g → (tsz v : Int) ≤ g.eval sz) : ¬ Prod v := by
  simp only [claimOK, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq] at h
  obtain ⟨d, hd, hc⟩ := h
  obtain ⟨hdc, hdt⟩ := lookup_sound hd
  have hv' : Inst d.term v := hdt ▸ hv
  have gs := grade_sound (f := fa) (root := cx.root) E.mins
  rcases hc with hlt | ⟨heq, h2 | ⟨h1, hr⟩⟩
  · exact E.ih d hdc v hv' (.inl hlt)
  · obtain ⟨g, rfl, hg⟩ := gs.1 h2
    have := hb g rfl; rw [E.root] at hg
    exact E.ih d hdc v hv' (.inr ⟨heq, .inl (by omega)⟩)
  · obtain ⟨g, rfl, hg⟩ := gs.2 h1
    have := hb g rfl; rw [E.root] at hg
    by_cases hlt : tsz v < N
    · exact E.ih d hdc v hv' (.inr ⟨heq, .inl hlt⟩)
    · exact E.ih d hdc v hv' (.inr ⟨heq, .inr ⟨by omega, hr⟩⟩)

theorem pairClose_sound (E : RunEnv cx sz N) : ∀ {t : RT} {u : Term},
    pairClose cx t = true → InstR sz t u → ¬ Prod u
  | .S, _, h, _ => by simp [pairClose] at h
  | .V _ _, _, h, _ => by simp [pairClose] at h
  | .A l r s, _, h, ⟨a, b, rfl, ha, hb, hs⟩ => by
    simp only [pairClose] at h
    split at h
    · simp at h
    · split at h
      · rename_i _ hacc
        simp only [List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
          beq_iff_eq] at h
        obtain ⟨d, hd, hc⟩ := h
        obtain ⟨hdc, hdt⟩ := lookup_sound hd
        have hv : Inst d.term (a ⬝ b) := by
          rw [hdt, ha.st, hb.st]; exact ⟨a, b, rfl, inst_mkV ha.pure, inst_mkV hb.pure⟩
        rcases hc with hlt | ⟨heq, h2⟩
        · exact E.ih d hdc _ hv (.inl hlt)
        · obtain ⟨g, hg, hle⟩ := (grade_sound (f := oadd l.sz r.sz) (root := cx.root) E.mins).1 h2
          have hbd : (tsz (a ⬝ b) : Int) ≤ g.eval sz := sz_bound (t := .A l r s) ⟨a, b, rfl, ha, hb, hs⟩ hg
          rw [E.root] at hle
          exact E.ih d hdc _ hv (.inr ⟨heq, .inl (by omega)⟩)
      · simp only [Bool.or_eq_true] at h
        have hp : PureS (a ⬝ b) := .app ha.pure hb.pure
        rcases h with hl | hr
        · exact np_of_sub hp (.left b (.refl a)) (pairClose_sound E hl ha)
        · exact np_of_sub hp (.right a (.refl b)) (pairClose_sound E hr hb)

/-! ## Head steps, unfolds, descents -/

theorem F2.inv3 {R : RT → Term → Prop} {x y z : RT} {rest : List RT} {vs : List Term}
    (h : F2 R (x :: y :: z :: rest) vs) :
    ∃ vx vy vz vrest, vs = vx :: vy :: vz :: vrest ∧ R x vx ∧ R y vy ∧ R z vz ∧ F2 R rest vrest := by
  cases h with
  | cons hx h => cases h with
    | cons hy h => cases h with
      | cons hz h => exact ⟨_, _, _, _, rfl, hx, hy, hz, h⟩

theorem step_inst {t : RT} {u : Term} {x y z : RT} {rest : List RT} (hu : InstR sz t u)
    (hsp : t.spine = (.S, x :: y :: z :: rest)) :
    ∃ u', InstR sz (build x (z :: mkA y z :: rest)) u' ∧ WSteps u u' := by
  obtain ⟨hd, vs, rfl, hh, hvs⟩ := spine_inst hu
  rw [hsp] at hh hvs
  simp only [InstR] at hh; subst hh
  obtain ⟨vx, vy, vz, vrest, rfl, hx, hy, hz, hrest⟩ := F2.inv3 hvs
  refine ⟨vrest.foldl Term.app (vx ⬝ vz ⬝ (vy ⬝ vz)), ?_, ?_⟩
  · have := build_inst (z :: mkA y z :: rest) (vz :: (vy ⬝ vz) :: vrest) hx
      (.cons hz (.cons (mkA_inst hy hz) hrest))
    simpa [List.foldl] using this
  · simp only [List.foldl]
    exact .single (wstep_foldl (.S vx vy vz) vrest)

theorem arg_inst {t : RT} {u : Term} {args : List RT} {i : Nat} {a : RT} (hu : InstR sz t u)
    (hsp : t.spine = (.S, args)) (hi : args[i]? = some a) : ∃ va, InstR sz a va ∧ Sub va u := by
  obtain ⟨hd, vs, rfl, hh, hvs⟩ := spine_inst hu
  rw [hsp] at hvs
  obtain ⟨v, _, hR, hm⟩ := F2.get hvs hi
  exact ⟨v, hR, sub_foldl_arg hd hm⟩

theorem cls_args {f x : Term} (hf : PureS f) (hx : PureS x) (h : cls (f ⬝ x) ≠ 37) :
    cls f ≠ 37 ∧ cls x ≠ 37 := by
  constructor
  · intro h37; apply h; simp only [cls, h37]; exact absorbL (cls_lt hx)
  · intro h37; apply h; simp only [cls, h37]; exact absorbR (cls_lt hf)

theorem eq_SS {a : Term} (ha : PureS a) (h : tsz a = 2) : a = S ⬝ S := by
  cases ha with
  | S => simp [tsz] at h
  | app hf hx =>
    rename_i f x
    have h1 := tsz_pos f; have h2 := tsz_pos x
    simp only [tsz] at h
    cases hf with
    | S => cases hx with
      | S => rfl
      | app _ _ => rename_i g y _ _; have := tsz_pos g; have := tsz_pos y; simp [tsz] at h; omega
    | app _ _ => rename_i g y _ _; have := tsz_pos g; have := tsz_pos y; simp [tsz] at h; omega

theorem exact1 : exactB 1 = some 2 := by decide +kernel

theorem unfold_inst (hSh : ShapesOK) {t : RT} {u : Term} {s : Nat} {f : Option Form} {args : List RT}
    (hu : InstR sz t u) (hsp : t.spine = (.V s f, args)) (hacc : accN s = true) :
    ∃ sh ∈ unf s, ∃ u', InstR sz (build (shapeTerm f sh) args) u' ∧ WSteps u u' := by
  obtain ⟨hd, vs, rfl, hh, hvs⟩ := spine_inst hu
  rw [hsp] at hh hvs
  obtain ⟨hp, hps, hfb⟩ := hh
  have hc : cls hd ≠ 37 := (accN_pst hp).mp (hps ▸ hacc)
  obtain ⟨h, hch, hl, hisH⟩ := sound_head hd hp (HnfProd.b1 hp hc)
  have hw := headChain_wsteps hch hp
  have hph := (HnfS.fold_wsteps hw hp).1
  have hpst : pst h = s := (pst_wsteps hw hp).trans hps
  have hch' : cls h ≠ 37 := by rw [wsteps_cls hw hp]; exact hc
  have hww : WSteps (vs.foldl Term.app hd) (vs.foldl Term.app h) := wsteps_foldl hw vs
  rcases hisH with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · refine ⟨.s0, ?_, _, build_inst args vs (rfl : InstR sz .S S) hvs, hww⟩
    rw [← hpst]; exact unf_s0
  · have ha := hph.app_inv.2
    have hca := (cls_args .S ha hch').2
    have hs1 : dxN 0 (pst a) = s := by rw [← hpst, pst_app .S ha]; rfl
    refine ⟨.s1 (pst a), hs1 ▸ unf_s1 (pst_accs ha hca), _, build_inst args vs ?_ hvs, hww⟩
    simp only [shapeTerm]
    refine mkA_inst (rfl : InstR sz .S S) (mkVR_inst ha rfl ?_)
    intro g hg
    cases hv : exactB (pst a % 64) with
    | some v =>
      simp only [hv, Option.some.injEq] at hg; subst hg; rw [eval_const]
      rw [pst_mod ha] at hv; rw [exact_size ha hv]; exact Int.le_refl _
    | none =>
      cases hf : f with
      | none => simp [hv, hf] at hg
      | some g0 =>
        simp only [hv, hf, Option.map_some, Option.some.injEq] at hg; subst hg
        rw [eval_shift]
        have hb := hfb g0 hf
        have := L0 hch (by simp [spine])
        subst this; simp only [tsz] at hb; omega
  · have hab := hph.app_inv
    have ha := hab.1.app_inv.2; have hb := hab.2
    have hc2 := cls_args hab.1 hb hch'
    have hca := (cls_args .S ha hc2.1).2
    have hs2 : dxN (dxN 0 (pst a)) (pst b) = s := by
      rw [← hpst, pst_app hab.1 hb, pst_app .S ha]; rfl
    refine ⟨.s2 (pst a) (pst b), hs2 ▸ unf_s2 hSh (pst_accs ha hca) (pst_accs hb hc2.2), _,
      build_inst args vs ?_ hvs, hww⟩
    simp only [shapeTerm]
    refine mkA_inst (mkA_inst (rfl : InstR sz .S S) (mkVR_inst ha rfl ?_)) (mkVR_inst hb rfl ?_)
    · intro g hg
      cases hv : exactB (pst a % 64) with
      | none => simp [hv] at hg
      | some v =>
        simp only [hv, Option.map_some, Option.some.injEq] at hg; subst hg; rw [eval_const]
        rw [pst_mod ha] at hv; rw [exact_size ha hv]; exact Int.le_refl _
    · intro g hg
      cases hv : exactB (pst b % 64) with
      | some v =>
        simp only [hv, Option.some.injEq] at hg; subst hg; rw [eval_const]
        rw [pst_mod hb] at hv; rw [exact_size hb hv]; exact Int.le_refl _
      | none =>
        simp only [hv] at hg
        split at hg
        · rename_i hblk
          cases hf : f with
          | none => simp [hf] at hg
          | some g0 =>
            simp only [hf, Option.map_some, Option.some.injEq] at hg; subst hg
            rw [eval_shift]
            have hbd := hfb g0 hf
            simp only [Bool.or_eq_true, beq_iff_eq] at hblk
            rw [pst_mod ha] at hblk
            rcases hblk with h0 | h1
            · have := fold_eq_zero ha h0; subst this
              have := L1 hch; omega
            · have h2 : tsz a = 2 := exact_size ha (by rw [h1]; exact exact1)
              have := eq_SS ha h2; subst this
              have := LA hch; omega
        · simp at hg

/-! ## The run -/

theorem foldl_bind_none {α : Type} (l : List α) (F : α → List Nat → Option (List Nat)) :
    l.foldl (fun acc sh => acc.bind fun hs => F sh hs) none = none := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simpa using ih

theorem foldl_bind_mem {α : Type} (F : α → List Nat → Option (List Nat)) : ∀ (l : List α) (init : Option (List Nat))
    (r : List Nat), l.foldl (fun acc sh => acc.bind fun hs => F sh hs) init = some r →
    ∀ x ∈ l, ∃ a b, F x a = some b
  | [], _, _, _, x, hx => by simp at hx
  | y :: ys, init, r, h, x, hx => by
    simp only [List.foldl] at h
    cases hi : init with
    | none => rw [hi] at h; simp only [Option.bind_none] at h; rw [foldl_bind_none] at h; cases h
    | some i =>
      rw [hi] at h; simp only [Option.bind_some] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · cases hF : F x i with
        | none => rw [hF] at h; rw [foldl_bind_none] at h; cases h
        | some b => exact ⟨i, b, hF⟩
      · exact foldl_bind_mem F ys _ r h x hx

theorem hnf_sound (E : RunEnv cx sz N) {rec : Nat → RT → List Nat → Option (List Nat)}
    (hrec : ∀ dl a hs hs', rec dl a hs = some hs' → ∀ v, InstR sz a v → ¬ Prod v)
    {t : RT} {u : Term} {args : List RT} (hu : InstR sz t u) (hsp : t.spine = (.S, args))
    {dl : Nat} {hs hs' : List Nat} (h : hnfStep cx rec dl args hs = some hs') : ¬ Prod u := by
  cases hs with
  | nil => simp [hnfStep] at h
  | cons hh hs1 =>
    simp only [hnfStep] at h
    split at h
    · cases h
    · rename_i a hi
      obtain ⟨va, hva, hsub⟩ := arg_inst hu hsp hi
      have hrej : ¬ Prod va → ¬ Prod u := np_of_sub hu.pure hsub
      split at h
      · cases h
      · split at h
        · split at h
          · rename_i hok
            exact hrej (claimOK_sound E hok (gen_sound hva) (fun g hg => sz_bound hva hg))
          · cases h
        · split at h
          · exact hrej (hrec _ a hs1 hs' h va hva)
          · cases h

theorem run_sound (E : RunEnv cx sz N) (hSh : ShapesOK) :
    ∀ (fuel dl : Nat) (t : RT) (hs hs' : List Nat), run cx fuel dl t hs = some hs' →
      ∀ u, InstR sz t u → ¬ Prod u := by
  intro fuel
  induction fuel with
  | zero => intro dl t hs hs' h; simp [run] at h
  | succ fuel ih =>
    intro dl t hs hs' hrun u hu
    simp only [run] at hrun
    split at hrun
    · rename_i hb
      obtain ⟨s, h1, h2⟩ := hasBot_sound hu hb
      obtain ⟨k, hk⟩ := B0 hu.pure h1 h2
      exact fun hP => hk (hP k)
    split at hrun
    · rename_i hpc; exact pairClose_sound E hpc hu
    generalize hsp : t.spine = p at hrun
    obtain ⟨hd, args⟩ := p
    cases hd with
    | S =>
      match args, hsp, hrun with
      | x :: y :: z :: rest, hsp, hrun =>
        obtain ⟨u', hu', hw⟩ := step_inst hu hsp
        exact np_of_wsteps hu.pure hw (ih dl _ hs hs' hrun u' hu')
      | [], hsp, hrun => exact hnf_sound E (fun dl a hs hs' h v hv => ih dl a hs hs' h v hv) hu hsp hrun
      | [x], hsp, hrun => exact hnf_sound E (fun dl a hs hs' h v hv => ih dl a hs hs' h v hv) hu hsp hrun
      | [x, y], hsp, hrun => exact hnf_sound E (fun dl a hs hs' h v hv => ih dl a hs hs' h v hv) hu hsp hrun
    | V s f =>
      match args, hsp, hrun with
      | [], _, hrun => cases hrun
      | a :: as, hsp, hrun =>
        simp only at hrun
        split at hrun
        · rename_i hacc
          obtain ⟨sh, hsh, u', hu', hw⟩ := unfold_inst hSh hu hsp hacc
          obtain ⟨a1, b1, hab⟩ := foldl_bind_mem
            (fun sh hs => run cx fuel dl (build (shapeTerm f sh) (a :: as)) hs) (unf s) (some hs) hs' hrun sh hsh
          exact np_of_wsteps hu.pure hw (ih dl _ a1 b1 hab u' hu')
        · cases hrun
    | A l r s' => cases hrun

end HnfCert
