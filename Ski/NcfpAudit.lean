import Lean
import Ski.Ncfp
import Ski.NcfpTheta
import Ski.NcfpLeafless
import Ski.NcfpN
import Ski.NcfpN2
import Ski.NcfpDepth2
import Ski.NcfpScheme
import Ski.NcfpThree
import Ski.NcfpXplus
import Ski.NcfpN12
import Ski.NcfpPlain

/-!
# Axiom gate for the proved cases of NCFP (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.Ncfp`, `Ski.NcfpTheta`, `Ski.NcfpLeafless`, `Ski.NcfpN`, `Ski.NcfpN2`, `Ski.NcfpDepth2`, `Ski.NcfpScheme`, `Ski.NcfpThree`, `Ski.NcfpXplus`, `Ski.NcfpN12` and `Ski.NcfpPlain`.

* `#ncfp_audit_module M` checks every theorem, and every definition without an internal name,
  declared in the module `M`, and reports the counts and the internal constants it skips
  (compiler and elaborator auxiliaries, which are programs and not proofs).
* `#ncfp_audit_clean ids` checks the named constants.
-/

open Lean Elab Command

namespace Ncfp.Audit

def allowed : List Name := [``propext, ``Quot.sound]

def check (n : Name) : CommandElabM Unit := do
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

elab "#ncfp_audit_clean " ids:ident+ : command => do
  for id in ids do
    check (← liftCoreM <| realizeGlobalConstNoOverload id)

elab "#ncfp_audit_module " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "module {m.getId} not found"
  let mut count : Nat := 0
  let mut thms : Nat := 0
  let mut skipped : Array Name := #[]
  for n in env.header.moduleData[idx.toNat]!.constNames do
    let isThm := match env.find? n with
      | some (.thmInfo _) => true
      | _ => false
    if isThm || !n.isInternal then
      check n
      count := count + 1
      if isThm then thms := thms + 1
    else
      skipped := skipped.push n
  logInfo m!"ncfp audit: {count} constants ({thms} theorems) in {m.getId}: axioms ⊆ {allowed}; skipped (internal, not theorems): {skipped}"

end Ncfp.Audit

#ncfp_audit_module Ski.Ncfp
#ncfp_audit_module Ski.NcfpTheta
#ncfp_audit_module Ski.NcfpLeafless
#ncfp_audit_module Ski.NcfpN
#ncfp_audit_module Ski.NcfpN2
#ncfp_audit_module Ski.NcfpDepth2
#ncfp_audit_module Ski.NcfpScheme
#ncfp_audit_module Ski.NcfpThree
#ncfp_audit_module Ski.NcfpXplus
#ncfp_audit_module Ski.NcfpN12
#ncfp_audit_module Ski.NcfpPlain

-- size, normal forms, contexts; Prop. 0
#ncfp_audit_clean Ncfp.sz_wstep Ncfp.sz_wsteps Ncfp.Normal.wsteps Ncfp.wsteps_to_normal
#ncfp_audit_clean Ncfp.wsteps_plug Ncfp.Holed.sz_le Ncfp.Holed.sz_lt Ncfp.prop0
-- head runs: Lemma L
#ncfp_audit_clean Ncfp.step_app Ncfp.plus_last Ncfp.hnf1_literal Ncfp.lemma_L Ncfp.lemma_L'
#ncfp_audit_clean Ncfp.last_item_step Ncfp.link
-- SS-chains
#ncfp_audit_clean Ncfp.ss_link Ncfp.SSPath.snoc Ncfp.sspath_strip Ncfp.ss_bound
-- descendants
#ncfp_audit_clean Ncfp.sub_sz_le Ncfp.PSub.sub Ncfp.PSub.sz_lt Ncfp.sub_psub Ncfp.sub_wsteps
#ncfp_audit_clean Ncfp.psub_wsteps Ncfp.Desc.trans Ncfp.Desc.irrefl Ncfp.Next.desc
-- Theorem 2
#ncfp_audit_clean Ncfp.nonlit_exists Ncfp.run_inner Ncfp.run Ncfp.small_desc Ncfp.enum
#ncfp_audit_clean Ncfp.mem_enum Ncfp.right_combs Ncfp.right_combs_seq Ncfp.right_combs_conv
-- comb contexts, no fixed-point combinator
#ncfp_audit_clean Ncfp.CombB.mono Ncfp.Comb.bound Ncfp.ncfp_comb Ncfp.ncfp_S_aux Ncfp.ncfp_S
#ncfp_audit_clean Ncfp.ncfp_S_comb Ncfp.no_fixed_point_combinator Ncfp.no_fpc

-- Theorem F; Theorem G, Lemma P, Corollary G1; Theorem B, Lemma T, Lemma A, the Moves, Corollary B1
#ncfp_audit_clean Ncfp.finite_descent Ncfp.desc_finite Ncfp.NextF.desc Ncfp.small_descF Ncfp.first_combs Ncfp.first_combs_seq
#ncfp_audit_clean Ncfp.lemma_P Ncfp.no_pred Ncfp.Rigid.sub Ncfp.Rigid.sz_lt Ncfp.Rigid.not_appS Ncfp.sspath_rigid Ncfp.NextG.desc Ncfp.runG_inner
#ncfp_audit_clean Ncfp.runG Ncfp.small_descG Ncfp.mixed_combs Ncfp.mixed_combs_seq Ncfp.mixed_combs_conv Ncfp.GCombB.mono Ncfp.GComb.bound Ncfp.Comb.gcomb
#ncfp_audit_clean Ncfp.ncfp_gcomb Ncfp.steps_antisymm Ncfp.bot_app Ncfp.firstStable_exists Ncfp.lemma_T Ncfp.lemma_A Ncfp.stepsK_of_steps
#ncfp_audit_clean Ncfp.stepsK_later Ncfp.steps_step_plus Ncfp.stepsK_plus Ncfp.past_root Ncfp.bmove Ncfp.step_apps Ncfp.plus_apps Ncfp.apps_append
#ncfp_audit_clean Ncfp.hdesc_of_steps Ncfp.HDesc.trans Ncfp.HDesc.irrefl Ncfp.tooth_descent Ncfp.teeth_unbounded Ncfp.teeth_unbounded_seq Ncfp.fold_apps Ncfp.pure_apps_of
#ncfp_audit_clean Ncfp.snoc_cases Ncfp.norm_bound Ncfp.fold_conv Ncfp.cor_B1 Ncfp.cor_B1'

#ncfp_audit_clean Ncfp.del Ncfp.mem_del Ncfp.del_length_le Ncfp.del_length_lt

-- NcfpTheta: Lemmas TD, SS, ZA, NH, ZI; Theorems Θ, Θ′, Θ″; Corollary Θ1
#ncfp_audit_clean Ncfp.lemma_TD Ncfp.sz_appS Ncfp.lemma_SS Ncfp.lemma_SS_sz Ncfp.cor_SS1 Ncfp.stepsK_steps Ncfp.pure_args Ncfp.step_apps_inv
#ncfp_audit_clean Ncfp.track_step Ncfp.apps_app_ne_S Ncfp.apps_eq_S1 Ncfp.apps_eq_S2 Ncfp.frame3_item Ncfp.GoodHnf.isHnf Ncfp.lemma_NH Ncfp.Leafless.fold_ne
#ncfp_audit_clean Ncfp.WZ.pure Ncfp.wz_step Ncfp.wz_no_hnf Ncfp.wz_bot Ncfp.lemma_ZA_two Ncfp.lemma_ZA_one Ncfp.track_run Ncfp.lemma_ZI_i
#ncfp_audit_clean Ncfp.IsItem.apps Ncfp.ItemSub.psub Ncfp.itemsub_step Ncfp.lemma_ZI_ii Ncfp.ThetaSet.leafless Ncfp.ThetaSet.k2 Ncfp.ThetaSet.not_S Ncfp.theta_chain
#ncfp_audit_clean Ncfp.theta_aux Ncfp.theta Ncfp.hnf1_conv Ncfp.hnf2_conv Ncfp.ncfp_two Ncfp.no_S_p_p Ncfp.thetap_td Ncfp.theta'
#ncfp_audit_clean Ncfp.no_S_p_Sp Ncfp.no_SSS_p Ncfp.theta'' Ncfp.no_S_Sp_p

-- NcfpLeafless: Fact LI, Lemma PR, Theorem L, Corollary L1
#ncfp_audit_clean Ncfp.em_false Ncfp.fact_LI Ncfp.spine_fun Ncfp.spine_conv Ncfp.Leafless.not_S Ncfp.sz_Sj_ge Ncfp.IsItem.itemsub Ncfp.pr_members
#ncfp_audit_clean Ncfp.pr_one Ncfp.leafless_chain Ncfp.lemma_PR Ncfp.thm_L_bounded Ncfp.spine_bound Ncfp.thm_L Ncfp.SubC.trans Ncfp.subs_self
#ncfp_audit_clean Ncfp.SubC.mem Ncfp.HCtx.hole_sub Ncfp.ncfp_holes

-- NcfpN: Lemma LL, Corollary LL1, Theorems N1, N2
#ncfp_audit_clean Ncfp.wrap_S Ncfp.lemma_LL Ncfp.cor_LL1 Ncfp.progress_bot Ncfp.claim_D Ncfp.claim_E Ncfp.thm_N1 Ncfp.no_S_SSp_p
#ncfp_audit_clean Ncfp.normal_S Ncfp.Normal.app_inv Ncfp.normalizing_S1 Ncfp.finite_descent_nn Ncfp.n2_not_norm Ncfp.n2_td Ncfp.thm_N2 Ncfp.no_S_p_Snp

-- NcfpN2: Theorem 2', Theorems N3, N4, N5
#ncfp_audit_clean Ncfp.Next'.desc Ncfp.nonlit_exists' Ncfp.run_inner' Ncfp.run' Ncfp.small_desc' Ncfp.right_combs' Ncfp.not_norm_gen Ncfp.not_normalizing
#ncfp_audit_clean Ncfp.thm_N5 Ncfp.hnf2_conv_right Ncfp.hnf2_conv_left Ncfp.no_S_p_Spn Ncfp.thm_N4 Ncfp.no_S_Spn_p Ncfp.claim_D'_frames Ncfp.thm_N3
#ncfp_audit_clean Ncfp.no_S_Snp_p

-- NcfpDepth2: Lemma SR, Lemma D*, Theorem G', Theorem X, Lemma LC
#ncfp_audit_clean Ncfp.lemma_SR Ncfp.dstar_frames Ncfp.lemma_Dstar Ncfp.NextG'.desc Ncfp.runG_inner' Ncfp.runG' Ncfp.small_descG' Ncfp.mixed_combs'
#ncfp_audit_clean Ncfp.thm_X Ncfp.lemma_LC
-- NcfpScheme: Theorem T at distance 0, N6-N10 equations, Theorem N11
#ncfp_audit_clean Ncfp.typed_nn Ncfp.typed_not_normalizing Ncfp.slot_mism Ncfp.typed_apart Ncfp.thm_T0 Ncfp.slotok_cls Ncfp.slotok_nf Ncfp.tyok_one
#ncfp_audit_clean Ncfp.tyok_two Ncfp.typed_of_reps Ncfp.ncfp_scheme Ncfp.no_S_Spp_n Ncfp.no_S_n_Spp Ncfp.no_S_Sp_Snp Ncfp.no_S_Snp_Spm Ncfp.no_S_Sp_Spn
#ncfp_audit_clean Ncfp.no_S_Snp_Sp Ncfp.no_S_Spn_Sp Ncfp.no_S_Snp_Smp Ncfp.no_S_Spn_Smp Ncfp.no_S_Spn_Spm Ncfp.thm_N11 Ncfp.no_S_SpSp_n

-- NcfpThree: the four three-hole shapes of depth 2
#ncfp_audit_clean Ncfp.nonlit_form Ncfp.big_ne_S Ncfp.three_X Ncfp.thm_T3a Ncfp.thm_T3b Ncfp.thm_T3d Ncfp.thm_T3c Ncfp.no_S_Spp_Snp
#ncfp_audit_clean Ncfp.no_S_Spp_Spn Ncfp.no_S_Snp_Spp Ncfp.no_S_Spn_Spp

#print axioms Ncfp.prop0
#print axioms Ncfp.lemma_L
#print axioms Ncfp.ss_bound
#print axioms Ncfp.right_combs
#print axioms Ncfp.right_combs_seq
#print axioms Ncfp.right_combs_conv
#print axioms Ncfp.ncfp_comb
#print axioms Ncfp.ncfp_S
#print axioms Ncfp.ncfp_S_comb
#print axioms Ncfp.no_fixed_point_combinator
#print axioms Ncfp.no_fpc
#print axioms Ncfp.first_combs
#print axioms Ncfp.first_combs_seq
#print axioms Ncfp.lemma_P
#print axioms Ncfp.mixed_combs
#print axioms Ncfp.mixed_combs_seq
#print axioms Ncfp.mixed_combs_conv
#print axioms Ncfp.ncfp_gcomb
#print axioms Ncfp.lemma_T
#print axioms Ncfp.bmove
#print axioms Ncfp.teeth_unbounded
#print axioms Ncfp.teeth_unbounded_seq
#print axioms Ncfp.cor_B1
#print axioms Ncfp.lemma_TD
#print axioms Ncfp.lemma_SS
#print axioms Ncfp.cor_SS1
#print axioms Ncfp.lemma_ZA_two
#print axioms Ncfp.lemma_ZA_one
#print axioms Ncfp.lemma_NH
#print axioms Ncfp.lemma_ZI_i
#print axioms Ncfp.lemma_ZI_ii
#print axioms Ncfp.theta
#print axioms Ncfp.ncfp_two
#print axioms Ncfp.no_S_p_p
#print axioms Ncfp.theta'
#print axioms Ncfp.no_S_p_Sp
#print axioms Ncfp.no_SSS_p
#print axioms Ncfp.theta''
#print axioms Ncfp.no_S_Sp_p
#print axioms Ncfp.em_false
#print axioms Ncfp.fact_LI
#print axioms Ncfp.pr_members
#print axioms Ncfp.lemma_PR
#print axioms Ncfp.thm_L_bounded
#print axioms Ncfp.spine_bound
#print axioms Ncfp.thm_L
#print axioms Ncfp.ncfp_holes
#print axioms Ncfp.lemma_LL
#print axioms Ncfp.cor_LL1
#print axioms Ncfp.claim_D
#print axioms Ncfp.thm_N1
#print axioms Ncfp.no_S_SSp_p
#print axioms Ncfp.thm_N2
#print axioms Ncfp.no_S_p_Snp
#print axioms Ncfp.right_combs'
#print axioms Ncfp.claim_D'_frames
#print axioms Ncfp.thm_N3
#print axioms Ncfp.no_S_Snp_p
#print axioms Ncfp.thm_N4
#print axioms Ncfp.no_S_Spn_p
#print axioms Ncfp.thm_N5
#print axioms Ncfp.no_S_p_Spn
#print axioms Ncfp.lemma_SR
#print axioms Ncfp.lemma_Dstar
#print axioms Ncfp.mixed_combs'
#print axioms Ncfp.thm_X
#print axioms Ncfp.lemma_LC
#print axioms Ncfp.thm_T0
#print axioms Ncfp.ncfp_scheme
#print axioms Ncfp.no_S_Spp_n
#print axioms Ncfp.no_S_n_Spp
#print axioms Ncfp.no_S_Sp_Snp
#print axioms Ncfp.no_S_Snp_Spm
#print axioms Ncfp.no_S_Sp_Spn
#print axioms Ncfp.no_S_Snp_Sp
#print axioms Ncfp.no_S_Spn_Sp
#print axioms Ncfp.no_S_Snp_Smp
#print axioms Ncfp.no_S_Spn_Smp
#print axioms Ncfp.no_S_Spn_Spm
#print axioms Ncfp.thm_N11
#print axioms Ncfp.no_S_SpSp_n
#print axioms Ncfp.thm_T3a
#print axioms Ncfp.thm_T3b
#print axioms Ncfp.thm_T3c
#print axioms Ncfp.thm_T3d
#print axioms Ncfp.no_S_Spp_Snp
#print axioms Ncfp.no_S_Spp_Spn
#print axioms Ncfp.no_S_Snp_Spp
#print axioms Ncfp.no_S_Spn_Spp
#print axioms Ncfp.thm_Xplus
#print axioms Ncfp.thm_X_of_Xplus
#print axioms Ncfp.cor_X1
#print axioms Ncfp.ncfp_X1
#print axioms Ncfp.no_S_SpSnp
#print axioms Ncfp.no_S_Sp_SnSp
#print axioms Ncfp.no_S_n_SpSp
#print axioms Ncfp.no_S_Snp_SSmp
#print axioms Ncfp.no_S_SpSnp_m
#print axioms Ncfp.no_S_Spn_SSpm
#print axioms Ncfp.no_S_n_SpSmp
#print axioms Ncfp.no_S_Snp_SmSkp
#print axioms Ncfp.no_S_Spn_SmSpk
#print axioms Ncfp.lemma_Dstar_add
#print axioms Ncfp.lemma_AP1
#print axioms Ncfp.lemma_AP2
#print axioms Ncfp.lemma_AP3
#print axioms Ncfp.lemma_AP4
#print axioms Ncfp.lemma_PF
#print axioms Ncfp.claim_P
#print axioms Ncfp.thm_N12_1
#print axioms Ncfp.thm_N12_2
#print axioms Ncfp.thm_N12_3
#print axioms Ncfp.thm_N12_4
#print axioms Ncfp.thm_N12_5
#print axioms Ncfp.thm_N12_6
#print axioms Ncfp.thm_N12_7
#print axioms Ncfp.thm_N12_8
#print axioms Ncfp.no_S_SSnpp_p
#print axioms Ncfp.no_S_SSpnp_p
#print axioms Ncfp.no_S_SSnpSp_p
#print axioms Ncfp.no_S_SSpnSp_p
#print axioms Ncfp.no_S_SSpSnp_p
#print axioms Ncfp.no_S_SSpSpn_p
#print axioms Ncfp.no_S_SpSnp_p
#print axioms Ncfp.no_S_SpSpn_p
#print axioms Ncfp.ncfp_depth2
