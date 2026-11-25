import Lean
import Ski.S11Closure
import Ski.S11Teeth
import Ski.S11Run
import Ski.S11Second
import Ski.S11Main

/-!
# Axiom gate for the S11 mechanization (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only the S11 modules.  The root module `Ski` imports this module, so the
default `lake build` runs the gate (as for `ConvAudit` and `NcfpAudit`).
-/

open Lean Elab Command

namespace S11.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#s11_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end S11.Audit

-- M1a: S11Base (families, head runs (1)–(3), block facts, Lemma 6(b) by blocks)
#s11_audit_clean
  S11.Q S11.G S11.c S11.pK S11.pK_eq S11.next S11.st S11.aT S11.bT S11.am S11.bm S11.im S11.xm
  S11.vm S11.Y S11.st_succ S11.am_zero S11.am_of_q S11.am_of_g S11.st_succ_q S11.st_succ_g
  S11.bm_succ S11.st_snd_ge S11.bm_eq S11.apps S11.nargs S11.apps_nil S11.apps_cons
  S11.apps_append S11.nargs_apps S11.apps_eq_app S11.S3_inj S11.apps_eq3 S11.apps_S2_eq3
  S11.step_apps S11.steps_apps S11.step_apps_det S11.step_apps_S2 S11.step_Q S11.step_SS
  S11.step_G S11.run_Q S11.run_G S11.run_am_SS S11.run_am S11.run_bm S11.pure_Q S11.pure_G
  S11.pure_c S11.pure_am S11.pure_apps S11.T_S11 S11.T_S11_31 S11.T_S11_36 S11.fold_Q
  S11.fold_c_zero S11.fold_c_succ S11.fold_c S11.fold_aT S11.fold_am S11.fold_cam S11.fold_Qam
  S11.fold_vm S11.fold_Qav S11.fold_apps_36 S11.fold_apps_31 S11.nohnf_am_apps S11.nohnf_cam_apps
  S11.nohnf_vm S11.nohnf_Qav_apps

-- M1a: S11Grammar (the set 𝔅, Lemma 16(i), RunFrame, Lemma 16(ii))
#s11_audit_clean
  S11.InB S11.allB_nil S11.allB_cons S11.InB.ofAm S11.InB.ofVm S11.InB.ofBm S11.InB.pure
  S11.allB_append_left S11.allB_append_last S11.InB.fun_arg S11.am_succ_of_q S11.am_succ_of_g
  S11.nargs_c S11.nargs_am S11.nargs_cam S11.RunFrame S11.InB.step_mem S11.RunFrame.step
  S11.RunFrame.steps S11.ne_S3_of_nargs S11.InB.three S11.RunFrame.three S11.lemma16_ii
  S11.lemma16_i

-- M1b: S11Closure (Lemma 15 over `Par`, Lemma 10(c) for spine predicates)
#s11_audit_clean
  S11.Red S11.RedB S11.Red.wsteps S11.Red.of_mem S11.mem_sub S11.red_S3 S11.subRed_par
  S11.subRed_wsteps S11.closure S11.lemma15 S11.hnf_eq S11.isHnf_S2 S11.reduct_ne_S
  S11.reduct_ne_S1 S11.reduct_S2 S11.Spine S11.Contains S11.Contains.sub S11.contains_par
  S11.contains_wsteps S11.lemma10c

-- M0: S11Teeth (teeth and rests as functions; Lemmas 3–7; decidable hnf; congruence)
#s11_audit_clean
  S11.conv_appL S11.conv_appR S11.conv_app S11.decHasHnf S11.hasHnfB S11.hasHnfB_iff S11.isPureB
  S11.isPureB_iff S11.runEnd S11.rest1 S11.tooth1 S11.restN S11.tooth S11.restN_zero
  S11.restN_succ S11.tooth_succ S11.runEnd_pure S11.headEnd_first S11.first_stable_spec
  S11.first_stable_unique S11.rest_tooth_of_first S11.rest1_pure S11.tooth1_pure S11.rest1_nohnf
  S11.restN_pure_nohnf S11.restN_pure S11.restN_nohnf S11.tooth_pure S11.move_spec S11.steps_left
  S11.head_step_items S11.step_to_S2 S11.run_to_S2 S11.lemma3c S11.nohnf_of_steps S11.nohnf_app
  S11.nohnf_wsteps S11.nohnf_three S11.nohnf_frames_three S11.wstep_app S11.wsteps_app S11.conv_S
  S11.Chain S11.chain_steps S11.chain_last S11.two_item S11.root_before S11.moves_loop S11.moves_A
  S11.moves_B S11.lemma4 S11.convSetoid S11.cls S11.cls_inv S11.cls_eq S11.inv_hnf0 S11.inv_hnf1
  S11.inv_hnf2 S11.inv_nohnf S11.inv_first S11.inv_restN S11.inv_tooth S11.teethRev
  S11.run_unfold S11.conv_apps_teeth S11.lemma6 S11.RSuf S11.RSuf.pure S11.rsuf_wstep
  S11.rsuf_wsteps S11.tIter S11.tIter_add S11.tIter_succ' S11.tIter_pure S11.wsteps_appR S11.rr
  S11.wsteps_rr S11.rsuf_rr S11.lemma7b S11.lemma7c S11.lemma7d


-- M2: S11Run (the run of p_K; Lemmas 8, 9, 10; the counter i_m)
#s11_audit_clean
  S11.moves_B0 S11.pure_xm S11.pure_bm S11.pure_Y S11.bm_eq_cam S11.lemma8a S11.lemma8a_first
  S11.lemma8b S11.pure_one S11.pure_two S11.restN_pK S11.tooth_pK_succ S11.tooth_pK S11.pure_pK
  S11.nohnf_pK S11.lemma9 S11.lemma9_suffix_Y S11.lemma9_suffix_tY S11.Dot1 S11.Kappa
  S11.dot1_hasHnf S11.dot1_unique S11.kappa_unique S11.kappa_conv S11.kappa_conv_iff S11.kappa_cam
  S11.kappa_xm S11.teeth_chain S11.xm_read S11.index_read S11.im_of_conv S11.st_snd_le_succ
  S11.st_snd_mono S11.im_mono S11.st_down S11.st_grow S11.st_unbounded S11.im_unbounded
  S11.im_unbounded' S11.im_not_periodic S11.im_shift_inj S11.nohnf_of_steps_rev S11.chain_rsuf_gen
  S11.chain_rsuf_w S11.chain_rsuf S11.chain_rsuf_w1

-- M4: S11Second (Lemmas 11, 12, 13: the run of q with the teeth of p_K)
#s11_audit_clean
  S11.lhs S11.hasHnf_S S11.app_not_conv_S S11.im_eq_of_xm_conv S11.chain_zero S11.lemma12a
  S11.lemma12b S11.cancel_cam S11.lemma13_core S11.moveY S11.bad_step S11.aq S11.bq
  S11.restN_split S11.aq_pure S11.bad_forever S11.no_bad S11.KindB S11.move_q S11.kindB_succ
  S11.exists_kindB S11.srun S11.lemma11 S11.lemma13 S11.second_run S11.srun_spine

-- M5: S11Main (Definition 14, Lemmas 15(a),(b), 18; Theorem 1; Corollary 2)
#s11_audit_clean
  S11.SolFrom S11.SolFrom.coind S11.SolFrom.unfold S11.solFrom_of_seq S11.SolFrom.step
  S11.SolFrom.hasHnf S11.SolFrom.not_short S11.SolFrom.first S11.sol_conv S11.sol_am S11.sol_aq
  S11.lemma15b S11.spine_aq S11.sol_am_shift S11.sol_am_eq S11.hasHnf_bm S11.lemma18
  S11.steps_cases S11.exists_nonliteral S11.ct_pK S11.pre S11.restN_add S11.tooth_add
  S11.pre_spec S11.ct_pK_rest

#print axioms S11.lemma16_ii
#print axioms S11.lemma16_i
#print axioms S11.run_am
#print axioms S11.fold_am
#print axioms S11.nohnf_Qav_apps
#print axioms S11.lemma15
#print axioms S11.lemma10c
#print axioms S11.first_stable_spec
#print axioms S11.moves_B
#print axioms S11.inv_hnf2
#print axioms S11.lemma6
#print axioms S11.lemma7b
#print axioms S11.lemma7d
#print axioms S11.lemma8a
#print axioms S11.lemma9
#print axioms S11.im_of_conv
#print axioms S11.im_shift_inj
#print axioms S11.chain_rsuf
#print axioms S11.nohnf_of_steps_rev
#print axioms S11.lemma11
#print axioms S11.lemma12b
#print axioms S11.second_run
#print axioms S11.srun_spine
#print axioms S11.lemma18
#print axioms S11.ct_pK
#print axioms S11.ct_pK_rest
