import Lean
import Ski.S11Closure

/-!
# Axiom gate for the S11 mechanization (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only the S11 modules.  These names are not yet listed in `Ski/Audit.lean`
(plan `notes/S11-MECH-PLAN.md`, M6: they join it at the release).
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

#print axioms S11.lemma16_ii
#print axioms S11.lemma16_i
#print axioms S11.run_am
#print axioms S11.fold_am
#print axioms S11.nohnf_Qav_apps
#print axioms S11.lemma15
#print axioms S11.lemma10c
