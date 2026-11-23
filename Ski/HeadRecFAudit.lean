import Lean
import Ski.HeadRecF

/-!
# Axiom gate for Theorem H (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.HeadRecF`.  The same names are also listed in `Ski/Audit.lean`.
-/

open Lean Elab Command

namespace HeadRec.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#headrecf_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end HeadRec.Audit

#headrecf_audit_clean HeadRec.IStep.weak HeadRec.FStep.weak HeadRec.FSteps.weak HeadRec.FStep.left
  HeadRec.fstep_of_step HeadRec.fsteps_of_steps HeadRec.lsz_pos HeadRec.LSteps.single HeadRec.LSteps.trans
  HeadRec.LSteps.left HeadRec.LSteps.right HeadRec.LStep.mono HeadRec.LSteps.mono HeadRec.lsz_lstep
  HeadRec.lsz_lsteps HeadRec.s2_dec HeadRec.lstep_dec HeadRec.nf_exists HeadRec.Normal.steps_eq
  HeadRec.root_join HeadRec.local_confluent HeadRec.confluent HeadRec.nf_unique HeadRec.Le.lsz_eq
  HeadRec.le_sim HeadRec.le_sims HeadRec.cons_le_tag HeadRec.rd_istep HeadRec.istep_tag HeadRec.fstep_tag
  HeadRec.fsteps_tag HeadRec.lifts HeadRec.sub_lift HeadRec.h_core HeadRec.theorem_H HeadRec.no_f_loop
  HeadRec.no_head_reduct_inside HeadRec.no_proper_ground_loop HeadRec.nhr_of_theorem_H

#print axioms HeadRec.theorem_H
#print axioms HeadRec.confluent
#print axioms HeadRec.nf_unique
#print axioms HeadRec.no_head_reduct_inside
