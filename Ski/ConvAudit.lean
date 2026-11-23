import Lean
import Ski.Conv

/-!
# Axiom gate for conversion invariance and prefix uniqueness (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.Conv`.  These names are not yet listed in `Ski/Audit.lean`.
-/

open Lean Elab Command

namespace Conv.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#conv_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end Conv.Audit

#conv_audit_clean Conv.Convertible.trans Conv.Convertible.symm Conv.Convertible.of_wsteps Conv.Convertible.least Conv.conv_iff_join Conv.stable_iff Conv.reach_frame Conv.hnf_not_bot Conv.run_hnf_hnf Conv.run_hnf_bot Conv.run_bot_bot Conv.first_stable Conv.Inv.wsteps Conv.obs_exists Conv.obs_unique Conv.obs_bot_first Conv.hnf1_wsteps Conv.hnf2_wsteps Conv.parIs_S Conv.parIs_app Conv.obs_back Conv.obs_fwd Conv.obs_wsteps Conv.obs_conv Conv.lemma3 Conv.SModel.inv Conv.lemma3_model Conv.lemma3_D Conv.pre_unique Conv.pre_total Conv.pre_bot_first

#print axioms Conv.lemma3
#print axioms Conv.lemma3_model
#print axioms Conv.lemma3_D
#print axioms Conv.obs_bot_first
#print axioms Conv.pre_unique
#print axioms Conv.pre_total
