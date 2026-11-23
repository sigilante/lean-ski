import Lean
import Ski.Phi

/-!
# Axiom gate for Theorem Φ (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.Phi`; building `Ski.Audit` maps every module of the library.
Every theorem of `Ski/Phi.lean` is listed.
-/

open Lean Elab Command

namespace Phi.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#phi_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end Phi.Audit

#phi_audit_clean Phi.sim_zero Phi.sim_succ Phi.All₂.append Phi.All₂.mono_mem Phi.All₂.mono Phi.All₂.forall_left Phi.All₂.forall_right Phi.All₂.map_eq Phi.fold_val Phi.fold_eq_of_val Phi.val_fibT Phi.val_tower
#phi_audit_clean Phi.Periodic.of_sIter Phi.step_foldl Phi.steps_foldl Phi.headChain_steps Phi.no_step_hnf Phi.hnf_unique Phi.steps_pure Phi.steps_fold Phi.head_hnf Phi.hasHnf_iff_head Phi.pure_foldl Phi.fold_foldl_bot
#phi_audit_clean Phi.step_spine Phi.r1_steps Phi.run_of_steps Phi.run_step Phi.run_steps Phi.tower_ne_S Phi.tower_inj Phi.towRel_succ Phi.mod_pred Phi.lvl_base Phi.lvl_dead Phi.Rel.pure
#phi_audit_clean Phi.Rel.val_eq Phi.Rel.mono Phi.Rel.refl Phi.rel_S Phi.base_tower Phi.rel_tower Phi.Good.of_steps Phi.hr_app Phi.hr_foldl Phi.hr_of_rel Phi.hr_refl Phi.hr_tower
#phi_audit_clean Phi.good_short Phi.caseS Phi.core Phi.rel_plug Phi.obs_total Phi.obs_unique Phi.obs_transfer Phi.good_of_sim Phi.theorem_phi Phi.lvl_refl Phi.fibB_dead Phi.s1_fib
#phi_audit_clean Phi.tower4B_eq Phi.fold_tower_ge4 Phi.s1_periodic Phi.theorem_phi_s1

#print axioms Phi.theorem_phi
#print axioms Phi.good_of_sim
#print axioms Phi.core
#print axioms Phi.s1_periodic
#print axioms Phi.theorem_phi_s1
