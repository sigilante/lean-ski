import Lean
import Ski.Full

/-!
# Axiom gate for Theorem 9 of S6 (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.Full`.

* `#full_audit_clean ids` checks the named constants.
* `#full_audit_module` checks every theorem, and every definition without an internal name,
  declared in `Ski.Full`, and reports the counts and the internal constants it skips
  (compiler and elaborator auxiliaries, which are programs and not proofs).
-/

open Lean Elab Command

namespace Full.Audit

def allowed : List Name := [``propext, ``Quot.sound]

def check (n : Name) : CommandElabM Unit := do
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

elab "#full_audit_clean " ids:ident+ : command => do
  for id in ids do
    check (← liftCoreM <| realizeGlobalConstNoOverload id)

elab "#full_audit_module" : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Ski.Full | throwError "module Ski.Full not found"
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
  logInfo m!"full audit: {count} constants ({thms} theorems) in Ski.Full: axioms ⊆ {allowed}; skipped (internal, not theorems): {skipped}"

end Full.Audit

#full_audit_module

-- the observable is a function
#full_audit_clean Full.val_step Full.val_steps Full.stable_run Full.psi_unique Full.psi_frame
#full_audit_clean Full.run_of_reach Full.run_total Full.obsF_total Full.obsF_unique Full.first_stable
-- runs, bursts, core forms
#full_audit_clean Full.run_inv Full.run_adv Full.nsteps_left Full.nsteps_args Full.nsteps_burst
#full_audit_clean Full.core_eq Full.core_cases Full.hnf_two Full.simL_val Full.fib_vals Full.fib_pair
-- configurations and the Claim
#full_audit_clean Full.RelF.vp Full.RelF.mono Full.hr_chain Full.hr_of_rel Full.hr_of_free
#full_audit_clean Full.rel_plugF Full.goodF_short Full.goodF_stable Full.good_or_ns Full.stepS
#full_audit_clean Full.caseS Full.caseT Full.coreF Full.good_of_simF Full.theorem_six
-- the signature
#full_audit_clean Full.nextOf_step Full.nextOf_none Full.acc_of_reach Full.nxt_wf Full.headEnd
#full_audit_clean Full.headEnd_spec Full.headEnd_hnf Full.headEnd_stable Full.kcls_lt Full.kcls_tow
#full_audit_clean Full.sig0 Full.sig Full.sig0_sound Full.sig_sound Full.pairF_inj Full.optF_inj
#full_audit_clean Full.baseCode_inj Full.sigCode Full.sigCode_inj Full.sig_congruence
#full_audit_clean Full.apx_refl Full.simL_refl Full.sitB_eq Full.s1_sIter Full.sitN_const
#full_audit_clean Full.s1_periodicF Full.sig_congruence_s1

#print axioms Full.theorem_six
#print axioms Full.coreF
#print axioms Full.obsF_unique
#print axioms Full.sig_sound
#print axioms Full.sigCode_inj
#print axioms Full.sig_congruence
#print axioms Full.headEnd
#print axioms Full.s1_periodicF
