import Lean
import Ski.GCertSound

/-!
# Axiom gate for the G certificate and the Ψ-skeleton bound (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.GCertSound`.  `Ski/Audit.lean` is not edited.

* `#gcert_audit_clean ids` checks the named constants.
* `#gcert_audit_modules` checks every theorem, and every definition without an internal name,
  declared in `Ski.GCertData`, `Ski.GCert` and `Ski.GCertSound` (the 304 chunk theorems
  included), and reports the counts.  The internal definitions it skips are compiler and
  elaborator auxiliaries, among them the code of the `chunks38` command, which is a program and
  not a proof.
-/

open Lean Elab Command

namespace GCert.Audit

def allowed : List Name := [``propext, ``Quot.sound]

def check (n : Name) : CommandElabM Unit := do
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

elab "#gcert_audit_clean " ids:ident+ : command => do
  for id in ids do
    check (← liftCoreM <| realizeGlobalConstNoOverload id)

elab "#gcert_audit_modules" : command => do
  let env ← getEnv
  let mods := [`Ski.GCertData, `Ski.GCert, `Ski.GCertSound]
  let mut count := 0
  let mut thms := 0
  let mut skipped : Array Name := #[]
  for m in mods do
    let some idx := env.getModuleIdx? m | throwError "module {m} not found"
    for n in env.header.moduleData[idx.toNat]!.constNames do
      let isThm := match env.find? n with
        | some (.thmInfo _) => true
        | _ => false
      -- every theorem, and every definition except the elaborator code of `chunks38`
      if isThm || !n.isInternal then
        check n
        count := count + 1
        if isThm then thms := thms + 1
      else
        skipped := skipped.push n
  logInfo m!"gcert audit: {count} constants ({thms} theorems) in {mods}: axioms ⊆ {allowed}; skipped (internal, not theorems): {skipped}"

end GCert.Audit

#gcert_audit_modules

-- the certificate checks
#gcert_audit_clean GCert.bfB_eq GCert.pwfB_eq GCert.oneFB_eq GCert.combFB_eq GCert.rowLenB_eq
#gcert_audit_clean GCert.a1 GCert.a2 GCert.a3 GCert.cc GCert.bnd GCert.invc GCert.b0 GCert.bb
-- the checks restated on β
#gcert_audit_clean GCert.bf_eq GCert.pwf_eq GCert.isOne_iff GCert.isComb_iff GCert.rank_chain
#gcert_audit_clean GCert.rank_other GCert.rank_mid GCert.fine_le GCert.phi_le GCert.rho1_le
#gcert_audit_clean GCert.fine_chain GCert.fine_other GCert.inv_three GCert.inv_four
-- soundness of the abstraction and the bound
#gcert_audit_clean GCert.headChain_pure GCert.flag_spine GCert.round_inv GCert.headChain_penult
#gcert_audit_clean GCert.other_le GCert.r1_le_pw GCert.run_hnf GCert.phase GCert.root_head_app
#gcert_audit_clean GCert.rankT_le GCert.root_bound_aux GCert.root_bound GCert.root_bound_67
#gcert_audit_clean GCert.psi_skeleton GCert.run_example

#print axioms GCert.a3
#print axioms GCert.bb
#print axioms GCert.round_inv
#print axioms GCert.root_bound
#print axioms GCert.psi_skeleton
