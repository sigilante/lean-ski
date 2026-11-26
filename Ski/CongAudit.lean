import Lean
import Ski.Congruence

/-!
# Axiom gate for the congruence theorem (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.Congruence`.  The root module `Ski` imports this module, so the
default `lake build` runs the gate (as for `S10Audit`).
-/

open Lean Elab Command

namespace Congruence.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#cong_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end Congruence.Audit

-- Lock 1 Theorem C: tree equality (`∀ d P, NF d t P ↔ NF d u P`) is a congruence on closed S-terms
#cong_audit_clean
  Congruence.Eqv Congruence.Eqv.refl Congruence.Eqv.symm Congruence.Eqv.trans
  Congruence.eqv_steps Congruence.node_inv Congruence.parts_dir Congruence.eqv_parts
  Congruence.eqv_bot Congruence.nargs Congruence.ptKind Congruence.nf2_kind Congruence.HnfMatch
  Congruence.factK Congruence.Cong Congruence.Cong.pure Congruence.Cong.symm Congruence.Cong.S
  Congruence.cong_S_inv Congruence.cong_hnf Congruence.cong_step Congruence.cong_steps
  Congruence.cong_fold Congruence.head_target Congruence.cong_split Congruence.cong_nf
  Congruence.cong_eqv Congruence.eqv_app Congruence.Ctx Congruence.Ctx.plug Congruence.cong_ctx
  Congruence.eqv_ctx

/-- info: 'Congruence.eqv_app' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Congruence.eqv_app

/-- info: 'Congruence.eqv_ctx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Congruence.eqv_ctx

/-- info: 'Congruence.cong_eqv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Congruence.cong_eqv
