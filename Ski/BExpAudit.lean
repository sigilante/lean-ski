import Lean
import Ski.BExp

/-!
# Axiom gate for the bounded-exposure table facts (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.BExp`; building `Ski.Audit` maps every module of the library.
The same names are also listed in `Ski/Audit.lean`.
-/

open Lean Elab Command

namespace BExp.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#bexp_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end BExp.Audit

#bexp_audit_clean BExp.C1_eq BExp.C2_eq BExp.C3_img BExp.C4_img BExp.C5_img BExp.C2_eq' BExp.C3_eq BExp.C4_eq BExp.C_ge4 BExp.row31B_eq BExp.row34B_eq BExp.row31 BExp.row34 BExp.mem_img BExp.chain_mem BExp.chain4_emitter BExp.chain3
#bexp_audit_clean BExp.budZeroB_eq BExp.budStepB_eq BExp.longB_eq BExp.A_ge6 BExp.budZero BExp.budStep7 BExp.budStep BExp.budConv BExp.app_budget BExp.unbounded_blocks BExp.long_app BExp.shapeB_eq BExp.shape_tab BExp.shape1 BExp.shape3 BExp.shape6 BExp.shape12 BExp.arityB_eq BExp.arity_blocks
#bexp_audit_clean BExp.towerShapeB_eq BExp.tower_of_fold BExp.exempt_shape BExp.headChainN_of BExp.piB_eq BExp.r1_le BExp.skeleton_r1 BExp.skeleton BExp.iterS_run BExp.fibT_pure BExp.fold_fibT BExp.fib8B_eq BExp.fibB_add BExp.fibB_bot BExp.fib_dead BExp.fold_iterS_congr BExp.deep_item BExp.psi_cex

#print axioms BExp.skeleton
#print axioms BExp.psi_cex
#print axioms BExp.long_app
#print axioms BExp.chain4_emitter
