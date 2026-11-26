import Lean
import Ski.FFBlock

/-!
# Axiom gate for FF on the 38-block fold (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.FFBlock`.  The root module `Ski` imports this module, so the
default `lake build` runs the gate (as for `CongAudit`).
-/

open Lean Elab Command

namespace FFBlock.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#ff_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end FFBlock.Audit

-- Lock 1, FF for 𝔹: `Eqv t u` gives `fold t = fold u` on pure S-terms
#ff_audit_clean
  FFBlock.tower FFBlock.tower_pure FFBlock.towerSet FFBlock.towerB FFBlock.towerB_eq
  FFBlock.tower_cert FFBlock.fold_ne_zero FFBlock.eq_S_of_fold FFBlock.eq_tower
  FFBlock.eqv_tower FFBlock.eqv_towerSet FFBlock.rankTable FFBlock.rank FFBlock.img0
  FFBlock.usable FFBlock.img0B FFBlock.baseB FFBlock.k1B FFBlock.k2Row FFBlock.img0B_eq
  FFBlock.baseB_eq FFBlock.k1B_eq FFBlock.k2Row_1 FFBlock.k2Row_2 FFBlock.k2Row_4
  FFBlock.k2Row_5 FFBlock.k2Row_8 FFBlock.k2Row_9 FFBlock.k2Row_10 FFBlock.k2Row_11
  FFBlock.k2Row_17 FFBlock.k2Row_18 FFBlock.k2Row_19 FFBlock.k2Row_20 FFBlock.k2Row_27
  FFBlock.k2Row_28 FFBlock.usable_iff FFBlock.img0_mem FFBlock.base_cert FFBlock.k1_cert
  FFBlock.k2_of_row FFBlock.k2_cert FFBlock.ff_core FFBlock.ff_step FFBlock.ff_le
  FFBlock.fold_eqv

/-- info: 'FFBlock.fold_eqv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FFBlock.fold_eqv

/-- info: 'FFBlock.eqv_tower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FFBlock.eqv_tower

/-- info: 'FFBlock.eq_tower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FFBlock.eq_tower
