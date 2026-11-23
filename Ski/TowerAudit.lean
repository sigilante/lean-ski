import Lean
import Ski.Tower

/-!
# Axiom gate for the tower of models (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.Tower`.

* `#tower_audit_module M` checks every theorem, and every definition without an internal name,
  declared in the module `M`, and reports the counts and the internal constants it skips
  (compiler and elaborator auxiliaries, which are programs and not proofs).
* `#tower_audit_clean ids` checks the named constants.
-/

open Lean Elab Command

namespace Tower.Audit

def allowed : List Name := [``propext, ``Quot.sound]

def check (n : Name) : CommandElabM Unit := do
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

elab "#tower_audit_clean " ids:ident+ : command => do
  for id in ids do
    check (← liftCoreM <| realizeGlobalConstNoOverload id)

elab "#tower_audit_module " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "module {m.getId} not found"
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
  logInfo m!"tower audit: {count} constants ({thms} theorems) in {m.getId}: axioms ⊆ {allowed}; skipped (internal, not theorems): {skipped}"

end Tower.Audit

#tower_audit_module Ski.TowerFin
#tower_audit_module Ski.Tower

-- finite combinatorics
#tower_audit_clean TowerFin.php TowerFin.iter_period TowerFin.iter_mod TowerFin.cnt_dich
#tower_audit_clean TowerFin.qidx TowerFin.qelt TowerFin.qelt_idx TowerFin.qidx_eq TowerFin.qidx_inj
#tower_audit_clean TowerFin.qidx_elt TowerFin.decEP TowerFin.stab_final TowerFin.EP_cong
#tower_audit_clean TowerFin.EP_max TowerFin.close_spec TowerFin.dist_len TowerFin.closed_closed
#tower_audit_clean TowerFin.closure
-- the bridge (Lemma 4 for the full observable)
#tower_audit_clean Tower.val_inv Tower.obsF_of_hasObs Tower.obsF_iff_hasObs Tower.obsF_conv
#tower_audit_clean Tower.cong_of_conv Tower.cong_ctx Tower.cong_left Tower.cong_right
-- the observable as a function; constants; finite index
#tower_audit_clean Tower.obsFn Tower.obsFn_spec Tower.obsFn_iff Tower.val_of_obs Tower.cong_val
#tower_audit_clean Tower.TModel.periodic Tower.sgc Tower.sgc_cong Tower.finite_index
-- Lemma 7
#tower_audit_clean Tower.alg Tower.foldA_cong Tower.rl_E Tower.E_plug Tower.E_sound Tower.qval_eq
#tower_audit_clean Tower.qrep_cong Tower.qval_iff Tower.qval_rep Tower.qlaw Tower.qh_val Tower.quoT
#tower_audit_clean Tower.lemma7 Tower.decCong Tower.Quo.gen Tower.Quo.h_s Tower.Quo.h_app
-- the reduction, Theorem 1, Corollary 2
#tower_audit_clean Tower.reduction Tower.reduction_hom Tower.s1RepsB_eq Tower.s1Reps_spec
#tower_audit_clean Tower.pre1_block Tower.base0 Tower.base1 Tower.next Tower.levels Tower.M Tower.o
#tower_audit_clean Tower.hom Tower.prefix_regularity Tower.generated Tower.block Tower.hom_val
#tower_audit_clean Tower.hom_s Tower.hom_app Tower.hom_φ Tower.M_syn Tower.theorem_one
#tower_audit_clean Tower.realizable Tower.realizable_iff Tower.realizableDec

#print axioms Tower.obsF_conv
#print axioms Tower.cong_of_conv
#print axioms Tower.TModel.periodic
#print axioms Tower.finite_index
#print axioms Tower.lemma7
#print axioms Tower.decCong
#print axioms Tower.reduction_hom
#print axioms Tower.levels
#print axioms Tower.prefix_regularity
#print axioms Tower.theorem_one
#print axioms Tower.realizable_iff
#print axioms Tower.realizableDec
