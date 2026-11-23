import Lean
import Ski.Ncfp

/-!
# Axiom gate for the proved cases of NCFP (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.Ncfp`.

* `#ncfp_audit_module M` checks every theorem, and every definition without an internal name,
  declared in the module `M`, and reports the counts and the internal constants it skips
  (compiler and elaborator auxiliaries, which are programs and not proofs).
* `#ncfp_audit_clean ids` checks the named constants.
-/

open Lean Elab Command

namespace Ncfp.Audit

def allowed : List Name := [``propext, ``Quot.sound]

def check (n : Name) : CommandElabM Unit := do
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

elab "#ncfp_audit_clean " ids:ident+ : command => do
  for id in ids do
    check (← liftCoreM <| realizeGlobalConstNoOverload id)

elab "#ncfp_audit_module " m:ident : command => do
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
  logInfo m!"ncfp audit: {count} constants ({thms} theorems) in {m.getId}: axioms ⊆ {allowed}; skipped (internal, not theorems): {skipped}"

end Ncfp.Audit

#ncfp_audit_module Ski.Ncfp

-- size, normal forms, contexts; Prop. 0
#ncfp_audit_clean Ncfp.sz_wstep Ncfp.sz_wsteps Ncfp.Normal.wsteps Ncfp.wsteps_to_normal
#ncfp_audit_clean Ncfp.wsteps_plug Ncfp.Holed.sz_le Ncfp.Holed.sz_lt Ncfp.prop0
-- head runs: Lemma L
#ncfp_audit_clean Ncfp.step_app Ncfp.plus_last Ncfp.hnf1_literal Ncfp.lemma_L Ncfp.lemma_L'
#ncfp_audit_clean Ncfp.last_item_step Ncfp.link
-- SS-chains
#ncfp_audit_clean Ncfp.ss_link Ncfp.SSPath.snoc Ncfp.sspath_strip Ncfp.ss_bound
-- descendants
#ncfp_audit_clean Ncfp.sub_sz_le Ncfp.PSub.sub Ncfp.PSub.sz_lt Ncfp.sub_psub Ncfp.sub_wsteps
#ncfp_audit_clean Ncfp.psub_wsteps Ncfp.Desc.trans Ncfp.Desc.irrefl Ncfp.Next.desc
-- Theorem 2
#ncfp_audit_clean Ncfp.nonlit_exists Ncfp.run_inner Ncfp.run Ncfp.small_desc Ncfp.enum
#ncfp_audit_clean Ncfp.mem_enum Ncfp.right_combs Ncfp.right_combs_seq Ncfp.right_combs_conv
-- comb contexts, no fixed-point combinator
#ncfp_audit_clean Ncfp.CombB.mono Ncfp.Comb.bound Ncfp.ncfp_comb Ncfp.ncfp_S_aux Ncfp.ncfp_S
#ncfp_audit_clean Ncfp.ncfp_S_comb Ncfp.no_fixed_point_combinator Ncfp.no_fpc

-- Theorem F; Theorem G, Lemma P, Corollary G1; Theorem B, Lemma T, Lemma A, the Moves, Corollary B1
#ncfp_audit_clean Ncfp.finite_descent Ncfp.desc_finite Ncfp.NextF.desc Ncfp.small_descF Ncfp.first_combs Ncfp.first_combs_seq
#ncfp_audit_clean Ncfp.lemma_P Ncfp.no_pred Ncfp.Rigid.sub Ncfp.Rigid.sz_lt Ncfp.Rigid.not_appS Ncfp.sspath_rigid Ncfp.NextG.desc Ncfp.runG_inner
#ncfp_audit_clean Ncfp.runG Ncfp.small_descG Ncfp.mixed_combs Ncfp.mixed_combs_seq Ncfp.mixed_combs_conv Ncfp.GCombB.mono Ncfp.GComb.bound Ncfp.Comb.gcomb
#ncfp_audit_clean Ncfp.ncfp_gcomb Ncfp.steps_antisymm Ncfp.bot_app Ncfp.firstStable_exists Ncfp.lemma_T Ncfp.lemma_A Ncfp.stepsK_of_steps
#ncfp_audit_clean Ncfp.stepsK_later Ncfp.steps_step_plus Ncfp.stepsK_plus Ncfp.past_root Ncfp.bmove Ncfp.step_apps Ncfp.plus_apps Ncfp.apps_append
#ncfp_audit_clean Ncfp.hdesc_of_steps Ncfp.HDesc.trans Ncfp.HDesc.irrefl Ncfp.tooth_descent Ncfp.teeth_unbounded Ncfp.teeth_unbounded_seq Ncfp.fold_apps Ncfp.pure_apps_of
#ncfp_audit_clean Ncfp.snoc_cases Ncfp.norm_bound Ncfp.fold_conv Ncfp.cor_B1 Ncfp.cor_B1'

#ncfp_audit_clean Ncfp.del Ncfp.mem_del Ncfp.del_length_le Ncfp.del_length_lt

#print axioms Ncfp.prop0
#print axioms Ncfp.lemma_L
#print axioms Ncfp.ss_bound
#print axioms Ncfp.right_combs
#print axioms Ncfp.right_combs_seq
#print axioms Ncfp.right_combs_conv
#print axioms Ncfp.ncfp_comb
#print axioms Ncfp.ncfp_S
#print axioms Ncfp.ncfp_S_comb
#print axioms Ncfp.no_fixed_point_combinator
#print axioms Ncfp.no_fpc
#print axioms Ncfp.first_combs
#print axioms Ncfp.first_combs_seq
#print axioms Ncfp.lemma_P
#print axioms Ncfp.mixed_combs
#print axioms Ncfp.mixed_combs_seq
#print axioms Ncfp.mixed_combs_conv
#print axioms Ncfp.ncfp_gcomb
#print axioms Ncfp.lemma_T
#print axioms Ncfp.bmove
#print axioms Ncfp.teeth_unbounded
#print axioms Ncfp.teeth_unbounded_seq
#print axioms Ncfp.cor_B1
