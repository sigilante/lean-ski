import Lean
import Ski.PsiSkel

/-!
# Axiom gate for the Ψ-skeleton table facts (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.PsiSkel`.  `Ski/Audit.lean` is not edited.
-/

open Lean Elab Command

namespace PsiSkel.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#psi_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end PsiSkel.Audit

#psi_audit_clean PsiSkel.oneB_eq PsiSkel.one_iff PsiSkel.one_item_of_fold PsiSkel.fold_one_item PsiSkel.fold_two_items
#psi_audit_clean PsiSkel.combB_eq PsiSkel.comb_alive PsiSkel.root_head_not_comb PsiSkel.inertB_eq PsiSkel.inert_iff
#psi_audit_clean PsiSkel.headChain_last PsiSkel.lzSelfB_eq PsiSkel.lzClosedB_eq PsiSkel.Lz_self PsiSkel.Lz_closed
#psi_audit_clean PsiSkel.lastArg_foldl PsiSkel.last_mem_Lz

#print axioms PsiSkel.headChain_last
#print axioms PsiSkel.last_mem_Lz
#print axioms PsiSkel.root_head_not_comb
#print axioms PsiSkel.one_item_of_fold
