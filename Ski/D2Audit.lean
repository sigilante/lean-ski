import Lean
import Ski.D2

/-!
# Axiom gate for the depth-2 theorem (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only `Ski.D2`, so that it can be built under a 1.5 GB memory cap; building
`Ski.Audit` maps every module of the library.  The same names are also listed in `Ski/Audit.lean`.
-/

open Lean Elab Command

namespace D2.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#d2_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end D2.Audit

#d2_audit_clean D2.checks D2.d2_closed D2.d2_slaw D2.d2_wsteps D2.d2_block D2.d1_prefix D2.d2_prefix D2.d2_nf
#d2_audit_clean D2.allB_spec D2.force_eq D2.chunk_get D2.colsIn_spec D2.rows_len D2.out1B_eq D2.botB_eq D2.phi0 D2.slawChunk_all D2.closedRow_all D2.out2Row_all D2.homRow_all D2.colsRow_all
#d2_audit_clean D2.τ_lt D2.col_eq D2.slaw D2.hom D2.outC_lt D2.outS D2.out_one D2.out_two D2.out_bot D2.foldD_lt D2.wstep_foldD D2.wsteps_foldD D2.steps_foldD D2.fold_eq
#d2_audit_clean D2.k4 D2.pt2_one D2.pt2_two D2.pt2_bot D2.q4 D2.pre1 D2.pre2 D2.pre_bwd D2.pre_exists D2.trunc_zero D2.nf_S D2.pre_nf D2.pre2_iff D2.nf2

#print axioms D2.d2_prefix
#print axioms D2.d2_nf
