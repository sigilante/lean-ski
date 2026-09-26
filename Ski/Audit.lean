import Lean
import Ski.Basic
import Ski.Fuel
import Ski.Trace
import Ski.Scott
import Ski.Words
import Ski.Decode
import Ski.Leaf
import Ski.Corpus

/-!
# The audit manifest — build-enforced

Adopted from `lean-nock`.  Every name below is cited or citable, so it is
API; a rename fails elaboration.  Every footprint is checked at `lake
build`: a theorem whose axioms grow past `{propext, Quot.sound}`, or a
`sorry` (`sorryAx`), fails the build.  There is no `native_decide` and no
runtime bridge in this repository yet; when a bridge to Avon arrives it
gets its own quarantined allow-list, as `Nock/RuntimeBridge.lean` does.
-/

open Lean Elab Command

namespace Ski.Audit

/-- Lean 4's standard foundations.  Nothing here may exceed this. -/
def allowed : List Name := [``propext, ``Quot.sound]

private def auditAgainst (allowed : List Name) (ids : Array Ident) : CommandElabM Unit := do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError
        "AUDIT FAILURE for {n}\n  \
         disallowed axioms: {bad.toList}\n  \
         full footprint:    {axs.toList}\n  \
         allowed here:      {allowed}\n\
         If this is an intended change, update Ski/Audit.lean deliberately — \
         do not widen the allow-list to make a build pass."

/-- Fails the build unless every named constant's axiom footprint is contained
    in `{propext, Quot.sound}`.  Also catches `sorryAx`. -/
elab "#audit_clean " ids:ident+ : command => auditAgainst allowed ids

end Ski.Audit

open Ski.Audit

-- L0: the calculus
#audit_clean Whnf.no_step Step.det progress Steps.trans Steps.left Eval.deterministic

-- L0: the fuel interpreter agrees with the relation
#audit_clean step?_iff whnf_iff_step?_none iter_sound
  evalF_sound evalF_mono evalF_complete diverges_iff_fuel runF_evalF

-- L1: trace certificates
#audit_clean certified_sound certified_complete traceF_certified

-- The Scott constructors, as compiled
#audit_clean Scott.Zero_elim Scott.Suc_elim Scott.Num_elim Scott.Quot_elim
  Scott.Empty_elim Scott.Push_elim Scott.QCons_elim Scott.QUnit_elim Scott.QThen_elim
  Scott.RVal_elim Scott.RErr_elim Scott.RTime_elim

-- Canonicity: the pasted word terms against the corpus compilation
#audit_clean canon_wDup canon_wSwap canon_wPop canon_wDip canon_wDo canon_wIfz
  canon_wLit canon_wQuote canon_wAdd
  canon_wQcons_differs canon_wCat_differs canon_wUnit_differs

-- The decode relation: backward closure, constructors, encodings, functionality
#audit_clean Steps.app2 Steps.app3
  DecNat.of_steps DecItem.of_steps DecQuot.of_steps DecStack.of_steps Decodes.of_steps
  decodes_iff steps_thunk1 steps_thunk2
  dec_zero dec_suc dec_num dec_quot dec_qcons dec_qunit dec_qthen dec_empty dec_push
  dec_rval dec_rerr
  encNat_dec encItem_dec encQuot_dec encStack_dec
  DecNat.functional DecItem.functional DecQuot.functional DecStack.functional
  Decodes.functional

-- Leaf contracts: shared steps, then per word its stages, skeletons and leaves
#audit_clean Contract.of_steps eval_rval dec_rvalW contract_val contract_err
  stack_err stack_push item_num_err item_quot
  wPop_stages leafD_pop leaf_pop
  dupD_push wDup_stages leafD_dup leaf_dup
  swapC_push swapT_push wSwap_stages leafD_swap leaf_swap
  unitC_push unitQ_quot wUnit_stages leafD_unit leaf_unit
  consC_push consQ_quot consR_qcons wQcons_stages leafD_cons leaf_cons
  catC_push catQ_quot catR_qcons catThen_qthen wCat_stages leafD_cat leaf_cat
  wDip_stages cw_dip leafD_dip_run leafD_dip leaf_dip
  wDo_stages leafD_i_run leafD_i leaf_i
  litC_push quoteC_push wLit_run wQuote_run leafD_lit leafD_quote
