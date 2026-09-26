import Lean
import Ski.Basic
import Ski.Fuel
import Ski.Trace
import Ski.Weak
import Ski.Scott
import Ski.Words
import Ski.Decode
import Ski.Leaf
import Ski.Composition
import Ski.Apply
import Ski.Converse
import Ski.Total
import Ski.Corpus
import Ski.Table
import Ski.Examples

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

-- Weak reduction: standardization, normalization transfer, confluence
#audit_clean WSteps.single WSteps.trans WSteps.left WSteps.right WSteps.app Step.weak Steps.weak
  Par.refl WStep.par Par.wsteps ParI.par
  par_split parI_step par_step par_steps standardization
  ParIs.wsteps wsteps_split ParI.whnf ParIs.whnf eval_back diverges_of_wsteps
  par_dev Pars.trans WSteps.pars Pars.wsteps par_strip pars_confluent church_rosser

-- The Scott constructors, as compiled
#audit_clean Scott.Zero_elim Scott.Suc_elim Scott.Num_elim Scott.Quot_elim
  Scott.Empty_elim Scott.Push_elim Scott.QCons_elim Scott.QUnit_elim Scott.QThen_elim
  Scott.RVal_elim Scott.RErr_elim Scott.RTime_elim

-- Canonicity: the pasted word terms against the corpus compilation
#audit_clean canon_wDup canon_wSwap canon_wPop canon_wDip canon_wDo canon_wIfz
  canon_wLit canon_wQuote canon_wAdd canon_add canon_seq canon_idW canon_applyU_differs
  canon_wQcons_differs canon_wCat_differs canon_wUnit_differs

-- The decode relation: backward closure, constructors, encodings, functionality
#audit_clean Steps.app2 Steps.app3 Steps.appF
  DecNat.of_steps DecItem.of_steps DecQuot.of_steps DecStack.of_steps Decodes.of_steps
  decodes_iff steps_thunk1 steps_thunk2
  dec_zero dec_suc dec_num dec_quot dec_stat dec_qcons dec_qunit dec_qthen dec_empty dec_push
  dec_rval dec_rerr
  encNat_dec encItem_dec encQuot_dec encStack_dec
  mkK_self mkK_ne mkS_self mkS_ne DecQuot.probeK DecQuot.probeS
  DecQuot.probe_cons DecQuot.probe_unit DecQuot.probe_then
  DecQuot.stat_stat DecQuot.stat_cons DecQuot.stat_unit DecQuot.stat_then
  DecQuot.cons_unit DecQuot.cons_then DecQuot.unit_then
  DecNat.functional DecItem.functional DecQuot.functional DecStack.functional
  Decodes.functional

-- Leaf contracts: shared steps, the table's skeletons, then per word its stages and leaves
#audit_clean Contract.of_steps eval_rval dec_rvalW contract_val contract_err
  stack_err stack_push item_num_err item_quot item_quot_err item_num nat_zero nat_succ
  unitC_push unitQ_quot consC_push consQ_quot consR_qcons
  catC_push catQ_quot catR_qcons catThen_qthen
  wPop_stages leafD_pop leaf_pop
  dupD_push wDup_stages leafD_dup leaf_dup
  swapC_push swapT_push wSwap_stages leafD_swap leaf_swap
  leafD_unit leaf_unit leafD_cons leaf_cons leafD_cat leaf_cat
  wDip_stages cw_dip leafD_dip_run leafD_dip leaf_dip
  wDo_stages leafD_i_run leafD_i leaf_i
  litC_push quoteC_push wLit_run wQuote_run leafD_lit leafD_quote
  wIfz_stages leafD_ifz leaf_ifz

-- Class C: the compiled add, by fixpoint induction, and its word
#audit_clean add_self addB_unfold addSelf_step addF_stages addSelf_dec add_dec
  addC_push addN_num addT_tail wAdd_stages leafD_add leaf_add

-- Composition: the word table, compiled forms, the two schemas, the theorem
#audit_clean leaf_correct compiles_N idW_contract seq_stages seq_contract Csem_single
  composition composition_agree composition_enc apErr_sound

-- apply: the fixpoint, the relational semantics, Run, and the table's compiled applyU
#audit_clean fix_unfold fixB_unfold fixSelf_step fixSelf_inv
  apSoundR_empty apSoundR_only leafR_i leafR_dip leafR_ifz leafR composition_rel
  Run.word_cwR CwR.run Run.prog_csemR CsemR.run
  applySelf_cases run_sound applySelf_sound apply_sound composition_apply ApplyRel.det

-- The converse and the divergence biconditional
#audit_clean StepsN.steps Steps.counted StepsN.tail StepsN.after_step StepsN.tail_lt
  Whnf.fn StepsN.app_left Converges.of_steps Converges.app_left Converges.app3_left
  StepsN.app3_left path_i path_dip path_ifz fixSelf_first fixSelf_rest
  word_complete_at prog_complete_at applySelf_soundR apply_complete_at apply_complete_all
  apply_complete apply_diverges applyU_claim
  composition_complete composition_diverges composition_exact

-- Without static quotations, nothing diverges
#audit_clean cw_ok apply_total_bound apply_total word_total program_total
  program_converges program_not_diverges

-- The quotation tables: each law checked by the kernel, and the programs' compiled forms
#audit_clean NoQuot.elim NoQuot.words NoQuot.apply NoQuot.cp_compiles
  CorpusTable.elim CorpusTable.words CorpusTable.apply
  CorpusTable.cp_compiles CorpusTable.cq_compiles CorpusTable.cr_compiles

-- End to end: the corpus programs, and a compiled program that diverges
#audit_clean NoQuot.up_six NoQuot.quote_i NoQuot.cat_i
  CorpusTable.uq_six CorpusTable.ur_over
  CorpusTable.stat1_run CorpusTable.omega_loop CorpusTable.omega_no_run CorpusTable.omega_diverges
