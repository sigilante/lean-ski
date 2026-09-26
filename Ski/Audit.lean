import Lean
import Ski.Basic
import Ski.Fuel
import Ski.Trace
import Ski.Weak
import Ski.Open
import Ski.Abs
import Ski.Kernel
import Ski.Laws
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
#audit_clean Whnf.no_step Step.det progress Steps.single Steps.trans Steps.left
  steps_whnf_det Eval.deterministic

-- L0: the fuel interpreter agrees with the relation
#audit_clean step?_none step?_sound step?_complete step?_iff whnf_iff_step?_none iter_sound
  evalF_sound evalF_mono evalF_complete diverges_iff_fuel runF_evalF

-- L1: trace certificates
#audit_clean certified_sound certified_complete traceF_certified

-- Weak reduction: standardization, normalization transfer, confluence
#audit_clean WSteps.single WSteps.trans WSteps.left WSteps.right WSteps.app Step.weak Steps.weak
  Par.refl WStep.par Par.wsteps ParI.par
  par_split parI_step par_step par_steps standardization
  ParIs.wsteps wsteps_split ParI.whnf ParIs.whnf eval_back diverges_of_wsteps
  par_dev Pars.trans WSteps.pars Pars.wsteps par_strip pars_confluent church_rosser
  par_step_le Par.whnf

-- The Scott constructors, as compiled
#audit_clean Scott.Zero_elim Scott.Suc_elim Scott.Num_elim Scott.Quot_elim
  Scott.Empty_elim Scott.Push_elim Scott.QCons_elim Scott.QUnit_elim Scott.QThen_elim
  Scott.RVal_elim Scott.RErr_elim Scott.RTime_elim
  Scott.Zero_oelim Scott.Suc_oelim Scott.Num_oelim Scott.Quot_oelim Scott.Empty_oelim
  Scott.Push_oelim Scott.QCons_oelim Scott.QUnit_oelim Scott.QThen_oelim Scott.RVal_oelim
  Scott.RErr_oelim Scott.RTime_oelim

-- Canonicity: the pasted word terms against the corpus compilation
#audit_clean canon_wDup canon_wSwap canon_wPop canon_wDip canon_wDo canon_wIfz
  canon_wLit canon_wQuote canon_wAdd canon_add canon_seq canon_idW canon_applyU_differs
  canon_wQcons_differs canon_wCat_differs canon_wUnit_differs

-- Open terms: head reduction, substitution, closing, symbolic runs, the split
#audit_clean OSteps.single OSteps.trans OSteps.left ONeutral.no_step
  OStep.no_S2 OStep.no_K1 OStep.no_I OStep.det osteps_neutral_det
  fresh_toO fresh_exists OStep.subst OSteps.subst subst_agree
  OStep.close OSteps.close close_toO toO_close close_appO subst_appO shiftAt_at subst_shiftAt
  ostep?_sound oiter_sound
  OWSteps.trans OWSteps.left OWSteps.right OWSteps.app OWSteps.appO OStep.weak OSteps.weak
  WStep.toO WSteps.toO OWStep.occ Fresh.of_owsteps
  OPar.refl OWStep.par OPar.wsteps OParI.par opar_split oparI_step opar_step opar_steps
  owsteps_split OParIs.var0 OParIs.var1 OParIs.var2 owsteps_var0 owsteps_var1 owsteps_var2

-- Bracket abstraction (G2): skijack's four rules, β, and fidelity to skijack's terms
#audit_clean mem_var mem_app OTerm.mem_of_occ OTerm.not_occ mem_toO single_self single_ne
  subst_var subst_single_of_not_mem abs_var abs_app abs_of_not_mem abs_beta abs_beta_head
  mem_subst_single subst_eq_var_iff abs_subst absN_subst OWSteps.appL absN_beta
  OWStep.subst OWSteps.subst OWStep.close OWSteps.close close_agree occ_abs single_var
  abs_beta_subst absN_beta_subst WSteps.appT appT_append close_appL abs_beta_close
  absN_beta_close updC_self overrideC_self overrideC_append
  Scott.Zero_abs Scott.Suc_abs Scott.Num_abs Scott.Quot_abs Scott.Empty_abs Scott.Push_abs Scott.QCons_abs Scott.QUnit_abs Scott.QThen_abs Scott.RVal_abs Scott.RErr_abs Scott.RTime_abs
  CorpusTable.Q1_abs CorpusTable.Q2_abs CorpusTable.QCons_abs CorpusTable.QUnit_abs CorpusTable.QThen_abs LoopTable.Q1_abs LoopTable.QCons_abs LoopTable.QUnit_abs LoopTable.QThen_abs

-- The kernel's source, compiled (G3): skijack's compilation modeled, pinned to its terms
#audit_clean wPop_compiles wDup_compiles wSwap_compiles wDip_compiles wDo_compiles wIfz_compiles
  wLit_compiles wQuote_compiles wAdd_compiles add_compiles seq_compiles idW_compiles
  wQcons0_compiles wCat0_compiles wUnit0_compiles NoQuot.table_QCons NoQuot.table_QUnit
  NoQuot.table_QThen NoQuot.table_wQcons NoQuot.table_wCat NoQuot.table_wUnit
  NoQuot.table_applyU CorpusTable.table_Qs0 CorpusTable.table_Qs1 CorpusTable.table_QCons
  CorpusTable.table_QUnit CorpusTable.table_QThen CorpusTable.table_wQcons
  CorpusTable.table_wCat CorpusTable.table_wUnit CorpusTable.table_applyU
  CorpusTable.table_bodyT0 CorpusTable.table_bodyT1 LoopTable.table_Qs0
  LoopTable.table_QCons LoopTable.table_QUnit LoopTable.table_QThen LoopTable.table_wQcons
  LoopTable.table_wCat LoopTable.table_wUnit LoopTable.table_applyU LoopTable.table_bodyT0

-- The decode relation: probing at fresh variables; substitution, closure under backward
-- weak reduction (G1b), the closed probes, constructors, encodings, functionality
#audit_clean probe_subst subst_end
  DecNatO.subst DecItemO.subst DecQuotO.subst DecStackO.subst DecodesO.subst
  DecNatO.of_owsteps DecItemO.of_owsteps DecQuotO.of_owsteps DecStackO.of_owsteps
  DecodesO.of_owsteps
  DecNat.of_wsteps DecItem.of_wsteps DecQuot.of_wsteps DecStack.of_wsteps Decodes.of_wsteps
  Steps.app2 Steps.app3 Steps.appF
  DecNat.of_steps DecItem.of_steps DecQuot.of_steps DecStack.of_steps Decodes.of_steps
  decodes_iff probe_close DecNatO.close DecItemO.close DecQuotO.close DecStackO.close
  DecNat.probe_zero DecNat.probe_succ DecItem.probe_num DecItem.probe_quot
  DecQuot.probe_stat DecQuot.probe_cons DecQuot.probe_unit DecQuot.probe_then
  DecStack.probe_nil DecStack.probe_cons Decodes.probe_val Decodes.probe_err
  steps_thunk1 steps_thunk2 owsteps_thunk1 owsteps_thunk2
  dec_zero dec_suc dec_num dec_quot dec_stat dec_qcons dec_qunit dec_qthen dec_empty dec_push
  dec_rval dec_rerr rtime_decodes_nothing
  encNat_dec encItem_dec encQuot_dec encStack_dec
  ONeutral.v1 ONeutral.v2
  DecNatO.functional DecItemO.functional DecQuotO.functional DecStackO.functional
  DecodesO.functional
  DecNat.functional DecItem.functional DecQuot.functional DecStack.functional
  Decodes.functional

-- Leaf contracts: shared steps, their weak forms, then per word its stages and leaves
#audit_clean Contract.of_steps Contract.of_wsteps eval_rval dec_rvalW contract_val contract_err
  stack_err stack_push item_num_err item_quot item_quot_err item_num nat_zero nat_succ
  contract_valW contract_errW stack_errW stack_pushW item_num_errW item_quotW
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
  StepsN.par StepsN.wtail StepsN.wtail_lt
  Whnf.fn StepsN.app_left Converges.of_steps Converges.app_left Converges.app3_left
  StepsN.app3_left path_i path_dip path_ifz fixSelf_first fixSelf_rest
  word_complete_at prog_complete_at applySelf_soundR apply_complete_at apply_complete_all
  apply_complete apply_diverges applyU_claim
  composition_complete composition_diverges composition_exact

-- Without static quotations, nothing diverges
#audit_clean cw_ok apply_total_bound apply_total word_total program_total
  program_converges program_not_diverges

-- The laws for every table (G4): compiled source under β, the constructors, the words, apply
#audit_clean close_comp_ev compLam_body wrapLift_beta lam1_beta lam2_beta compDef1_beta
  appL_append subst_appL appO_eq override_append override_range ctor_beta
  Table.wUnit_stages Table.wQcons_stages Table.wCat_stages Table.kit_elim Table.kit_words
  Table.appF_agree Table.armsK_lt Table.armsK_n Table.armsK_n1 Table.armsK_n2 Table.appF_armsK
  Table.ev_arms Table.applySrc_ev Table.armCons_beta Table.armUnit_beta Table.armThen_beta
  Table.kit_applyU_unfold Table.kit_applyF_stages Table.encItem_eq Table.encQuot_eq
  Table.ev_wordSrc Table.ev_bodySrc Table.kit_body_compiles Table.kit_apply

-- The quotation tables as data (G5): each valid, its laws the generic ones, and the
-- programs' compiled forms
#audit_clean NoQuot.table_valid NoQuot.elim NoQuot.words NoQuot.apply NoQuot.cp_compiles
  CorpusTable.table_valid CorpusTable.elim CorpusTable.words CorpusTable.apply
  CorpusTable.cp_compiles CorpusTable.cq_compiles CorpusTable.cr_compiles
  CorpusTable.compiled_up_eq CorpusTable.compiled_uq_eq CorpusTable.compiled_ur_eq
  LoopTable.table_valid LoopTable.elim LoopTable.words LoopTable.apply LoopTable.cloop_compiles

-- End to end: the corpus programs, and a compiled program that diverges
#audit_clean NoQuot.up_six NoQuot.quote_i NoQuot.cat_i
  CorpusTable.uq_six CorpusTable.ur_over
  CorpusTable.stat1_run CorpusTable.omega_loop CorpusTable.omega_no_run CorpusTable.omega_diverges
  LoopTable.loop_run LoopTable.loop_no_run LoopTable.cloop_diverges
