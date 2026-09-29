import Lean
import Ski.Basic
import Ski.Fuel
import Ski.Trace
import Ski.Heap
import Ski.Air
import Ski.AirCheck
import Ski.HeapOpen
import Ski.AirOpen
import Ski.Inst
import Ski.SmallLemma
import Ski.AirJet
import Ski.JetTable
import Ski.InstOpen
import Ski.ProbeTree
import Ski.AirProbe
import Ski.Witness
import Ski.WitnessExamples
import Ski.Compose
import Ski.ComposeExamples
import Ski.Composed
import Ski.Circuit.BaseSound
import Ski.Circuit.BaseComplete
import Ski.Circuit.Selectors
import Ski.Circuit.CompAir
import Ski.Circuit.CompFinal
import Ski.Circuit.CompComplete
import Ski.Circuit.WitAir
import Ski.Circuit.WitComplete
import Ski.Circuit.SudAir
import Ski.Circuit.SudSound
import Ski.Circuit.SudComplete
import Ski.Circuit.JetAir
import Ski.Circuit.Flow
import Ski.Circuit.JetKind
import Ski.Circuit.JetSound
import Ski.BoolProbe
import Ski.Statement
import Ski.Sudoku
import Ski.SudokuCheck
import Ski.Weak
import Ski.Lambda
import Ski.Quote
import Ski.Open
import Ski.Abs
import Ski.Transfer
import Ski.Realize
import Ski.Tait
import Ski.Stratum
import Ski.Stratum2
import Ski.Stratum2C
import Ski.BridgeA
import Ski.Stratum3
import Ski.Sigma
import Ski.Census
import Ski.Outcome
import Ski.Bridge
import Ski.Cost
import Ski.CostAdd
import Ski.Compile
import Ski.Front
import Ski.Check
import Ski.TypeCheck
import Ski.Source
import Ski.Kernel
import Ski.Laws
import Ski.Programs
import Ski.Simulation
import Ski.SourceEval
import Ski.SourceJoy
import Ski.SourceRun
import Ski.Adequacy
import Ski.SourceTables
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
  "AUDIT FAILURE for {n}\n \
  disallowed axioms: {bad.toList}\n \
  full footprint: {axs.toList}\n \
  allowed here: {allowed}\n\
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
  padStep_of_some padStep_of_none certifiedPad_stutter evalF_pad pad_of_evalF
  certified_pad_iff certifiedPad_sound certifiedPad_unique evalF_of_runF certified_pad_budgets

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
  absO_eq mem_abs OTerm.mem_vars absNV_eq absNF_eq wrapLiftF_eq compF_eq compLamF_eq
  compDefF_eq compRecF_eq ctorOF_eq
  Scott.Zero_abs Scott.Suc_abs Scott.Num_abs Scott.Quot_abs Scott.Empty_abs Scott.Push_abs Scott.QCons_abs Scott.QUnit_abs Scott.QThen_abs Scott.RVal_abs Scott.RErr_abs Scott.RTime_abs
  CorpusTable.Q1_abs CorpusTable.Q2_abs CorpusTable.QCons_abs CorpusTable.QUnit_abs CorpusTable.QThen_abs LoopTable.Q1_abs LoopTable.QCons_abs LoopTable.QUnit_abs LoopTable.QThen_abs
  SumTable.Q1_abs SumTable.Q2_abs SumTable.Q3_abs SumTable.Q4_abs SumTable.Q5_abs
  SumTable.QCons_abs SumTable.QUnit_abs SumTable.QThen_abs

-- The kernel's source, compiled (G3): read from the text skijack compiled by the front end,
-- which agrees with skijack on every term; skijack's compilation modeled, pinned to its terms
#audit_clean Front.refuses_incomplete Front.refuses_mixed Front.refuses_repeated
  Front.lowers_in_declaration_order kernel_agrees kernel_formals kernel_wUnit kernel_wQcons kernel_wCat kernel_applyU
  KernelSrc.wUnit_def KernelSrc.wQcons_def KernelSrc.wCat_def KernelSrc.armCons_def
  KernelSrc.armUnit_def KernelSrc.armThen_def
  NoQuot.front_agrees CorpusTable.front_agrees LoopTable.front_agrees SumTable.front_agrees
  wPop_compiles wDup_compiles wSwap_compiles wDip_compiles wDo_compiles wIfz_compiles
  wLit_compiles wQuote_compiles wAdd_compiles add_compiles seq_compiles idW_compiles
  wQcons0_compiles wCat0_compiles wUnit0_compiles NoQuot.table_QCons NoQuot.table_QUnit
  NoQuot.table_QThen NoQuot.table_wQcons NoQuot.table_wCat NoQuot.table_wUnit
  NoQuot.table_applyU CorpusTable.table_Qs0 CorpusTable.table_Qs1 CorpusTable.table_QCons
  CorpusTable.table_QUnit CorpusTable.table_QThen CorpusTable.table_wQcons
  CorpusTable.table_wCat CorpusTable.table_wUnit CorpusTable.table_applyU
  CorpusTable.table_bodyT0 CorpusTable.table_bodyT1 LoopTable.table_Qs0
  LoopTable.table_QCons LoopTable.table_QUnit LoopTable.table_QThen LoopTable.table_wQcons
  LoopTable.table_wCat LoopTable.table_wUnit LoopTable.table_applyU LoopTable.table_bodyT0
  SumTable.table_Qs0 SumTable.table_Qs1 SumTable.table_Qs2 SumTable.table_Qs3 SumTable.table_Qs4
  SumTable.table_QCons SumTable.table_QUnit SumTable.table_QThen SumTable.table_wQcons
  SumTable.table_wCat SumTable.table_wUnit SumTable.table_applyU SumTable.table_bodyT0
  SumTable.table_bodyT1 SumTable.table_bodyT2 SumTable.table_bodyT3 SumTable.table_bodyT4

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

-- The compiler simulates the source semantics: λ-lifted β, δ with Y for recursion, Scott
-- case; the fixedness of each compiled source; `wPop` on a push, from the source
#audit_clean Front.CSrc.occurs_resolve Front.CSrc.peel_resolve compLam_chain
  All2.length All2.append All2.split All2.getD Tr.apps Tr.apps_inv Tr.override Tr.junk tr_inst
  ycomb_step fixSelf_unroll getD_app_left getD_app_right map_getD_range overrideC_range
  ctor_close_beta Tr.unroll simulation simulation_steps lookup_some_mem fixed_of_check
  kernel_fixed corpus_fixed loop_fixed sum_fixed prog_wPop prog_Push prog_RVal genv_kernel
  wPop_source wPop_push

-- The front end's agreement check: what `agrees` establishes (the coverage itself, every
-- file checked against skijack, is the separate project coverage/)
#audit_clean Front.FEqn.compileF_eq Front.takeEntry_lookup
  Front.agreeEnv_lookup Front.agreeEnv_lookup_rev Front.agrees_termOf Front.agrees_termOf_rev
  Front.lookup_cons_self Front.lookup_cons_ne Front.agreeEnv_cons

-- skijack's checker: Stage A and Stage B, ported; where it passes the checked compilation
-- is the unchecked one (that it passes exactly where skijack's does is coverage/)
#audit_clean Front.checkedWith_of_pass Front.checkedWith_of_fail

-- L2: the write-once heap machine refines L1 contraction for contraction
#audit_clean Mach.get_append Mach.termAt_append Mach.termAt_mono Mach.stackAt_append
  Mach.stackAt_mono Mach.getElem?_concat Mach.termAt_cell Mach.stackAt_cell Mach.apps_cons
  Mach.step?_apps Mach.decode_eq Mach.decode_of Mach.length_concat Mach.mstep_none
  Mach.termAt_grow Mach.stackAt_grow Mach.mstep_some Mach.mrunC_sound Mach.mrunC_of_reach
  Mach.reach_of_evalF Mach.build_spec Mach.decode_load Mach.machine_eval Mach.machine_count
  Mach.mstep_append

-- The λ-calculus: substitution fusion, Church–Rosser by complete development, a sound
-- normalizer; and Proposition 3.1 of the metacircular paper: no combinator quotes live terms
#audit_clean Lam.ren_ren Lam.sub_ren Lam.ren_sub Lam.sub_sub Lam.sub_var Lam.sub_beta1
  Lam.ren_beta1 Lam.LPar.refl Lam.LStep.par Lam.LPar.steps Lam.LPar.sub Lam.LPar.dev
  Lam.lpar_diamond Lam.lpars_confluent Lam.lsteps_confluent Lam.LNormal.steps_eq
  Lam.normal_unique Lam.lstep?_sound Lam.lstep?_none Lam.lnf_sound
  tr_sub tr_ren tr_S tr_K tr_I tr_wstep tr_wsteps tr_SK no_quote_of_separated
  quote_separated no_quote

-- Part II's transfer lemmas: standardization (qualitative; the counted form refuted in the
-- kernel), and counted β for the compiler's bracket abstraction
#audit_clean eval_of_wsteps counted_standardization_false OWStepsN.weak OWStepsN.trans
  OWStepsN.left OWStepsN.right OWStepsN.app OWStepsN.appL vsize_pos vsize_of_closed
  vsize_app_open vsize_app_le mem_of_closed closed_of_mem closedB_toO subst_closed vsize_subst
  closedB_abs_of_closed vsize_abs abs_beta_count vsize_absN vsize_substL absN_beta_count

-- Part II's logic: realizability, soundness of the combinator system, completeness by
-- bracket abstraction (Curry's theorem)
#audit_clean Real.back Whnf.wstep Whnf.wsteps_K real_atom_iff real_atom_diverges lam_beta
  pairT_beta fstT_beta sndT_beta inlT_beta inrT_beta caseT_beta K_beta KI_beta soundness
  OTypes.congr toO_ne_var OTypes.var_inv OTypes.app_inv abs_types OTypes.close OTypes.real
  nd_compile completeness completeness_closed nd_realizes
  unpackT_beta subst_toO abs_subst_self compile_substW close_subst_single ndx_realizes
  NDX.exElim exElim_realizes

-- Part II's realizer language: simply typed λ with products and sums, strongly
-- normalizing by Tait's method
#audit_clean Rz.Tm.upr_comp Rz.Tm.ren_ren Rz.Tm.up_ren_comp Rz.Tm.sub_ren Rz.Tm.ren_up_comp
  Rz.Tm.ren_sub Rz.Tm.up_comp Rz.Tm.sub_sub Rz.Tm.up_var Rz.Tm.sub_var Rz.Tm.sub_beta1
  Rz.Tm.ren_beta1 Rz.Tm.beta1_up Rz.Tm.Steps.single Rz.Tm.Steps.trans Rz.Tm.Steps.map
  Rz.Tm.Step.ren Rz.Tm.Step.sub Rz.Tm.SN.step Rz.Tm.SN.steps Rz.Tm.SN.of_map Rz.Tm.SN.of_sub
  Rz.Tm.SN.of_app Rz.Tm.SN.of_fst Rz.Tm.inl_step_inv Rz.Tm.inr_step_inv Rz.Tm.sn_inl
  Rz.Tm.sn_inr Rz.Tm.inl_steps_inv Rz.Tm.inr_steps_inv Rz.Tm.app_step_neutral
  Rz.Tm.fst_step_neutral Rz.Tm.snd_step_neutral Rz.Tm.neutral_steps_first
  Rz.cr Rz.Red.sn Rz.Red.step Rz.Red.steps Rz.Red.neutral Rz.Red.var Rz.Red.const Rz.Red.lam
  Rz.Red.fst_pair Rz.Red.snd_pair Rz.Red.inl Rz.Red.inr Rz.Red.case Rz.Red.pair_inv
  Rz.Red.split Rz.fundamental
  Rz.strong_normalization Rz.omega_not_sn Rz.omega_untyped

-- Stratum 1 at the source: call-by-name steps of an additively affine realizer shrink its
-- additive size
#audit_clean Rz.asz_pos Rz.asz_ren Rz.upr_inj Rz.acnt_ren_inj Rz.succ_inj Rz.acnt_shift
  Rz.acnt_sub_self Rz.affA_ren Rz.affA_sub Rz.VarsBut.up Rz.asz_sub_zero Rz.asz_sub_le
  Rz.beta1_varsBut Rz.beta1_affA Rz.WH.affA Rz.WH.asz_lt Rz.wh_bound Rz.wh_steps_lt

-- The bridge: a typed realizer, written as SKIjack source and compiled by `comp`, converges
#audit_clean Rz.Converges.back Rz.RS.back Rz.converges_whnf Rz.pairG_beta Rz.inlG_beta
  Rz.inrG_beta Rz.RS.inh_conv Rz.RS.conv Rz.RS.pair Rz.RS.inl Rz.RS.inr Rz.absN_append
  Rz.wrapLift_close Rz.comp_lam_close Rz.projS_beta Rz.EnvOK.cons Rz.sem Rz.compiled_RS
  Rz.compiled_converges Rz.compiled_apply_converges Rz.glue_converges

-- The normal-order cost of compiled affine realizers: graded types, each combinator firing once
#audit_clean StepsN.left' StepsN.trans' Rz.Q.mono Rz.Q.backN Rz.Q.back Rz.Q_prodE Rz.Q_sumE
  Rz.Sub.sound Rz.Q.garr_app Rz.Q_K Rz.Q_I Rz.Q_S1 Rz.Q_S2 leaves_toO envsum_toO count_eq_zero
  mem_of_count count_pos mem_false_of_count Rz.OG.sound Rz.OG.congr Rz.toO_ne_var' Rz.OG.var_inv
  Rz.OG.app_inv Rz.Sub.garr_lin Rz.abs_OG Rz.count_abs_ne Rz.count_absN Rz.absN_OG
  Rz.oiter_stepsN Rz.Q_pairG Rz.Q_inlG Rz.Q_inrG Src.cnt_peel Src.cnt_pos_of_occurs
  Src.sizeOf_peel count_toO count_absN_mem count_appL count_comp_aux count_comp Src.occurs_peel
  Rz.Src.cnt_projS Rz.Src.cnt_trS Rz.trS_peel Rz.distinct_of_nodup Rz.nodup_of_distinct
  Rz.CtxOK.cons Rz.overrideG_self Rz.OG.var' Rz.OG.appL_vars Rz.filter_false_nil Rz.projS_occurs
  Rz.projS_OG Rz.og_usual Rz.ogsem
  Rz.envsum_zero Rz.leaves_close Rz.compiled_Q Rz.glue_head_bound Rz.fstPairT_typed
  Rz.fstPairT_leaves Rz.fstPairT_bound

-- The source semantics, run: normal-order proof search, the words' meaning from their
-- source, every Run derivation a source run, and adequacy for the four compiled sources
#audit_clean Cl.apps_append Cl.spine_apps SStep.apps_left SSteps.single SSteps.trans SSteps.left
  SSteps.right SStep.mono SSteps.mono headStep_sound sstep?_sound seval_sound Cl.substC_apps
  inst_substC overrideCl_substC getD_map_substC junk_substC SStep.substC SSteps.substC
  holeT_ne_K fill_K kernel_mono kernelDefs_sources add_source dup_source swap_source pop_source
  cons_source cat_source unit_source lit_source quote_source add_word_source plain_source
  i_run_source i_bad_source dip_stages outS_val_cases outS_err_cases SSteps.apps_left
  dip_run_source dip_bad_source ifz_zero_source ifz_succ_source ifz_bad_source cwR_source
  inst_natC inst_itemCS inst_quoteCS inst_wordC inst_bodyC seq_source_stages seq_source
  armsOf_length inst_arms applyU_dispatch getD_map_range getD_armsOf_static getD_armsOf_last
  arm_fill3 arm_fill4 armCons_source armUnit_source armThen_source idW_source run_source
  tr_gref_eq tr_natS tr_itemS tr_quotS tr_stackS tr_wordS tr_progS tr_ctor_inv dec_of_tr_natS
  dec_of_tr_itemS dec_of_tr_quotS dec_of_tr_stackS contract_of_tr_outS converges_of_tr_outS
  tr_srcRun run_of_source exact_iff diverges_iff_source of_tableCheck NoQuot.adequate
  CorpusTable.adequate LoopTable.adequate SumTable.adequate SumTable.source_six
  SumTable.source_exact LoopTable.source_diverges

-- Every program over every table (G6): divergence invariant under weak reduction, and
-- the forward theorem, the biconditional and agreement for the kernel's compilation
#audit_clean diverges_iff_of_wsteps Table.progT_wsteps Table.program_apply
  Table.program_diverges Table.program_exact

-- The quotation tables as data (G5): each valid, its laws the generic ones; each
-- program's term the kernel's compilation of its words (G6)
#audit_clean NoQuot.table_valid NoQuot.elim NoQuot.words NoQuot.apply NoQuot.cp_eq
  CorpusTable.table_valid CorpusTable.elim CorpusTable.words CorpusTable.apply
  CorpusTable.cp_eq CorpusTable.cq_eq CorpusTable.cr_eq
  CorpusTable.compiled_up_eq CorpusTable.compiled_uq_eq CorpusTable.compiled_ur_eq
  LoopTable.table_valid LoopTable.elim LoopTable.words LoopTable.apply LoopTable.cloop_eq
  SumTable.table_valid SumTable.elim SumTable.words SumTable.apply SumTable.cs_eq
  SumTable.cs_run SumTable.sumto_us_eq

-- End to end: the corpus programs, and a compiled program that diverges
#audit_clean NoQuot.up_six NoQuot.quote_i NoQuot.cat_i
  CorpusTable.uq_six CorpusTable.ur_over
  CorpusTable.stat1_run CorpusTable.omega_loop CorpusTable.omega_no_run CorpusTable.omega_diverges
  LoopTable.loop_run LoopTable.loop_no_run LoopTable.cloop_diverges
  SumTable.us_six SumTable.us_exact

-- The normal-order cost of additively affine realizers: shared variables threaded through
-- each case's continuations
#audit_clean Rz.Src.cnt_zero_of_not_occurs Rz.Src.cnt_appS Rz.Src.cnt_lamsS Rz.Src.cnt_brS
  Rz.mem_downFrom Rz.nodup_downFrom Rz.sharedS_lt Rz.sharedS_nodup Rz.sharedS_occurs
  Rz.not_sharedS Rz.Src.cnt_trA Rz.appS_app Rz.comp_appS Rz.lamsS_peel Rz.comp_brS
  Rz.overrideG_ext Rz.brS_OG Rz.trA_peel Rz.og_usualA Rz.ogsemA Rz.compiledA_Q
  Rz.glue_head_bound_add Rz.sharedT_not_aff Rz.sharedT_affA Rz.sharedT_typed
  Rz.sharedT_leaves Rz.sharedT_bound

-- Stratum 2: contraction normalizes, with no elementary bound on call-by-name steps
#audit_clean Rz.WH.no_lam Rz.WH.no_pair Rz.WH.no_inl Rz.WH.no_inr Rz.WH.det Rz.IsInj.no_step
  Rz.case_dec Rz.LB.back Rz.LB.backN Rz.LB_case Rz.LB_tog Rz.sub_beta1_shift Rz.LB_two
  Rz.iterN_succ' Rz.iterN_add Rz.iterN_sq Rz.LB_towerT Rz.iterN_succ_zero Rz.evalT_lower
  Rz.twoT_typed Rz.togT_typed Rz.towerT_typed Rz.evalT_typed Rz.asz_towerT Rz.asz_evalT
  Rz.Typed.ren Rz.Typed.sub Rz.WH.typed Rz.closedAt_ren Rz.closedAt_sub Rz.WH.closed
  Rz.WH.step Rz.WH.wh? Rz.wh?_sound Rz.Tm.SN.wh_normal Rz.Typed.const_inv Rz.canonical
  Rz.WHN.typed Rz.WHN.closed Rz.evaluates_inj Rz.closedAt_twoT Rz.closedAt_togT
  Rz.closedAt_towerT Rz.closedAt_evalT Rz.evalT_terminates Rz.two_pow_pos' Rz.lt_two_pow'
  Rz.two_pow_lt Rz.expT_lt Rz.tw_add Rz.pow_le_tw Rz.tw_beats_linear Rz.no_elementary_bound

-- The threaded compilation converges: convergence and cost speak of the same compiled term
#audit_clean Rz.lamsS_occurs_out Rz.lamsS_occurs_in Rz.brS_closed Rz.brS_trA_closed
  Rz.overrideC_brS Rz.EnvOK.upd_depth Rz.brS_beta Rz.semA Rz.compiledA_RS Rz.compiledA_converges
  Rz.compiledA_apply_converges Rz.glueA_converges

-- Stratum 2 on the compiled trace: the tower's lower bound, under both compilations
#audit_clean Rz.LBS.back Rz.LBS.back_succ Whnf.app_fun Rz.head_first Rz.LBS_case
  Rz.compiled_togT Rz.compiledA_togT Rz.compiled_twoT Rz.compiledA_twoT Rz.LBS_togC Rz.LBS_twoC
  Rz.compiled_towerT Rz.compiledA_towerT Rz.compiled_trueT Rz.compiledA_trueT Rz.compiled_evalT
  Rz.compiledA_evalT Rz.LBS_towerC Rz.evalC_lower Rz.compiled_evalT_lower
  Rz.compiledA_evalT_lower Rz.evalC_converges Rz.leaves_towerC Rz.leaves_evalC
  Rz.compiled_no_elementary_bound Rz.compiled_evalT_converges Rz.compiledA_evalT_converges
  Rz.compiledA_no_elementary_bound

-- Stratum 3: the fixed point breaks strong normalization; Y ⬝ I diverges, compiled
#audit_clean Ycomb_eq iI_steps Bterm_steps chainT_step Y_I_chain chainT_no_whnf Y_I_diverges
  Rz.omegaF_typed Rz.WHF.no_lam Rz.WHF.no_const Rz.omegaF_reducts Rz.omegaF_diverges
  Rz.fixConst_evaluates Rz.compiled_omegaF Rz.compiled_omegaF_diverges
  Rz.compiled_omegaF_timeout Rz.compiled_fixConst_converges Rz.fixfree_evaluates

-- The Σ-protocol algebra: AND, OR and threshold (a fold); its glue lies in stratum 1
#audit_clean Rz.thrPlan_isSome Rz.Stratum1.app Rz.Stratum1.source_bound Rz.Stratum1.compiled_bound
  Rz.closedAt_mono Rz.acnt_closed Rz.idT_s1 Rz.andI_s1 Rz.fstE_s1 Rz.sndE_s1 Rz.inlI_s1
  Rz.inrI_s1 Rz.caseE_s1 Rz.splitE_s1 Rz.andComm_s1 Rz.orComm_s1 Rz.thrTake_s1 Rz.thrSkip_s1 Rz.thrWeaken_s1
  Rz.Plan.build_typed Rz.Plan.build_closed Rz.Plan.build_acnt Rz.Plan.build_affA
  Rz.acnt_lams Rz.closedAt_lams Rz.lams_typed Rz.lams_affA Rz.Plan.compose_s1
  Rz.thr_compose_s1 Rz.glue_stratum1 Rz.glue_bounds Rz.swapT_not_affA Rz.orDist_s1 Rz.orDist_needs_additive Rz.intros_raw_affine Rz.thrPlan_extract

-- The circuit: an AIR over the write-once heap, accepting exactly the machine's runs
#audit_clean Air.mstep_eq Air.rd_eq Air.take_length Air.take_one_more Air.take_of_wrs
  Air.wrs_of_take Air.get_st Air.stepRow_mstep Air.mstep_stepRow Air.haltRow_mstep
  Air.stackAt_pos Air.haltRow_of Air.Reach.snoc Air.st_row0 Air.air_sound Air.air_sound_eval
  Air.iterM_succ' Air.adv_prefix Air.iterM_prefix Air.iterM_of_reach Air.take_of_prefix
  Air.st_regs Air.air_complete Air.air_budgets Air.Accepts.ctr_le Air.rd_pad Air.wrs_pad
  Air.stepRow_pad Air.short_pad Air.haltRow_pad Air.Accepts.pad

-- The AIR's constraints decided on a table, over a list and over an array
#audit_clean Air.chainB_trans Air.getLast_eq_getD Air.checkB_sound Air.checkB_eval Air.rd_G
  Air.wrs_G Air.stepRow_G Air.short_G Air.haltRow_G Air.chainB_G Air.checkA_eq Air.checkA_sound
  Air.rowFn_cons Air.chainB_of_trans Air.checkB_complete Air.checkA_iff

-- Atoms as probe markers: the heap machine and the AIR on open terms, and the probe binding
#audit_clean Mach.otermAt_append Mach.otermAt_mono Mach.ostackAt_append Mach.ostackAt_mono
  Mach.otermAt_grow Mach.ostackAt_grow Mach.otermAt_cell Mach.ostackAt_cell Mach.odecode_eq
  Mach.odecode_of Mach.OStep.appL Mach.ONeutral.appL Mach.omstep_some Mach.atom_head
  Mach.obuild_spec Mach.odecode_oload Mach.MSteps.snoc Mach.omachine_run Air.accepts_iff
  Air.AcceptsFrom.st0 Air.AcceptsFrom.reach Air.air_sound_open Air.air_probe

-- Supercombinator jets: instantiation is weak reduction, and a jetted run proves evaluation
#audit_clean Mach.overrideN_notin Mach.overrideC_notin Mach.override_ptr Mach.PtrsOK.mono
  Mach.popN_spec Mach.ibuild_spec Mach.apps_eq_appT Mach.inst_sound_g Mach.inst_sound
  Mach.JStep.ofTemplate Mach.jsteps_wsteps
  Mach.jet_run_eval

-- The small lemma: weak reduction keeps a stuck spine's head and arity
#audit_clean nhead_step nhead_steps nhead_appL appL_snoc nhead_inv small_lemma whnf_wstep
  small_lemma_whnf jet_run_shape

-- The AIR with instantiation rows: licensed roots, a row that is a jetted step, soundness, the checker
#audit_clean Air.termAt_G Air.rootsOKB_sound Air.popR_popN Air.ibuild_icells Air.termAt_take Air.instRow_jstep
  Mach.JSteps.snoc Air.AcceptsJ.reach Air.air_sound_jet Air.chainJ_trans Air.checkJA_sound
  JetTable.overrideN_argIx JetTable.symCells_icells

-- Probe segments: jets on open terms, probe trees, and the output bound by the AIR
#audit_clean Probe.AllW.refl Probe.AllW.trans Probe.AllW.snoc Probe.AllW.length OParI.spineN
  OParI.spine OParIs.spine Probe.owsteps_spine Probe.subst_appL Probe.DecV.subst Probe.DecVs.subst
  Probe.DecV.of_owsteps Probe.DecVs.of_allw Probe.DecV.of_probe Probe.decNat_of_decV
  Probe.decStack_of_decV Probe.mapM_num Probe.decodes_of_decV Mach.override_notin Mach.override_optr
  Mach.OPtrsOK.mono Mach.popN_ospec Mach.ibuild_ospec Mach.appL_app Mach.oinst_sound_g
  Mach.otermAt_of_termAt Mach.ojsteps_owsteps Air.kSum_append Air.Consec.append Air.planGo_consec
  Air.planKids_consec Air.Consec.head Air.Consec.next Air.planGo_parent Air.planKids_parent
  Air.planOf_consec Air.planOf_parent Air.Slice.cons Air.Slice.append Air.decV_go Air.decV_kids
  Air.AB.append Air.AB.mono Air.AB.take Air.fresh_of_AB Air.stkCells_AB Air.pcells_AB Air.stepG_AB
  Air.icells_AB Air.load_AB Air.wrs_len Air.probeRow_spec Air.normRow_spec Air.stkCells_ostack
  Air.appL_range Air.markers_ok Air.probeRow_decode Air.endRow_decode Mach.JSteps.snoc_all
  Air.otermAt_take Mach.OPtrsOK.get Mach.OPtrsOK.map_getD Mach.OPtrsOK.length Air.load_otermAt
  Air.pmono_le Air.not_start Air.AcceptsP.c0 Air.AcceptsP.ctrs Air.AcceptsP.ctr_mono
  Air.AcceptsP.run Air.AcceptsP.readF Air.AcceptsP.segs Air.AcceptsP.segsOK Air.air_probe_sound
  Air.air_probe_decodes Air.normB_sound Air.checkPA_sound Air.checkPA_decodes

-- A hidden term: knowing a realizer of an atom, proved by the AIR from the witness machine
#audit_clean Wit.wfB_sound Wit.wf_termAt Wit.witnessOf_some Wit.odecode_wMachine Wit.odecode_K Wit.wit_sound Wit.wit_realizes Wit.build_shape Wit.wMachine_public Wit.witCheck_sound Wit.witCheck_realizes WitEx.neg_real WitEx.neg_not_I WitEx.neg_fake WitEx.sat_real WitEx.sat_not_TTT WitEx.sat_fake

-- Zero knowledge, composed: a formula's statement, exact both ways, and the composition theorem
#audit_clean Compose.ws1 Compose.sI_app Compose.pairT_app Compose.pairT_fst Compose.pairT_snd
  Compose.inlT_app Compose.inrT_app Compose.K_wsteps Compose.eval_K_iff Compose.wsteps_K_iff
  Compose.F_not_K Compose.boolT_sel Compose.BT.sub_append Compose.enc_proj_step Compose.close_appL
  Compose.close_appP Compose.env0 Compose.env1 Compose.stmt_beta Compose.proj_sub Compose.fm_red
  Compose.phi_iff Compose.leaf_iff Compose.leaves_prefix Compose.leaf_path Compose.readBack_real
  Compose.real_of_accepted Compose.clear_shape Compose.clear_leaves Compose.good_of_real
  Compose.accepted_of_good Compose.accepted_of_real Compose.compose ComposeEx.negOr_accepts
  ComposeEx.negOr_real ComposeEx.negOr_refuses_clear ComposeEx.negOr_refuses_I

-- The circuit's statement for a composed proof: segments of evaluation, and its checker
#audit_clean CompM.sbool_boolT CompM.encO_fill CompM.fillB_shape CompM.addStmts_spec CompM.slots_wf
  CompM.cMachine_decode CompM.emono_le CompM.segStart_le CompM.not_end CompM.halt_K
  CompM.AcceptsC.segment CompM.msteps_len CompM.AcceptsC.runs CompM.composed_sound
  CompM.addStmts_shape CompM.getElem_agree CompM.cMachine_public CompM.checkC_sound
  CompM.shape_of_same CompM.checkC_realizes

-- Boolean statements: a formula compiled to Scott Booleans, read by a probe, and proved by the AIR
#audit_clean BExpr.sbool_sel BExpr.fill_tt BExpr.fill_ff BExpr.bool_reduce BExpr.probe_true
  BExpr.eval_all BExpr.eval_any Stmt.pbuild_spec Stmt.slotHeap_length Stmt.slotHeap_get
  Stmt.slot_reads Stmt.compile_occ Stmt.subst_probe Stmt.odecode_stmt Stmt.stmt_sound
  Stmt.pbuild_shape Stmt.stmtMachine_public

-- Sudoku: the formula is the checker, a passing grid solves the puzzle, and the AIR proves it
#audit_clean Sudoku.eval_sudoku Sudoku.bounded_all Sudoku.bounded_any Sudoku.idx_lt
  Sudoku.mem_nine Sudoku.mem_cells Sudoku.mem_pairs Sudoku.boxCell_lt Sudoku.mem_groups
  Sudoku.bounded_sudoku Sudoku.gridOf_eq Sudoku.mem_pairs_iff Sudoku.mem_cells_iff
  Sudoku.valid_cell Sudoku.valid_grid Sudoku.valid_group Sudoku.valid_digits
  Sudoku.valid_values Sudoku.row_mem Sudoku.col_mem Sudoku.box_mem Sudoku.valid_clues
  Sudoku.solves_of_valid
  Sudoku.sudoku_sound Sudoku.cluesOK_of Sudoku.wiki_clues_ok Sudoku.wiki_valid Sudoku.wiki_swapped Sudoku.wiki_solves

-- The Sudoku table check: a table produced outside Lean, decided from the statement machine
#audit_clean Air.getElem?_fun Air.checkFromA_sound Stmt.pbuildA_eq Stmt.stmtMachineA_eq
  Sudoku.sudokuCheck_sound

-- The three-valued outcome: structured formulas demand a normal form, an atom need not
#audit_clean Real.and_converges Real.or_converges Real.ex_converges atom_divergent_realizer

-- The census: the strata decided by the additive count, each with its theorem
#audit_clean Rz.affB_iff Rz.census_one_iff Rz.census_two_iff Rz.census_three_iff Rz.hasFix_ren
  Rz.hasFix_sub Rz.WHF.of_fixFree Rz.WHFN.of_fixFree Rz.WH.toWHF Rz.WHN.toWHFN
  Rz.census_hasFix Rz.census_one_bound Rz.Typed.unfix Rz.census_le_two_evaluates
  Rz.census_three_diverges Rz.census_le_two_normalizes Rz.additive_rule_needed_glue Rz.additive_rule_needed Rz.census_evalT Rz.census_table

-- The Plonky3 circuit as data: its normal forms, the field, and the corpus circuit's
-- soundness and completeness against the Lean AIR, with the export comparison's meaning
#audit_clean Circuit.noDiv_sound Circuit.euclid Circuit.mul_eq_zero Circuit.sub_eq_zero Circuit.bit_of
  Circuit.E.eval_poly Circuit.E.eval_norm Circuit.E.eval_eq_of_norm
  Circuit.sameAirB_sound Circuit.sameAirB_symm Circuit.sameAirsB_symm Circuit.accepted_transfer
  Circuit.kind_of Circuit.kindOK_all Circuit.kind_facts Circuit.mem_addr Circuit.lookup
  Circuit.BaseOK.read Circuit.BaseOK.step Circuit.BaseOK.halt
  Circuit.base_sound Circuit.baseAirs_sound Circuit.export_sound
  Circuit.shape Circuit.cpu_sat Circuit.mem_sat Circuit.prog_sat Circuit.balanced
  Circuit.cpu_honest Circuit.prog_honest Circuit.mstep_fits
  Circuit.base_complete Circuit.fits_pad Circuit.base_complete_padded Circuit.eval_complete
  Circuit.export_complete
-- Plonky3's selectors as they are: any values of their zero pattern
#audit_clean Circuit.guarded_iff Circuit.satP_iff Circuit.satP_transfer Circuit.base_guarded
  Circuit.acceptedP_iff Circuit.export_sound_P Circuit.export_complete_P

-- The composed circuit: the bus lemma for any tables, and soundness against the composed statement
#audit_clean Circuit.bus_hit Circuit.kind_ofC Circuit.kindOKC_all Circuit.kind_factsC
  Circuit.CompOK.memHit Circuit.CompOK.segHit Circuit.CompOK.read Circuit.CompOK.step Circuit.CompOK.halt
  Circuit.cMachine_fits Circuit.CompOK.witCell Circuit.CompOK.heap0 Circuit.CompOK.regionWF
  Circuit.endRow_mono Circuit.endRow_of_one Circuit.CompOK.restart Circuit.CompOK.stepOrHalt
  Circuit.CompOK.acceptsC Circuit.CompOK.sound Circuit.comp_guarded Circuit.compExport_sound

-- The composed circuit's completeness: honest tables for every run of the AIR with segments
#audit_clean Circuit.cntS_end Circuit.cntS_after Circuit.valid_rowP Circuit.cpuC_kind Circuit.cpuC_read
  Circuit.cpuC_sat Circuit.cpuC_memSend Circuit.foldBits_val Circuit.wit_sat Circuit.AcceptsC.ctr_le
  Circuit.AcceptsC.stk_le Circuit.progC_honest Circuit.witT_honest Circuit.cpuC_honest Circuit.cpuC_segsHonest
  Circuit.balancedC Circuit.memC_sat Circuit.comp_complete

-- The hidden-term circuit: soundness against the atom's realizer, and completeness
#audit_clean Circuit.RowOK.read Circuit.RowOK.step Circuit.RowOK.halt Circuit.RowOK.acceptsFrom
  Circuit.witCellG Circuit.WitOK.row Circuit.wMachine_fits Circuit.WitOK.heap0 Circuit.WitOK.sound
  Circuit.wit_guarded Circuit.witExport_sound Circuit.cpuW_sat Circuit.cpuW_honest Circuit.progW_honest
  Circuit.balancedW Circuit.wit_complete

-- The Sudoku circuit: soundness against the puzzle's solution
#audit_clean Circuit.stmt_fitsB Circuit.stmt_take Circuit.SudOK.input Circuit.SudOK.pubCell
  Circuit.SudOK.heap0 Circuit.SudOK.accepts Circuit.SudOK.sound Circuit.sud_guarded Circuit.sudOK_of
  Circuit.sudExport_sound

-- The Sudoku circuit: completeness
#audit_clean Circuit.cpuS_sat Circuit.progS_honest Circuit.witS_sat Circuit.witS_honest Circuit.balanced4
  Circuit.sud_complete

-- Chains on a balanced bus: no supply, no flow; one supply, one path
#audit_clean Circuit.pigeon Circuit.Edges.walk_stops Circuit.Edges.noFlow Circuit.Edges.sumTo_path Circuit.Edges.path

-- The jet CPU's rows: the eleven kinds are corpus rows; an instantiation's parts
#audit_clean Circuit.bus_hit_on Circuit.bus_hit Circuit.inst_facts Circuit.kind_ofJ Circuit.flags_zero
  Circuit.rowSat_ofJ Circuit.next_regsJ Circuit.clk_eq

-- The jet circuit: soundness against the AIR with instantiation rows
#audit_clean Circuit.provider_row Circuit.JetOK.memHit Circuit.JetOK.row Circuit.JetOK.rootsHit Circuit.JetOK.hdrHit
  Circuit.JetOK.tmplHit Circuit.JetOK.argHit Circuit.JetOK.popConserve Circuit.JetOK.wchConserve
  Circuit.JetOK.popPath Circuit.JetOK.popR_path Circuit.JetOK.wchPath Circuit.JetOK.resolve Circuit.JetOK.rootRes
  Circuit.JetOK.cellAt Circuit.JetOK.inst Circuit.JetOK.acceptsJ Circuit.JetOK.heap0 Circuit.JetOK.sound
  Circuit.jet_guarded Circuit.jetOK_of Circuit.jetExport_sound
