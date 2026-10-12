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
import Ski.JetPublic
import Ski.JetRun
import Ski.InstOpen
import Ski.ProbeTree
import Ski.AirProbe
import Ski.Witness
import Ski.WitnessExamples
import Ski.Compose
import Ski.ComposeExamples
import Ski.ComposeX
import Ski.ComposeXExamples
import Ski.ComposedX
import Ski.Chain
import Ski.ChainExamples
import Ski.DataJet
import Ski.BitArith
import Ski.ZK.Poseidon2SKI
import Ski.Circuit.P2Air
import Ski.P2Jet
import Ski.ComposedP
import Ski.Circuit.CompPFinal
import Ski.P2PreSound
import Ski.P2Commit
import Ski.P2Complete
import Ski.P2Once
import Ski.ZK.CompPHonest
import Ski.Circuit.CompPCompleteFinal
import Ski.ZK.CompP
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
import Ski.Circuit.CompJAir
import Ski.Circuit.CompJFinal
import Ski.Circuit.CompJComplete
import Ski.ZK.CompJ
import Ski.ZK.LogUpCJ
import Ski.ZK.MaskOOD
import Ski.ZK.MaskPCS
import Ski.ZK.PRG
import Ski.ZK.Reject
import Ski.ZK.Honest
import Ski.ZK.Heights
import Ski.ZK.MaskMulti
import Ski.ZK.MaskQuot
import Ski.ZK.MaskChunk
import Ski.ZK.MaskRand
import Ski.ZK.Fri
import Ski.ZK.MaskFri
import Ski.ZK.MaskGen
import Ski.ZK.MaskCom
import Ski.ZK.MaskRec
import Ski.ZK.MaskCoset
import Ski.ComposeDist
import Ski.ZK.ComposeZK
import Ski.ZK.CompPSD
import Ski.ZK.HeightsJ
import Ski.ZK.CompRun
import Ski.ZK.CompRunEx
import Ski.ZK.FSRound
import Ski.ComposedJ
import Ski.Circuit.Flow
import Ski.Circuit.JetKind
import Ski.Circuit.JetSound
import Ski.Circuit.JetComplete
import Ski.Circuit.JetCore
import Ski.Circuit.ProbeAir
import Ski.Circuit.ProbeKind
import Ski.Circuit.ProbeSound
import Ski.Circuit.ProbeRows
import Ski.Circuit.ProbeComplete
import Ski.BoolProbe
import Ski.Statement
import Ski.Sudoku
import Ski.SudokuCheck
import Ski.Weak
import Ski.Lambda
import Ski.Quote
import Ski.Requote
import Ski.Graph
import Ski.RWMem
import Ski.GraphMem
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
import Ski.ZK.Circuits
import Ski.ZK.Generic
import Ski.ZK.Abort
import Ski.Circuit.CompPred
import Ski.Entropy
import Ski.ZK.Transcript
import Ski.ZK.Tree
import Ski.ZK.TranscriptN
import Ski.ZK.Poseidon2Grain
import Ski.ZK.Poseidon2Generic
import Ski.ZK.Poseidon2Inv
import Ski.ZK.Blocks
import Ski.Circuit.SendsFast
import Ski.Circuit.JetCntFast
import Ski.Circuit.CpuFast
import Ski.Circuit.TraceCheck

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
  Circuit.balancedC Circuit.memC_sat Circuit.comp_complete Circuit.comp_complete_log Mach.buildA_eq
  Mach.build_eq_buildFast

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

-- The jet circuit: completeness, the honest tables satisfying and balancing
#audit_clean Circuit.JRun.base_trans Circuit.JRun.inst_spec Circuit.JRun.cpu_sat Circuit.JRun.pop_sat
  Circuit.JRun.instw_sat Circuit.sends_rows Circuit.JRun.bal_popch Circuit.JRun.bal_wch Circuit.JRun.bal_arg
  Circuit.prov_sends Circuit.JRun.bal_roots Circuit.JRun.bal_hdr Circuit.JRun.bal_tmpl Circuit.JRun.cpu_honestJ
  Circuit.JRun.pop_honest Circuit.JRun.instw_honest Circuit.bal_mem4 Circuit.JRun.balanced Circuit.AcceptsJ.stk_le
  Circuit.jet_complete Circuit.AcceptsJ.pad Circuit.fits_pad_nil

-- An instantiation row from the buses' facts; the probe CPU's rows
#audit_clean Circuit.JetCore.inst Circuit.JetOK.core Circuit.probe_facts Circuit.kind_ofP Circuit.rowSat_ofP
  Circuit.next_regsP Circuit.clk_eqP

-- Probe soundness: the buses' facts, the chains, the probe rows, and the output bound
#audit_clean Circuit.ProbeOK.memHit Circuit.ProbeOK.rootsHit Circuit.ProbeOK.hdrHit Circuit.ProbeOK.tmplHit
  Circuit.ProbeOK.argHit Circuit.ProbeOK.planHit Circuit.ProbeOK.popConserve Circuit.ProbeOK.popConserveL
  Circuit.ProbeOK.wchConserve Circuit.ProbeOK.pwConserve Circuit.ProbeOK.core Circuit.cnt_eq Circuit.pr_later
  Circuit.pRow_spec Circuit.pr_eq Circuit.pRow_mono Circuit.ProbeOK.row Circuit.ProbeOK.readHead
  Circuit.ProbeOK.nilRead Circuit.ProbeOK.sSeg Circuit.ProbeOK.eSeg Circuit.ProbeOK.probeWrites
  Circuit.ProbeOK.probeStep Circuit.ProbeOK.popPathL Circuit.ProbeOK.endLater Circuit.ProbeOK.endLast
  Circuit.ProbeOK.segendHit Circuit.ProbeOK.childPtr Circuit.ProbeOK.norm Circuit.ProbeOK.acceptsP
  Circuit.ProbeOK.heap0 Circuit.ProbeOK.sound Circuit.probe_guarded Circuit.probeOK_of Circuit.probeExport_sound

-- Probe completeness: the honest tables satisfy the AIRs and balance
#audit_clean Circuit.PRun.jok Circuit.PRun.probe_spec Circuit.PRun.later_end Circuit.PRun.probe_rowSat
  Circuit.PRun.norm_rowSat Circuit.PRun.cpu_satP Circuit.PRun.pop_satP Circuit.PRun.pw_satP Circuit.mem5_sat
  Circuit.bal_mem5 Circuit.PRun.cpuP_split Circuit.PRun.bal_popch_probe Circuit.PRun.bal_pwch Circuit.PRun.bal_plan
  Circuit.PRun.bal_segend Circuit.PRun.bal_arg_probe Circuit.PRun.cpu_honestP Circuit.PRun.pw_honest
  Circuit.PRun.pop_honestP Circuit.PRun.balancedP Circuit.PRun.hd_lt Circuit.PRun.stk_le Circuit.probe_complete
  Circuit.AcceptsP.pad Air.planOf_last Circuit.probe_complete_planOf

-- Zero knowledge: BabyBear's quartic extension, the combiner, the blinding chain, and the terminals
#audit_clean Circuit.fermat Circuit.euler_11 Circuit.nonsquare_11 Circuit.EF.mul_inv Circuit.EF.inv_inv
  Circuit.EF.inv_ne_zero Circuit.Mat4.mulT_inv Circuit.Mat4.inv_mulT Circuit.horner_combInv Circuit.combInv_horner
  Circuit.blindTerm_pre Circuit.blindPre_term Circuit.Tup.dec_enc Circuit.Tup.enc_dec Circuit.sumTo_perm
  Circuit.count2_bij Circuit.chain_hides Circuit.pole_count Circuit.chain_hides_valid Circuit.logup_sum
  Circuit.terminal_setBlind Circuit.chain_terminals
  Circuit.sud_zk Circuit.sud_zk_valid Circuit.wit_zk Circuit.wit_zk_valid Circuit.comp_zk Circuit.comp_zk_valid
  Circuit.vdm_eq Circuit.generic_iff Circuit.det_zero_iff Circuit.nongeneric_count
  Circuit.den_one Circuit.abort_count Circuit.entries_length

-- Predicates over literal bits: the composed circuit for any evaluation statement, and a
-- verifier that reads the constrained bits, not the witness
#audit_clean Circuit.compG_guarded Circuit.compOK_ofG Circuit.compExportG_sound Circuit.comp_completeG_log
  CompM.combBT_nleaves CompM.fillB_combBT CompM.slotBits_length CompM.pred_iff
  Circuit.predExport_sound Circuit.checkPred_sound

-- The whole transcript, simulated over an ideal hiding PCS
#audit_clean Circuit.transcript_zk Circuit.pcsHides_unit Circuit.pcsClose_of_hides
  Circuit.allEntries_length Circuit.comp_transcript Circuit.sud_transcript Circuit.wit_transcript
  Circuit.rowSends_one Circuit.foldr_single Circuit.cpuC_rowSegs Circuit.cpuC_segsCount Circuit.segs_honest

-- A blinding tree hides the terminals: any spanning tree of blinding buses, one tuple an edge
#audit_clean Circuit.countN_last Circuit.viewT_congr_x Circuit.viewT_congr_t Circuit.sumL_updF
  Circuit.edge_shift Circuit.tree_hides Circuit.viewT_sum Circuit.tree_chain Circuit.chain_hides_tree

-- The whole transcript over any number of blinded tables
#audit_clean Circuit.countN_eq_sumN Circuit.sumN_add Circuit.sumN_const Circuit.sumTo_sumN Circuit.xrefN_sum
  Circuit.inner_pcsN Circuit.inner_chainN Circuit.transcript_zkN Circuit.comp_transcriptN
  Circuit.chain_viewT Circuit.viewT_xrefN Circuit.tsum_tsumN

-- Public closures: jets over a heap with private cells, licensed over the blank heap and every filled one
#audit_clean Air.termAtG_public Air.termAt_public Air.publicB_sound Air.rootsOK_public Air.privC_false
  Air.rootsOK_filled Air.jetStmtC_sound

-- The composed circuit with jets, as data: the composed tables carry over, a blinded table keeps its own
#audit_clean Circuit.compJAirs_composed Circuit.withBlocks_cons

-- Soundness of the composed circuit with jets: the machine with jets and segments, its rows and kinds, the
-- jet core from its tables, the memory's prefix, the restarts and instantiations, the export
#audit_clean CompM.chead_K CompM.AcceptsCJ.runs CompM.composedJ_sound CompM.checkCJ_sound
  Circuit.kind_ofCJ Circuit.kindOKCJ_all Circuit.kind_factsCJ Circuit.next_regsCJ Circuit.clk_eqCJ
  Circuit.rowSends_withBlocks Circuit.CJOK.memHit Circuit.CJOK.segHit Circuit.CJOK.rootsHit Circuit.CJOK.hdrHit
  Circuit.CJOK.tmplHit Circuit.CJOK.argHit Circuit.CJOK.read Circuit.CJOK.step Circuit.CJOK.halt
  Circuit.CJOK.popConserve Circuit.CJOK.wchConserve Circuit.CJOK.core Circuit.CJOK.heap0 Circuit.CJOK.regionWF
  Circuit.CJOK.blank_le Circuit.CJOK.restart Circuit.CJOK.norm Circuit.CJOK.acceptsCJ Circuit.CJOK.sound
  Circuit.compJ_guarded Circuit.compJOK_of Circuit.compJExport_sound Circuit.predJExport_sound Circuit.checkCJ_pred

-- Completeness of the composed circuit with jets: the honest CPU satisfies its AIR and sends honestly, the
-- blinded tables send as their bases, the ten tables balance, and the main theorem with its statement form
#audit_clean CompM.AcceptsCJ.ctr_le CompM.AcceptsCJ.jok CompM.AcceptsCJ.stk_le CompM.AcceptsCJ.hd_lt
  Circuit.CRun.cpuCJ_sat Circuit.CRun.cpuCJ_honest Circuit.CRun.cpuCJ_jetSends Circuit.CRun.cpuCJ_blindZero
  Circuit.CRun.cpuCJ_segsHonest Circuit.CRun.segs_honestCJ Circuit.JRun.bal_rootsCJ Circuit.JRun.bal_hdrCJ
  Circuit.JRun.bal_tmplCJ Circuit.sends_provCJ Circuit.sends_quiet_tail Circuit.sends_withBlocks_quiet
  Circuit.sat_withBlocks Circuit.honest_withBlocks Circuit.provCJ_sat Circuit.sends_memC5 Circuit.memC5_sat
  Circuit.bal_segsC Circuit.JRun.pop_wide Circuit.JRun.instw_wide Circuit.CRun.balancedCJ
  Circuit.compJ_complete_log Circuit.compJStmt_complete_log

-- Zero knowledge of the composed circuit with jets: the tree of eight tables and seven tuples, each blinded
-- table's terminal, the published view as the tree's, the sum, the transcript, and the honest tables' fit
#audit_clean Circuit.jetPar_ok Circuit.viewT_jet Circuit.ef_mid Circuit.ef_last Circuit.ef_cpu
  Circuit.blindInter_avoids Circuit.terminal_wb2 Circuit.terminal_wb1 Circuit.terminal_cpuCJ Circuit.compJ_chain
  Circuit.compJ_sum Circuit.compJ_transcript Circuit.witT_flag Circuit.CRun.honest_zk

-- LogUp is sound: a polynomial's roots, the fingerprints of Plonky3's buses, the sum of fractions over the
-- distinct messages; tables that do not balance pass the check for few challenges; for the circuit with jets
#audit_clean Circuit.roots_lt Circuit.root_count Circuit.cval_divq Circuit.alpha_count Circuit.npoly_at
  Circuit.group_sum Circuit.group_count Circuit.group_nodup Circuit.kpoly_cval Circuit.kpoly_inj
  Circuit.collide_count Circuit.countOf_mem Circuit.countOf_relabel Circuit.terminals_pts Circuit.logup_sound Circuit.logup_accept Circuit.compJAirs_ok
  Circuit.compJ_logup_sound

-- The hiding PCS's algebraic core: interpolation over F, a column interleaved with random rows opens with one
-- distribution whatever its trace, at points of F and out of domain, one column or many
#audit_clean Circuit.froots_lt Circuit.finterp_eval Circuit.fagree_zero Circuit.fagree Circuit.vsum_shift
  Circuit.vsum_append Circuit.vsum_comm Circuit.mask_hides Circuit.mF_root Circuit.mF_ne Circuit.mask_hides_ood
  Circuit.masks_hide

-- Re-encoding is definable: one closed term takes ⟨t⟩ to ⟨⟨t⟩⟩
#audit_clean Requote.quoteS_elim Requote.quoteK_elim Requote.quoteI_elim Requote.quoteApp_elim
  Requote.R_unroll Requote.R_case Requote.requote Requote.requote_iter

-- Graph reduction with update in place, sound and complete against L1, never more contractions
#audit_clean Graph.Dec.det Graph.dec_spine Graph.spine_dec Graph.spine_ne Graph.dec_update Graph.gstep_sound
  Graph.gstep_inv Graph.gstep_none Graph.grun_sound Graph.grun_halts Graph.grun_mono Graph.grun_le
  Graph.loadT_spec Graph.inv_load Graph.graph_sound Graph.graph_complete Graph.graph_leaf
  Graph.wstep_whnf Graph.wsteps_whnf Graph.graph_spine

-- The read-write memory argument: timestamped multiset balance gives last-write reads, and honest runs balance
#audit_clean RWMem.cnt_le_one RWMem.least RWMem.lastW_of RWMem.left_le_one RWMem.no_double RWMem.rw_step
  RWMem.rw_sound RWMem.cnt_set RWMem.rw_complete

-- The graph machine under the memory argument: one access a step, an accepted trace is the honest run,
-- honest runs are accepted at every budget from the halt, and the accepted trace is unique
#audit_clean GraphMem.ustep_halt GraphMem.sim_some GraphMem.sim_none GraphMem.halts_of_steps
  GraphMem.steps_of_halts GraphMem.expected_memAt GraphMem.accepts_honest GraphMem.accepts_sound
  GraphMem.lastW_congr GraphMem.expected_congr GraphMem.memAt_honest GraphMem.accepts_halted GraphMem.accepts_of_halted GraphMem.accepts_complete
  GraphMem.accepts_unique

-- The masked-column PCS satisfies the transcript simulator's PCS hypothesis exactly
#audit_clean Circuit.sumTo_digitsF Circuit.pcsCloseN_masked

-- The prover's randomness from one seed: counts move from uniform draws to the seed's at the generator's cost
#audit_clean Circuit.sumTo_mulR Circuit.sumTo_bound Circuit.prg_transfer Circuit.transcript_prg

-- Rejecting the non-generic challenges: the transcript at every generic β, without the P^2/P^4 term
#audit_clean Circuit.genB_iff Circuit.sumTo_sumN_zero Circuit.transcript_zkG Circuit.comp_transcriptG
  Circuit.sud_transcriptG Circuit.wit_transcriptG Circuit.compJ_transcriptG Circuit.compP_transcriptG

-- The composed, Sudoku and hidden-term circuits' honest tables meet the transcript theorems' hypotheses
#audit_clean Circuit.comp_honest_zk Circuit.sud_honest_zk Circuit.wit_honest_zk

-- The trace heights in the view: fixed by the statement, emitted by the simulator
#audit_clean Circuit.setBlind_h Circuit.transcript_zkGH Circuit.comp_heights Circuit.sud_heights
  Circuit.wit_heights Circuit.compJ_heights Circuit.compP_heights Circuit.comp_honest_heights
  Circuit.sud_honest_heights Circuit.wit_honest_heights

-- Masked columns of several heights: the openings hide, the PCS meets PCSCloseN exactly, every circuit's transcript has no PCS term
#audit_clean Circuit.masks_hide_multi Circuit.shaped_zero Circuit.pcsCloseN_multi Circuit.transcript_zkG_masked
  Circuit.comp_transcriptG_masked Circuit.sud_transcriptG_masked Circuit.wit_transcriptG_masked
  Circuit.compJ_transcriptG_masked Circuit.compP_transcriptG_masked
#audit_clean Circuit.PCSCloseN.post Circuit.QGroup.ext_OK Circuit.colsAt_openAll Circuit.QGroup.view_quot
  Circuit.pcsCloseN_quot Circuit.transcript_zkG_quot Circuit.comp_transcriptG_quot
  Circuit.sud_transcriptG_quot Circuit.wit_transcriptG_quot Circuit.compJ_transcriptG_quot
  Circuit.compP_transcriptG_quot

-- The quotient's chunks: a polynomial over F through one point of the extension, the chunks hide all but what the
-- verifier recombines, the simulator's canonical chunks, the PCS with chunks, every circuit's transcript
#audit_clean Circuit.M4.sol0 Circuit.M4.sol1 Circuit.M4.sol2 Circuit.M4.sol3 Circuit.solve_spec Circuit.mz_gen_det
  Circuit.interpSZ_spec Circuit.wsumR_vadd Circuit.wsumR_vaddE Circuit.shiftK_spec Circuit.chunks_hide
  Circuit.agree_of_shows Circuit.canon_shows Circuit.chunks_sim Circuit.chunks_recombine Circuit.chunks_recombineE Circuit.csets_sim
  Circuit.pcsCloseN_chunks Circuit.transcript_zkG_chunks Circuit.comp_transcriptG_chunks
  Circuit.sud_transcriptG_chunks Circuit.wit_transcriptG_chunks Circuit.compJ_transcriptG_chunks
  Circuit.compP_transcriptG_chunks
#audit_clean Circuit.sumTo_split Circuit.PCSCloseN.indep Circuit.pcsCloseN_rand
#audit_clean Circuit.ev_add Circuit.ev_smul Circuit.ev_split Circuit.ev_ffold Circuit.fold_formula Circuit.friPath_add
  Circuit.friLast_add Circuit.friView_add Circuit.fri_hides_of_cancel
#audit_clean Circuit.mask_shift_ood Circuit.masks_shift Circuit.masks_shift_multi Circuit.openMulti_eq
  Circuit.openMulti_of_rel Circuit.four_gam Circuit.wcomb_cwShift Circuit.mat_cancel Circuit.cwShift_vanish
  Circuit.cw_rel Circuit.cws_rel Circuit.chunkPolys_rel Circuit.batch_eq Circuit.cwOpen_eq Circuit.fri_hides
#audit_clean Circuit.chunks_shiftV Circuit.chunksView_eq Circuit.vanish_of_open_rel Circuit.vsum_dshift
  Circuit.wsumR_rcomb Circuit.lcv_chunkPoly Circuit.rows_rel Circuit.firstPolys_get Circuit.firstDiffs_get
  Circuit.rcomb_sl Circuit.cwShift_get Circuit.chunkDiffs_get Circuit.cw_entry Circuit.cw_rows
#audit_clean Circuit.csets_shift Circuit.csView_sets Circuit.tab_rel Circuit.relAll_append Circuit.cwRel_append
  Circuit.relAll_of_get Circuit.cwRel_of_get Circuit.pieces_vadd Circuit.tab_all
#audit_clean Circuit.tabs_all Circuit.trace_all Circuit.recOK_canon Circuit.tabsOK_of Circuit.pcsCloseN_fri
  Circuit.PCSCloseN.family Circuit.pcsCloseN_friR Circuit.transcript_zkG_fri Circuit.comp_transcriptG_fri
  Circuit.sud_transcriptG_fri Circuit.wit_transcriptG_fri Circuit.compJ_transcriptG_fri Circuit.compP_transcriptG_fri
#audit_clean Circuit.M4.det_rev Circuit.mz_det_eq Circuit.mz_generic Circuit.generic_ofF_ne Circuit.generic_apow_ne
  Circuit.pcsCloseN_fri_generic Circuit.cset_ok_of_generic Circuit.nongeneric_count
#audit_clean Circuit.PCSCloseN.commit
-- Honest chunks meet RecOK: the recombination is the quotient
#audit_clean Circuit.rpoly_val Circuit.rpoly_on Circuit.rpoly_len Circuit.rpoly_quot Circuit.rpoly_valE
  Circuit.nsum_allL Circuit.nsumE_allL Circuit.shows_of_quot Circuit.shows_of_honest Circuit.shows_congr
  Circuit.recOK_of_honest
-- On cosets the selectors are normalized from each first point
#audit_clean Circuit.fval_coset Circuit.pr_rot Circuit.pr_inv Circuit.coset_const Circuit.opv_congr
  Circuit.sel_of_coset Circuit.quotOK_of_coset

-- Part II's interface with an additive distance: the errors add, the hybrid argument proved
#audit_clean Compose.lsum_le Compose.lsum_add Compose.lsum_const Compose.lsum_comm Compose.lsum_prod
  Compose.lprod_length Compose.CloseD.refl Compose.CloseD.symm Compose.CloseD.trans Compose.CloseD.mono
  Compose.closeD_prod Compose.PSD.aborts_le Compose.composeD Compose.chain2D Compose.chain2D_draws

-- The transcript theorems as the interface's zero knowledge
#audit_clean Circuit.sumTo_lsum Circuit.sumN_lsum Circuit.lsum_tdraws Circuit.closeD_of_transcriptG Circuit.comp_closeD

-- The composed circuit as a PSD, its zero knowledge proved; the jet circuits' honest heights public
#audit_clean Circuit.comp_entries Circuit.assigns_ne Circuit.tdraws_ne Circuit.compPSD Circuit.composeC
  Circuit.compJ_honest_heights Circuit.compP_honest_heights

-- From an accepted witness to an accepted run, within the budget; from a realizer to a proof
#audit_clean Circuit.termAt_of_otermAt Circuit.citer_add Circuit.citer_prefix Circuit.findIdx_least
  Circuit.decode_K Circuit.seg_run Circuit.citer_seg_mono Circuit.citer_seg_lt Circuit.decode_start
  Circuit.crun_heap Circuit.seg_from Circuit.segs Circuit.cend_eq Circuit.acceptsC_of_eval Circuit.crun_fits
  Circuit.crel_of_eval Circuit.same_of_shape Circuit.fillB_leafAt Circuit.build_len Circuit.build_wf
  Circuit.regionOf'_spec Circuit.accepted_run Circuit.realizer_run Circuit.composeC_accepted
  Circuit.composeC_realizer Circuit.or_region Circuit.or_budget Circuit.or_run

-- Fiat–Shamir round by round: adaptive hash calls, grinding, and the LogUp round under them
#audit_clean Circuit.seqSum_const Circuit.seqSum_mono Circuit.seqSum_add Circuit.fs_attempts Circuit.sumTo_pair
  Circuit.sumTo_at_zero Circuit.grind_count Circuit.logup_fs

-- Composed statements with ∃ over a hidden witness and knowledge implication through certified witness maps
#audit_clean Compose.close_inpO Compose.fmX_red Compose.phi_iffX Compose.leaf_iffX Compose.leaf_pathX
  Compose.readBackX_real Compose.real_of_acceptedX Compose.leaves_prefixX Compose.clear_shapeX
  Compose.clear_leavesX Compose.inp_red Compose.good_lift Compose.good_of_realX Compose.accepted_of_goodX
  Compose.accepted_of_realX Compose.composeX Compose.fst_real Compose.snd_real Compose.swap_real
  Compose.inl_real Compose.inr_real Compose.XS.cert Compose.real_of_acceptedXS
  CompM.shape_of_sameX CompM.checkCX_realizes
  ComposeXEx.exEq_accepts ComposeXEx.exEq_real ComposeXEx.exEq_refuses ComposeXEx.fstAnd_accepts
  ComposeXEx.fstAnd_real ComposeXEx.inlNeg_accepts ComposeXEx.inlNeg_real

-- Incremental composition without recursion: chains of proofs over public hand-offs
#audit_clean Chain.ofEval Chain.chain2 Chain.chain2_knowledge Chain.chain3_rel Chain.chainX_real Chain.chainX_knowledge
  ChainEx.stage₁_accepts ChainEx.stage₂_accepts ChainEx.chain_real ChainEx.stage₁_refuses_other

-- Data jets: the contract, closing to an implementation, Poseidon2's specification, a hidden hand-off
#audit_clean DataJet.JStep.close DataJet.JSteps.close DataJet.real_of_jet DataJet.respects_of_inj
  DataJet.notP_implements DataJet.bitsT_inj DataJet.stateT_inj DataJet.poseidon2_respects
  DataJet.hidden_chain Poseidon2.permute_matches

-- The checks of the provers' traces against Lean's tables: each view's blinding blocks as data,
-- a bus's counts in one pass, a jet run's lookup counts from its instantiations listed once
#audit_clean Circuit.compViewN_blocks Circuit.sudView_blocks Circuit.witView_blocks Circuit.compJViewN_blocks
  Circuit.compPViewN_blocks Circuit.sumMatch_append Circuit.tableSends_eq Circuit.multStep_get Circuit.multArr_go
  Circuit.multArr_get Circuit.memTable5_mult Circuit.memTableC_mult Circuit.sumTo_filterMap Circuit.sumTo_filterMap'
  Circuit.JRun.cntRoots_eq Circuit.JRun.cntHdr_eq Circuit.JRun.cntTmpl_eq Circuit.firstOcc_arr
  Circuit.TraceCheck.getD_toList

-- Every CPU row compared: each circuit's honest CPU row, its memory read from an array
#audit_clean Circuit.kindOf_G Circuit.addrAt_G Circuit.fieldsAt_G Circuit.rangeValue_G Circuit.cpuCol_G
  Circuit.foldl_cntS Circuit.cntArr_get Circuit.cpuColW_arr Circuit.cpuColC_G Circuit.cpuColC_arr
  Circuit.jetOf_G Circuit.JRun.instAt_G Circuit.JRun.cpuCol_G Circuit.JRun.insts_arr Circuit.CRun.cpuColCJ_arr
  P2Jet.boolAt_G P2Jet.bitsAt_G P2Jet.slotsOK_G P2Jet.popN_G P2Jet.take_G P2Jet.p2Row_G
  Circuit.P2Run.jetAt_G Circuit.P2Run.jetRange_G Circuit.P2Run.cpuColP_arr

-- Poseidon2's specification: the paper's construction with Plonky3's parameters, its constants
-- the Grain LFSR's, its S-box and linear layers invertible
#audit_clean Poseidon2.Grain.rc_grain Poseidon2.Lin.dotF_unitL Poseidon2.Lin.dotF_addL
  Poseidon2.Lin.dotF_scaleL Poseidon2.Lin.lin_length Poseidon2.Lin.lin_sound Poseidon2.Lin.linRow_sound
  Poseidon2.Lin.linRows_sound Poseidon2.Lin.dot_dotF Poseidon2.Lin.matVec_rows Poseidon2.Lin.matVec_eval
  Poseidon2.Generic.plonky3_ok Poseidon2.Generic.linRows_ext Poseidon2.Generic.linRows_int
  Poseidon2.Generic.extLinear_eq Poseidon2.Generic.intLinear_eq Poseidon2.Generic.foldl_full
  Poseidon2.Generic.foldl_partial Poseidon2.Generic.permute_plonky3
  Poseidon2.Inv.gcd_7 Poseidon2.Inv.seven_e Poseidon2.Inv.pow_cycles Poseidon2.Inv.sboxInv_sbox
  Poseidon2.Inv.sbox_sboxInv Poseidon2.Inv.sbox_bijective Poseidon2.Inv.inv_of_rows
  Poseidon2.Inv.ext_inv Poseidon2.Inv.int_inv Poseidon2.Inv.extLinear_inv Poseidon2.Inv.intLinear_inv

-- Binary arithmetic in SKI, and Poseidon2 in SKI implementing the data jet
#audit_clean BitArith.wnf_sound BitArith.run BitArith.theta_unfold BitArith.add_spec BitArith.mul_spec
  BitArith.lt_spec BitArith.sub_spec BitArith.mod_step BitArith.mod_spec BitArith.mod_two_mul
  BitArith.val_bitsOf BitArith.val_lit BitArith.RepR.add BitArith.RepR.mul BitArith.RepR.mod BitArith.RepR.pow7
  Poseidon2SKI.extRound_split Poseidon2SKI.intRound_split Poseidon2SKI.bridge_sbox Poseidon2SKI.bridge_mat4
  Poseidon2SKI.bridge_mix Poseidon2SKI.bridge_sbox0 Poseidon2SKI.bridge_intLin Poseidon2SKI.comp_ok
  Poseidon2SKI.extL_ok Poseidon2SKI.intL_ok Poseidon2SKI.Ex.comp_spec Poseidon2SKI.layer_ok Poseidon2SKI.inK_spec
  Poseidon2SKI.outK_spec Poseidon2SKI.inS_spec Poseidon2SKI.outS_spec Poseidon2SKI.chain_ok
  Poseidon2SKI.rounds_ok Poseidon2SKI.rounds_fold Poseidon2SKI.P_spec Poseidon2SKI.poseidon2_implements
  DataJet.poseidon2_spec

-- The Poseidon2 table: every row whose constraints vanish computes the permutation
#audit_clean P2Air.evalF_ofN P2Air.toE_eval P2Air.eval_subst P2Air.bridge_ext P2Air.lin_ok P2Air.round_ok
  P2Air.gen_ok P2Air.rounds_spec P2Air.p2_sound P2Air.p2_sound_row
  DataJet.CSteps.close DataJet.real_of_cjet Poseidon2SKI.permute_len Poseidon2SKI.P_specN
  Poseidon2SKI.Pbits_implements Poseidon2SKI.poseidon2B_respects

-- The Poseidon2 jet in the machine, and composed statements that use it
#audit_clean P2Jet.boolAt_cases P2Jet.boolAt_ot P2Jet.bitsAt_ptrs P2Jet.bitsAt_length P2Jet.slot_ot P2Jet.push_ot
  P2Jet.pushR_length P2Jet.CStep.appL P2Jet.p2Row_cstep P2Jet.p2Row_ctr_len
  CompM.build_obuild CompM.addStmts_eq CompM.addStmtsO_spec CompM.addStmtsO_ext CompM.cHeap_eq CompM.cMachine_eq
  CompM.cMachineO_decode CompM.owstep_cstep CompM.CSteps.trans CompM.owsteps_csteps CompM.bitsAt_append
  CompM.bitsAt_det CompM.combAt_ext CompM.combAt_take CompM.normRowP_spec CompM.AcceptsCP.within
  CompM.AcceptsCP.within_ctr CompM.AcceptsCP.runs CompM.composedP_sound_of CompM.pbuild_len CompM.combRoot_public
  CompM.fill_comb CompM.range'_shift CompM.slots_bits CompM.comb_heap CompM.composedP_sound
  Poseidon2SKI.poseidon2Comb_encI Poseidon2SKI.poseidon2Comb_encO Poseidon2SKI.poseidon2Comb_spec
  Poseidon2SKI.spreadT_spec Poseidon2SKI.Pcomb_implements P2Air.permute_mod P2Air.permute_lt

-- The circuit with the Poseidon2 jet: accepted tables are a run AcceptsCP accepts
#audit_clean CompM.obuild_pbuild CompM.addStmtsO_shape CompM.cMachineO_public
  Circuit.kind_ofP2 Circuit.kindOKP_all Circuit.kind_factsP Circuit.sel_sumP2 Circuit.next_regsP2 Circuit.p2_pinsP
  Circuit.CompPOK.memHit Circuit.CompPOK.segHit Circuit.CompPOK.idxHit Circuit.CompPOK.read Circuit.CompPOK.step
  Circuit.CompPOK.halt Circuit.CompPOK.ctr_eq Circuit.CompPOK.next_ctr Circuit.CompPOK.jet_key_unique
  Circuit.CompPOK.jetReads Circuit.CompPOK.jetNext Circuit.CompPOK.pinConserve Circuit.CompPOK.poutConserve
  Circuit.CompPOK.pinPath Circuit.CompPOK.poutPath Circuit.CompPOK.pinLevel Circuit.CompPOK.poutLevel
  Circuit.accum Circuit.lowhi Circuit.canon Circuit.CompPOK.pinSlot Circuit.CompPOK.poutWrite
  Circuit.CompPOK.p2vCount Circuit.CompPOK.p2Unique Circuit.CompPOK.p2wMatch Circuit.CompPOK.pinVals
  Circuit.CompPOK.poutVals Circuit.CompPOK.poutCells Circuit.CompPOK.jetOut Circuit.CompPOK.jetRow
  Circuit.cMachineO_fitsB Circuit.CompPOK.heap0 Circuit.CompPOK.regionWF Circuit.CompPOK.restart
  Circuit.CompPOK.normRow Circuit.CompPOK.acceptsCP Circuit.compPOK_ofG Circuit.verifierO_occ Circuit.compPExportG_sound
  Circuit.compPExport_sound

-- What a proof of p2pre h proves: a Poseidon2 preimage
#audit_clean P2Pre.thetaK_absorbs P2Pre.thetaK_not_K P2Pre.chk_sound P2Pre.env_J P2Pre.p2pre_meaning
  Circuit.p2preExport_sound

-- What a proof of p2commit c pat proves, and the hidden hand-off over one commitment
#audit_clean P2Commit.chkX_sound P2Commit.absorbX_steps P2Commit.selT_sound P2Commit.patO_sound
  P2Commit.cbits_inj P2Commit.p2commit_meaning P2Commit.verifierC_occ P2Commit.value_bits P2Commit.value_lt
  P2Commit.openB_commit P2Commit.handoff Circuit.p2commitExport_sound Circuit.p2commit_chain
  P2Commit.valueOnlyB_sound P2Commit.canonicalB_sound P2Commit.ok_commit P2Commit.chainB_sound
  Circuit.p2commit_chainB

-- The jet's verifiers accept honest bits
#audit_clean P2Complete.absorbO_K P2Complete.chk_complete P2Complete.chkX_complete P2Complete.selT_complete
  P2Complete.patO_complete P2Complete.jet_step P2Complete.p2pre_complete P2Complete.p2commit_complete

-- The verifiers with the Poseidon2 jet call it exactly once
#audit_clean P2Jet.p2Row_step P2Jet.p2Row_cstep Circuit.CompPOK.normRowSel P2Once.outer_step P2Once.outer_steps
  P2Once.outer_occ P2Once.outer_jet P2Once.partP P2Once.partC P2Once.verifierO_eq P2Once.verifierC_eq
  P2Once.once_of Circuit.compP_once Circuit.p2pre_once Circuit.p2commit_once

-- The honest tables of the circuit with the Poseidon2 jet: balance and clear flags
#audit_clean CompM.AcceptsC.runC Circuit.p2Row_inv Circuit.p2Row_halt Circuit.P2Run.runC
  Circuit.P2Run.plain_row Circuit.P2Run.jetAt_spec Circuit.P2Run.cpuP_env_plain Circuit.P2Run.cpuP_honest
  Circuit.P2Run.cpuP_segs Circuit.P2Run.segsTableP Circuit.P2Run.cpuP_blindZero Circuit.accN_succ Circuit.lowL_succ
  Circuit.hiL_succ Circuit.pin_sends Circuit.pout_sends Circuit.sum_elems Circuit.acc_last Circuit.pin_p2i_call
  Circuit.pin_idx_call Circuit.pin_p2v_call Circuit.pout_p2o_call Circuit.pout_idx_call Circuit.pout_p2w_call
  Circuit.traceAll_last Circuit.rounds_len Circuit.p2RowT_get Circuit.p2_sends_v Circuit.p2_sends_w
  Circuit.honest_ofRows Circuit.pushR_get Circuit.P2Run.pin_honest Circuit.P2Run.pout_honest Circuit.witTP_honest
  Circuit.P2Run.cpuP_p2i Circuit.P2Run.cpuP_p2o Circuit.chunk_out Circuit.P2Run.bal_p2i Circuit.P2Run.bal_p2o
  Circuit.P2Run.bal_p2v Circuit.P2Run.bal_p2w Circuit.P2Run.calls_sum Circuit.P2Run.cpuP_segsHonest
  Circuit.idx_sends Circuit.P2Run.bal_p2idx Circuit.P2Run.balancedP Circuit.P2Run.honest_zkP Circuit.filter_one
  Circuit.P2Run.calls_one Circuit.P2Run.honest_zk_one Circuit.P2Run.honest_zk_p2pre Circuit.P2Run.honest_zk_p2commit

-- Completeness of the circuit with the Poseidon2 jet: each honest table satisfies its AIR
#audit_clean Circuit.eval_cur Circuit.env_pre0 Circuit.witCons_cur Circuit.witCons_zero Circuit.witP_sat
  Circuit.sat_ofRows Circuit.bF_bool Circuit.bF_toNat Circuit.p2in_cur Circuit.p2in_zero Circuit.pinRow_cons
  Circuit.ofN_sub_of_le Circuit.bitsOf_getD Circuit.two27 Circuit.canon_bits Circuit.bF_or_and Circuit.bF_and_or
  Circuit.p2out_cur Circuit.p2out_zero Circuit.outBits_bit Circuit.out_canon Circuit.poutRow_cons Circuit.allZ_app
  Circuit.allZ_mem Circuit.range_map_getD Circuit.mapEval_getD Circuit.ev_cols Circuit.lin_zero Circuit.cube_ofN
  Circuit.triple_get Circuit.round_zero Circuit.gen_zero Circuit.p2RowT_eq Circuit.p2Pad_eq Circuit.epow_cur
  Circuit.toE_cur Circuit.stE_cur Circuit.colsFrom_cur Circuit.lcur_app Circuit.lin_cur Circuit.round_cur
  Circuit.gen_cur Circuit.p2Cons_cur Circuit.p2Row_cons Circuit.sat_ofRows_full Circuit.P2Run.pin_sat
  Circuit.P2Run.pout_sat Circuit.P2Run.p2_sat Circuit.P2Run.c_vals Circuit.P2Run.colP_eq Circuit.P2Run.colP_reg
  Circuit.P2Run.colP_hd Circuit.P2Run.colP_stk Circuit.P2Run.colP_ctr Circuit.P2Run.colP_cnt Circuit.P2Run.colP_rs
  Circuit.P2Run.colP_root Circuit.P2Run.colP_blind Circuit.P2Run.colP_p2flag Circuit.P2Run.colP_fld
  Circuit.P2Run.kindP_isKind Circuit.P2Run.rowP_stepP Circuit.P2Run.cvC Circuit.P2Run.cpuC_nextP
  Circuit.P2Run.rd_lt Circuit.P2Run.jet_row Circuit.P2Run.colP_bit Circuit.P2Run.colP_jetBit
  Circuit.P2Run.bool_mod2 Circuit.P2Run.range_zero Circuit.P2Run.readX_now Circuit.P2Run.cpuP_read
  Circuit.P2Run.last_kindCfP Circuit.P2Run.kindSumP_all Circuit.P2Run.nextHd_now Circuit.P2Run.nextStk_now
  Circuit.P2Run.nextCtr_now Circuit.P2Run.last_plain Circuit.P2Run.cpuP_sat Circuit.idx_sat Circuit.idx_pre
  Circuit.witRowsP_le Circuit.witRowsP_512 CompM.AcceptsCP.ctr_le CompM.AcceptsCP.stk_le
  Circuit.compPG_complete_log Circuit.compP_complete_log
  Circuit.runP_calls_one Circuit.compPC_complete_log

-- Zero knowledge of the circuit with the Poseidon2 jet: the blinding tree CPU —c— P2IN —d— P2OUT —e— P2
#audit_clean Circuit.viewT_p2 Circuit.terminal_cpuP2 Circuit.p2_avoids Circuit.compP_chain Circuit.compP_sum
  Circuit.compP_transcript Circuit.pinB_sends Circuit.poutB_sends Circuit.p2B_sends Circuit.tableSends_withBlocks

-- A poke whose event is an entropy reply, its bits private: the predicate circuit's bits
-- become Avon's reply [0 [id bits]], and the kernel is poked with it
#audit_clean Entropy.hd_red Entropy.tl_red Entropy.pairT_cong Entropy.consT_cong Entropy.convT_one
  Entropy.convT_succ Entropy.convT_red Entropy.entropyV_red Entropy.entropyV_iff Entropy.entropyV_iff'
  Circuit.entropyExport_sound Circuit.checkEntropy_sound
