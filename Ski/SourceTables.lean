import Ski.Adequacy
import Ski.Examples
open Term Front

/-!
# The four source texts meet the adequacy hypotheses

For each compilation `skijack` compiled (`Ski/Source.lean`), the source
program the front end reads has the table's structure and its compiled
globals are the table's terms (`*.adequate`, one kernel check each), and
`kernel_fixed` and its siblings give `Fixed`.  So `exact_iff` and
`diverges_iff_source` hold for every valid program and stack over each of
the four tables.  Two instances: the source of `3 sumto` reaches `[6]`,
and the source of `[dup i] dup i` reaches no outcome.
-/

theorem NoQuot.adequate :
    JoyProg (progOf kernelText) NoQuot.table ∧ GenvTable (genvOf kernelText) NoQuot.table :=
  of_tableCheck (kernel_mono kernelDefs_sources.1) (by decide +kernel)

theorem CorpusTable.adequate :
    JoyProg (progOf corpusText) CorpusTable.table ∧ GenvTable (genvOf corpusText) CorpusTable.table :=
  of_tableCheck (kernel_mono kernelDefs_sources.2.1) (by decide +kernel)

theorem LoopTable.adequate :
    JoyProg (progOf loopText) LoopTable.table ∧ GenvTable (genvOf loopText) LoopTable.table :=
  of_tableCheck (kernel_mono kernelDefs_sources.2.2.1) (by decide +kernel)

theorem SumTable.adequate :
    JoyProg (progOf sumText) SumTable.table ∧ GenvTable (genvOf sumText) SumTable.table :=
  of_tableCheck (kernel_mono kernelDefs_sources.2.2.2) (by decide +kernel)

/-- **`3 sumto` at the source.**  Its source program, read from the text
    `skijack` compiled, reaches `[6]` in the source semantics, and that is
    the only outcome it reaches, the compiled program's, and `Run`'s. -/
theorem SumTable.source_six :
    SSteps (progOf sumText)
      (srcRun [.lit 3, .quote (.stat 0), .quote (.stat 1), .swap, .cat, .dup, .cons, .i] [])
      (outS (.val [.num 6])) :=
  run_source SumTable.adequate.1 SumTable.cs_run

theorem SumTable.source_exact (o : Outcome) (ho : o.ok SumTable.table.n = true) :
    SSteps (progOf sumText)
      (srcRun [.lit 3, .quote (.stat 0), .quote (.stat 1), .swap, .cat, .dup, .cons, .i] []) (outS o) ↔
      o = .val [.num 6] := by
  letI : Kit := SumTable.table.kit
  haveI : KitElim := SumTable.table.kit_elim
  constructor
  · intro h
    have hr := run_of_source SumTable.table_valid SumTable.adequate.1 sum_fixed SumTable.adequate.2
      rfl rfl ho h
    cases Table.program_apply SumTable.table_valid hr rfl (encStack_dec [] rfl) with
    | intro u hu =>
      cases Table.program_apply SumTable.table_valid SumTable.cs_run rfl (encStack_dec [] rfl) with
      | intro u' hu' =>
        have e := Eval.deterministic hu.1 hu'.1
        rw [← e] at hu'
        exact Decodes.functional hu.2 hu'.2
  · intro e
    rw [e]
    exact SumTable.source_six

/-- **`[dup i] dup i` at the source reaches no outcome**: the compiled
    program diverges, so by `diverges_iff_source` its source does too. -/
theorem LoopTable.source_diverges (o : Outcome) :
    ¬ SSteps (progOf loopText) (srcRun [.quote (.stat 0), .dup, .i] []) (outS o) :=
  (diverges_iff_source LoopTable.table_valid LoopTable.adequate.1 loop_fixed LoopTable.adequate.2
    rfl rfl).mp (by rw [← LoopTable.cloop_eq]; exact LoopTable.cloop_diverges) o
