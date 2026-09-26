import Ski.Table
import Ski.Total
import Ski.Programs
open Term

/-!
# End to end

Corpus programs as `skijack` compiles them, run on the empty stack with
their table's compiled `applyU`: each compiled term reduces to a weak head
normal form that decodes to the stack the C model derives.  The `c*_eq`
facts of `Ski/Table.lean` identify each compiled term with the kernel's
compilation of its words (`Table.progT`); `Table.program_apply` and
`Table.program_diverges` (`Ski/Programs.lean`) do the rest, for every
program over every valid table.

`3 [dup +] i` and `1 2 over` run static quotations: `apply` reaches the
table's constructor for `[dup +]` or `[dup]` and runs its compiled body.

Static bodies are where code enters, and with it divergence.
`LoopTable.cloop_diverges` is the witness: `[dup i] dup i`, as `skijack`
compiles it, never reaches a weak head normal form, because its static
quotation's body runs a quotation.  Joy's `y` builds that loop from data
and bounds it: `SumTable.us_six` runs `3 sumto` to `[6]`.  `CorpusTable.omega_diverges` is a
second, weaker witness: its quotation `Ω` is written in by hand as a
runtime value, not emitted by the compiler, and no Joy program over the
corpus table builds it (`cat` produces `then` only as the tail of a
`cons`; an informal argument, not proved here).
-/

namespace NoQuot

/-- `1 2 + dup +` decodes to `[6]`. -/
theorem up_six : Contract (cp ⬝ Kit.applyU ⬝ encStack []) (.val [.num 6]) := by
  rw [cp_eq]
  exact Table.program_apply table_valid
    (.seq_val (.plain rfl) (.seq_val (.plain rfl) (.seq_val (.plain rfl)
      (.seq_val (.plain rfl) (.seq_val (.plain rfl) (.nil _))))))
    rfl (encStack_dec [] rfl)

/-- `[1] i`, a quotation built from data. -/
theorem quote_i : Contract
    (N Kit.applyU [.quote (.unit (.num 1)), .i] ⬝ encStack []) (.val [.num 1]) :=
  composition_apply (.seq_val (.plain rfl) (.seq_val (.i_run .unit) (.nil _)))
    rfl (compiles_N _ _) (encStack_dec [] rfl)

/-- `[1] [2] cat i`: `apply` runs the concatenation through `then`. -/
theorem cat_i : Contract
    (N Kit.applyU [.quote (.unit (.num 1)), .quote (.unit (.num 2)), .cat, .i] ⬝ encStack [])
    (.val [.num 2, .num 1]) :=
  composition_apply
    (.seq_val (.plain rfl) (.seq_val (.plain rfl) (.seq_val (.plain rfl)
      (.seq_val (.i_run (.cons (.then_val .unit .unit))) (.nil _)))))
    rfl (compiles_N _ _) (encStack_dec [] rfl)

end NoQuot

namespace CorpusTable

/-- `3 [dup +] i` decodes to `[6]`: `i` runs the static quotation `[dup +]`. -/
theorem uq_six : Contract (cq ⬝ Kit.applyU ⬝ encStack []) (.val [.num 6]) := by
  rw [cq_eq]
  exact Table.program_apply table_valid
    (.seq_val (.plain rfl) (.seq_val (.plain rfl)
      (.seq_val (.i_run (.stat (k := 0) (by decide)
        (.seq_val (.plain rfl) (.seq_val (.plain rfl) (.nil _))))) (.nil _))))
    rfl (encStack_dec [] rfl)

/-- `1 2 over`, that is `1 2 [dup] dip swap`, decodes to `[1, 2, 1]`. -/
theorem ur_over : Contract (cr ⬝ Kit.applyU ⬝ encStack []) (.val [.num 1, .num 2, .num 1]) := by
  rw [cr_eq]
  exact Table.program_apply table_valid
    (.seq_val (.plain rfl) (.seq_val (.plain rfl) (.seq_val (.plain rfl)
      (.seq_val (.dip_run (.stat (k := 1) (by decide) (.seq_val (.plain rfl) (.nil _))))
        (.seq_val (.plain rfl) (.nil _))))))
    rfl (encStack_dec [] rfl)

/-- A quotation that runs itself: push the static `[dup]`, run it, then run
    the copy of `Ω` it made.  `[Ω] dup i` loops.  `Ω` is a runtime value
    written in by hand; the compiler emits only static quotations. -/
def Ω : Quotation := .cons (.quot (.stat 1)) (.then (.then (.unit (.num 0))))

theorem stat1_run {o : Outcome} (h : Run (.quot (.stat 1)) [.quot Ω] o) :
    o = .val [.quot Ω, .quot Ω] := by
  cases h with
  | stat _ hb =>
    have hb : Run (.prog [.dup]) [.quot Ω] o := hb
    cases hb with
    | seq_val hw hp =>
      cases hp
      cases hw with
      | plain _ => rfl
    | seq_err hw => cases hw

/-- No derivation passes through `Ω` on `[Ω]`, nor through the two states
    its run visits on the way back to it. -/
theorem omega_loop {j : Job} {S : Stack} {o : Outcome} (h : Run j S o) :
    (j = .quot Ω → S = [.quot Ω] → False) ∧
    (j = .quot (.then (.then (.unit (.num 0)))) → S = [.quot (.stat 1), .quot Ω] → False) ∧
    (j = .quot (.then (.unit (.num 0))) → S = [.quot Ω, .quot Ω] → False) := by
  induction h with
  | cons _ ih =>
    refine And.intro (fun e hS => ?_) (And.intro (fun e _ => by cases e) (fun e _ => by cases e))
    cases e
    subst hS
    exact ih.2.1 rfl rfl
  | then_val h1 _ ih1 ih2 =>
    refine And.intro (fun e _ => by cases e) (And.intro (fun e hS => ?_) (fun e hS => ?_))
    · cases e
      cases hS
      cases stat1_run h1
      exact ih2.2.2 rfl rfl
    · cases e
      cases hS
      exact ih1.1 rfl rfl
  | then_err h1 ih1 =>
    refine And.intro (fun e _ => by cases e) (And.intro (fun e hS => ?_) (fun e hS => ?_))
    · cases e
      cases hS
      cases stat1_run h1
    · cases e
      cases hS
      exact ih1.1 rfl rfl
  | then_bad hb =>
    refine And.intro (fun e _ => by cases e) (And.intro (fun _ hS => hb _ _ hS) (fun _ hS => hb _ _ hS))
  | stat => exact And.intro (fun e _ => by cases e) (And.intro (fun e _ => by cases e) (fun e _ => by cases e))
  | unit => exact And.intro (fun e _ => by cases e) (And.intro (fun e _ => by cases e) (fun e _ => by cases e))
  | _ => exact And.intro (fun e _ => by cases e) (And.intro (fun e _ => by cases e) (fun e _ => by cases e))

theorem omega_no_run (o : Outcome) : ¬ Run (.prog [.quote Ω, .dup, .i]) [] o := by
  intro h
  cases h with
  | seq_err hw => cases hw
  | seq_val hw hp =>
    cases hw with
    | plain _ =>
      cases hp with
      | seq_err hw2 => cases hw2
      | seq_val hw2 hp2 =>
        cases hw2 with
        | plain _ =>
          cases hp2 with
          | seq_err hw3 =>
            cases hw3 with
            | plain hh => cases hh
            | i_run hr => exact (omega_loop hr).1 rfl rfl
            | i_bad hb => exact hb _ _ rfl
          | seq_val hw3 _ =>
            cases hw3 with
            | i_run hr => exact (omega_loop hr).1 rfl rfl

/-- `N` of `[Ω] dup i` over the corpus table diverges: `Run` derives
    nothing, so by `composition_diverges` the term never reaches a weak head
    normal form.  The program is not `skijack` output (see
    `LoopTable.cloop_diverges` for one that is). -/
theorem omega_diverges : Diverges (N Kit.applyU [.quote Ω, .dup, .i] ⬝ encStack []) :=
  (composition_diverges rfl (compiles_N _ _) (encStack_dec [] rfl)).2 omega_no_run

end CorpusTable

namespace LoopTable

/-- No derivation passes through the static `[dup i]` on `[[dup i]]`, nor
    through the states its body visits on the way back to it. -/
theorem loop_run {j : Job} {S : Stack} {o : Outcome} (h : Run j S o) :
    (j = .quot (.stat 0) → S = [.quot (.stat 0)] → False) ∧
    (j = .prog [.dup, .i] → S = [.quot (.stat 0)] → False) ∧
    (j = .prog [.i] → S = [.quot (.stat 0), .quot (.stat 0)] → False) ∧
    (j = .word .i → S = [.quot (.stat 0), .quot (.stat 0)] → False) := by
  induction h with
  | stat _ _ ih =>
    refine And.intro (fun e hS => ?_) (And.intro (fun e _ => by cases e)
      (And.intro (fun e _ => by cases e) (fun e _ => by cases e)))
    cases e
    subst hS
    exact ih.2.1 rfl rfl
  | seq_val hw _ ihw ihp =>
    refine And.intro (fun e _ => by cases e) (And.intro (fun e hS => ?_)
      (And.intro (fun e hS => ?_) (fun e _ => by cases e)))
    · cases e
      subst hS
      cases hw with
      | plain _ => exact ihp.2.2.1 rfl rfl
    · cases e
      subst hS
      exact ihw.2.2.2 rfl rfl
  | seq_err hw ihw =>
    refine And.intro (fun e _ => by cases e) (And.intro (fun e hS => ?_)
      (And.intro (fun e hS => ?_) (fun e _ => by cases e)))
    · cases e
      subst hS
      cases hw
    · cases e
      subst hS
      exact ihw.2.2.2 rfl rfl
  | i_run _ ih =>
    refine And.intro (fun e _ => by cases e) (And.intro (fun e _ => by cases e)
      (And.intro (fun e _ => by cases e) (fun _ hS => ?_)))
    cases hS
    exact ih.1 rfl rfl
  | i_bad hb =>
    exact And.intro (fun e _ => by cases e) (And.intro (fun e _ => by cases e)
      (And.intro (fun e _ => by cases e) (fun _ hS => hb _ _ hS)))
  | plain hho =>
    refine And.intro (fun e _ => by cases e) (And.intro (fun e _ => by cases e)
      (And.intro (fun e _ => by cases e) (fun e _ => ?_)))
    cases e
    cases hho
  | _ =>
    exact And.intro (fun e _ => by cases e) (And.intro (fun e _ => by cases e)
      (And.intro (fun e _ => by cases e) (fun e _ => by cases e)))

theorem loop_no_run (o : Outcome) : ¬ Run (.prog [.quote (.stat 0), .dup, .i]) [] o := by
  intro h
  cases h with
  | seq_err hw => cases hw
  | seq_val hw hp =>
    cases hw with
    | plain _ => exact (loop_run hp).2.1 rfl rfl

/-- **A compiled program that diverges.**  `[dup i] dup i`, as `skijack`
    compiles it (`cloop`), run with its table's compiled `applyU` on the
    empty stack: `Run` derives nothing, so by `composition_diverges` the
    term never reaches a weak head normal form. -/
theorem cloop_diverges : Diverges (cloop ⬝ Kit.applyU ⬝ encStack []) := by
  rw [cloop_eq]
  exact (Table.program_diverges table_valid rfl (encStack_dec [] rfl)).2 loop_no_run

end LoopTable

namespace SumTable

/-- **Joy's recursion, end to end.**  The corpus row `3 sumto`, as `skijack`
    compiles it with its own table, reaches a weak head normal form that
    decodes to `[6]`: `sumto` is `[swap [pop 0] [dup [swap i] dip 1 + +]
    ifz] y`, and `y` is Kerby's `[dup cons] swap cat dup cons i`, so the
    run builds `cons`, `cat` and `then` quotations and runs them by `i`,
    `dip` and `ifz`.  Nothing here is specific to the program but its
    derivation (`cs_run`) and `skijack`'s terms (`cs_eq`, `table_*`). -/
theorem us_six : Contract sumto_us (.val [.num 6]) := by
  rw [sumto_us_eq, cs_eq]
  exact Table.program_apply table_valid cs_run rfl (encStack_dec [] rfl)

/-- Whatever `3 sumto` normalizes to decodes to `[6]` and nothing else. -/
theorem us_exact {u : Term} {o : Outcome} (he : Eval sumto_us u) (hd : Decodes u o) :
    o = .val [.num 6] := by
  cases us_six with
  | intro u' hu' =>
    have e := Eval.deterministic he hu'.1
    rw [← e] at hu'
    exact Decodes.functional hd hu'.2

end SumTable
