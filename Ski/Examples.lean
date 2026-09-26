import Ski.Table
import Ski.Total
open Term

/-!
# End to end

Corpus programs as `skijack` compiles them, run on the empty stack with
their table's compiled `applyU`: each compiled term reduces to a weak head
normal form that decodes to the stack the C model derives.  The
`*_compiles` facts of `Ski/Table.lean` identify each compiled term with
its words; `composition_apply` does the rest.

`3 [dup +] i` and `1 2 over` run static quotations: `apply` reaches the
table's constructor for `[dup +]` or `[dup]` and runs its compiled body.
Static bodies are where code enters, and with it divergence: `omega_diverges`
is a program over the corpus table whose compiled term provably diverges.
-/

namespace NoQuot

/-- `1 2 + dup +` decodes to `[6]`. -/
theorem up_six : Contract (cp ⬝ Kit.applyU ⬝ encStack []) (.val [.num 6]) :=
  composition_apply
    (.seq_val (.plain rfl) (.seq_val (.plain rfl) (.seq_val (.plain rfl)
      (.seq_val (.plain rfl) (.seq_val (.plain rfl) (.nil _))))))
    rfl (cp_compiles _) (encStack_dec [] rfl)

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
theorem uq_six : Contract (cq ⬝ Kit.applyU ⬝ encStack []) (.val [.num 6]) :=
  composition_apply
    (.seq_val (.plain rfl) (.seq_val (.plain rfl)
      (.seq_val (.i_run (.stat (k := 0) (by decide)
        (.seq_val (.plain rfl) (.seq_val (.plain rfl) (.nil _))))) (.nil _))))
    rfl (cq_compiles _) (encStack_dec [] rfl)

/-- `1 2 over`, that is `1 2 [dup] dip swap`, decodes to `[1, 2, 1]`. -/
theorem ur_over : Contract (cr ⬝ Kit.applyU ⬝ encStack []) (.val [.num 1, .num 2, .num 1]) :=
  composition_apply
    (.seq_val (.plain rfl) (.seq_val (.plain rfl) (.seq_val (.plain rfl)
      (.seq_val (.dip_run (.stat (k := 1) (by decide) (.seq_val (.plain rfl) (.nil _))))
        (.seq_val (.plain rfl) (.nil _))))))
    rfl (cr_compiles _) (encStack_dec [] rfl)

/-- A quotation that runs itself: push the static `[dup]`, run it, then run
    the copy of `Ω` it made.  `[Ω] dup i` loops. -/
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

/-- **A compiled program that diverges.**  `[Ω] dup i` over the corpus
    table: `Run` derives nothing, so by `composition_diverges` the compiled
    term never reaches a weak head normal form. -/
theorem omega_diverges : Diverges (N Kit.applyU [.quote Ω, .dup, .i] ⬝ encStack []) :=
  (composition_diverges rfl (compiles_N _ _) (encStack_dec [] rfl)).2 omega_no_run

end CorpusTable
