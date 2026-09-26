import Ski.Converse
import Ski.Laws
open Term

set_option linter.unusedSectionVars false

/-!
# Every program, over every table

G6 of `PLAN.md` §3.  A program's compiled term is `Table.progT p`, the
kernel's compilation of its words (`Ski/Kernel.lean`), which takes the
table's `applyU` and then the stack.  Over every valid table, for every
program valid over it and every stack term that decodes:

- `Table.program_apply`: a derivation of `Run` is realized by the
  compiled term;
- `Table.program_diverges`: the compiled term diverges exactly when `Run`
  derives no outcome;
- `Table.program_exact`: whatever the compiled term normalizes to decodes
  to an outcome `Run` derives.

No hypothesis names a particular program or table beyond its validity.
The instances are `Table.kit` and the laws of `Ski/Laws.lean`, and the
program's compiled form comes from `progT_wsteps`, which reduces
`progT p ⬝ ap ⬝ s` weakly to `N ap p ⬝ s`, so no per-program `Compiles`
proof is needed.  Divergence, contracts and decoding transfer along that
weak reduction (`diverges_iff_of_wsteps`, `Contract.of_wsteps`).
`skijack`'s term for each generated program is `progT` of its words by
`rfl` (`c*_eq`, `Ski/Table.lean`), and `SumTable.us_six`
(`Ski/Examples.lean`) runs `3 sumto`, built on Joy's `y`, end to end.
-/

/-- Divergence is invariant under weak reduction: weak reduction never
    lengthens the run to a normal form (`StepsN.wtail`). -/
theorem diverges_iff_of_wsteps {t u : Term} (h : WSteps t u) : Diverges t ↔ Diverges u := by
  constructor
  · exact diverges_of_wsteps h
  · intro hu v hv
    cases hv.1.counted with
    | intro n hn =>
      cases StepsN.wtail h hn hv.2 with
      | intro m hm =>
        cases hm with
        | intro w hw => exact hu w ⟨hw.2.1.steps, hw.2.2⟩

namespace Table

variable (tb : Table)

/-- A program's compiled term, given the eliminator and the stack, runs
    to `N` of its words. -/
theorem progT_wsteps (p : List Word) (R s : Term) :
    WSteps (tb.progT p ⬝ R ⬝ s) (@N tb.kit R p ⬝ s) := by
  have h := compDef1_beta 0 (tb.bodySrc p) R
  rw [ev_bodySrc] at h
  exact WSteps.left s h

/-- **Every derivation is realized**, for every program over every valid
    table. -/
theorem program_apply {tb : Table} (hv : tb.Valid) {p : List Word} {S : Stack} {o : Outcome}
    (h : @Run tb.kit (.prog p) S o) (hp : p.all (Word.ok tb.n) = true) {s : Term}
    (hs : @DecStack tb.kit s S) : @Contract tb.kit (tb.progT p ⬝ tb.applyU ⬝ s) o := by
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  haveI : KitWords := tb.kit_words
  haveI : KitApply := tb.kit_apply hv
  exact Contract.of_wsteps (tb.progT_wsteps p _ s) (composition_apply h hp (compiles_N _ _) hs)

/-- **The divergence biconditional**, for every program over every valid
    table: the compiled program diverges exactly when `Run` derives no
    outcome. -/
theorem program_diverges {tb : Table} (hv : tb.Valid) {p : List Word} {S : Stack}
    (hp : p.all (Word.ok tb.n) = true) {s : Term} (hs : @DecStack tb.kit s S) :
    Diverges (tb.progT p ⬝ tb.applyU ⬝ s) ↔ ∀ o, ¬ @Run tb.kit (.prog p) S o := by
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  haveI : KitWords := tb.kit_words
  haveI : KitApply := tb.kit_apply hv
  exact (diverges_iff_of_wsteps (tb.progT_wsteps p _ s)).trans
    (composition_diverges hp (compiles_N _ _) hs)

/-- **Agreement, both ways**, for every program over every valid table:
    whatever the compiled program normalizes to decodes to an outcome `Run`
    derives. -/
theorem program_exact {tb : Table} (hv : tb.Valid) {p : List Word} {S : Stack} {o : Outcome}
    (hp : p.all (Word.ok tb.n) = true) {s u : Term} (hs : @DecStack tb.kit s S)
    (he : Eval (tb.progT p ⬝ tb.applyU ⬝ s) u) (hd : @Decodes tb.kit u o) :
    @Run tb.kit (.prog p) S o := by
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  haveI : KitWords := tb.kit_words
  haveI : KitApply := tb.kit_apply hv
  have hc : Converges (N tb.applyU p ⬝ s) := by
    cases he.1.counted with
    | intro n hn =>
      cases StepsN.wtail (tb.progT_wsteps p _ s) hn he.2 with
      | intro m hm =>
        cases hm with
        | intro w hw => exact ⟨w, hw.2.1.steps, hw.2.2⟩
  cases composition_complete hp (compiles_N _ _) hs hc with
  | intro o' ho' =>
    cases program_apply hv ho' hp hs with
    | intro u' hu' =>
      have e := Eval.deterministic he hu'.1
      rw [← e] at hu'
      rw [Decodes.functional hd hu'.2]
      exact ho'

end Table
