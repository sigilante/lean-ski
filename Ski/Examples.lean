import Ski.Corpus
import Ski.Apply
open Term

/-!
# End to end

The corpus program `1 2 + dup +`, as `skijack` compiles it, run on the
empty stack: the compiled term reduces to a weak head normal form that
decodes to the stack `[6]`.  `compiled_cp_N` (generated) identifies the
compiled program with `N`; `composition` does the rest.
-/

theorem up_six : Contract (corpus_cp ⬝ apErr ⬝ encStack []) (.val [.num 6]) :=
  Contract.of_steps (Steps.left _ (compiled_cp_N apErr))
    (composition apErr _ apErr_sound [.lit 1, .lit 2, .add, .dup, .add] [] (encStack_dec []))

/-!
Two programs that run quotations, with the compiled `applyU`: `[1] i`,
and `[1] [2] cat i`, whose concatenation `apply` runs through `QThen`:
pop `[1]`, run it, then run `[2]`.
-/

theorem quote_i : Contract
    (N Scott.applyU [.quote (.unit (.num 1)), .i] ⬝ encStack []) (.val [.num 1]) :=
  composition_apply
    (.val (.plain rfl) (.val (.i_run .unit) (.nil _))) (encStack_dec [])

theorem cat_i : Contract
    (N Scott.applyU [.quote (.unit (.num 1)), .quote (.unit (.num 2)), .cat, .i] ⬝ encStack [])
    (.val [.num 2, .num 1]) :=
  composition_apply
    (.val (.plain rfl) (.val (.plain rfl) (.val (.plain rfl)
      (.val (.i_run (.cons (.then_val .unit .unit))) (.nil _))))) (encStack_dec [])
