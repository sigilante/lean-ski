import Ski.Corpus
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
