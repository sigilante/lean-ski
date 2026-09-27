import Ski.Corpus
open Term

/-!
Print the conformance corpus for the zkVM benchmark: one row per line, as
name, reference contraction count, and the term in prefix form (`` ` `` for
application).  Run with `lake env lean --run bench/Dump.lean`.
-/

def enc : Term → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .app f a => "`" ++ enc f ++ enc a

def main : IO Unit := do
  for r in corpus do
    IO.println s!"{r.name} {r.steps} {enc r.term}"
