import Ski.Fuel
import Ski.Scott
import Ski.Corpus
import Ski.Audit
open Term

/-- Run every corpus row and compare the contraction count with the
    reference reducer's.  Exit nonzero on the first disagreement. -/
def main : IO UInt32 := do
  let mut bad := 0
  for row in corpus do
    match runF 5_000_000 row.term with
    | some (_, n) =>
      let ok := n == row.steps
      IO.println s!"{if ok then "ok  " else "FAIL"} {row.name}: {n} contractions (reference {row.steps})  -- {row.joy}"
      if !ok then bad := bad + 1
    | none =>
      IO.println s!"FAIL {row.name}: timeout at 5,000,000"
      bad := bad + 1
  return if bad == 0 then 0 else 1
