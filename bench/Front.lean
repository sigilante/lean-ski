import Ski.TypeCheck
open Term Front

/-!
The front end on one source file, for the differential test against
`skijack` (`scripts/differential.py`).

`front FILE LEXICON [eta]` reads `FILE` as UTF-8, its code points the
source `Front.compileWith` takes, in the lexicon `ascii` or `unicode`, and
prints three things (with `eta`, both compilations η-lift, as
`skijack.compile(eta=True)` does):

```
compile refused | compile ok N      -- compileWith, then its N terms
check pass | check fail             -- checkPass
checked refused | checked ok N      -- checkedWith, then its N terms
```

Each term is a line `NAME TERM`, sorted by name (code point order), with
`TERM` in prefix form: `S`, `K`, `I`, and `` ` `` before an application's
function and argument.  A name the compilation lists twice prints twice.
-/

def nmStr (n : Nm) : String := String.ofList (n.map Char.ofNat)

/-- `t` in prefix form, after `acc`. -/
def pre : Term → String → String
  | .S, acc => acc.push 'S'
  | .K, acc => acc.push 'K'
  | .I, acc => acc.push 'I'
  | .app f a, acc => pre a (pre f (acc.push '`'))

def printFile (label : String) : Option (List (Nm × Term)) → IO Unit
  | none => IO.println s!"{label} refused"
  | some env => do
    let es := (env.map fun (n, t) => (nmStr n, t)).toArray.qsort (fun a b => a.1 < b.1)
    IO.println s!"{label} ok {es.size}"
    for (n, t) in es do
      IO.println (pre t (n ++ " "))

def main (args : List String) : IO UInt32 := do
  match args with
  | file :: lex :: rest =>
    let eta ← match rest with
      | [] => pure false
      | ["eta"] => pure true
      | _ => do IO.eprintln "usage: front FILE ascii|unicode [eta]"; return 2
    let u ← match lex with
      | "ascii" => pure false
      | "unicode" => pure true
      | _ => do IO.eprintln s!"front: unknown lexicon {lex}"; return 2
    let src := (← IO.FS.readFile file).toList.map Char.toNat
    printFile "compile" (compileWith u src eta)
    IO.println s!"check {if checkPass u src then "pass" else "fail"}"
    printFile "checked" (checkedWith u src eta)
    return 0
  | _ => IO.eprintln "usage: front FILE ascii|unicode [eta]"; return 2
