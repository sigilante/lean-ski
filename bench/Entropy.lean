import Ski.Front
import Ski.ComposedText
import Ski.Entropy
open Term

/-!
A poke whose event is an entropy reply, its bits private (`Ski/Entropy.lean`).

Avon's pier, booted with `--entropy`, answers the kernel's boot request
with the event `[0 [0 bits]]` and logs it as `eny 1 <id> <16 bytes>`, perhaps with a checksum
(avon `docs/DESIGN.md` §9.1).  The statement here is the predicate
`entropyV 128` on `x = [k [0 chk]]`: some 128 literal bits, given to the
kernel `k` as that reply, make the check `chk` accept the poke's result
`[effects k']`.  Lean compiles `k` (the source's `kernel`) and `chk` (the
definition named `CHECK`) from a SKIjack source; the source's kernel is avon's
`tests/kernel/entropy.ascii.ski`, which Lean and SKIjack's compiler compile
to the same term.

**What an accepted proof shows** (`Circuit.entropyExport_sound`): 128
Booleans `bs` with `chk (poke k [0 [0 (listT bs)]])` evaluating to `K`.
The bits are the composed circuit's slot cells, hidden as every composed
witness is (`Circuit.comp_zk`, `transcript_zk`).

- `entropy emit SRC CHECK LOG R M DIR` compiles `SRC` and writes to `DIR` the
  statement at CPU and memory heights `2^R` and `2^M` (`public.txt`), and
  the witness: the bits of the pier log `LOG`'s boot reply, `eny 1`, whose
  id must be `K` (`jamK`), bit
  `8i + j` bit `j` of byte `i` as Avon builds the list (`witness.txt`), and
  two tampered witnesses, a bit cell that is no Boolean
  (`witness_nonbool.txt`) and a region cell pointing forward
  (`witness_forged.txt`).
- `entropy statement SRC CHECK PUBLIC` checks that `PUBLIC` is that
  statement for the source's `kernel` and `CHECK`, at any heights
  `ComposedText` accepts.

`release/entropy/source.ski` holds two checks: `bootok`, which reads no
bit (the boot poke emits nothing and counts one reply), and `firstset`,
which also needs the reply's first bit set.

- `entropy pill SRC PREFIX` checks that `PREFIX`, `avon prefix` of the pill
  a pier booted, is `K kernel` for the source's kernel as Lean compiles
  it: the witness's bits went to the statement's kernel.
-/

open Mach Compose ComposedText CompM Entropy

namespace EntropyPoke

def nm (s : String) : List Nat := s.toList.map Char.toNat

/-- The bits a reply carries, in Avon's order. -/
def nbits : Nat := 128

/-- The region: one cell, since the predicate reads no witness. -/
def W : Nat := 1

/-- The kernel and the check named `chk`, compiled from the source. -/
def readSrc (path chk : String) : IO (Option (Term × Term)) := do
  let some ts := Front.compileFile ((← IO.FS.readFile path).toList.map Char.toNat) | return none
  let some k := ts.lookup (nm "kernel") | return none
  let some c := ts.lookup (nm chk) | return none
  return some (k, c)

/-- The statement: boot's reply carries the id `0`, `K`. -/
def stmtOf (k chk : Term) : CStmt := entropyStmt k K chk nbits

def hexByte (s : String) : Option Nat :=
  let d (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  match s.toList with
  | [a, b] => do some (16 * (← d a) + (← d b))
  | _ => none

/-- A lowercase hex digit, as Avon writes them. -/
def isHex (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- Avon's SKIT jam of `K`, the id boot's reply carries, in hex. -/
def jamK : String := "534b49540100000000000000020000000000000002"

/-- The 16 bytes of the log's `eny 1` record, boot's reply: its id must be
    `K`, as the statement says.  Avon's records may end with a checksum
    field, `=` and 8 hex digits (`SUM_HEX`, Avon's `src/pier.c`), which
    the witness does not read and this reader does not recompute. -/
def bootBytes (log : String) : Option (List Nat) := do
  let line ← (log.splitOn "\n").find? (·.startsWith "eny 1 ")
  let fields := (line.splitOn " ").filter (· ≠ "")
  let (id, hex) ← match fields with
    | ["eny", "1", id, hex] => some (id, hex)
    | ["eny", "1", id, hex, sum] =>
      match sum.toList with
      | '=' :: ds => if ds.length == 8 && ds.all isHex then some (id, hex) else none
      | _ => none
    | _ => none
  if id != jamK then none
  let cs := hex.toList
  if cs.length != 32 then none
  (List.range 16).mapM fun i => hexByte (String.ofList [cs[2 * i]!, cs[2 * i + 1]!])

/-- Bit `8i + j` is bit `j` of byte `i`, least significant first. -/
def bitsOfBytes (bs : List Nat) : List Bool :=
  bs.flatMap fun b => (List.range 8).map fun j => b / 2 ^ j % 2 == 1

def witnessText (bits : List Bool) (region : List Cell) : String :=
  bits.foldl (fun s b => s ++ (if b then "1" else "0") ++ "\n") "" ++
    region.foldl (fun s c => s ++ cellText c ++ "\n") ""

def emit (src cname log : String) (r m : Nat) (dir : String) : IO UInt32 := do
  let some (k, chk) ← readSrc src cname | do IO.println s!"{src}: no kernel and {cname}"; return 1
  if !logOK (r, m) then IO.println "heights out of bounds"; return 1
  let some bytes := bootBytes (← IO.FS.readFile log) | do IO.println s!"{log}: no boot reply (eny 1)"; return 1
  let c := stmtOf k chk
  if !privateOK c W then IO.println "too many bits"; return 1
  let bits := bitsOfBytes bytes
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/public.txt" (publicTextC c W (r, m))
  IO.FS.writeFile s!"{dir}/witness.txt" (witnessText bits [.S])
  IO.FS.writeFile s!"{dir}/witness_nonbool.txt" ("I\n" ++ witnessText (bits.drop 1) [.S])
  IO.FS.writeFile s!"{dir}/witness_forged.txt" (witnessText bits [.app (nbits + 3) (nbits + 3)])
  IO.println s!"entropy: boot's reply from {log}, {nbits} bits ({(bits.filter id).length} set), heights 2^{r} and 2^{m}"
  return 0

/-- **The pier's kernel is the statement's**: `avon prefix` of the pill
    the pier booted, in `PREFIX`, is `K kernel` as Lean compiles it. -/
def pill (src pfx : String) : IO UInt32 := do
  let some ts := Front.compileFile ((← IO.FS.readFile src).toList.map Char.toNat) | do
    IO.println s!"{src}: does not compile"; return 1
  let some k := ts.lookup (nm "kernel") | do IO.println s!"{src}: no kernel"; return 1
  if (← IO.FS.readFile pfx).trimAscii.toString == termText (K ⬝ k) then
    IO.println s!"PILL {pfx}: K applied to the kernel of {src}, as Lean compiles it"
    return 0
  IO.println s!"NOT THIS PILL {pfx}"
  return 1

def statement (src cname pub : String) : IO UInt32 := do
  let some (k, chk) ← readSrc src cname | do IO.println s!"{src}: no kernel and {cname}"; return 1
  match statementOfText (← IO.FS.readFile pub) with
  | some (.pred V x n, W', lg) =>
    if V == entropyV nbits && x == xOf k K chk && n == nbits && W' == W then
      IO.println s!"STATEMENT {pub}: some {nbits} literal bits, given as the reply [0 [0 bits]] to the kernel of {src}, make its {cname} accept the poke (heights 2^{lg.1} and 2^{lg.2})"
      return 0
    IO.println s!"NOT THIS STATEMENT {pub}"
    return 1
  | _ =>
    IO.println s!"NOT A PREDICATE STATEMENT {pub}"
    return 1

end EntropyPoke

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", src, chk, log, r, m, dir] =>
    match r.toNat?, m.toNat? with
    | some r, some m => EntropyPoke.emit src chk log r m dir
    | _, _ => IO.println "heights must be numbers"; return 1
  | ["statement", src, chk, pub] => EntropyPoke.statement src chk pub
  | ["pill", src, pfx] => EntropyPoke.pill src pfx
  | _ =>
    IO.println "usage: entropy emit SRC CHECK LOG R M DIR | entropy statement SRC CHECK PUBLIC | entropy pill SRC PREFIX"
    return 2
