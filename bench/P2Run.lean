import Ski.ZK.Poseidon2SKI
import Std.Data.HashMap

/-!
# Poseidon2 in SKI, as a term for a runtime

`lake exe p2run K OUTDIR` writes the term `P ⬝ stateT x` for Plonky3's
test vector `K` (0, 1 or 2) in Avon's DAG form (`OUTDIR/p2.dag`), each
distinct subterm once, and the normal form `P_spec` proves it reaches,
`stateN (permute x)` with Plonky3's output (`OUTDIR/p2.expected`), in
Avon's printed form.  `avon reduce OUTDIR/p2.dag` reduces it.  It also
writes `P` alone (`OUTDIR/P.dag`), the term `avon reduce --p2=OUTDIR/P.dag`
runs natively.
-/

open Term

/-- Hash-consing: each distinct subterm gets one id. -/
structure DagSt where
  ids : Std.HashMap (Nat × Nat × Nat) Nat := {}
  lines : Array String := #[]

def atomId : Term → Option (Nat × String)
  | .S => some (0, "S")
  | .K => some (1, "K")
  | .I => some (2, "I")
  | _ => none

partial def dagOf (t : Term) : StateM DagSt Nat := do
  let key ← match t with
    | .app f x => do
      let a ← dagOf f
      let b ← dagOf x
      pure (3, a, b)
    | .S => pure (0, 0, 0)
    | .K => pure (1, 0, 0)
    | .I => pure (2, 0, 0)
  let st ← get
  match st.ids.get? key with
  | some i => pure i
  | none =>
    let i := st.ids.size
    let rhs := match key with
      | (0, _, _) => "S" | (1, _, _) => "K" | (2, _, _) => "I"
      | (_, a, b) => s!"{a}.{b}"
    set ({ ids := st.ids.insert key i, lines := st.lines.push s!"{i}={rhs}" } : DagSt)
    pure i

/-- Avon's printed form: application to the left, arguments that are
    applications in parentheses. -/
partial def pretty : Term → String
  | .S => "S" | .K => "K" | .I => "I"
  | .app f x =>
    let a := match x with
      | .app _ _ => s!"({pretty x})"
      | _ => pretty x
    s!"{pretty f} {a}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [k, out] =>
    let some (inp, outp) := Poseidon2.vectors[k.toNat!]? | IO.eprintln "no such vector"; return 1
    let t := Poseidon2SKI.P ⬝ DataJet.stateN inp
    let (root, st) := (dagOf t).run {}
    IO.FS.writeFile s!"{out}/p2.dag" ("dag " ++ " ".intercalate st.lines.toList ++ s!" @{root}\n")
    IO.FS.writeFile s!"{out}/p2.expected" (pretty (DataJet.stateN outp) ++ "\n")
    let (proot, pst) := (dagOf Poseidon2SKI.P).run {}
    IO.FS.writeFile s!"{out}/P.dag" ("dag " ++ " ".intercalate pst.lines.toList ++ s!" @{proot}\n")
    IO.println s!"{st.ids.size} distinct subterms; input {inp}"
    return 0
  | ["part", name, out] =>
    -- One piece alone, for its cost: `mul`, `mod`, `sbox`, `ext`, `int`.
    let a := BitArith.litT 1234567890
    let b := BitArith.litT 2013265920
    let st := Poseidon2SKI.packT ((List.range 16).map fun i => BitArith.litT (i * 99991 + 7))
    let t := match name with
      | "mul" => BitArith.mulT ⬝ a ⬝ b
      | "mod" => Poseidon2SKI.mdT ⬝ (BitArith.mulT ⬝ a ⬝ b)
      | "sbox" => Poseidon2SKI.sboxT ⬝ a
      | "ext" => Poseidon2SKI.extL (Poseidon2.rcInitial.head!) ⬝ st
      | "int" => Poseidon2SKI.intL (Poseidon2.rcInternal.head!) ⬝ st
      | "ext2" => Poseidon2SKI.compT (Poseidon2SKI.extL (Poseidon2.rcInitial.head!))
          (Poseidon2SKI.extL (Poseidon2.rcInitial.head!)) ⬝ st
      | "int2" => Poseidon2SKI.compT (Poseidon2SKI.intL (Poseidon2.rcInternal.head!))
          (Poseidon2SKI.intL (Poseidon2.rcInternal.head!)) ⬝ st
      | _ => Poseidon2SKI.L0 ⬝ st
    let (root, d) := (dagOf t).run {}
    IO.FS.writeFile s!"{out}/{name}.dag" ("dag " ++ " ".intercalate d.lines.toList ++ s!" @{root}\n")
    return 0
  | _ => IO.eprintln "usage: p2run K OUTDIR | p2run part NAME OUTDIR"; return 1
