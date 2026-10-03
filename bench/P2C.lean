import Ski.ZK.Poseidon2

/-!
`lake env lean --run bench/P2C.lean`: Poseidon2's constants, as the
specification (`Ski/ZK/Poseidon2.lean`) holds them, printed as a C header
for Avon's jet: the initial and terminal rounds' constants, the internal
rounds', the internal layer's diagonal, and the three test vectors.
-/

open Poseidon2

def row (xs : List Nat) : String := "{" ++ ", ".intercalate (xs.map (fun x => s!"{x}u")) ++ "}"

def main : IO Unit := do
  IO.println "/*  Poseidon2 over BabyBear, width 16: the constants of lean-ski's"
  IO.println " *  specification (Ski/ZK/Poseidon2.lean), printed by bench/P2C.lean."
  IO.println " *  Generated; do not edit. */"
  IO.println ""
  IO.println "#define AV_P2_P 2013265921u"
  IO.println s!"static const uint32_t av_p2_rc_initial[4][16] = \{{", ".intercalate (rcInitial.map row)}};"
  IO.println s!"static const uint32_t av_p2_rc_internal[13] = {row rcInternal};"
  IO.println s!"static const uint32_t av_p2_rc_terminal[4][16] = \{{", ".intercalate (rcTerminal.map row)}};"
  IO.println s!"static const uint32_t av_p2_diag[16] = {row V};"
  IO.println s!"static const uint32_t av_p2_vectors[3][2][16] = \{{", ".intercalate (vectors.map fun io => "{" ++ row io.1 ++ ", " ++ row io.2 ++ "}")}};"
