import Ski.ZK.Poseidon2Data

/-!
# Poseidon2 over BabyBear, width 16: a specification

The permutation every proof's commitments and transcript hash with
(Plonky3 0.8's `default_babybear_poseidon2_16`), written as plain
arithmetic modulo `p = 15 · 2^27 + 1` over lists of sixteen numbers:

- the S-box `x ↦ x^7`;
- the external linear layer: Plonky3's `4 × 4` matrix `M₄` on each block
  of four, then each entry plus the sum of the entries in its position
  mod 4 (the `[[2M M M M], …]` circulant);
- the internal linear layer `1 + Diag(V)`, `V` as Plonky3 publishes it:
  `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 2^-8, 1/4, 1/8, 2^-27, -2^-8,
  -1/16, -2^-27]`;
- the rounds: the external layer, four full rounds, thirteen partial
  rounds (the S-box on the first entry only), four full rounds, each full
  round its constants, the S-box on every entry, the external layer.

The constants are Plonky3's own (`Ski/ZK/Poseidon2Data.lean`, generated
by `ski-air poseidon2-lean`), and the kernel checks the specification
against Plonky3's outputs on three inputs (`permute_matches`).  Each
layer follows Plonky3's source.  The check confirms their composition on
those three inputs; it is a test, not a proof of equality on all inputs.
-/

namespace Poseidon2

def p : Nat := 2013265921

def md (x : Nat) : Nat := x % p

/-- The S-box. -/
def sbox (x : Nat) : Nat := x ^ 7 % p

/-- `2⁻¹ = (p + 1) / 2`, and `2^-k`. -/
def inv2k (k : Nat) : Nat := ((p + 1) / 2) ^ k % p

def neg (x : Nat) : Nat := (p - x % p) % p

/-- Plonky3's `M₄`. -/
def mat4 : List Nat → List Nat
  | [x0, x1, x2, x3] =>
    [md (2 * x0 + 3 * x1 + x2 + x3), md (x0 + 2 * x1 + 3 * x2 + x3),
     md (x0 + x1 + 2 * x2 + 3 * x3), md (3 * x0 + x1 + x2 + 2 * x3)]
  | l => l

def chunks4 : List Nat → List (List Nat)
  | a :: b :: c :: d :: r => [a, b, c, d] :: chunks4 r
  | [] => []
  | l => [l]

/-- The sum of the entries at positions `k`, `k + 4`, `k + 8`, …. -/
def colSum (s : List Nat) (k : Nat) : Nat :=
  md (((List.range s.length).filter (fun i => i % 4 == k)).foldl (fun acc i => acc + s.getD i 0) 0)

/-- The external linear layer. -/
def extLinear (s : List Nat) : List Nat :=
  let m := (chunks4 s).flatMap mat4
  (List.range m.length).map fun i => md (m.getD i 0 + colSum m (i % 4))

/-- The internal layer's diagonal. -/
def V : List Nat :=
  [neg 2, 1, 2, inv2k 1, 3, 4, neg (inv2k 1), neg 3, neg 4, inv2k 8, inv2k 2, inv2k 3, inv2k 27,
   neg (inv2k 8), neg (inv2k 4), neg (inv2k 27)]

/-- The internal linear layer `1 + Diag(V)`: each entry the full sum plus
    its own times its diagonal entry. -/
def intLinear (s : List Nat) : List Nat :=
  let sum := md (s.foldl (· + ·) 0)
  (s.zip V).map fun (x, v) => md (sum + v * x)

/-- A full round: constants, the S-box on every entry, the external
    layer. -/
def extRound (s : List Nat) (rc : List Nat) : List Nat :=
  extLinear ((s.zip rc).map fun (x, c) => sbox (x + c))

/-- A partial round: a constant and the S-box on the first entry, the
    internal layer. -/
def intRound (s : List Nat) (c : Nat) : List Nat :=
  match s with
  | x :: r => intLinear (sbox (x + c) :: r)
  | [] => []

/-- **The permutation.** -/
def permute (s : List Nat) : List Nat :=
  let s := rcInitial.foldl extRound (extLinear s)
  let s := rcInternal.foldl intRound s
  rcTerminal.foldl extRound s

/-- **The specification is Plonky3's permutation**, on its three test
    inputs, checked by the kernel. -/
theorem permute_matches : vectors.all (fun io => permute io.1 == io.2) = true := by decide +kernel

end Poseidon2
