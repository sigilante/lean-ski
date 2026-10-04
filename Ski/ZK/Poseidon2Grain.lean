import Ski.ZK.Poseidon2

/-!
# Poseidon2's round constants are the Grain LFSR's output

Plonky3 0.8 generated BabyBear's width-16 round constants with the Grain
LFSR of the Poseidon paper (Grassi et al., eprint 2019/458, Appendix E),
by `p3-poseidon2`'s `generate_constants.py --field babybear --width 16`.
This file writes that procedure as a Lean function and has the kernel
check that its output is the tables of `Ski/ZK/Poseidon2Data.lean`
(`rc_grain`).

The procedure, for a prime `p` of `n` bits, width `t`, `rf` full and `rp`
partial rounds:

- **The register** holds 80 bits `b₀ … b₇₉`, initialized big-endian to
  the field type (2 bits, 1 for a prime field), the S-box (4 bits, 0 for
  `x^α`), `n` (12 bits), `t` (12 bits), `rf` (10 bits), `rp` (10 bits),
  then thirty ones.
- **A clock** shifts in `b₀ ⊕ b₁₃ ⊕ b₂₃ ⊕ b₃₈ ⊕ b₅₁ ⊕ b₆₂` as `b₇₉` and
  drops `b₀`.  The first 160 clocks are discarded.
- **A bit** is self-shrinking: clock twice for `(a, b)`; output `b` if
  `a = 1`, else discard both and repeat.
- **An element** is `n` bits, most significant first, rejected and redrawn
  while `≥ p`.
- **The constants** are `rf · t + rp` elements in one stream: `rf/2` rows
  of `t` for the initial full rounds, then `rp` for the partial rounds,
  then `rf/2` rows of `t` for the terminal full rounds.

The register, its seed, the taps, the 160 discarded clocks, the
self-shrinking rule and the draws are those of the Poseidon reference's
`generate_parameters_grain.sage` (the `hadeshash` repository), read and
compared by hand; the stream's layout, one constant per partial round,
is Poseidon2's, as `generate_constants.py` lays it out.  That Plonky3 ran
this script for its tables is Plonky3's own doc comment; the kernel
checks that the procedure outputs them.

Here `b₀` is the register's bit 79, so a clock is a shift left.  The loops
take fuel and return `none` when it runs out, so `rc_grain` says the
procedure ends and what it gives.

The internal layer's diagonal `V` and the external layer's `M₄` are not
Grain's: Plonky3 chose `V` by a search for cheap multiplications, and
uses its own `M₄` (`MDSMat4`), not the paper's.
-/

namespace Poseidon2.Grain

/-- The register after initialization, before the discarded clocks. -/
def init (n t rf rp : Nat) : Nat :=
  (1 <<< 78) ||| (n <<< 62) ||| (t <<< 50) ||| (rf <<< 40) ||| (rp <<< 30) ||| (2 ^ 30 - 1)

/-- One clock: the new bit `b₀ ⊕ b₁₃ ⊕ b₂₃ ⊕ b₃₈ ⊕ b₅₁ ⊕ b₆₂` (`bᵢ` at bit
    `79 - i`), and the register shifted with it. -/
def clock (s : Nat) : Nat × Nat :=
  let b := ((s >>> 79) ^^^ (s >>> 66) ^^^ (s >>> 56) ^^^ (s >>> 41) ^^^ (s >>> 28) ^^^ (s >>> 17)) &&& 1
  (b, ((s <<< 1) % 2 ^ 80) ||| b)

/-- `k` clocks, their bits discarded. -/
def burn : Nat → Nat → Nat
  | 0, s => s
  | k + 1, s => burn k (clock s).2

/-- A self-shrunk bit: pairs `(a, b)` until `a = 1`, then `b`. -/
def nextBit : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | f + 1, s =>
    let (a, s₁) := clock s
    let (b, s₂) := clock s₁
    if a = 1 then some (b, s₂) else nextBit f s₂

/-- `k` bits, most significant first, onto `acc`. -/
def bitsMSB : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, acc, s => some (acc, s)
  | k + 1, acc, s => do
    let (b, s₁) ← nextBit 1000 s
    bitsMSB k (2 * acc + b) s₁

/-- An element below `p`, of `n` bits, redrawn while `≥ p`. -/
def element (p n : Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | f + 1, s => do
    let (v, s₁) ← bitsMSB n 0 s
    if v < p then some (v, s₁) else element p n f s₁

/-- `k` elements in order. -/
def elements (p n : Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some []
  | k + 1, s => do
    let (v, s₁) ← element p n 1000 s
    let vs ← elements p n k s₁
    some (v :: vs)

/-- A list cut into `k` rows of `t`. -/
def rows (t : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | k + 1, l => l.take t :: rows t k (l.drop t)

/-- The round constants: the initial full rounds' rows, the partial
    rounds', the terminal full rounds' rows. -/
def constants (p n t rf rp : Nat) : Option (List (List Nat) × List Nat × List (List Nat)) := do
  let raw ← elements p n (rf * t + rp) (burn 160 (init n t rf rp))
  let h := rf / 2 * t
  some (rows t (rf / 2) raw, (raw.drop h).take rp, rows t (rf / 2) (raw.drop (h + rp)))

/-- **Plonky3's round constants are the Grain LFSR's**, for BabyBear
    (`p`, 31 bits), width 16, 8 full and 13 partial rounds. -/
theorem rc_grain : constants p 31 16 8 13 = some (rcInitial, rcInternal, rcTerminal) := by
  decide +kernel

end Poseidon2.Grain
