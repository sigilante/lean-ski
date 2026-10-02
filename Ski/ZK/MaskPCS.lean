import Ski.ZK.MaskOOD
import Ski.ZK.TranscriptN

/-!
# The masked column openings discharge `PCSCloseN`

`transcript_zkN` assumes a PCS whose view is within `ε` of a simulator's
(`PCSCloseN`).  `masks_hide` proves that columns interleaved with random
rows open with one distribution whatever their contents.  This file joins
them: for a PCS whose view is the openings of its masked columns
(`pcsM`), at query points `S` of `F` and out-of-domain points `Z`, the
columns any function of the blinding tuples and the challenges, the
hypothesis holds exactly, `ε = 0` (`pcsCloseN_masked`).  The simulator
opens zero columns under fresh masks (`psimM`), and so sees nothing.

The PCS's randomness is `r < P ^ (ncol · n)`, read as `ncol · n` base-`P`
digits (`digitsF`); counting over `r` is counting over the masks
(`sumTo_digitsF`).

Scope.  This is the column-opening part of Plonky3's hiding PCS, in the
public-coin model with `S` and `Z` fixed before the masks.  The view
`pcsM` leaves out the quotient chunks and their randomization, the random
codeword columns, FRI's layers, Merkle paths and salts, and Fiat–Shamir;
for Plonky3 those stay assumed.  The theorem fixes `S` and `Z`: a protocol
that draws `ζ` must also charge `ζ ∈ F` (`hZ`, probability about `P^-3` a
point) and draw it independently of the masks, and every committed table
needs at least `|S| + 4|Z|` rows.  Simulating the quotient's openings,
which this file does not do, would further need `S` to include the
next-row points `g S` they couple to.
-/

namespace Circuit

open ZKF

/-- `k` base-`P` digits of `x`, lowest first. -/
def digitsF : Nat → Nat → List F
  | 0, _ => []
  | k + 1, x => ofN (x % P) :: digitsF k (x / P)

/-- Counting over `r < P ^ k` is counting over `k` digits. -/
theorem sumTo_digitsF : ∀ (k : Nat) (g : List F → Nat), sumTo (P ^ k) (fun x => g (digitsF k x)) = vsum k g
  | 0, g => Nat.zero_add _
  | k + 1, g => by
    rw [Nat.pow_succ', sumTo_digits]
    have e : (fun q => sumTo P (fun r => g (digitsF (k + 1) (r + P * q)))) =
        fun q => sumTo P (fun r => g (ofN r :: digitsF k q)) := funext fun q =>
      sumTo_congr P fun r hr => by
        show g (ofN ((r + P * q) % P) :: digitsF k ((r + P * q) / P)) = _
        rw [(Tup.digit r q hr).1, (Tup.digit r q hr).2]
    rw [e, sumTo_exch (fun q r => g (ofN r :: digitsF k q))]
    exact sumTo_congr P fun d _ => sumTo_digitsF k (fun l => g (ofN d :: l))

section
variable (T R S : List F) (Z : List EF) (n ncol : Nat) (cols : (Nat → Tup) → EF → EF → List (List F))

/-- **The masked-column PCS**: the openings of its `ncol` columns, each
    interleaved with `n` random rows, the randomness `r`'s digits. -/
def pcsM (t : Nat → Tup) (α β : EF) (r : Nat) : List (List F × List EF) :=
  openAll T R S Z n (cols t α β) (digitsF (ncol * n) r)

/-- **Its simulator**: zero columns under the same masks; it uses nothing. -/
def psimM (_ _ : EF) (_ : List EF) (r : Nat) : List (List F × List EF) :=
  openAll T R S Z n (List.replicate ncol (List.replicate n 0)) (digitsF (ncol * n) r)
end

/-- **The masked-column PCS hides exactly.**  With `n` random rows a column,
    `|S| + 4|Z| ≤ n`, `S` off the trace rows and `Z` out of `F`, the
    PCS's view has the simulator's distribution for every tuple
    assignment and challenges: `PCSCloseN` with `ε = 0`. -/
theorem pcsCloseN_masked {T R S : List F} {Z : List EF} {n ncol : Nat}
    {cols : (Nat → Tup) → EF → EF → List (List F)}
    (hT : T.length = n) (hR : R.length = n) (hTR : (T ++ R).Nodup) (hTS : ∀ x ∈ T, x ∉ S)
    (hZ : ∀ z ∈ Z, ∀ x : F, EF.ofF x ≠ z) (hn : S.length + 4 * Z.length ≤ n)
    (hcols : ∀ t α β, (cols t α β).length = ncol ∧ ∀ c ∈ cols t α β, c.length = n)
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF) :
    PCSCloseN off (P ^ (ncol * n)) tv (pcsM T R S Z n ncol cols) (psimM T R S Z n ncol) 0 := by
  intro t α β F
  have key : sumTo (P ^ (ncol * n)) (fun r => indB (F (pcsM T R S Z n ncol cols t α β r))) =
      sumTo (P ^ (ncol * n)) (fun r => indB (F (psimM T R S Z n ncol α β
        (tv (prefixOf α (off β)) β t) r))) := by
    unfold pcsM psimM
    rw [sumTo_digitsF (ncol * n) (fun rs => indB (F (openAll T R S Z n (cols t α β) rs))),
      sumTo_digitsF (ncol * n) (fun rs => indB (F (openAll T R S Z n
        (List.replicate ncol (List.replicate n 0)) rs)))]
    obtain ⟨hl, hc⟩ := hcols t α β
    have h := masks_hide hT hR hTR hTS hZ hn (cols t α β) (List.replicate ncol (List.replicate n 0))
      (by rw [hl, List.length_replicate]) hc
      (fun c hc' => by rw [List.eq_of_mem_replicate hc', List.length_replicate]) F
    rw [hl] at h
    exact h
  rw [key]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end Circuit
