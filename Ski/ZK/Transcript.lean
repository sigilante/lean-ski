import Ski.ZK.Circuits
import Ski.ZK.Abort

/-!
# A simulator for the whole transcript: the model

A proof's transcript is what the verifier sees: the challenges, the
published LogUp terminals, and everything the PCS commits and opens.  This
file sets out the model for three private tables blinded along a chain:
the transcripts (`realV`, `simV`) and the assumption on the PCS
(`PCSClose`).  The theorem, the simulated transcript within a fraction
`P^2 / P^4 + M / P^4 + ε / NR` of the real one on every event
(`transcript_zk`), `M` the number of LogUp messages and `ε / NR` the PCS's
own distance, is proved in `TranscriptN.lean`, as the three-table
instance of the tree's `transcript_zkN`.

**The model.**
- The public-coin protocol: the challenges `α` and `β` are uniform and
  independent of the prover's randomness, as an honest verifier draws them.
  This is honest-verifier zero knowledge; Fiat–Shamir in the random oracle
  model turns it into a non-interactive proof, a standard step not proved
  here.  The bus prefixes are `α` plus offsets of `β` (`prefixOf`), as
  Plonky3's are.
- The prover's randomness: the PCS's, `ρ < NR`, and the two blinding
  tuples `a` and `b`, all uniform and independent.
- **The one assumption, a hiding PCS** (`PCSClose ε`; `PCSHides` is the
  exact case): everything the PCS commits and opens, for the prover's
  tables and any challenges, is distributed over `ρ` within `ε` of a
  simulator's output `psim`, given only the challenges and the published
  terminals.  For the theorem to be zero knowledge, `psim` is fixed by the
  statement, before the witness; the theorem holds for every witness with
  the same `psim`.
- The honest prover aborts, publishing nothing, when a LogUp denominator is
  zero (`Aborts`).

**The simulator** (`simV`) draws its own `a` and `b` and publishes
`chainView` of a public reference triple (`xref`) with the unblinded
terminals' sum, which is minus the public tables' terminals `tp`; for a
generic `β` that has the real terminals' distribution (`tree_hides`, on
the chain).  The public tables' terminals themselves (`pb`) it computes.
It departs from the real transcript only at a non-generic `β` (`P^2` of
`P^4`, `nongeneric_count`), at the draws where the prover aborts (at most
`M` of the `P^4` values of `α`, `abort_count`), and by the PCS's `ε`.
-/

namespace Circuit

open ZKF

/-- Extension element number `i`. -/
def efOf (i : Nat) : EF := (Tup.dec i).toEF

theorem sumTo_exch (f : Nat → Nat → Nat) (n : Nat) : ∀ m,
    sumTo m (fun i => sumTo n (fun j => f i j)) = sumTo n (fun j => sumTo m (fun i => f i j))
  | 0 => by
    show 0 = sumTo n (fun _ => 0)
    rw [sumTo_const, Nat.mul_zero]
  | m + 1 => by
    show sumTo m (fun i => sumTo n (fun j => f i j)) + sumTo n (fun j => f m j) = _
    rw [sumTo_exch f n m]
    exact (sumTo_add (fun j => sumTo m (fun i => f i j)) (fun j => f m j) n).symm

theorem sumTo_le_const {f : Nat → Nat} {c : Nat} (h : ∀ q, f q ≤ c) : ∀ n, sumTo n f ≤ n * c
  | n => Nat.le_trans (sumTo_mono n (fun q _ => h q)) (Nat.le_of_eq (sumTo_const c n))

/-- A published view: everything the PCS shows, the challenges, the private
    terminals and the public tables' terminals; `none` when the prover
    aborts. -/
abbrev TView (PV PB : Type) := Option (PV × EF × EF × View3 × PB)

/-- The reference triple: zero, zero, and minus the public terminal. -/
def xref (t : EF) : View3 := ⟨EF.zero, EF.zero, EF.zero.sub t⟩

/-- A sum over the whole randomness: `α`, `β`, the PCS's `ρ`, `a`, `b`. -/
def tsum (NR : Nat) (f : EF → EF → Nat → Tup → Tup → Nat) : Nat :=
  sumTo Q4 fun i => sumTo Q4 fun j => sumTo NR fun r => sumTo Q4 fun a => sumTo Q4 fun b =>
    f (efOf i) (efOf j) r (Tup.dec a) (Tup.dec b)

def indB (b : Bool) : Nat := if b then 1 else 0

theorem indB_le (b : Bool) : indB b ≤ 1 := by cases b <;> decide

section

variable {PV PB : Type} (off : EF → String → EF) (NR : Nat) (tabs : Tup → Tup → List (AirD × Table))
  (tv : (String → EF) → EF → Tup → Tup → View3) (tp : (String → EF) → EF → EF)
  (pb : (String → EF) → EF → PB)
  (pcs : Tup → Tup → EF → EF → Nat → PV) (psim : EF → EF → View3 → Nat → PV)

/-- **The real transcript**, for challenges `α β`, PCS randomness `r` and
    blinding `a b`. -/
def realV (α β : EF) (r : Nat) (a b : Tup) : TView PV PB :=
  if Aborts (prefixOf α (off β)) β (tabs a b) then none
  else some (pcs a b α β r, α, β, tv (prefixOf α (off β)) β a b, pb (prefixOf α (off β)) β)

/-- **The simulated transcript**: public data, and its own `r a b`. -/
def simV (α β : EF) (r : Nat) (a b : Tup) : TView PV PB :=
  some (psim α β (chainView β (prefixOf α (off β) "blind_a") (prefixOf α (off β) "blind_b")
      (xref (tp (prefixOf α (off β)) β)) a b) r, α, β,
    chainView β (prefixOf α (off β) "blind_a") (prefixOf α (off β) "blind_b")
      (xref (tp (prefixOf α (off β)) β)) a b,
    pb (prefixOf α (off β)) β)

/-- **The ideal hiding PCS**: for the prover's tables (fixed by `a b`) and
    any challenges, what the PCS shows is distributed over its randomness
    as the simulator's output from the challenges and the published
    terminals. -/
def PCSHides : Prop :=
  ∀ (a b : Tup) (α β : EF) (F : PV → Bool),
    sumTo NR (fun r => indB (F (pcs a b α β r))) =
      sumTo NR (fun r => indB (F (psim α β (tv (prefixOf α (off β)) β a b) r)))

/-- **A statistically hiding PCS**: the same, each count within `ε` of the
    `NR` draws of its randomness (a statistical distance of `ε / NR`). -/
def PCSClose (ε : Nat) : Prop :=
  ∀ (a b : Tup) (α β : EF) (F : PV → Bool),
    sumTo NR (fun r => indB (F (pcs a b α β r))) ≤
      sumTo NR (fun r => indB (F (psim α β (tv (prefixOf α (off β)) β a b) r))) + ε ∧
    sumTo NR (fun r => indB (F (psim α β (tv (prefixOf α (off β)) β a b) r))) ≤
      sumTo NR (fun r => indB (F (pcs a b α β r))) + ε

end

theorem pcsClose_of_hides {PV : Type} {off : EF → String → EF} {NR : Nat}
    {tv : (String → EF) → EF → Tup → Tup → View3} {pcs : Tup → Tup → EF → EF → Nat → PV}
    {psim : EF → EF → View3 → Nat → PV} (h : PCSHides off NR tv pcs psim) : PCSClose off NR tv pcs psim 0 :=
  fun a b α β F => by rw [h a b α β F]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- **The assumption can hold**: a PCS that shows nothing hides.  With it,
    `transcript_zk` is the simulation of what is published in the clear,
    the challenges and the terminals, with no assumption at all. -/
theorem pcsHides_unit (off : EF → String → EF) (NR : Nat) (tv : (String → EF) → EF → Tup → Tup → View3) :
    PCSHides off NR tv (fun _ _ _ _ _ => ()) (fun _ _ _ _ => ()) :=
  fun _ _ _ _ _ => rfl


-- ---------------------------------------------------------------------------
-- The messages
-- ---------------------------------------------------------------------------

/-- The number of messages: each table's height times its interactions. -/
theorem allEntries_length : ∀ ts : List (AirD × Table),
    (allEntries ts).length = (ts.map fun p => p.2.h * p.1.inters.length).sum
  | [] => rfl
  | p :: ts => by
    show (entries p.1 p.2 ++ allEntries ts).length = _
    rw [List.length_append, entries_length, allEntries_length ts]
    rfl


end Circuit
