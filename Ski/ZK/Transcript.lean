import Ski.ZK.Circuits
import Ski.ZK.Abort
import Ski.Circuit.CompComplete
import Ski.Circuit.SudComplete
import Ski.Circuit.WitComplete

/-!
# A simulator for the whole transcript, over a hiding PCS

A proof's transcript is what the verifier sees: the challenges, the
published LogUp terminals, and everything the PCS commits and opens.  This
file proves the transcript **simulatable**: a simulator that knows only the
public data produces, for every event, a count within a fraction
`P^2 / P^4 + M / P^4 + ε / NR` of the real one (`transcript_zk`), `M` the
number of LogUp messages and `ε / NR` the PCS's own distance.

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
generic `β` that has the real terminals' distribution (`chain_hides`).  The
public tables' terminals themselves (`pb`) it computes.  It departs from
the real transcript only at a non-generic `β` (`P^2` of `P^4`,
`nongeneric_count`), at the draws where the prover aborts (at most `M` of
the `P^4` values of `α`, `abort_count`), and by the PCS's `ε`.

The circuits' instances are `sud_transcript`, `wit_transcript` and
`comp_transcript` (formulas and predicates alike).  Each takes the
public tables the honest prover writes: the program table of the
statement's heap, and for the composed proof the segment table
`segsPub roots`, whose multiplicities are private columns but fixed by the
statement for the honest prover (`segs_honest`).  The completeness
theorems return exactly these tables, so `tp` and `pb` are public.
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

theorem count2_le (p : Tup → Tup → Bool) : count2 p ≤ Q4 * Q4 := by
  unfold count2
  refine sumTo_le_const (fun i => ?_) Q4
  refine Nat.le_trans (sumTo_le_const (c := 1) (fun j => ?_) Q4) (Nat.le_of_eq (Nat.mul_one Q4))
  split <;> omega

/-- A published view: everything the PCS shows, the challenges, the private
    terminals and the public tables' terminals; `none` when the prover
    aborts. -/
abbrev TView (PV PB : Type) := Option (PV × EF × EF × View3 × PB)

/-- The reference triple: zero, zero, and minus the public terminal. -/
def xref (t : EF) : View3 := ⟨EF.zero, EF.zero, EF.zero.sub t⟩

theorem xref_sum (t : EF) : (xref t).sum = EF.zero.sub t := by
  show (EF.zero.add EF.zero).add (EF.zero.sub t) = _
  rw [EF.zero_add, EF.zero_add]

/-- A sum over the whole randomness: `α`, `β`, the PCS's `ρ`, `a`, `b`. -/
def tsum (NR : Nat) (f : EF → EF → Nat → Tup → Tup → Nat) : Nat :=
  sumTo Q4 fun i => sumTo Q4 fun j => sumTo NR fun r => sumTo Q4 fun a => sumTo Q4 fun b =>
    f (efOf i) (efOf j) r (Tup.dec a) (Tup.dec b)

theorem tsum_mono {NR : Nat} {f g : EF → EF → Nat → Tup → Tup → Nat}
    (h : ∀ α β r a b, f α β r a b ≤ g α β r a b) : tsum NR f ≤ tsum NR g :=
  sumTo_mono _ fun _ _ => sumTo_mono _ fun _ _ => sumTo_mono _ fun _ _ => sumTo_mono _ fun _ _ =>
    sumTo_mono _ fun _ _ => h _ _ _ _ _

theorem tsum_add (NR : Nat) (f g : EF → EF → Nat → Tup → Tup → Nat) :
    tsum NR (fun α β r a b => f α β r a b + g α β r a b) = tsum NR f + tsum NR g := by
  unfold tsum
  rw [← sumTo_add]
  refine sumTo_congr _ fun _ _ => ?_
  rw [← sumTo_add]
  refine sumTo_congr _ fun _ _ => ?_
  rw [← sumTo_add]
  refine sumTo_congr _ fun _ _ => ?_
  rw [← sumTo_add]
  refine sumTo_congr _ fun _ _ => ?_
  rw [← sumTo_add]

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
-- The pieces
-- ---------------------------------------------------------------------------

section
variable {PV PB : Type} {off : EF → String → EF} {NR : Nat}
  {tv : (String → EF) → EF → Tup → Tup → View3} {tp : (String → EF) → EF → EF}
  {pb : (String → EF) → EF → PB}
  {pcs : Tup → Tup → EF → EF → Nat → PV} {psim : EF → EF → View3 → Nat → PV}

/-- The real transcript's count at fixed challenges, the abort aside. -/
def realIn (E : TView PV PB → Bool) (α β : EF) : Nat :=
  sumTo NR fun r => sumTo Q4 fun a => sumTo Q4 fun b =>
    indB (E (some (pcs (Tup.dec a) (Tup.dec b) α β r, α, β, tv (prefixOf α (off β)) β (Tup.dec a) (Tup.dec b),
      pb (prefixOf α (off β)) β)))

/-- The same with the PCS's view simulated from the real terminals. -/
def midIn (E : TView PV PB → Bool) (α β : EF) : Nat :=
  sumTo NR fun r => sumTo Q4 fun a => sumTo Q4 fun b =>
    indB (E (some (psim α β (tv (prefixOf α (off β)) β (Tup.dec a) (Tup.dec b)) r, α, β,
      tv (prefixOf α (off β)) β (Tup.dec a) (Tup.dec b), pb (prefixOf α (off β)) β)))

/-- The simulated transcript's count at fixed challenges. -/
def simIn (E : TView PV PB → Bool) (α β : EF) : Nat :=
  sumTo NR fun r => sumTo Q4 fun a => sumTo Q4 fun b =>
    indB (E (simV off tp pb psim α β r (Tup.dec a) (Tup.dec b)))

/-- The PCS's randomness innermost. -/
theorem inner_swap (f : Nat → Nat → Nat → Nat) :
    (sumTo NR fun r => sumTo Q4 fun a => sumTo Q4 fun b => f r a b) =
      sumTo Q4 fun a => sumTo Q4 fun b => sumTo NR fun r => f r a b := by
  rw [sumTo_exch _ Q4 NR]
  refine sumTo_congr _ fun a _ => ?_
  rw [sumTo_exch _ Q4 NR]

/-- **The PCS step**: its view simulated, within `ε` for each blinding. -/
theorem inner_pcs {ε : Nat} (hpcs : PCSClose off NR tv pcs psim ε) (E : TView PV PB → Bool) (α β : EF) :
    realIn (off := off) (NR := NR) (tv := tv) (pb := pb) (pcs := pcs) E α β ≤
        midIn (off := off) (NR := NR) (tv := tv) (pb := pb) (psim := psim) E α β + Q4 * (Q4 * ε) ∧
      midIn (off := off) (NR := NR) (tv := tv) (pb := pb) (psim := psim) E α β ≤
        realIn (off := off) (NR := NR) (tv := tv) (pb := pb) (pcs := pcs) E α β + Q4 * (Q4 * ε) := by
  unfold realIn midIn
  rw [inner_swap, inner_swap]
  have hb := fun a b => hpcs (Tup.dec a) (Tup.dec b) α β
    (fun pv => E (some (pv, α, β, tv (prefixOf α (off β)) β (Tup.dec a) (Tup.dec b), pb (prefixOf α (off β)) β)))
  have tot : ∀ (g : Nat → Nat → Nat), (sumTo Q4 fun a => sumTo Q4 fun b => g a b + ε) =
      (sumTo Q4 fun a => sumTo Q4 fun b => g a b) + Q4 * (Q4 * ε) := by
    intro g
    rw [sumTo_congr Q4 (fun a _ => sumTo_add (g a) (fun _ => ε) Q4), sumTo_add, sumTo_const, sumTo_const]
  constructor
  · rw [← tot]
    exact sumTo_mono _ fun a _ => sumTo_mono _ fun b _ => (hb a b).1
  · rw [← tot]
    exact sumTo_mono _ fun a _ => sumTo_mono _ fun b _ => (hb a b).2

/-- **The terminals step**: at a generic `β`, the chain hides them. -/
theorem inner_chain {xu : (String → EF) → EF → View3}
    (hchain : ∀ pre β a b, tv pre β a b = chainView β (pre "blind_a") (pre "blind_b") (xu pre β) a b)
    (hsum : ∀ pre β, (xu pre β).sum = EF.zero.sub (tp pre β)) (E : TView PV PB → Bool) {α β : EF}
    (hg : Generic β) :
    midIn (off := off) (NR := NR) (tv := tv) (pb := pb) (psim := psim) E α β =
      simIn (off := off) (NR := NR) (tp := tp) (pb := pb) (psim := psim) E α β := by
  unfold midIn simIn simV
  refine sumTo_congr _ fun r _ => ?_
  have e := chain_hides hg (prefixOf α (off β) "blind_a") (prefixOf α (off β) "blind_b")
    (xu (prefixOf α (off β)) β) (xref (tp (prefixOf α (off β)) β))
    (by rw [hsum, xref_sum])
    (fun t => E (some (psim α β t r, α, β, t, pb (prefixOf α (off β)) β)))
  unfold count2 at e
  have e' : ∀ a b : Tup, tv (prefixOf α (off β)) β a b = chainView β (prefixOf α (off β) "blind_a")
      (prefixOf α (off β) "blind_b") (xu (prefixOf α (off β)) β) a b :=
    fun a b => hchain (prefixOf α (off β)) β a b
  simp only [e']
  exact e

theorem inner_le (NR : Nat) (g : Nat → Tup → Tup → Bool) :
    (sumTo NR fun r => sumTo Q4 fun a => sumTo Q4 fun b => indB (g r (Tup.dec a) (Tup.dec b))) ≤
      NR * (Q4 * Q4) :=
  sumTo_le_const (fun r => count2_le (g r)) NR

end

-- ---------------------------------------------------------------------------
-- The theorem
-- ---------------------------------------------------------------------------

/-- **The transcript is simulatable, over a hiding PCS.**  Given the chain
    (the published private terminals are `chainView` of the unblinded ones,
    whose sum is minus the public terminal `tp`), at most `M` LogUp
    messages, and a PCS whose view is within `ε` of a simulator's for each
    blinding and challenges (`PCSClose`), the simulated transcript matches
    the real one on every event `E`, up to `errG + errA + errP` of the
    `Q4 · Q4 · NR · Q4 · Q4` draws: `errG` for the `P^2` non-generic
    challenges `β`, a fraction `P^2 / P^4`; `errA` for the aborts, a
    fraction `M / P^4`; `errP` for the PCS, a fraction `ε / NR`.  The
    simulator (`simV`) uses the challenges, the public `tp` and `pb`, and
    `psim`: a zero-knowledge statement when `psim` is fixed by the
    statement alone, before the witness. -/
theorem transcript_zk {PV PB : Type} {off : EF → String → EF} {NR M ε : Nat}
    {tabs : Tup → Tup → List (AirD × Table)}
    {tv : (String → EF) → EF → Tup → Tup → View3} {tp : (String → EF) → EF → EF}
    {pb : (String → EF) → EF → PB}
    {pcs : Tup → Tup → EF → EF → Nat → PV} {psim : EF → EF → View3 → Nat → PV}
    {xu : (String → EF) → EF → View3}
    (hchain : ∀ pre β a b, tv pre β a b = chainView β (pre "blind_a") (pre "blind_b") (xu pre β) a b)
    (hsum : ∀ pre β, (xu pre β).sum = EF.zero.sub (tp pre β))
    (hM : ∀ a b, (allEntries (tabs a b)).length ≤ M)
    (hpcs : PCSClose off NR tv pcs psim ε) (E : TView PV PB → Bool) :
    tsum NR (fun α β r a b => indB (E (realV off tabs tv pb pcs α β r a b))) ≤
      tsum NR (fun α β r a b => indB (E (simV off tp pb psim α β r a b))) +
        Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (NR * (Q4 * (Q4 * M))) + Q4 * (Q4 * (Q4 * (Q4 * ε))) ∧
    tsum NR (fun α β r a b => indB (E (simV off tp pb psim α β r a b))) ≤
      tsum NR (fun α β r a b => indB (E (realV off tabs tv pb pcs α β r a b))) +
        Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (NR * (Q4 * (Q4 * M))) + Q4 * (Q4 * (Q4 * (Q4 * ε))) := by
  let U := tsum NR (fun α β r a b => indB (E (some (pcs a b α β r, α, β, tv (prefixOf α (off β)) β a b,
    pb (prefixOf α (off β)) β))))
  let S := tsum NR (fun α β r a b => indB (E (simV off tp pb psim α β r a b)))
  let Rl := tsum NR (fun α β r a b => indB (E (realV off tabs tv pb pcs α β r a b)))
  let Ab := tsum NR (fun α β r a b => indB (Aborts (prefixOf α (off β)) β (tabs a b)))
  -- 1. the abort moves the count by at most the aborting draws
  have hRU : Rl ≤ U + Ab := by
    show Rl ≤ U + Ab
    rw [← tsum_add]
    refine tsum_mono fun α β r a b => ?_
    unfold realV
    cases Aborts (prefixOf α (off β)) β (tabs a b)
    · simp only [Bool.false_eq_true, if_false]; exact Nat.le_add_right _ _
    · simp only [if_true]
      have := indB_le (E none)
      show indB (E none) ≤ _ + 1
      omega
  have hUR : U ≤ Rl + Ab := by
    show U ≤ Rl + Ab
    rw [← tsum_add]
    refine tsum_mono fun α β r a b => ?_
    unfold realV
    cases Aborts (prefixOf α (off β)) β (tabs a b)
    · simp only [Bool.false_eq_true, if_false]; exact Nat.le_add_right _ _
    · simp only [if_true]
      have := indB_le (E (some (pcs a b α β r, α, β, tv (prefixOf α (off β)) β a b, pb (prefixOf α (off β)) β)))
      show _ ≤ _ + 1
      omega
  -- 2. the aborting draws: at most `M` values of `α` for each of the rest
  have hAb : Ab ≤ Q4 * (NR * (Q4 * (Q4 * M))) := by
    show tsum NR _ ≤ _
    unfold tsum
    rw [sumTo_exch _ Q4 Q4]
    refine sumTo_le_const (fun j => ?_) Q4
    rw [sumTo_exch _ NR Q4]
    refine sumTo_le_const (fun r => ?_) NR
    rw [sumTo_exch _ Q4 Q4]
    refine sumTo_le_const (fun a => ?_) Q4
    rw [sumTo_exch _ Q4 Q4]
    refine sumTo_le_const (fun b => ?_) Q4
    exact Nat.le_trans (abort_count (off (efOf j)) (efOf j) (tabs (Tup.dec a) (Tup.dec b))) (hM _ _)
  -- 3. the challenges: the PCS within `ε`, then equal at a generic `β`
  let ng : Nat → Nat := fun j => if (combMat (efOf j)).det = 0 then 1 else 0
  have hng : sumTo Q4 ng = P * P := nongeneric_count
  let B := NR * (Q4 * Q4)
  let D := Q4 * (Q4 * ε)
  have per : ∀ i j,
      realIn (off := off) (NR := NR) (tv := tv) (pb := pb) (pcs := pcs) E (efOf i) (efOf j) ≤
        simIn (off := off) (NR := NR) (tp := tp) (pb := pb) (psim := psim) E (efOf i) (efOf j) + B * ng j + D ∧
      simIn (off := off) (NR := NR) (tp := tp) (pb := pb) (psim := psim) E (efOf i) (efOf j) ≤
        realIn (off := off) (NR := NR) (tv := tv) (pb := pb) (pcs := pcs) E (efOf i) (efOf j) + B * ng j + D := by
    intro i j
    by_cases hd : (combMat (efOf j)).det = 0
    · have e1 : ng j = 1 := if_pos hd
      rw [e1, Nat.mul_one]
      have h1 := inner_le NR (fun r a b => E (some (pcs a b (efOf i) (efOf j) r, efOf i, efOf j,
          tv (prefixOf (efOf i) (off (efOf j))) (efOf j) a b, pb (prefixOf (efOf i) (off (efOf j))) (efOf j))))
      have h2 := inner_le NR (fun r a b => E (simV off tp pb psim (efOf i) (efOf j) r a b))
      have e3 : realIn (off := off) (NR := NR) (tv := tv) (pb := pb) (pcs := pcs) E (efOf i) (efOf j) ≤ B := h1
      have e4 : simIn (off := off) (NR := NR) (tp := tp) (pb := pb) (psim := psim) E (efOf i) (efOf j) ≤ B := h2
      exact ⟨by omega, by omega⟩
    · have hp := inner_pcs (tv := tv) (pb := pb) hpcs E (efOf i) (efOf j)
      have hc := inner_chain (off := off) (NR := NR) (pb := pb) (psim := psim) hchain hsum E (α := efOf i) hd
      rw [hc] at hp
      exact ⟨by omega, by omega⟩
  have hsumng : (sumTo Q4 fun _ => sumTo Q4 fun j => B * ng j + D) =
      Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (Q4 * (Q4 * (Q4 * ε))) := by
    rw [sumTo_const, sumTo_add, ← sumTo_mul, hng, sumTo_const, Nat.mul_add]
  have hUS : U ≤ S + (Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (Q4 * (Q4 * (Q4 * ε)))) := by
    show tsum NR _ ≤ tsum NR _ + _
    unfold tsum
    rw [← hsumng, ← sumTo_add]
    refine sumTo_mono _ fun i _ => ?_
    rw [← sumTo_add]
    refine sumTo_mono _ fun j _ => ?_
    have := (per i j).1
    unfold realIn simIn at this
    dsimp only
    omega
  have hSU : S ≤ U + (Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (Q4 * (Q4 * (Q4 * ε)))) := by
    show tsum NR _ ≤ tsum NR _ + _
    unfold tsum
    rw [← hsumng, ← sumTo_add]
    refine sumTo_mono _ fun i _ => ?_
    rw [← sumTo_add]
    refine sumTo_mono _ fun j _ => ?_
    have := (per i j).2
    unfold realIn simIn at this
    dsimp only
    omega
  exact ⟨by omega, by omega⟩

-- ---------------------------------------------------------------------------
-- The circuits
-- ---------------------------------------------------------------------------

/-- The number of messages: each table's height times its interactions. -/
theorem allEntries_length : ∀ ts : List (AirD × Table),
    (allEntries ts).length = (ts.map fun p => p.2.h * p.1.inters.length).sum
  | [] => rfl
  | p :: ts => by
    show (entries p.1 p.2 ++ allEntries ts).length = _
    rw [List.length_append, entries_length, allEntries_length ts]
    rfl

section
variable {PV : Type} (off : EF → String → EF) (NR ε : Nat)
  (pcs : Tup → Tup → EF → EF → Nat → PV) (psim : EF → EF → View3 → Nat → PV)

/-- **The composed proof's transcript is simulatable** (formulas and
    predicates alike), over a hiding PCS.  The prover's tables are
    balanced and unblinded before it blinds them with `a` and `b`, and its
    program and segment tables are the public ones, as the honest prover's
    are (`comp_completeG_log`, `segs_honest`); so the simulator's `tp` and
    `pb`, those tables' terminals, are public. -/
theorem comp_transcript {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
    {C Mm Wt : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt (segsPub roots)))
    (h : Unblinded WT_BLIND C Mm Wt)
    (hpcs : PCSClose off NR (fun pre β a b => compView pre β hd0 stk0 ctr0 n nilA N W C Mm Wt a b) pcs psim ε)
    (E : TView PV (EF × EF) → Bool) :
    let tabs := fun a b => compTables hd0 stk0 ctr0 n nilA heap N W roots ((C.setBlind BLA a).setBlind BLB b)
      (Mm.setBlind 5 b) (progTableC heap N W) (Wt.setBlind WT_BLIND a) (segsPub roots)
    let tv := fun pre β a b => compView pre β hd0 stk0 ctr0 n nilA N W C Mm Wt a b
    let pb := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W), terminal pre β (segsAir roots) (segsPub roots))
    let tp := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W)).add (terminal pre β (segsAir roots) (segsPub roots))
    let M := (allEntries (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt
      (segsPub roots))).length
    tsum NR (fun α β r a b => indB (E (realV off tabs tv pb pcs α β r a b))) ≤
      tsum NR (fun α β r a b => indB (E (simV off tp pb psim α β r a b))) +
        Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (NR * (Q4 * (Q4 * M))) + Q4 * (Q4 * (Q4 * (Q4 * ε))) ∧
    tsum NR (fun α β r a b => indB (E (simV off tp pb psim α β r a b))) ≤
      tsum NR (fun α β r a b => indB (E (realV off tabs tv pb pcs α β r a b))) +
        Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (NR * (Q4 * (Q4 * M))) + Q4 * (Q4 * (Q4 * (Q4 * ε))) :=
  transcript_zk (xu := fun pre β => ⟨terminal pre β (witAir N W) Wt,
      terminal pre β (cpuAirC hd0 stk0 ctr0 n nilA) C, terminal pre β memAirC Mm⟩)
    (fun pre β a b => comp_chain pre β hd0 stk0 ctr0 n nilA N W h a b)
    (fun pre β => comp_sum pre β hb)
    (fun a b => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

/-- **The Sudoku proof's transcript is simulatable**, over a hiding PCS. -/
theorem sud_transcript {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Wt : Table}
    (hb : Balanced (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)) (h : Unblinded 1 C Mm Wt)
    (hpcs : PCSClose off NR (fun pre β a b => sudView pre β hd0 stk0 ctr0 C Mm Wt a b) pcs psim ε)
    (E : TView PV EF → Bool) :
    let tabs := fun a b => sudTables hd0 stk0 ctr0 heap ((C.setBlind BLA a).setBlind BLB b)
      (Mm.setBlind 5 b) (progTableS heap) (Wt.setBlind 1 a)
    let tv := fun pre β a b => sudView pre β hd0 stk0 ctr0 C Mm Wt a b
    let tp := fun pre β => terminal pre β (progAirS heap) (progTableS heap)
    let M := (allEntries (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)).length
    tsum NR (fun α β r a b => indB (E (realV off tabs tv tp pcs α β r a b))) ≤
      tsum NR (fun α β r a b => indB (E (simV off tp tp psim α β r a b))) +
        Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (NR * (Q4 * (Q4 * M))) + Q4 * (Q4 * (Q4 * (Q4 * ε))) ∧
    tsum NR (fun α β r a b => indB (E (simV off tp tp psim α β r a b))) ≤
      tsum NR (fun α β r a b => indB (E (realV off tabs tv tp pcs α β r a b))) +
        Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (NR * (Q4 * (Q4 * M))) + Q4 * (Q4 * (Q4 * (Q4 * ε))) :=
  transcript_zk (xu := fun pre β => ⟨terminal pre β witAirS Wt,
      terminal pre β (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) C, terminal pre β memAirC Mm⟩)
    (fun pre β a b => sud_chain pre β hd0 stk0 ctr0 h a b)
    (fun pre β => sud_sum pre β hb)
    (fun a b => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

/-- **The hidden-term proof's transcript is simulatable**, over a hiding
    PCS. -/
theorem wit_transcript {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat} {C Mm Wt : Table}
    (hb : Balanced (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)) (h : Unblinded WT_BLIND C Mm Wt)
    (hpcs : PCSClose off NR (fun pre β a b => witView pre β hd0 stk0 ctr0 W C Mm Wt a b) pcs psim ε)
    (E : TView PV EF → Bool) :
    let tabs := fun a b => witTables hd0 stk0 ctr0 heap W ((C.setBlind BLA a).setBlind BLB b)
      (Mm.setBlind 5 b) (progTableW heap W) (Wt.setBlind WT_BLIND a)
    let tv := fun pre β a b => witView pre β hd0 stk0 ctr0 W C Mm Wt a b
    let tp := fun pre β => terminal pre β (progAirW heap W) (progTableW heap W)
    let M := (allEntries (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)).length
    tsum NR (fun α β r a b => indB (E (realV off tabs tv tp pcs α β r a b))) ≤
      tsum NR (fun α β r a b => indB (E (simV off tp tp psim α β r a b))) +
        Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (NR * (Q4 * (Q4 * M))) + Q4 * (Q4 * (Q4 * (Q4 * ε))) ∧
    tsum NR (fun α β r a b => indB (E (simV off tp tp psim α β r a b))) ≤
      tsum NR (fun α β r a b => indB (E (realV off tabs tv tp pcs α β r a b))) +
        Q4 * (NR * (Q4 * Q4) * (P * P)) + Q4 * (NR * (Q4 * (Q4 * M))) + Q4 * (Q4 * (Q4 * (Q4 * ε))) :=
  transcript_zk (xu := fun pre β => ⟨terminal pre β (witAirW W) Wt,
      terminal pre β (cpuAirW hd0 stk0 ctr0) C, terminal pre β memAirC Mm⟩)
    (fun pre β a b => wit_chain pre β hd0 stk0 ctr0 W h a b)
    (fun pre β => wit_sum pre β hb)
    (fun a b => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

end

end Circuit
