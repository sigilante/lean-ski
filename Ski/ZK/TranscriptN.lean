import Ski.ZK.Transcript
import Ski.ZK.Tree
import Ski.Circuit.CompComplete
import Ski.Circuit.SudComplete
import Ski.Circuit.WitComplete

/-!
# A simulator for the whole transcript, over any number of blinded tables

A circuit with more private tables than three (the jet tables under
hiding, Avon's `docs/ZK-JETS.md`) blinds them along a tree: `m + 1`
tables, `m` edges, each a bus of its own carrying one uniform tuple, each
running either way (`Tree.lean`).  This file proves the simulation of the
transcript for any such tree (`transcript_zkN`), and derives the
three-table theorem, the chain memory ← CPU ← witness, as its instance
(`transcript_zk`), with the circuits' instances `sud_transcript`,
`wit_transcript` and `comp_transcript`.  Each circuit instance takes the
public tables the honest prover writes: the program table of the
statement's heap, and for the composed proof the segment table
`segsPub roots`, whose multiplicities are private columns but fixed by the
statement for the honest prover (`segs_honest`).  The completeness
theorems return exactly these tables, so `tp` and `pb` are public.

**The model** is `Transcript.lean`'s: public-coin challenges `α` and `β`
(honest-verifier zero knowledge; Fiat–Shamir not proved), the prover's
randomness the PCS's `ρ < NR` and the tuples, uniform and independent, one
assumption, a PCS whose view is within `ε` of a simulator's from the
challenges and the published terminals (`PCSCloseN`), and a prover that
aborts on a zero LogUp denominator.  The tuples are an assignment
`t : Nat → Tup` of the `m` edges, counted by `sumN m`.

**The simulator** (`simVN`) draws its own tuples and publishes the tree's
view (`viewT`) of the reference base `xrefN`: minus the public terminals at
the root, zero elsewhere, the unblinded terminals' sum.  For a generic `β`
the tree hides the difference (`tree_hides`).  The error is a fraction
`P^2/P^4 + M/P^4 + ε/NR` of the draws, as for three tables.
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Sums over tuple assignments
-- ---------------------------------------------------------------------------

/-- **A sum over the tuple assignments of `m` edges**, each over all `P^4`
    tuples, the last edge outermost; `countN` is its count. -/
def sumN : Nat → ((Nat → Tup) → Nat) → Nat
  | 0, f => f (fun _ => tup0)
  | m + 1, f => sumTo Q4 fun i => sumN m (fun t => f (updT t m (Tup.dec i)))

theorem countN_eq_sumN : ∀ (m : Nat) (p : (Nat → Tup) → Bool), countN m p = sumN m (fun t => indB (p t))
  | 0, _ => rfl
  | m + 1, _ => sumTo_congr _ fun _ _ => countN_eq_sumN m _

theorem sumN_mono : ∀ (m : Nat) {f g : (Nat → Tup) → Nat}, (∀ t, f t ≤ g t) → sumN m f ≤ sumN m g
  | 0, _, _, h => h _
  | m + 1, _, _, h => sumTo_mono _ fun _ _ => sumN_mono m fun _ => h _

theorem sumN_add : ∀ (m : Nat) (f g : (Nat → Tup) → Nat),
    sumN m (fun t => f t + g t) = sumN m f + sumN m g
  | 0, _, _ => rfl
  | m + 1, f, g => by
    show (sumTo Q4 fun i => sumN m fun t => f (updT t m (Tup.dec i)) + g (updT t m (Tup.dec i))) = _
    rw [sumTo_congr _ fun i _ => sumN_add m (fun t => f (updT t m (Tup.dec i))) (fun t => g (updT t m (Tup.dec i))),
      sumTo_add]
    rfl

theorem sumN_const : ∀ (m c : Nat), sumN m (fun _ => c) = Q4 ^ m * c
  | 0, c => by rw [Nat.pow_zero, Nat.one_mul]; rfl
  | m + 1, c => by
    show (sumTo Q4 fun _ => sumN m fun _ => c) = _
    rw [sumTo_congr _ fun _ _ => sumN_const m c, sumTo_const, Nat.pow_succ, Nat.mul_comm (Q4 ^ m) Q4,
      Nat.mul_assoc]

theorem sumN_le_const {f : (Nat → Tup) → Nat} {c : Nat} (m : Nat) (h : ∀ t, f t ≤ c) : sumN m f ≤ Q4 ^ m * c :=
  Nat.le_trans (sumN_mono m h) (Nat.le_of_eq (sumN_const m c))

/-- An ordinary sum passes inside a sum over tuple assignments. -/
theorem sumTo_sumN : ∀ (m n : Nat) (f : Nat → (Nat → Tup) → Nat),
    sumTo n (fun i => sumN m (fun t => f i t)) = sumN m (fun t => sumTo n (fun i => f i t))
  | 0, _, _ => rfl
  | m + 1, n, f => by
    show (sumTo n fun i => sumTo Q4 fun j => sumN m fun t => f i (updT t m (Tup.dec j))) =
      sumTo Q4 fun j => sumN m fun t => sumTo n fun i => f i (updT t m (Tup.dec j))
    rw [sumTo_exch _ Q4 n]
    exact sumTo_congr _ fun j _ => sumTo_sumN m n (fun i t => f i (updT t m (Tup.dec j)))

-- ---------------------------------------------------------------------------
-- The transcripts
-- ---------------------------------------------------------------------------

/-- A published view: what the PCS shows, the challenges, the private
    terminals in the tree's order, and the public ones; `none` when the
    prover aborts. -/
abbrev TViewN (PV PB : Type) := Option (PV × EF × EF × List EF × PB)

/-- The reference base: minus the public terminals at the root, zero
    elsewhere. -/
def xrefN (tp : EF) : Nat → EF := fun j => if j = 0 then EF.zero.sub tp else EF.zero

theorem xrefN_sum (tp : EF) : ∀ k, sumL (xrefN tp) (List.range (k + 1)) = EF.zero.sub tp
  | 0 => by
    rw [sumL_range_succ]
    show (EF.zero).add (if 0 = 0 then EF.zero.sub tp else EF.zero) = _
    rw [if_pos rfl, EF.zero_add]
  | k + 1 => by
    rw [sumL_range_succ, xrefN_sum tp k]
    show (EF.zero.sub tp).add (if k + 1 = 0 then EF.zero.sub tp else EF.zero) = _
    rw [if_neg (by omega), EF.add_zero]

section
variable {PV PB : Type} (off : EF → String → EF) (NR : Nat) (tabs : (Nat → Tup) → List (AirD × Table))
  (tv : (String → EF) → EF → (Nat → Tup) → List EF) (pb : (String → EF) → EF → PB)
  (pcs : (Nat → Tup) → EF → EF → Nat → PV)

/-- **The real transcript**, for challenges `α β`, PCS randomness `r` and
    the tuples `t`. -/
def realVN (α β : EF) (r : Nat) (t : Nat → Tup) : TViewN PV PB :=
  if Aborts (prefixOf α (off β)) β (tabs t) then none
  else some (pcs t α β r, α, β, tv (prefixOf α (off β)) β t, pb (prefixOf α (off β)) β)

/-- **The simulated transcript**: the tree's view of the reference base,
    under its own tuples. -/
def simVN (bus : Nat → String) (sg : Nat → Bool) (par : Nat → Nat) (n : Nat) (tp : (String → EF) → EF → EF)
    (psim : EF → EF → List EF → Nat → PV) (α β : EF) (r : Nat) (t : Nat → Tup) : TViewN PV PB :=
  some (psim α β (viewT β (fun k => prefixOf α (off β) (bus k)) sg par n (xrefN (tp (prefixOf α (off β)) β)) t) r,
    α, β, viewT β (fun k => prefixOf α (off β) (bus k)) sg par n (xrefN (tp (prefixOf α (off β)) β)) t,
    pb (prefixOf α (off β)) β)

/-- **A statistically hiding PCS**, for the tree: for each tuple
    assignment and challenges, each event's count over the PCS's `NR`
    draws is within `ε` of the simulator's, given the published
    terminals. -/
def PCSCloseN (psim : EF → EF → List EF → Nat → PV) (ε : Nat) : Prop :=
  ∀ (t : Nat → Tup) (α β : EF) (F : PV → Bool),
    sumTo NR (fun r => indB (F (pcs t α β r))) ≤
      sumTo NR (fun r => indB (F (psim α β (tv (prefixOf α (off β)) β t) r))) + ε ∧
    sumTo NR (fun r => indB (F (psim α β (tv (prefixOf α (off β)) β t) r))) ≤
      sumTo NR (fun r => indB (F (pcs t α β r))) + ε

end

/-- A sum over the whole randomness: `α`, `β`, the PCS's `r`, and the
    tuples of `m` edges. -/
def tsumN (NR m : Nat) (f : EF → EF → Nat → (Nat → Tup) → Nat) : Nat :=
  sumTo Q4 fun i => sumTo Q4 fun j => sumTo NR fun r => sumN m fun t => f (efOf i) (efOf j) r t

theorem tsumN_mono {NR m : Nat} {f g : EF → EF → Nat → (Nat → Tup) → Nat}
    (h : ∀ α β r t, f α β r t ≤ g α β r t) : tsumN NR m f ≤ tsumN NR m g :=
  sumTo_mono _ fun _ _ => sumTo_mono _ fun _ _ => sumTo_mono _ fun _ _ => sumN_mono m fun _ => h _ _ _ _

theorem tsumN_add (NR m : Nat) (f g : EF → EF → Nat → (Nat → Tup) → Nat) :
    tsumN NR m (fun α β r t => f α β r t + g α β r t) = tsumN NR m f + tsumN NR m g := by
  unfold tsumN
  rw [← sumTo_add]
  refine sumTo_congr _ fun _ _ => ?_
  rw [← sumTo_add]
  refine sumTo_congr _ fun _ _ => ?_
  rw [← sumTo_add]
  exact sumTo_congr _ fun _ _ => sumN_add m _ _

-- ---------------------------------------------------------------------------
-- The pieces, at fixed challenges
-- ---------------------------------------------------------------------------

section
variable {PV PB : Type} {off : EF → String → EF} {NR m : Nat}
  {tv : (String → EF) → EF → (Nat → Tup) → List EF} {pb : (String → EF) → EF → PB}
  {pcs : (Nat → Tup) → EF → EF → Nat → PV} {psim : EF → EF → List EF → Nat → PV}

/-- The real count at fixed challenges, the abort aside. -/
def realInN (E : TViewN PV PB → Bool) (α β : EF) : Nat :=
  sumTo NR fun r => sumN m fun t =>
    indB (E (some (pcs t α β r, α, β, tv (prefixOf α (off β)) β t, pb (prefixOf α (off β)) β)))

/-- The same with the PCS's view simulated from the real terminals. -/
def midInN (E : TViewN PV PB → Bool) (α β : EF) : Nat :=
  sumTo NR fun r => sumN m fun t =>
    indB (E (some (psim α β (tv (prefixOf α (off β)) β t) r, α, β, tv (prefixOf α (off β)) β t,
      pb (prefixOf α (off β)) β)))

/-- **The PCS step**, for each tuple assignment. -/
theorem inner_pcsN {ε : Nat} (hpcs : PCSCloseN off NR tv pcs psim ε) (E : TViewN PV PB → Bool) (α β : EF) :
    realInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (pcs := pcs) E α β ≤
        midInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (psim := psim) E α β + Q4 ^ m * ε ∧
      midInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (psim := psim) E α β ≤
        realInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (pcs := pcs) E α β + Q4 ^ m * ε := by
  unfold realInN midInN
  rw [sumTo_sumN m NR, sumTo_sumN m NR, ← sumN_const m ε, ← sumN_add, ← sumN_add]
  have hb := fun t => hpcs t α β
    (fun pv => E (some (pv, α, β, tv (prefixOf α (off β)) β t, pb (prefixOf α (off β)) β)))
  exact ⟨sumN_mono m fun t => (hb t).1, sumN_mono m fun t => (hb t).2⟩

/-- **The terminals step**: at a generic `β`, the tree hides them. -/
theorem inner_chainN {bus : Nat → String} {sg : Nat → Bool} {par : Nat → Nat} (hpar : ∀ k, par (k + 1) ≤ k)
    {tp : (String → EF) → EF → EF} {xu : (String → EF) → EF → Nat → EF}
    (hchain : ∀ pre β t, tv pre β t = viewT β (fun k => pre (bus k)) sg par (m + 1) (xu pre β) t)
    (hsum : ∀ pre β, sumL (xu pre β) (List.range (m + 1)) = EF.zero.sub (tp pre β))
    (E : TViewN PV PB → Bool) {α β : EF} (hg : Generic β) :
    midInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (psim := psim) E α β =
      sumTo NR fun r => sumN m fun t => indB (E (simVN off pb bus sg par (m + 1) tp psim α β r t)) := by
  unfold midInN simVN
  refine sumTo_congr _ fun r _ => ?_
  have e := tree_hides hg (fun k => prefixOf α (off β) (bus k)) sg par hpar (m + 1)
    (xu (prefixOf α (off β)) β) (xrefN (tp (prefixOf α (off β)) β))
    (by rw [hsum, xrefN_sum]) (fun L => E (some (psim α β L r, α, β, L, pb (prefixOf α (off β)) β)))
  rw [countN_eq_sumN, countN_eq_sumN] at e
  simp only [hchain]
  exact e

theorem inner_leN (NR m : Nat) (g : Nat → (Nat → Tup) → Bool) :
    (sumTo NR fun r => sumN m fun t => indB (g r t)) ≤ NR * Q4 ^ m :=
  Nat.le_trans (sumTo_le_const (fun r => Nat.le_trans (sumN_le_const m fun t => indB_le (g r t))
    (Nat.le_of_eq (Nat.mul_one _))) NR) (Nat.le_refl _)

end

-- ---------------------------------------------------------------------------
-- The theorem
-- ---------------------------------------------------------------------------

/-- **The transcript is simulatable, over a hiding PCS, for any number of
    blinded tables.**  Given a tree of `m + 1` private tables numbered leaf
    by leaf (`par (k + 1) ≤ k`), whose published terminals are the tree's
    view of the unblinded ones (`hchain`, edge `k` on bus `bus k` with sign
    `sg k`), whose unblinded terminals sum to minus the public terminals
    `tp` (`hsum`), at most `M` LogUp messages, and a PCS within `ε`
    (`PCSCloseN`), the simulated transcript matches the real one on every
    event `E`, up to `errG + errA + errP` of the `Q4 · Q4 · NR · Q4^m`
    draws: fractions `P^2/P^4` (a non-generic `β`), `M/P^4` (the aborts)
    and `ε/NR` (the PCS).  The simulator uses the challenges, the public
    `tp` and `pb`, the tree, and `psim`: a zero-knowledge statement when
    `psim` is fixed by the statement alone, before the witness. -/
theorem transcript_zkN {PV PB : Type} {off : EF → String → EF} {NR M ε m : Nat}
    {bus : Nat → String} {sg : Nat → Bool} {par : Nat → Nat} (hpar : ∀ k, par (k + 1) ≤ k)
    {tabs : (Nat → Tup) → List (AirD × Table)}
    {tv : (String → EF) → EF → (Nat → Tup) → List EF} {tp : (String → EF) → EF → EF}
    {pb : (String → EF) → EF → PB}
    {pcs : (Nat → Tup) → EF → EF → Nat → PV} {psim : EF → EF → List EF → Nat → PV}
    {xu : (String → EF) → EF → Nat → EF}
    (hchain : ∀ pre β t, tv pre β t = viewT β (fun k => pre (bus k)) sg par (m + 1) (xu pre β) t)
    (hsum : ∀ pre β, sumL (xu pre β) (List.range (m + 1)) = EF.zero.sub (tp pre β))
    (hM : ∀ t, (allEntries (tabs t)).length ≤ M)
    (hpcs : PCSCloseN off NR tv pcs psim ε) (E : TViewN PV PB → Bool) :
    tsumN NR m (fun α β r t => indB (E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR m (fun α β r t => indB (E (simVN off pb bus sg par (m + 1) tp psim α β r t))) +
        Q4 * (NR * Q4 ^ m * (P * P)) + Q4 * (NR * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * ε)) ∧
    tsumN NR m (fun α β r t => indB (E (simVN off pb bus sg par (m + 1) tp psim α β r t))) ≤
      tsumN NR m (fun α β r t => indB (E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * Q4 ^ m * (P * P)) + Q4 * (NR * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * ε)) := by
  let U := tsumN NR m (fun α β r t => indB (E (some (pcs t α β r, α, β, tv (prefixOf α (off β)) β t,
    pb (prefixOf α (off β)) β))))
  let S := tsumN NR m (fun α β r t => indB (E (simVN off pb bus sg par (m + 1) tp psim α β r t)))
  let Rl := tsumN NR m (fun α β r t => indB (E (realVN off tabs tv pb pcs α β r t)))
  let Ab := tsumN NR m (fun α β r t => indB (Aborts (prefixOf α (off β)) β (tabs t)))
  -- 1. the abort moves the count by at most the aborting draws
  have hRU : Rl ≤ U + Ab := by
    show Rl ≤ U + Ab
    rw [← tsumN_add]
    refine tsumN_mono fun α β r t => ?_
    unfold realVN
    cases Aborts (prefixOf α (off β)) β (tabs t)
    · simp only [Bool.false_eq_true, if_false]; exact Nat.le_add_right _ _
    · simp only [if_true]
      have := indB_le (E none)
      show indB (E none) ≤ _ + 1
      omega
  have hUR : U ≤ Rl + Ab := by
    show U ≤ Rl + Ab
    rw [← tsumN_add]
    refine tsumN_mono fun α β r t => ?_
    unfold realVN
    cases Aborts (prefixOf α (off β)) β (tabs t)
    · simp only [Bool.false_eq_true, if_false]; exact Nat.le_add_right _ _
    · simp only [if_true]
      have := indB_le (E (some (pcs t α β r, α, β, tv (prefixOf α (off β)) β t, pb (prefixOf α (off β)) β)))
      show _ ≤ _ + 1
      omega
  -- 2. the aborting draws: at most `M` values of `α` for each of the rest
  have hAb : Ab ≤ Q4 * (NR * (Q4 ^ m * M)) := by
    show tsumN NR m _ ≤ _
    unfold tsumN
    rw [sumTo_exch _ Q4 Q4]
    refine sumTo_le_const (fun j => ?_) Q4
    rw [sumTo_exch _ NR Q4]
    refine sumTo_le_const (fun r => ?_) NR
    rw [sumTo_sumN m Q4]
    refine sumN_le_const m (fun t => ?_)
    exact Nat.le_trans (abort_count (off (efOf j)) (efOf j) (tabs t)) (hM _)
  -- 3. the challenges: the PCS within `ε`, then equal at a generic `β`
  let ng : Nat → Nat := fun j => if (combMat (efOf j)).det = 0 then 1 else 0
  have hng : sumTo Q4 ng = P * P := nongeneric_count
  let B := NR * Q4 ^ m
  let D := Q4 ^ m * ε
  have per : ∀ i j,
      realInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (pcs := pcs) E (efOf i) (efOf j) ≤
        (sumTo NR fun r => sumN m fun t => indB (E (simVN off pb bus sg par (m + 1) tp psim (efOf i) (efOf j) r t)))
          + B * ng j + D ∧
      (sumTo NR fun r => sumN m fun t => indB (E (simVN off pb bus sg par (m + 1) tp psim (efOf i) (efOf j) r t))) ≤
        realInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (pcs := pcs) E (efOf i) (efOf j)
          + B * ng j + D := by
    intro i j
    by_cases hd : (combMat (efOf j)).det = 0
    · have e1 : ng j = 1 := if_pos hd
      rw [e1, Nat.mul_one]
      have h1 := inner_leN NR m (fun r t => E (some (pcs t (efOf i) (efOf j) r, efOf i, efOf j,
          tv (prefixOf (efOf i) (off (efOf j))) (efOf j) t, pb (prefixOf (efOf i) (off (efOf j))) (efOf j))))
      have h2 := inner_leN NR m (fun r t => E (simVN off pb bus sg par (m + 1) tp psim (efOf i) (efOf j) r t))
      have e3 : realInN (off := off) (NR := NR) (m := m) (tv := tv) (pb := pb) (pcs := pcs) E (efOf i) (efOf j)
          ≤ B := h1
      exact ⟨by omega, by omega⟩
    · have hp := inner_pcsN (tv := tv) (pb := pb) (m := m) hpcs E (efOf i) (efOf j)
      have hc := inner_chainN (off := off) (NR := NR) (pb := pb) (psim := psim) hpar hchain hsum E
        (α := efOf i) hd
      rw [hc] at hp
      exact ⟨by omega, by omega⟩
  have hsumng : (sumTo Q4 fun _ => sumTo Q4 fun j => B * ng j + D) =
      Q4 * (NR * Q4 ^ m * (P * P)) + Q4 * (Q4 * (Q4 ^ m * ε)) := by
    rw [sumTo_const, sumTo_add, ← sumTo_mul, hng, sumTo_const, Nat.mul_add]
  have hUS : U ≤ S + (Q4 * (NR * Q4 ^ m * (P * P)) + Q4 * (Q4 * (Q4 ^ m * ε))) := by
    show tsumN NR m _ ≤ tsumN NR m _ + _
    unfold tsumN
    rw [← hsumng, ← sumTo_add]
    refine sumTo_mono _ fun i _ => ?_
    rw [← sumTo_add]
    refine sumTo_mono _ fun j _ => ?_
    have := (per i j).1
    unfold realInN at this
    dsimp only
    omega
  have hSU : S ≤ U + (Q4 * (NR * Q4 ^ m * (P * P)) + Q4 * (Q4 * (Q4 ^ m * ε))) := by
    show tsumN NR m _ ≤ tsumN NR m _ + _
    unfold tsumN
    rw [← hsumng, ← sumTo_add]
    refine sumTo_mono _ fun i _ => ?_
    rw [← sumTo_add]
    refine sumTo_mono _ fun j _ => ?_
    have := (per i j).2
    unfold realInN at this
    dsimp only
    omega
  exact ⟨by omega, by omega⟩

-- ---------------------------------------------------------------------------
-- The chain, a tree of three
-- ---------------------------------------------------------------------------

/-- The composed circuits' buses, by edge: edge 0 is `blind_b` (CPU on
    memory), edge 1 `blind_a` (witness on CPU). -/
def chainBus : Nat → String
  | 0 => "blind_b"
  | _ => "blind_a"

theorem chainBus_pre (pre : String → EF) : (fun k => pre (chainBus k)) = chainPre (pre "blind_a") (pre "blind_b") := by
  funext k
  cases k <;> rfl

/-- Three terminals in the tree's order: memory, CPU, witness. -/
def enc3 (x : View3) : List EF := [x.tm, x.tc, x.tw]

/-- The chain's triple, from the tree's view. -/
def dec3 : List EF → View3
  | [m, c, w] => ⟨w, c, m⟩
  | _ => ⟨EF.zero, EF.zero, EF.zero⟩

theorem dec3_enc3 (x : View3) : dec3 (enc3 x) = x := rfl

/-- **The chain's view is the tree's**, for any assignment: `t 1` blinds
    `blind_a`, `t 0` `blind_b`. -/
theorem chain_viewT (β preA preB : EF) (x : View3) (t : Nat → Tup) :
    viewT β (chainPre preA preB) (fun _ => false) chainPar 3 (chainBase x) t =
      enc3 (chainView β preA preB x (t 1) (t 0)) := by
  rw [viewT_congr_t 3 _ t (chainTups (t 1) (t 0)) (fun k hk => by
    unfold chainTups
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> rfl), tree_chain]
  rfl

/-- The tree's reference base is the chain's reference triple. -/
theorem viewT_xrefN (β preA preB : EF) (sg : Nat → Bool) (tp : EF) (t : Nat → Tup) :
    viewT β (chainPre preA preB) sg chainPar 3 (xrefN tp) t =
      viewT β (chainPre preA preB) sg chainPar 3 (chainBase (xref tp)) t :=
  viewT_congr_x chainPar_ok 3 _ _ t (fun j hj => by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> rfl)

/-- A sum over two tuples is one over the assignments of two edges, `a`
    the tuple of edge 1 and `b` of edge 0. -/
theorem tsum_tsumN (NR : Nat) (f : EF → EF → Nat → Tup → Tup → Nat) :
    tsum NR f = tsumN NR 2 (fun α β r t => f α β r (t 1) (t 0)) := rfl

/-- The tree's published view, in the chain's form. -/
def decV {PV PB : Type} : TViewN PV PB → TView PV PB
  | none => none
  | some (pv, α, β, L, q) => some (pv, α, β, dec3 L, q)

/-- **The transcript is simulatable, over a hiding PCS**, for three
    private tables blinded along the chain: `transcript_zkN` for the tree
    of three (`chain_viewT`), its events read back in the chain's form
    (`decV`).  Given the chain (the published private terminals are
    `chainView` of the unblinded ones, whose sum is minus the public
    terminal `tp`), at most `M` LogUp messages, and a PCS whose view is
    within `ε` of a simulator's for each blinding and challenges
    (`PCSClose`), the simulated transcript matches the real one on every
    event `E`, up to `errG + errA + errP` of the `Q4 · Q4 · NR · Q4 · Q4`
    draws: `errG` for the `P^2` non-generic challenges `β`, a fraction
    `P^2 / P^4`; `errA` for the aborts, a fraction `M / P^4`; `errP` for
    the PCS, a fraction `ε / NR`.  The simulator (`simV`) uses the
    challenges, the public `tp` and `pb`, and `psim`: a zero-knowledge
    statement when `psim` is fixed by the statement alone, before the
    witness. -/
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
  have h := transcript_zkN (m := 2) (M := M) (ε := ε) chainPar_ok (bus := chainBus) (sg := fun _ => false)
    (tabs := fun t => tabs (t 1) (t 0)) (tv := fun pre β t => enc3 (tv pre β (t 1) (t 0))) (tp := tp) (pb := pb)
    (pcs := fun t => pcs (t 1) (t 0)) (psim := fun α β L => psim α β (dec3 L))
    (xu := fun pre β => chainBase (xu pre β))
    (fun pre β t => by rw [chainBus_pre, chain_viewT, hchain])
    (fun pre β => by rw [chainBase_sum]; exact hsum pre β)
    (fun t => hM _ _) (fun t α β F => hpcs (t 1) (t 0) α β F) (fun v => E (decV v))
  have hr : ∀ α β r (t : Nat → Tup), E (decV (realVN off (fun t => tabs (t 1) (t 0))
      (fun pre β t => enc3 (tv pre β (t 1) (t 0))) pb (fun t => pcs (t 1) (t 0)) α β r t)) =
      E (realV off tabs tv pb pcs α β r (t 1) (t 0)) := by
    intro α β r t
    unfold realVN realV
    cases Aborts (prefixOf α (off β)) β (tabs (t 1) (t 0)) <;> rfl
  have hs : ∀ α β r (t : Nat → Tup), E (decV (simVN off pb chainBus (fun _ => false) chainPar 3 tp
      (fun α β L => psim α β (dec3 L)) α β r t)) = E (simV off tp pb psim α β r (t 1) (t 0)) := by
    intro α β r t
    unfold simVN simV
    rw [chainBus_pre, viewT_xrefN, chain_viewT]
    rfl
  simp only [hr, hs] at h
  rw [tsum_tsumN, tsum_tsumN]
  rw [Nat.pow_two Q4, Nat.mul_assoc Q4 Q4 M, Nat.mul_assoc Q4 Q4 ε] at h
  exact h

-- ---------------------------------------------------------------------------
-- The circuits
-- ---------------------------------------------------------------------------

/-- The composed circuit's published private terminals, in the tree's
    order: memory, CPU, witness; `t 1` blinds `blind_a`, `t 0` `blind_b`. -/
def compViewN (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA N W : Nat) (C Mm Wt : Table) (t : Nat → Tup) :
    List EF :=
  enc3 (compView pre β hd0 stk0 ctr0 n nilA N W C Mm Wt (t 1) (t 0))

/-- **The composed proof's transcript, by `transcript_zkN`**: the tree of
    three the composed circuits blind (formulas and predicates alike). -/
theorem comp_transcriptN {PV : Type} (off : EF → String → EF) (NR ε : Nat)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat} {C Mm Wt : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt (segsPub roots)))
    (h : Unblinded WT_BLIND C Mm Wt)
    (hpcs : PCSCloseN off NR (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) pcs psim ε)
    (E : TViewN PV (EF × EF) → Bool) :
    let tabs := fun t : Nat → Tup => compTables hd0 stk0 ctr0 n nilA heap N W roots
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableC heap N W)
      (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
    let tv := fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t
    let pb := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W),
      terminal pre β (segsAir roots) (segsPub roots))
    let tp := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))
    let M := (allEntries (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt
      (segsPub roots))).length
    tsumN NR 2 (fun α β r t => indB (E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (E (simVN off pb chainBus (fun _ => false) chainPar 3 tp psim α β r t))) +
        Q4 * (NR * Q4 ^ 2 * (P * P)) + Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * ε)) ∧
    tsumN NR 2 (fun α β r t => indB (E (simVN off pb chainBus (fun _ => false) chainPar 3 tp psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * Q4 ^ 2 * (P * P)) + Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * ε)) :=
  transcript_zkN (m := 2) chainPar_ok
    (xu := fun pre β => chainBase ⟨terminal pre β (witAir N W) Wt, terminal pre β (cpuAirC hd0 stk0 ctr0 n nilA) C,
      terminal pre β memAirC Mm⟩)
    (fun pre β t => by
      rw [chainBus_pre, chain_viewT, ← comp_chain pre β hd0 stk0 ctr0 n nilA N W h (t 1) (t 0)]; rfl)
    (fun pre β => by rw [chainBase_sum]; exact comp_sum pre β hb)
    (fun t => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E

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
