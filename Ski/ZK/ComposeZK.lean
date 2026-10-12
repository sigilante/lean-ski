import Ski.ComposeDist
import Ski.ZK.Reject

/-!
# The transcript theorems as the interface's zero knowledge

`Compose.PSD` states zero knowledge as `CloseD` over an explicit list of
draws.  The transcript theorems count over the draws `(α, β, r, t)`, the
challenges, the PCS's randomness and the blinding tuples, and, with the
non-generic `β` rejected, only the draws with `genB β` (`transcript_zkG`).
Here those draws are a list (`tdraws`), its sums are the transcript's
(`lsum_tdraws`), and a transcript bound is `CloseD` over it
(`closeD_of_transcriptG`).  For the composed circuit's honest tables the
bound is `comp_transcriptG`'s (`comp_closeD`): the zero-knowledge field of
a `PSD` whose proofs are that circuit's transcripts, with error
`M/P^4 + ε/NR` of all the draws.  What links an accepted witness to those
tables is the run: `comp_honest_zk` takes an accepted run of the composed
machine within the statement's heights.
-/

namespace Circuit

open ZKF Compose

theorem lsum_append {α : Type} (l₁ l₂ : List α) (f : α → Nat) : lsum (l₁ ++ l₂) f = lsum l₁ f + lsum l₂ f := by
  simp [lsum, List.map_append, List.sum_append]

theorem lsum_map {α β : Type} (l : List α) (g : α → β) (f : β → Nat) : lsum (l.map g) f = lsum l (fun a => f (g a)) := by
  simp [lsum, List.map_map, Function.comp_def]

theorem lsum_flatMap {α β : Type} (f : β → Nat) (g : α → List β) :
    ∀ l : List α, lsum (l.flatMap g) f = lsum l (fun a => lsum (g a) f)
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, lsum_append, lsum_flatMap f g l, lsum_cons]

theorem sumTo_lsum (f : Nat → Nat) : ∀ n, sumTo n f = lsum (List.range n) f
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, lsum_append, ← sumTo_lsum f n]
    show sumTo n f + f n = sumTo n f + (f n + 0)
    rfl

/-- The tuple assignments of `m` edges, as `sumN` counts them. -/
def assigns : Nat → List (Nat → Tup)
  | 0 => [fun _ => tup0]
  | m + 1 => (List.range Q4).flatMap fun i => (assigns m).map fun t => updT t m (Tup.dec i)

theorem sumN_lsum : ∀ (m : Nat) (f : (Nat → Tup) → Nat), sumN m f = lsum (assigns m) f
  | 0, f => by show f (fun _ => tup0) = f (fun _ => tup0) + 0; rfl
  | m + 1, f => by
    show (sumTo Q4 fun i => sumN m fun t => f (updT t m (Tup.dec i))) = _
    unfold assigns
    rw [lsum_flatMap, sumTo_lsum]
    exact congrArg (lsum (List.range Q4)) (funext fun i => by rw [sumN_lsum m, lsum_map])

/-- **The draws of a transcript with the non-generic `β` rejected**: the
    challenges `α` and `β`, `β` generic, the PCS's `r < NR`, and the
    tuples of `m` edges. -/
def tdraws (NR m : Nat) : List (EF × EF × Nat × (Nat → Tup)) :=
  (List.range Q4).flatMap fun i => (List.range Q4).flatMap fun j =>
    if genB (efOf j) then (List.range NR).flatMap fun r => (assigns m).map fun t => (efOf i, efOf j, r, t)
    else []

/-- Sums over the draws are the transcript's sums over the generic `β`. -/
theorem lsum_tdraws (NR m : Nat) (f : EF × EF × Nat × (Nat → Tup) → Nat) :
    lsum (tdraws NR m) f = tsumN NR m (fun α β r t => if genB β then f (α, β, r, t) else 0) := by
  unfold tdraws tsumN
  rw [lsum_flatMap, sumTo_lsum]
  refine congrArg (lsum (List.range Q4)) (funext fun i => ?_)
  rw [lsum_flatMap, sumTo_lsum]
  refine congrArg (lsum (List.range Q4)) (funext fun j => ?_)
  cases hg : genB (efOf j)
  · simp only [hg, Bool.false_eq_true, if_false]
    rw [sumTo_lsum]
    show 0 = lsum (List.range NR) fun r => sumN m fun _ => 0
    rw [show (fun r => sumN m fun (_ : Nat → Tup) => 0) = fun (_ : Nat) => 0 from
      funext fun _ => by rw [sumN_const, Nat.mul_zero], lsum_const, Nat.mul_zero]
  · simp only [hg, if_true]
    rw [lsum_flatMap, sumTo_lsum]
    exact congrArg (lsum (List.range NR)) (funext fun r => by rw [lsum_map, sumN_lsum])

/-- **A transcript bound is `CloseD`**: counts over the generic `β`
    within `e`, for every event, are closeness over `tdraws` within `e`. -/
theorem closeD_of_transcriptG {V : Type} {NR m e : Nat} {real sim : EF → EF → Nat → (Nat → Tup) → V}
    (h : ∀ E : V → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (real α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sim α β r t))) + e ∧
      tsumN NR m (fun α β r t => indB (genB β && E (sim α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (real α β r t))) + e) :
    CloseD (tdraws NR m) e (fun x => real x.1 x.2.1 x.2.2.1 x.2.2.2) (fun x => sim x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  intro E
  have key : ∀ g : EF → EF → Nat → (Nat → Tup) → V,
      cnt (tdraws NR m) (fun x => g x.1 x.2.1 x.2.2.1 x.2.2.2) E =
        tsumN NR m (fun α β r t => indB (genB β && E (g α β r t))) := by
    intro g
    unfold cnt
    rw [lsum_tdraws]
    have pw : ∀ α β r t, (if genB β then (if E (g α β r t) then 1 else 0) else 0) =
        indB (genB β && E (g α β r t)) := by
      intro α β r t
      cases genB β <;> cases E (g α β r t) <;> rfl
    exact Nat.le_antisymm (tsumN_mono fun α β r t => Nat.le_of_eq (pw α β r t))
      (tsumN_mono fun α β r t => Nat.le_of_eq (pw α β r t).symm)
  rw [key real, key sim]
  exact h E

/-- **The composed circuit's zero knowledge, as closeness**: for honest
    tables (balanced, unblinded, `comp_honest_zk`), the real transcript is
    within `comp_transcriptG`'s error of the simulated one over `tdraws`. -/
theorem comp_closeD {PV : Type} (off : EF → String → EF) (NR ε : Nat)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat} {C Mm Wt : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt (segsPub roots)))
    (h : Unblinded WT_BLIND C Mm Wt)
    (hpcs : PCSCloseN off NR (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) pcs psim ε) :
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
    CloseD (tdraws NR 2) (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * ε)))
      (fun x => realVN off tabs tv pb pcs x.1 x.2.1 x.2.2.1 x.2.2.2)
      (fun x => simVN off pb chainBus (fun _ => false) chainPar 3 tp psim x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  intro tabs tv pb tp M
  refine closeD_of_transcriptG fun E => ?_
  have := comp_transcriptG off NR ε pcs psim hb h hpcs E
  exact ⟨by rw [← Nat.add_assoc]; exact this.1, by rw [← Nat.add_assoc]; exact this.2⟩

end Circuit
