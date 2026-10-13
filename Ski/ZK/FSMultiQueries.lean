import Ski.ZK.FSMultiReads
import Ski.ZK.FSRounds3

/-!
# The distinguisher's queries before a proof

`FSMultiT`'s distinguisher sees the final tables.  Queries it makes before a
proof is simulated see the tables as they stood then, and the proof's
programming may overwrite their points.  A query phase is a component of the
composition that programs nothing, its view the answers to `k` adaptive
queries (`advRun`, each query a table and point chosen from the answers so
far); its simulated view reads the tables before the later proof's
programming, as `ZKBT`'s simulated views do.  `zkbT_pair` composes it with a
proof's bound: the queries' answers in the simulation come from the tables
before the proof's programming, and the error gains the queries' hits on the
programmed points (`zkbT_queries`, the hits flagged at the unprogrammed
tables, `runR4_prog`).  The queries depend on the tables alone, so with every
coordinate of the programmed points spreading over the draws the hits number
at most `k δq` at each table (`advHit_count`).

Not shown: query phases interleaved with several proofs (`zkbT_powD`'s
collision side charges a hit to the reader's first message, and a query
carries none, so a mixed bound is needed); queries chosen from earlier
proofs' views; a query count or strategy that varies.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The distinguisher's `k` adaptive queries into the four tables, each
    `(table, point)` chosen from the answers so far (`runR4` at `n1 = 1`,
    the point itself). -/
def advRun (K1 K2 K3 K4 k : Nat) (nxt : List Nat → Nat × Nat × Unit) (H : Nat × Nat × Nat × Nat) : List Nat :=
  runR4 K1 K2 K3 K4 1 0 (fun m _ => m) nxt H k

/-- Its queries hitting a programmed point, made at the tables `H`. -/
def advHit (K1 K2 K3 K4 k : Nat) (nxt : List Nat → Nat × Nat × Unit) (H p : Nat × Nat × Nat × Nat) : Bool :=
  (readsR4 K1 K2 K3 K4 1 0 (fun m _ => m) nxt H k).any (fun r => decide (coord4 r.1 p = pt4 1 (fun m _ => m) 0 r))

/-- **The distinguisher's queries before a proof is simulated**: a proof's
    bound `hA` (the simulator programming `prog4 H (pts c x) (cv c)`) and `k`
    adaptive queries made before that programming compose: the queries'
    answers in the simulation are read off the tables before the proof's
    programming, as an adversary querying first sees them.  The error gains
    `δ`, the queries' hits on the programmed points over the draws
    (`hcol`). -/
theorem zkbT_queries {XA CA VA : Type} {K1 K2 K3 K4 KA εA δ k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4) (ST : (Nat × Nat × Nat × Nat → Nat) → Nat) (hST : Lin ST)
    (smA : (XA → Nat) → Nat) (hsA : Lin smA) (SCA : (CA → Nat) → Nat) (hcA : Lin SCA)
    (c4 : Comm ST SCA) (c5 : Comm ST smA)
    (rvA : Nat × Nat × Nat × Nat → XA → VA) (pts : CA → XA → Nat × Nat × Nat × Nat) (cv : CA → Nat × Nat × Nat × Nat)
    (svA : Nat × Nat × Nat × Nat → CA → XA → VA)
    (hA : ZKBT ST KA smA SCA rvA (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) (cv c)) svA εA)
    (okA : CA → Bool) (hokA : ∀ f g : CA → Nat, (∀ c, okA c = true → f c ≤ g c) → SCA f ≤ SCA g)
    (hcv : ∀ c, okA c = true → (cv c).1 < K1 ∧ (cv c).2.1 < K2 ∧ (cv c).2.2.1 < K3 ∧ (cv c).2.2.2 < K4)
    (nxt : List Nat → Nat × Nat × Unit)
    (hcol : SCA (fun ca => smA (fun xa => ST (fun H => indB (advHit K1 K2 K3 K4 k nxt H (pts ca xa))))) ≤ δ) :
    ZKBT ST KA (fun f : XA × Unit → Nat => smA (fun xa => f (xa, ())))
      (fun g : CA × Unit → Nat => SCA (fun ca => g (ca, ())))
      (fun H x => (rvA H x.1, advRun K1 K2 K3 K4 k nxt H))
      (fun H c x => prog4 K1 K2 K3 K4 H (pts c.1 x.1) (cv c.1))
      (fun H c x => (svA H c.1 x.1, advRun K1 K2 K3 K4 k nxt H))
      (εA + δ) := by
  have hB : ZKBT ST 1 (fun f : Unit → Nat => f ()) (fun g : Unit → Nat => g ()) (fun H _ => advRun K1 K2 K3 K4 k nxt H)
      (fun H _ _ => H) (fun H _ _ => advRun K1 K2 K3 K4 k nxt H) 0 := fun E => by
    rw [Nat.one_mul, Nat.add_zero]; exact Nat.le_refl _
  have h := zkbT_pair ST hST smA hsA (fun f : Unit → Nat => f ()) (fun _ _ => rfl) SCA hcA (fun g : Unit → Nat => g ())
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) c4 c5 (fun _ => rfl)
    rvA (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) (cv c)) svA
    (fun H _ => advRun K1 K2 K3 K4 k nxt H) (fun H _ _ => H) (fun H _ _ => advRun K1 K2 K3 K4 k nxt H) hA hB
    (fun H ca xa _ => advHit K1 K2 K3 K4 k nxt H (pts ca xa)) okA hokA
    (fun H ca xa _ hok hc => runR4_prog h1 h2 h3 h4 _ nxt H (pts ca xa) (cv ca) (hcv ca hok) k (fun r hr e => by
      have hit : advHit K1 K2 K3 K4 k nxt H (pts ca xa) = true :=
        List.any_eq_true.2 ⟨r, hr, decide_eq_true e⟩
      rw [hc] at hit; exact Bool.false_ne_true hit))
    hcol
  intro E
  have := h E
  simp only [Nat.one_mul, Nat.mul_one, Nat.zero_mul, Nat.add_zero] at this
  exact this

theorem readsR4_length {W : Type} (K1 K2 K3 K4 n1 m : Nat) (φ : Nat → W → Nat) (nxt : List Nat → Nat × Nat × W)
    (H : Nat × Nat × Nat × Nat) : ∀ k, (readsR4 K1 K2 K3 K4 n1 m φ nxt H k).length = k
  | 0 => rfl
  | k + 1 => by show (readsR4 K1 K2 K3 K4 n1 m φ nxt H k).length + 1 = k + 1; rw [readsR4_length _ _ _ _ _ _ φ nxt H k]

/-- A list of queries hits the programmed points of at most `|l| δq` draws,
    each coordinate of the points spreading (`hsp`). -/
theorem any_hits_le {XA : Type} (smA : (XA → Nat) → Nat) (hsA : Lin smA) (pts : XA → Nat × Nat × Nat × Nat)
    (δq : Nat) (hsp : ∀ i v, smA (fun xa => indB (decide (coord4 i (pts xa) = v))) ≤ δq) :
    ∀ (l : List (Nat × Nat × Unit)), smA (fun xa => indB (l.any (fun r =>
      decide (coord4 r.1 (pts xa) = pt4 1 (fun m _ => m) 0 r)))) ≤ l.length * δq
  | [] => by
    show smA (fun _ => 0) ≤ 0 * δq
    have e := hsA 0 (fun _ _ => 0)
    simp only [sumTo] at e
    rw [e, Nat.zero_mul]; exact Nat.le_refl _
  | r :: l => by
    have ih := any_hits_le smA hsA pts δq hsp l
    have hpt : ∀ xa, indB ((r :: l).any (fun r => decide (coord4 r.1 (pts xa) = pt4 1 (fun m _ => m) 0 r))) ≤
        indB (decide (coord4 r.1 (pts xa) = pt4 1 (fun m _ => m) 0 r)) +
          indB (l.any (fun r => decide (coord4 r.1 (pts xa) = pt4 1 (fun m _ => m) 0 r))) := fun xa => by
      rw [List.any_cons]
      cases decide (coord4 r.1 (pts xa) = pt4 1 (fun m _ => m) 0 r) <;>
        cases l.any (fun r => decide (coord4 r.1 (pts xa) = pt4 1 (fun m _ => m) 0 r)) <;> decide
    refine Nat.le_trans (sm_mono smA hsA hpt) ?_
    rw [sm_add smA hsA, List.length_cons, Nat.succ_mul, Nat.add_comm (l.length * δq)]
    exact Nat.add_le_add (hsp _ _) ih

/-- **The queries' hits are few**: `k` queries, the programmed points'
    every coordinate spreading over the draws (`hsp`), hit at most `k δq` of
    them at each table. -/
theorem advHit_count {XA : Type} {K1 K2 K3 K4 k : Nat} (nxt : List Nat → Nat × Nat × Unit)
    (smA : (XA → Nat) → Nat) (hsA : Lin smA) (pts : XA → Nat × Nat × Nat × Nat)
    (δq : Nat) (hsp : ∀ i v, smA (fun xa => indB (decide (coord4 i (pts xa) = v))) ≤ δq) (H : Nat × Nat × Nat × Nat) :
    smA (fun xa => indB (advHit K1 K2 K3 K4 k nxt H (pts xa))) ≤ k * δq := by
  have h := any_hits_le smA hsA pts δq hsp (readsR4 K1 K2 K3 K4 1 0 (fun m _ => m) nxt H k)
  rwa [readsR4_length] at h

end Circuit
