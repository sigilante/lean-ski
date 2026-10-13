import Ski.ZK.FSMultiT

/-!
# Outputs reading the tables at their own points meet `hout` and `hpq`

`FSMultiT`, `FSQueryPowT` and `ROMFamilyT` take an output's table reads as
hypotheses: unchanged by an in-range programming its reads miss (`hout`),
and a read that hits another proof's programmed point carrying the reader's
first message (`hpq`).  Here a class of outputs meets both: an output that
reads the first three tables at points `m1 x + n1 k` (its first message as
low digit, as its messages are), any function of the answers (`outR`, its
reads flagged by `hqR`).  `hout` holds (`outR_hout`); `hpq` holds at every
programmed point whose coordinates carry its first message as low digit
(`outR_hpq`), as the simulated points do (`fs4_powD`'s `hp2`, `hp3`, with
`hr1`).  Not covered: reads of the fourth table, whose points are `φ` of the
third message and the view, and adaptive reads (the read list `ks x` fixed
by the draw); no circuit's openings are shown to be of this form.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- A programmed point's coordinate in one of the first three tables. -/
def coordT (i : Nat) (p : Nat × Nat × Nat × Nat) : Nat :=
  match i with
  | 0 => p.1
  | 1 => p.2.1
  | _ => p.2.2.1

/-- One of the first three tables' answer at a point. -/
def rgetT (K1 K2 K3 : Nat) (H : Nat × Nat × Nat × Nat) (i m : Nat) : Nat :=
  match i with
  | 0 => rget K1 m H.1
  | 1 => rget K2 m H.2.1
  | _ => rget K3 m H.2.2.1

/-- An output reading the first three tables at points carrying the
    reader's first message as low digit: read `(i, k)` asks table `i` at
    `m1 x + n1 k`; the output any function of the answers. -/
def outR {X O : Type} (K1 K2 K3 n1 : Nat) (m1 : X → Nat) (ks : X → List (Nat × Nat))
    (g : Nat → Nat → Nat → Nat → X → List Nat → O) (H : Nat × Nat × Nat × Nat) (c4 c1 c2 c3 : Nat) (x : X) : O :=
  g c4 c1 c2 c3 x ((ks x).map (fun r => rgetT K1 K2 K3 H r.1 (m1 x + n1 * r.2)))

/-- Its reads' hits on a programmed point. -/
def hqR {X : Type} (n1 : Nat) (m1 : X → Nat) (ks : X → List (Nat × Nat)) (_ : Nat × Nat × Nat × Nat)
    (p : Nat × Nat × Nat × Nat) (x : X) : Bool :=
  (ks x).any (fun r => decide (coordT r.1 p = m1 x + n1 * r.2))

theorem rgetT_prog {K1 K2 K3 K4 : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (H p a : Nat × Nat × Nat × Nat)
    (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (i m : Nat) (hne : coordT i p ≠ m) :
    rgetT K1 K2 K3 (prog4 K1 K2 K3 K4 H p a) i m = rgetT K1 K2 K3 H i m := by
  match i with
  | 0 => exact rget_rset_ne h1 (Ne.symm hne) ha.1
  | 1 => exact rget_rset_ne h2 (Ne.symm hne) ha.2.1
  | j + 2 => exact rget_rset_ne h3 (Ne.symm hne) ha.2.2.1

/-- **`hout` holds for such an output**: a programming its reads miss leaves
    every answer, and so the output, unchanged. -/
theorem outR_hout {X O : Type} {K1 K2 K3 K4 n1 : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (m1 : X → Nat)
    (ks : X → List (Nat × Nat)) (g : Nat → Nat → Nat → Nat → X → List Nat → O) :
    ∀ H p a c4 c1 c2 c3 x, a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4 → hqR n1 m1 ks H p x = false →
      outR K1 K2 K3 n1 m1 ks g (prog4 K1 K2 K3 K4 H p a) c4 c1 c2 c3 x = outR K1 K2 K3 n1 m1 ks g H c4 c1 c2 c3 x := by
  intro H p a c4 c1 c2 c3 x ha hq
  unfold outR
  congr 1
  refine List.map_congr_left (fun r hr => rgetT_prog h1 h2 h3 H p a ha r.1 _ (fun e => ?_))
  have : (ks x).any (fun r => decide (coordT r.1 p = m1 x + n1 * r.2)) = true :=
    List.any_eq_true.2 ⟨r, hr, decide_eq_true e⟩
  unfold hqR at hq
  rw [hq] at this; exact Bool.false_ne_true this

/-- **`hpq` holds for such an output**: a read hitting a programmed point
    whose coordinates carry its first message as low digit (`hpA`, `hpB`,
    `hpC`: `hr1` and `fs4_powD`'s `hp2`, `hp3` give them for the simulated
    points) carries the reader's
    first message, so the two agree. -/
theorem outR_hpq {X : Type} {n1 : Nat} (m1 : X → Nat) (hm1 : ∀ x, m1 x < n1) (ks : X → List (Nat × Nat))
    (H p : Nat × Nat × Nat × Nat) (hpA : p.1 < n1) (hpB : p.2.1 % n1 = p.1) (hpC : p.2.2.1 % n1 = p.1) (x : X) :
    hqR n1 m1 ks H p x = true → m1 x = p.1 := by
  intro h
  unfold hqR at h
  obtain ⟨r, _, e⟩ := List.any_eq_true.1 h
  have e' : coordT r.1 p = m1 x + n1 * r.2 := of_decide_eq_true e
  have hmod : (m1 x + n1 * r.2) % n1 = m1 x := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hm1 x)]
  have hc : coordT r.1 p % n1 = p.1 := by
    match r.1 with
    | 0 => exact Nat.mod_eq_of_lt hpA
    | 1 => exact hpB
    | j + 2 => exact hpC
  rw [← hmod, ← e', hc]

end Circuit
