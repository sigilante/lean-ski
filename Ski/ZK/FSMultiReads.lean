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
`hr1`).  The reads may also be chosen by the challenges' residues
(`outRA`, `outRA_hout`, `outRA_hpq`) and adaptively, each from the answers
so far, the hits flagged at the unprogrammed tables (`runR`, `runR_prog`,
`outRQ`, `outRQ_hout`, `outRQ_hpq`).  The ranges `B1 … B4` lose nothing:
taken as the challenges' ranges, `c % B = c` for every challenge counted,
so the reads may be any function of the in-range challenges.  The read
count `k` is fixed (an adaptive stopping rule pads to the maximum), and a
read sees only the draw, the challenges and the earlier answers.  The
fourth table too: a read at the query hash `φ (m1 x + n1 k) w` of a message
carrying the reader's first message, a fourth-table hash that lands on the programmed point
carrying the programmer's (`hpD`; the circuits' `hφs` gives it across
statements, `hpD_of_hφs`) (`runR4`, `runR4_prog`,
`outR4`, `outR4_hout`, `outR4_hpq`).  The circuits' openings receive the
third message and meet `hout` and `hpq` when they read only at its digit
(`FSMultiOpen`, under the coarser digit flag `hqD`); they are not shown to
be `outR4`s.
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

/-- `outR` with the reads chosen by the challenges (each read modulo a range
    `B1 … B4`): read `(i, k)` of `ks c4 c1 c2 c3 x` asks table `i` at
    `m1 x + n1 k`. -/
def outRA {X O : Type} (K1 K2 K3 n1 B1 B2 B3 B4 : Nat) (m1 : X → Nat)
    (ks : Nat → Nat → Nat → Nat → X → List (Nat × Nat))
    (g : Nat → Nat → Nat → Nat → X → List Nat → O) (H : Nat × Nat × Nat × Nat) (c4 c1 c2 c3 : Nat) (x : X) : O :=
  g c4 c1 c2 c3 x ((ks (c4 % B4) (c1 % B1) (c2 % B2) (c3 % B3) x).map
    (fun r => rgetT K1 K2 K3 H r.1 (m1 x + n1 * r.2)))

/-- Its hits: any read, at any challenges' residues, landing on the point. -/
def hqRA {X : Type} (n1 B1 B2 B3 B4 : Nat) (m1 : X → Nat) (ks : Nat → Nat → Nat → Nat → X → List (Nat × Nat))
    (_ : Nat × Nat × Nat × Nat) (p : Nat × Nat × Nat × Nat) (x : X) : Bool :=
  (List.range B4).any (fun c4 => (List.range B1).any (fun c1 => (List.range B2).any (fun c2 =>
    (List.range B3).any (fun c3 =>
      (ks c4 c1 c2 c3 x).any (fun r => decide (coordT r.1 p = m1 x + n1 * r.2))))))

/-- **`hout` for challenge-chosen reads.** -/
theorem outRA_hout {X O : Type} {K1 K2 K3 K4 n1 B1 B2 B3 B4 : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (hB1 : 0 < B1) (hB2 : 0 < B2) (hB3 : 0 < B3) (hB4 : 0 < B4) (m1 : X → Nat)
    (ks : Nat → Nat → Nat → Nat → X → List (Nat × Nat)) (g : Nat → Nat → Nat → Nat → X → List Nat → O) :
    ∀ H p a c4 c1 c2 c3 x, a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4 →
      hqRA n1 B1 B2 B3 B4 m1 ks H p x = false →
      outRA K1 K2 K3 n1 B1 B2 B3 B4 m1 ks g (prog4 K1 K2 K3 K4 H p a) c4 c1 c2 c3 x =
        outRA K1 K2 K3 n1 B1 B2 B3 B4 m1 ks g H c4 c1 c2 c3 x := by
  intro H p a c4 c1 c2 c3 x ha hq
  unfold outRA
  congr 1
  refine List.map_congr_left (fun r hr => rgetT_prog h1 h2 h3 H p a ha r.1 _ (fun e => ?_))
  have hit : hqRA n1 B1 B2 B3 B4 m1 ks H p x = true := by
    unfold hqRA
    exact List.any_eq_true.2 ⟨c4 % B4, List.mem_range.2 (Nat.mod_lt _ hB4),
      List.any_eq_true.2 ⟨c1 % B1, List.mem_range.2 (Nat.mod_lt _ hB1),
      List.any_eq_true.2 ⟨c2 % B2, List.mem_range.2 (Nat.mod_lt _ hB2),
      List.any_eq_true.2 ⟨c3 % B3, List.mem_range.2 (Nat.mod_lt _ hB3),
      List.any_eq_true.2 ⟨r, hr, decide_eq_true e⟩⟩⟩⟩⟩
  rw [hq] at hit; exact Bool.false_ne_true hit

/-- **`hpq` for challenge-chosen reads**: every read carries the reader's
    first message as low digit, whatever the challenges. -/
theorem outRA_hpq {X : Type} {n1 B1 B2 B3 B4 : Nat} (m1 : X → Nat) (hm1 : ∀ x, m1 x < n1)
    (ks : Nat → Nat → Nat → Nat → X → List (Nat × Nat))
    (H p : Nat × Nat × Nat × Nat) (hpA : p.1 < n1) (hpB : p.2.1 % n1 = p.1) (hpC : p.2.2.1 % n1 = p.1) (x : X) :
    hqRA n1 B1 B2 B3 B4 m1 ks H p x = true → m1 x = p.1 := by
  intro h
  unfold hqRA at h
  obtain ⟨c4, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨c1, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨c2, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨c3, _, h⟩ := List.any_eq_true.1 h
  exact outR_hpq m1 hm1 (ks c4 c1 c2 c3) H p hpA hpB hpC x h

/-- A run of `k` adaptive reads: each read `nxt as` chosen from the answers
    `as` so far, asking table `r.1` at `m n1`-offset `m + n1 r.2`. -/
def runR (K1 K2 K3 n1 m : Nat) (nxt : List Nat → Nat × Nat) (H : Nat × Nat × Nat × Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => rgetT K1 K2 K3 H (nxt (runR K1 K2 K3 n1 m nxt H k)).1 (m + n1 * (nxt (runR K1 K2 K3 n1 m nxt H k)).2) ::
      runR K1 K2 K3 n1 m nxt H k

/-- The run's reads, as made at the tables `H`. -/
def readsR (K1 K2 K3 n1 m : Nat) (nxt : List Nat → Nat × Nat) (H : Nat × Nat × Nat × Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | k + 1 => nxt (runR K1 K2 K3 n1 m nxt H k) :: readsR K1 K2 K3 n1 m nxt H k

/-- **An adaptive run is unchanged by a programming its reads miss**: by
    induction, each read is the same on both tables, so each answer is. -/
theorem runR_prog {K1 K2 K3 K4 n1 m : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (nxt : List Nat → Nat × Nat)
    (H p a : Nat × Nat × Nat × Nat) (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) :
    ∀ k, (∀ r ∈ readsR K1 K2 K3 n1 m nxt H k, coordT r.1 p ≠ m + n1 * r.2) →
      runR K1 K2 K3 n1 m nxt (prog4 K1 K2 K3 K4 H p a) k = runR K1 K2 K3 n1 m nxt H k
  | 0, _ => rfl
  | k + 1, hm => by
    have ih := runR_prog h1 h2 h3 nxt H p a ha k (fun r hr => hm r (List.mem_cons_of_mem _ hr))
    show rgetT K1 K2 K3 (prog4 K1 K2 K3 K4 H p a) (nxt (runR K1 K2 K3 n1 m nxt (prog4 K1 K2 K3 K4 H p a) k)).1
        (m + n1 * (nxt (runR K1 K2 K3 n1 m nxt (prog4 K1 K2 K3 K4 H p a) k)).2) ::
        runR K1 K2 K3 n1 m nxt (prog4 K1 K2 K3 K4 H p a) k = _
    rw [ih]
    show _ = rgetT K1 K2 K3 H (nxt (runR K1 K2 K3 n1 m nxt H k)).1 (m + n1 * (nxt (runR K1 K2 K3 n1 m nxt H k)).2) ::
        runR K1 K2 K3 n1 m nxt H k
    rw [rgetT_prog h1 h2 h3 H p a ha _ _ (hm _ (List.mem_cons_self ..))]

/-- An output from `k` adaptive reads, the read strategy chosen by the draw
    and the challenges' residues. -/
def outRQ {X O : Type} (K1 K2 K3 n1 B1 B2 B3 B4 k : Nat) (m1 : X → Nat)
    (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat)
    (g : Nat → Nat → Nat → Nat → X → List Nat → O) (H : Nat × Nat × Nat × Nat) (c4 c1 c2 c3 : Nat) (x : X) : O :=
  g c4 c1 c2 c3 x (runR K1 K2 K3 n1 (m1 x) (nxt (c4 % B4) (c1 % B1) (c2 % B2) (c3 % B3) x) H k)

/-- Its hits, the reads made at the unprogrammed tables. -/
def hqRQ {X : Type} (K1 K2 K3 n1 B1 B2 B3 B4 k : Nat) (m1 : X → Nat) (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat)
    (H p : Nat × Nat × Nat × Nat) (x : X) : Bool :=
  (List.range B4).any (fun c4 => (List.range B1).any (fun c1 => (List.range B2).any (fun c2 =>
    (List.range B3).any (fun c3 =>
      (readsR K1 K2 K3 n1 (m1 x) (nxt c4 c1 c2 c3 x) H k).any
        (fun r => decide (coordT r.1 p = m1 x + n1 * r.2))))))

/-- **`hout` for adaptive reads.** -/
theorem outRQ_hout {X O : Type} {K1 K2 K3 K4 n1 B1 B2 B3 B4 k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (hB1 : 0 < B1) (hB2 : 0 < B2) (hB3 : 0 < B3) (hB4 : 0 < B4) (m1 : X → Nat)
    (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat) (g : Nat → Nat → Nat → Nat → X → List Nat → O) :
    ∀ H p a c4 c1 c2 c3 x, a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4 →
      hqRQ K1 K2 K3 n1 B1 B2 B3 B4 k m1 nxt H p x = false →
      outRQ K1 K2 K3 n1 B1 B2 B3 B4 k m1 nxt g (prog4 K1 K2 K3 K4 H p a) c4 c1 c2 c3 x =
        outRQ K1 K2 K3 n1 B1 B2 B3 B4 k m1 nxt g H c4 c1 c2 c3 x := by
  intro H p a c4 c1 c2 c3 x ha hq
  unfold outRQ
  rw [runR_prog h1 h2 h3 _ H p a ha k (fun r hr e => ?_)]
  have hit : hqRQ K1 K2 K3 n1 B1 B2 B3 B4 k m1 nxt H p x = true := by
    unfold hqRQ
    exact List.any_eq_true.2 ⟨c4 % B4, List.mem_range.2 (Nat.mod_lt _ hB4),
      List.any_eq_true.2 ⟨c1 % B1, List.mem_range.2 (Nat.mod_lt _ hB1),
      List.any_eq_true.2 ⟨c2 % B2, List.mem_range.2 (Nat.mod_lt _ hB2),
      List.any_eq_true.2 ⟨c3 % B3, List.mem_range.2 (Nat.mod_lt _ hB3),
      List.any_eq_true.2 ⟨r, hr, decide_eq_true e⟩⟩⟩⟩⟩
  rw [hq] at hit; exact Bool.false_ne_true hit

/-- **`hpq` for adaptive reads.** -/
theorem outRQ_hpq {X : Type} {K1 K2 K3 n1 B1 B2 B3 B4 k : Nat} (m1 : X → Nat) (hm1 : ∀ x, m1 x < n1)
    (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat)
    (H p : Nat × Nat × Nat × Nat) (hpA : p.1 < n1) (hpB : p.2.1 % n1 = p.1) (hpC : p.2.2.1 % n1 = p.1) (x : X) :
    hqRQ K1 K2 K3 n1 B1 B2 B3 B4 k m1 nxt H p x = true → m1 x = p.1 := by
  intro h
  unfold hqRQ at h
  obtain ⟨c4, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨c1, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨c2, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨c3, _, h⟩ := List.any_eq_true.1 h
  exact outR_hpq m1 hm1 (fun x' => readsR K1 K2 K3 n1 (m1 x') (nxt c4 c1 c2 c3 x') H k) H p hpA hpB hpC x h

/-- A programmed point's coordinate in any of the four tables. -/
def coord4 (i : Nat) (p : Nat × Nat × Nat × Nat) : Nat :=
  match i with
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2.1
  | _ => p.2.2.2

/-- Any of the four tables' answer at a point. -/
def rget4 (K1 K2 K3 K4 : Nat) (H : Nat × Nat × Nat × Nat) (i m : Nat) : Nat :=
  match i with
  | 0 => rget K1 m H.1
  | 1 => rget K2 m H.2.1
  | 2 => rget K3 m H.2.2.1
  | _ => rget K4 m H.2.2.2

/-- A read `(i, k, w)` at the first message `m`: the first three tables at
    `m + n1 k`, the fourth at the query hash `φ (m + n1 k) w`. -/
def pt4 {W : Type} (n1 : Nat) (φ : Nat → W → Nat) (m : Nat) (r : Nat × Nat × W) : Nat :=
  match r.1 with
  | 0 => m + n1 * r.2.1
  | 1 => m + n1 * r.2.1
  | 2 => m + n1 * r.2.1
  | _ => φ (m + n1 * r.2.1) r.2.2

theorem rget4_prog {K1 K2 K3 K4 : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (H p a : Nat × Nat × Nat × Nat) (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (i m : Nat)
    (hne : coord4 i p ≠ m) : rget4 K1 K2 K3 K4 (prog4 K1 K2 K3 K4 H p a) i m = rget4 K1 K2 K3 K4 H i m := by
  match i with
  | 0 => exact rget_rset_ne h1 (Ne.symm hne) ha.1
  | 1 => exact rget_rset_ne h2 (Ne.symm hne) ha.2.1
  | 2 => exact rget_rset_ne h3 (Ne.symm hne) ha.2.2.1
  | j + 3 => exact rget_rset_ne h4 (Ne.symm hne) ha.2.2.2

/-- `k` adaptive reads over all four tables. -/
def runR4 {W : Type} (K1 K2 K3 K4 n1 m : Nat) (φ : Nat → W → Nat) (nxt : List Nat → Nat × Nat × W)
    (H : Nat × Nat × Nat × Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => rget4 K1 K2 K3 K4 H (nxt (runR4 K1 K2 K3 K4 n1 m φ nxt H k)).1
      (pt4 n1 φ m (nxt (runR4 K1 K2 K3 K4 n1 m φ nxt H k))) :: runR4 K1 K2 K3 K4 n1 m φ nxt H k

def readsR4 {W : Type} (K1 K2 K3 K4 n1 m : Nat) (φ : Nat → W → Nat) (nxt : List Nat → Nat × Nat × W)
    (H : Nat × Nat × Nat × Nat) : Nat → List (Nat × Nat × W)
  | 0 => []
  | k + 1 => nxt (runR4 K1 K2 K3 K4 n1 m φ nxt H k) :: readsR4 K1 K2 K3 K4 n1 m φ nxt H k

theorem runR4_prog {W : Type} {K1 K2 K3 K4 n1 m : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (φ : Nat → W → Nat) (nxt : List Nat → Nat × Nat × W)
    (H p a : Nat × Nat × Nat × Nat) (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) :
    ∀ k, (∀ r ∈ readsR4 K1 K2 K3 K4 n1 m φ nxt H k, coord4 r.1 p ≠ pt4 n1 φ m r) →
      runR4 K1 K2 K3 K4 n1 m φ nxt (prog4 K1 K2 K3 K4 H p a) k = runR4 K1 K2 K3 K4 n1 m φ nxt H k
  | 0, _ => rfl
  | k + 1, hm => by
    have ih := runR4_prog h1 h2 h3 h4 φ nxt H p a ha k (fun r hr => hm r (List.mem_cons_of_mem _ hr))
    show rget4 K1 K2 K3 K4 (prog4 K1 K2 K3 K4 H p a) (nxt (runR4 K1 K2 K3 K4 n1 m φ nxt (prog4 K1 K2 K3 K4 H p a) k)).1
        (pt4 n1 φ m (nxt (runR4 K1 K2 K3 K4 n1 m φ nxt (prog4 K1 K2 K3 K4 H p a) k))) ::
        runR4 K1 K2 K3 K4 n1 m φ nxt (prog4 K1 K2 K3 K4 H p a) k = _
    rw [ih]
    show _ = rget4 K1 K2 K3 K4 H (nxt (runR4 K1 K2 K3 K4 n1 m φ nxt H k)).1
        (pt4 n1 φ m (nxt (runR4 K1 K2 K3 K4 n1 m φ nxt H k))) :: runR4 K1 K2 K3 K4 n1 m φ nxt H k
    rw [rget4_prog h1 h2 h3 h4 H p a ha _ _ (hm _ (List.mem_cons_self ..))]

/-- An output from `k` adaptive reads over all four tables, the strategy
    chosen by the draw and the challenges' residues. -/
def outR4 {X O W : Type} (K1 K2 K3 K4 n1 B1 B2 B3 B4 k : Nat) (m1 : X → Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat × W)
    (g : Nat → Nat → Nat → Nat → X → List Nat → O) (H : Nat × Nat × Nat × Nat) (c4 c1 c2 c3 : Nat) (x : X) : O :=
  g c4 c1 c2 c3 x (runR4 K1 K2 K3 K4 n1 (m1 x) φ (nxt (c4 % B4) (c1 % B1) (c2 % B2) (c3 % B3) x) H k)

def hqR4 {X W : Type} (K1 K2 K3 K4 n1 B1 B2 B3 B4 k : Nat) (m1 : X → Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat × W) (H p : Nat × Nat × Nat × Nat) (x : X) : Bool :=
  (List.range B4).any (fun c4 => (List.range B1).any (fun c1 => (List.range B2).any (fun c2 =>
    (List.range B3).any (fun c3 =>
      (readsR4 K1 K2 K3 K4 n1 (m1 x) φ (nxt c4 c1 c2 c3 x) H k).any
        (fun r => decide (coord4 r.1 p = pt4 n1 φ (m1 x) r))))))

/-- **`hout` for adaptive reads of all four tables.** -/
theorem outR4_hout {X O W : Type} {K1 K2 K3 K4 n1 B1 B2 B3 B4 k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4) (hB1 : 0 < B1) (hB2 : 0 < B2) (hB3 : 0 < B3) (hB4 : 0 < B4) (m1 : X → Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat × W) (g : Nat → Nat → Nat → Nat → X → List Nat → O) :
    ∀ H p a c4 c1 c2 c3 x, a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4 →
      hqR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt H p x = false →
      outR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt g (prog4 K1 K2 K3 K4 H p a) c4 c1 c2 c3 x =
        outR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt g H c4 c1 c2 c3 x := by
  intro H p a c4 c1 c2 c3 x ha hq
  unfold outR4
  rw [runR4_prog h1 h2 h3 h4 φ _ H p a ha k (fun r hr e => ?_)]
  have hit : hqR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt H p x = true := by
    unfold hqR4
    exact List.any_eq_true.2 ⟨c4 % B4, List.mem_range.2 (Nat.mod_lt _ hB4),
      List.any_eq_true.2 ⟨c1 % B1, List.mem_range.2 (Nat.mod_lt _ hB1),
      List.any_eq_true.2 ⟨c2 % B2, List.mem_range.2 (Nat.mod_lt _ hB2),
      List.any_eq_true.2 ⟨c3 % B3, List.mem_range.2 (Nat.mod_lt _ hB3),
      List.any_eq_true.2 ⟨r, hr, decide_eq_true e⟩⟩⟩⟩⟩
  rw [hq] at hit; exact Bool.false_ne_true hit

/-- **`hpq` for adaptive reads of all four tables**: a fourth-table read
    landing on the programmed point hashes a message carrying the programmer's
    first message (`hpD`).  The circuits' query hashes give it: the programmed
    point is `φ j s3 w'` with `s3`'s digit the programmer's first message,
    and `hφs` (`φ i m w = φ j m' w' → m % n1 = m' % n1`) carries the digit
    across, whichever statement reads. -/
theorem outR4_hpq {X W : Type} {K1 K2 K3 K4 n1 B1 B2 B3 B4 k : Nat} (m1 : X → Nat) (hm1 : ∀ x, m1 x < n1)
    (φ : Nat → W → Nat) (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat × W)
    (H p : Nat × Nat × Nat × Nat) (hpA : p.1 < n1) (hpB : p.2.1 % n1 = p.1) (hpC : p.2.2.1 % n1 = p.1)
    (hpD : ∀ m w, φ m w = p.2.2.2 → m % n1 = p.1) (x : X) :
    hqR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt H p x = true → m1 x = p.1 := by
  intro h
  unfold hqR4 at h
  obtain ⟨c4, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨c1, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨c2, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨c3, _, h⟩ := List.any_eq_true.1 h
  obtain ⟨r, _, e⟩ := List.any_eq_true.1 h
  have e' : coord4 r.1 p = pt4 n1 φ (m1 x) r := of_decide_eq_true e
  have hmod : (m1 x + n1 * r.2.1) % n1 = m1 x := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hm1 x)]
  rcases r with ⟨i, kk, w⟩
  match i with
  | 0 => simp only [coord4, pt4] at e'; rw [← hmod, ← e', Nat.mod_eq_of_lt hpA]
  | 1 => simp only [coord4, pt4] at e'; rw [← hmod, ← e', hpB]
  | 2 => simp only [coord4, pt4] at e'; rw [← hmod, ← e', hpC]
  | j + 3 =>
    simp only [coord4, pt4] at e'
    rw [← hmod, hpD _ _ e'.symm]

/-- **The circuits' query hashes give `hpD`**: a programmed fourth-table point
    `φ j m' w'` whose message `m'` carries the programmer's first message, and
    hashes that keep the digit across statements (`hφs`, the circuits'
    hypothesis), make every reader's hash landing on it carry that digit. -/
theorem hpD_of_hφs {W : Type} {n1 : Nat} (φ : Nat → Nat → W → Nat)
    (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (i j m' : Nat) (w' : W)
    (p : Nat × Nat × Nat × Nat) (hp : p.2.2.2 = φ j m' w') (hm' : m' % n1 = p.1) :
    ∀ m w, φ i m w = p.2.2.2 → m % n1 = p.1 :=
  fun m w e => by rw [hp] at e; rw [hφs i j m w m' w' e, hm']

end Circuit
