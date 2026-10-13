import Ski.ZK.FSMultiQueries

/-!
# Query phases interleaved with proofs

`read4T_powD` charges a hit on a programmed point to the reader's first
message, which a distinguisher's query does not carry.  Here a hit is
charged to the programmer instead.  Each component, a proof or a query
phase, programs its points or nothing (`prg i`, `pgRd`) and reads the
tables at a finite list of points computed at the unprogrammed tables
(`rd i H x`, at most `R i`), its view unchanged by an in-range programming
they miss (`hrd`); every coordinate of each programmer's points spreads over
its draws (`hsp`).  Then `n` components compose in any order
(`zkbT_powD_rd`), a programming component's collision term the earlier
reads `rSum R n` times its spread (`hitPowDH_le`), a query phase's none.
Instances: a query phase (`adv_zkbT`, programming nothing; `advRd`,
`advRd_hrd`, `k` reads); a four-round proof reading the tables at its
messages (`rd4`, `rd4_hrd`, four reads); and one whose output also reads
them as `outR4` does (`rd4 ++ rdOut`, `rd4T_hrd`, `4 + B4 B1 B2 B3 k`
reads, `rdOut_length`).  Queries chosen from earlier proofs' views: `FSMultiViews`.  Not shown: the
circuits' openings as `outR4`s, so these interleavings do not cover them;
`FSMultiOpen` covers openings that read only at their digit (`RdOK`) in
`fs4_powDT`, without query phases.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- `hitPowD` over components of different draw types. -/
def hitPowDH {X : Nat → Type} (hit : (j : Nat) → X j → Bool) : (n : Nat) → PowD X n → Bool
  | 0, _ => false
  | n + 1, x => hit n x.1 || hitPowDH hit n x.2

theorem readPowDH {T : Type} {X V : Nat → Type} (rv : (i : Nat) → T → X i → V i) (H H' : T)
    (hit : (j : Nat) → X j → Bool) (h : ∀ j x, hit j x = false → rv j H' x = rv j H x) :
    ∀ n xs, hitPowDH hit n xs = false → rvPowD rv n H' xs = rvPowD rv n H xs
  | 0, _, _ => rfl
  | n + 1, xs, hx => by
    simp only [hitPowDH, Bool.or_eq_false_iff] at hx
    show (rv n H' xs.1, rvPowD rv n H' xs.2) = (rv n H xs.1, rvPowD rv n H xs.2)
    rw [h n xs.1 hx.1, readPowDH rv H H' hit h n xs.2 hx.2]

theorem indB_or_le (a b : Bool) : indB (a || b) ≤ indB a + indB b := by cases a <;> cases b <;> decide

/-- A list of reads `(table, point)` hits the programmed points of at most
    `|l| δq` draws, every coordinate of the points spreading (`hsp`). -/
theorem reads_hits_le {XA : Type} (smA : (XA → Nat) → Nat) (hsA : Lin smA) (pts : XA → Nat × Nat × Nat × Nat)
    (δq : Nat) (hsp : ∀ i v, smA (fun xa => indB (decide (coord4 i (pts xa) = v))) ≤ δq) :
    ∀ (l : List (Nat × Nat)), smA (fun xa => indB (l.any (fun r => decide (coord4 r.1 (pts xa) = r.2)))) ≤
      l.length * δq
  | [] => by
    show smA (fun _ => 0) ≤ 0 * δq
    have e := hsA 0 (fun _ _ => 0)
    simp only [sumTo] at e
    rw [e, Nat.zero_mul]; exact Nat.le_refl _
  | r :: l => by
    have ih := reads_hits_le smA hsA pts δq hsp l
    have hpt : ∀ xa, indB ((r :: l).any (fun r => decide (coord4 r.1 (pts xa) = r.2))) ≤
        indB (decide (coord4 r.1 (pts xa) = r.2)) + indB (l.any (fun r => decide (coord4 r.1 (pts xa) = r.2))) :=
      fun xa => by rw [List.any_cons]; exact indB_or_le _ _
    refine Nat.le_trans (sm_mono smA hsA hpt) ?_
    rw [sm_add smA hsA, List.length_cons, Nat.succ_mul, Nat.add_comm (l.length * δq)]
    exact Nat.add_le_add (hsp _ _) ih

/-- The reads' total bound over the first `n` components. -/
def rSum (R : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => R n + rSum R n

/-- The earlier components' reads, at fixed tables and draws, hit the
    programmed points of at most `rSum R n · δq` of the new draws. -/
theorem hitPowDH_le {X : Nat → Type} {XA : Type} (smA : (XA → Nat) → Nat) (hsA : Lin smA)
    (pts : XA → Nat × Nat × Nat × Nat) (δq : Nat) (hsp : ∀ i v, smA (fun xa => indB (decide (coord4 i (pts xa) = v))) ≤ δq)
    (rd : (j : Nat) → X j → List (Nat × Nat)) (R : Nat → Nat) (hR : ∀ j x, (rd j x).length ≤ R j) :
    ∀ n (xs : PowD X n), smA (fun xa => indB (hitPowDH (fun j x => (rd j x).any (fun r =>
      decide (coord4 r.1 (pts xa) = r.2))) n xs)) ≤ rSum R n * δq
  | 0, _ => by
    show smA (fun _ => 0) ≤ 0 * δq
    have e := hsA 0 (fun _ _ => 0)
    simp only [sumTo] at e
    rw [e, Nat.zero_mul]; exact Nat.le_refl _
  | n + 1, xs => by
    have ih := hitPowDH_le smA hsA pts δq hsp rd R hR n xs.2
    have hpt : ∀ xa, indB (hitPowDH (fun j x => (rd j x).any (fun r => decide (coord4 r.1 (pts xa) = r.2))) (n + 1) xs) ≤
        indB ((rd n xs.1).any (fun r => decide (coord4 r.1 (pts xa) = r.2))) +
          indB (hitPowDH (fun j x => (rd j x).any (fun r => decide (coord4 r.1 (pts xa) = r.2))) n xs.2) := fun xa => by
      exact indB_or_le _ _
    refine Nat.le_trans (sm_mono smA hsA hpt) ?_
    rw [sm_add smA hsA]
    show _ ≤ (R n + rSum R n) * δq
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.le_trans (reads_hits_le smA hsA pts δq hsp _) (Nat.mul_le_mul_right _ (hR n xs.1))) ih

/-- A count of zeros is zero. -/
theorem count_zero {Y : Type} (s : (Y → Nat) → Nat) (h : Lin s) : s (fun _ => 0) = 0 := by
  have e := h 0 (fun _ _ => 0); simp only [sumTo] at e; exact e

/-- A component's programming: its points, or nothing (`prg i = false`, a
    query phase). -/
def pgRd (K1 K2 K3 K4 : Nat) {X C : Nat → Type} (prg : Nat → Bool) (pts : (i : Nat) → C i → X i → Nat × Nat × Nat × Nat)
    (cv : (i : Nat) → C i → Nat × Nat × Nat × Nat) (i : Nat) (H : Nat × Nat × Nat × Nat) (c : C i) (x : X i) :
    Nat × Nat × Nat × Nat :=
  cond (prg i) (prog4 K1 K2 K3 K4 H (pts i c x) (cv i c)) H

/-- **`n` components under one oracle, each hit charged to the programmer**:
    proofs and query phases alike (`prg i`: whether component `i` programs
    the tables), each component's view reading the tables at a finite list of
    points (`rd i H x`, at most `R i` of them, computed at the unprogrammed
    tables, its view unchanged by an in-range programming they miss: `hrd`),
    and every coordinate of each programmer's points spreading over its draws
    (`hsp`).  The collision term at a programming `n`-th component is the
    earlier components' reads, `rSum R n`, times its spread `δq n`
    (`hitPowDH_le`); a component that programs nothing has none.  No read
    need carry a first message. -/
theorem zkbT_powD_rd {X C V : Nat → Type} {K1 K2 K3 K4 : Nat} (K : Nat → Nat)
    (ST : (Nat × Nat × Nat × Nat → Nat) → Nat) (hST : Lin ST)
    (sm : (i : Nat) → (X i → Nat) → Nat) (hs : ∀ i, Lin (sm i))
    (sc : (i : Nat) → (C i → Nat) → Nat) (hc : ∀ i, Lin (sc i))
    (c1 : ∀ i j, Comm (sm i) (sm j)) (c2 : ∀ i, Comm ST (sm i)) (c3 : ∀ i j, Comm (sc i) (sm j))
    (c4 : ∀ i, Comm ST (sc i)) (c7 : ∀ i j, Comm (sm i) (sc j)) (prg : Nat → Bool)
    (rv : (i : Nat) → Nat × Nat × Nat × Nat → X i → V i) (pts : (i : Nat) → C i → X i → Nat × Nat × Nat × Nat)
    (cv : (i : Nat) → C i → Nat × Nat × Nat × Nat) (sv : (i : Nat) → Nat × Nat × Nat × Nat → C i → X i → V i)
    (ε : Nat → Nat)
    (hzk : ∀ i, ZKBT ST (K i) (sm i) (sc i) (rv i) (pgRd K1 K2 K3 K4 prg pts cv i) (sv i) (ε i))
    (ok : (i : Nat) → C i → Bool) (hok : ∀ i (f g : C i → Nat), (∀ c, ok i c = true → f c ≤ g c) → sc i f ≤ sc i g)
    (hcv : ∀ i c, ok i c = true → (cv i c).1 < K1 ∧ (cv i c).2.1 < K2 ∧ (cv i c).2.2.1 < K3 ∧ (cv i c).2.2.2 < K4)
    (rd : (i : Nat) → Nat × Nat × Nat × Nat → X i → List (Nat × Nat))
    (hrd : ∀ i H p a x, a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4 →
      (rd i H x).any (fun r => decide (coord4 r.1 p = r.2)) = false → rv i (prog4 K1 K2 K3 K4 H p a) x = rv i H x)
    (R : Nat → Nat) (hR : ∀ i H x, (rd i H x).length ≤ R i)
    (δq : Nat → Nat)
    (hsp : ∀ n, prg n = true → ∀ c tab v, sm n (fun x => indB (decide (coord4 tab (pts n c x) = v))) ≤ δq n) :
    ∀ n, ZKBT ST (KPowD K n) (smPowD sm n) (scPowD sc n) (rvPowD rv n)
      (pgPowD (pgRd K1 K2 K3 K4 prg pts cv) n) (svPowDT (pgRd K1 K2 K3 K4 prg pts cv) sv n)
      (errPowD K sm sc ε (fun n => sc n (fun _ => ST (fun _ => smPowD sm n (fun _ => rSum R n * δq n)))) n) := by
  refine zkbT_powD K ST hST sm hs sc hc c1 c2 c3 c4 c7 rv (pgRd K1 K2 K3 K4 prg pts cv) sv ε _ hzk ok hok
    (fun n H ca xa xb => prg n &&
      hitPowDH (fun j x => (rd j H x).any (fun r => decide (coord4 r.1 (pts n ca xa) = r.2))) n xb)
    (fun n H ca xa xb hok' hcl => ?_) (fun n => ?_)
  · unfold pgRd
    cases hp : prg n
    · rfl
    · rw [hp, Bool.true_and] at hcl
      exact readPowDH rv H (prog4 K1 K2 K3 K4 H (pts n ca xa) (cv n ca)) _
        (fun j x hj => hrd j H (pts n ca xa) (cv n ca) x (hcv n ca hok') hj) n xb hcl
  · refine sm_mono (sc n) (hc n) (fun ca => ?_)
    cases hp : prg n
    · simp only [Bool.false_and]
      show sm n (fun _ => ST (fun _ => smPowD sm n (fun _ => indB false))) ≤ _
      rw [show indB false = 0 from rfl, count_zero _ (lin_smPowD hs n), count_zero ST hST, count_zero (sm n) (hs n)]
      exact Nat.zero_le _
    · simp only [Bool.true_and]
      rw [c2 n (fun H xa => smPowD sm n (fun xb => indB (hitPowDH (fun j x => (rd j H x).any
        (fun r => decide (coord4 r.1 (pts n ca xa) = r.2))) n xb)))]
      refine sm_mono ST hST (fun H => ?_)
      rw [← comm_smPowD' (fun i => c1 n i) n (fun xa xb => indB (hitPowDH (fun j x => (rd j H x).any
        (fun r => decide (coord4 r.1 (pts n ca xa) = r.2))) n xb))]
      exact sm_mono _ (lin_smPowD hs n) (fun xb => hitPowDH_le (sm n) (hs n) (pts n ca) (δq n) (hsp n hp ca)
        (fun j x => rd j H x) R (fun j x => hR j H x) n xb)

/-- A query phase's reads: its queries' `(table, point)`s, made at `H`. -/
def advRd (K1 K2 K3 K4 k : Nat) (nxt : List Nat → Nat × Nat × Unit) (H : Nat × Nat × Nat × Nat) : List (Nat × Nat) :=
  (readsR4 K1 K2 K3 K4 1 0 (fun m _ => m) nxt H k).map (fun r => (r.1, pt4 1 (fun m _ => m) 0 r))

/-- **A query phase meets `hrd`**: its answers are unchanged by an in-range
    programming its queries miss (`runR4_prog`). -/
theorem advRd_hrd {K1 K2 K3 K4 k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (nxt : List Nat → Nat × Nat × Unit) (H p a : Nat × Nat × Nat × Nat)
    (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4)
    (hm : (advRd K1 K2 K3 K4 k nxt H).any (fun r => decide (coord4 r.1 p = r.2)) = false) :
    advRun K1 K2 K3 K4 k nxt (prog4 K1 K2 K3 K4 H p a) = advRun K1 K2 K3 K4 k nxt H :=
  runR4_prog h1 h2 h3 h4 _ nxt H p a ha k (fun r hr e => by
    have hit : (advRd K1 K2 K3 K4 k nxt H).any (fun r => decide (coord4 r.1 p = r.2)) = true :=
      List.any_eq_true.2 ⟨(r.1, pt4 1 (fun m _ => m) 0 r), List.mem_map.2 ⟨r, hr, rfl⟩, decide_eq_true e⟩
    rw [hm] at hit; exact Bool.false_ne_true hit)

theorem advRd_length (K1 K2 K3 K4 k : Nat) (nxt : List Nat → Nat × Nat × Unit) (H : Nat × Nat × Nat × Nat) :
    (advRd K1 K2 K3 K4 k nxt H).length = k := by
  unfold advRd; rw [List.length_map, readsR4_length]

/-- A four-round proof's reads: its four messages, read off the tables `H`. -/
def rd4 {X : Type} (K1 K2 K3 : Nat) (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat)
    (q : Nat → Nat → Nat → X → Nat) (H : Nat × Nat × Nat × Nat) (x : X) : List (Nat × Nat) :=
  [(0, m1 x), (1, m2 (rget K1 (m1 x) H.1) x),
   (2, m3 (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1) x),
   (3, q (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1)
     (rget K3 (m3 (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1) x) H.2.2.1) x)]

/-- **A four-round proof's view meets `hrd`** (`read4_beside`), four reads. -/
theorem rd4_hrd {X O : Type} {K1 K2 K3 K4 : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (q : Nat → Nat → Nat → X → Nat)
    (out : Nat → Nat → Nat → Nat → X → O) (H p a : Nat × Nat × Nat × Nat)
    (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (x : X)
    (hm : (rd4 K1 K2 K3 m1 m2 m3 q H x).any (fun r => decide (coord4 r.1 p = r.2)) = false) :
    read4 K1 K2 K3 K4 m1 m2 m3 q out (prog4 K1 K2 K3 K4 H p a) x = read4 K1 K2 K3 K4 m1 m2 m3 q out H x := by
  refine read4_beside h1 h2 h3 h4 m1 m2 m3 q out H p a ha x ?_
  simp only [rd4, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff, decide_eq_false_iff_not, coord4] at hm
  obtain ⟨e0, e1, e2, e3⟩ := hm
  simp only [hit4, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨⟨⟨fun e => e0 e.symm, fun e => e1 e.symm⟩, fun e => e2 e.symm⟩, fun e => e3 e.symm⟩

theorem rd4_length {X : Type} (K1 K2 K3 : Nat) (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat)
    (q : Nat → Nat → Nat → X → Nat) (H : Nat × Nat × Nat × Nat) (x : X) : (rd4 K1 K2 K3 m1 m2 m3 q H x).length = 4 := rfl

/-- **A query phase is a component**: its bound holds trivially, it
    programming nothing (`prg i = false` in `zkbT_powD_rd`). -/
theorem adv_zkbT {K1 K2 K3 K4 k : Nat} (ST : (Nat × Nat × Nat × Nat → Nat) → Nat)
    (nxt : List Nat → Nat × Nat × Unit) :
    ZKBT ST 1 (fun f : Unit → Nat => f ()) (fun g : Unit → Nat => g ()) (fun H _ => advRun K1 K2 K3 K4 k nxt H)
      (fun H _ _ => H) (fun H _ _ => advRun K1 K2 K3 K4 k nxt H) 0 := fun E => by
  rw [Nat.one_mul, Nat.add_zero]; exact Nat.le_refl _

theorem length_flatMap_range_le {α : Type} (f : Nat → List α) (c : Nat) (hf : ∀ i, (f i).length ≤ c) :
    ∀ N, ((List.range N).flatMap f).length ≤ N * c
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, Nat.succ_mul]
    have := length_flatMap_range_le f c hf N
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact Nat.add_le_add this (hf N)

/-- An `outR4` output's reads at every residue of the challenges. -/
def rdOut {X W : Type} (K1 K2 K3 K4 n1 B1 B2 B3 B4 k : Nat) (m1 : X → Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat × W) (H : Nat × Nat × Nat × Nat) (x : X) :
    List (Nat × Nat) :=
  (List.range B4).flatMap (fun c4 => (List.range B1).flatMap (fun c1 => (List.range B2).flatMap (fun c2 =>
    (List.range B3).flatMap (fun c3 =>
      (readsR4 K1 K2 K3 K4 n1 (m1 x) φ (nxt c4 c1 c2 c3 x) H k).map (fun r => (r.1, pt4 n1 φ (m1 x) r))))))

theorem rdOut_length {X W : Type} (K1 K2 K3 K4 n1 B1 B2 B3 B4 k : Nat) (m1 : X → Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat × W) (H : Nat × Nat × Nat × Nat) (x : X) :
    (rdOut K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt H x).length ≤ B4 * (B1 * (B2 * (B3 * k))) := by
  unfold rdOut
  refine length_flatMap_range_le _ _ (fun c4 => length_flatMap_range_le _ _ (fun c1 =>
    length_flatMap_range_le _ _ (fun c2 => length_flatMap_range_le _ _ (fun c3 => ?_) B3) B2) B1) B4
  rw [List.length_map, readsR4_length]; exact Nat.le_refl _

theorem hqR4_rdOut {X W : Type} {K1 K2 K3 K4 n1 B1 B2 B3 B4 k : Nat} (m1 : X → Nat) (φ : Nat → W → Nat)
    (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat × W) (H p : Nat × Nat × Nat × Nat) (x : X)
    (h : hqR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt H p x = true) :
    (rdOut K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt H x).any (fun r => decide (coord4 r.1 p = r.2)) = true := by
  unfold hqR4 at h
  obtain ⟨c4, h4, h⟩ := List.any_eq_true.1 h
  obtain ⟨c1, h1, h⟩ := List.any_eq_true.1 h
  obtain ⟨c2, h2, h⟩ := List.any_eq_true.1 h
  obtain ⟨c3, h3, h⟩ := List.any_eq_true.1 h
  obtain ⟨r, hr, e⟩ := List.any_eq_true.1 h
  refine List.any_eq_true.2 ⟨(r.1, pt4 n1 φ (m1 x) r), ?_, e⟩
  unfold rdOut
  exact List.mem_flatMap.2 ⟨c4, h4, List.mem_flatMap.2 ⟨c1, h1, List.mem_flatMap.2 ⟨c2, h2,
    List.mem_flatMap.2 ⟨c3, h3, List.mem_map.2 ⟨r, hr, rfl⟩⟩⟩⟩⟩

/-- **A four-round proof whose output reads the tables meets `hrd`**: its
    messages' reads and its output's reads at every residue (`rd4 ++ rdOut`),
    by `read4T_beside` and `outR4_hout`. -/
theorem rd4T_hrd {X O W : Type} {K1 K2 K3 K4 n1 B1 B2 B3 B4 k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4) (hB1 : 0 < B1) (hB2 : 0 < B2) (hB3 : 0 < B3) (hB4 : 0 < B4)
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (q : Nat → Nat → Nat → X → Nat)
    (φ : Nat → W → Nat) (nxt : Nat → Nat → Nat → Nat → X → List Nat → Nat × Nat × W)
    (g : Nat → Nat → Nat → Nat → X → List Nat → O) (H p a : Nat × Nat × Nat × Nat)
    (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (x : X)
    (hm : (rd4 K1 K2 K3 m1 m2 m3 q H x ++ rdOut K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt H x).any
      (fun r => decide (coord4 r.1 p = r.2)) = false) :
    read4T K1 K2 K3 K4 m1 m2 m3 q (outR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt g) (prog4 K1 K2 K3 K4 H p a) x =
      read4T K1 K2 K3 K4 m1 m2 m3 q (outR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt g) H x := by
  rw [List.any_append, Bool.or_eq_false_iff] at hm
  obtain ⟨hm4, hmo⟩ := hm
  refine read4T_beside h1 h2 h3 h4 m1 m2 m3 q _ (hqR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt)
    (outR4_hout h1 h2 h3 h4 hB1 hB2 hB3 hB4 m1 φ nxt g) H p a ha x ?_
  rw [Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · simp only [rd4, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff, decide_eq_false_iff_not, coord4] at hm4
    obtain ⟨e0, e1, e2, e3⟩ := hm4
    simp only [hit4, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨⟨⟨fun e => e0 e.symm, fun e => e1 e.symm⟩, fun e => e2 e.symm⟩, fun e => e3 e.symm⟩
  · cases hq : hqR4 K1 K2 K3 K4 n1 B1 B2 B3 B4 k m1 φ nxt H p x
    · rfl
    · rw [hqR4_rdOut m1 φ nxt H p x hq] at hmo; exact absurd hmo (by decide)

end Circuit
