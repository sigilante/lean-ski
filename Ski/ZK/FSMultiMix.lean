import Ski.ZK.FSMultiOpenRd

/-!
# Proofs and query phases interleaved

`FSMultiInterleave`'s `zkbT_powD_rd` composes components in any order.  Here
its components are four-round proofs (`FS4DT`, `fs4_powDT`'s data) and the
distinguisher's query phases, mixed by a pattern `isQ`: component `i` is a
query phase when `isQ i`, else proof `i`.  Every component takes the proof's
draws and challenges, and shows `(some view, [])` or `(none, answers)`;
a query phase programs nothing and ignores its draws (`mixRv`, `mixSv`).
Each proof reads the tables at a finite list (`hrdP`, met by
`FSMultiOpenRd`'s `sudFS4T_hrd`, `sudFS4T_hrdD`), each programmed
coordinate spreads (`hsp`), and the bound composes (`fs4_interleave`): a
query phase adds no error of its own, and its hits are charged to the
spread of the proofs that program after it (a query that lands on a later
proof's point is the real and simulated views' only difference; a hit on an
earlier proof's point reads the programmed table in both).  The bound is
unnormalized: a query phase's unused draws and challenges multiply both
sides alike and cancel.  Each proof's own bound is `fs4_powDT`'s hypothesis (the circuits'
`sud_fs4T` and the others).  The Sudoku proof's spread: `FSMultiMixSud`'s
`sudFS4T_hsp`.  Not shown: the hidden-term and composed circuits' spread; query phases reading at
points chosen from earlier views (`FSMultiViews`, stage by stage).
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- A component's view: a proof's, or a query phase's answers. -/
def mixRv {O : Type} (K1 K2 K3 K4 kq : Nat) (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit)
    (rvP : (i : Nat) → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Nat × Nat × Nat × O)
    (i : Nat) (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) :
    Option (Nat × Nat × Nat × O) × List Nat :=
  cond (isQ i) (none, advRun K1 K2 K3 K4 kq (nxtQ i) H) (some (rvP i H x), [])

/-- A component's simulated view. -/
def mixSv {O : Type} (K1 K2 K3 K4 kq : Nat) (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit)
    (svP : (i : Nat) → Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) →
      Nat × Nat × Nat × O)
    (i : Nat) (H c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) :
    Option (Nat × Nat × Nat × O) × List Nat :=
  cond (isQ i) (none, advRun K1 K2 K3 K4 kq (nxtQ i) H) (some (svP i H c x), [])

theorem lin_mul {X : Type} {s : (X → Nat) → Nat} (h : Lin s) (a : Nat) (f : X → Nat) :
    s (fun x => a * f x) = a * s f := by
  have e := h a (fun _ x => f x)
  simp only [sumTo_const] at e
  exact e

theorem lin_const {X : Type} {s : (X → Nat) → Nat} (h : Lin s) (a : Nat) : s (fun _ => a) = s (fun _ => 1) * a := by
  have e := lin_mul h a (fun _ => 1)
  simp only [Nat.mul_one] at e
  rw [e, Nat.mul_comm]

/-- **Proofs and query phases interleaved**: component `i` a query phase of
    `kq` adaptive queries when `isQ i`, else proof `i` with its `fs4_powDT`
    bound; each proof's view meets `hrd` with at most `RP i` reads, each
    programmed coordinate spreads (`hsp`). -/
theorem fs4_interleave {O : Type} {m K2 K4 N4 T1 T2 T3 kq : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (D : Nat → FS4DT O)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit)
    (rdP : Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → List (Nat × Nat))
    (hrdP : ∀ i H p a x, a.1 < Q4 * Q4 ∧ a.2.1 < K2 ∧ a.2.2.1 < Q4 ∧ a.2.2.2 < K4 →
      (rdP i H x).any (fun r => decide (coord4 r.1 p = r.2)) = false →
      read4T (Q4 * Q4) K2 Q4 K4 (D i).m1 (D i).m2 (D i).m3 (D i).q (D i).out (prog4 (Q4 * Q4) K2 Q4 K4 H p a) x =
        read4T (Q4 * Q4) K2 Q4 K4 (D i).m1 (D i).m2 (D i).m3 (D i).q (D i).out H x)
    (RP : Nat → Nat) (hRP : ∀ i H x, (rdP i H x).length ≤ RP i)
    (δq : Nat → Nat)
    (hsp : ∀ n, isQ n = false → ∀ c tab v, (D n).sm m (fun x => indB (decide (coord4 tab ((D n).pts c x) = v))) ≤ δq n) :
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo T1 (fun H1 =>
      sumTo T2 (fun H2 => sumTo T3 (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))
    let K := K4 * (Q4 * Q4 * (K2 * Q4))
    (∀ i, isQ i = false → ZKBT ST K ((D i).sm m) SC (read4T (Q4 * Q4) K2 Q4 K4 (D i).m1 (D i).m2 (D i).m3 (D i).q (D i).out)
      (fun H c x => prog4 (Q4 * Q4) K2 Q4 K4 H ((D i).pts c x) c) (D i).sv (D i).ε) →
    ∀ n, ZKBT ST (KPowD (fun _ => K) n) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => (D i).sm m) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => SC) n)
      (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 (D i).m1 (D i).m2 (D i).m3 (D i).q (D i).out)) n)
      (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => (D i).pts) (fun _ c => c)) n)
      (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => (D i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => (D i).sv)) n)
      (errPowD (fun _ => K) (fun i => (D i).sm m) (fun _ => SC) (fun i => cond (isQ i) 0 (D i).ε)
        (fun n => SC (fun _ => ST (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => (D i).sm m) n
          (fun _ => rSum (fun i => cond (isQ i) kq (RP i)) n * cond (isQ n) 0 (δq n))))) n) := by
  intro ST SC K hzk
  have hQ : 0 < Q4 * Q4 := Nat.mul_pos Q4_pos Q4_pos
  have hST : Lin ST := lin_sum4 _ _ _ _
  have hSC : Lin SC := lin_sum4 _ _ _ _
  let ok := fun (c : Nat × Nat × Nat × Nat) =>
    decide (c.1 < Q4 * Q4) && decide (c.2.1 < K2) && decide (c.2.2.1 < Q4) && decide (c.2.2.2 < K4)
  have hok : ∀ f g : Nat × Nat × Nat × Nat → Nat, (∀ c, ok c = true → f c ≤ g c) → SC f ≤ SC g := by
    intro f g h
    refine sumTo_mono _ (fun c4 h4 => sumTo_mono _ (fun c1 h1 => sumTo_mono _ (fun c2 h2 => sumTo_mono _ (fun c3 h3 =>
      h _ ?_))))
    simp only [ok, h1, h2, h3, h4, decide_true, Bool.and_self]
  have hcv : ∀ c, ok c = true → c.1 < Q4 * Q4 ∧ c.2.1 < K2 ∧ c.2.2.1 < Q4 ∧ c.2.2.2 < K4 := by
    intro c h
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  refine zkbT_powD_rd (fun _ => K) ST hST (fun i => (D i).sm m) (fun i => lin_sm _ _ _ _) (fun _ => SC) (fun _ => hSC)
    (fun i j => comm_sm (lin_sm _ _ _ _) _ _ _ _) (fun i => comm_sum4 (lin_sm _ _ _ _) _ _ _ _)
    (fun i j => comm_sum4 (lin_sm _ _ _ _) _ _ _ _) (fun i => comm_sum4 (lin_sum4 _ _ _ _) _ _ _ _)
    (fun i j => comm_sm (lin_sum4 _ _ _ _) _ _ _ _) (fun i => !isQ i)
    _ _ (fun _ c => c) _ (fun i => cond (isQ i) 0 (D i).ε) (fun i => ?_) (fun _ => ok) (fun _ => hok) (fun _ => hcv)
    (fun i H x => cond (isQ i) (advRd (Q4 * Q4) K2 Q4 K4 kq (nxtQ i) H) (rdP i H x)) (fun i H p a x ha hm => ?_)
    (fun i => cond (isQ i) kq (RP i)) (fun i H x => ?_) (fun n => cond (isQ n) 0 (δq n)) (fun n hp => ?_)
  · -- each component's bound
    cases hq : isQ i
    · intro E
      have h := hzk i hq (fun H v => E H (some v, []))
      simpa only [mixRv, mixSv, pgRd, hq, cond_false, cond_true, Bool.not_false] using h
    · intro E
      simp only [mixRv, mixSv, pgRd, hq, cond_true, Bool.not_true, cond_false, Nat.add_zero]
      have hsc : SC (fun _ => 1) = K := by
        show sumTo K4 (fun _ => sumTo (Q4 * Q4) (fun _ => sumTo K2 (fun _ => sumTo Q4 (fun _ => 1)))) = _
        simp only [sumTo_const, Nat.mul_one]; rfl
      have e : ∀ y, SC (fun _ => y) = K * y := fun y => by rw [lin_const hSC, hsc]
      simp only [e]
      exact Nat.le_of_eq (lin_mul hST K (fun H => (D i).sm m fun x => indB (E H (none, advRun (Q4 * Q4) K2 Q4 K4 kq (nxtQ i) H)))).symm
  · cases hq : isQ i
    · simp only [mixRv, hq, cond_false] at hm ⊢
      rw [hrdP i H p a x ha hm]
    · simp only [mixRv, hq, cond_true] at hm ⊢
      rw [advRd_hrd hQ hK2 Q4_pos hK4 (nxtQ i) H p a ha hm]
  · cases hq : isQ i
    · simp only [cond_false]; exact hRP i H x
    · simp only [cond_true, advRd_length]; exact Nat.le_refl _
  · have hq : isQ n = false := by simpa using hp
    simp only [hq, cond_false]
    exact hsp n hq

end Circuit
