import Ski.ZK.FSRounds3

/-!
# Three Fiat–Shamir rounds, every commitment opened

The second and third commitments, the permutation trace's and the
quotient's, hide jointly as a pair, their salts drawn independently
(`ComHides.prod`, `ComPfHides.prod`); `open_two_core` then reduces the real
count with all three commitments to view events, and `fs_zk3` hashes the
three rounds (`fs_open3`).
-/

namespace Circuit

open ZKF

/-- Two commitments as one, their salts one number's digits. -/
def comPair {D2 D3 : Type} (NS2 n2 : Nat) (Com2 : D2 → Nat → Nat) (Com3 : D3 → Nat → Nat) (d : D2 × D3) (σ : Nat) : Nat :=
  Com2 d.1 (σ % NS2) + n2 * Com3 d.2 (σ / NS2)

def pfPair {D2 D3 P2 P3 : Type} (NS2 : Nat) (Pf2 : D2 → Nat → P2) (Pf3 : D3 → Nat → P3) (d : D2 × D3) (σ : Nat) :
    P2 × P3 :=
  (Pf2 d.1 (σ % NS2), Pf3 d.2 (σ / NS2))

theorem split_salt {NS2 NS3 : Nat} (g : Nat → Nat → Nat) :
    sumTo (NS2 * NS3) (fun σ => g (σ % NS2) (σ / NS2)) = sumTo NS3 (fun σ3 => sumTo NS2 (fun σ2 => g σ2 σ3)) := by
  rw [sumTo_split NS2 _ NS3]
  refine sumTo_congr _ (fun σ3 _ => sumTo_congr _ (fun σ2 hσ2 => ?_))
  have hpos : 0 < NS2 := Nat.lt_of_le_of_lt (Nat.zero_le _) hσ2
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hσ2, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hσ2,
    Nat.zero_add]

/-- **Two hiding commitments hide as a pair.** -/
theorem ComHides.prod {D2 D3 : Type} {NS2 NS3 n2 : Nat} {Com2 : D2 → Nat → Nat} {Com3 : D3 → Nat → Nat}
    (h2 : ComHides NS2 Com2) (h3 : ComHides NS3 Com3) : ComHides (NS2 * NS3) (comPair NS2 n2 Com2 Com3) := by
  intro d d' E
  unfold comPair
  rw [split_salt (fun a b => indB (E (Com2 d.1 a + n2 * Com3 d.2 b))),
    split_salt (fun a b => indB (E (Com2 d'.1 a + n2 * Com3 d'.2 b)))]
  rw [sumTo_congr _ (fun σ3 _ => h2 d.1 d'.1 (fun c => E (c + n2 * Com3 d.2 σ3)))]
  rw [sumTo_exch _ NS2 NS3, sumTo_exch _ NS2 NS3]
  exact sumTo_congr _ (fun σ2 _ => h3 d.2 d'.2 (fun c => E (Com2 d'.1 σ2 + n2 * c)))

/-- **Two commitments hiding given their openings hide so as a pair.** -/
theorem ComPfHides.prod {D2 D3 O2 O3 P2 P3 : Type} {NS2 NS3 n2 : Nat} {Com2 : D2 → Nat → Nat}
    {Com3 : D3 → Nat → Nat} {Pf2 : D2 → Nat → P2} {Pf3 : D3 → Nat → P3} {op2 : D2 → O2} {op3 : D3 → O3}
    (h2 : ComPfHides NS2 Com2 Pf2 op2) (h3 : ComPfHides NS3 Com3 Pf3 op3) :
    ComPfHides (NS2 * NS3) (comPair NS2 n2 Com2 Com3) (pfPair NS2 Pf2 Pf3) (fun d => (op2 d.1, op3 d.2)) := by
  intro d d' hop E
  have e1 : op2 d.1 = op2 d'.1 := congrArg Prod.fst hop
  have e2 : op3 d.2 = op3 d'.2 := congrArg Prod.snd hop
  unfold comPair pfPair
  rw [split_salt (fun a b => indB (E (Com2 d.1 a + n2 * Com3 d.2 b) (Pf2 d.1 a, Pf3 d.2 b))),
    split_salt (fun a b => indB (E (Com2 d'.1 a + n2 * Com3 d'.2 b) (Pf2 d'.1 a, Pf3 d'.2 b)))]
  rw [sumTo_congr _ (fun σ3 _ => h2 d.1 d'.1 e1 (fun c p => E (c + n2 * Com3 d.2 σ3) (p, Pf3 d.2 σ3)))]
  rw [sumTo_exch _ NS2 NS3, sumTo_exch _ NS2 NS3]
  exact sumTo_congr _ (fun σ2 _ => h3 d.2 d'.2 e2 (fun c p => E (Com2 d'.1 σ2 + n2 * c) (Pf2 d'.1 σ2, p)))

theorem comPair_mod {D2 D3 : Type} {NS2 n2 : Nat} {Com2 : D2 → Nat → Nat} (Com3 : D3 → Nat → Nat)
    (hr2 : ∀ d σ, Com2 d σ < n2) (d : D2 × D3) (σ : Nat) :
    comPair NS2 n2 Com2 Com3 d σ % n2 = Com2 d.1 (σ % NS2) := by
  unfold comPair; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hr2 _ _)]

/-- The pair of openings where the view shows both. -/
def ovPair {PV PB O2 O3 : Type} (ov2 : TViewN PV PB → Option O2) (ov3 : TViewN PV PB → Option O3)
    (v : TViewN PV PB) : Option (O2 × O3) :=
  match ov2 v, ov3 v with
  | some a, some b => some (a, b)
  | _, _ => none

/-- **Fiat–Shamir over three rounds, every commitment opened**, in the
    programmable random-oracle model: the real proof commits its first
    message, gets the LogUp challenges; commits its second (`main2`, after
    them), gets the second challenge; commits its third (`main3`, after
    both), gets the third; each challenge the oracle's answer at the
    transcript so far.  Its output is the openings where it does not
    abort and the view at the second and third challenges' transcript.
    The simulator commits and opens data through its own view's openings
    and programs all three tables.  Where the transcript bound holds at
    each guarded pair of later challenges, `Q4² K2 K3` times the real
    count is at most the simulator's plus `(Q4²)^n1 K2^(n1 n2)
    K3^(n1 n2 n3) K2 K3 NS1 NS2 NS3 (e1 + e2)`; one direction only.  One proof per oracle.  The guard `gz`
    drops the excluded challenges from both counts; their mass is not in
    the bound. -/
theorem fs_open3 {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3)
    (rv sv : Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    (hrv : ∀ c2 c3 α β r t, rv c2 c3 α β r t = none ∨ ∃ p x y, rv c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 c3 α β r t, ∃ p x y, sv c2 c3 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (Pf1 : D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) (hp1 : ComPfHides NS1 Com1 Pf1 op1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : TViewN PV PB → Option O1) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ComPfHides NS2 Com2 Pf2 op2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : TViewN PV PB → Option O2) (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3 : D3 → Nat → P3) (op3 : D3 → O3) (sd3 : O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ComPfHides NS3 Com3 Pf3 op3) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : TViewN PV PB → Option O3) (hov3 : ov3 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c c' t r, op3 (sd3 (op3 (main3 c c' t r))) = op3 (main3 c c' t r))
    (hvo1 : ∀ c2 c3 c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 (main1 t r)))
    (hvo2 : ∀ c2 c3 c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r)))
    (hvo3 : ∀ c2 c3 c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c2 c3 c r t, ov1 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 c3 r t))
    (hsvo2 : ∀ c2 c3 c r t, ov2 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c3 c r t))
    (hsvo3 : ∀ c2 c3 c r t, ov3 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair ov2 ov3 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 Pf2 Pf3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * Com2 (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 Pf2 Pf3 (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 c3 : Nat) => genB (efOf (c1 % Q4)) && gz c2 c3
    (Q4 * Q4) * (K2 * (K3 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
          (rget K3 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) &&
        E H1 H2 H3 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
            (rget K3 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && E (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (svo c1 c2 c3 x))))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2))))))) := by
  intro sm m1 m2 m3 rvo s1 s2 s3 svo gd
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2 * NS3) (NR := NR) (m := m) (N := N)
      (fun i σ r t => f i (σ1, σ, r, t)))]
    exact sumTo_exch _ N NS1
  have hc23 : ∀ d σ, comPair NS2 n2 Com2 Com3 d σ < n2 * n3 := fun d σ => by
    unfold comPair; exact pair_lt (hr2 _ _) (hr3 _ _)
  refine fs_zk3 (K1 := Q4 * Q4) (K2 := K2) (K3 := K3) (n1 := n1) (n2 := n1 * n2) (n3 := n1 * (n2 * n3))
    (Nat.mul_pos Q4_pos Q4_pos) hK2 hK3 sm hsm m1 m2 m3 (fun x => hr1 _ _) (fun _ x => pair_lt (hr1 _ _) (hr2 _ _))
    (fun _ _ x => pair_lt (hr1 _ _) (hc23 _ _)) s1 s2 s3 rvo svo gd (fun F => ?_) E
  rw [sumTo_exch _ K2 (Q4 * Q4), sumTo_exch _ K2 (Q4 * Q4)]
  rw [sumTo_congr _ (fun c2 _ => sumTo_exch _ K3 (Q4 * Q4)), sumTo_congr _ (fun c2 _ => sumTo_exch _ K3 (Q4 * Q4))]
  rw [← sumTo_const (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) K2, ← sumTo_add]
  refine sumTo_mono _ (fun c2 _ => ?_)
  rw [← sumTo_const (NS1 * (NS2 * NS3 * (e1 + e2))) K3, ← sumTo_add]
  refine sumTo_mono _ (fun c3 _ => ?_)
  cases hg : gz c2 c3
  · simp only [gd, hg, Bool.and_false, Bool.false_and]
    exact Nat.le_add_right _ _
  · simp only [gd, hg, Bool.and_true]
    have hov23 : ovPair ov2 ov3 none = none := by unfold ovPair; rw [hov2, hov3]
    have hvo23 : ∀ c r t, rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
        ovPair ov2 ov3 (rv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r), op3 (main3 c c2 t r)) :=
      fun c r t => by
        rcases hvo2 c2 c3 c r t with e | e
        · exact .inl e
        · rcases hvo3 c2 c3 c r t with e' | e'
          · exact .inl e'
          · exact .inr (by unfold ovPair; rw [e, e'])
    have hsvo23 : ∀ c r t, ovPair ov2 ov3 (sv c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
        some (sop2 c2 c3 c r t, sop3 c2 c3 c r t) := fun c r t => by
      unfold ovPair; rw [hsvo2 c2 c3 c r t, hsvo3 c2 c3 c r t]
    have core := open_two_core (NR := NR) (m := m) (rv c2 c3) (sv c2 c3) (hrv c2 c3) (hsv c2 c3) (h1 c2 c3 hg)
      (h2 c2 c3 hg) Com1 Pf1 op1 sd1 d1 hc1 hp1 ov1 hov1 main1 hsd1
      (comPair NS2 n2 Com2 Com3) (pfPair NS2 Pf2 Pf3) (fun d => (op2 d.1, op3 d.2)) (fun o => (sd2 o.1, sd3 o.2))
      (d2, d3) (ComHides.prod hc2 hc3) (ComPfHides.prod hp2 hp3) (ovPair ov2 ov3) hov23
      (fun c t r => (main2 c t r, main3 c c2 t r))
      (fun c t r => by show (op2 (sd2 (op2 (main2 c t r))), op3 (sd3 (op3 (main3 c c2 t r)))) = _; rw [hsd2, hsd3])
      (hvo1 c2 c3) hvo23 (sop1 c2 c3) (fun c r t => (sop2 c2 c3 c r t, sop3 c2 c3 c r t)) (hsvo1 c2 c3) hsvo23
      (fun c a b p q w => F c c2 c3 a (a + n1 * (b % n2)) (a + n1 * b) (p, q, w))
    simp only [comPair_mod Com3 hr2] at core
    exact core

section
open B Air Stmt Mach Sudoku SudokuText

set_option maxRecDepth 100000 in
/-- **The Sudoku PCS's shape reads neither `ζ` nor the weights**, only
    their lengths. -/
theorem sud_same_w (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table) (tp : Nat)
    (S16 S10 SP : List F) (ζ ζ' : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wm' wc' ww' wp' : List (EF → EF → List F)) (ncw : Nat)
    (hm : wm.length = wm'.length) (hc : wc.length = wc'.length) (hw : ww.length = ww'.length)
    (hp : wp.length = wp'.length) :
    SameShape (sudGroups tp S16 S10 SP ζ qv) (sudGroups tp S16 S10 SP ζ' qv) (sudKs hd0 stk0 ctr0 heap)
      ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst)
      ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ' qv wm' wc' ww' wp').map Prod.fst) ncw where
  trn := rfl
  dom := rfl
  S := rfl
  shape := by
    simp only [sudTs, bbTab, airQTabG, tShape, List.map_cons, List.map_nil, List.length_map]
    rw [hm, hc, hw, hp]
  tS := by simp only [sudTs, bbTab, airQTabG, List.map_cons, List.map_nil]
  iS := by simp only [sudTs, bbTab, airQTabG, tabsInfo, tInfo, List.map_cons, List.map_nil, List.map_append,
    List.map_replicate]

/-- **The quotient tables' shapes read the tables' preprocessed columns
    only**, as the simulator does (`sudPsim_pre`): the simulated openings
    of `sud_fs_open3` read the tables only through these shapes. -/
theorem sudTs_pre (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell)
    {C Mm Wt C' Mm' Wt' : Table} (hC : C.pre = C'.pre) (hM : Mm.pre = Mm'.pre) (hW : Wt.pre = Wt'.pre) (tp : Nat)
    (S16 S10 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) :
    (sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst =
      (sudTs off hd0 stk0 ctr0 heap C' Mm' Wt' tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst := by
  simp only [sudTs, List.map_cons, List.map_nil, bbTab, preInterp_pre hC, preInterp_pre hM, preInterp_pre hW]
end

section
open B Air Stmt Mach Sudoku SudokuText

set_option maxRecDepth 100000 in
/-- **The Sudoku proof over three Fiat–Shamir rounds, every commitment
    opened**, in the programmable random-oracle model: the LogUp
    challenges hashed from the main matrices' commitment, the
    constraint-folding challenge (which picks the quotient's weights) from
    the transcript with the permutation matrices' commitment, `ζ` from the
    transcript with the quotient chunks' commitment; each commitment
    opened beside the view; the simulator commits and opens interpolants
    through its own view's openings and programs all three tables
    (`fs_open3`).  Assumed: each commitment hides alone and given its
    openings at the real query points, perfectly, and is a primitive apart
    from the oracle; generic `β` and `ζ`, the other draws dropped from
    both counts, their mass outside the bound; the weights a family of
    fixed lengths; the FRI challenge `αb` and the query points fixed
    parameters, unhashed; one proof per oracle.  The third commitment's
    data are taken at `ζ = 0`: without an abort they equal the data at
    every `ζ` (`sud_data_zeta`), and with one only the commitment shows.
    The simulator reads the tables only through `sudPsim` and the quotient
    tables' shapes, both their preprocessed columns only (`sudPsim_pre`,
    `sudTs_pre`). -/
theorem sud_fs_open3 {V Wv P1 P2 P3 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    {S16 S10 SP : List F} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 : Nat} (hK2 : 0 < K2)
    (hS16 : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz16 : 2 * S16.length + 8 ≤ 2 ^ 16) (hsz : 2 * S10.length + 8 ≤ 2 ^ 10)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hncw : 4 ≤ ncw) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS1 NS2 NS3 n1 n2 n3 : Nat}
    (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : List (List (List F)) → Nat → P1) (hc1 : ComHides NS1 Com1)
    (hp1 : ComPfHides NS1 Com1 Pf1 (opF ((sudGroups tP S16 S10 SP EF.zero qv).map (·.base.S)) [0, 2, 4, 6]))
    (hr1 : ∀ d σ, Com1 d σ < n1) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ComPfHides NS2 Com2 Pf2 (opF ((sudGroups tP S16 S10 SP EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ComPfHides NS3 Com3 Pf3 (fun d => (opQ (sudSsT S16 S10 SP) d.1, opCw (sudSsC tP S16 S10 SP) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF → Bool) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw αb
      (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw αb
      (friX fri Rb Ro (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP S16 S10 SP EF.zero qv
    let Ss0 := q0.map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT0 := (tqZ 0 EF.zero).map (·.S)
    let SsC0 := (tabsInfo ncw (tqZ 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ c2 EF.zero) (qdZ c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ c2 EF.zero) (ccF q0 ks (tqZ c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let qZ := fun (ζ : EF) => sudGroups tP S16 S10 SP ζ qv
    let sop1 := fun (c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF Ss0 mk1 (mainZ2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF Ss0 mk2 (mainZ2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ SsT0 (tabsPolys (tqZ c2 (efOf c3)) (canonT (tqZ c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ (efOf c3)).map QGroup.ext) ((((qZ (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F)))) (msF (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw (r % NR0))),
       opCw SsC0 (tabsCws ncw (tqZ c2 (efOf c3)) (ccF (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss0 mk1 pv)
      | none => none
    let ov2 : TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss0 mk2 pv)
      | none => none
    let ov3 : TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) := fun v =>
      match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) => realVN off tabs tv tp (pcsZ c2 (efOf c3)) α β r t
    let svF := fun (c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c2 (efOf c3)) α β r t
    let op3 := fun (d : List (List (List (List F))) × List (List (List F))) => (opQ SsT0 d.1, opCw SsC0 d.2)
    let sd3 := fun (o : List (List (List (List F))) × List (List (List F))) => (sdQ SsT0 o.1, sdCw SsC0 o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rvF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair ov2 ov3 (rvF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 Pf2 Pf3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 ((sdF Ss0 mk1) (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * Com2 ((sdF Ss0 mk2) (sop2 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        ((sdF Ss0 mk2) (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 ((sdF Ss0 mk1) (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 Pf2 Pf3 ((sdF Ss0 mk2) (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 c3 : Nat) => genB (efOf (c1 % Q4)) && genB (efOf c3)
    (Q4 * Q4) * (K2 * (Q4 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
          (rget Q4 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) &&
        E H1 H2 H3 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
            (rget Q4 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
        indB (gd c1 c2 c3 && E (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset Q4 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (svo c1 c2 c3 x))))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
        (K2 * (Q4 * (NS1 * (NS2 * NS3 * ((Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))))))) := by
  intro blank C Pg Wt Mm NR0 pcsZ psimZ NR tabs tv tp M q0 Ss0 ks cols tqZ qdZ SsT0 SsC0 mk1 mk2 main1 main2 main3 vS qZ sop1 sop2 sop3 ov1 ov2 ov3 rvF svF op3 sd3
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sms, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨hP23, hPg⟩ := sud_prog_height hc hA hlen
  rw [← htp] at hP23 hPg
  have hSw := fun (c2 c3 : Nat) => sud_same_w off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hSz := fun (c2 c3 : Nat) => sud_same_w off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm c2) (wc c2) (ww c2) (wp c2) ncw rfl rfl rfl rfl
  have hS0 := fun (c2 : Nat) => sud_same_w off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP EF.zero EF.zero qv (wm c2) (wc c2) (ww c2) (wp c2) (wm 0) (wc 0) (ww 0) (wp 0) ncw (by rw [hlwm, hlwm]) (by rw [hlwc, hlwc]) (by rw [hlww, hlww]) (by rw [hlwp, hlwp])
  have hb : ∀ c2 c3, genB (efOf c3) = true →
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (SudPV (V × Wv)) EF → Bool,
        tsumN NR 2 (fun α β r t => indB (genB β && E' (svF c2 c3 α β r t))) ≤
          tsumN NR 2 (fun α β r t => indB (genB β && E' (rvF c2 c3 α β r t))) + Q4 * (NR * (Q4 ^ 2 * M)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c2 c3 hg => by
    have hgz := (genB_iff _).1 hg
    have hpcs := sud_pcsX (heap := blank.heap) (ζ := efOf c3) off sc sms sw (rfl : C.h = 2 ^ 16) hlen
      (rfl : Wt.h = 2 ^ 10) (by omega) hPg qv (wm c2) (wc c2) (ww c2) (wp c2) hS16 hS10 hSP hsz16 hsz hszP (generic_ofF_ne hgz)
      (mz_generic hgz) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
    have hNR : sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2) ncw = sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw := by
      unfold sudNR; rw [(hSw c2 c3).n1, (hSw c2 c3).n2]
    rw [hNR] at hpcs
    exact ⟨fun E' => (sud_transcriptG off NR 0 (pcsZ c2 (efOf c3)) (psimZ c2 (efOf c3)) hbal hun hpcs E').1,
      fun E' => (sud_transcriptG off NR 0 (pcsZ c2 (efOf c3)) (psimZ c2 (efOf c3)) hbal hun hpcs E').2⟩
  have hlen8 : ∀ (ζ : EF) t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length :=
    fun ζ t α β => by
      rw [(sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg
          S16 S10 SP ζ qv t α β).2,
        (sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg
          S16 S10 SP ζ qv t EF.zero EF.zero).2]
  have hmk1 : ∀ k ∈ mk1, k < 8 ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk1, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 8 := by rcases hk' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, sudCols_main off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2 : ∀ k ∈ mk2, k < 8 ∧ ∀ t α β, k < (cols t α β).length := by
    intro k hk
    simp only [mk2, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hkn : k < 8 := by rcases hk with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun _ _ _ => hkn⟩
  have hvo1 : ∀ c2 c3 c r t, rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF Ss0 mk1 (main1 t r)) := by
    intro c2 c3 c r t
    show realVN off tabs tv tp (pcsZ c2 (efOf c3)) _ _ r t = none ∨
      ov1 (realVN off tabs tv tp (pcsZ c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ov2 off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP S16 S10 SP (efOf c3) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw αb
        (friX fri Rb Ro (r / NR0)) mk1 hmk1 (hlen8 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSw c2 c3).dataF2 cols mk1 t (r % NR0), (hSw c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo2 : ∀ c2 c3 c r t, rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF Ss0 mk2 (main2 c t r)) := by
    intro c2 c3 c r t
    show realVN off tabs tv tp (pcsZ c2 (efOf c3)) _ _ r t = none ∨
      ov2 (realVN off tabs tv tp (pcsZ c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have e := pcsFri_ovP off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP S16 S10 SP (efOf c3) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw αb
        (friX fri Rb Ro (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      rw [(hSw c2 c3).dataP2 cols mk2 t _ _ (r % NR0), (hSw c2 c3).S] at e
      exact .inr (congrArg some e)
  have hvo3 : ∀ c2 c3 c r t, rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 (rvF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 (main3 c c2 t r)) := by
    intro c2 c3 c r t
    show realVN off tabs tv tp (pcsZ c2 (efOf c3)) _ _ r t = none ∨
      ov3 (realVN off tabs tv tp (pcsZ c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab' : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (off (efOf (c % Q4)))) (efOf (c % Q4)) (tabs t)
        · rfl
        · exact absurd h hab
      have e0 := pcsFri_ovR2 off (fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t) (sudGroups tP S16 S10 SP (efOf c3) qv) ks cols ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) (fun t α β ms => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map fun p => p.2 t α β ms) ncw αb
        (friX fri Rb Ro (r / NR0)) mk2 hmk2 rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0)
      have e := congrArg Prod.snd e0
      rw [(hSz c2 c3).tS, (hSz c2 c3).iS, tabsPolys_congr _ _ _ _ (hSz c2 c3).shape,
        tabsCws_congr ncw _ _ _ (hSz c2 c3).shape, (hSz c2 c3).cr (r % NR0), (hSz c2 c3).cc (r % NR0),
        (hSz c2 c3).ms (r % NR0), (hS0 c2).tS, (hS0 c2).iS,
        sud_data_zeta off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) EF.zero
          qv (wm c2) (wc c2) (ww c2) (wp c2) t _ _ _ hab'] at e
      exact .inr (congrArg some e)
  have hsvo1 : ∀ c2 c3 c r t, ov1 (svF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 c3 r t) :=
    fun c2 c3 c r t => congrArg some (psimFri_ov2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw αb _ mk1
      (fun k hk => (hmk1 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo2 : ∀ c2 c3 c r t, ov2 (svF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c3 c r t) :=
    fun c2 c3 c r t => congrArg some (psimFri_ov2 (qZ (efOf c3)) ks (tqZ c2 (efOf c3)) ncw αb _ mk2
      (fun k hk => (hmk2 k hk).1) rfl _ _ _ (r % NR0))
  have hsvo3 : ∀ c2 c3 c r t, ov3 (svF c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c2 c3 c r t) := by
    intro c2 c3 c r t
    have e0 := psimFri_ovR2 (sudGroups tP S16 S10 SP (efOf c3) qv) ks ((sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP (efOf c3) qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst) ncw αb (friX fri Rb Ro (r / NR0)) mk2
      (fun k hk => (hmk2 k hk).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vS (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0)
    have e := congrArg Prod.snd e0
    rw [(hSw c2 c3).tS, (hSw c2 c3).iS] at e
    exact congrArg some e
  have hsd1 : ∀ t r, opF Ss0 mk1 (sdF Ss0 mk1 (opF Ss0 mk1 (main1 t r))) = opF Ss0 mk1 (main1 t r) :=
    fun t r => opF_sdF _ _ _
  have hsd2 : ∀ c t r, opF Ss0 mk2 (sdF Ss0 mk2 (opF Ss0 mk2 (main2 c t r))) = opF Ss0 mk2 (main2 c t r) :=
    fun c t r => opF_sdF _ _ _
  have hsd3 : ∀ c c' t r, op3 (sd3 (op3 (main3 c c' t r))) = op3 (main3 c c' t r) := fun c c' t r =>
    congrArg Prod.snd (op2_sd2 Ss0 [] SsT0 SsC0 (fun _ => []) (main3 c c' t r).1 (main3 c c' t r).2)
  have hp3' : ComPfHides NS3 Com3 Pf3 op3 := by
    have e1 : SsT0 = sudSsT S16 S10 SP := sud_SsT off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0)
    have e2 : SsC0 = sudSsC tP S16 S10 SP := sud_SsC off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    show ComPfHides NS3 Com3 Pf3 (fun d => (opQ SsT0 d.1, opCw SsC0 d.2))
    rw [e1, e2]; exact hp3
  exact fs_open3 hK2 Q4_pos rvF svF (fun c2 c3 => genB (efOf c3))
    (fun c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    (fun c2 c3 hg => (hb c2 c3 hg).1) (fun c2 c3 hg => (hb c2 c3 hg).2)
    Com1 Pf1 (opF Ss0 mk1) (sdF Ss0 mk1) d1 hc1 hp1 hr1 ov1 rfl main1 hsd1
    Com2 Pf2 (opF Ss0 mk2) (sdF Ss0 mk2) d2 hc2 hp2 hr2 ov2 rfl main2 hsd2
    Com3 Pf3 op3 sd3 d3 hc3 hp3' hr3 ov3 rfl main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E
end

end Circuit
