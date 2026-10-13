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
    count is within `(Q4²)^n1 K2^(n1 n2) K3^(n1 n2 n3) K2 K3 NS1 NS2 NS3
    (e1 + e2)` of the simulator's. -/
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

end Circuit
