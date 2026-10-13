import Ski.ZK.ROMHide

/-!
# Two Fiat–Shamir rounds, the first commitment drawn from the oracle

`Ski/ZK/ROMHide.lean` draws one round's commitment from the random oracle
(`comR`, `pfR`) and bounds the distance from the real opening to an ideal
one that hides exactly (`transferR`).  Here the transfer runs inside the
other draws' count (`transferR_in`) and composes with `fs_open2`: `K` times
the real two-round count, the first commitment the answer of its own
table, is within the transfer's error of the count with the ideal opening,
which meets `fs_open2`'s exact hiding (`fs_open2ROM`).  The second
commitment stays a primitive, and the commitment's table is apart from the
Fiat–Shamir tables, as a domain-separated oracle's.
-/

namespace Circuit
open ZKF

/-- **`transferR` inside a count**: over any count `so` of the other draws,
    the data `dat y` and the event `G y` read off them. -/
theorem transferR_in {Y D O P : Type} {K n NSh NSo s k : Nat} (hK : 0 < K) (so : (Y → Nat) → Nat) (hso : Lin so)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (op : D → O) (g : O → Nat → P)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxt : P → Nat → List Nat → Nat) (dat : Y → D) (G : Y → Nat → P × List Nat → Bool) :
    K * so (fun y => sumTo (NSh * (NSo * K ^ n)) (fun σ =>
      indB (G y (comR K NSh NSo pos (dat y) σ) (pfR K NSh NSo k pos op g nxt (dat y) σ)))) ≤
      so (fun y => sumTo (NSh * (NSo * K ^ n) * K) (fun σ =>
        indB (G y (comI K NSh NSo pos (dat y) σ) (pfI K NSh NSo k pos op g nxt (dat y) σ)))) +
        K * (NSo * (K ^ n * (s * k))) * so (fun _ => 1) ∧
    so (fun y => sumTo (NSh * (NSo * K ^ n) * K) (fun σ =>
        indB (G y (comI K NSh NSo pos (dat y) σ) (pfI K NSh NSo k pos op g nxt (dat y) σ)))) ≤
      K * so (fun y => sumTo (NSh * (NSo * K ^ n)) (fun σ =>
        indB (G y (comR K NSh NSo pos (dat y) σ) (pfR K NSh NSo k pos op g nxt (dat y) σ)))) +
        K * (NSo * (K ^ n * (s * k))) * so (fun _ => 1) := by
  have t := fun y => transferR (NSh := NSh) (NSo := NSo) (k := k) hK pos hpos op g hs nxt (G y) (dat y)
  have eE := smC so hso (K * (NSo * (K ^ n * (s * k))))
  constructor
  · rw [← smK so hso, ← eE, ← sm_add so hso]
    exact sm_mono so hso (fun y => (t y).1)
  · rw [← smK so hso, ← eE, ← sm_add so hso]
    exact sm_mono so hso (fun y => (t y).2)

/-- The count over a second salt and the tuples. -/
def smT (NS NR m : Nat) (f : Nat × Nat × (Nat → Tup) → Nat) : Nat :=
  sumTo NS (fun σ2 => sumTo NR (fun r => sumN m (fun t => f (σ2, r, t))))

theorem smT_lin (NS NR m : Nat) : Lin (smT NS NR m) := fun N f =>
  sm_exch (NS := NS) (NR := NR) (m := m) (N := N) (fun i σ2 r t => f i (σ2, r, t))

theorem smT_one (NS NR m : Nat) : smT NS NR m (fun _ => 1) = NS * (NR * (Q4 ^ m * 1)) := by
  show sumTo NS (fun _ => sumTo NR (fun _ => sumN m (fun _ => 1))) = _
  rw [sumN_const, sumTo_const, sumTo_const]

/-- **Two Fiat–Shamir rounds, the first commitment drawn from the oracle**:
    `fs_open2` with `Com1` the answer of its own table (`comR`) and its
    opening `pfR`, the distinguisher's `k` queries into that table.  `K`
    times the real count is at most the count with the ideal opening
    (`transferR_in`) plus the transfer's `K NSo K^n s k` a draw of the other
    salts and tuples; the ideal opening hides exactly (`comI_hides`,
    `pfI_hides`) and so meets `fs_open2`, and the simulator commits through
    it.  Normalized, the real probability is at most the simulator's plus
    `(e1 + e2) / (Q4² NR Q4^m) + s k / NSh` a draw.  One direction, as
    `fs_open2`'s.  `ROMHide`'s limits hold: the queries read only the first
    opening and its commitment, no query answers where the prover aborts,
    `Com2` a primitive, the commitment's table apart from the Fiat–Shamir
    tables, one hash and no Merkle path. -/
theorem fs_open2ROM {PV PB D O P D2 O2 P2 : Type} {NR m e1 e2 NSh NSo s k n NS2 K2 n2 : Nat}
    (hK : 0 < K) (hK2 : 0 < K2)
    (rv sv : Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Bool)
    (hrv : ∀ c2 α β r t, rv c2 α β r t = none ∨ ∃ p x y, rv c2 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 α β r t, ∃ p x y, sv c2 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) + e1 + e2)
    (h2 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) + e1 + e2)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (g : O → Nat → P)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxt : P → Nat → List Nat → Nat) (op1 : D → O) (sd1 : O → D) (d1 : D)
    (ov1 : TViewN PV PB → Option O) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ComPfHides NS2 Com2 Pf2 op2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : TViewN PV PB → Option O2) (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (hvo1 : ∀ c2 c r t, rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 (main1 t r)))
    (hvo2 : ∀ c2 c r t, rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r)))
    (sop1 : Nat → Nat → (Nat → Tup) → O) (sop2 : Nat → Nat → Nat → (Nat → Tup) → O2)
    (hsvo1 : ∀ c2 c r t, ov1 (sv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 r t))
    (hsvo2 : ∀ c2 c r t, ov2 (sv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c r t))
    (E : Nat → Nat → Nat → Nat → Option (P × List Nat) × Option P2 × TViewN PV PB → Bool) :
    let Com1 := comR K NSh NSo pos
    let Pf1 := pfR K NSh NSo k pos op1 g nxt
    let Cmi := comI K NSh NSo pos
    let Pfi := pfI K NSh NSo k pos op1 g nxt
    let smR := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * K ^ n)) (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t => f (σ1, σ2, r, t)))))
    let smI := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * K ^ n) * K) (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ2, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      Com1 (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
       (ov2 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => Pf2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (_c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 x + K * Com2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1), some (Pf2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1),
        sv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 : Nat) => genB (efOf (c1 % Q4)) && gz c2
    K * ((Q4 * Q4) * (K2 * sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => smR (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x))))))) ≤
    sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 =>
      smI (fun x => indB (gd c1 c2 && E (rset (Q4 * Q4) (s1 c1 c2 x) H1 c1) (rset K2 (s2 c1 c2 x) H2 c2)
        (s1 c1 c2 x) (s2 c1 c2 x) (svo c1 c2 x))))))) +
      (Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K2 * (NSh * (NSo * K ^ n) * K * (NS2 * (e1 + e2))))) +
      (Q4 * Q4) * (K2 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) *
        (K * (NSo * (K ^ n * (s * k))) * (NS2 * (NR * (Q4 ^ m * 1))))))) := by
  intro Com1 Pf1 Cmi Pfi smR smI m1 m2 rvo s1 s2 svo gd
  have fo := fs_open2 (NS1 := NSh * (NSo * K ^ n) * K) (n1 := K) hK2 rv sv gz hrv hsv h1 h2 Cmi Pfi op1 sd1 d1
    (comI_hides hK pos hpos) (pfI_hides hK pos hpos op1 g nxt) (fun _ _ => Nat.mod_lt _ hK) ov1 hov1 main1 hsd1
    Com2 Pf2 op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 hvo1 hvo2 sop1 sop2 hsvo1 hsvo2 E
  -- the other draws' count, and the transfer at each pair of tables
  have hso := smT_lin NS2 NR m
  have so1 := smT_one NS2 NR m
  have step : ∀ H1 H2, K * smR (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x))) ≤
      smI (fun x =>
      indB (gd (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1)
          (rget K2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1)
            x.2.2.2 x.2.2.1) x.2.1) H2) &&
        E H1 H2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)
          (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1)
            x.2.2.2 x.2.2.1) x.2.1)
          ((ov1 (rv (rget K2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4)
              (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1) x.2.2.2 x.2.2.1) x.2.1) H2)
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 / Q4))
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 % Q4)) x.2.2.1 x.2.2.2)).map
              (fun _ => Pfi (main1 x.2.2.2 x.2.2.1) x.1),
           (ov2 (rv (rget K2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4)
              (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1) x.2.2.2 x.2.2.1) x.2.1) H2)
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 / Q4))
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 % Q4)) x.2.2.1 x.2.2.2)).map
              (fun _ => Pf2 (main2 (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1) x.2.2.2 x.2.2.1) x.2.1),
           rv (rget K2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1 + K * Com2 (main2 (rget (Q4 * Q4)
              (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1) x.2.2.2 x.2.2.1) x.2.1) H2)
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 / Q4))
              (efOf (rget (Q4 * Q4) (Cmi (main1 x.2.2.2 x.2.2.1) x.1) H1 % Q4)) x.2.2.1 x.2.2.2))) +
        K * (NSo * (K ^ n * (s * k))) * (NS2 * (NR * (Q4 ^ m * 1))) := fun H1 H2 => by
    have tr := (transferR_in (n := n) (NSh := NSh) (NSo := NSo) (s := s) (k := k) hK (smT NS2 NR m) hso pos hpos op1 g hs nxt (fun y => main1 y.2.2 y.2.1)
      (fun y c pf => gd (rget (Q4 * Q4) c H1)
          (rget K2 (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1) H2) &&
        E H1 H2 c (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1)
          ((ov1 (rv (rget K2 (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1) H2)
              (efOf (rget (Q4 * Q4) c H1 / Q4)) (efOf (rget (Q4 * Q4) c H1 % Q4)) y.2.1 y.2.2)).map (fun _ => pf),
           (ov2 (rv (rget K2 (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1) H2)
              (efOf (rget (Q4 * Q4) c H1 / Q4)) (efOf (rget (Q4 * Q4) c H1 % Q4)) y.2.1 y.2.2)).map
              (fun _ => Pf2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1),
           rv (rget K2 (c + K * Com2 (main2 (rget (Q4 * Q4) c H1) y.2.2 y.2.1) y.1) H2)
              (efOf (rget (Q4 * Q4) c H1 / Q4)) (efOf (rget (Q4 * Q4) c H1 % Q4)) y.2.1 y.2.2))).1
    rw [hso, hso, so1] at tr
    exact tr
  have hb : K * ((Q4 * Q4) * (K2 * sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => smR (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x))))))) =
      (Q4 * Q4) * (K2 * sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => K * smR (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)))))) := by
    rw [Nat.mul_left_comm K (Q4 * Q4), Nat.mul_left_comm K K2, sumTo_mul]
    exact congrArg (fun z => Q4 * Q4 * (K2 * z)) (sumTo_congr _ (fun H1 _ => sumTo_mul _ _ _))
  rw [hb]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ => step H1 H2))))) ?_
  simp only [sumTo_add, sumTo_const]
  rw [Nat.mul_add K2, Nat.mul_add (Q4 * Q4)]
  exact Nat.add_le_add_right fo _
end Circuit

