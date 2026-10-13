import Ski.ZK.ROMInst

/-!
# Several four-round proofs, each first commitment drawn from the oracle

`fs_open4_two` composes two four-round proofs under shared Fiat–Shamir
tables, each first commitment a primitive that hides and whose values
spread (`hsp`).  Here each is the answer of its own table (`comR`), its
opening `pfR` at the drawn query challenge.  `rom4_step` moves one proof's
real view to its ideal one for any event at fixed tables; `pair_transfer`
does so for both inside the pair's count, the second proof's count brought
inside; the ideal commitment spreads (`comI_spread_sm`, from the tables'
answers spreading: `rget_spread`, `comR_spread`), and `fs_open4_two` holds
at the ideal openings (`fs_open4_twoROM`).  Each transfer adds `s k / NSh`
a draw; one direction; the two proofs' commitment tables apart from each
other and from the Fiat–Shamir tables, the commitments' range `KQ` shared.
For `n` copies, `pow_transfer` moves every copy's view, newest first, and
`zkb_rom` carries `fs_open4_pow`'s bound at the ideal opening to the real
one (`fs_open4_powROM`).
-/

namespace Circuit
open ZKF
theorem sumTo_indEq (v : Nat) : ∀ N, sumTo N (fun c => indB (decide (c = v))) ≤ 1 ∧
    (N ≤ v → sumTo N (fun c => indB (decide (c = v))) = 0)
  | 0 => ⟨Nat.zero_le _, fun _ => rfl⟩
  | N + 1 => by
    obtain ⟨h1, h0⟩ := sumTo_indEq v N
    show sumTo N (fun c => indB (decide (c = v))) + indB (decide (N = v)) ≤ 1 ∧
      (N + 1 ≤ v → sumTo N (fun c => indB (decide (c = v))) + indB (decide (N = v)) = 0)
    by_cases hN : N = v
    · subst hN
      rw [h0 (Nat.le_refl _)]
      simp [indB]
    · have e : indB (decide (N = v)) = 0 := by simp [indB, hN]
      rw [e, Nat.add_zero]
      exact ⟨h1, fun h => h0 (Nat.le_of_succ_le h)⟩

/-- **A table's answer is spread**: at a position below `n`, each value is
    the answer of at most `K^n / K` of the tables. -/
theorem rget_spread {K n p v : Nat} (hK : 0 < K) (hp : p < n) :
    K * sumTo (K ^ n) (fun H => indB (decide (rget K p H = v))) ≤ K ^ n := by
  rw [← oracle_reprog_get hK hp (fun _ c => indB (decide (c = v)))]
  calc sumTo (K ^ n) (fun H => sumTo K (fun c => indB (decide (c = v))))
      ≤ sumTo (K ^ n) (fun _ => 1) := sumTo_mono _ (fun H _ => (sumTo_indEq v K).1)
    _ = K ^ n := by rw [sumTo_const, Nat.mul_one]

/-- **The oracle's commitment is spread**: `K` times the salts at which it
    takes any one value number at most `NSh NSo K^n`. -/
theorem comR_spread {D : Type} {K n NSh NSo : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hpos : ∀ d σo σh, pos d σo σh < n) (d : D) (v : Nat) :
    K * sumTo (NSh * (NSo * K ^ n)) (fun σ => indB (decide (comR K NSh NSo pos d σ = v))) ≤ NSh * (NSo * K ^ n) := by
  rw [sum_salt_eq, sumTo_mul]
  have per : ∀ o, o < NSo → K * sumTo NSh (fun σh => sumTo (K ^ n) (fun h =>
      indB (decide (comR K NSh NSo pos d (σh + NSh * (o + NSo * h)) = v)))) ≤ NSh * K ^ n := fun o ho => by
    rw [sumTo_mul, ← sumTo_const (K ^ n) NSh]
    refine sumTo_mono _ (fun σh hh => ?_)
    have e : sumTo (K ^ n) (fun h => indB (decide (comR K NSh NSo pos d (σh + NSh * (o + NSo * h)) = v))) =
        sumTo (K ^ n) (fun h => indB (decide (rget K (pos d o σh) h = v))) :=
      sumTo_congr _ (fun h _ => by
        obtain ⟨a, b, c⟩ := salt_dec (h := h) hh ho
        simp only [comR, a, b, c])
    rw [e]
    exact rget_spread hK (hpos d o σh)
  calc sumTo NSo (fun o => K * sumTo NSh (fun σh => sumTo (K ^ n) (fun h =>
        indB (decide (comR K NSh NSo pos d (σh + NSh * (o + NSo * h)) = v)))))
      ≤ sumTo NSo (fun _ => NSh * K ^ n) := sumTo_mono _ per
    _ = NSh * (NSo * K ^ n) := by rw [sumTo_const, Nat.mul_left_comm]
/-- **The ideal commitment is spread**: over its salts, each value at most
    `NSh NSo K^n` times. -/
theorem comI_spread {D : Type} {K n NSh NSo : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hpos : ∀ d σo σh, pos d σo σh < n) (d : D) (v : Nat) :
    sumTo (NSh * (NSo * K ^ n) * K) (fun σ => indB (decide (comI K NSh NSo pos d σ = v))) ≤ NSh * (NSo * K ^ n) := by
  rw [sum_digit]
  have e : ∀ σ, sumTo K (fun u => indB (decide (comI K NSh NSo pos d (u + K * σ) = v))) =
      K * indB (decide (comR K NSh NSo pos d σ = v)) := fun σ => by
    rw [sumTo_congr _ (fun u hu => by rw [comI_digit pos d hu]), sumTo_const]
  rw [sumTo_congr _ (fun σ _ => e σ), ← sumTo_mul]
  exact comR_spread hK pos hpos d v

/-- **The ideal commitment's spread over the whole count** (`fs_open4_two`'s
    `hsp`): each value at most `NSh NSo K^n` times a draw of the others. -/
theorem comI_spread_sm {D : Type} {K n NSh NSo NS NR m : Nat} (hK : 0 < K) (pos : D → Nat → Nat → Nat)
    (hpos : ∀ d σo σh, pos d σo σh < n) (main : (Nat → Tup) → Nat → D) (v : Nat) :
    sumTo (NSh * (NSo * K ^ n) * K) (fun σ1 => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (decide (comI K NSh NSo pos (main t r) σ1 = v)))))) ≤
      NSh * (NSo * K ^ n) * (NS * (NR * (Q4 ^ m * 1))) := by
  have hso := smT_lin NS NR m
  have e := hso (NSh * (NSo * K ^ n) * K) (fun σ1 y => indB (decide (comI K NSh NSo pos (main y.2.2 y.2.1) σ1 = v)))
  show sumTo (NSh * (NSo * K ^ n) * K) (fun σ1 => smT NS NR m (fun y =>
    indB (decide (comI K NSh NSo pos (main y.2.2 y.2.1) σ1 = v)))) ≤ _
  rw [← e, ← smT_one NS NR m, ← smC _ hso]
  exact sm_mono _ hso (fun y => comI_spread hK pos hpos (main y.2.2 y.2.1) v)
/-- **Two transfers inside a pair's count**: each proof's real view moved to
    its ideal one at every table and every draw of the other, the second's
    count brought inside by `Comm`. -/
theorem pair_transfer {T XA XB VA VB : Type} {KA KB eA eB : Nat} (ST : (T → Nat) → Nat) (hST : Lin ST)
    (smAR smAI : (XA → Nat) → Nat) (hAI : Lin smAI)
    (smBR smBI : (XB → Nat) → Nat) (hBR : Lin smBR)
    (hC : Comm smAI smBR) (hC' : Comm smAI smBI)
    (vAR vAI : T → XA → VA) (vBR vBI : T → XB → VB)
    (hA : ∀ H (G : VA → Bool), KA * smAR (fun xa => indB (G (vAR H xa))) ≤ smAI (fun xa => indB (G (vAI H xa))) + eA)
    (hB : ∀ H (G : VB → Bool), KB * smBR (fun xb => indB (G (vBR H xb))) ≤ smBI (fun xb => indB (G (vBI H xb))) + eB)
    (E : T → VA → VB → Bool) :
    KA * (KB * ST (fun H => smBR (fun xb => smAR (fun xa => indB (E H (vAR H xa) (vBR H xb)))))) ≤
      ST (fun H => smBI (fun xb => smAI (fun xa => indB (E H (vAI H xa) (vBI H xb))))) +
        KB * (eA * ST (fun _ => smBR (fun _ => 1))) + eB * ST (fun _ => smAI (fun _ => 1)) := by
  -- the first proof's transfer, inside
  have s1 : KA * ST (fun H => smBR (fun xb => smAR (fun xa => indB (E H (vAR H xa) (vBR H xb))))) ≤
      ST (fun H => smBR (fun xb => smAI (fun xa => indB (E H (vAI H xa) (vBR H xb))))) +
        eA * ST (fun _ => smBR (fun _ => 1)) := by
    rw [← smK ST hST, ← smK ST hST, ← sm_add ST hST]
    refine sm_mono ST hST (fun H => ?_)
    rw [← smK smBR hBR, ← smC smBR hBR, ← sm_add smBR hBR]
    exact sm_mono smBR hBR (fun xb => hA H (fun v => E H v (vBR H xb)))
  -- the second's, its count brought inside
  have s2 : KB * ST (fun H => smBR (fun xb => smAI (fun xa => indB (E H (vAI H xa) (vBR H xb))))) ≤
      ST (fun H => smBI (fun xb => smAI (fun xa => indB (E H (vAI H xa) (vBI H xb))))) +
        eB * ST (fun _ => smAI (fun _ => 1)) := by
    rw [← smK ST hST, ← smK ST hST, ← sm_add ST hST]
    refine sm_mono ST hST (fun H => ?_)
    rw [hC (fun xa xb => indB (E H (vAI H xa) (vBR H xb))), hC' (fun xa xb => indB (E H (vAI H xa) (vBI H xb))),
      ← smK smAI hAI, ← smC smAI hAI, ← sm_add smAI hAI]
    exact sm_mono smAI hAI (fun xa => hB H (fun v => E H (vAI H xa) v))
  calc KA * (KB * ST (fun H => smBR (fun xb => smAR (fun xa => indB (E H (vAR H xa) (vBR H xb))))))
      = KB * (KA * ST (fun H => smBR (fun xb => smAR (fun xa => indB (E H (vAR H xa) (vBR H xb)))))) :=
        Nat.mul_left_comm _ _ _
    _ ≤ KB * (ST (fun H => smBR (fun xb => smAI (fun xa => indB (E H (vAI H xa) (vBR H xb))))) +
        eA * ST (fun _ => smBR (fun _ => 1))) := Nat.mul_le_mul_left _ s1
    _ = KB * ST (fun H => smBR (fun xb => smAI (fun xa => indB (E H (vAI H xa) (vBR H xb))))) +
        KB * (eA * ST (fun _ => smBR (fun _ => 1))) := Nat.mul_add _ _ _
    _ ≤ _ := by
      refine Nat.le_trans (Nat.add_le_add_right s2 _) (Nat.le_of_eq ?_)
      ac_rfl

/-- One four-round proof's view at the tables `H` (`fs_open4_abs`'s `rvT`,
    at `n1 = K`): its three messages and its output. -/
def view4 {PV PB D O1 P1 D2 O2 P2 D3 O3 P3 W : Type} (K NS2 K2 K3 K4 n2 : Nat)
    (φ : Nat → W → Nat) (rv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (oz : TViewN PV PB → W) (ov1 : Nat → TViewN PV PB → Option O1) (main1 : (Nat → Tup) → Nat → D)
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (ov2 : Nat → TViewN PV PB → Option O2)
    (main2 : Nat → (Nat → Tup) → Nat → D2)
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → D3 → Nat → P3) (ov3 : Nat → TViewN PV PB → Option O3)
    (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (Com1 : D → Nat → Nat) (Pf1 : Nat → D → Nat → P1)
    (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) :
    Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN PV PB) :=
  let m1 := Com1 (main1 x.2.2.2 x.2.2.1) x.1
  let c1 := rget (Q4 * Q4) m1 H.1
  let m2 := m1 + K * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
  let c2 := rget K2 m2 H.2.1
  let m3 := m1 + K * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
  let c3 := rget K3 m3 H.2.2.1
  let c4 := rget K4 (φ m3 (oz (rv 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H.2.2.2
  (m1, m2, m3,
   ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
    (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
      (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
    rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))

/-- **The four-round transfer at fixed tables, for any event of the view**. -/
theorem rom4_step {PV PB D O Pq D2 O2 P2 D3 O3 P3 W : Type}
    {K NR m NSh NSo s k n NS2 NS3 K2 K3 K4 n2 : Nat} (hK : 0 < K)
    (φ : Nat → W → Nat) (rv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (oz : TViewN PV PB → W)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (g : O → Nat → Pq)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxt : Pq → Nat → List Nat → Nat) (op1 : Nat → D → O)
    (ov1 : Nat → TViewN PV PB → Option O) (main1 : (Nat → Tup) → Nat → D)
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (ov2 : Nat → TViewN PV PB → Option O2)
    (main2 : Nat → (Nat → Tup) → Nat → D2)
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → D3 → Nat → P3) (ov3 : Nat → TViewN PV PB → Option O3)
    (main3 : Nat → Nat → (Nat → Tup) → Nat → D3) (H : Nat × Nat × Nat × Nat)
    (G : Nat × Nat × Nat × (Option (Pq × List Nat) × Option (P2 × P3) × TViewN PV PB) → Bool) :
    K * sumTo (NSh * (NSo * K ^ n)) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (G (view4 K NS2 K2 K3 K4 n2 φ rv oz ov1 main1 Com2 Pf2 ov2 main2 Com3 Pf3 ov3 main3
        (comR K NSh NSo pos) (fun c4 => pfR K NSh NSo k pos (op1 c4) g nxt) H (σ1, σ, r, t))))))) ≤
    sumTo (NSh * (NSo * K ^ n) * K) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (G (view4 K NS2 K2 K3 K4 n2 φ rv oz ov1 main1 Com2 Pf2 ov2 main2 Com3 Pf3 ov3 main3
        (comI K NSh NSo pos) (fun c4 => pfI K NSh NSo k pos (op1 c4) g nxt) H (σ1, σ, r, t))))))) +
      K * (NSo * (K ^ n * (s * k))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))) := by
  let c4f := fun (y : Nat × Nat × (Nat → Tup)) (c : Nat) =>
    let c1 := rget (Q4 * Q4) c H.1
    let c2 := rget K2 (c + K * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)) H.2.1
    let mm3 := c + K * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H.2.2.1
    rget K4 (φ mm3 (oz (rv 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2))) H.2.2.2
  let ev := fun (y : Nat × Nat × (Nat → Tup)) (c : Nat) (pf : Pq × List Nat) =>
    let c1 := rget (Q4 * Q4) c H.1
    let mm2 := c + K * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)
    let c2 := rget K2 mm2 H.2.1
    let mm3 := c + K * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H.2.2.1
    let c4 := c4f y c
    G (c, mm2, mm3,
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map (fun _ => pf),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2))
  have hso := smT_lin (NS2 * NS3) NR m
  have tr := transferRc_in (n := n) (NSh := NSh) (NSo := NSo) (s := s) (k := k) hK (smT (NS2 * NS3) NR m) hso
    pos hpos op1 g hs nxt (fun y => main1 y.2.2 y.2.1) c4f ev
  rw [hso, hso, smT_one] at tr
  exact tr

theorem two_comm4 {K c S : Nat} : K * (K * (c * (c * S))) = c * (c * (K * (K * S))) := by
  ac_rfl

theorem two_le4 {c a y b : Nat} (h : c * (c * a) ≤ b) : c * (c * (a + y)) ≤ b + c * (c * y) := by
  rw [Nat.mul_add, Nat.mul_add]; exact Nat.add_le_add_right h _

set_option maxRecDepth 100000 in
/-- **Two four-round proofs under shared tables, each first commitment drawn
    from its own oracle table** (`fs_open4_two` through `pair_transfer` and
    `rom4_step`): `KQ²` times the real count is at most `fs_open4_two`'s
    bound at the ideal openings, the second's spread `hsp` from
    `comI_spread_sm`, plus each transfer's `s k / NSh` a draw; one direction. -/
theorem fs_open4_twoROM {PVA PBA D1A O1A PqA D2A O2A P2A D3A O3A P3A WA : Type} {NRA mA e1A e2A NShA NSoA sA kA nA NS2A NS3A K2 K3 K4 KQ n2 n3 : Nat}
    (hKQ : 0 < KQ) (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φA : Nat → WA → Nat) {N4 : Nat} (hφA : ∀ mA w, φA mA w < N4)
    (rvA svA : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PVA PBA) (gzA : Nat → Nat → Bool)
    {BzA : Nat} (hgzA : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gzA c2 c3))) ≤ BzA)
    (g4A : Nat → Bool) {B4A : Nat} (hB4A : sumTo K4 (fun c4 => indB (!g4A c4)) ≤ B4A)
    (hrvA : ∀ c4 c2 c3 α β r t, rvA c4 c2 c3 α β r t = none ∨ ∃ p x y, rvA c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsvA : ∀ c4 c2 c3 α β r t, ∃ p x y, svA c4 c2 c3 α β r t = some (p, α, β, x, y))
    (ozA : TViewN PVA PBA → WA) (hozA : ∀ c4 c2 c3 α β r t, ozA (rvA c4 c2 c3 α β r t) = ozA (rvA 0 c2 c3 α β r t))
    (h1A : ∀ c4 c2 c3, g4A c4 = true → gzA c2 c3 = true → ∀ E : TViewN PVA PBA → Bool,
      tsumN NRA mA (fun α β r t => indB (genB β && E (rvA c4 c2 c3 α β r t))) ≤
        tsumN NRA mA (fun α β r t => indB (genB β && E (svA c4 c2 c3 α β r t))) + e1A + e2A)
    (h2A : ∀ c4 c2 c3, g4A c4 = true → gzA c2 c3 = true → ∀ E : TViewN PVA PBA → Bool,
      tsumN NRA mA (fun α β r t => indB (genB β && E (svA c4 c2 c3 α β r t))) ≤
        tsumN NRA mA (fun α β r t => indB (genB β && E (rvA c4 c2 c3 α β r t))) + e1A + e2A)
    (op1A : Nat → D1A → O1A) (sd1A : Nat → O1A → D1A) (d1A : D1A)
    (posA : D1A → Nat → Nat → Nat) (hposA : ∀ d σo σh, posA d σo σh < nA) (gA : O1A → Nat → PqA)
    (hsA : ∀ d σo v, sumTo NShA (fun σh => indB (decide (posA d σo σh = v))) ≤ sA)
    (nxtA : PqA → Nat → List Nat → Nat)
    (ov1A : Nat → TViewN PVA PBA → Option O1A) (hov1A : ∀ c4, ov1A c4 none = none) (main1A : (Nat → Tup) → Nat → D1A)
    (hsd1A : ∀ c4 t r, op1A c4 (sd1A c4 (op1A c4 (main1A t r))) = op1A c4 (main1A t r))
    (Com2A : D2A → Nat → Nat) (Pf2A : Nat → D2A → Nat → P2A) (op2A : Nat → D2A → O2A) (sd2A : Nat → O2A → D2A) (d2A : D2A)
    (hc2A : ComHides NS2A Com2A) (hp2A : ∀ c4, ComPfHides NS2A Com2A (Pf2A c4) (op2A c4)) (hr2A : ∀ d σ, Com2A d σ < n2)
    (ov2A : Nat → TViewN PVA PBA → Option O2A) (hov2A : ∀ c4, ov2A c4 none = none) (main2A : Nat → (Nat → Tup) → Nat → D2A)
    (hsd2A : ∀ c4 c t r, op2A c4 (sd2A c4 (op2A c4 (main2A c t r))) = op2A c4 (main2A c t r))
    (Com3A : D3A → Nat → Nat) (Pf3A : Nat → D3A → Nat → P3A) (op3A : Nat → D3A → O3A) (sd3A : Nat → O3A → D3A) (d3A : D3A)
    (hc3A : ComHides NS3A Com3A) (hp3A : ∀ c4, ComPfHides NS3A Com3A (Pf3A c4) (op3A c4)) (hr3A : ∀ d σ, Com3A d σ < n3)
    (ov3A : Nat → TViewN PVA PBA → Option O3A) (hov3A : ∀ c4, ov3A c4 none = none) (main3A : Nat → Nat → (Nat → Tup) → Nat → D3A)
    (hsd3A : ∀ c4 c c' t r, op3A c4 (sd3A c4 (op3A c4 (main3A c c' t r))) = op3A c4 (main3A c c' t r))
    (hvo1A : ∀ c4 c2 c3 c r t, rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1A c4 (rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1A c4 (main1A t r)))
    (hvo2A : ∀ c4 c2 c3 c r t, rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2A c4 (rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2A c4 (main2A c t r)))
    (hvo3A : ∀ c4 c2 c3 c r t, rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3A c4 (rvA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3A c4 (main3A c c2 t r)))
    (sop1A : Nat → Nat → Nat → Nat → (Nat → Tup) → O1A) (sop2A : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2A)
    (sop3A : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3A)
    (hsvo1A : ∀ c4 c2 c3 c r t, ov1A c4 (svA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1A c4 c2 c3 r t))
    (hsvo2A : ∀ c4 c2 c3 c r t, ov2A c4 (svA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2A c4 c2 c3 c r t))
    (hsvo3A : ∀ c4 c2 c3 c r t, ov3A c4 (svA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3A c4 c2 c3 c r t))
    {PVB PBB D1B O1B PqB D2B O2B P2B D3B O3B P3B WB : Type} {NRB mB e1B e2B NShB NSoB sB kB nB NS2B NS3B : Nat}
    (φB : Nat → WB → Nat) (hφB : ∀ mB w, φB mB w < N4)
    (rvB svB : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PVB PBB) (gzB : Nat → Nat → Bool)
    {BzB : Nat} (hgzB : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gzB c2 c3))) ≤ BzB)
    (g4B : Nat → Bool) {B4B : Nat} (hB4B : sumTo K4 (fun c4 => indB (!g4B c4)) ≤ B4B)
    (hrvB : ∀ c4 c2 c3 α β r t, rvB c4 c2 c3 α β r t = none ∨ ∃ p x y, rvB c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsvB : ∀ c4 c2 c3 α β r t, ∃ p x y, svB c4 c2 c3 α β r t = some (p, α, β, x, y))
    (ozB : TViewN PVB PBB → WB) (hozB : ∀ c4 c2 c3 α β r t, ozB (rvB c4 c2 c3 α β r t) = ozB (rvB 0 c2 c3 α β r t))
    (h1B : ∀ c4 c2 c3, g4B c4 = true → gzB c2 c3 = true → ∀ E : TViewN PVB PBB → Bool,
      tsumN NRB mB (fun α β r t => indB (genB β && E (rvB c4 c2 c3 α β r t))) ≤
        tsumN NRB mB (fun α β r t => indB (genB β && E (svB c4 c2 c3 α β r t))) + e1B + e2B)
    (h2B : ∀ c4 c2 c3, g4B c4 = true → gzB c2 c3 = true → ∀ E : TViewN PVB PBB → Bool,
      tsumN NRB mB (fun α β r t => indB (genB β && E (svB c4 c2 c3 α β r t))) ≤
        tsumN NRB mB (fun α β r t => indB (genB β && E (rvB c4 c2 c3 α β r t))) + e1B + e2B)
    (op1B : Nat → D1B → O1B) (sd1B : Nat → O1B → D1B) (d1B : D1B)
    (posB : D1B → Nat → Nat → Nat) (hposB : ∀ d σo σh, posB d σo σh < nB) (gB : O1B → Nat → PqB)
    (hsB : ∀ d σo v, sumTo NShB (fun σh => indB (decide (posB d σo σh = v))) ≤ sB)
    (nxtB : PqB → Nat → List Nat → Nat)
    (ov1B : Nat → TViewN PVB PBB → Option O1B) (hov1B : ∀ c4, ov1B c4 none = none) (main1B : (Nat → Tup) → Nat → D1B)
    (hsd1B : ∀ c4 t r, op1B c4 (sd1B c4 (op1B c4 (main1B t r))) = op1B c4 (main1B t r))
    (Com2B : D2B → Nat → Nat) (Pf2B : Nat → D2B → Nat → P2B) (op2B : Nat → D2B → O2B) (sd2B : Nat → O2B → D2B) (d2B : D2B)
    (hc2B : ComHides NS2B Com2B) (hp2B : ∀ c4, ComPfHides NS2B Com2B (Pf2B c4) (op2B c4)) (hr2B : ∀ d σ, Com2B d σ < n2)
    (ov2B : Nat → TViewN PVB PBB → Option O2B) (hov2B : ∀ c4, ov2B c4 none = none) (main2B : Nat → (Nat → Tup) → Nat → D2B)
    (hsd2B : ∀ c4 c t r, op2B c4 (sd2B c4 (op2B c4 (main2B c t r))) = op2B c4 (main2B c t r))
    (Com3B : D3B → Nat → Nat) (Pf3B : Nat → D3B → Nat → P3B) (op3B : Nat → D3B → O3B) (sd3B : Nat → O3B → D3B) (d3B : D3B)
    (hc3B : ComHides NS3B Com3B) (hp3B : ∀ c4, ComPfHides NS3B Com3B (Pf3B c4) (op3B c4)) (hr3B : ∀ d σ, Com3B d σ < n3)
    (ov3B : Nat → TViewN PVB PBB → Option O3B) (hov3B : ∀ c4, ov3B c4 none = none) (main3B : Nat → Nat → (Nat → Tup) → Nat → D3B)
    (hsd3B : ∀ c4 c c' t r, op3B c4 (sd3B c4 (op3B c4 (main3B c c' t r))) = op3B c4 (main3B c c' t r))
    (hvo1B : ∀ c4 c2 c3 c r t, rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1B c4 (rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1B c4 (main1B t r)))
    (hvo2B : ∀ c4 c2 c3 c r t, rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2B c4 (rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2B c4 (main2B c t r)))
    (hvo3B : ∀ c4 c2 c3 c r t, rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3B c4 (rvB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3B c4 (main3B c c2 t r)))
    (sop1B : Nat → Nat → Nat → Nat → (Nat → Tup) → O1B) (sop2B : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2B)
    (sop3B : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3B)
    (hsvo1B : ∀ c4 c2 c3 c r t, ov1B c4 (svB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1B c4 c2 c3 r t))
    (hsvo2B : ∀ c4 c2 c3 c r t, ov2B c4 (svB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2B c4 c2 c3 c r t))
    (hsvo3B : ∀ c4 c2 c3 c r t, ov3B c4 (svB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3B c4 c2 c3 c r t))
    (hφ : ∀ m w m' w', φB m w = φA m' w' → m % KQ = m' % KQ) :
    let Com1A := comR KQ NShA NSoA posA
    let Pf1A := fun (c4 : Nat) => pfR KQ NShA NSoA kA posA (op1A c4) gA nxtA
    let CmiA := comI KQ NShA NSoA posA
    let PfiA := fun (c4 : Nat) => pfI KQ NShA NSoA kA posA (op1A c4) gA nxtA
    let Com1B := comR KQ NShB NSoB posB
    let Pf1B := fun (c4 : Nat) => pfR KQ NShB NSoB kB posB (op1B c4) gB nxtB
    let CmiB := comI KQ NShB NSoB posB
    let PfiB := fun (c4 : Nat) => pfI KQ NShB NSoB kB posB (op1B c4) gB nxtB
    let smA := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NShA * (NSoA * KQ ^ nA) * KQ) (fun σ1 => sumTo (NS2A * NS3A) (fun σ => sumTo NRA (fun r => sumN mA (fun t => g (σ1, σ, r, t)))))
    let smAR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NShA * (NSoA * KQ ^ nA)) (fun σ1 => sumTo (NS2A * NS3A) (fun σ => sumTo NRA (fun r => sumN mA (fun t => g (σ1, σ, r, t)))))
    let m1A := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1A (main1A x.2.2.2 x.2.2.1) x.1
    let m2A := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1A x + KQ * Com2A (main2A c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2A)
    let m3A := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1A x + KQ * comPair NS2A n2 Com2A Com3A (main2A c1 x.2.2.2 x.2.2.1, main3A c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvoA := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1A c4 (rvA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1A c4 (main1A x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2A c4) (ov3A c4) (rvA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2A (Pf2A c4) (Pf3A c4) (main2A c1 x.2.2.2 x.2.2.1, main3A c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1A := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => CmiA (sd1A c4 (sop1A c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2A := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1A c4 c1 c2 c3 x + KQ * Com2A (sd2A c4 (sop2A c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2A)
    let s3A := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1A c4 c1 c2 c3 x + KQ * comPair NS2A n2 Com2A Com3A
        (sd2A c4 (sop2A c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3A c4 (sop3A c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svoA := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (PfiA c4 (sd1A c4 (sop1A c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2A (Pf2A c4) (Pf3A c4) (sd2A c4 (sop2A c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3A c4 (sop3A c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4A := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (K3 ^ (KQ * (n2 * n3))) (fun H3 => smA (fun x => g (H1, H2, H3, x)))))
    let r1A := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1A y.2.2.2) y.1
    let r2A := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2A (r1A y) y.2.2.2) y.2.1
    let r3A := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3A (r1A y) (r2A y) y.2.2.2) y.2.2.1
    let MqA := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φA (m3A (r1A y) (r2A y) y.2.2.2)
      (ozA (rvA 0 (r2A y) (r3A y) (efOf (r1A y / Q4)) (efOf (r1A y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let smB := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NShB * (NSoB * KQ ^ nB) * KQ) (fun σ1 => sumTo (NS2B * NS3B) (fun σ => sumTo NRB (fun r => sumN mB (fun t => g (σ1, σ, r, t)))))
    let smBR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NShB * (NSoB * KQ ^ nB)) (fun σ1 => sumTo (NS2B * NS3B) (fun σ => sumTo NRB (fun r => sumN mB (fun t => g (σ1, σ, r, t)))))
    let m1B := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1B (main1B x.2.2.2 x.2.2.1) x.1
    let m2B := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1B x + KQ * Com2B (main2B c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2B)
    let m3B := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1B x + KQ * comPair NS2B n2 Com2B Com3B (main2B c1 x.2.2.2 x.2.2.1, main3B c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvoB := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1B c4 (rvB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1B c4 (main1B x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2B c4) (ov3B c4) (rvB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2B (Pf2B c4) (Pf3B c4) (main2B c1 x.2.2.2 x.2.2.1, main3B c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1B := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => CmiB (sd1B c4 (sop1B c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2B := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1B c4 c1 c2 c3 x + KQ * Com2B (sd2B c4 (sop2B c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2B)
    let s3B := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1B c4 c1 c2 c3 x + KQ * comPair NS2B n2 Com2B Com3B
        (sd2B c4 (sop2B c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3B c4 (sop3B c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svoB := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (PfiB c4 (sd1B c4 (sop1B c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2B (Pf2B c4) (Pf3B c4) (sd2B c4 (sop2B c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3B c4 (sop3B c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4B := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (K3 ^ (KQ * (n2 * n3))) (fun H3 => smB (fun x => g (H1, H2, H3, x)))))
    let r1B := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1B y.2.2.2) y.1
    let r2B := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2B (r1B y) y.2.2.2) y.2.1
    let r3B := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3B (r1B y) (r2B y) y.2.2.2) y.2.2.1
    let MqB := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φB (m3B (r1B y) (r2B y) y.2.2.2)
      (ozB (rvB 0 (r2B y) (r3B y) (efOf (r1B y / Q4)) (efOf (r1B y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ KQ) (fun H1 =>
      sumTo (K2 ^ (KQ * n2)) (fun H2 => sumTo (K3 ^ (KQ * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => f (c1, c2, c3, c4)))))
    let rvTA := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1A x, m2A (r1A (H.1, H.2.1, H.2.2.1, x)) x, m3A (r1A (H.1, H.2.1, H.2.2.1, x)) (r2A (H.1, H.2.1, H.2.2.1, x)) x,
       rvoA (rget K4 (MqA (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1A (H.1, H.2.1, H.2.2.1, x)) (r2A (H.1, H.2.1, H.2.2.1, x))
         (r3A (H.1, H.2.1, H.2.2.1, x)) x)
    let pgTA := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1A c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2A c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset K3 (s3A c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φA (s3A c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozA (svA c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svTA := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1A c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2A c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3A c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svoA c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    let rvTB := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1B x, m2B (r1B (H.1, H.2.1, H.2.2.1, x)) x, m3B (r1B (H.1, H.2.1, H.2.2.1, x)) (r2B (H.1, H.2.1, H.2.2.1, x)) x,
       rvoB (rget K4 (MqB (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1B (H.1, H.2.1, H.2.2.1, x)) (r2B (H.1, H.2.1, H.2.2.1, x))
         (r3B (H.1, H.2.1, H.2.2.1, x)) x)
    let pgTB := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1B c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2B c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset K3 (s3B c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φB (s3B c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozB (svB c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svTB := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1B c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2B c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3B c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svoB c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    let colT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (xa xb : Nat × Nat × Nat × (Nat → Tup)) =>
      decide (m1B xb = s1A c.2.2.2 c.1 c.2.1 c.2.2.1 xa) ||
      decide (m2B (r1B (H.1, H.2.1, H.2.2.1, xb)) xb = s2A c.2.2.2 c.1 c.2.1 c.2.2.1 xa) ||
      decide (m3B (r1B (H.1, H.2.1, H.2.2.1, xb)) (r2B (H.1, H.2.1, H.2.2.1, xb)) xb = s3A c.2.2.2 c.1 c.2.1 c.2.2.1 xa) ||
      decide (MqB (H.1, H.2.1, H.2.2.1, xb) = φA (s3A c.2.2.2 c.1 c.2.1 c.2.2.1 xa)
        (ozA (svA c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) xa.2.2.1 xa.2.2.2)))
    let okT := fun (c : Nat × Nat × Nat × Nat) =>
      decide (c.1 < Q4 * Q4) && decide (c.2.1 < K2) && decide (c.2.2.1 < K3) && decide (c.2.2.2 < K4)
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option (PqA × List Nat) × Option (P2A × P3A) × TViewN PVA PBA) → Nat × Nat × Nat × (Option (PqB × List Nat) × Option (P2B × P3B) × TViewN PVB PBB) → Bool,
    KQ * (KQ * ((K4 * (Q4 * Q4 * (K2 * K3))) * ((K4 * (Q4 * Q4 * (K2 * K3))) * ST (fun H => smBR (fun xb => smAR (fun xa => indB (E H (rvTA H xa) (rvTB H xb)))))))) ≤
      SC (fun ca => smA (fun xa => ST (fun H => SC (fun cb => smB (fun xb =>
        indB (E (pgTA (pgTB H cb xb) ca xa) (svTA ca xa) (svTB cb xb))))))) +
      (K4 * (Q4 * Q4 * (K2 * K3))) * ((K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (K3 ^ (KQ * (n2 * n3)) *
        (K2 * (K3 * ((NShA * (NSoA * KQ ^ nA) * KQ) * (NS2A * NS3A * (e1A + e2A)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * BzA) * ((NShA * (NSoA * KQ ^ nA) * KQ) * (NS2A * NS3A * (NRA * (Q4 ^ mA * 1)))))))) +
          B4A * (Q4 * Q4 * (K2 * K3) * sm4A (fun _ => 1)))) * smB (fun _ => 1)) + (K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (K3 ^ (KQ * (n2 * n3)) *
        (K2 * (K3 * ((NShB * (NSoB * KQ ^ nB) * KQ) * (NS2B * NS3B * (e1B + e2B)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * BzB) * ((NShB * (NSoB * KQ ^ nB) * KQ) * (NS2B * NS3B * (NRB * (Q4 ^ mB * 1)))))))) +
          B4B * (Q4 * Q4 * (K2 * K3) * sm4B (fun _ => 1)))) * SC (fun _ => smA (fun _ => 1)) +
      (K4 * (Q4 * Q4 * (K2 * K3))) * SC (fun _ => smA (fun _ => ST (fun _ => (NShB * (NSoB * KQ ^ nB) * (NS2B * NS3B * (NRB * (Q4 ^ mB * 1))))))) +
      (K4 * (Q4 * Q4 * (K2 * K3))) * ((K4 * (Q4 * Q4 * (K2 * K3))) * (KQ * ((KQ * (NSoA * (KQ ^ nA * (sA * kA))) * (NS2A * NS3A * (NRA * (Q4 ^ mA * 1)))) * ST (fun _ => smBR (fun _ => 1))) + (KQ * (NSoB * (KQ ^ nB * (sB * kB))) * (NS2B * NS3B * (NRB * (Q4 ^ mB * 1)))) * ST (fun _ => smA (fun _ => 1)))) := by
  intro Com1A Pf1A CmiA PfiA Com1B Pf1B CmiB PfiB smA smAR m1A m2A m3A rvoA s1A s2A s3A svoA sm4A r1A r2A r3A MqA smB smBR m1B m2B m3B rvoB s1B s2B s3B svoB sm4B r1B r2B r3B MqB ST SC rvTA pgTA svTA rvTB pgTB svTB colT okT E
  have fo := fs_open4_two hK2 hK3 hK4 φA hφA rvA svA gzA hgzA g4A hB4A hrvA hsvA ozA hozA h1A h2A CmiA PfiA op1A sd1A d1A (comI_hides hKQ posA hposA) (fun c4 => pfI_hides hKQ posA hposA (op1A c4) gA nxtA) (fun _ _ => Nat.mod_lt _ hKQ) ov1A hov1A main1A hsd1A Com2A Pf2A op2A sd2A d2A hc2A hp2A hr2A ov2A hov2A main2A hsd2A Com3A Pf3A op3A sd3A d3A hc3A hp3A hr3A ov3A hov3A main3A hsd3A hvo1A hvo2A hvo3A sop1A sop2A sop3A hsvo1A hsvo2A hsvo3A φB hφB rvB svB gzB hgzB g4B hB4B hrvB hsvB ozB hozB h1B h2B CmiB PfiB op1B sd1B d1B (comI_hides hKQ posB hposB) (fun c4 => pfI_hides hKQ posB hposB (op1B c4) gB nxtB) (fun _ _ => Nat.mod_lt _ hKQ) ov1B hov1B main1B hsd1B Com2B Pf2B op2B sd2B d2B hc2B hp2B hr2B ov2B hov2B main2B hsd2B Com3B Pf3B op3B sd3B d3B hc3B hp3B hr3B ov3B hov3B main3B hsd3B hvo1B hvo2B hvo3B sop1B sop2B sop3B hsvo1B hsvo2B hsvo3B hφ (comI_spread_sm hKQ posB hposB main1B) E
  have pt := pair_transfer ST (lin_sum4 _ _ _ _) smAR smA (lin_sm _ _ _ _) smBR smB (lin_sm _ _ _ _)
    (comm_sm (lin_sm _ _ _ _) _ _ _ _) (comm_sm (lin_sm _ _ _ _) _ _ _ _)
    (fun H x => view4 KQ NS2A K2 K3 K4 n2 φA rvA ozA ov1A main1A Com2A Pf2A ov2A main2A Com3A Pf3A ov3A main3A Com1A Pf1A H x) (fun H x => view4 KQ NS2A K2 K3 K4 n2 φA rvA ozA ov1A main1A Com2A Pf2A ov2A main2A Com3A Pf3A ov3A main3A CmiA PfiA H x) (fun H x => view4 KQ NS2B K2 K3 K4 n2 φB rvB ozB ov1B main1B Com2B Pf2B ov2B main2B Com3B Pf3B ov3B main3B Com1B Pf1B H x) (fun H x => view4 KQ NS2B K2 K3 K4 n2 φB rvB ozB ov1B main1B Com2B Pf2B ov2B main2B Com3B Pf3B ov3B main3B CmiB PfiB H x)
    (fun H G => rom4_step (NR := NRA) (m := mA) (NSh := NShA) (NSo := NSoA) (s := sA) (k := kA) (n := nA) (NS2 := NS2A) (NS3 := NS3A) (K2 := K2) (K3 := K3) (K4 := K4) (n2 := n2) hKQ φA rvA ozA posA hposA gA hsA nxtA op1A ov1A main1A Com2A Pf2A ov2A main2A Com3A Pf3A ov3A main3A H G) (fun H G => rom4_step (NR := NRB) (m := mB) (NSh := NShB) (NSo := NSoB) (s := sB) (k := kB) (n := nB) (NS2 := NS2B) (NS3 := NS3B) (K2 := K2) (K3 := K3) (K4 := K4) (n2 := n2) hKQ φB rvB ozB posB hposB gB hsB nxtB op1B ov1B main1B Com2B Pf2B ov2B main2B Com3B Pf3B ov3B main3B H G) E
  rw [Nat.add_assoc] at pt
  rw [two_comm4]
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ pt)) (two_le4 fo)


/-- **A simulation bound moves to the real opening**: a bound at the ideal
    view and a transfer from the real view to it bound the real count, `Kt`
    times, the transfer's error `K` times. -/
theorem zkb_rom {T X C V : Type} {K Kt ε et : Nat} {ST : (T → Nat) → Nat} {smR smI : (X → Nat) → Nat}
    {SC : (C → Nat) → Nat} {rvR rvI : T → X → V} {pg : T → C → X → T} {sv : C → X → V}
    (hz : ZKB ST K smI SC rvI pg sv ε)
    (ht : ∀ E : T → V → Bool, Kt * ST (fun H => smR (fun x => indB (E H (rvR H x)))) ≤
      ST (fun H => smI (fun x => indB (E H (rvI H x)))) + et) (E : T → V → Bool) :
    Kt * K * ST (fun H => smR (fun x => indB (E H (rvR H x)))) ≤
      ST (fun H => SC (fun c => smI (fun x => indB (E (pg H c x) (sv c x))))) + (ε + K * et) := by
  calc Kt * K * ST (fun H => smR (fun x => indB (E H (rvR H x))))
      = K * (Kt * ST (fun H => smR (fun x => indB (E H (rvR H x))))) := by rw [Nat.mul_comm Kt K, Nat.mul_assoc]
    _ ≤ K * (ST (fun H => smI (fun x => indB (E H (rvI H x)))) + et) := Nat.mul_le_mul_left _ (ht E)
    _ = K * ST (fun H => smI (fun x => indB (E H (rvI H x)))) + K * et := Nat.mul_add _ _ _
    _ ≤ _ := by
      rw [← Nat.add_assoc]
      exact Nat.add_le_add_right (hz E) _

/-- The transfer's error over `n` proofs: each step's over the older
    proofs' real draws and the newer ones' ideal draws. -/
def errT {T X : Type} (K e : Nat) (ST : (T → Nat) → Nat) (smR smI : (X → Nat) → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => K ^ n * (e * ST (fun _ => smPow smR n (fun _ => 1))) + errT K e ST smR smI n * smI (fun _ => 1)

/-- **`n` transfers inside the proofs' count**: each proof's real view
    moved to its ideal one, newest first. -/
theorem pow_transfer {T X V : Type} {K e : Nat} (ST : (T → Nat) → Nat) (hST : Lin ST)
    (smR smI : (X → Nat) → Nat) (hR : Lin smR) (hI : Lin smI) (hC : Comm smI ST) (hCR : Comm smR smI)
    (hII : Comm smI smI)
    (vR vI : T → X → V)
    (hA : ∀ H (G : V → Bool), K * smR (fun x => indB (G (vR H x))) ≤ smI (fun x => indB (G (vI H x))) + e) :
    ∀ n (E : T → PowT V n → Bool), K ^ n * ST (fun H => smPow smR n (fun xs => indB (E H (rvPow (fun _ => vR) n H xs)))) ≤
      ST (fun H => smPow smI n (fun xs => indB (E H (rvPow (fun _ => vI) n H xs)))) + errT K e ST smR smI n
  | 0, E => by simp only [Nat.pow_zero, Nat.one_mul, errT, Nat.add_zero]; exact Nat.le_refl _
  | n + 1, E => by
    have hRn := lin_smPow hR n
    have hIn := lin_smPow hI n
    -- the newest proof's transfer, inside
    have s1 : K * ST (fun H => smPow smR n (fun rest => smR (fun x =>
        indB (E H (vR H x, rvPow (fun _ => vR) n H rest))))) ≤
        ST (fun H => smPow smR n (fun rest => smI (fun x => indB (E H (vI H x, rvPow (fun _ => vR) n H rest))))) +
          e * ST (fun _ => smPow smR n (fun _ => 1)) := by
      rw [← smK ST hST, ← smK ST hST, ← sm_add ST hST]
      refine sm_mono ST hST (fun H => ?_)
      rw [← smK _ hRn, ← smC _ hRn, ← sm_add _ hRn]
      exact sm_mono _ hRn (fun rest => hA H (fun v => E H (v, rvPow (fun _ => vR) n H rest)))
    -- the older proofs', the newest's ideal count outside
    have hCn : Comm smI (smPow smR n) := comm_smPow' (fun f => (hCR (fun a b => f b a)).symm) n
    have hCI : Comm smI (smPow smI n) := comm_smPow' hII n
    have s2 : K ^ n * ST (fun H => smPow smR n (fun rest => smI (fun x =>
        indB (E H (vI H x, rvPow (fun _ => vR) n H rest))))) ≤
        ST (fun H => smPow smI n (fun rest => smI (fun x => indB (E H (vI H x, rvPow (fun _ => vI) n H rest))))) +
          errT K e ST smR smI n * smI (fun _ => 1) := by
      have l : ∀ (sm : (PowT X n → Nat) → Nat), Comm smI sm → ∀ f : T → PowT X n → X → Nat,
          ST (fun H => sm (fun rest => smI (fun x => f H rest x))) = smI (fun x => ST (fun H => sm (fun rest => f H rest x))) :=
        fun sm hc f => (congrArg ST (funext fun H => hc (fun x rest => f H rest x))).trans
          (hC (fun x H => sm (fun rest => f H rest x)))
      rw [l _ hCn, l _ hCI, ← smK smI hI, ← smC smI hI, ← sm_add smI hI]
      exact sm_mono smI hI (fun x => pow_transfer ST hST smR smI hR hI hC hCR hII vR vI hA n
        (fun H w => E H (vI H x, w)))
    show K ^ (n + 1) * ST (fun H => smPow smR n (fun rest => smR (fun x =>
        indB (E H (vR H x, rvPow (fun _ => vR) n H rest))))) ≤
      ST (fun H => smPow smI n (fun rest => smI (fun x => indB (E H (vI H x, rvPow (fun _ => vI) n H rest))))) +
        (K ^ n * (e * ST (fun _ => smPow smR n (fun _ => 1))) + errT K e ST smR smI n * smI (fun _ => 1))
    rw [Nat.pow_succ, Nat.mul_assoc]
    refine Nat.le_trans (Nat.mul_le_mul_left _ s1) ?_
    rw [Nat.mul_add]
    refine Nat.le_trans (Nat.add_le_add_right s2 _) (Nat.le_of_eq ?_)
    ac_rfl
set_option maxRecDepth 100000 in
/-- **`n` copies of a four-round proof, the first commitment drawn from the
    oracle** (`fs_open4_pow` through `pow_transfer` and `zkb_rom`): `KQ^n`
    times the real count is at most `fs_open4_pow`'s bound at the ideal
    opening, its spread from `comI_spread`, plus the transfers' errors
    (`errT`): each copy's `s k / NSh` a draw over the others; one direction.
    Each copy's commitment table is its own draw, with its salt. -/
theorem fs_open4_powROM {PV PB D1 O1 Pq D2 O2 P2 D3 O3 P3 W : Type} {NR m e1 e2 NSh NSo sQ kQ nQ NS2 NS3 K2 K3 K4 KQ n2 n3 : Nat}
    (hKQ : 0 < KQ) (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φ : Nat → W → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (rv sv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (g4 : Nat → Bool) {B4 : Nat} (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hrv : ∀ c4 c2 c3 α β r t, rv c4 c2 c3 α β r t = none ∨ ∃ p x y, rv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c4 c2 c3 α β r t, ∃ p x y, sv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (oz : TViewN PV PB → W) (hoz : ∀ c4 c2 c3 α β r t, oz (rv c4 c2 c3 α β r t) = oz (rv 0 c2 c3 α β r t))
    (h1 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) + e1 + e2)
    (op1 : Nat → D1 → O1) (sd1 : Nat → O1 → D1) (d1 : D1)
    (pos : D1 → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < nQ) (g : O1 → Nat → Pq)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ sQ)
    (nxt : Pq → Nat → List Nat → Nat)
    (ov1 : Nat → TViewN PV PB → Option O1) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) (Pf2 : Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) (Pf3 : Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : Nat → TViewN PV PB → Option O3) (hov3 : ∀ c4, ov3 c4 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r))
    (hvo1 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 c4 (main1 t r)))
    (hvo2 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 c4 (main2 c t r)))
    (hvo3 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t))
    (hφs : ∀ m w m' w', φ m w = φ m' w' → m % KQ = m' % KQ) :
    let Com1 := comR KQ NSh NSo pos
    let Pf1 := fun (c4 : Nat) => pfR KQ NSh NSo kQ pos (op1 c4) g nxt
    let Cmi := comI KQ NSh NSo pos
    let Pfi := fun (c4 : Nat) => pfI KQ NSh NSo kQ pos (op1 c4) g nxt
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * KQ ^ nQ) * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * KQ ^ nQ)) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (K3 ^ (KQ * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ KQ) (fun H1 =>
      sumTo (K2 ^ (KQ * n2)) (fun H2 => sumTo (K3 ^ (KQ * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => f (c1, c2, c3, c4)))))
    let rvT := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1 x, m2 (r1 (H.1, H.2.1, H.2.2.1, x)) x, m3 (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x)) x,
       rvo (rget K4 (Mq (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x))
         (r3 (H.1, H.2.1, H.2.2.1, x)) x)
    let pgT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset K3 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (oz (sv c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svT := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svo c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    let q := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      φ (m3 c1 c2 x) (oz (rv 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))
    let pts := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x, φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (oz (sv c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) x.2.2.1 x.2.2.2)))
    let δ₀ := NS2 * NS3 * (NR * (Q4 ^ m * (NSh * (NSo * KQ ^ nQ))))
    ∀ n (E : Nat × Nat × Nat × Nat → PowT (Nat × Nat × Nat × (Option (Pq × List Nat) × Option (P2 × P3) × TViewN PV PB)) n → Bool),
    KQ ^ n * (K4 * (Q4 * Q4 * (K2 * K3))) ^ n * ST (fun H => smPow smR n (fun x => indB (E H (rvPow (fun _ => rvT) n H x)))) ≤
      ST (fun H => scPow SC n (fun c => smPow sm n (fun x => indB (E (pgPow (fun _ => pgT) n H c x) (svPow (fun _ => svT) n c x))))) +
      ((errPow (K4 * (Q4 * Q4 * (K2 * K3))) sm SC (fun _ => K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (K3 ^ (KQ * (n2 * n3)) *
        (K2 * (K3 * ((NSh * (NSo * KQ ^ nQ) * KQ) * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * ((NSh * (NSo * KQ ^ nQ) * KQ) * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4 (fun _ => 1)))) (fun j => SC (fun _ => sm (fun _ => ST (fun _ => hitB sm δ₀ j)))) n) + (K4 * (Q4 * Q4 * (K2 * K3))) ^ n * errT KQ (KQ * (NSo * (KQ ^ nQ * (sQ * kQ))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))) ST smR sm n) := by
  intro Com1 Pf1 Cmi Pfi sm smR m1 m2 m3 rvo s1 s2 s3 svo sm4 r1 r2 r3 Mq ST SC rvT pgT svT q pts δ₀ n E
  have fo := fs_open4_pow hK2 hK3 hK4 φ hφ rv sv gz hgz g4 hB4 hrv hsv oz hoz h1 h2 Cmi Pfi op1 sd1 d1 (comI_hides hKQ pos hpos) (fun c4 => pfI_hides hKQ pos hpos (op1 c4) g nxt) (fun _ _ => Nat.mod_lt _ hKQ) ov1 hov1 main1 hsd1 Com2 Pf2 op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 Com3 Pf3 op3 sd3 d3 hc3 hp3 hr3 ov3 hov3 main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 hφs (fun d v => comI_spread hKQ pos hpos d v) n
  exact zkb_rom fo (pow_transfer ST (lin_sum4 _ _ _ _) smR sm (lin_sm _ _ _ _) (lin_sm _ _ _ _)
    (comm_sm (lin_sum4 _ _ _ _) _ _ _ _) (comm_sm (lin_sm _ _ _ _) _ _ _ _) (comm_sm (lin_sm _ _ _ _) _ _ _ _)
    (fun H x => view4 KQ NS2 K2 K3 K4 n2 φ rv oz ov1 main1 Com2 Pf2 ov2 main2 Com3 Pf3 ov3 main3 Com1 Pf1 H x) (fun H x => view4 KQ NS2 K2 K3 K4 n2 φ rv oz ov1 main1 Com2 Pf2 ov2 main2 Com3 Pf3 ov3 main3 Cmi Pfi H x)
    (fun H G => rom4_step (NR := NR) (m := m) (NSh := NSh) (NSo := NSo) (s := sQ) (k := kQ) (n := nQ) (NS2 := NS2) (NS3 := NS3) (K2 := K2) (K3 := K3) (K4 := K4) (n2 := n2) hKQ φ rv oz pos hpos g hs nxt op1 ov1 main1 Com2 Pf2 ov2 main2 Com3 Pf3 ov3 main3 H G) n) E

end Circuit
