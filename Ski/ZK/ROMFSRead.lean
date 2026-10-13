import Ski.ZK.ROMAbort

/-!
# The distinguisher's queries reading the Fiat–Shamir table

The theorems so far let the distinguisher's queries into the commitment's
table read the opening and the commitment, not the Fiat–Shamir table.
Here they may.  After the reprogramming (`fs_real`) the real view reads
`rset H m c`, the table `H` but at the message, so for each `H` it is a view
of the challenge and the draw, and `fs_zk` holds with its hypothesis taken
at each table (`fs_zkT`).  An opening that reads the table then reads it
through the commitment's value, and hides when it hides at each table
(`comPf_choose`, the commitment's value picking the table); so one round
with the commitment opened holds (`fs_openT`), and over the oracle's
commitment, the distinguisher's queries `nxtT H` chosen from the table, the
transfer runs at each table and `fs_openT` at the ideal opening
(`fs_openROMT`).  One round; the multi-round theorems over table-reading
views are not yet written.
-/

set_option autoImplicit false
namespace Circuit
open ZKF

/-- **Fiat–Shamir keeps an exact simulation, the views reading the table**:
    `fs_zk` with the real and simulated views reading the oracle's table
    (`rvT H c x`, `svT H c x`), the distinguisher's queries among them.
    After the reprogramming the real view reads `rset H (msg x) c`, which is
    `H` but at the message, so the hypothesis is taken at each table `H`. -/
theorem fs_zkT {X Vw : Type} {K n ε : Nat} (hK : 0 < K) (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (msg smsg : X → Nat) (hmsg : ∀ x, msg x < n) (rvT svT : Nat → Nat → X → Vw) (gd : Nat → Bool)
    (h : ∀ (H : Nat) (F : Nat → Nat → Vw → Bool),
      sumTo K (fun c => sm (fun x => indB (gd c && F c (msg x) (rvT (rset K (msg x) H c) c x)))) ≤
        sumTo K (fun c => sm (fun x => indB (gd c && F c (smsg x) (svT (rset K (smsg x) H c) c x)))) + ε)
    (E : Nat → Nat → Nat → Vw → Bool) :
    K * sumTo (K ^ n) (fun H => sm (fun x => indB (gd (rget K (msg x) H) &&
      E H (msg x) (rget K (msg x) H) (rvT H (rget K (msg x) H) x)))) ≤
      sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c &&
        E (rset K (smsg x) H c) (smsg x) c (svT (rset K (smsg x) H c) c x))))) + K ^ n * ε := by
  rw [fs_real (Vw := X) hK sm hsm msg hmsg (fun _ x => x) (fun H m c x => gd c && E H m c (rvT H c x))]
  calc sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c &&
        E (rset K (msg x) H c) (msg x) c (rvT (rset K (msg x) H c) c x)))))
      ≤ sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c &&
          E (rset K (smsg x) H c) (smsg x) c (svT (rset K (smsg x) H c) c x)))) + ε) :=
        sumTo_mono _ (fun H _ => h H (fun c m v => E (rset K m H c) m c v))
    _ = _ := by rw [sumTo_add, sumTo_const]

theorem sum_pick (g : Nat → Bool) : ∀ (n a : Nat), a < n →
    sumTo n (fun v => indB (decide (a = v) && g v)) = indB (g a)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, h => by
    show sumTo n (fun v => indB (decide (a = v) && g v)) + indB (decide (a = n) && g n) = indB (g a)
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | e
    · rw [sum_pick g n a h']
      have : decide (a = n) = false := decide_eq_false (Nat.ne_of_lt h')
      rw [this]; rfl
    · subst e
      have z : ∀ m, m ≤ a → sumTo m (fun v => indB (decide (a = v) && g v)) = 0 := by
        intro m; induction m with
        | zero => intro _; rfl
        | succ m ih => intro hm; show sumTo m _ + indB (decide (a = m) && g m) = 0
                       rw [ih (Nat.le_of_succ_le hm), decide_eq_false (Nat.ne_of_gt hm)]; rfl
      rw [z a (Nat.le_refl _), decide_eq_true rfl, Nat.zero_add]; rfl

/-- **An opening chosen by the commitment's value hides** when it hides at
    every choice: the commitment's value picks the choice, and each value's
    count is hidden. -/
theorem comPf_choose {D O Pp : Type} {NS n : Nat} {Com : D → Nat → Nat} {Pf : Nat → D → Nat → Pp} {op : D → O}
    (hp : ∀ T, ComPfHides NS Com (Pf T) op) (hr : ∀ d σ, Com d σ < n) (tab : Nat → Nat) :
    ComPfHides NS Com (fun d σ => Pf (tab (Com d σ)) d σ) op := by
  intro d d' hop E
  have e : ∀ dd : D, sumTo NS (fun σ => indB (E (Com dd σ) (Pf (tab (Com dd σ)) dd σ))) =
      sumTo n (fun v => sumTo NS (fun σ => indB (decide (Com dd σ = v) && E (Com dd σ) (Pf (tab v) dd σ)))) := fun dd => by
    rw [sumTo_exch _ NS n]
    refine sumTo_congr _ (fun σ _ => ?_)
    exact (sum_pick (fun v => E (Com dd σ) (Pf (tab v) dd σ)) n (Com dd σ) (hr dd σ)).symm
  rw [e d, e d']
  refine sumTo_congr _ (fun v _ => ?_)
  exact hp (tab v) d d' hop (fun c p => decide (c = v) && E c p)

section
variable {PV PB D O Pp : Type} {NR m NS : Nat} (Com : D → Nat → Nat) (Pf : Nat → D → Nat → Pp) (op : D → O)
  (sd : O → D) (d0 : D) (ov : TViewN PV PB → Option O) (main : (Nat → Tup) → Nat → D) (sop : Nat → (Nat → Tup) → O)
  (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)

/-- `openG` with the opening read at the challenge. -/
def openGC (F : Nat → Nat → Option Pp × TViewN PV PB → Bool) (σ c : Nat) (v : TViewN PV PB) : Bool :=
  openEv Com (Pf c) sd d0 ov (fun mm p w => F c mm (p, w)) σ v

theorem open_real_tC (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r)) (hcom : ComHides NS Com)
    (hpf : ∀ c, ComPfHides NS Com (Pf c) op) (hovn : ov none = none)
    (hrvo : ∀ α β r t, rv α β r t = none ∨ ov (rv α β r t) = some (op (main t r)))
    (F : Nat → Nat → Option Pp × TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
        ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf c (main t r) σ),
          rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
    sumTo NS (fun σ => tsumN NR m (fun α β r t =>
      indB (genB β && openGC Com Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α) (rv α β r t)))) := by
  rw [sumTo_congr _ (fun c _ => open_real (NR := NR) (m := m) Com (Pf c) op sd d0 hcom (hpf c) ov hovn main hsd
    (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hrvo _ _ r t)
    (fun mm p w => genB (efOf (c % Q4)) && F c mm (p, w)))]
  rw [sumTo_exch _ NS (Q4 * Q4)]
  refine sumTo_congr _ (fun σ _ => ?_)
  rw [← csum_tsumN rv (fun c v => openGC Com Pf sd d0 ov F σ c v)]
  exact sumTo_congr _ (fun c _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
    (sumN_mono m (fun t => Nat.le_of_eq (by rw [openEv_and]; rfl)))
    (sumN_mono m (fun t => Nat.le_of_eq (by rw [openEv_and]; rfl)))))

theorem open_sim_tC (hsvo : ∀ α β r t, ov (sv α β r t) = some (sop r t))
    (F : Nat → Nat → Option Pp × TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com (sd (sop r t)) σ)
        (some (Pf c (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
    sumTo NS (fun σ => tsumN NR m (fun α β r t =>
      indB (genB β && openGC Com Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α) (sv α β r t)))) := by
  rw [sumTo_exch _ NS (Q4 * Q4)]
  refine sumTo_congr _ (fun σ _ => ?_)
  rw [← csum_tsumN sv (fun c v => openGC Com Pf sd d0 ov F σ c v)]
  exact sumTo_congr _ (fun c _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
    (sumN_mono m (fun t => Nat.le_of_eq (by unfold openGC openEv; rw [hsvo])))
    (sumN_mono m (fun t => Nat.le_of_eq (by unfold openGC openEv; rw [hsvo])))))
end

/-- **Fiat–Shamir with the commitment opened, the opening reading the
    oracle's table** (`fs_open` over `fs_zkT`): the opening `PfT H d σ` may
    read the Fiat–Shamir table `H` (the distinguisher's queries chosen
    from it); hiding given the openings at every table (`hpf`).  After the
    reprogramming the opening reads `H` set at the commitment, a choice by
    the commitment's value (`comPf_choose`).  One direction. -/
theorem fs_openT {PV PB D O Pp : Type} {NR m NS n e1 e2 : Nat} (Com : D → Nat → Nat) (PfT : Nat → D → Nat → Pp)
    (op : D → O) (sd : O → D) (d0 : D) (hcom : ComHides NS Com)
    (hpf : ∀ T, ComPfHides NS Com (PfT T) op) (hrange : ∀ d σ, Com d σ < n)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (sop : Nat → (Nat → Tup) → O) {rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB}
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (hrvo : ∀ α β r t, rv α β r t = none ∨ ov (rv α β r t) = some (op (main t r)))
    (hsvo : ∀ α β r t, ov (sv α β r t) = some (sop r t))
    (E : Nat → Nat → Option Pp × TViewN PV PB → Bool) :
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)).map (fun _ => PfT H (main t r) σ),
          rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)))))) ≤
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sd (sop r t)) σ) H c) (Com (sd (sop r t)) σ)
        (some (PfT (rset (Q4 * Q4) (Com (sd (sop r t)) σ) H c) (sd (sop r t)) σ),
          sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ n * (NS * (e1 + e2)) := by
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × (Nat → Tup) → Nat),
      sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => sumTo N (fun i => f i (σ, r, t))))) =
        sumTo N (fun i => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => f i (σ, r, t))))) :=
    fun N f => sm_exch (fun i σ r t => f i (σ, r, t))
  refine fs_zkT (X := Nat × Nat × (Nat → Tup)) (K := Q4 * Q4) (n := n) (ε := NS * (e1 + e2))
    (Nat.mul_pos Q4_pos Q4_pos) (fun g => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ, r, t))))) hsm
    (fun x => Com (main x.2.2 x.2.1) x.1) (fun x => Com (sd (sop x.2.1 x.2.2)) x.1) (fun x => hrange _ _)
    (fun T c x => ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2)).map (fun _ => PfT T (main x.2.2 x.2.1) x.1),
      rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun T c x => (some (PfT T (sd (sop x.2.1 x.2.2)) x.1), sv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c => genB (efOf (c % Q4))) (fun H F => ?_) (fun H mm _ w => E H mm w)
  have hpc : ∀ c, ComPfHides NS Com (fun d σ => PfT (rset (Q4 * Q4) (Com d σ) H c) d σ) op :=
    fun c => comPf_choose hpf hrange (fun v => rset (Q4 * Q4) v H c)
  rw [open_real_tC Com (fun c d σ => PfT (rset (Q4 * Q4) (Com d σ) H c) d σ) op sd d0 ov main rv hsd hcom hpc hovn hrvo F,
    open_sim_tC Com (fun c d σ => PfT (rset (Q4 * Q4) (Com d σ) H c) d σ) sd d0 ov sop sv hsvo F,
    ← sumTo_const (e1 + e2) NS, ← sumTo_add]
  exact sumTo_mono _ (fun σ _ => (tsumN_ab rv sv hrv hsv h1' h2' _).1)

/-- **One Fiat–Shamir round, the commitment drawn from the oracle, the
    distinguisher's queries reading the Fiat–Shamir table** (`nxtT H`): the
    transfer at each table, then `fs_openT` at the ideal opening, whose
    queries read the table the simulator programs.  `K` times the real count
    is at most the simulator's plus `fs_open`'s error and `s k / NSh` a
    draw; one direction. -/
theorem fs_openROMT {PV PB D O P : Type} {NR m e1 e2 K n NSh NSo s k : Nat} (hK : 0 < K)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (g : O → Nat → P)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxtT : Nat → P → Nat → List Nat → Nat)
    (op : D → O) (sd : O → D) (d0 : D)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (sop : Nat → (Nat → Tup) → O) {rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB}
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (hrvo : ∀ α β r t, rv α β r t = none ∨ ov (rv α β r t) = some (op (main t r)))
    (hsvo : ∀ α β r t, ov (sv α β r t) = some (sop r t))
    (E : Nat → Nat → Option (P × List Nat) × TViewN PV PB → Bool) :
    K * ((Q4 * Q4) * sumTo ((Q4 * Q4) ^ K) (fun H => sumTo (NSh * (NSo * K ^ n)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H % Q4)) && E H (comR K NSh NSo pos (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H / Q4))
          (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H % Q4)) r t)).map
            (fun _ => pfR K NSh NSo k pos op g (nxtT H) (main t r) σ),
          rv (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H / Q4))
            (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H % Q4)) r t))))))) ≤
    sumTo ((Q4 * Q4) ^ K) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSh * (NSo * K ^ n) * K) (fun σ =>
      sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (comI K NSh NSo pos (sd (sop r t)) σ) H c)
        (comI K NSh NSo pos (sd (sop r t)) σ)
        (some (pfI K NSh NSo k pos op g (nxtT (rset (Q4 * Q4) (comI K NSh NSo pos (sd (sop r t)) σ) H c)) (sd (sop r t)) σ),
          sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
      (Q4 * Q4) ^ K * (NSh * (NSo * K ^ n) * K * (e1 + e2)) +
      (Q4 * Q4) * ((Q4 * Q4) ^ K * (K * (NSo * (K ^ n * (s * k))) * (NR * (Q4 ^ m * 1)))) := by
  have fo := fs_openT (n := K) (comI K NSh NSo pos) (fun T => pfI K NSh NSo k pos op g (nxtT T)) op sd d0
    (comI_hides hK pos hpos) (fun T => pfI_hides hK pos hpos op g (nxtT T)) (fun _ _ => Nat.mod_lt _ hK) ov hovn main
    hsd sop h1 h2 hrv hsv hrvo hsvo E
  have hso := smRT_lin NR m
  have step : ∀ H, K * sumTo (NSh * (NSo * K ^ n)) (fun σ => smRT NR m (fun y =>
      indB (genB (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H % Q4)) &&
        E H (comR K NSh NSo pos (main y.2 y.1) σ)
          ((ov (rv (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H / Q4))
          (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H % Q4)) y.1 y.2)).map
            (fun _ => pfR K NSh NSo k pos op g (nxtT H) (main y.2 y.1) σ),
          rv (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H / Q4))
            (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H % Q4)) y.1 y.2)))) ≤
      sumTo (NSh * (NSo * K ^ n) * K) (fun σ => smRT NR m (fun y =>
      indB (genB (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H % Q4)) &&
        E H (comI K NSh NSo pos (main y.2 y.1) σ)
          ((ov (rv (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H / Q4))
          (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H % Q4)) y.1 y.2)).map
            (fun _ => pfI K NSh NSo k pos op g (nxtT H) (main y.2 y.1) σ),
          rv (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H / Q4))
            (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H % Q4)) y.1 y.2)))) +
      K * (NSo * (K ^ n * (s * k))) * (NR * (Q4 ^ m * 1)) := fun H => by
    have tr := (transferR_in (n := n) (NSh := NSh) (NSo := NSo) (s := s) (k := k) hK (smRT NR m) hso pos hpos op g hs
      (nxtT H) (fun y => main y.2 y.1)
      (fun y c pf => genB (efOf (rget (Q4 * Q4) c H % Q4)) && E H c (
        (ov (rv (efOf (rget (Q4 * Q4) c H / Q4)) (efOf (rget (Q4 * Q4) c H % Q4)) y.1 y.2)).map (fun _ => pf),
        rv (efOf (rget (Q4 * Q4) c H / Q4)) (efOf (rget (Q4 * Q4) c H % Q4)) y.1 y.2))).1
    rw [hso, hso, smRT_one] at tr
    exact tr
  rw [Nat.mul_left_comm K (Q4 * Q4), sumTo_mul]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => step H))) ?_
  rw [sumTo_add, sumTo_const, Nat.mul_add]
  exact Nat.add_le_add_right fo _
end Circuit
