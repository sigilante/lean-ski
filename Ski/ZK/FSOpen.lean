import Ski.ZK.FSInst

/-!
# Fiat–Shamir with the commitment opened

`Ski/ZK/FSZK.lean` hashes a commitment that the view never opens.  Here the
proof opens it: beside the commitment `m = Com d σ` the proof carries an
opening `Pf d σ` (the Merkle paths and salts at the opened positions),
and the view shows the opened values `op d`.

**Hiding given the openings** (`ComPfHides`): over the salt, the
commitment with its opening has one distribution for any two data with
the same opened values `op d`.  `op` must be exactly what the opening
reveals: for a Merkle tree with salted leaves, the opened leaves' values,
which the view shows too.  Assumed perfect.  `Pf` is abstract; for any
check the scheme passes on honest openings, the simulator's opening
passes it against its view's values (`sim_opening_verifies`).

**The simulator commits its own data** (`fs_open`): it reads the opened
values its simulated view shows (`sop`, the masked columns at the query
points, independent of the challenges), commits to data `sd o` with
exactly those opened values, opens it, draws the challenge and programs
the oracle at that commitment.  The real proof's view shows the committed
data's opened values wherever it does not abort (`hrvo`); where it
aborts, it shows only the commitment, which hides (`ComHides`).  Then
the real non-interactive proof, `(H, m, opening, view)`, and the
simulator's keep the transcript's error, as in `fs_transcript`.

Scope.  One proof per oracle; one round (the LogUp challenges, at
generic `β`; `ζ`, the FRI challenge and the query points stay fixed
parameters); the oracle ideal and `Com` a primitive apart from it; the
hiding perfect.  Only the first commitment is in the proof's output: the
later ones (the permutation and quotient matrices, the quotient's
codewords, FRI's layers) are absent, their roots neither output nor
hashed.  The view's openings must be the committed data's
(`hrvo`, `hsvo`): for an instance, the main groups' openings at the
query points.
-/

namespace Circuit

open ZKF

/-- **A commitment hides given its openings**: over the salt, the
    commitment with its opening proof has one distribution for any two
    data with the same opened values. -/
def ComPfHides {D O Pp : Type} (NS : Nat) (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (op : D → O) : Prop :=
  ∀ (d d' : D), op d = op d' → ∀ E : Nat → Pp → Bool,
    sumTo NS (fun σ => indB (E (Com d σ) (Pf d σ))) = sumTo NS (fun σ => indB (E (Com d' σ) (Pf d' σ)))

theorem sig_in {NS NR m : Nat} (g : Nat → Nat → (Nat → Tup) → Nat) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g σ r t))) =
      sumTo NR (fun r => sumN m (fun t => sumTo NS (fun σ => g σ r t))) := by
  rw [sumTo_exch _ NR NS]
  exact sumTo_congr _ (fun r _ => sumTo_sumN m NS (fun σ t => g σ r t))

/-- The event on the view the opened commitment reduces to, for a salt
    `σ`: the commitment and opening of the data the view's openings fix,
    or of a fixed datum where the view shows nothing. -/
def openEv {PV PB D O Pp : Type} (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (sd : O → D) (d0 : D)
    (ov : TViewN PV PB → Option O) (F : Nat → Option Pp → TViewN PV PB → Bool) (σ : Nat) (v : TViewN PV PB) : Bool :=
  match ov v with
  | some o => F (Com (sd o) σ) (some (Pf (sd o) σ)) v
  | none => F (Com d0 σ) none v

/-- **The real count, the commitment opened, reduces to view events.** -/
theorem open_real {PV PB D O Pp : Type} {NS NR m : Nat} (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (op : D → O)
    (sd : O → D) (d0 : D) (hcom : ComHides NS Com) (hpf : ComPfHides NS Com Pf op)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (v : Nat → (Nat → Tup) → TViewN PV PB) (hvo : ∀ r t, v r t = none ∨ ov (v r t) = some (op (main t r)))
    (F : Nat → Option Pp → TViewN PV PB → Bool) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (F (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ)) (v r t))))) =
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (openEv Com Pf sd d0 ov F σ (v r t))))) := by
  have key : ∀ r t, sumTo NS (fun σ => indB (F (Com (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ))
      (v r t))) = sumTo NS (fun σ => indB (openEv Com Pf sd d0 ov F σ (v r t))) := by
    intro r t
    rcases hvo r t with e | e
    · rw [e]
      unfold openEv
      rw [hovn]
      exact hcom (main t r) d0 (fun mm => F mm none none)
    · unfold openEv
      rw [e]
      exact hpf (main t r) (sd (op (main t r))) (hsd t r).symm (fun mm p => F mm (some p) (v r t))
  rw [sig_in, sig_in]
  exact sumTo_congr _ (fun r _ => Nat.le_antisymm (sumN_mono m (fun t => Nat.le_of_eq (key r t)))
    (sumN_mono m (fun t => Nat.le_of_eq (key r t).symm)))

theorem openEv_and {PV PB D O Pp : Type} (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (sd : O → D) (d0 : D)
    (ov : TViewN PV PB → Option O) (b : Bool) (F : Nat → Option Pp → TViewN PV PB → Bool) (σ : Nat)
    (v : TViewN PV PB) :
    openEv Com Pf sd d0 ov (fun mm p w => b && F mm p w) σ v = (b && openEv Com Pf sd d0 ov F σ v) := by
  unfold openEv; cases ov v <;> rfl

section
variable {PV PB D O Pp : Type} {NR m NS : Nat} (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (op : D → O)
  (sd : O → D) (d0 : D) (ov : TViewN PV PB → Option O) (main : (Nat → Tup) → Nat → D) (sop : Nat → (Nat → Tup) → O)
  (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)

/-- The event a salt `σ` gives on the view, the challenge index read. -/
def openG (F : Nat → Nat → Option Pp × TViewN PV PB → Bool) (σ c : Nat) (v : TViewN PV PB) : Bool :=
  openEv Com Pf sd d0 ov (fun mm p w => F c mm (p, w)) σ v

/-- The real count as view events, one transcript count per salt. -/
theorem open_real_t (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r)) (hcom : ComHides NS Com) (hpf : ComPfHides NS Com Pf op)
    (hovn : ov none = none)
    (hrvo : ∀ α β r t, rv α β r t = none ∨ ov (rv α β r t) = some (op (main t r)))
    (F : Nat → Nat → Option Pp × TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
        ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
    sumTo NS (fun σ => tsumN NR m (fun α β r t =>
      indB (genB β && openG Com Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α) (rv α β r t)))) := by
  rw [sumTo_congr _ (fun c _ => open_real (NR := NR) (m := m) Com Pf op sd d0 hcom hpf ov hovn main hsd
    (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hrvo _ _ r t)
    (fun mm p w => genB (efOf (c % Q4)) && F c mm (p, w)))]
  rw [sumTo_exch _ NS (Q4 * Q4)]
  refine sumTo_congr _ (fun σ _ => ?_)
  rw [← csum_tsumN rv (fun c v => openG Com Pf sd d0 ov F σ c v)]
  exact sumTo_congr _ (fun c _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
    (sumN_mono m (fun t => Nat.le_of_eq (by rw [openEv_and]; rfl)))
    (sumN_mono m (fun t => Nat.le_of_eq (by rw [openEv_and]; rfl)))))

/-- The simulator's count as view events. -/
theorem open_sim_t (hsvo : ∀ α β r t, ov (sv α β r t) = some (sop r t))
    (F : Nat → Nat → Option Pp × TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com (sd (sop r t)) σ)
        (some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
    sumTo NS (fun σ => tsumN NR m (fun α β r t =>
      indB (genB β && openG Com Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α) (sv α β r t)))) := by
  rw [sumTo_exch _ NS (Q4 * Q4)]
  refine sumTo_congr _ (fun σ _ => ?_)
  rw [← csum_tsumN sv (fun c v => openG Com Pf sd d0 ov F σ c v)]
  exact sumTo_congr _ (fun c _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
    (sumN_mono m (fun t => Nat.le_of_eq (by unfold openG openEv; rw [hsvo])))
    (sumN_mono m (fun t => Nat.le_of_eq (by unfold openG openEv; rw [hsvo])))))
end

/-- **Fiat–Shamir with the commitment opened, in the programmable random
    oracle model**: the proof carries the commitment `m = Com (main t r) σ`
    of its first message, the opening `Pf (main t r) σ` wherever it does
    not abort, and the view, whose opened values are the committed
    data's.  The simulator commits and opens `sd (sop r t)`, data with the
    opened values its own view shows, draws the challenges and programs
    the oracle there.  With the commitment hiding given its openings,
    `Q4²` times the real count is within `(Q4²)^n · NS · (e1 + e2)` of the
    simulator's, and back. -/
theorem fs_open {PV PB D O Pp : Type} {NR m NS n e1 e2 : Nat} (Com : D → Nat → Nat) (Pf : D → Nat → Pp)
    (op : D → O) (sd : O → D) (d0 : D) (hcom : ComHides NS Com)
    (hpf : ComPfHides NS Com Pf op) (hrange : ∀ d σ, Com d σ < n)
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
            r t)).map (fun _ => Pf (main t r) σ),
          rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)))))) ≤
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sd (sop r t)) σ) H c) (Com (sd (sop r t)) σ)
        (some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ n * (NS * (e1 + e2)) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sd (sop r t)) σ) H c) (Com (sd (sop r t)) σ)
        (some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)).map (fun _ => Pf (main t r) σ),
          rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)))))) +
    (Q4 * Q4) ^ n * (NS * (e1 + e2)) := by
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × (Nat → Tup) → Nat),
      sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => sumTo N (fun i => f i (σ, r, t))))) =
        sumTo N (fun i => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => f i (σ, r, t))))) :=
    fun N f => sm_exch (fun i σ r t => f i (σ, r, t))
  have core : ∀ F : Nat → Nat → Option Pp × TViewN PV PB → Bool,
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
          ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf (main t r) σ),
            rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) ≤
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (sd (sop r t)) σ)
          (some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) + NS * (e1 + e2) ∧
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (sd (sop r t)) σ)
          (some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) ≤
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
          ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf (main t r) σ),
            rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) + NS * (e1 + e2) := by
    intro F
    rw [open_real_t Com Pf op sd d0 ov main rv hsd hcom hpf hovn hrvo F,
      open_sim_t Com Pf sd d0 ov sop sv hsvo F, ← sumTo_const (e1 + e2) NS, ← sumTo_add, ← sumTo_add]
    exact ⟨sumTo_mono _ (fun σ _ => (tsumN_ab rv sv hrv hsv h1' h2' _).1),
      sumTo_mono _ (fun σ _ => (tsumN_ab rv sv hrv hsv h1' h2' _).2)⟩
  refine ⟨fs_zk (X := Nat × Nat × (Nat → Tup)) (K := Q4 * Q4) (n := n) (ε := NS * (e1 + e2))
    (Nat.mul_pos Q4_pos Q4_pos) (fun g => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ, r, t))))) hsm
    (fun x => Com (main x.2.2 x.2.1) x.1) (fun x => Com (sd (sop x.2.1 x.2.2)) x.1) (fun x => hrange _ _)
    (fun c x => ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2)).map (fun _ => Pf (main x.2.2 x.2.1) x.1),
      rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c x => (some (Pf (sd (sop x.2.1 x.2.2)) x.1), sv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c => genB (efOf (c % Q4))) (fun F => (core F).1) (fun H mm _ w => E H mm w),
    fs_zk' (X := Nat × Nat × (Nat → Tup)) (K := Q4 * Q4) (n := n) (ε := NS * (e1 + e2))
    (Nat.mul_pos Q4_pos Q4_pos) (fun g => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ, r, t))))) hsm
    (fun x => Com (main x.2.2 x.2.1) x.1) (fun x => Com (sd (sop x.2.1 x.2.2)) x.1) (fun x => hrange _ _)
    (fun c x => ((ov (rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2)).map (fun _ => Pf (main x.2.2 x.2.1) x.1),
      rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c x => (some (Pf (sd (sop x.2.1 x.2.2)) x.1), sv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c => genB (efOf (c % Q4))) (fun F => (core F).2) (fun H mm _ w => E H mm w)⟩

/-- **The simulator's opening verifies**: for any check `Verify` the scheme
    passes on honest commitments and openings, the simulator's
    commitment and opening of `sd o` pass it against the opened values
    `o` its view shows, whenever `sd o` opens to `o`. -/
theorem sim_opening_verifies {D O Pp : Type} (Com : D → Nat → Nat) (Pf : D → Nat → Pp) (op : D → O) (sd : O → D)
    (Verify : Nat → O → Pp → Bool) (hver : ∀ d σ, Verify (Com d σ) (op d) (Pf d σ) = true)
    (o : O) (h : op (sd o) = o) (σ : Nat) : Verify (Com (sd o) σ) o (Pf (sd o) σ) = true := by
  have := hver (sd o) σ
  rw [h] at this
  exact this

end Circuit
