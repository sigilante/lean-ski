import Ski.ZK.ROMRounds

/-!
# Query answers shown where the proof aborts

The Fiat–Shamir theorems show the opening, and with it the distinguisher's
answers into the commitment's table, only where the proof does not abort;
where it aborts the view shows the commitment alone.  Here a part `PA` is
shown always (`fs_openQ`, over `openEvQ`): the commitment hides jointly
with it, and given the openings with both.  Over the oracle's commitment
(`fs_openROMQ`), the distinguisher's first `k0` queries are chosen from the
commitment alone (`nxtC`) and answered always, the oldest `k0` of the run
(`runQ_split`); the rest read the opening.  The transfer covers both, as
one run of `k0 + k` queries, and the ideal opening's commitment-only
answers hide with the commitment (`pfI_hides` at a constant opening).  One
round.  Two rounds, both commitments with a part shown always:
`fs_open2Q` (`open_two_coreQ`, over `openEv2Q`); three and four rounds, the
first commitment's: `fs_open3Q`, `fs_open3UQ`, `fs_open4Q`; and over the
oracle's commitment, four rounds: `fs_open4ROMQ`.
-/

set_option autoImplicit false
namespace Circuit
open ZKF

/-- The event on the view with a part `Pa` shown even where the proof
    aborts. -/
def openEvQ {PV PB D O Pa Pp : Type} (Com : D → Nat → Nat) (PA : D → Nat → Pa) (Pf : D → Nat → Pp) (sd : O → D) (d0 : D)
    (ov : TViewN PV PB → Option O) (F : Nat → Pa → Option Pp → TViewN PV PB → Bool) (σ : Nat) (v : TViewN PV PB) : Bool :=
  match ov v with
  | some o => F (Com (sd o) σ) (PA (sd o) σ) (some (Pf (sd o) σ)) v
  | none => F (Com d0 σ) (PA d0 σ) none v

theorem open_realQ {PV PB D O Pa Pp : Type} {NS NR m : Nat} (Com : D → Nat → Nat) (PA : D → Nat → Pa) (Pf : D → Nat → Pp)
    (op : D → O) (sd : O → D) (d0 : D)
    (hcom : ∀ (d d' : D) (E : Nat → Pa → Bool), sumTo NS (fun σ => indB (E (Com d σ) (PA d σ))) =
      sumTo NS (fun σ => indB (E (Com d' σ) (PA d' σ))))
    (hpf : ComPfHides NS Com (fun d σ => (PA d σ, Pf d σ)) op)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (v : Nat → (Nat → Tup) → TViewN PV PB) (hvo : ∀ r t, v r t = none ∨ ov (v r t) = some (op (main t r)))
    (F : Nat → Pa → Option Pp → TViewN PV PB → Bool) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (F (Com (main t r) σ) (PA (main t r) σ) ((ov (v r t)).map (fun _ => Pf (main t r) σ)) (v r t))))) =
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (openEvQ Com PA Pf sd d0 ov F σ (v r t))))) := by
  have key : ∀ r t, sumTo NS (fun σ => indB (F (Com (main t r) σ) (PA (main t r) σ)
      ((ov (v r t)).map (fun _ => Pf (main t r) σ)) (v r t))) =
      sumTo NS (fun σ => indB (openEvQ Com PA Pf sd d0 ov F σ (v r t))) := by
    intro r t
    rcases hvo r t with e | e
    · rw [e]
      unfold openEvQ
      rw [hovn]
      exact hcom (main t r) d0 (fun mm a => F mm a none none)
    · unfold openEvQ
      rw [e]
      exact hpf (main t r) (sd (op (main t r))) (hsd t r).symm (fun mm p => F mm p.1 (some p.2) (v r t))
  rw [sig_in, sig_in]
  exact sumTo_congr _ (fun r _ => Nat.le_antisymm (sumN_mono m (fun t => Nat.le_of_eq (key r t)))
    (sumN_mono m (fun t => Nat.le_of_eq (key r t).symm)))

theorem openEvQ_and {PV PB D O Pa Pp : Type} (Com : D → Nat → Nat) (PA : D → Nat → Pa) (Pf : D → Nat → Pp) (sd : O → D)
    (d0 : D) (ov : TViewN PV PB → Option O) (b : Bool) (F : Nat → Pa → Option Pp → TViewN PV PB → Bool) (σ : Nat)
    (v : TViewN PV PB) :
    openEvQ Com PA Pf sd d0 ov (fun mm a p w => b && F mm a p w) σ v = (b && openEvQ Com PA Pf sd d0 ov F σ v) := by
  unfold openEvQ; cases ov v <;> rfl

section
variable {PV PB D O Pa Pp : Type} {NR m NS : Nat} (Com : D → Nat → Nat) (PA : D → Nat → Pa) (Pf : D → Nat → Pp)
  (op : D → O) (sd : O → D) (d0 : D) (ov : TViewN PV PB → Option O) (main : (Nat → Tup) → Nat → D)
  (sop : Nat → (Nat → Tup) → O) (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)

def openGQ (F : Nat → Nat → Pa × Option Pp × TViewN PV PB → Bool) (σ c : Nat) (v : TViewN PV PB) : Bool :=
  openEvQ Com PA Pf sd d0 ov (fun mm a p w => F c mm (a, p, w)) σ v

theorem open_real_tQ (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (hcom : ∀ (d d' : D) (E : Nat → Pa → Bool), sumTo NS (fun σ => indB (E (Com d σ) (PA d σ))) =
      sumTo NS (fun σ => indB (E (Com d' σ) (PA d' σ))))
    (hpf : ComPfHides NS Com (fun d σ => (PA d σ, Pf d σ)) op) (hovn : ov none = none)
    (hrvo : ∀ α β r t, rv α β r t = none ∨ ov (rv α β r t) = some (op (main t r)))
    (F : Nat → Nat → Pa × Option Pp × TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
        (PA (main t r) σ, (ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
    sumTo NS (fun σ => tsumN NR m (fun α β r t =>
      indB (genB β && openGQ Com PA Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α) (rv α β r t)))) := by
  rw [sumTo_congr _ (fun c _ => open_realQ (NR := NR) (m := m) Com PA Pf op sd d0 hcom hpf ov hovn main hsd
    (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hrvo _ _ r t)
    (fun mm a p w => genB (efOf (c % Q4)) && F c mm (a, p, w)))]
  rw [sumTo_exch _ NS (Q4 * Q4)]
  refine sumTo_congr _ (fun σ _ => ?_)
  rw [← csum_tsumN rv (fun c v => openGQ Com PA Pf sd d0 ov F σ c v)]
  exact sumTo_congr _ (fun c _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
    (sumN_mono m (fun t => Nat.le_of_eq (by rw [openEvQ_and]; rfl)))
    (sumN_mono m (fun t => Nat.le_of_eq (by rw [openEvQ_and]; rfl)))))

theorem open_sim_tQ (hsvo : ∀ α β r t, ov (sv α β r t) = some (sop r t))
    (F : Nat → Nat → Pa × Option Pp × TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com (sd (sop r t)) σ)
        (PA (sd (sop r t)) σ, some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
    sumTo NS (fun σ => tsumN NR m (fun α β r t =>
      indB (genB β && openGQ Com PA Pf sd d0 ov F σ (efIdx β + Q4 * efIdx α) (sv α β r t)))) := by
  rw [sumTo_exch _ NS (Q4 * Q4)]
  refine sumTo_congr _ (fun σ _ => ?_)
  rw [← csum_tsumN sv (fun c v => openGQ Com PA Pf sd d0 ov F σ c v)]
  exact sumTo_congr _ (fun c _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
    (sumN_mono m (fun t => Nat.le_of_eq (by unfold openGQ openEvQ; rw [hsvo])))
    (sumN_mono m (fun t => Nat.le_of_eq (by unfold openGQ openEvQ; rw [hsvo])))))
end
/-- **Fiat–Shamir with the commitment opened, a part shown even where the
    proof aborts** (`fs_open` with `PA`): the view carries `PA d σ` always
    (say the distinguisher's answers to queries it chooses from the
    commitment alone) and the opening `Pf d σ` where the proof does not
    abort; the commitment hides jointly with `PA` (`hcom`) and, given the
    openings, with both (`hpf`). -/
theorem fs_openQ {PV PB D O Pa Pp : Type} {NR m NS n e1 e2 : Nat} (Com : D → Nat → Nat) (PA : D → Nat → Pa) (Pf : D → Nat → Pp)
    (op : D → O) (sd : O → D) (d0 : D) (hcom : ∀ (d d' : D) (E : Nat → Pa → Bool), sumTo NS (fun σ => indB (E (Com d σ) (PA d σ))) =
      sumTo NS (fun σ => indB (E (Com d' σ) (PA d' σ))))
    (hpf : ComPfHides NS Com (fun d σ => (PA d σ, Pf d σ)) op) (hrange : ∀ d σ, Com d σ < n)
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
    (E : Nat → Nat → Pa × Option Pp × TViewN PV PB → Bool) :
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (PA (main t r) σ, (ov (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)).map (fun _ => Pf (main t r) σ),
          rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
            r t)))))) ≤
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sd (sop r t)) σ) H c) (Com (sd (sop r t)) σ)
        (PA (sd (sop r t)) σ, some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ n * (NS * (e1 + e2)) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sd (sop r t)) σ) H c) (Com (sd (sop r t)) σ)
        (PA (sd (sop r t)) σ, some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (PA (main t r) σ, (ov (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
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
  have core : ∀ F : Nat → Nat → Pa × Option Pp × TViewN PV PB → Bool,
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
          (PA (main t r) σ, (ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf (main t r) σ),
            rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) ≤
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (sd (sop r t)) σ)
          (PA (sd (sop r t)) σ, some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) + NS * (e1 + e2) ∧
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (sd (sop r t)) σ)
          (PA (sd (sop r t)) σ, some (Pf (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) ≤
      sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ)
          (PA (main t r) σ, (ov (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf (main t r) σ),
            rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) + NS * (e1 + e2) := by
    intro F
    rw [open_real_tQ Com PA Pf op sd d0 ov main rv hsd hcom hpf hovn hrvo F,
      open_sim_tQ Com PA Pf sd d0 ov sop sv hsvo F, ← sumTo_const (e1 + e2) NS, ← sumTo_add, ← sumTo_add]
    exact ⟨sumTo_mono _ (fun σ _ => (tsumN_ab rv sv hrv hsv h1' h2' _).1),
      sumTo_mono _ (fun σ _ => (tsumN_ab rv sv hrv hsv h1' h2' _).2)⟩
  refine ⟨fs_zk (X := Nat × Nat × (Nat → Tup)) (K := Q4 * Q4) (n := n) (ε := NS * (e1 + e2))
    (Nat.mul_pos Q4_pos Q4_pos) (fun g => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ, r, t))))) hsm
    (fun x => Com (main x.2.2 x.2.1) x.1) (fun x => Com (sd (sop x.2.1 x.2.2)) x.1) (fun x => hrange _ _)
    (fun c x => (PA (main x.2.2 x.2.1) x.1, (ov (rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2)).map (fun _ => Pf (main x.2.2 x.2.1) x.1),
      rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c x => (PA (sd (sop x.2.1 x.2.2)) x.1, some (Pf (sd (sop x.2.1 x.2.2)) x.1), sv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c => genB (efOf (c % Q4))) (fun F => (core F).1) (fun H mm _ w => E H mm w),
    fs_zk' (X := Nat × Nat × (Nat → Tup)) (K := Q4 * Q4) (n := n) (ε := NS * (e1 + e2))
    (Nat.mul_pos Q4_pos Q4_pos) (fun g => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ, r, t))))) hsm
    (fun x => Com (main x.2.2 x.2.1) x.1) (fun x => Com (sd (sop x.2.1 x.2.2)) x.1) (fun x => hrange _ _)
    (fun c x => (PA (main x.2.2 x.2.1) x.1, (ov (rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2)).map (fun _ => Pf (main x.2.2 x.2.1) x.1),
      rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c x => (PA (sd (sop x.2.1 x.2.2)) x.1, some (Pf (sd (sop x.2.1 x.2.2)) x.1), sv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2))
    (fun c => genB (efOf (c % Q4))) (fun F => (core F).2) (fun H mm _ w => E H mm w)⟩

theorem runQ_length {K : Nat} (nxt : Nat → List Nat → Nat) (c H : Nat) : ∀ k, (runQ K nxt c k H).length = k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (runQ_length nxt c H k)

/-- The queries: the first `k0` chosen from the commitment alone, the rest
    reading the opening `p`. -/
def nxtC (k0 : Nat) {P : Type} (nxt0 : Nat → List Nat → Nat) (nxtF : P → Nat → List Nat → Nat) (p : P)
    (c : Nat) (l : List Nat) : Nat :=
  if l.length < k0 then nxt0 c l else nxtF p c l

theorem runQ_pre {K k0 : Nat} {P : Type} (nxt0 : Nat → List Nat → Nat) (nxtF : P → Nat → List Nat → Nat) (p : P)
    (c H : Nat) : ∀ i, i ≤ k0 → runQ K (nxtC k0 nxt0 nxtF p) c i H = runQ K nxt0 c i H
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := runQ_pre (K := K) nxt0 nxtF p c H i (Nat.le_of_succ_le hi)
    show rget K (nxtC k0 nxt0 nxtF p c (runQ K (nxtC k0 nxt0 nxtF p) c i H)) H :: runQ K (nxtC k0 nxt0 nxtF p) c i H =
      rget K (nxt0 c (runQ K nxt0 c i H)) H :: runQ K nxt0 c i H
    have hl : (runQ K (nxtC k0 nxt0 nxtF p) c i H).length < k0 := by rw [runQ_length]; exact hi
    rw [show nxtC k0 nxt0 nxtF p c (runQ K (nxtC k0 nxt0 nxtF p) c i H) = nxt0 c (runQ K (nxtC k0 nxt0 nxtF p) c i H)
      from if_pos hl, ih]

/-- **The answers to the commitment-only queries are the run's oldest
    `k0`.** -/
theorem runQ_split {K k0 : Nat} {P : Type} (nxt0 : Nat → List Nat → Nat) (nxtF : P → Nat → List Nat → Nat) (p : P)
    (c H : Nat) : ∀ k, (runQ K (nxtC k0 nxt0 nxtF p) c (k0 + k) H).drop k = runQ K nxt0 c k0 H
  | 0 => by rw [Nat.add_zero, List.drop_zero]; exact runQ_pre (K := K) nxt0 nxtF p c H k0 (Nat.le_refl _)
  | k + 1 => by
    show (_ :: runQ K (nxtC k0 nxt0 nxtF p) c (k0 + k) H).drop (k + 1) = _
    rw [List.drop_succ_cons]; exact runQ_split (K := K) nxt0 nxtF p c H k

/-- The tuples' count, a count of the other draws. -/
def smRT (NR m : Nat) (f : Nat × (Nat → Tup) → Nat) : Nat := sumTo NR (fun r => sumN m (fun t => f (r, t)))

theorem smRT_lin (NR m : Nat) : Lin (smRT NR m) := fun N f => by
  unfold smRT
  rw [show (fun r => sumN m (fun t => sumTo N (fun i => f i (r, t)))) =
    (fun r => sumTo N (fun i => sumN m (fun t => f i (r, t)))) from funext fun r => (sumTo_sumN m N (fun i t => f i (r, t))).symm]
  exact sumTo_exch _ N NR

theorem smRT_one (NR m : Nat) : smRT NR m (fun _ => 1) = NR * (Q4 ^ m * 1) := by
  show sumTo NR (fun _ => sumN m (fun _ => 1)) = _
  rw [sumN_const, sumTo_const]

/-- **One Fiat–Shamir round, the commitment drawn from the oracle, with
    query answers shown even where the proof aborts**: the distinguisher's
    first `k0` queries chosen from the commitment alone, answered always
    (`PA`), the next `k` reading the opening, answered with it; `K` times
    the real count is at most the simulator's (through the ideal opening)
    plus `fs_openQ`'s error and the transfer's `s (k0 + k) / NSh` a draw;
    one direction.  A strategy that queries differently on abort is covered
    with `nxt0` its abort strategy, `nxtF` the other, `k0 = k`, at twice the
    transfer term; no query reads the Fiat–Shamir table or the view
    (`ROMHide`'s limit); the simulator commits through the ideal opening. -/
theorem fs_openROMQ {PV PB D O P : Type} {NR m e1 e2 K n NSh NSo s k0 k : Nat} (hK : 0 < K)
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (g : O → Nat → P)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxt0 : Nat → List Nat → Nat) (nxtF : P → Nat → List Nat → Nat)
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
    (E : Nat → Nat → List Nat × Option (P × List Nat) × TViewN PV PB → Bool) :
    let Pf := pfR K NSh NSo (k0 + k) pos op g (nxtC k0 nxt0 nxtF)
    let PA := fun (d : D) (σ : Nat) => (Pf d σ).2.drop k
    let Pfi := pfI K NSh NSo (k0 + k) pos op g (nxtC k0 nxt0 nxtF)
    let PAi := fun (d : D) (σ : Nat) => (Pfi d σ).2.drop k
    K * ((Q4 * Q4) * sumTo ((Q4 * Q4) ^ K) (fun H => sumTo (NSh * (NSo * K ^ n)) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H % Q4)) && E H (comR K NSh NSo pos (main t r) σ)
        (PA (main t r) σ, (ov (rv (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H / Q4))
          (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          rv (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H / Q4))
            (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main t r) σ) H % Q4)) r t))))))) ≤
    sumTo ((Q4 * Q4) ^ K) (fun H => sumTo (Q4 * Q4) (fun c => sumTo (NSh * (NSo * K ^ n) * K) (fun σ =>
      sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (comI K NSh NSo pos (sd (sop r t)) σ) H c)
        (comI K NSh NSo pos (sd (sop r t)) σ)
        (PAi (sd (sop r t)) σ, some (Pfi (sd (sop r t)) σ), sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
      (Q4 * Q4) ^ K * (NSh * (NSo * K ^ n) * K * (e1 + e2)) +
      (Q4 * Q4) * ((Q4 * Q4) ^ K * (K * (NSo * (K ^ n * (s * (k0 + k)))) * (NR * (Q4 ^ m * 1)))) := by
  intro Pf PA Pfi PAi
  -- the ideal pair hides: the commitment-only answers with the commitment, and both given the openings
  have hsplit : ∀ d σ, PAi d σ = (pfI K NSh NSo k0 pos (fun _ => ()) (fun _ _ => ()) (fun _ => nxt0) d σ).2 :=
    fun d σ => runQ_split (K := K) nxt0 nxtF _ _ _ k
  have hcom : ∀ (d d' : D) (F : Nat → List Nat → Bool), sumTo (NSh * (NSo * K ^ n) * K) (fun σ =>
      indB (F (comI K NSh NSo pos d σ) (PAi d σ))) = sumTo (NSh * (NSo * K ^ n) * K) (fun σ =>
      indB (F (comI K NSh NSo pos d' σ) (PAi d' σ))) := fun d d' F => by
    simp only [hsplit]
    exact pfI_hides hK pos hpos (fun _ => ()) (fun _ _ => ()) (fun _ => nxt0) d d' rfl (fun c pf => F c pf.2)
  have hpf : ComPfHides (NSh * (NSo * K ^ n) * K) (comI K NSh NSo pos) (fun d σ => (PAi d σ, Pfi d σ)) op :=
    fun d d' hop F => pfI_hides hK pos hpos op g (nxtC k0 nxt0 nxtF) d d' hop (fun c pf => F c (pf.2.drop k, pf))
  have fo := (fs_openQ (n := K) (comI K NSh NSo pos) PAi Pfi op sd d0 hcom hpf (fun _ _ => Nat.mod_lt _ hK) ov hovn main
    hsd sop h1 h2 hrv hsv hrvo hsvo E).1
  -- the transfer, at each table, inside the tuples' count
  have hso := smRT_lin NR m
  have step : ∀ H, K * sumTo (NSh * (NSo * K ^ n)) (fun σ => smRT NR m (fun y =>
      indB (genB (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H % Q4)) &&
        E H (comR K NSh NSo pos (main y.2 y.1) σ)
          ((Pf (main y.2 y.1) σ).2.drop k, (ov (rv (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H / Q4))
          (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H % Q4)) y.1 y.2)).map (fun _ => Pf (main y.2 y.1) σ),
          rv (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H / Q4))
            (efOf (rget (Q4 * Q4) (comR K NSh NSo pos (main y.2 y.1) σ) H % Q4)) y.1 y.2)))) ≤
      sumTo (NSh * (NSo * K ^ n) * K) (fun σ => smRT NR m (fun y =>
      indB (genB (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H % Q4)) &&
        E H (comI K NSh NSo pos (main y.2 y.1) σ)
          ((Pfi (main y.2 y.1) σ).2.drop k, (ov (rv (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H / Q4))
          (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H % Q4)) y.1 y.2)).map (fun _ => Pfi (main y.2 y.1) σ),
          rv (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H / Q4))
            (efOf (rget (Q4 * Q4) (comI K NSh NSo pos (main y.2 y.1) σ) H % Q4)) y.1 y.2)))) +
      K * (NSo * (K ^ n * (s * (k0 + k)))) * (NR * (Q4 ^ m * 1)) := fun H => by
    have tr := (transferR_in (n := n) (NSh := NSh) (NSo := NSo) (s := s) (k := k0 + k) hK (smRT NR m) hso pos hpos op g hs
      (nxtC k0 nxt0 nxtF) (fun y => main y.2 y.1)
      (fun y c pf => genB (efOf (rget (Q4 * Q4) c H % Q4)) && E H c (pf.2.drop k,
        (ov (rv (efOf (rget (Q4 * Q4) c H / Q4)) (efOf (rget (Q4 * Q4) c H % Q4)) y.1 y.2)).map (fun _ => pf),
        rv (efOf (rget (Q4 * Q4) c H / Q4)) (efOf (rget (Q4 * Q4) c H % Q4)) y.1 y.2))).1
    rw [hso, hso, smRT_one] at tr
    exact tr
  rw [Nat.mul_left_comm K (Q4 * Q4), sumTo_mul]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => step H))) ?_
  rw [sumTo_add, sumTo_const, Nat.mul_add]
  exact Nat.add_le_add_right fo _

/-- A commitment hides jointly with a part shown always. -/
def ComHidesP {D Pa : Type} (NS : Nat) (Com : D → Nat → Nat) (PA : D → Nat → Pa) : Prop :=
  ∀ (d d' : D) (E : Nat → Pa → Bool), sumTo NS (fun σ => indB (E (Com d σ) (PA d σ))) =
    sumTo NS (fun σ => indB (E (Com d' σ) (PA d' σ)))

/-- `openEvQ` with the shown part and the opening paired. -/
def openEvP {PV PB D O Pa Pp : Type} (Com : D → Nat → Nat) (PA : D → Nat → Pa) (Pf : D → Nat → Pp) (sd : O → D)
    (d0 : D) (ov : TViewN PV PB → Option O) (F : Nat → Pa × Option Pp → TViewN PV PB → Bool) (σ : Nat)
    (v : TViewN PV PB) : Bool :=
  openEvQ Com PA Pf sd d0 ov (fun mm a p w => F mm (a, p) w) σ v

/-- **`open_real` with the event reading the draw.** -/
theorem open_real2Q {PV PB D O Pa Pp : Type} {NS NR m : Nat} (Com : D → Nat → Nat) (PA : D → Nat → Pa) (Pf : D → Nat → Pp) (op : D → O)
    (sd : O → D) (d0 : D) (hcom : ComHidesP NS Com PA) (hpf : ComPfHides NS Com (fun d σ => (PA d σ, Pf d σ)) op)
    (ov : TViewN PV PB → Option O) (hovn : ov none = none) (main : (Nat → Tup) → Nat → D)
    (hsd : ∀ t r, op (sd (op (main t r))) = op (main t r))
    (v : Nat → (Nat → Tup) → TViewN PV PB) (hvo : ∀ r t, v r t = none ∨ ov (v r t) = some (op (main t r)))
    (F : Nat → (Nat → Tup) → Nat → Pa × Option Pp → TViewN PV PB → Bool) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (F r t (Com (main t r) σ) (PA (main t r) σ, (ov (v r t)).map (fun _ => Pf (main t r) σ)) (v r t))))) =
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (openEvP Com PA Pf sd d0 ov (F r t) σ (v r t))))) := by
  have key : ∀ r t, sumTo NS (fun σ => indB (F r t (Com (main t r) σ) (PA (main t r) σ, (ov (v r t)).map (fun _ => Pf (main t r) σ))
      (v r t))) = sumTo NS (fun σ => indB (openEvP Com PA Pf sd d0 ov (F r t) σ (v r t))) := by
    intro r t
    rcases hvo r t with e | e
    · rw [e]
      unfold openEvP openEvQ
      rw [hovn]
      exact hcom (main t r) d0 (fun mm a => F r t mm (a, none) none)
    · unfold openEvP openEvQ
      rw [e]
      exact hpf (main t r) (sd (op (main t r))) (hsd t r).symm (fun mm p => F r t mm (p.1, some p.2) (v r t))
  rw [sig_in, sig_in]
  exact sumTo_congr _ (fun r _ => Nat.le_antisymm (sumN_mono m (fun t => Nat.le_of_eq (key r t)))
    (sumN_mono m (fun t => Nat.le_of_eq (key r t).symm)))

/-- The view event two salts give: each commitment and opening of the data
    the view's openings fix, or of fixed data where it shows nothing. -/
def openEv2Q {PV PB D1 O1 Pa1 P1 D2 O2 Pa2 P2 : Type} (Com1 : D1 → Nat → Nat) (PA1 : D1 → Nat → Pa1) (Pf1 : D1 → Nat → P1) (sd1 : O1 → D1)
    (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (PA2 : D2 → Nat → Pa2) (Pf2 : D2 → Nat → P2) (sd2 : O2 → D2)
    (d2 : D2) (ov2 : TViewN PV PB → Option O2)
    (F : Nat → Nat → Pa1 × Option P1 → Pa2 × Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) : Bool :=
  openEvP Com1 PA1 Pf1 sd1 d1 ov1 (fun mm1 p1 w => openEvP Com2 PA2 Pf2 sd2 d2 ov2 (fun mm2 p2 w' => F mm1 mm2 p1 p2 w') σ2 w)
    σ1 v

theorem openEv2_andQ {PV PB D1 O1 Pa1 P1 D2 O2 Pa2 P2 : Type} (Com1 : D1 → Nat → Nat) (PA1 : D1 → Nat → Pa1) (Pf1 : D1 → Nat → P1) (sd1 : O1 → D1)
    (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (PA2 : D2 → Nat → Pa2) (Pf2 : D2 → Nat → P2) (sd2 : O2 → D2)
    (d2 : D2) (ov2 : TViewN PV PB → Option O2) (b : Bool)
    (F : Nat → Nat → Pa1 × Option P1 → Pa2 × Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) :
    openEv2Q Com1 PA1 Pf1 sd1 d1 ov1 Com2 PA2 Pf2 sd2 d2 ov2 (fun a b' p q w => b && F a b' p q w) σ1 σ2 v =
      (b && openEv2Q Com1 PA1 Pf1 sd1 d1 ov1 Com2 PA2 Pf2 sd2 d2 ov2 F σ1 σ2 v) := by
  unfold openEv2Q openEvP openEvQ
  split <;> (dsimp only; split <;> rfl)

theorem openEv2_someQ {PV PB D1 O1 Pa1 P1 D2 O2 Pa2 P2 : Type} (Com1 : D1 → Nat → Nat) (PA1 : D1 → Nat → Pa1) (Pf1 : D1 → Nat → P1) (sd1 : O1 → D1)
    (d1 : D1) (ov1 : TViewN PV PB → Option O1) (Com2 : D2 → Nat → Nat) (PA2 : D2 → Nat → Pa2) (Pf2 : D2 → Nat → P2) (sd2 : O2 → D2)
    (d2 : D2) (ov2 : TViewN PV PB → Option O2)
    (F : Nat → Nat → Pa1 × Option P1 → Pa2 × Option P2 → TViewN PV PB → Bool) (σ1 σ2 : Nat) (v : TViewN PV PB) (o1 : O1)
    (o2 : O2) (h1 : ov1 v = some o1) (h2 : ov2 v = some o2) :
    openEv2Q Com1 PA1 Pf1 sd1 d1 ov1 Com2 PA2 Pf2 sd2 d2 ov2 F σ1 σ2 v =
      F (Com1 (sd1 o1) σ1) (Com2 (sd2 o2) σ2) (PA1 (sd1 o1) σ1, some (Pf1 (sd1 o1) σ1)) (PA2 (sd2 o2) σ2, some (Pf2 (sd2 o2) σ2)) v := by
  unfold openEv2Q openEvP openEvQ; rw [h1]; dsimp only; rw [h2]

/-- **Two opened commitments beside a transcript**, at one second
    challenge: the real count, both commitments and their openings shown,
    is within `NS1 · NS2 · (e1 + e2)` of the simulator's, which commits
    and opens data through its own view's openings. -/
theorem open_two_coreQ {PV PB D1 O1 Pa1 P1 D2 O2 Pa2 P2 : Type} {NR m e1 e2 NS1 NS2 : Nat}
    (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (PA1 : D1 → Nat → Pa1) (Pf1 : D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHidesP NS1 Com1 PA1) (hp1 : ComPfHides NS1 Com1 (fun d σ => (PA1 d σ, Pf1 d σ)) op1) (ov1 : TViewN PV PB → Option O1)
    (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (PA2 : D2 → Nat → Pa2) (Pf2 : D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHidesP NS2 Com2 PA2) (hp2 : ComPfHides NS2 Com2 (fun d σ => (PA2 d σ, Pf2 d σ)) op2) (ov2 : TViewN PV PB → Option O2)
    (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (hvo1 : ∀ c r t, rv (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 (main1 t r)))
    (hvo2 : ∀ c r t, rv (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r)))
    (sop1 : Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → (Nat → Tup) → O2)
    (hsvo1 : ∀ c r t, ov1 (sv (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 r t))
    (hsvo2 : ∀ c r t, ov2 (sv (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c r t))
    (F : Nat → Nat → Nat → Pa1 × Option P1 → Pa2 × Option P2 → TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) (Com2 (main2 c t r) σ2)
        (PA1 (main1 t r) σ1, (ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf1 (main1 t r) σ1))
        (PA2 (main2 c t r) σ2, (ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf2 (main2 c t r) σ2))
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    sumTo (Q4 * Q4) (fun c => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (sd1 (sop1 r t)) σ1) (Com2 (sd2 (sop2 c r t)) σ2)
        (PA1 (sd1 (sop1 r t)) σ1, some (Pf1 (sd1 (sop1 r t)) σ1)) (PA2 (sd2 (sop2 c r t)) σ2, some (Pf2 (sd2 (sop2 c r t)) σ2))
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) + NS1 * (NS2 * (e1 + e2)) := by
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  let G : Nat → Nat → Nat → TViewN PV PB → Bool := fun σ1 σ2 c w =>
    openEv2Q Com1 PA1 Pf1 sd1 d1 ov1 Com2 PA2 Pf2 sd2 d2 ov2 (F c) σ1 σ2 w
  -- the real side: both commitments swapped, a view event per pair of salts
  have hreal : ∀ c, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) (Com2 (main2 c t r) σ2)
        (PA1 (main1 t r) σ1, (ov1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf1 (main1 t r) σ1))
        (PA2 (main2 c t r) σ2, (ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)).map (fun _ => Pf2 (main2 c t r) σ2))
        (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) := fun c => by
    rw [sumTo_congr _ (fun σ1 _ => open_real2Q Com2 PA2 Pf2 op2 sd2 d2 hc2 hp2 ov2 hov2 (main2 c) (hsd2 c)
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo2 c r t)
      (fun r t mm2 p2 w => genB (efOf (c % Q4)) && F c (Com1 (main1 t r) σ1) mm2
        (PA1 (main1 t r) σ1, (ov1 w).map (fun _ => Pf1 (main1 t r) σ1)) p2 w))]
    rw [sumTo_exch _ NS2 NS1]
    refine sumTo_congr _ (fun σ2 _ => ?_)
    have e := open_real2Q (NR := NR) (m := m) Com1 PA1 Pf1 op1 sd1 d1 hc1 hp1 ov1 hov1 main1 hsd1
      (fun r t => rv (efOf (c / Q4)) (efOf (c % Q4)) r t) (fun r t => hvo1 c r t)
      (fun _ _ mm1 p1 w => openEvP Com2 PA2 Pf2 sd2 d2 ov2 (fun mm2 p2 w' => genB (efOf (c % Q4)) && F c mm1 mm2 p1 p2 w')
        σ2 w)
    refine Eq.trans ?_ (e.trans ?_)
    · refine sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
        (sumN_mono m (fun t => Nat.le_of_eq ?_)) (sumN_mono m (fun t => Nat.le_of_eq ?_))))
      all_goals (unfold openEvP openEvQ; cases ov2 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t) <;> rfl)
    · have eq : ∀ σ1 r t, indB (openEvP Com1 PA1 Pf1 sd1 d1 ov1 (fun mm1 p1 w =>
            openEvP Com2 PA2 Pf2 sd2 d2 ov2 (fun mm2 p2 w' => genB (efOf (c % Q4)) && F c mm1 mm2 p1 p2 w') σ2 w)
            σ1 (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)) =
          indB (genB (efOf (c % Q4)) && G σ1 σ2 c (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)) := fun σ1 r t => by
        show indB (openEv2Q Com1 PA1 Pf1 sd1 d1 ov1 Com2 PA2 Pf2 sd2 d2 ov2
          (fun a b' p q w => genB (efOf (c % Q4)) && F c a b' p q w) σ1 σ2 _) = _
        rw [openEv2_andQ]
      refine sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
        (sumN_mono m (fun t => Nat.le_of_eq (eq σ1 r t))) (sumN_mono m (fun t => Nat.le_of_eq (eq σ1 r t).symm))))
  -- the simulated side: its commitments are the view event's
  have hsim : ∀ c, sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com1 (sd1 (sop1 r t)) σ1) (Com2 (sd2 (sop2 c r t)) σ2)
        (PA1 (sd1 (sop1 r t)) σ1, some (Pf1 (sd1 (sop1 r t)) σ1)) (PA2 (sd2 (sop2 c r t)) σ2, some (Pf2 (sd2 (sop2 c r t)) σ2))
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) := fun c => by
    rw [sumTo_exch _ NS2 NS1]
    refine sumTo_congr _ (fun σ2 _ => sumTo_congr _ (fun σ1 _ => sumTo_congr _ (fun r _ => Nat.le_antisymm
      (sumN_mono m (fun t => Nat.le_of_eq ?_)) (sumN_mono m (fun t => Nat.le_of_eq ?_)))))
    · show _ = indB (genB (efOf (c % Q4)) && openEv2Q Com1 PA1 Pf1 sd1 d1 ov1 Com2 PA2 Pf2 sd2 d2 ov2 (F c) σ1 σ2 _)
      rw [openEv2_someQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hsvo1 c r t) (hsvo2 c r t)]
    · show indB (genB (efOf (c % Q4)) && openEv2Q Com1 PA1 Pf1 sd1 d1 ov1 Com2 PA2 Pf2 sd2 d2 ov2 (F c) σ1 σ2 _) = _
      rw [openEv2_someQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hsvo1 c r t) (hsvo2 c r t)]
  have ex : ∀ (v : EF → EF → Nat → (Nat → Tup) → TViewN PV PB),
      sumTo (Q4 * Q4) (fun c => sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => sumTo NR (fun r => sumN m (fun t =>
        indB (genB (efOf (c % Q4)) && G σ1 σ2 c (v (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) =
      sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && G σ1 σ2 (efIdx β + Q4 * efIdx α) (v α β r t))))) := fun v => by
    rw [sumTo_exch _ NS2 (Q4 * Q4)]
    refine sumTo_congr _ (fun σ2 _ => ?_)
    rw [sumTo_exch _ NS1 (Q4 * Q4)]
    exact sumTo_congr _ (fun σ1 _ => csum_tsumN v (fun c w => G σ1 σ2 c w))
  rw [sumTo_congr _ (fun c _ => hreal c), sumTo_congr _ (fun c _ => hsim c), ex rv, ex sv]
  calc sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && G σ1 σ2 (efIdx β + Q4 * efIdx α) (rv α β r t)))))
      ≤ sumTo NS2 (fun σ2 => sumTo NS1 (fun σ1 => tsumN NR m (fun α β r t =>
        indB (genB β && G σ1 σ2 (efIdx β + Q4 * efIdx α) (sv α β r t))) + (e1 + e2))) :=
        sumTo_mono _ (fun σ2 _ => sumTo_mono _ (fun σ1 _ => (tsumN_ab rv sv hrv hsv h1' h2' _).1))
    _ = _ := by
      simp only [sumTo_add, sumTo_const, Nat.mul_add]
      ac_rfl

set_option maxRecDepth 100000 in
/-- **`fs_open2` with a part of each commitment shown even where the proof
    aborts** (`PA1`, `PA2`, hiding jointly with their commitments,
    `ComHidesP`, and with the openings, `ComPfHides` of pairs).  `fs_open2`'s
    statement:

    **Fiat–Shamir over two rounds, both commitments opened**, in the
    programmable random-oracle model: the real proof's first message
    `Com1 (main1 t r) σ1`, its LogUp challenges `c1 = H1` there, its second
    message the pair with `Com2 (main2 c1 t r) σ2`, `c2 = H2` there, and
    its output the openings where it does not abort and the view at
    `c2`'s transcript; the simulator commits and opens data through its
    own view's openings, draws both challenges and programs both tables.
    Where the transcript bound holds at each guarded `c2`, `Q4² K2` times
    the real count is within `(Q4²)^n1 K2^(n1 n2) K2 NS1 NS2 (e1 + e2)` of
    the simulator's. -/
theorem fs_open2Q {PV PB D1 O1 Pa1 P1 D2 O2 Pa2 P2 : Type} {NR m e1 e2 NS1 NS2 K2 n1 n2 : Nat} (hK2 : 0 < K2)
    (rv sv : Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Bool)
    (hrv : ∀ c2 α β r t, rv c2 α β r t = none ∨ ∃ p x y, rv c2 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 α β r t, ∃ p x y, sv c2 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) + e1 + e2)
    (h2 : ∀ c2, gz c2 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (PA1 : D1 → Nat → Pa1) (Pf1 : D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHidesP NS1 Com1 PA1) (hp1 : ComPfHides NS1 Com1 (fun d σ => (PA1 d σ, Pf1 d σ)) op1) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : TViewN PV PB → Option O1) (hov1 : ov1 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ t r, op1 (sd1 (op1 (main1 t r))) = op1 (main1 t r))
    (Com2 : D2 → Nat → Nat) (PA2 : D2 → Nat → Pa2) (Pf2 : D2 → Nat → P2) (op2 : D2 → O2) (sd2 : O2 → D2) (d2 : D2)
    (hc2 : ComHidesP NS2 Com2 PA2) (hp2 : ComPfHides NS2 Com2 (fun d σ => (PA2 d σ, Pf2 d σ)) op2) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : TViewN PV PB → Option O2) (hov2 : ov2 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c t r, op2 (sd2 (op2 (main2 c t r))) = op2 (main2 c t r))
    (hvo1 : ∀ c2 c r t, rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 (rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 (main1 t r)))
    (hvo2 : ∀ c2 c r t, rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 (rv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 (main2 c t r)))
    (sop1 : Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → (Nat → Tup) → O2)
    (hsvo1 : ∀ c2 c r t, ov1 (sv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c2 r t))
    (hsvo2 : ∀ c2 c r t, ov2 (sv c2 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c2 c r t))
    (E : Nat → Nat → Nat → Nat → Pa1 × Option P1 × Pa2 × Option P2 × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t => g (σ1, σ2, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      Com1 (main1 x.2.2.2 x.2.2.1) x.1 + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (PA1 (main1 x.2.2.2 x.2.2.1) x.1, (ov1 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
       PA2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1, (ov2 (rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => Pf2 (main2 c1 x.2.2.2 x.2.2.1) x.2.1),
       rv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c1 c2 x + n1 * Com2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (PA1 (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1, some (Pf1 (sd1 (sop1 c2 x.2.2.1 x.2.2.2)) x.1), PA2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1, some (Pf2 (sd2 (sop2 c2 c1 x.2.2.1 x.2.2.2)) x.2.1),
        sv c2 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 : Nat) => genB (efOf (c1 % Q4)) && gz c2
    (Q4 * Q4) * (K2 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sm (fun x =>
      indB (gd (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) &&
        E H1 H2 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 =>
      sm (fun x => indB (gd c1 c2 && E (rset (Q4 * Q4) (s1 c1 c2 x) H1 c1) (rset K2 (s2 c1 c2 x) H2 c2)
        (s1 c1 c2 x) (s2 c1 c2 x) (svo c1 c2 x))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K2 * (NS1 * (NS2 * (e1 + e2))))) := by
  intro sm m1 m2 rvo s1 s2 svo gd
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ2, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2) (NR := NR) (m := m) (N := N)
      (fun i σ2 r t => f i (σ1, σ2, r, t)))]
    exact sumTo_exch _ N NS1
  refine fs_zk2 (K1 := Q4 * Q4) (K2 := K2) (n1 := n1) (n2 := n1 * n2) (Nat.mul_pos Q4_pos Q4_pos) hK2 sm hsm m1 m2
    (fun x => hr1 _ _) (fun _ x => pair_lt (hr1 _ _) (hr2 _ _)) s1 s2 rvo svo gd (fun F => ?_) E
  show sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo NS1 (fun σ1 => sumTo NS2 (fun σ2 => sumTo NR (fun r =>
    sumN m (fun t => _)))))) ≤ _
  rw [sumTo_exch _ K2 (Q4 * Q4), sumTo_exch _ K2 (Q4 * Q4), ← sumTo_const (NS1 * (NS2 * (e1 + e2))) K2, ← sumTo_add]
  refine sumTo_mono _ (fun c2 _ => ?_)
  cases hg : gz c2
  · simp only [gd, hg, Bool.and_false, Bool.false_and]
    exact Nat.le_add_right _ _
  · simp only [gd, hg, Bool.and_true]
    exact open_two_coreQ (rv c2) (sv c2) (hrv c2) (hsv c2) (h1 c2 hg) (h2 c2 hg) Com1 PA1 Pf1 op1 sd1 d1 hc1 hp1 ov1 hov1
      main1 hsd1 Com2 PA2 Pf2 op2 sd2 d2 hc2 hp2 ov2 hov2 main2 hsd2 (hvo1 c2) (hvo2 c2) (sop1 c2) (sop2 c2)
      (hsvo1 c2) (hsvo2 c2)
      (fun c1 a b p q w => F c1 c2 a (a + n1 * b) (p.1, p.2, q.1, q.2, w))


theorem ComHides_toP {D : Type} {NS : Nat} {Com : D → Nat → Nat} (h : ComHides NS Com) :
    ComHidesP NS Com (fun _ _ => ()) := fun d d' E => h d d' (fun c => E c ())

theorem ComPfHides_toP {D O Pp : Type} {NS : Nat} {Com : D → Nat → Nat} {Pf : D → Nat → Pp} {op : D → O}
    (h : ComPfHides NS Com Pf op) : ComPfHides NS Com (fun d σ => ((), Pf d σ)) op :=
  fun d d' hop E => h d d' hop (fun c p => E c ((), p))

set_option maxRecDepth 100000 in
/-- **`fs_open3` with a part of the first commitment shown even where the
    proof aborts** (`PA1`); the later commitments as `fs_open3`'s. -/
theorem fs_open3Q {PV PB D1 O1 Pa1 P1 D2 O2 P2 D3 O3 P3 : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 n1 n2 n3 : Nat}
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
    (Com1 : D1 → Nat → Nat) (PA1 : D1 → Nat → Pa1) (Pf1 : D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHidesP NS1 Com1 PA1) (hp1 : ComPfHides NS1 Com1 (fun d σ => (PA1 d σ, Pf1 d σ)) op1) (hr1 : ∀ d σ, Com1 d σ < n1)
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
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Pa1 × Option P1 × Option (P2 × P3) × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (PA1 (main1 x.2.2.2 x.2.2.1) x.1, (ov1 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
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
      (PA1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1, some (Pf1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
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
    have core := open_two_coreQ (NR := NR) (m := m) (rv c2 c3) (sv c2 c3) (hrv c2 c3) (hsv c2 c3) (h1 c2 c3 hg)
      (h2 c2 c3 hg) Com1 PA1 Pf1 op1 sd1 d1 hc1 hp1 ov1 hov1 main1 hsd1
      (comPair NS2 n2 Com2 Com3) (fun _ _ => ()) (pfPair NS2 Pf2 Pf3) (fun d => (op2 d.1, op3 d.2)) (fun o => (sd2 o.1, sd3 o.2))
      (d2, d3) (ComHides_toP (ComHides.prod hc2 hc3)) (ComPfHides_toP (ComPfHides.prod hp2 hp3)) (ovPair ov2 ov3) hov23
      (fun c t r => (main2 c t r, main3 c c2 t r))
      (fun c t r => by show (op2 (sd2 (op2 (main2 c t r))), op3 (sd3 (op3 (main3 c c2 t r)))) = _; rw [hsd2, hsd3])
      (hvo1 c2 c3) hvo23 (sop1 c2 c3) (fun c r t => (sop2 c2 c3 c r t, sop3 c2 c3 c r t)) (hsvo1 c2 c3) hsvo23
      (fun c a b p q w => F c c2 c3 a (a + n1 * (b % n2)) (a + n1 * b) (p.1, p.2, q.2, w))
    simp only [comPair_mod Com3 hr2] at core
    exact core

set_option maxRecDepth 100000 in
/-- **`fs_open3U` with a part of the first commitment shown even where the
    proof aborts** (`PA1`). -/
theorem fs_open3UQ {PV PB D1 O1 Pa1 P1 D2 O2 P2 D3 O3 P3 : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3)
    (rv sv : Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (hrv : ∀ c2 c3 α β r t, rv c2 c3 α β r t = none ∨ ∃ p x y, rv c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c2 c3 α β r t, ∃ p x y, sv c2 c3 α β r t = some (p, α, β, x, y))
    (h1 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c2 c3, gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c2 c3 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) (PA1 : D1 → Nat → Pa1) (Pf1 : D1 → Nat → P1) (op1 : D1 → O1) (sd1 : O1 → D1) (d1 : D1)
    (hc1 : ComHidesP NS1 Com1 PA1) (hp1 : ComPfHides NS1 Com1 (fun d σ => (PA1 d σ, Pf1 d σ)) op1) (hr1 : ∀ d σ, Com1 d σ < n1)
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
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Pa1 × Option P1 × Option (P2 × P3) × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (PA1 (main1 x.2.2.2 x.2.2.1) x.1, (ov1 (rv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 (main1 x.2.2.2 x.2.2.1) x.1),
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
      (PA1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1, some (Pf1 (sd1 (sop1 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 Pf2 Pf3 (sd2 (sop2 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 (sop3 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let gd := fun (c1 c2 c3 : Nat) => genB (efOf (c1 % Q4)) && gz c2 c3
    (Q4 * Q4) * (K2 * (K3 * sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x =>
      indB (E H1 H2 H3 (m1 x) (m2 (rget (Q4 * Q4) (m1 x) H1) x)
          (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x)
          (rvo (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2)
            (rget K3 (m3 (rget (Q4 * Q4) (m1 x) H1) (rget K2 (m2 (rget (Q4 * Q4) (m1 x) H1) x) H2) x) H3) x)))))))) ≤
    sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c1 c2 c3 x) H1 c1) (rset K2 (s2 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c1 c2 c3 x) H3 c3) (s1 c1 c2 c3 x) (s2 c1 c2 c3 x) (s3 c1 c2 c3 x) (svo c1 c2 c3 x))))))))) +
      (Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1))))))) := by
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
  refine Nat.le_trans (fs_zk3U (K1 := Q4 * Q4) (K2 := K2) (K3 := K3) (n1 := n1) (n2 := n1 * n2) (n3 := n1 * (n2 * n3))
    (ε := K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))))
    (Nat.mul_pos Q4_pos Q4_pos) hK2 hK3 sm hsm m1 m2 m3 (fun x => hr1 _ _) (fun _ x => pair_lt (hr1 _ _) (hr2 _ _))
    (fun _ _ x => pair_lt (hr1 _ _) (hc23 _ _)) s1 s2 s3 rvo svo gd (fun F => ?_) E) ?_
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
    have core := open_two_coreQ (NR := NR) (m := m) (rv c2 c3) (sv c2 c3) (hrv c2 c3) (hsv c2 c3) (h1 c2 c3 hg)
      (h2 c2 c3 hg) Com1 PA1 Pf1 op1 sd1 d1 hc1 hp1 ov1 hov1 main1 hsd1
      (comPair NS2 n2 Com2 Com3) (fun _ _ => ()) (pfPair NS2 Pf2 Pf3) (fun d => (op2 d.1, op3 d.2)) (fun o => (sd2 o.1, sd3 o.2))
      (d2, d3) (ComHides_toP (ComHides.prod hc2 hc3)) (ComPfHides_toP (ComPfHides.prod hp2 hp3)) (ovPair ov2 ov3) hov23
      (fun c t r => (main2 c t r, main3 c c2 t r))
      (fun c t r => by show (op2 (sd2 (op2 (main2 c t r))), op3 (sd3 (op3 (main3 c c2 t r)))) = _; rw [hsd2, hsd3])
      (hvo1 c2 c3) hvo23 (sop1 c2 c3) (fun c r t => (sop2 c2 c3 c r t, sop3 c2 c3 c r t)) (hsvo1 c2 c3) hsvo23
      (fun c a b p q w => F c c2 c3 a (a + n1 * (b % n2)) (a + n1 * b) (p.1, p.2, q.2, w))
    simp only [comPair_mod Com3 hr2] at core
    exact core
  · refine Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.add_le_add_left ?_ _)))) _
    have hk : ∀ k, sm (fun _ => k) = NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1))) * k := fun k => by
      simp only [sm, sumN_const, sumTo_const, Nat.mul_one, Nat.mul_assoc]
    show sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 =>
      sm (fun _ => indB (!(genB (efOf (c1 % Q4)) && gz c2 c3)))))) ≤ _
    simp only [hk, ← sumTo_mul]
    rw [Nat.mul_comm _ (NS1 * _)]
    exact Nat.mul_le_mul_left _ (bad3_count gz hgz)


set_option maxRecDepth 100000 in
/-- **`fs_open4` with a part of the first commitment shown even where the
    proof aborts** (`PA1 c4`, hiding with the commitment at each `c4`). -/
theorem fs_open4Q {PV PB D1 O1 Pa1 P1 D2 O2 P2 D3 O3 P3 W : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 K4 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
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
    (Com1 : D1 → Nat → Nat) (PA1 : Nat → D1 → Nat → Pa1) (Pf1 : Nat → D1 → Nat → P1) (op1 : Nat → D1 → O1) (sd1 : Nat → O1 → D1) (d1 : D1)
    (hc1 : ∀ c4, ComHidesP NS1 Com1 (PA1 c4)) (hp1 : ∀ c4, ComPfHides NS1 Com1 (fun d σ => (PA1 c4 d σ, Pf1 c4 d σ)) (op1 c4)) (hr1 : ∀ d σ, Com1 d σ < n1)
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
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Pa1 × Option P1 × Option (P2 × P3) × TViewN PV PB → Bool) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (PA1 c4 (main1 x.2.2.2 x.2.2.1) x.1, (ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (PA1 c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1, some (Pf1 c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
      indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
        (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2))))) ≤
    sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
          (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4 (fun _ => 1))) := by
  intro sm m1 m2 m3 rvo s1 s2 s3 svo sm4 r1 r2 r3 Mq
  have hsm : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat → Tup) → Nat),
      sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)) := fun N f => by
    show sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
      sumTo N (fun i => f i (σ1, σ, r, t)))))) = _
    rw [sumTo_congr _ (fun σ1 _ => sm_exch (NS := NS2 * NS3) (NR := NR) (m := m) (N := N)
      (fun i σ r t => f i (σ1, σ, r, t)))]
    exact sumTo_exch _ N NS1
  have hc23 : ∀ d σ, comPair NS2 n2 Com2 Com3 d σ < n2 * n3 := fun d σ => by
    unfold comPair; exact pair_lt (hr2 _ _) (hr3 _ _)
  have hsm4 : ∀ (N : Nat) (f : Nat → Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat),
      sm4 (fun y => sumTo N (fun i => f i y)) = sumTo N (fun i => sm4 (f i)) := fun N f => by
    show sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => sumTo N (fun i => f i (H1, H2, H3, x)))))) = _
    simp only [hsm N]
    rw [sumTo_congr _ (fun H1 _ => sumTo_congr _ (fun H2 _ => sumTo_exch _ N (K3 ^ (n1 * (n2 * n3)))))]
    rw [sumTo_congr _ (fun H1 _ => sumTo_exch _ N (K2 ^ (n1 * n2)))]
    exact sumTo_exch _ N ((Q4 * Q4) ^ n1)
  refine fs_lastG (K := Q4 * Q4 * (K2 * K3)) (n4 := N4) hK4 sm4 hsm4 Mq
    (fun y => hφ _ _)
    (fun c4 y => (y.1, y.2.1, y.2.2.1, m1 y.2.2.2, m2 (r1 y) y.2.2.2, m3 (r1 y) (r2 y) y.2.2.2, rvo c4 (r1 y) (r2 y) (r3 y) y.2.2.2))
    (fun c4 G => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3)))
      (fun H3 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => sm (fun x =>
        indB (G (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1, rset K2 (s2 c4 c1 c2 c3 x) H2 c2,
          rset K3 (s3 c4 c1 c2 c3 x) H3 c3, s1 c4 c1 c2 c3 x, s2 c4 c1 c2 c3 x, s3 c4 c1 c2 c3 x, svo c4 c1 c2 c3 x))))))))))
    g4 hB4 (fun c4 hg4 G => ?_) (fun H4 _ c4 v => E v.1 v.2.1 v.2.2.1 H4 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2.1 v.2.2.2.2.2.2)
  have h3 := fs_open3UQ hK2 hK3 (rv c4) (sv c4) gz hgz (hrv c4) (hsv c4) (fun c2 c3 hg => h1 c4 c2 c3 hg4 hg) (fun c2 c3 hg => h2 c4 c2 c3 hg4 hg)
    Com1 (PA1 c4) (Pf1 c4) (op1 c4) (sd1 c4) d1 (hc1 c4) (hp1 c4) hr1 (ov1 c4) (hov1 c4) main1 (hsd1 c4)
    Com2 (Pf2 c4) (op2 c4) (sd2 c4) d2 hc2 (hp2 c4) hr2 (ov2 c4) (hov2 c4) main2 (hsd2 c4)
    Com3 (Pf3 c4) (op3 c4) (sd3 c4) d3 hc3 (hp3 c4) hr3 (ov3 c4) (hov3 c4) main3 (hsd3 c4)
    (hvo1 c4) (hvo2 c4) (hvo3 c4) (sop1 c4) (sop2 c4) (sop3 c4) (hsvo1 c4) (hsvo2 c4) (hsvo3 c4)
    (fun H1 H2 H3 a b c v => G (φ c (oz v.2.2.2)) (H1, H2, H3, a, b, c, v))
  simp only [Mq, ← hoz c4]
  rw [Nat.mul_assoc, Nat.mul_assoc K2]
  exact h3

set_option maxRecDepth 100000 in
/-- **Four Fiat–Shamir rounds, the first commitment drawn from the oracle,
    with query answers shown where the proof aborts** (`fs_open4ROM` over
    `fs_open4Q`): the first `k0` queries chosen from the commitment alone,
    answered always; the rest read the opening at the drawn challenge.  The
    bound gains `s (k0 + k) / NSh` a draw; one direction.  As `fs_openROMQ`:
    no query reads the Fiat–Shamir tables or the view, and a strategy that
    queries differently on abort takes `k0 = k` at twice the transfer term. -/
theorem fs_open4ROMQ {PV PB D O Pq D2 O2 P2 D3 O3 P3 W : Type}
    {K NR m e1 e2 NSh NSo s k0 k n NS2 NS3 K2 K3 K4 n2 n3 : Nat}
    (hK : 0 < K) (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
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
    (pos : D → Nat → Nat → Nat) (hpos : ∀ d σo σh, pos d σo σh < n) (g : O → Nat → Pq)
    (hs : ∀ d σo v, sumTo NSh (fun σh => indB (decide (pos d σo σh = v))) ≤ s)
    (nxt0 : Nat → List Nat → Nat) (nxtF : Pq → Nat → List Nat → Nat) (op1 : Nat → D → O) (sd1 : Nat → O → D) (d1 : D)
    (ov1 : Nat → TViewN PV PB → Option O) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D)
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
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat × Option (Pq × List Nat) × Option (P2 × P3) × TViewN PV PB → Bool) :
    let Com1 := comR K NSh NSo pos
    let Pf1 := fun c4 => pfR K NSh NSo (k0 + k) pos (op1 c4) g (nxtC k0 nxt0 nxtF)
    let PA1 := fun (c4 : Nat) (d : D) (σ : Nat) => (Pf1 c4 d σ).2.drop k
    let Cmi := comI K NSh NSo pos
    let Pfi := fun c4 => pfI K NSh NSo (k0 + k) pos (op1 c4) g (nxtC k0 nxt0 nxtF)
    let PAi := fun (c4 : Nat) (d : D) (σ : Nat) => (Pfi c4 d σ).2.drop k
    let smR := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * K ^ n)) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ, r, t)))))
    let smI := fun (f : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSh * (NSo * K ^ n) * K) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t =>
        f (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + K * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + K * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (PA1 c4 (main1 x.2.2.2 x.2.2.1) x.1, (ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 _c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + K * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + K * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (PAi c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1, some (Pfi c4 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let sm4I := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => smI (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    K * (K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 => sm4 (fun y =>
      indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
        (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
    sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 => sumTo (K3 ^ (K * (n2 * n3))) (fun H3 =>
      sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo K3 (fun c3 => smI (fun x =>
        indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
          (rset K3 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (oz (sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
          (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K2 * (K3 * (NSh * (NSo * K ^ n) * K * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NSh * (NSo * K ^ n) * K * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4I (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * K3) * (K4 ^ N4 * ((Q4 * Q4) ^ K * (K2 ^ (K * n2) * (K3 ^ (K * (n2 * n3)) *
        (K * (NSo * (K ^ n * (s * (k0 + k)))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))))))))) := by
  intro Com1 Pf1 PA1 Cmi Pfi PAi smR smI m1 m2 m3 rvo s1 s2 s3 svo sm4 sm4I r1 r2 r3 Mq
  have hsplit : ∀ c4 d σ, PAi c4 d σ = (pfI K NSh NSo k0 pos (fun _ => ()) (fun _ _ => ()) (fun _ => nxt0) d σ).2 :=
    fun c4 d σ => runQ_split (K := K) nxt0 nxtF _ _ _ k
  have hc1 : ∀ c4, ComHidesP (NSh * (NSo * K ^ n) * K) Cmi (PAi c4) := fun c4 d d' F => by
    simp only [hsplit]
    exact pfI_hides hK pos hpos (fun _ => ()) (fun _ _ => ()) (fun _ => nxt0) d d' rfl (fun c pf => F c pf.2)
  have hp1 : ∀ c4, ComPfHides (NSh * (NSo * K ^ n) * K) Cmi (fun d σ => (PAi c4 d σ, Pfi c4 d σ)) (op1 c4) :=
    fun c4 d d' hop F => pfI_hides hK pos hpos (op1 c4) g (nxtC k0 nxt0 nxtF) d d' hop (fun c pf => F c (pf.2.drop k, pf))
  have fo := fs_open4Q (NS1 := NSh * (NSo * K ^ n) * K) (n1 := K) hK2 hK3 hK4 φ hφ rv sv gz hgz g4 hB4 hrv hsv oz hoz
    h1 h2 Cmi PAi Pfi op1 sd1 d1 hc1 hp1
    (fun _ _ => Nat.mod_lt _ hK) ov1 hov1 main1 hsd1
    Com2 Pf2 op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 Com3 Pf3 op3 sd3 d3 hc3 hp3 hr3 ov3 hov3 main3 hsd3
    hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 E
  -- the query challenge and the event, read off the first commitment's value `c`
  let c4f := fun (H1 H2 H3 H4 : Nat) (y : Nat × Nat × (Nat → Tup)) (c : Nat) =>
    let c1 := rget (Q4 * Q4) c H1
    let c2 := rget K2 (c + K * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)) H2
    let mm3 := c + K * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H3
    rget K4 (φ mm3 (oz (rv 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2))) H4
  let ev := fun (H1 H2 H3 H4 : Nat) (y : Nat × Nat × (Nat → Tup)) (c : Nat) (pf : Pq × List Nat) =>
    let c1 := rget (Q4 * Q4) c H1
    let mm2 := c + K * Com2 (main2 c1 y.2.2 y.2.1) (y.1 % NS2)
    let c2 := rget K2 mm2 H2
    let mm3 := c + K * comPair NS2 n2 Com2 Com3 (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1
    let c3 := rget K3 mm3 H3
    let c4 := c4f H1 H2 H3 H4 y c
    E H1 H2 H3 H4 c mm2 mm3
      (pf.2.drop k, (ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map (fun _ => pf),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 y.2.2 y.2.1, main3 c1 c2 y.2.2 y.2.1) y.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) y.2.1 y.2.2)
  have hso := smT_lin (NS2 * NS3) NR m
  have so1 := smT_one (NS2 * NS3) NR m
  have step : ∀ H4 H1 H2 H3,
      K * smR (fun x => indB (ev H1 H2 H3 H4 x.2 (Com1 (main1 x.2.2.2 x.2.2.1) x.1)
        (Pf1 (c4f H1 H2 H3 H4 x.2 (Com1 (main1 x.2.2.2 x.2.2.1) x.1)) (main1 x.2.2.2 x.2.2.1) x.1))) ≤
      smI (fun x => indB (ev H1 H2 H3 H4 x.2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)
        (Pfi (c4f H1 H2 H3 H4 x.2 (Cmi (main1 x.2.2.2 x.2.2.1) x.1)) (main1 x.2.2.2 x.2.2.1) x.1))) +
        K * (NSo * (K ^ n * (s * (k0 + k)))) * (NS2 * NS3 * (NR * (Q4 ^ m * 1))) := fun H4 H1 H2 H3 => by
    have tr := transferRc_in (n := n) (NSh := NSh) (NSo := NSo) (s := s) (k := k0 + k) hK (smT (NS2 * NS3) NR m) hso
      pos hpos op1 g hs (nxtC k0 nxt0 nxtF) (fun y => main1 y.2.2 y.2.1) (fun y c => c4f H1 H2 H3 H4 y c)
      (fun y c pf => ev H1 H2 H3 H4 y c pf)
    rw [hso, hso, so1] at tr
    exact tr
  have hb : ∀ X : Nat → Nat → Nat → Nat → Nat, K * (K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => X H4 H1 H2 H3)))))) =
      K4 * (Q4 * Q4 * (K2 * K3) * sumTo (K4 ^ N4) (fun H4 =>
      sumTo ((Q4 * Q4) ^ K) (fun H1 => sumTo (K2 ^ (K * n2)) (fun H2 =>
        sumTo (K3 ^ (K * (n2 * n3))) (fun H3 => K * X H4 H1 H2 H3))))) := fun X => by
    rw [Nat.mul_left_comm K K4, Nat.mul_left_comm K (Q4 * Q4 * (K2 * K3)), sumTo_mul]
    exact congrArg (fun z => K4 * (Q4 * Q4 * (K2 * K3) * z)) (sumTo_congr _ (fun H4 _ =>
      (sumTo_mul _ _ _).trans (sumTo_congr _ (fun H1 _ =>
        (sumTo_mul _ _ _).trans (sumTo_congr _ (fun H2 _ => sumTo_mul _ _ _))))))
  rw [hb]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (sumTo_mono _ (fun H4 _ => sumTo_mono _ (fun H1 _ => sumTo_mono _ (fun H2 _ =>
      sumTo_mono _ (fun H3 _ => step H4 H1 H2 H3))))))) ?_
  simp only [sumTo_add, sumTo_const]
  rw [Nat.mul_add (Q4 * Q4 * (K2 * K3)), Nat.mul_add K4]
  exact Nat.add_le_add_right fo _
end Circuit
