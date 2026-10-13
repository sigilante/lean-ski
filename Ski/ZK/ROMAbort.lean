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
round; the multi-round theorems with `PA` are not yet written.
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
end Circuit
