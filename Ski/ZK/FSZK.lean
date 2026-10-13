import Ski.ZK.Interleave
import Ski.ZK.MaskCom

/-!
# Fiat–Shamir keeps the simulation's error, in the programmable random-oracle model

A non-interactive proof draws its challenge by hashing the message before
it: `c = H(m)`.  Model the hash as a random oracle, a uniformly drawn
function from `n` inputs to `K` answers, encoded as one number `H < K^n`
whose base-`K` digit `m` is `H(m)` (`rget`).  The distinguisher sees the
whole table `H` with the proof, so it may query the oracle anywhere, as
often as it likes.

**Reprogramming keeps the oracle uniform** (`oracle_reprog`): drawing a
table and then setting its digit `m` to each answer `c` covers every
table `K` times.  **Fiat–Shamir keeps the simulation's error**
(`fs_zk`): when the public-coin view, the message `m` with it, has a
simulator, the real non-interactive view `(H, m, view at c = H(m))` and
the simulator's, which draws `c`, simulates, and programs `H(m) := c`,
count within the public-coin error times the `K^n` tables, the real count
taken `K` times (the simulator draws `c` beside `H`).

**Events may read the challenges** (`tsumN_ab`): each circuit's
transcript theorem bounds events on its view; the distinguisher here sees
the oracle table, so its event depends on the challenge even where the
real proof aborts and shows nothing.  Reading the challenges from the
view where it shows them and fixing the event elsewhere, `true` one way
and `false` the other, gives the same bound with the same error.

**A transcript under Fiat–Shamir** (`fs_transcript`, `fs_transcript'`):
the hashed message is the commitment `Com (main t r) σ` of the prover's
first message, any data it computes from the blinding tuples `t` and the
PCS randomness `r`, its salt `σ` drawn apart.  A hiding commitment
(`ComHides`, `com_swap`) makes it count as a fixed datum's, the challenge
index `c < Q4²` reads as the pair `(α, β)` (`sumQ2`, `csum_tsumN`), and
`fs_zk` does the rest.

Scope.  This is Fiat–Shamir for an idealized proof, and these are its
limits:
* **The commitment is never opened.**  The view does not depend on the
  salt or the committed data, so nothing in it is checked against the
  hashed `m`; the theorem holds even for a constant `main`.  In Plonky3
  the main root is opened at the query points, with leaves, salts and
  Merkle paths, and the simulator's commitment to `d0` would fail those
  checks.  A faithful version needs the simulator to commit its own
  masked data and hiding of the root given the opened positions.
* **`Com` is a primitive apart from the oracle.**  It hides perfectly over
  its salt and is not computed from `H`; in Plonky3 both are Poseidon2,
  and an adversary with the hash's whole table could test commitments,
  so a real instantiation needs bounded queries and a ROM-hiding term.
* **One proof per oracle.**  Programming several proofs into one table
  needs a hybrid argument and a collision term, not proved.
* **One round, and only generic `β`.**  The hashed challenges are the
  LogUp pair; `ζ`, the FRI challenge and the query points stay fixed.
  The count is the guarded joint count (`genB β`), as in the transcript
  theorems; a prover that resamples under a fixed table is not modeled.
* **The sponge is a random oracle**, its fixed public absorptions (the
  statement, the preprocessed commitment) folded into it, and the lookup
  proof-of-work nonce, a public function of `m` and `H`, is left out.
* The salts are drawn apart from the PCS randomness; Plonky3 draws both
  from one ChaCha20 seed, so this rests on the PRG assumption.
-/

namespace Circuit

open ZKF

/-- The oracle table `H`'s answer at `m`: its base-`K` digit. -/
def rget (K m H : Nat) : Nat := H / K ^ m % K

/-- The table `H` with its answer at `m` set to `c`. -/
def rset (K m H c : Nat) : Nat := H - rget K m H * K ^ m + c * K ^ m

theorem split_digit {K m : Nat} (hK : 0 < K) {lo d hi : Nat} (hlo : lo < K ^ m) (hd : d < K) :
    rget K m (lo + K ^ m * (d + K * hi)) = d ∧
      ∀ c, rset K m (lo + K ^ m * (d + K * hi)) c = lo + K ^ m * (c + K * hi) := by
  have hpos : 0 < K ^ m := Nat.pow_pos hK
  have hdiv : (lo + K ^ m * (d + K * hi)) / K ^ m = d + K * hi := by
    rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
  have hg : rget K m (lo + K ^ m * (d + K * hi)) = d := by
    unfold rget; rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  refine ⟨hg, fun c => ?_⟩
  unfold rset; rw [hg]
  have e1 : lo + K ^ m * (d + K * hi) = lo + K ^ m * (K * hi) + d * K ^ m := by
    rw [Nat.mul_add, Nat.mul_comm (K ^ m) d]; omega
  rw [e1, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_comm (K ^ m) c]; omega

theorem rget_rset {K m H c : Nat} (hK : 0 < K) (hc : c < K) : rget K m (rset K m H c) = c := by
  have hpos : 0 < K ^ m := Nat.pow_pos hK
  have h1 := Nat.mod_add_div H (K ^ m)
  have h2 := Nat.mod_add_div (H / K ^ m) K
  have hH : H = H % K ^ m + K ^ m * (H / K ^ m % K + K * (H / K ^ m / K)) := by rw [h2]; exact h1.symm
  obtain ⟨_, hs⟩ := split_digit (m := m) hK (Nat.mod_lt H hpos) (Nat.mod_lt (H / K ^ m) hK)
    (hi := H / K ^ m / K)
  rw [← hH] at hs
  rw [hs c]
  exact (split_digit hK (Nat.mod_lt H hpos) hc).1

/-- **Reprogramming keeps the oracle uniform**: over all `K^n` tables, the
    tables with the answer at `m < n` set to each of the `K` answers are
    every table `K` times. -/
theorem oracle_reprog {K n m : Nat} (hK : 0 < K) (hm : m < n) (g : Nat → Nat) :
    sumTo (K ^ n) (fun H => sumTo K (fun c => g (rset K m H c))) = K * sumTo (K ^ n) g := by
  have hn : K ^ n = K ^ m * (K * K ^ (n - m - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
  have hpos : 0 < K ^ m := Nat.pow_pos hK
  rw [hn, sumTo_split (K ^ m) _ (K * K ^ (n - m - 1)), sumTo_split (K ^ m) _ (K * K ^ (n - m - 1))]
  rw [sumTo_split K _ (K ^ (n - m - 1)), sumTo_split K _ (K ^ (n - m - 1))]
  rw [sumTo_mul]
  refine sumTo_congr _ (fun hi _ => ?_)
  -- left: Σ_d Σ_lo Σ_c g(lo + K^m(c + K hi)); right: K * Σ_d Σ_lo g(lo + K^m(d + K hi))
  have hl : ∀ d, d < K → sumTo (K ^ m) (fun lo => sumTo K (fun c => g (rset K m (lo + K ^ m * (d + K * hi)) c))) =
      sumTo (K ^ m) (fun lo => sumTo K (fun c => g (lo + K ^ m * (c + K * hi)))) := fun d hd =>
    sumTo_congr _ (fun lo hlo => sumTo_congr _ (fun c _ => by rw [(split_digit hK hlo hd).2 c]))
  rw [sumTo_congr K hl, sumTo_const, sumTo_exch (fun lo c => g (lo + K ^ m * (c + K * hi))) K (K ^ m)]

/-- **The real Fiat–Shamir count, reprogrammed**: `K` times the count over
    the tables with the challenge `c = H(m)` is the count over the tables
    and every challenge, the table's answer at `m` set to `c`. -/
theorem fs_real {X Vw : Type} {K n : Nat} (hK : 0 < K) (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (msg : X → Nat) (hmsg : ∀ x, msg x < n) (rv : Nat → X → Vw) (E : Nat → Nat → Nat → Vw → Bool) :
    K * sumTo (K ^ n) (fun H => sm (fun x => indB (E H (msg x) (rget K (msg x) H) (rv (rget K (msg x) H) x)))) =
      sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (E (rset K (msg x) H c) (msg x) c (rv c x))))) := by
  have hKs : ∀ f : X → Nat, sm (fun x => K * f x) = K * sm f := fun f => by
    rw [show (fun x => K * f x) = fun x => sumTo K (fun _ => f x) from funext fun x => (sumTo_const _ K).symm,
      hsm K (fun _ x => f x), sumTo_const]
  rw [← hsm (K ^ n) (fun H x => indB (E H (msg x) (rget K (msg x) H) (rv (rget K (msg x) H) x))), ← hKs]
  have : ∀ x, K * sumTo (K ^ n) (fun H => indB (E H (msg x) (rget K (msg x) H) (rv (rget K (msg x) H) x))) =
      sumTo (K ^ n) (fun H => sumTo K (fun c => indB (E (rset K (msg x) H c) (msg x) c (rv c x)))) := fun x => by
    rw [← oracle_reprog hK (hmsg x)]
    exact sumTo_congr _ (fun H _ => sumTo_congr _ (fun c hc => by rw [rget_rset hK hc]))
  rw [show (fun x => K * sumTo (K ^ n) (fun H => indB (E H (msg x) (rget K (msg x) H) (rv (rget K (msg x) H) x)))) =
      fun x => sumTo (K ^ n) (fun H => sumTo K (fun c => indB (E (rset K (msg x) H c) (msg x) c (rv c x)))) from
      funext this, hsm (K ^ n)]
  exact sumTo_congr _ (fun H _ => hsm K _)

/-- **Fiat–Shamir keeps an exact simulation**, in the programmable random
    oracle model.  The public-coin protocol draws its randomness `x`,
    summed by `sm`, which commutes with finite sums; its message `msg x < n`
    comes before the challenge `c < K`, and its view is `rv c x`.  When
    every event on the challenge, the message and the view counts within
    `ε` of the simulator's (`smsg`, `sv`), then the real non-interactive
    view `(H, m, H(m), view)`, `K` times, counts within `K^n · ε` of the
    simulator that draws `H` and `c` and programs `H(m) := c`. -/
theorem fs_zk {X Vw : Type} {K n ε : Nat} (hK : 0 < K) (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (msg smsg : X → Nat) (hmsg : ∀ x, msg x < n) (rv sv : Nat → X → Vw) (gd : Nat → Bool)
    (h : ∀ F : Nat → Nat → Vw → Bool,
      sumTo K (fun c => sm (fun x => indB (gd c && F c (msg x) (rv c x)))) ≤
        sumTo K (fun c => sm (fun x => indB (gd c && F c (smsg x) (sv c x)))) + ε)
    (E : Nat → Nat → Nat → Vw → Bool) :
    K * sumTo (K ^ n) (fun H => sm (fun x => indB (gd (rget K (msg x) H) && E H (msg x) (rget K (msg x) H) (rv (rget K (msg x) H) x)))) ≤
      sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c && E (rset K (smsg x) H c) (smsg x) c (sv c x))))) +
        K ^ n * ε := by
  rw [fs_real hK sm hsm msg hmsg rv (fun H m c v => gd c && E H m c v)]
  calc sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c && E (rset K (msg x) H c) (msg x) c (rv c x)))))
      ≤ sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c && E (rset K (smsg x) H c) (smsg x) c (sv c x))))
          + ε) :=
        sumTo_mono _ (fun H _ => h (fun c m v => E (rset K m H c) m c v))
    _ = _ := by rw [sumTo_add, sumTo_const]

/-- **And the other way**: the simulator's count is within `K^n · ε` of
    `K` times the real one. -/
theorem fs_zk' {X Vw : Type} {K n ε : Nat} (hK : 0 < K) (sm : (X → Nat) → Nat)
    (hsm : ∀ (N : Nat) (f : Nat → X → Nat), sm (fun x => sumTo N (fun i => f i x)) = sumTo N (fun i => sm (f i)))
    (msg smsg : X → Nat) (hmsg : ∀ x, msg x < n) (rv sv : Nat → X → Vw) (gd : Nat → Bool)
    (h : ∀ F : Nat → Nat → Vw → Bool,
      sumTo K (fun c => sm (fun x => indB (gd c && F c (smsg x) (sv c x)))) ≤
        sumTo K (fun c => sm (fun x => indB (gd c && F c (msg x) (rv c x)))) + ε)
    (E : Nat → Nat → Nat → Vw → Bool) :
    sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c && E (rset K (smsg x) H c) (smsg x) c (sv c x))))) ≤
      K * sumTo (K ^ n) (fun H => sm (fun x => indB (gd (rget K (msg x) H) && E H (msg x) (rget K (msg x) H) (rv (rget K (msg x) H) x)))) +
        K ^ n * ε := by
  rw [fs_real hK sm hsm msg hmsg rv (fun H m c v => gd c && E H m c v)]
  calc sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c && E (rset K (smsg x) H c) (smsg x) c (sv c x)))))
      ≤ sumTo (K ^ n) (fun H => sumTo K (fun c => sm (fun x => indB (gd c && E (rset K (msg x) H c) (msg x) c (rv c x))))
          + ε) :=
        sumTo_mono _ (fun H _ => h (fun c m v => E (rset K m H c) m c v))
    _ = _ := by rw [sumTo_add, sumTo_const]

-- ---------------------------------------------------------------------------
-- Events that read the challenges
-- ---------------------------------------------------------------------------

/-- An event on the view and the challenges, read from the view where it
    shows them; `dflt` where it shows nothing. -/
def viewEv {PV PB : Type} (E : EF → EF → TViewN PV PB → Bool) (dflt : Bool) : TViewN PV PB → Bool
  | some (p, a, b, x, y) => E a b (some (p, a, b, x, y))
  | none => dflt

/-- **Events may read the challenges**: a transcript bound for every event
    on the view gives the same bound for events on the challenges and the
    view, when the real view shows nothing or its own challenges and the
    simulated view always shows its own. -/
theorem tsumN_ab {PV PB : Type} {NR m err : Nat} (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + err)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + err)
    (E : EF → EF → TViewN PV PB → Bool) :
    tsumN NR m (fun α β r t => indB (genB β && E α β (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E α β (sv α β r t))) + err ∧
    tsumN NR m (fun α β r t => indB (genB β && E α β (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E α β (rv α β r t))) + err := by
  have hs : ∀ d α β r t, viewEv E d (sv α β r t) = E α β (sv α β r t) := fun d α β r t => by
    obtain ⟨p, x, y, e⟩ := hsv α β r t; rw [e]; rfl
  have hr : ∀ α β r t, indB (genB β && E α β (rv α β r t)) ≤ indB (genB β && viewEv E true (rv α β r t)) ∧
      indB (genB β && viewEv E false (rv α β r t)) ≤ indB (genB β && E α β (rv α β r t)) := fun α β r t => by
    rcases hrv α β r t with e | ⟨p, x, y, e⟩
    · rw [e]
      refine ⟨?_, ?_⟩
      · show indB (genB β && E α β none) ≤ indB (genB β && true)
        cases genB β
        · exact Nat.le_refl _
        · exact indB_le _
      · show indB (genB β && false) ≤ _
        cases genB β <;> exact Nat.zero_le _
    · rw [e]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have ef : ∀ d, (fun α β r t => indB (genB β && viewEv E d (sv α β r t))) =
      (fun α β r t => indB (genB β && E α β (sv α β r t))) := fun d =>
    funext fun α => funext fun β => funext fun r => funext fun t => by rw [hs]
  refine ⟨?_, ?_⟩
  · calc _ ≤ tsumN NR m (fun α β r t => indB (genB β && viewEv E true (rv α β r t))) :=
          tsumN_mono fun α β r t => (hr α β r t).1
      _ ≤ tsumN NR m (fun α β r t => indB (genB β && viewEv E true (sv α β r t))) + err := h1 _
      _ = _ := by rw [ef]
  · calc _ = tsumN NR m (fun α β r t => indB (genB β && viewEv E false (sv α β r t))) := by rw [ef]
      _ ≤ tsumN NR m (fun α β r t => indB (genB β && viewEv E false (rv α β r t))) + err := h2 _
      _ ≤ _ := Nat.add_le_add_right (tsumN_mono fun α β r t => (hr α β r t).2) _

-- ---------------------------------------------------------------------------
-- A transcript under Fiat–Shamir
-- ---------------------------------------------------------------------------

/-- `efOf` has an inverse on the first `Q4` indices. -/
def efIdx (e : EF) : Nat := Tup.enc ⟨e.x0, e.x1, e.x2, e.x3⟩

theorem efIdx_efOf {i : Nat} (hi : i < Q4) : efIdx (efOf i) = i := by
  have h : (Tup.dec i).toEF = efOf i := rfl
  rw [toEF_eq] at h
  unfold efIdx; rw [← h, Tup.enc_dec hi]

theorem Q4_pos : 0 < Q4 := by
  have := P_pos
  unfold Q4; exact Nat.mul_pos this (Nat.mul_pos this (Nat.mul_pos this this))

/-- A challenge index `c < Q4²` read as the pair `(c / Q4, c % Q4)`. -/
theorem sumQ2 (g : Nat → Nat → Nat) :
    sumTo (Q4 * Q4) (fun c => g (c / Q4) (c % Q4)) = sumTo Q4 (fun i => sumTo Q4 (fun j => g i j)) := by
  rw [sumTo_split Q4 _ Q4]
  refine sumTo_congr _ (fun i _ => sumTo_congr _ (fun j hj => ?_))
  have hq := Q4_pos
  rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hj, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hj]

/-- The salt passes through the tuples' sums. -/
theorem sm_exch {NS NR m N : Nat} (f : Nat → Nat → Nat → (Nat → Tup) → Nat) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => sumTo N (fun i => f i σ r t)))) =
      sumTo N (fun i => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => f i σ r t)))) := by
  have e1 : ∀ σ r, sumN m (fun t => sumTo N (fun i => f i σ r t)) = sumTo N (fun i => sumN m (fun t => f i σ r t)) :=
    fun σ r => (sumTo_sumN m N (fun i t => f i σ r t)).symm
  simp only [e1]
  have e2 : ∀ σ, sumTo NR (fun r => sumTo N (fun i => sumN m (fun t => f i σ r t))) =
      sumTo N (fun i => sumTo NR (fun r => sumN m (fun t => f i σ r t))) := fun σ => sumTo_exch _ N NR
  simp only [e2]
  exact sumTo_exch _ N NS

/-- **Hiding commitments**: the data's commitment beside any view counts
    as a fixed datum's. -/
theorem com_swap {D : Type} {NS NR m : Nat} (Com : D → Nat → Nat) (hcom : ComHides NS Com)
    (main : (Nat → Tup) → Nat → D) (d0 : D) (G : Nat → (Nat → Tup) → Nat → Bool) :
    sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (G r t (Com (main t r) σ))))) =
      sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (G r t (Com d0 σ))))) := by
  have sw : ∀ d : (Nat → Tup) → Nat → D, sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => indB (G r t (Com (d t r) σ))))) =
      sumTo NR (fun r => sumN m (fun t => sumTo NS (fun σ => indB (G r t (Com (d t r) σ))))) := fun d => by
    rw [sumTo_exch _ NR NS]
    exact sumTo_congr _ (fun r _ => sumTo_sumN m NS (fun σ t => indB (G r t (Com (d t r) σ))))
  rw [sw main, sw (fun _ _ => d0)]
  exact sumTo_congr _ (fun r _ => Nat.le_antisymm
    (sumN_mono m (fun t => Nat.le_of_eq (hcom (main t r) d0 (G r t))))
    (sumN_mono m (fun t => Nat.le_of_eq (hcom (main t r) d0 (G r t)).symm)))

/-- A challenge-indexed transcript count, as `tsumN` with the event reading
    its challenges' indices. -/
theorem csum_tsumN {PV PB : Type} {NR m : Nat} (v : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (F : Nat → TViewN PV PB → Bool) :
    sumTo (Q4 * Q4) (fun c => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (v (efOf (c / Q4)) (efOf (c % Q4)) r t))))) =
    tsumN NR m (fun α β r t => indB (genB β && F (efIdx β + Q4 * efIdx α) (v α β r t))) := by
  let g := fun i j => sumTo NR (fun r => sumN m (fun t =>
    indB (genB (efOf j) && F (j + Q4 * i) (v (efOf i) (efOf j) r t))))
  have e : (fun c => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (v (efOf (c / Q4)) (efOf (c % Q4)) r t))))) = fun c => g (c / Q4) (c % Q4) :=
    funext fun c => by show _ = sumTo NR _; rw [Nat.mod_add_div]
  rw [e, sumQ2 g]
  unfold tsumN
  exact sumTo_congr _ (fun i hi => sumTo_congr _ (fun j hj => by
    show _ = sumTo NR fun r => sumN m fun t =>
      indB (genB (efOf j) && F (efIdx (efOf j) + Q4 * efIdx (efOf i)) (v (efOf i) (efOf j) r t))
    rw [efIdx_efOf hi, efIdx_efOf hj]))

/-- **A transcript under Fiat–Shamir, in the programmable random-oracle
    model**: the challenges `(α, β)` are the oracle's answer, read as a
    pair of indices, at the commitment `Com (main t r) σ` of the prover's
    first message.  Given the transcript bound for every event on the
    view (`h1`, `h2`), a hiding commitment (`ComHides`) and the real view
    showing nothing or its own challenges, the real non-interactive view,
    the oracle's whole table with it, `Q4²` times, is within `(Q4²)^n · NS ·
    err` of the simulator's, which commits to a fixed datum, draws the
    challenges and programs the oracle. -/
theorem fs_transcript {PV PB D : Type} {NR m err NS n : Nat}
    (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + err)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + err)
    (Com : D → Nat → Nat) (hcom : ComHides NS Com) (hrange : ∀ d σ, Com d σ < n)
    (main : (Nat → Tup) → Nat → D) (d0 : D) (E : Nat → Nat → TViewN PV PB → Bool) :
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
          r t)))))) ≤
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ n * (NS * err) := by
  refine fs_zk (X := Nat × Nat × (Nat → Tup)) (K := Q4 * Q4) (n := n) (ε := NS * err) (Nat.mul_pos Q4_pos Q4_pos)
    (fun g => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ, r, t)))))
    (fun N f => sm_exch (fun i σ r t => f i (σ, r, t)))
    (fun x => Com (main x.2.2 x.2.1) x.1) (fun x => Com d0 x.1) (fun x => hrange _ _)
    (fun c x => rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2) (fun c x => sv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2)
    (fun c => genB (efOf (c % Q4))) (fun F => ?_) (fun H mm _ v => E H mm v)
  show sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ) (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) ≤
    sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com d0 σ) (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) + NS * err
  rw [sumTo_congr _ (fun c _ => com_swap Com hcom main d0
    (fun r t cm => genB (efOf (c % Q4)) && F c cm (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))]
  rw [sumTo_exch _ NS (Q4 * Q4), sumTo_exch _ NS (Q4 * Q4), ← sumTo_const err NS, ← sumTo_add]
  refine sumTo_mono _ (fun σ _ => ?_)
  rw [csum_tsumN rv (fun c v => F c (Com d0 σ) v), csum_tsumN sv (fun c v => F c (Com d0 σ) v)]
  exact (tsumN_ab rv sv hrv hsv h1 h2 (fun α β v => F (efIdx β + Q4 * efIdx α) (Com d0 σ) v)).1

/-- **And the other way.** -/
theorem fs_transcript' {PV PB D : Type} {NR m err NS n : Nat}
    (rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + err)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + err)
    (Com : D → Nat → Nat) (hcom : ComHides NS Com) (hrange : ∀ d σ, Com d σ < n)
    (main : (Nat → Tup) → Nat → D) (d0 : D) (E : Nat → Nat → TViewN PV PB → Bool) :
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
          r t)))))) +
    (Q4 * Q4) ^ n * (NS * err) := by
  refine fs_zk' (X := Nat × Nat × (Nat → Tup)) (K := Q4 * Q4) (n := n) (ε := NS * err) (Nat.mul_pos Q4_pos Q4_pos)
    (fun g => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ, r, t)))))
    (fun N f => sm_exch (fun i σ r t => f i (σ, r, t)))
    (fun x => Com (main x.2.2 x.2.1) x.1) (fun x => Com d0 x.1) (fun x => hrange _ _)
    (fun c x => rv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2) (fun c x => sv (efOf (c / Q4)) (efOf (c % Q4)) x.2.1 x.2.2)
    (fun c => genB (efOf (c % Q4))) (fun F => ?_) (fun H mm _ v => E H mm v)
  show sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com d0 σ) (sv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) ≤
    sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && F c (Com (main t r) σ) (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))))) + NS * err
  rw [sumTo_congr _ (fun c _ => com_swap Com hcom main d0
    (fun r t cm => genB (efOf (c % Q4)) && F c cm (rv (efOf (c / Q4)) (efOf (c % Q4)) r t)))]
  rw [sumTo_exch _ NS (Q4 * Q4), sumTo_exch _ NS (Q4 * Q4), ← sumTo_const err NS, ← sumTo_add]
  refine sumTo_mono _ (fun σ _ => ?_)
  rw [csum_tsumN rv (fun c v => F c (Com d0 σ) v), csum_tsumN sv (fun c v => F c (Com d0 σ) v)]
  exact (tsumN_ab rv sv hrv hsv h1 h2 (fun α β v => F (efIdx β + Q4 * efIdx α) (Com d0 σ) v)).2

end Circuit
