import Ski.ZK.SudChallenger

/-!
# A duplex sponge meets the challenger's spread

`SudChallenger` asks the fourth table's index `φ m w` to spread over the
first commitment's salt (`hφsp`).  Here a sponge meets it.  An index
injective in the first commitment's digit, for each later absorbed block,
spreads exactly as the commitment does (`hφsp_of_inj`).  A sponge whose
absorption is injective in its state, as a permutation of the full state
with the block added in is, has that property: the state after absorbing
the digit and then any blocks determines the digit (`spongeφ`,
`sponge_inj`, `sponge_hφsp`).  Squeezing a shorter index loses at most its
largest fibre: an index truncated by `tr`, at most `t` states to a value,
spreads within `t` times (`hφsp_trunc`), the floor that truncation to `N4`
values forces.

The absorption `P (state, block)` injective in the state is a sponge that
adds or XORs the block into the full state and permutes.  Plonky3's
`DuplexChallenger` overwrites the rate part of the state instead, so two
states differing only there meet after one absorption; its spread rests on
the permutation's randomness over the capacity, a collision bound not
shown here.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- A positive sum has a positive term. -/
theorem sum_pos_exists (f : Nat → Nat) : ∀ n, 0 < sumTo n f → ∃ i, i < n ∧ 0 < f i
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, h => by
    show ∃ i, i < n + 1 ∧ 0 < f i
    have h' : 0 < sumTo n f + f n := h
    rcases Nat.eq_zero_or_pos (f n) with e | e
    · rw [e, Nat.add_zero] at h'
      obtain ⟨i, hi, hf⟩ := sum_pos_exists f n h'
      exact ⟨i, Nat.lt_succ_of_lt hi, hf⟩
    · exact ⟨n, Nat.lt_succ_self n, e⟩

/-- **An index injective in the first commitment's digit spreads as the
    commitment does.** -/
theorem hφsp_of_inj {D W : Type} {NS1 n1 δs : Nat} (Com1 : D → Nat → Nat) (φ : Nat → W → Nat)
    (hinj : ∀ rest w a b, a < n1 → b < n1 → φ (a + n1 * rest) w = φ (b + n1 * rest) w → a = b)
    (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) :
    ∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide (φ (Com1 d σ1 + n1 * rest) w = v))) ≤ δs := by
  intro d rest w v
  rcases Nat.eq_zero_or_pos (sumTo NS1 (fun σ1 => indB (decide (φ (Com1 d σ1 + n1 * rest) w = v)))) with e | e
  · rw [e]; exact Nat.zero_le _
  · obtain ⟨σ0, _, hpos⟩ := sum_pos_exists _ NS1 e
    have h0 : φ (Com1 d σ0 + n1 * rest) w = v := by
      cases hd : decide (φ (Com1 d σ0 + n1 * rest) w = v)
      · rw [hd] at hpos; exact absurd hpos (Nat.lt_irrefl 0)
      · exact of_decide_eq_true hd
    refine Nat.le_trans (sumTo_mono _ (fun σ1 _ => ?_)) (hsp1 d (Com1 d σ0))
    cases hd : decide (φ (Com1 d σ1 + n1 * rest) w = v)
    · exact Nat.zero_le _
    · have e1 := hinj rest w _ _ (hr1 d σ1) (hr1 d σ0) ((of_decide_eq_true hd).trans h0.symm)
      rw [decide_eq_true e1]; exact Nat.le_refl _

/-- **A duplex sponge's state**: the digit absorbed first, then the rest of
    the message and the later blocks, each absorption `P (state, block)`. -/
def spongeφ (P : Nat × Nat → Nat) (iv n1 : Nat) (m : Nat) (w : List Nat) : Nat :=
  (m / n1 :: w).foldl (fun s x => P (s, x)) (P (iv, m % n1))

theorem foldl_inj (P : Nat × Nat → Nat) (hP : ∀ a b, P a = P b → a = b) :
    ∀ (xs : List Nat) (s s' : Nat), xs.foldl (fun s x => P (s, x)) s = xs.foldl (fun s x => P (s, x)) s' → s = s'
  | [], _, _, h => h
  | x :: xs, s, s', h => by
    have := foldl_inj P hP xs _ _ h
    exact (Prod.mk.inj (hP _ _ this)).1

/-- **The sponge's state determines the first absorbed digit**, the
    absorption injective in the state. -/
theorem sponge_inj (P : Nat × Nat → Nat) (hP : ∀ a b, P a = P b → a = b) (iv n1 : Nat) :
    ∀ rest w a b, a < n1 → b < n1 → spongeφ P iv n1 (a + n1 * rest) w = spongeφ P iv n1 (b + n1 * rest) w → a = b := by
  intro rest w a b ha hb h
  unfold spongeφ at h
  have hpos : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  rw [Nat.add_mul_div_left _ _ hpos, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb,
    Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  have := foldl_inj P hP _ _ _ h
  exact (Prod.mk.inj (hP _ _ this)).2

/-- **A duplex sponge meets the spread**: its full state as the index. -/
theorem sponge_hφsp {D : Type} {NS1 n1 δs : Nat} (P : Nat × Nat → Nat) (hP : ∀ a b, P a = P b → a = b) (iv : Nat)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) :
    ∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide (spongeφ P iv n1 (Com1 d σ1 + n1 * rest) w = v))) ≤ δs :=
  hφsp_of_inj Com1 (spongeφ P iv n1) (sponge_inj P hP iv n1) hr1 hsp1

/-- **A truncated index spreads within its largest fibre**: states below
    `U`, at most `t` of them sent to any one value by `tr`. -/
theorem hφsp_trunc {D W : Type} {NS1 n1 δs U t : Nat} (Com1 : D → Nat → Nat) (φ : Nat → W → Nat)
    (hU : ∀ m w, φ m w < U) (tr : Nat → Nat) (ht : ∀ v, sumTo U (fun u => indB (decide (tr u = v))) ≤ t)
    (hsp : ∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide (φ (Com1 d σ1 + n1 * rest) w = v))) ≤ δs) :
    ∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide (tr (φ (Com1 d σ1 + n1 * rest) w) = v))) ≤ t * δs := by
  intro d rest w v
  have pt : ∀ σ1, indB (decide (tr (φ (Com1 d σ1 + n1 * rest) w) = v)) ≤
      sumTo U (fun u => indB (decide (tr u = v)) * indB (decide (φ (Com1 d σ1 + n1 * rest) w = u))) := by
    intro σ1
    cases hd : decide (tr (φ (Com1 d σ1 + n1 * rest) w) = v)
    · exact Nat.zero_le _
    · have hv := of_decide_eq_true hd
      have key : ∀ n, φ (Com1 d σ1 + n1 * rest) w < n →
          1 ≤ sumTo n (fun u => indB (decide (tr u = v)) * indB (decide (φ (Com1 d σ1 + n1 * rest) w = u))) := by
        intro n
        induction n with
        | zero => intro h; exact absurd h (Nat.not_lt_zero _)
        | succ n ih =>
          intro h
          show 1 ≤ sumTo n _ + _
          rcases Nat.lt_or_ge (φ (Com1 d σ1 + n1 * rest) w) n with h' | h'
          · exact Nat.le_trans (ih h') (Nat.le_add_right _ _)
          · have e : φ (Com1 d σ1 + n1 * rest) w = n := Nat.le_antisymm (Nat.le_of_lt_succ h) h'
            rw [← e]
            dsimp only
            rw [decide_eq_true hv, decide_eq_true rfl]
            exact Nat.le_add_left _ _
      exact key U (hU _ _)
  refine Nat.le_trans (sumTo_mono _ (fun σ1 _ => pt σ1)) ?_
  rw [sumTo_exch _ U NS1]
  have each : ∀ u, sumTo NS1 (fun σ1 => indB (decide (tr u = v)) * indB (decide (φ (Com1 d σ1 + n1 * rest) w = u))) ≤
      δs * indB (decide (tr u = v)) := fun u => by
    rw [← sumTo_mul, Nat.mul_comm δs]; exact Nat.mul_le_mul_left _ (hsp d rest w u)
  refine Nat.le_trans (sumTo_mono _ (fun u _ => each u)) ?_
  rw [← sumTo_mul, Nat.mul_comm t]
  exact Nat.mul_le_mul_left _ (ht v)

end Circuit
