import Ski.ZK.SudChallenger

/-!
# An adding duplex sponge meets the challenger's spread

`SudChallenger` asks the fourth table's index `φ m w` to spread over the
first commitment's salt (`hφsp`).  An index injective in the first
commitment's digit, for each later absorbed block, spreads exactly as the
commitment does (`hφsp_of_inj`).  An adding duplex sponge has that
property: its state lies in `[0, N)`, each absorption adds the block modulo
`N` and applies a permutation `π` of `[0, N)`, so for a fixed block it is
injective in the state, and the state after absorbing the digit (below
`n1 ≤ N`) and then any blocks determines the digit (`spongeA`,
`spongeA_inj`, `spongeA_hφsp`, the transcript encoded as blocks by any
`enc`).  The index is the full state, below `N` (`spongeA_lt`), so the
fourth table spans it: `N ≤ N4`.  The state is one element of `Z_N`, all of
it rate; each block is one absorption, so a digit spread over several rate
blocks is not covered.  Over any state type, a vector of field elements
included, the same holds when each absorption is injective in the state
(a translation followed by a permutation is), the first absorption in the
digit (`n1` at most the rate's values), and the index in the state
(`spongeG`, `spongeG_hφsp`); the digit still absorbs in one block.  The
index is then the full state, capacity included, so the fourth table
spans every reachable state, `N4 ≥ |S|`: about `p^t` for a width-`t`
state, sound but far from a deployed challenger, which squeezes a shorter
index (not shown).

Not shown: Plonky3's `DuplexChallenger`, which overwrites the rate part of
the state instead of adding into it, so two states differing only there
meet after one absorption; its spread rests on the permutation's
randomness over the capacity.  Not shown either: a squeezed index shorter
than the state, whose spread is a property of a random permutation, not
of a worst-case fibre.
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

theorem add_mod_cancel {N s s' x : Nat} (hs : s < N) (hs' : s' < N) (h : (s + x) % N = (s' + x) % N) : s = s' := by
  rcases Nat.le_total s s' with hl | hl
  · have e := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    have hd : s' + x - (s + x) = s' - s := by omega
    rw [hd] at e
    have hlt : s' - s < N := by omega
    rw [Nat.mod_eq_of_lt hlt] at e
    omega
  · have e := Nat.sub_mod_eq_zero_of_mod_eq h
    have hd : s + x - (s' + x) = s - s' := by omega
    rw [hd] at e
    have hlt : s - s' < N := by omega
    rw [Nat.mod_eq_of_lt hlt] at e
    omega

/-- One absorption of an adding sponge: the block added into the state
    modulo `N`, then the permutation `π` of `[0, N)`. -/
def absorbA (π : Nat → Nat) (N : Nat) (s x : Nat) : Nat := π ((s + x) % N)

/-- **An adding duplex sponge's state**: from `iv`, the digit absorbed
    first, then the rest of the message and the later blocks. -/
def spongeA (π : Nat → Nat) (N iv n1 : Nat) (m : Nat) (w : List Nat) : Nat :=
  (m / n1 :: w).foldl (absorbA π N) (absorbA π N iv (m % n1))

theorem foldlA_lt {π : Nat → Nat} {N : Nat} (hπN : ∀ a, a < N → π a < N) (hN : 0 < N) :
    ∀ (xs : List Nat) (s : Nat), s < N → xs.foldl (absorbA π N) s < N
  | [], _, h => h
  | _ :: xs, _, _ => foldlA_lt hπN hN xs _ (hπN _ (Nat.mod_lt _ hN))

theorem foldlA_inj {π : Nat → Nat} {N : Nat} (hπ : ∀ a b, a < N → b < N → π a = π b → a = b)
    (hπN : ∀ a, a < N → π a < N) (hN : 0 < N) :
    ∀ (xs : List Nat) (s s' : Nat), s < N → s' < N →
      xs.foldl (absorbA π N) s = xs.foldl (absorbA π N) s' → s = s'
  | [], _, _, _, _, h => h
  | x :: xs, s, s', hs, hs', h => by
    have h1 := foldlA_inj hπ hπN hN xs _ _ (hπN _ (Nat.mod_lt _ hN)) (hπN _ (Nat.mod_lt _ hN)) h
    exact add_mod_cancel hs hs' (hπ _ _ (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) h1)

/-- **The adding sponge's state determines the first absorbed digit**: `π`
    a permutation of `[0, N)`, the digits below `n1 ≤ N`. -/
theorem spongeA_inj {π : Nat → Nat} {N iv n1 : Nat} (hπ : ∀ a b, a < N → b < N → π a = π b → a = b)
    (hπN : ∀ a, a < N → π a < N) (hn1 : n1 ≤ N) :
    ∀ rest w a b, a < n1 → b < n1 → spongeA π N iv n1 (a + n1 * rest) w = spongeA π N iv n1 (b + n1 * rest) w → a = b := by
  intro rest w a b ha hb h
  have hpos : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  have hN : 0 < N := Nat.lt_of_lt_of_le hpos hn1
  unfold spongeA at h
  rw [Nat.add_mul_div_left _ _ hpos, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb,
    Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  have h1 := foldlA_inj hπ hπN hN _ _ _ (hπN _ (Nat.mod_lt _ hN)) (hπN _ (Nat.mod_lt _ hN)) h
  have h2 := hπ _ _ (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) h1
  have h3 : (a + iv) % N = (b + iv) % N := by rw [Nat.add_comm a, Nat.add_comm b]; exact h2
  exact add_mod_cancel (Nat.lt_of_lt_of_le ha hn1) (Nat.lt_of_lt_of_le hb hn1) h3

/-- **An adding duplex sponge meets the spread**, its full state the index,
    the transcript `w` encoded as blocks by any `enc`. -/
theorem spongeA_hφsp {D W : Type} {NS1 n1 δs : Nat} {π : Nat → Nat} {N iv : Nat}
    (hπ : ∀ a b, a < N → b < N → π a = π b → a = b) (hπN : ∀ a, a < N → π a < N) (hn1 : n1 ≤ N)
    (enc : W → List Nat) (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) :
    ∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide (spongeA π N iv n1 (Com1 d σ1 + n1 * rest) (enc w) = v))) ≤ δs :=
  hφsp_of_inj Com1 (fun m w => spongeA π N iv n1 m (enc w))
    (fun rest w a b ha hb h => spongeA_inj hπ hπN hn1 rest (enc w) a b ha hb h) hr1 hsp1

/-- **The sponge's state lies in `[0, N)`**: as the fourth table's index it
    needs `N ≤ N4`, the table spanning the whole state. -/
theorem spongeA_lt {π : Nat → Nat} {N iv n1 : Nat} (hπN : ∀ a, a < N → π a < N) (hN : 0 < N) (m : Nat)
    (w : List Nat) : spongeA π N iv n1 m w < N :=
  foldlA_lt hπN hN _ _ (hπN _ (Nat.mod_lt _ hN))

/-- The identity is a permutation of `[0, N)`: the hypotheses are met. -/
theorem spongeA_sat (N : Nat) : (∀ a b, a < N → b < N → (fun x => x) a = (fun x => x) b → a = b) ∧
    (∀ a, a < N → (fun x : Nat => x) a < N) := ⟨fun _ _ _ _ h => h, fun _ h => h⟩

/-- **A sponge over any state**: the digit absorbed first by `start`, then
    the rest of the message and the later blocks by `absorb`, the state
    read as a table index by `idx`. -/
def spongeG {S B : Type} (start : Nat → S) (absorb : S → B → S) (blk : Nat → B) (idx : S → Nat)
    (n1 : Nat) (m : Nat) (w : List B) : Nat :=
  idx ((blk (m / n1) :: w).foldl absorb (start (m % n1)))

theorem foldlG_inj {S B : Type} {absorb : S → B → S} (habs : ∀ x s s', absorb s x = absorb s' x → s = s') :
    ∀ (xs : List B) (s s' : S), xs.foldl absorb s = xs.foldl absorb s' → s = s'
  | [], _, _, h => h
  | x :: xs, s, s', h => habs x s s' (foldlG_inj habs xs _ _ h)

/-- **A sponge over any state meets the spread** when each absorption is
    injective in the state (a translation by the block followed by a
    permutation, over any group: a vector of field elements, added
    componentwise, included), the first absorption injective in the digit,
    and the index injective in the state. -/
theorem spongeG_hφsp {D S B W : Type} {NS1 n1 δs : Nat} (start : Nat → S) (absorb : S → B → S) (blk : Nat → B)
    (idx : S → Nat) (enc : W → List B)
    (hstart : ∀ a b, a < n1 → b < n1 → start a = start b → a = b)
    (habs : ∀ x s s', absorb s x = absorb s' x → s = s') (hidx : ∀ s s', idx s = idx s' → s = s')
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) :
    ∀ d rest w v, sumTo NS1 (fun σ1 =>
      indB (decide (spongeG start absorb blk idx n1 (Com1 d σ1 + n1 * rest) (enc w) = v))) ≤ δs := by
  refine hφsp_of_inj Com1 (fun m w => spongeG start absorb blk idx n1 m (enc w)) (fun rest w a b ha hb h => ?_) hr1 hsp1
  have hpos : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  have h' := hidx _ _ h
  rw [Nat.add_mul_div_left _ _ hpos, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb,
    Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  exact hstart a b ha hb (foldlG_inj habs _ _ _ h')

end Circuit
