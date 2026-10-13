import Ski.ZK.SpongeSpread

/-!
# Two sponge chains meet rarely under per-step random round functions

An overwriting duplex sponge is not injective in its state, so
`SpongeSpread`'s exact argument does not reach it.  Here each absorption
reads its own uniformly drawn table, the step's round function, at a
position injective in the state below `K` for the block (`inner`).  Two
chains from distinct states below `K` meet on at most `L/K` of the tables
over `L` absorptions (`chainL_meet`): at the first step where they meet,
two distinct positions of a fresh table agree (`pair_countT`).  Two digits
absorbed from one state at distinct positions meet on at most `(L+1)/K`
(`chainL_meet_digit`).  `chainL_sat` meets the hypotheses.

The model's state is the capacity, the next capacity the round function's
answer at the block and the capacity: an overwriting sponge whose blocks
fill the rate.  Not shown:
- Plonky3's one permutation in place of independent per-step round
  functions (Plonky3 feeds no step counter): its random-function part is
  in `SpongePerm`, a birthday term of order `(2L)²/(2K)`;
- partial-rate absorptions, where old rate elements enter the next call;
- a squeezed index shorter than the capacity;
- `SudChallenger`'s `hφsp`: it bounds, at every table, how many salts
  reach one index, while these bounds average over the tables whether one
  pair of chains meets; pair collisions bound the squared fibre sizes, so
  even averaged they give fibres of order `NS1 √((L+1)/K)` beyond the
  first commitment's own fibre (equal digits meet surely), the digits
  must lie below the sponge's digit range, and a worst-case table defeats
  `hφsp` outright.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **Two distinct positions of a uniform table agree on `1/K` of the
    tables.** -/
theorem pair_countT {K n p q : Nat} (hK : 0 < K) (hp : p < n) (hpq : p ≠ q) :
    K * sumTo (K ^ n) (fun H => indB (decide (rget K p H = rget K q H))) ≤ K ^ n := by
  have hq : q < n ∨ n ≤ q := Nat.lt_or_ge q n
  rcases hq with hq | hq
  · have e := reprog_swap (n := n) hK hq (fun c H => indB (decide (rget K p H = c)))
    have lhs : sumTo (K ^ n) (fun H => sumTo K (fun u => indB (decide (rget K p (rset K q H u) = rget K q H)))) =
        K * sumTo (K ^ n) (fun H => indB (decide (rget K p H = rget K q H))) := by
      rw [sumTo_mul]
      refine sumTo_congr _ (fun H _ => ?_)
      rw [← sumTo_const _ K]
      refine sumTo_congr _ (fun u hu => ?_)
      rw [rget_rset_ne hK hpq hu]
    rw [← lhs, e]
    calc sumTo (K ^ n) (fun H => sumTo K (fun c => indB (decide (rget K p H = c))))
        ≤ sumTo (K ^ n) (fun _ => 1) := sumTo_mono _ (fun H _ => by
          have h := (sumTo_indEq (rget K p H) K).1
          refine Nat.le_trans (Nat.le_of_eq (sumTo_congr _ (fun c _ => ?_))) h
          by_cases hc : rget K p H = c
          · rw [decide_eq_true hc, decide_eq_true hc.symm]
          · rw [decide_eq_false hc, decide_eq_false (Ne.symm hc)])
      _ = K ^ n := by rw [sumTo_const, Nat.mul_one]
  · -- a position past the table reads `0`
    have z : ∀ H, H < K ^ n → rget K q H = 0 := fun H hH => by
      unfold rget
      have : H / K ^ q = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hH (Nat.pow_le_pow_right hK hq))
      rw [this, Nat.zero_mod]
    have e : ∀ H, H < K ^ n → indB (decide (rget K p H = rget K q H)) = indB (decide (rget K p H = 0)) :=
      fun H hH => by rw [z H hH]
    rw [sumTo_congr _ e]
    have := reprog_swap (n := n) hK hp (fun c _ => indB (decide (c = 0)))
    have lhs : sumTo (K ^ n) (fun H => sumTo K (fun _ => indB (decide (rget K p H = 0)))) =
        K * sumTo (K ^ n) (fun H => indB (decide (rget K p H = 0))) := by
      rw [sumTo_mul]; exact sumTo_congr _ (fun H _ => sumTo_const _ K)
    rw [← lhs, this]
    calc sumTo (K ^ n) (fun _ => sumTo K (fun c => indB (decide (c = 0))))
        ≤ sumTo (K ^ n) (fun _ => 1) := sumTo_mono _ (fun _ _ => by
          have h := (sumTo_indEq 0 K).1
          refine Nat.le_trans (Nat.le_of_eq (sumTo_congr _ (fun c _ => ?_))) h
          by_cases hc : c = 0 <;> simp [hc, indB])
      _ = K ^ n := by rw [sumTo_const, Nat.mul_one]

theorem rget_lt {K : Nat} (hK : 0 < K) (m H : Nat) : rget K m H < K := Nat.mod_lt _ hK

/-- A sum over `L` tables, each below `T`. -/
def sumTabs (T : Nat) : Nat → (List Nat → Nat) → Nat
  | 0, f => f []
  | L + 1, f => sumTo T (fun h => sumTabs T L (fun hs => f (h :: hs)))

theorem sumTabs_mono (T : Nat) : ∀ (L : Nat) (f g : List Nat → Nat), (∀ hs, f hs ≤ g hs) → sumTabs T L f ≤ sumTabs T L g
  | 0, _, _, h => h []
  | L + 1, _, _, h => sumTo_mono _ (fun x _ => sumTabs_mono T L _ _ (fun hs => h (x :: hs)))

theorem sumTabs_const (T c : Nat) : ∀ L, sumTabs T L (fun _ => c) = T ^ L * c
  | 0 => by show c = 1 * c; rw [Nat.one_mul]
  | L + 1 => by
    show sumTo T (fun _ => sumTabs T L (fun _ => c)) = T ^ (L + 1) * c
    rw [sumTabs_const T c L, sumTo_const, Nat.pow_succ]; ac_rfl

theorem sumTabs_add (T : Nat) : ∀ (L : Nat) (f g : List Nat → Nat), sumTabs T L (fun hs => f hs + g hs) = sumTabs T L f + sumTabs T L g
  | 0, _, _ => rfl
  | L + 1, f, g => by
    show sumTo T (fun h => sumTabs T L (fun hs => f (h :: hs) + g (h :: hs))) = sumTo T _ + sumTo T _
    rw [← sumTo_add]
    exact sumTo_congr _ (fun h _ => sumTabs_add T L _ _)

theorem sumTabs_mul (T k : Nat) : ∀ (L : Nat) (f : List Nat → Nat), k * sumTabs T L f = sumTabs T L (fun hs => k * f hs)
  | 0, _ => rfl
  | L + 1, f => by
    show k * sumTo T _ = sumTo T _
    rw [sumTo_mul]
    exact sumTo_congr _ (fun h _ => sumTabs_mul T k L _)

/-- **A sponge chain over per-step tables**: each block absorbed by reading
    the step's table at `inner s x`, the state's position for the block. -/
def chainL (K : Nat) (inner : Nat → Nat → Nat) : Nat → List Nat → List Nat → Nat
  | s, x :: xs, h :: hs => chainL K inner (rget K (inner s x) h) xs hs
  | s, _, _ => s

/-- **Two chains from distinct states meet on at most `L/K` of the tables**
    over `L` absorptions, each position injective in the state. -/
theorem chainL_meet {K M : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, s < K → inner s x < M)
    (hinj : ∀ x s s', s < K → s' < K → inner s x = inner s' x → s = s') :
    ∀ (xs : List Nat) (s s' : Nat), s < K → s' < K → s ≠ s' →
      K * sumTabs (K ^ M) xs.length (fun hs => indB (decide (chainL K inner s xs hs = chainL K inner s' xs hs))) ≤
        xs.length * (K ^ M) ^ xs.length
  | [], s, s', _, _, hne => by
    show K * indB (decide (s = s')) ≤ 0 * 1
    rw [decide_eq_false hne]; exact Nat.le_of_eq rfl
  | x :: xs, s, s', hs, hs', hne => by
    have hpq : inner s x ≠ inner s' x := fun e => hne (hinj x s s' hs hs' e)
    have ih := fun u v (hu : u < K) (hv : v < K) (huv : u ≠ v) => chainL_meet hK inner hin hinj xs u v hu hv huv
    let p := inner s x
    let q := inner s' x
    have pt : ∀ h hs, indB (decide (chainL K inner s (x :: xs) (h :: hs) = chainL K inner s' (x :: xs) (h :: hs))) ≤
        indB (decide (rget K p h = rget K q h)) +
          (if rget K p h = rget K q h then 0 else
            indB (decide (chainL K inner (rget K p h) xs hs = chainL K inner (rget K q h) xs hs))) := by
      intro h hs
      show indB (decide (chainL K inner (rget K p h) xs hs = chainL K inner (rget K q h) xs hs)) ≤ _
      by_cases e : rget K p h = rget K q h
      · rw [if_pos e, decide_eq_true e]; exact Nat.le_trans (indB_le _) (Nat.le_of_eq (by simp [indB]))
      · rw [if_neg e]; exact Nat.le_add_left _ _
    show K * sumTo (K ^ M) (fun h => sumTabs (K ^ M) xs.length (fun hs =>
        indB (decide (chainL K inner s (x :: xs) (h :: hs) = chainL K inner s' (x :: xs) (h :: hs))))) ≤
      (xs.length + 1) * (K ^ M) ^ (xs.length + 1)
    have step : ∀ h, h < K ^ M → K * sumTabs (K ^ M) xs.length (fun hs =>
        indB (decide (chainL K inner s (x :: xs) (h :: hs) = chainL K inner s' (x :: xs) (h :: hs)))) ≤
        K * ((K ^ M) ^ xs.length * indB (decide (rget K p h = rget K q h))) + xs.length * (K ^ M) ^ xs.length := by
      intro h _
      refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTabs_mono _ _ _ _ (fun hs => pt h hs))) ?_
      rw [sumTabs_add, Nat.mul_add, sumTabs_const]
      refine Nat.add_le_add_left ?_ _
      by_cases e : rget K p h = rget K q h
      · simp only [if_pos e]; rw [sumTabs_const, Nat.mul_zero, Nat.mul_zero]; exact Nat.zero_le _
      · simp only [if_neg e]; exact ih _ _ (rget_lt hK _ _) (rget_lt hK _ _) e
    rw [sumTo_mul]
    refine Nat.le_trans (sumTo_mono _ step) ?_
    rw [sumTo_add, sumTo_const, ← sumTo_mul, ← sumTo_mul]
    have pc := pair_countT (n := M) hK (hin s x hs) hpq
    have e2 : K * ((K ^ M) ^ xs.length * sumTo (K ^ M) (fun h => indB (decide (rget K p h = rget K q h)))) ≤
        (K ^ M) ^ xs.length * K ^ M := by
      rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ pc
    calc K * ((K ^ M) ^ xs.length * sumTo (K ^ M) (fun h => indB (decide (rget K p h = rget K q h)))) +
          K ^ M * (xs.length * (K ^ M) ^ xs.length)
        ≤ (K ^ M) ^ xs.length * K ^ M + K ^ M * (xs.length * (K ^ M) ^ xs.length) := Nat.add_le_add_right e2 _
      _ = (xs.length + 1) * (K ^ M) ^ (xs.length + 1) := by
        rw [Nat.pow_succ, Nat.succ_mul]; ac_rfl

/-- **Two digits absorbed from one state meet on at most `(L+1)/K` of the
    tables**: the digits read at distinct positions (`hd`, the absorption
    injective in the block), then `L` more blocks. -/
theorem chainL_meet_digit {K M : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, s < K → inner s x < M)
    (hinj : ∀ x s s', s < K → s' < K → inner s x = inner s' x → s = s') (iv a b : Nat) (hiv : iv < K)
    (hd : inner iv a ≠ inner iv b)
    (xs : List Nat) :
    K * sumTabs (K ^ M) (xs.length + 1)
        (fun hs => indB (decide (chainL K inner iv (a :: xs) hs = chainL K inner iv (b :: xs) hs))) ≤
      (xs.length + 1) * (K ^ M) ^ (xs.length + 1) := by
  have ih := fun u v (hu : u < K) (hv : v < K) (huv : u ≠ v) => chainL_meet hK inner hin hinj xs u v hu hv huv
  let p := inner iv a
  let q := inner iv b
  have hpq : p ≠ q := hd
  have pt : ∀ h hs, indB (decide (chainL K inner iv (a :: xs) (h :: hs) = chainL K inner iv (b :: xs) (h :: hs))) ≤
      indB (decide (rget K p h = rget K q h)) +
        (if rget K p h = rget K q h then 0 else
          indB (decide (chainL K inner (rget K p h) xs hs = chainL K inner (rget K q h) xs hs))) := by
    intro h hs
    show indB (decide (chainL K inner (rget K p h) xs hs = chainL K inner (rget K q h) xs hs)) ≤ _
    by_cases e : rget K p h = rget K q h
    · rw [if_pos e, decide_eq_true e]; exact Nat.le_trans (indB_le _) (Nat.le_of_eq (by simp [indB]))
    · rw [if_neg e]; exact Nat.le_add_left _ _
  show K * sumTo (K ^ M) (fun h => sumTabs (K ^ M) xs.length (fun hs =>
      indB (decide (chainL K inner iv (a :: xs) (h :: hs) = chainL K inner iv (b :: xs) (h :: hs))))) ≤
    (xs.length + 1) * (K ^ M) ^ (xs.length + 1)
  have step : ∀ h, h < K ^ M → K * sumTabs (K ^ M) xs.length (fun hs =>
      indB (decide (chainL K inner iv (a :: xs) (h :: hs) = chainL K inner iv (b :: xs) (h :: hs)))) ≤
      K * ((K ^ M) ^ xs.length * indB (decide (rget K p h = rget K q h))) + xs.length * (K ^ M) ^ xs.length := by
    intro h _
    refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTabs_mono _ _ _ _ (fun hs => pt h hs))) ?_
    rw [sumTabs_add, Nat.mul_add, sumTabs_const]
    refine Nat.add_le_add_left ?_ _
    by_cases e : rget K p h = rget K q h
    · simp only [if_pos e]; rw [sumTabs_const, Nat.mul_zero, Nat.mul_zero]; exact Nat.zero_le _
    · simp only [if_neg e]; exact ih _ _ (rget_lt hK _ _) (rget_lt hK _ _) e
  rw [sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ step) ?_
  rw [sumTo_add, sumTo_const, ← sumTo_mul, ← sumTo_mul]
  have pc := pair_countT (n := M) hK (hin iv a hiv) hpq
  have e2 : K * ((K ^ M) ^ xs.length * sumTo (K ^ M) (fun h => indB (decide (rget K p h = rget K q h)))) ≤
      (K ^ M) ^ xs.length * K ^ M := by
    rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ pc
  calc K * ((K ^ M) ^ xs.length * sumTo (K ^ M) (fun h => indB (decide (rget K p h = rget K q h)))) +
        K ^ M * (xs.length * (K ^ M) ^ xs.length)
      ≤ (K ^ M) ^ xs.length * K ^ M + K ^ M * (xs.length * (K ^ M) ^ xs.length) := Nat.add_le_add_right e2 _
    _ = (xs.length + 1) * (K ^ M) ^ (xs.length + 1) := by
      rw [Nat.pow_succ, Nat.succ_mul]; ac_rfl

/-- **The hypotheses are met** by `inner s x = (x % X) K + s`: positions
    below `X K`, injective in the state below `K`, and distinct digits
    below `X` at distinct positions. -/
theorem chainL_sat {K X : Nat} (hK : 0 < K) (hX : 0 < X) :
    (∀ s x, s < K → (x % X) * K + s < X * K) ∧
      (∀ x s s', s < K → s' < K → (x % X) * K + s = (x % X) * K + s' → s = s') ∧
      (∀ iv a b, a < X → b < X → a ≠ b → (a % X) * K + iv ≠ (b % X) * K + iv) := by
  refine ⟨fun s x hs => ?_, fun x s s' _ _ h => by omega, fun iv a b ha hb hab h => hab ?_⟩
  · calc (x % X) * K + s < (x % X) * K + K := Nat.add_lt_add_left hs _
      _ = (x % X + 1) * K := by rw [Nat.succ_mul]
      _ ≤ X * K := Nat.mul_le_mul_right _ (Nat.mod_lt _ hX)
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
    exact Nat.eq_of_mul_eq_mul_right hK (by omega)

end Circuit
