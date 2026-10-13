import Ski.ZK.SpongePermT

/-!
# The overwrite sponge's index over the first commitment

`SudChallenger` asks the fourth table's index `φ m w` to spread over the
first commitment's salt (`hφsp`).  Plonky3's challenger is a duplex sponge
whose blocks overwrite the rate; there the index is the chain's state after
absorbing the first commitment `c` and the later blocks `xs`
(`chain1`).  Distinct first commitments send the index alike only through
pairs of chains that meet.

- **At every table.** At most `δs (1 + pairs)` salts reach any index
  value, `pairs` the ordered pairs of distinct first commitments below
  `n1` whose chains meet (`spread_pairs`, through `preimage_le_pairs`).
- **Averaged over a uniform permutation.** Those pairs number at most
  `n1² (0 + ⋯ + (2L+1)) F / (K - 2(L+1))` per permutation table, from
  `two_meet_digitKP` (`pairs_countP`); so the salts reaching an index
  value chosen with the table in view number at most
  `δs (1 + n1² (0 + ⋯ + (2L+1)) F / (K - 2(L+1)))` on average
  (`spread_countP`).  `spread_satPT` meets `hd` at `two_meet_satPT`'s
  full-width instance.
- **Every later transcript at one table.** The later blocks `enc rest w`
  number at most `X^L` on their first `L` blocks (`xsOf_cover`), so one
  table's `δs' = δs (1 + pairsAll)`, `pairsAll` the meeting pairs summed
  over all `X^L` block lists, meets `hsp1` and `hφsp` in exactly the form
  `sudFS4T_hspS` and `sud_interleaveS` take, for every `d`, `rest`, `w`
  and `v` (`hφsp_sponge`, `sponge_hsp`).  Averaged over a uniform
  permutation, `δs'` is at most
  `δs (1 + X^L n1² (0 + ⋯ + (2L+1)) F / (K - 2(L+1)))` (`pairsAll_countP`,
  `sponge_δs_countP`).  The composites hold at each table with that
  table's `δs'`, their errors linear in it (checked by elaboration against
  `sudFS4T_hspS` and `sud_interleaveS`).

Not shown: the composites averaged over the permutation.  Their
distributions read the table through `φ`, so the per-table statements
must be summed over the tables, a step beyond the linearity of the error.

The bound says something only while
`X^L n1² (0 + ⋯ + (2L+1)) F` stays below `K - 2(L+1)`; with `F / K` one
over the capacity's size, that asks `n1²` well below the capacity even at
`L = 0`, and few later block lists besides.  It fails at Plonky3's widths:
an 8-element digest over a capacity of 8 elements puts `n1²` near the
capacity squared.  The cause is the per-table count itself
(`preimage_le_pairs`): about `n1² / |capacity|` pairs of first commitments
do meet.  A useful bound there needs the commitments actually drawn, not
all `n1` values, and the later blocks drawn independently of the
permutation.

Two modelling assumptions enter as well.  The state `iv` before the first commitment is fixed before
the permutation is drawn: no permutation call precedes the commitment.  The
first commitment fills one aligned block (`hd`, `n1 ≤ R1` at the full-width
instance); a digest straddling two permutation calls is not covered.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- One sponge chain under the table `H`: from `s`, the state after `i`
    absorptions of the blocks `xs`. -/
def chain1 (K : Nat) (inner : Nat → Nat → Nat) (s : Nat) (xs : List Nat) (H : Nat) : Nat → Nat
  | 0 => s
  | i + 1 => rget K (inner (chain1 K inner s xs H i) (xs.getD i 0)) H

theorem stA_chain (K : Nat) (inner : Nat → Nat → Nat) (sa sb : Nat) (xa xb : List Nat) (H : Nat) :
    ∀ i, stA K inner sa sb xa xb H i = chain1 K inner sa xa H i
  | 0 => by unfold stA; rw [if_pos rfl]; rfl
  | i + 1 => by
    unfold stA; rw [if_neg (by omega), two_step]
    show rget K (inner (stA K inner sa sb xa xb H i) (xa.getD i 0)) H = _
    rw [stA_chain K inner sa sb xa xb H i]; rfl

theorem stB_chain (K : Nat) (inner : Nat → Nat → Nat) (sa sb : Nat) (xa xb : List Nat) (H : Nat) :
    ∀ i, stB K inner sa sb xa xb H i = chain1 K inner sb xb H i
  | 0 => by unfold stB; rw [if_pos rfl]; rfl
  | i + 1 => by
    unfold stB; rw [if_neg (by omega), two_step]
    show rget K (inner (stB K inner sa sb xa xb H i) (xb.getD i 0)) H = _
    rw [stB_chain K inner sa sb xa xb H i]; rfl

/-- Ordered pairs of distinct arguments below `n` that `φ` sends alike. -/
def pairsEq (n : Nat) (φ : Nat → Nat) : Nat :=
  sumTo n (fun a => sumTo n (fun b => indB (a != b && decide (φ a = φ b))))

/-- **A value's preimage is one more than the pairs at most**: the `s`
    arguments sent to `v` give `s - 1` pairs with any one of them. -/
theorem preimage_le_pairs (n : Nat) (φ : Nat → Nat) (v : Nat) :
    sumTo n (fun a => indB (decide (φ a = v))) ≤ 1 + pairsEq n φ := by
  by_cases hex : ∃ a0, a0 < n ∧ φ a0 = v
  · obtain ⟨a0, ha0, hv⟩ := hex
    have pt : ∀ b, indB (decide (φ b = v)) ≤ indB (decide (b = a0)) + indB (a0 != b && decide (φ a0 = φ b)) := fun b => by
      by_cases e : b = a0
      · subst e
        rw [decide_eq_true rfl, show indB true = 1 from rfl]
        exact Nat.le_trans (indB_le _) (Nat.le_add_right _ _)
      · have hne : (a0 != b) = true := bne_iff_ne.2 (fun h => e h.symm)
        rw [decide_eq_false e, hne, Bool.true_and, hv]
        by_cases h2 : φ b = v
        · rw [decide_eq_true h2, decide_eq_true h2.symm]; simp [indB]
        · rw [decide_eq_false h2, decide_eq_false (fun h => h2 h.symm)]; simp [indB]
    refine Nat.le_trans (sumTo_mono _ (fun b _ => pt b)) ?_
    rw [sumTo_add]
    exact Nat.add_le_add (sumTo_indEq a0 n).1
      (le_sumTo (fun a => sumTo n (fun b => indB (a != b && decide (φ a = φ b)))) n ha0)
  · have : sumTo n (fun a => indB (decide (φ a = v))) = 0 :=
      Eq.trans (sumTo_congr _ (fun a ha => by
        rw [decide_eq_false (fun e => hex ⟨a, ha, e⟩)]; rfl)) (Eq.trans (sumTo_const 0 n) (Nat.mul_zero n))
    rw [this]; exact Nat.zero_le _

/-- **The index spreads over the salt, at every table, up to its pairs**:
    with the first commitment `Com1 d σ` below `n1` and each commitment
    value reached by at most `δs` salts, at most `δs (1 + pairs)` salts send
    the index `φ (Com1 d σ)` to any `v`. -/
theorem spread_pairs {D : Type} {NS1 n1 δs : Nat} (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) (φ : Nat → Nat) (d : D) (v : Nat) :
    sumTo NS1 (fun σ => indB (decide (φ (Com1 d σ) = v))) ≤ δs * (1 + pairsEq n1 φ) := by
  rw [sumTo_split_pos (Com1 d) (hr1 d)]
  have each : ∀ c, sumTo NS1 (fun σ => indB (decide (Com1 d σ = c)) * indB (decide (φ (Com1 d σ) = v))) ≤
      δs * indB (decide (φ c = v)) := fun c => by
    have e : ∀ σ, indB (decide (Com1 d σ = c)) * indB (decide (φ (Com1 d σ) = v)) =
        indB (decide (φ c = v)) * indB (decide (Com1 d σ = c)) := fun σ => by
      by_cases h : Com1 d σ = c
      · rw [h, Nat.mul_comm]
      · rw [decide_eq_false h]; simp [indB]
    rw [sumTo_congr _ (fun σ _ => e σ), ← sumTo_mul, Nat.mul_comm δs]
    exact Nat.mul_le_mul_left _ (hsp1 d c)
  refine Nat.le_trans (sumTo_mono _ (fun c _ => each c)) ?_
  rw [← sumTo_mul]
  exact Nat.mul_le_mul_left _ (preimage_le_pairs n1 φ v)

/-- **The overwrite sponge's pairs are rare under a uniform permutation**:
    first blocks `c < n1` absorbed from one state `iv` at distinct positions
    (`hd`), then the shared blocks `xs`; the ordered pairs of first blocks
    whose chains meet after `L + 1` absorptions, summed over the permutation
    tables, are at most `n1² (0 + ⋯ + (2L+1)) F / (K - 2(L+1))` per table. -/
theorem pairs_countP {K F n1 : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K)
    (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {iv : Nat}
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat) :
    (K - 2 * (L + 1)) * sumTo (K ^ K) (fun H =>
        indB (permB K H) * pairsEq n1 (fun c => chain1 K inner iv (c :: xs) H (L + 1))) ≤
      n1 * n1 * (sumTo (2 * (L + 1)) (fun j => j) * F * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  let B := sumTo (2 * (L + 1)) (fun j => j) * F * sumTo (K ^ K) (fun H => indB (permB K H))
  have pair : ∀ a b, a < n1 → b < n1 → (K - 2 * (L + 1)) * sumTo (K ^ K) (fun H => indB (permB K H) *
      indB (a != b && decide (chain1 K inner iv (a :: xs) H (L + 1) = chain1 K inner iv (b :: xs) H (L + 1)))) ≤ B := by
    intro a b ha hb
    by_cases hab : a = b
    · subst hab
      have z : ∀ H, indB (permB K H) * indB (a != a &&
          decide (chain1 K inner iv (a :: xs) H (L + 1) = chain1 K inner iv (a :: xs) H (L + 1))) = 0 := fun H => by
        rw [bne_self_eq_false, Bool.false_and]; exact Nat.mul_zero _
      rw [sumTo_congr _ (fun H _ => z H), sumTo_const, Nat.mul_zero, Nat.mul_zero]
      exact Nat.zero_le _
    · have hc := two_meet_digitKP hK inner hin κ hF hpk (hd a b ha hb hab) xs L
      refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_))) hc
      rw [stA_chain, stB_chain, bne_iff_ne.2 hab, Bool.true_and]
      cases permB K H <;> cases decide (chain1 K inner iv (a :: xs) H (L + 1) = chain1 K inner iv (b :: xs) H (L + 1)) <;>
        simp [indB]
  have e : sumTo (K ^ K) (fun H => indB (permB K H) * pairsEq n1 (fun c => chain1 K inner iv (c :: xs) H (L + 1))) =
      sumTo n1 (fun a => sumTo n1 (fun b => sumTo (K ^ K) (fun H => indB (permB K H) *
        indB (a != b && decide (chain1 K inner iv (a :: xs) H (L + 1) = chain1 K inner iv (b :: xs) H (L + 1)))))) := by
    unfold pairsEq
    rw [sumTo_congr _ (fun H _ => Eq.trans (sumTo_mul _ _ n1) (sumTo_congr _ (fun a _ => sumTo_mul _ _ n1)))]
    rw [sumTo_exch _ n1 (K ^ K)]
    exact sumTo_congr _ (fun a _ => sumTo_exch _ n1 (K ^ K))
  have row : ∀ a, a < n1 → (K - 2 * (L + 1)) * sumTo n1 (fun b => sumTo (K ^ K) (fun H => indB (permB K H) *
      indB (a != b && decide (chain1 K inner iv (a :: xs) H (L + 1) = chain1 K inner iv (b :: xs) H (L + 1))))) ≤
      n1 * B := fun a ha => by
    rw [sumTo_mul]
    exact Nat.le_trans (sumTo_mono _ (fun b hb => pair a b ha hb)) (Nat.le_of_eq (sumTo_const B n1))
  rw [e, sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun a ha => row a ha)) (Nat.le_of_eq ?_)
  · rw [sumTo_const, Nat.mul_assoc]

/-- **The index spreads over the salt, averaged over a uniform
    permutation**: the overwrite sponge's index after the first commitment
    and the shared blocks `xs`, the target `v H` chosen with the table in
    view; the salts reaching it, summed over the permutation tables, are at
    most `δs (1 + n1² (0 + ⋯ + (2L+1)) F / (K - 2(L+1)))` per table. -/
theorem spread_countP {D : Type} {K F n1 NS1 δs : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K)
    (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {iv : Nat}
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) (d : D) (v : Nat → Nat) :
    (K - 2 * (L + 1)) * sumTo (K ^ K) (fun H => indB (permB K H) *
        sumTo NS1 (fun σ => indB (decide (chain1 K inner iv (Com1 d σ :: xs) H (L + 1) = v H)))) ≤
      δs * ((K - 2 * (L + 1)) * sumTo (K ^ K) (fun H => indB (permB K H)) +
        n1 * n1 * (sumTo (2 * (L + 1)) (fun j => j) * F * sumTo (K ^ K) (fun H => indB (permB K H)))) := by
  have pt : ∀ H, indB (permB K H) * sumTo NS1 (fun σ => indB (decide (chain1 K inner iv (Com1 d σ :: xs) H (L + 1) = v H))) ≤
      δs * (indB (permB K H) + indB (permB K H) * pairsEq n1 (fun c => chain1 K inner iv (c :: xs) H (L + 1))) := fun H => by
    have h := spread_pairs Com1 hr1 hsp1 (fun c => chain1 K inner iv (c :: xs) H (L + 1)) d (v H)
    calc indB (permB K H) * sumTo NS1 (fun σ => indB (decide (chain1 K inner iv (Com1 d σ :: xs) H (L + 1) = v H)))
        ≤ indB (permB K H) * (δs * (1 + pairsEq n1 (fun c => chain1 K inner iv (c :: xs) H (L + 1)))) :=
          Nat.mul_le_mul_left _ h
      _ = δs * (indB (permB K H) + indB (permB K H) * pairsEq n1 (fun c => chain1 K inner iv (c :: xs) H (L + 1))) := by
          rw [Nat.mul_left_comm, Nat.mul_add, Nat.mul_one]
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => pt H))) ?_
  rw [← sumTo_mul, sumTo_add, Nat.mul_left_comm, Nat.mul_add]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.le_refl _) (pairs_countP hK inner hin κ hF hpk hd xs L))

/-- **First commitments below the rate absorb at distinct positions**: at
    `two_meet_satPT`'s instance, `hd` holds for `n1 ≤ R1`. -/
theorem spread_satPT {R1 R2 C n1 : Nat} (hn : n1 ≤ R1) (iv : Nat) :
    ∀ a b, a < n1 → b < n1 → a ≠ b →
      a % R1 + R1 * ((iv / R1) % (R2 * C)) ≠ b % R1 + R1 * ((iv / R1) % (R2 * C)) := by
  intro a b ha hb hab e
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha hn), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb hn)] at e
  exact hab (Nat.add_right_cancel e)

/-! ### Every later transcript at one table: a union bound -/

theorem chain1_congr (K : Nat) (inner : Nat → Nat → Nat) (s : Nat) (xs ys : List Nat) (H : Nat) :
    ∀ j, (∀ i, i < j → xs.getD i 0 = ys.getD i 0) → chain1 K inner s xs H j = chain1 K inner s ys H j
  | 0, _ => rfl
  | j + 1, h => by
    show rget K (inner (chain1 K inner s xs H j) (xs.getD j 0)) H = rget K (inner (chain1 K inner s ys H j) (ys.getD j 0)) H
    rw [chain1_congr K inner s xs ys H j (fun i hi => h i (Nat.lt_succ_of_lt hi)), h j (Nat.lt_succ_self j)]

/-- The `i`-th list of `L` blocks below `X`: the digits of `i`. -/
def xsOf (X L i : Nat) : List Nat := (List.range L).map (fun m => rget X m i)

theorem xsOf_getD (X L i m : Nat) (hm : m < L) : (xsOf X L i).getD m 0 = rget X m i := by
  unfold xsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]; rfl

/-- **Every block list below `X` is one of the `X^L`** on its first `L`
    blocks. -/
theorem xsOf_cover {X L : Nat} (hX : 0 < X) (xs : List Nat) (hxs : ∀ i, i < L → xs.getD i 0 < X) :
    ∃ i, i < X ^ L ∧ ∀ m, m < L → xs.getD m 0 = (xsOf X L i).getD m 0 :=
  ⟨tab X (fun m => xs.getD m 0) L, tab_lt L _ hxs, fun m hm => by
    rw [xsOf_getD X L _ m hm, rget_tab hX L _ hxs m hm]⟩

/-- The meeting pairs summed over all `X^L` lists of later blocks. -/
def pairsAll (K : Nat) (inner : Nat → Nat → Nat) (iv n1 X L H : Nat) : Nat :=
  sumTo (X ^ L) (fun i => pairsEq n1 (fun c => chain1 K inner iv (c :: xsOf X L i) H (L + 1)))

/-- **`hφsp` at every table, in its exact form**: the index the overwrite
    sponge's state after the first commitment `m % n1` and `L` later blocks
    `enc (m / n1) w`, each below `X`; at the table `H` at most
    `δs (1 + pairsAll)` salts reach any `v`, for every `d`, `rest` and `w`. -/
theorem hφsp_sponge {D W : Type} {K NS1 n1 δs X L : Nat} (hX : 0 < X) (inner : Nat → Nat → Nat) (iv : Nat)
    (enc : Nat → W → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) (H : Nat) :
    ∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        (chain1 K inner iv (((Com1 d σ1 + n1 * rest) % n1) :: enc ((Com1 d σ1 + n1 * rest) / n1) w) H (L + 1) = v))) ≤
      δs * (1 + pairsAll K inner iv n1 X L H) := by
  intro d rest w v
  have hn1 : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (hr1 d 0)
  have em : ∀ σ1, (Com1 d σ1 + n1 * rest) % n1 = Com1 d σ1 ∧ (Com1 d σ1 + n1 * rest) / n1 = rest := fun σ1 =>
    ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hr1 d σ1)],
     by rw [Nat.add_mul_div_left _ _ hn1, Nat.div_eq_of_lt (hr1 d σ1), Nat.zero_add]⟩
  obtain ⟨i, hi, hag⟩ := xsOf_cover hX (enc rest w) (henc rest w)
  have hch : ∀ c, chain1 K inner iv (c :: enc rest w) H (L + 1) = chain1 K inner iv (c :: xsOf X L i) H (L + 1) :=
    fun c => chain1_congr K inner iv _ _ H (L + 1) (fun j hj => by
      cases j with
      | zero => rfl
      | succ j => exact hag j (Nat.lt_of_succ_lt_succ hj))
  have e : ∀ σ1, chain1 K inner iv (((Com1 d σ1 + n1 * rest) % n1) :: enc ((Com1 d σ1 + n1 * rest) / n1) w) H (L + 1) =
      (fun c => chain1 K inner iv (c :: xsOf X L i) H (L + 1)) (Com1 d σ1) := fun σ1 => by
    rw [(em σ1).1, (em σ1).2, hch]
  rw [sumTo_congr _ (fun σ1 _ => by rw [e σ1])]
  refine Nat.le_trans (spread_pairs Com1 hr1 hsp1 (fun c => chain1 K inner iv (c :: xsOf X L i) H (L + 1)) d v) (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ 1))
  exact le_sumTo (fun i => pairsEq n1 (fun c => chain1 K inner iv (c :: xsOf X L i) H (L + 1))) _ hi

/-- **The table's `δs` averaged over a uniform permutation**: summed over the
    permutation tables, `pairsAll` is at most
    `X^L n1² (0 + ⋯ + (2L+1)) F / (K - 2(L+1))` per table, a union over the
    `X^L` later block lists. -/
theorem pairsAll_countP {K F n1 X L : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K)
    (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {iv : Nat}
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) :
    (K - 2 * (L + 1)) * sumTo (K ^ K) (fun H => indB (permB K H) * pairsAll K inner iv n1 X L H) ≤
      X ^ L * (n1 * n1 * (sumTo (2 * (L + 1)) (fun j => j) * F * sumTo (K ^ K) (fun H => indB (permB K H)))) := by
  unfold pairsAll
  have e : sumTo (K ^ K) (fun H => indB (permB K H) * sumTo (X ^ L)
        (fun i => pairsEq n1 (fun c => chain1 K inner iv (c :: xsOf X L i) H (L + 1)))) =
      sumTo (X ^ L) (fun i => sumTo (K ^ K) (fun H => indB (permB K H) *
        pairsEq n1 (fun c => chain1 K inner iv (c :: xsOf X L i) H (L + 1)))) := by
    rw [sumTo_congr _ (fun H _ => sumTo_mul _ _ (X ^ L))]
    exact sumTo_exch _ (X ^ L) (K ^ K)
  rw [e, sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun i _ => pairs_countP hK inner hin κ hF hpk hd (xsOf X L i) L)) ?_
  rw [sumTo_const]; exact Nat.le_refl _

/-- **`SudChallenger`'s two spread hypotheses at every table**: with the
    index `φ m w` the overwrite sponge's state over `m % n1` and
    `enc (m / n1) w`, the table's `δs' = δs (1 + pairsAll)` meets `hsp1` and
    `hφsp` exactly as `sudFS4T_hspS` and `sud_interleaveS` take them. -/
theorem sponge_hsp {D W : Type} {K NS1 n1 δs X L : Nat} (hX : 0 < X) (inner : Nat → Nat → Nat) (iv : Nat)
    (enc : Nat → W → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) (H : Nat) :
    (∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs * (1 + pairsAll K inner iv n1 X L H)) ∧
      (∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        ((fun m w => chain1 K inner iv ((m % n1) :: enc (m / n1) w) H (L + 1)) (Com1 d σ1 + n1 * rest) w = v))) ≤
        δs * (1 + pairsAll K inner iv n1 X L H)) :=
  ⟨fun d v => Nat.le_trans (hsp1 d v) (Nat.le_trans (Nat.le_of_eq (Nat.mul_one δs).symm)
      (Nat.mul_le_mul_left _ (Nat.le_add_right 1 _))),
   hφsp_sponge hX inner iv enc henc Com1 hr1 hsp1 H⟩

/-- **The table's `δs'` averaged over a uniform permutation**: at most
    `δs (1 + X^L n1² (0 + ⋯ + (2L+1)) F / (K - 2(L+1)))` per table. -/
theorem sponge_δs_countP {K F n1 X L δs : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K)
    (κ : Nat → Nat) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk : ∀ x s s', inner s x = inner s' x → κ s = κ s') {iv : Nat}
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) :
    (K - 2 * (L + 1)) * sumTo (K ^ K) (fun H => indB (permB K H) * (δs * (1 + pairsAll K inner iv n1 X L H))) ≤
      δs * ((K - 2 * (L + 1)) * sumTo (K ^ K) (fun H => indB (permB K H)) +
        X ^ L * (n1 * n1 * (sumTo (2 * (L + 1)) (fun j => j) * F * sumTo (K ^ K) (fun H => indB (permB K H))))) := by
  have pt : ∀ H, indB (permB K H) * (δs * (1 + pairsAll K inner iv n1 X L H)) =
      δs * (indB (permB K H) + indB (permB K H) * pairsAll K inner iv n1 X L H) := fun H => by
    rw [Nat.mul_left_comm, Nat.mul_add, Nat.mul_one]
  rw [sumTo_congr _ (fun H _ => pt H), ← sumTo_mul, sumTo_add, Nat.mul_left_comm, Nat.mul_add]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.le_refl _) (pairsAll_countP hK inner hin κ hF hpk hd))

end Circuit
