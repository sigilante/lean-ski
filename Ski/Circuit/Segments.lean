import Ski.Circuit.Field

/-!
# Counting restarts

A sequence of bits `f`, its running count `cntS f r` (the ones before row
`r`), and the row of the `j`-th one (`endRow`): the facts the composed
circuit's segment counter needs.
-/

namespace Circuit

/-- The ones of `f` before row `r`. -/
def cntS (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => cntS f r + f r

theorem cntS_le (f : Nat → Nat) (hf : ∀ r, f r ≤ 1) : ∀ r, cntS f r ≤ r
  | 0 => Nat.le_refl _
  | r + 1 => by
    show cntS f r + f r ≤ r + 1
    have := cntS_le f hf r
    have := hf r
    omega

theorem cntS_mono (f : Nat → Nat) {a : Nat} : ∀ {b : Nat}, a ≤ b → cntS f a ≤ cntS f b
  | 0, h => by rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | b + 1, h => by
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · show cntS f a ≤ cntS f b + f b
      exact Nat.le_trans (cntS_mono f (Nat.le_of_lt_succ h')) (Nat.le_add_right _ _)
    · rw [Nat.le_antisymm h h']; exact Nat.le_refl _

/-- Every count below the total is reached at a one. -/
theorem cntS_hit (f : Nat → Nat) (hf : ∀ r, f r ≤ 1) : ∀ L j, j < cntS f L → ∃ r, r < L ∧ cntS f r = j ∧ f r = 1
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | L + 1, j, h => by
    change j < cntS f L + f L at h
    rcases Nat.lt_or_ge j (cntS f L) with h' | h'
    · obtain ⟨r, hr, e, hf1⟩ := cntS_hit f hf L j h'
      exact ⟨r, Nat.lt_succ_of_lt hr, e, hf1⟩
    · have := hf L
      exact ⟨L, Nat.lt_succ_self L, by omega, by omega⟩

/-- A one's count names it. -/
theorem cntS_inj (f : Nat → Nat) {a b : Nat} (ha : f a = 1) (hb : f b = 1) (e : cntS f a = cntS f b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := cntS_mono f (Nat.succ_le_of_lt h)
    change cntS f a + f a ≤ cntS f b at this
    omega
  · exact h
  · have := cntS_mono f (Nat.succ_le_of_lt h)
    change cntS f b + f b ≤ cntS f a at this
    omega

/-- The row of the `j`-th one below `L`, or `L` itself for the last
    segment. -/
def endRow (f : Nat → Nat) (L n j : Nat) : Nat :=
  if j + 1 < n then ((List.range L).find? (fun r => f r == 1 && cntS f r == j)).getD 0 else L

theorem endRow_spec (f : Nat → Nat) (hf : ∀ r, f r ≤ 1) {L n j : Nat} (hn : cntS f L = n - 1) (hj : j + 1 < n) :
    endRow f L n j < L ∧ f (endRow f L n j) = 1 ∧ cntS f (endRow f L n j) = j := by
  obtain ⟨r, hr, e, hf1⟩ := cntS_hit f hf L j (by omega)
  have hs : ((List.range L).find? (fun r => f r == 1 && cntS f r == j)).isSome = true :=
    List.find?_isSome.2 ⟨r, List.mem_range.2 hr, by rw [Bool.and_eq_true]; exact ⟨beq_iff_eq.2 hf1, beq_iff_eq.2 e⟩⟩
  cases hq : (List.range L).find? (fun r => f r == 1 && cntS f r == j) with
  | none => rw [hq] at hs; cases hs
  | some q =>
    have hp := List.find?_some hq
    have hm := List.mem_range.1 (List.mem_of_find?_eq_some hq)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    unfold endRow
    rw [if_pos hj, hq]
    exact ⟨hm, hp.1, hp.2⟩

theorem endRow_last (f : Nat → Nat) (L n : Nat) (hn : 0 < n) : endRow f L n (n - 1) = L := by
  unfold endRow; rw [if_neg (by omega)]

/-- The ends increase. -/
theorem endRow_mono (f : Nat → Nat) (hf : ∀ r, f r ≤ 1) {L n : Nat} (hn : cntS f L = n - 1) :
    ∀ j, j + 1 < n → endRow f L n j < endRow f L n (j + 1) := by
  intro j hj
  obtain ⟨a1, a2, a3⟩ := endRow_spec f hf hn hj
  by_cases hj2 : j + 2 < n
  · obtain ⟨b1, b2, b3⟩ := endRow_spec f hf hn hj2
    rcases Nat.lt_or_ge (endRow f L n j) (endRow f L n (j + 1)) with h | h
    · exact h
    · have := cntS_mono f h
      omega
  · have e : j + 1 = n - 1 := by omega
    rw [e, endRow_last f L n (by omega)]
    exact a1

/-- A one below `L` is some segment's end. -/
theorem endRow_of_one (f : Nat → Nat) (hf : ∀ r, f r ≤ 1) {L n i : Nat} (hn : cntS f L = n - 1) (hi : i < L)
    (h1 : f i = 1) : ∃ j, j + 1 < n ∧ endRow f L n j = i := by
  have hc : cntS f i + 1 ≤ cntS f L := by
    have := cntS_mono f (Nat.succ_le_of_lt hi)
    change cntS f i + f i ≤ cntS f L at this
    omega
  refine ⟨cntS f i, by omega, ?_⟩
  obtain ⟨_, a2, a3⟩ := endRow_spec f hf hn (j := cntS f i) (by omega)
  exact cntS_inj f a2 h1 a3

end Circuit

namespace Circuit

/-- Whether row `i` is a restart: some segment `j < n - 1` ends there. -/
def isRestart (e : Nat → Nat) (n i : Nat) : Bool := (List.range (n - 1)).any fun j => e j == i

def rsI (e : Nat → Nat) (n : Nat) (i : Nat) : Nat := if isRestart e n i then 1 else 0

theorem rsI_le (e : Nat → Nat) (n i : Nat) : rsI e n i ≤ 1 := by unfold rsI; split <;> decide

theorem isRestart_iff {e : Nat → Nat} {n i : Nat} : isRestart e n i = true ↔ ∃ j, j + 1 < n ∧ e j = i := by
  unfold isRestart
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, by have := List.mem_range.1 hj; omega, beq_iff_eq.1 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, List.mem_range.2 (by omega), beq_iff_eq.2 h⟩

theorem emono_lt {e : Nat → Nat} {n : Nat} (hmono : ∀ j, j + 1 < n → e j < e (j + 1)) :
    ∀ {a b : Nat}, a < b → b < n → e a < e b := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    have hs := hmono b (by omega)
    rcases Nat.lt_or_ge a b with h | h
    · exact Nat.lt_trans (ih h (by omega)) hs
    · rw [show a = b by omega]; exact hs

/-- No restart strictly between consecutive ends, before the first, or
    after the last. -/
theorem rsI_zero {e : Nat → Nat} {n : Nat} {r : Nat} (h : ∀ j, j + 1 < n → e j ≠ r) : rsI e n r = 0 := by
  unfold rsI
  cases hr : isRestart e n r with
  | false => rfl
  | true =>
    obtain ⟨j, hj, e'⟩ := isRestart_iff.1 hr
    exact absurd e' (h j hj)

theorem rsI_one {e : Nat → Nat} {n : Nat} {j : Nat} (hj : j + 1 < n) : rsI e n (e j) = 1 := by
  unfold rsI; rw [isRestart_iff.2 ⟨j, hj, rfl⟩]; rfl

theorem cntS_const {f : Nat → Nat} {a : Nat} : ∀ b, a ≤ b → (∀ r, a ≤ r → r < b → f r = 0) → cntS f b = cntS f a
  | 0, h, _ => by rw [Nat.le_zero.1 h]
  | b + 1, h, hz => by
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · show cntS f b + f b = _
      rw [hz b (by omega) (Nat.lt_succ_self b), Nat.add_zero]
      exact cntS_const b (by omega) (fun r h1 h2 => hz r h1 (by omega))
    · rw [show a = b + 1 by omega]

section

variable {e : Nat → Nat} {n : Nat} (hmono : ∀ j, j + 1 < n → e j < e (j + 1))
include hmono

/-- **The restarts before segment `j`'s end are `j`.** -/
theorem cntS_end : ∀ j, j < n → cntS (rsI e n) (e j) = j
  | 0, hn => by
    rw [cntS_const (a := 0) (e 0) (Nat.zero_le _) (fun r _ hr => rsI_zero (fun j hj h' => by
      have : e 0 ≤ e j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0]; exact Nat.le_refl _
        · exact Nat.le_of_lt (emono_lt hmono h0 (by omega))
      omega))]
    rfl
  | j + 1, hn => by
    have ih := cntS_end j (by omega)
    have hs := hmono j hn
    rw [cntS_const (a := e j + 1) (e (j + 1)) hs (fun r h1 h2 => rsI_zero (fun j' hj' h' => by
      rcases Nat.lt_trichotomy j' j with h | h | h
      · have := emono_lt hmono h (by omega); omega
      · rw [h] at h'; omega
      · rcases Nat.lt_or_ge j' (j + 1) with h'' | h''
        · omega
        · rcases Nat.eq_or_lt_of_le h'' with h3 | h3
          · rw [← h3] at h'; omega
          · have := emono_lt hmono h3 (by omega); omega))]
    show cntS (rsI e n) (e j) + rsI e n (e j) = j + 1
    rw [ih, rsI_one hn]

/-- After the last end, no more restarts. -/
theorem cntS_after (hn : 0 < n) {r : Nat} (hr : e (n - 1) ≤ r) : cntS (rsI e n) r = n - 1 := by
  rw [cntS_const (a := e (n - 1)) r hr (fun r' h1 _ => rsI_zero (fun j hj h' => by
    have := emono_lt hmono (a := j) (b := n - 1) (by omega) (by omega); omega)),
    cntS_end hmono (n - 1) (by omega)]

end

end Circuit
