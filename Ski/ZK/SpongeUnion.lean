import Ski.ZK.SpongeTree

/-!
# Chains that meet saw near-collisions, without domain separation

`SpongeTree` bounds an index's preimage polynomially in the number `L`
of later blocks when every step carries its own tag.  Here a run-wide
charging argument drops that: later blocks need only stay outside the
first commitments' tag.

- **Labels.** Along any run, a query at a repeated position merges its
  chain's label with the position's first visitor's (`labR`,
  `labR_coh`).  The invariant `t + Σ_v0 (labels among v0's visitors - 1) ≤
  fresh near queries + labels` holds query by query (`labR_inv`): a fresh
  query raises a projection's surplus only together with a near query, and
  a merge that
  lowers the label count lowers some projection's visitor labels too,
  because the two chains' previous positions answered alike under `κ`.
  Chains that end at one position therefore made at least `t - 1` fresh
  near queries (`labR_final`).  The counting lemmas are `dcount_merge`,
  `dcount_add` and their kin.
- **The sponge.** With equal positions forcing equal projections whatever
  the blocks (`hpk2`) and first positions never revisited (`hcf`), chains
  that all meet made at least `t - 1` fresh near queries in their joint run
  (`allMeet_near2`; `nearN_runS` identifies the count with `nearN`).
  `hpk2_satPT` meets `hpk2` at the full-width instance.
- **The bounds.** `allMeet_countP2`, `meetM_countP2`, `meet_markov2` and
  the load `loadTU` over later block lists whose tags are nonzero
  (`cf_of_tags`, `preimage_loadTU`, `loadTU_hsp`, `loadTU_countP`), and the
  composite `sud_interleaveLU` with a number for its error
  (`sud_interleaveLUN`).

Size.  The run now has `t (L + 1)` queries; at the overstated point of
`SpongeTree` (`n1 = Kc = X = 2^248`), `E[loadTU]` is about `2^13`, `2^16`,
`2^20`, `2^29` for `L = 1, 3, 10, 100`.

Limits.  First commitments carry tag `0` and later blocks a nonzero tag
(`h0`, `hnz`): the later blocks must never repeat a first commitment's
block, which Plonky3 does not enforce.  The other limits are `SpongeLoad`'s.
`sud_interleaveLUN` needs `maxHeartbeats 6000000`, and says nothing unless
`Kp > t (L + 1)` and `s0 ≥ t`.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-! ### Distinct labels and merging -/

/-- The labels below `t` that some chain `j < t` meeting `P` carries. -/
def present (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) (v : Nat) : Bool :=
  (List.range t).any (fun j => P j && lab j == v)

/-- The number of distinct labels among the chains meeting `P`. -/
def dcount (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) : Nat := sumTo t (fun v => indB (present t lab P v))

/-- Relabel `b` as `a`. -/
def mergeL (lab : Nat → Nat) (a b : Nat) (j : Nat) : Nat := if lab j = b then a else lab j

theorem present_merge (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) {a b : Nat} (hab : a ≠ b) (v : Nat) :
    indB (present t (mergeL lab a b) P v) + indB (decide (v = b)) * indB (present t lab P b) =
      indB (present t lab P v) + indB (decide (v = a)) * indB (present t lab P b && !present t lab P a) := by
  have iff : present t (mergeL lab a b) P v = true ↔
      (present t lab P v = true ∧ v ≠ b) ∨ (v = a ∧ present t lab P b = true) := by
    unfold present mergeL
    rw [List.any_eq_true, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨j, hj, h⟩
      rw [Bool.and_eq_true, beq_iff_eq] at h
      by_cases e : lab j = b
      · rw [if_pos e] at h; exact Or.inr ⟨h.2.symm, j, hj, by rw [Bool.and_eq_true, beq_iff_eq]; exact ⟨h.1, e⟩⟩
      · rw [if_neg e] at h
        exact Or.inl ⟨⟨j, hj, by rw [Bool.and_eq_true, beq_iff_eq]; exact h⟩, fun hv => e (h.2.trans hv)⟩
    · rintro (⟨⟨j, hj, h⟩, hvb⟩ | ⟨hva, j, hj, h⟩)
      · rw [Bool.and_eq_true, beq_iff_eq] at h
        refine ⟨j, hj, ?_⟩
        rw [Bool.and_eq_true, beq_iff_eq, if_neg (fun e => hvb (h.2 ▸ e))]; exact h
      · rw [Bool.and_eq_true, beq_iff_eq] at h
        refine ⟨j, hj, ?_⟩
        rw [Bool.and_eq_true, beq_iff_eq, if_pos h.2]; exact ⟨h.1, hva.symm⟩
  by_cases hva : v = a
  · subst hva
    have hvb : v ≠ b := hab
    rw [decide_eq_false hvb, decide_eq_true rfl]
    cases hp : present t lab P v <;> cases hq : present t lab P b <;>
      cases hm : present t (mergeL lab v b) P v <;> simp_all [indB]
  · rw [decide_eq_false hva]
    by_cases hvb : v = b
    · subst hvb
      rw [decide_eq_true rfl]
      cases hp : present t lab P v <;> cases hm : present t (mergeL lab a v) P v <;> simp_all [indB]
    · rw [decide_eq_false hvb]
      cases hp : present t lab P v <;> cases hm : present t (mergeL lab a b) P v <;> simp_all [indB]

theorem dcount_merge (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) {a b : Nat} (hab : a ≠ b) (ha : a < t) (hb : b < t) :
    dcount t (mergeL lab a b) P + indB (present t lab P b) =
      dcount t lab P + indB (present t lab P b && !present t lab P a) := by
  unfold dcount
  have h := sumTo_congr t (fun v _ => present_merge t lab P hab v)
  rw [sumTo_add, sumTo_add] at h
  have e1 : sumTo t (fun v => indB (decide (v = b)) * indB (present t lab P b)) = indB (present t lab P b) :=
    sumTo_point _ t hb
  have e2 : sumTo t (fun v => indB (decide (v = a)) * indB (present t lab P b && !present t lab P a)) =
      indB (present t lab P b && !present t lab P a) := sumTo_point _ t ha
  rw [e1, e2] at h; exact h

theorem dcount_merge_le (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) {a b : Nat} (hab : a ≠ b) (ha : a < t) (hb : b < t) :
    dcount t (mergeL lab a b) P ≤ dcount t lab P := by
  have h := dcount_merge t lab P hab ha hb
  revert h
  cases present t lab P b <;> cases present t lab P a <;> intro h <;> simp only [indB] at h <;> simp at h <;> omega

theorem dcount_merge_ge (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) {a b : Nat} (hab : a ≠ b) (ha : a < t) (hb : b < t) :
    dcount t lab P ≤ dcount t (mergeL lab a b) P + 1 := by
  have h := dcount_merge t lab P hab ha hb
  revert h
  cases present t lab P b <;> cases present t lab P a <;> intro h <;> simp only [indB] at h <;> simp at h <;> omega

theorem dcount_merge_both (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) {a b : Nat} (hab : a ≠ b) (ha : a < t) (hb : b < t)
    (hpa : present t lab P a = true) (hpb : present t lab P b = true) :
    dcount t (mergeL lab a b) P + 1 = dcount t lab P := by
  have h := dcount_merge t lab P hab ha hb
  rw [hpa, hpb] at h; simpa [indB] using h

/-- Adding one chain `j0` to `P` adds at most one label, and none if a
    chain of `P` already carries `j0`'s. -/
theorem dcount_add (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) {j0 : Nat} (hj0 : j0 < t) (hl : lab j0 < t) :
    dcount t lab (fun j => P j || j == j0) ≤ dcount t lab P + indB (!present t lab P (lab j0)) := by
  unfold dcount
  have pt : ∀ v, indB (present t lab (fun j => P j || j == j0) v) ≤
      indB (present t lab P v) + indB (decide (v = lab j0)) * indB (!present t lab P (lab j0)) := fun v => by
    cases hp : present t lab P v
    · cases hq : present t lab (fun j => P j || j == j0) v
      · exact Nat.zero_le _
      · obtain ⟨j, hj, h⟩ := List.any_eq_true.1 hq
        rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
        rcases h with ⟨h1 | h1, h2⟩
        · exfalso
          have : present t lab P v = true := List.any_eq_true.2 ⟨j, hj, by rw [Bool.and_eq_true, beq_iff_eq]; exact ⟨h1, h2⟩⟩
          rw [hp] at this; exact Bool.noConfusion this
        · subst h1
          rw [h2, hp, decide_eq_true rfl]; simp [indB]
    · exact Nat.le_trans (indB_le _) (by simp [indB])
  refine Nat.le_trans (sumTo_mono _ (fun v _ => pt v)) ?_
  rw [sumTo_add, sumTo_point _ t hl]
  exact Nat.le_refl _

theorem dcount_add_eq (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) {j0 : Nat}
    (hold : present t lab P (lab j0) = true) :
    dcount t lab (fun j => P j || j == j0) = dcount t lab P := by
  unfold dcount
  refine sumTo_congr _ (fun v _ => ?_)
  congr 1
  cases hp : present t lab P v
  · cases hq : present t lab (fun j => P j || j == j0) v
    · rfl
    · exfalso
      obtain ⟨j, hj, h⟩ := List.any_eq_true.1 hq
      rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
      rcases h with ⟨h1 | h1, h2⟩
      · have : present t lab P v = true := List.any_eq_true.2 ⟨j, hj, by rw [Bool.and_eq_true, beq_iff_eq]; exact ⟨h1, h2⟩⟩
        rw [hp] at this; exact Bool.noConfusion this
      · subst h1; rw [h2] at hold; rw [hp] at hold; exact Bool.noConfusion hold
  · obtain ⟨j, hj, h⟩ := List.any_eq_true.1 hp
    rw [Bool.and_eq_true, beq_iff_eq] at h
    exact List.any_eq_true.2 ⟨j, hj, by rw [Bool.and_eq_true, Bool.or_eq_true]; exact ⟨Or.inl h.1, beq_iff_eq.2 h.2⟩⟩

/-! ### Labels along a run -/

section Run
variable (t : Nat) (pos ch kap : Nat → Nat)

/-- Query `T` repeats an earlier position. -/
def oldB (T : Nat) : Bool := (List.range T).any (fun τ => pos τ == pos T)

/-- The first earlier query at query `T`'s position. -/
def firstOld (T : Nat) : Nat := ((List.range T).find? (fun τ => pos τ == pos T)).getD 0

/-- Chains' labels after `T` queries: a repeated position merges the
    labels of its chain and of the position's first visitor. -/
def labR : Nat → Nat → Nat
  | 0, j => j
  | T + 1, j => if oldB pos T = true
      then mergeL (labR T) (labR T (ch T)) (labR T (ch (firstOld pos T))) j else labR T j

/-- Chain `j` visited a position whose answer projects to `v0` before `T`. -/
def visB (T v0 j : Nat) : Bool := (List.range T).any (fun τ => ch τ == j && kap τ == v0)

/-- Query `τ` is fresh and its answer projects as an earlier one's. -/
def nearInc (τ : Nat) : Bool := !oldB pos τ && (List.range τ).any (fun τ' => kap τ' == kap τ)

theorem firstOld_spec {T : Nat} (h : oldB pos T = true) : firstOld pos T < T ∧ pos (firstOld pos T) = pos T := by
  unfold firstOld
  unfold oldB at h
  cases hf : (List.range T).find? (fun τ => pos τ == pos T) with
  | none => rw [List.find?_eq_none] at hf
            obtain ⟨τ, hτ, e⟩ := List.any_eq_true.1 h
            exact absurd e (hf τ hτ)
  | some τ =>
    have hm := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    exact ⟨List.mem_range.1 hm, beq_iff_eq.1 he⟩

theorem oldB_spec {T τ : Nat} (hτ : τ < T) (e : pos τ = pos T) : oldB pos T = true :=
  List.any_eq_true.2 ⟨τ, List.mem_range.2 hτ, beq_iff_eq.2 e⟩

theorem labR_lt (hch : ∀ τ, ch τ < t) : ∀ T j, j < t → labR pos ch T j < t
  | 0, j, hj => hj
  | T + 1, j, hj => by
    show (if oldB pos T = true then mergeL (labR pos ch T) (labR pos ch T (ch T)) (labR pos ch T (ch (firstOld pos T))) j
      else labR pos ch T j) < t
    split
    · unfold mergeL; split
      · exact labR_lt hch T _ (hch _)
      · exact labR_lt hch T j hj
    · exact labR_lt hch T j hj

/-- **Coherence**: two earlier queries at one position leave their chains
    one label. -/
theorem labR_coh : ∀ T τ1 τ2, τ1 < T → τ2 < T → pos τ1 = pos τ2 → labR pos ch T (ch τ1) = labR pos ch T (ch τ2)
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | T + 1, τ1, τ2, h1, h2, e => by
    have mrg : ∀ (lab : Nat → Nat) (a b j1 j2 : Nat), lab j1 = lab j2 → mergeL lab a b j1 = mergeL lab a b j2 :=
      fun lab a b j1 j2 h => by unfold mergeL; rw [h]
    -- the new query's chain and the first visitor share a label after the merge
    have newq : ∀ τ, τ < T → pos τ = pos T → oldB pos T = true →
        mergeL (labR pos ch T) (labR pos ch T (ch T)) (labR pos ch T (ch (firstOld pos T))) (ch τ) =
          mergeL (labR pos ch T) (labR pos ch T (ch T)) (labR pos ch T (ch (firstOld pos T))) (ch T) := by
      intro τ hτ eτ hold
      obtain ⟨hf, ef⟩ := firstOld_spec pos hold
      have : labR pos ch T (ch τ) = labR pos ch T (ch (firstOld pos T)) := labR_coh T τ (firstOld pos T) hτ hf (eτ.trans ef.symm)
      unfold mergeL
      rw [if_pos this]
      by_cases h' : labR pos ch T (ch T) = labR pos ch T (ch (firstOld pos T))
      · rw [if_pos h']
      · rw [if_neg h']
    show (if oldB pos T = true then _ else _) = (if oldB pos T = true then _ else _)
    rcases Nat.lt_or_ge τ1 T with a1 | a1 <;> rcases Nat.lt_or_ge τ2 T with a2 | a2
    · have := labR_coh T τ1 τ2 a1 a2 e
      split
      · exact mrg _ _ _ _ _ this
      · exact this
    · have e2 : τ2 = T := by omega
      subst e2
      rw [if_pos (oldB_spec pos a1 e), if_pos (oldB_spec pos a1 e)]
      exact newq τ1 a1 e (oldB_spec pos a1 e)
    · have e1 : τ1 = T := by omega
      subst e1
      rw [if_pos (oldB_spec pos a2 e.symm), if_pos (oldB_spec pos a2 e.symm)]
      exact (newq τ2 a2 e.symm (oldB_spec pos a2 e.symm)).symm
    · have e1 : τ1 = T := by omega
      have e2 : τ2 = T := by omega
      subst e1; subst e2; rfl

end Run

section Inv
variable (t : Nat) (pos ch kap : Nat → Nat)

theorem visB_succ (T v0 j : Nat) : visB ch kap (T + 1) v0 j = (visB ch kap T v0 j || (ch T == j && kap T == v0)) := by
  unfold visB; rw [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem visB_add (T : Nat) : (fun j => visB ch kap (T + 1) (kap T) j) = (fun j => visB ch kap T (kap T) j || j == ch T) := by
  funext j; rw [visB_succ]
  cases h : (ch T == j)
  · have : (j == ch T) = false := by
      cases h' : (j == ch T)
      · rfl
      · rw [beq_iff_eq] at h'; rw [h', beq_iff_eq.2 rfl] at h; exact absurd h Bool.noConfusion
    rw [this]; rfl
  · rw [beq_iff_eq] at h; rw [h, beq_iff_eq.2 rfl, beq_iff_eq.2 rfl]; rfl

theorem visB_other (T v0 : Nat) (hv : kap T ≠ v0) : (fun j => visB ch kap (T + 1) v0 j) = (fun j => visB ch kap T v0 j) := by
  funext j; rw [visB_succ]
  have : (kap T == v0) = false := by
    cases h : (kap T == v0)
    · rfl
    · exact absurd (beq_iff_eq.1 h) hv
  rw [this, Bool.and_false, Bool.or_false]

theorem dcount_id (t : Nat) : dcount t (fun j => j) (fun _ => true) = t := by
  unfold dcount
  refine Eq.trans (sumTo_congr _ (fun v hv => ?_)) (Eq.trans (sumTo_const 1 t) (Nat.mul_one t))
  show indB (present t (fun j => j) (fun _ => true) v) = 1
  have : present t (fun j => j) (fun _ => true) v = true :=
    List.any_eq_true.2 ⟨v, List.mem_range.2 hv, by rw [Bool.true_and]; exact beq_iff_eq.2 rfl⟩
  rw [this]; rfl

theorem dcount_none (t : Nat) (lab : Nat → Nat) : dcount t lab (fun _ => false) = 0 := by
  unfold dcount
  refine Eq.trans (sumTo_congr _ (fun v _ => ?_)) (Eq.trans (sumTo_const 0 t) (Nat.mul_zero t))
  show indB (present t lab (fun _ => false) v) = 0
  have : present t lab (fun _ => false) v = false := List.any_eq_false.2 (fun j _ => by rw [Bool.false_and]; exact Bool.noConfusion)
  rw [this]; rfl

theorem present_of (t : Nat) (lab : Nat → Nat) (P : Nat → Bool) {j : Nat} (hj : j < t) (hP : P j = true) :
    present t lab P (lab j) = true :=
  List.any_eq_true.2 ⟨j, List.mem_range.2 hj, by rw [hP, Bool.true_and]; exact beq_iff_eq.2 rfl⟩

theorem visB_of {T τ : Nat} (hτ : τ < T) : visB ch kap T (kap τ) (ch τ) = true :=
  List.any_eq_true.2 ⟨τ, List.mem_range.2 hτ, by rw [beq_iff_eq.2 rfl, beq_iff_eq.2 rfl]; rfl⟩

theorem mergeL_self (lab : Nat → Nat) (a : Nat) : mergeL lab a a = lab := by
  funext j; unfold mergeL; split
  · next h => exact h.symm
  · rfl

/-- **The invariant**: `t` plus each projection's surplus of labels among
    its visitors is at most the fresh near queries plus the labels. -/
theorem labR_inv {Kc : Nat} (hch : ∀ τ, ch τ < t) (hkap : ∀ τ, kap τ < Kc)
    (hkp : ∀ τ τ', pos τ = pos τ' → kap τ = kap τ')
    (Tend : Nat) (hprev : ∀ T τ0, T < Tend → τ0 < T → pos τ0 = pos T → labR pos ch T (ch T) ≠ labR pos ch T (ch τ0) →
      ∃ τ1 τ2, τ1 < T ∧ τ2 < T ∧ ch τ1 = ch T ∧ ch τ2 = ch τ0 ∧ kap τ1 = kap τ2) :
    ∀ T, T ≤ Tend → t + sumTo Kc (fun v0 => dcount t (labR pos ch T) (visB ch kap T v0) - 1) ≤
      sumTo T (fun τ => indB (nearInc pos kap τ)) + dcount t (labR pos ch T) (fun _ => true)
  | 0, _ => by
    have hv : ∀ v0, visB ch kap 0 v0 = fun _ => false := fun v0 => rfl
    show t + sumTo Kc (fun v0 => dcount t (fun j => j) (visB ch kap 0 v0) - 1) ≤ 0 + dcount t (fun j => j) (fun _ => true)
    rw [dcount_id, Nat.zero_add]
    refine Nat.le_of_eq (Eq.trans (congrArg (t + ·) (Eq.trans (sumTo_congr _ (fun v0 _ => by
      rw [hv v0, dcount_none])) (Eq.trans (sumTo_const 0 Kc) (Nat.mul_zero Kc)))) (Nat.add_zero t))
  | T + 1, hT => by
    have ih := labR_inv hch hkap hkp Tend hprev T (Nat.le_of_succ_le hT)
    have hnear : sumTo (T + 1) (fun τ => indB (nearInc pos kap τ)) =
        sumTo T (fun τ => indB (nearInc pos kap τ)) + indB (nearInc pos kap T) := rfl
    rw [hnear]
    have hlt : ∀ j, j < t → labR pos ch T j < t := fun j hj => labR_lt t pos ch hch T j hj
    cases ho : oldB pos T
    · -- a fresh query: labels unchanged, one visit added
      have hL : labR pos ch (T + 1) = labR pos ch T := by
        funext j; show (if oldB pos T = true then _ else _) = _; rw [ho]; rfl
      rw [hL]
      have pt : ∀ v0, dcount t (labR pos ch T) (visB ch kap (T + 1) v0) - 1 ≤
          (dcount t (labR pos ch T) (visB ch kap T v0) - 1) + indB (decide (v0 = kap T)) * indB (nearInc pos kap T) := by
        intro v0
        by_cases hv : v0 = kap T
        · subst hv
          have e := visB_add ch kap T
          have hadd := dcount_add t (labR pos ch T) (visB ch kap T (kap T)) (hch T) (hlt _ (hch T))
          rw [show visB ch kap (T + 1) (kap T) = fun j => visB ch kap T (kap T) j || j == ch T from e]
          rw [decide_eq_true rfl, show indB true = 1 from rfl, Nat.one_mul]
          cases hex : (List.range T).any (fun τ' => kap τ' == kap T)
          · -- no earlier visitor of this projection
            have hnone : visB ch kap T (kap T) = fun _ => false := by
              funext j
              refine List.any_eq_false.2 (fun τ hτ hb => ?_)
              rw [Bool.and_eq_true] at hb
              have := List.any_eq_false.1 hex τ hτ
              exact this hb.2
            rw [hnone, dcount_none] at hadd ⊢
            have := indB_le (!present t (labR pos ch T) (fun _ => false) (labR pos ch T (ch T)))
            omega
          · have hn : nearInc pos kap T = true := by unfold nearInc; rw [ho, hex]; rfl
            rw [hn, show indB true = 1 from rfl]
            have := indB_le (!present t (labR pos ch T) (visB ch kap T (kap T)) (labR pos ch T (ch T)))
            omega
        · rw [decide_eq_false hv, show indB false = 0 from rfl, Nat.zero_mul, Nat.add_zero]
          rw [show visB ch kap (T + 1) v0 = fun j => visB ch kap T v0 j from visB_other ch kap T v0 (fun e => hv e.symm)]
          exact Nat.le_refl _
      have hs := sumTo_mono Kc (fun v0 _ => pt v0)
      rw [sumTo_add, sumTo_point _ Kc (hkap T)] at hs
      omega
    · -- a repeated query
      obtain ⟨hf, ef⟩ := firstOld_spec pos ho
      have hn : nearInc pos kap T = false := by unfold nearInc; rw [ho]; rfl
      rw [hn, show indB false = 0 from rfl, Nat.add_zero]
      let τ0 := firstOld pos T
      let a := labR pos ch T (ch T)
      let b := labR pos ch T (ch τ0)
      have hL : labR pos ch (T + 1) = mergeL (labR pos ch T) a b := by
        funext j; show (if oldB pos T = true then _ else _) = _; rw [ho]; rfl
      have hk0 : kap τ0 = kap T := hkp _ _ ef
      have vis0 : visB ch kap T (kap T) (ch τ0) = true := by rw [← hk0]; exact visB_of ch kap hf
      by_cases hab : a = b
      · -- same label: nothing merges
        have hL' : labR pos ch (T + 1) = labR pos ch T := by rw [hL, ← hab, mergeL_self]
        rw [hL']
        have pt : ∀ v0, dcount t (labR pos ch T) (visB ch kap (T + 1) v0) = dcount t (labR pos ch T) (visB ch kap T v0) := by
          intro v0
          by_cases hv : v0 = kap T
          · subst hv
            rw [show visB ch kap (T + 1) (kap T) = fun j => visB ch kap T (kap T) j || j == ch T from visB_add ch kap T]
            refine dcount_add_eq t _ _ ?_
            have := present_of t (labR pos ch T) (visB ch kap T (kap T)) (hch τ0) vis0
            show present t (labR pos ch T) (visB ch kap T (kap T)) a = true
            rw [hab]; exact this
          · rw [show visB ch kap (T + 1) v0 = fun j => visB ch kap T v0 j from visB_other ch kap T v0 (fun e => hv e.symm)]
        rw [sumTo_congr _ (fun v0 _ => by rw [pt v0])]
        exact ih
      · -- two labels merge, paid by a projection whose visitors carried both
        obtain ⟨τ1, τ2, h1, h2, c1, c2, k12⟩ := hprev T τ0 (Nat.lt_of_succ_le hT) hf ef hab
        have ha : a < t := hlt _ (hch T)
        have hb : b < t := hlt _ (hch τ0)
        rw [hL]
        have hLmT : (mergeL (labR pos ch T) a b) (ch T) = a := by show (if labR pos ch T (ch T) = b then a else labR pos ch T (ch T)) = a; rw [if_neg hab]
        have hLm0 : (mergeL (labR pos ch T) a b) (ch τ0) = a := by show (if labR pos ch T (ch τ0) = b then a else labR pos ch T (ch τ0)) = a; rw [if_pos rfl]
        have d_eq : ∀ v0, dcount t (mergeL (labR pos ch T) a b) (visB ch kap (T + 1) v0) = dcount t (mergeL (labR pos ch T) a b) (visB ch kap T v0) := by
          intro v0
          by_cases hv : v0 = kap T
          · subst hv
            rw [show visB ch kap (T + 1) (kap T) = fun j => visB ch kap T (kap T) j || j == ch T from visB_add ch kap T]
            refine dcount_add_eq t _ _ ?_
            rw [hLmT]
            have := present_of t (mergeL (labR pos ch T) a b) _ (hch τ0) vis0
            rw [hLm0] at this; exact this
          · rw [show visB ch kap (T + 1) v0 = fun j => visB ch kap T v0 j from visB_other ch kap T v0 (fun e => hv e.symm)]
        let cs := kap τ1
        have pa : present t (labR pos ch T) (visB ch kap T cs) a = true := by
          have := present_of t (labR pos ch T) (visB ch kap T cs) (hch τ1) (visB_of ch kap h1)
          rw [c1] at this; exact this
        have pb : present t (labR pos ch T) (visB ch kap T cs) b = true := by
          have v2 : visB ch kap T cs (ch τ2) = true := by show visB ch kap T (kap τ1) (ch τ2) = true; rw [k12]; exact visB_of ch kap h2
          have := present_of t (labR pos ch T) (visB ch kap T cs) (hch τ2) v2
          rw [c2] at this; exact this
        have both := dcount_merge_both t (labR pos ch T) (visB ch kap T cs) hab ha hb pa pb
        have dpos : 1 ≤ dcount t (mergeL (labR pos ch T) a b) (visB ch kap T cs) := by
          have pr : present t (mergeL (labR pos ch T) a b) (visB ch kap T cs) a = true := by
            have := present_of t (mergeL (labR pos ch T) a b) (visB ch kap T cs) (hch τ1) (visB_of ch kap h1)
            rw [c1, hLmT] at this; exact this
          refine Nat.le_trans (Nat.le_of_eq ?_) (le_sumTo (fun v => indB (present t (mergeL (labR pos ch T) a b) (visB ch kap T cs) v)) t ha)
          rw [pr]; rfl
        have pt : ∀ v0, (dcount t (mergeL (labR pos ch T) a b) (visB ch kap (T + 1) v0) - 1) + indB (decide (v0 = cs)) ≤
            dcount t (labR pos ch T) (visB ch kap T v0) - 1 := by
          intro v0
          rw [d_eq v0]
          by_cases hv : v0 = cs
          · rw [hv, decide_eq_true rfl, show indB true = 1 from rfl]
            have b2 := both
            omega
          · rw [decide_eq_false hv, show indB false = 0 from rfl, Nat.add_zero]
            exact Nat.sub_le_sub_right (dcount_merge_le t _ _ hab ha hb) 1
        have hs := sumTo_mono Kc (fun v0 _ => pt v0)
        rw [sumTo_add] at hs
        have hpt : sumTo Kc (fun v0 => indB (decide (v0 = cs))) = 1 := by
          have := sumTo_point 1 Kc (hkap τ1)
          rw [← this]; exact sumTo_congr _ (fun v0 _ => (Nat.mul_one _).symm)
        rw [hpt] at hs
        have hc := dcount_merge_ge t (labR pos ch T) (fun _ => true) hab ha hb
        omega

end Inv

/-- **Chains whose last queries share a position saw near queries**: if each
    chain `j < t` makes a query before `Tend` at one position `p`, then
    `t ≤ 1 +` the fresh near queries before `Tend`. -/
theorem labR_final (t : Nat) (pos ch kap : Nat → Nat) {Kc : Nat} (hch : ∀ τ, ch τ < t) (hkap : ∀ τ, kap τ < Kc)
    (hkp : ∀ τ τ', pos τ = pos τ' → kap τ = kap τ')
    (Tend p : Nat) (hprev : ∀ T τ0, T < Tend → τ0 < T → pos τ0 = pos T → labR pos ch T (ch T) ≠ labR pos ch T (ch τ0) →
      ∃ τ1 τ2, τ1 < T ∧ τ2 < T ∧ ch τ1 = ch T ∧ ch τ2 = ch τ0 ∧ kap τ1 = kap τ2) (hall : ∀ j, j < t → ∃ τ, τ < Tend ∧ ch τ = j ∧ pos τ = p) :
    t ≤ sumTo Tend (fun τ => indB (nearInc pos kap τ)) + 1 := by
  have hinv := labR_inv t pos ch kap hch hkap hkp Tend hprev Tend (Nat.le_refl _)
  have hc : dcount t (labR pos ch Tend) (fun _ => true) ≤ 1 := by
    refine sum_le_one t (fun v v' _ _ h1 h2 => ?_)
    obtain ⟨j, hj, e⟩ := List.any_eq_true.1 h1
    obtain ⟨j', hj', e'⟩ := List.any_eq_true.1 h2
    rw [Bool.true_and, beq_iff_eq] at e e'
    obtain ⟨τ, hτ, c, pτ⟩ := hall j (List.mem_range.1 hj)
    obtain ⟨τ', hτ', c', pτ'⟩ := hall j' (List.mem_range.1 hj')
    rw [← e, ← e', ← c, ← c']
    exact labR_coh pos ch Tend τ τ' hτ hτ' (pτ.trans pτ'.symm)
  omega

/-! ### The sponge's joint run -/

/-- **The fresh near queries of the joint run are `nearN`'s.** -/
theorem nearN_runS {K : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (κ : Nat → Nat) (iv : Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (xs : List Nat) (H : Nat) :
    ∀ T, nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtS inner iv n1 cf xs) H T) =
      sumTo T (fun τ => indB (nearInc (posS K inner iv n1 cf xs H) (fun τ => κ (rget K (posS K inner iv n1 cf xs H τ) H)) τ))
  | 0 => rfl
  | T + 1 => by
    have ih := nearN_runS hK inner κ iv hn1 cf xs H T
    have hr : runAdp K (nxtS inner iv n1 cf xs) H (T + 1) =
        (posS K inner iv n1 cf xs H T, rget K (posS K inner iv n1 cf xs H T) H) :: runAdp K (nxtS inner iv n1 cf xs) H T := by
      rw [runS_eq K inner iv hn1 cf xs H, runS_eq K inner iv hn1 cf xs H, List.range_succ, List.reverse_append]; rfl
    rw [hr]
    show nearN K _ (runAdp K (nxtS inner iv n1 cf xs) H T) + _ = sumTo T _ + _
    rw [ih]
    congr 2
    have hmem : ∀ q, q ∈ (runAdp K (nxtS inner iv n1 cf xs) H T).map Prod.fst ↔ ∃ τ, τ < T ∧ posS K inner iv n1 cf xs H τ = q := by
      intro q
      rw [runS_eq K inner iv hn1 cf xs H, List.map_map, List.mem_map]
      exact ⟨fun ⟨τ, hτ, e⟩ => ⟨τ, List.mem_range.1 (List.mem_reverse.1 hτ), e⟩,
        fun ⟨τ, hτ, e⟩ => ⟨τ, List.mem_reverse.2 (List.mem_range.2 hτ), e⟩⟩
    have hsnd : ∀ u, u ∈ (runAdp K (nxtS inner iv n1 cf xs) H T).map Prod.snd ↔
        ∃ τ, τ < T ∧ rget K (posS K inner iv n1 cf xs H τ) H = u := by
      intro u
      rw [runS_eq K inner iv hn1 cf xs H, List.map_map, List.mem_map]
      exact ⟨fun ⟨τ, hτ, e⟩ => ⟨τ, List.mem_range.1 (List.mem_reverse.1 hτ), e⟩,
        fun ⟨τ, hτ, e⟩ => ⟨τ, List.mem_reverse.2 (List.mem_range.2 hτ), e⟩⟩
    have e1 : decide (posS K inner iv n1 cf xs H T ∈ (runAdp K (nxtS inner iv n1 cf xs) H T).map Prod.fst) =
        oldB (posS K inner iv n1 cf xs H) T := by
      cases h : oldB (posS K inner iv n1 cf xs H) T
      · refine decide_eq_false (fun hm => ?_)
        obtain ⟨τ, hτ, e⟩ := (hmem _).1 hm
        rw [oldB_spec _ hτ e] at h; exact Bool.noConfusion h
      · obtain ⟨hf, ef⟩ := firstOld_spec _ h
        exact decide_eq_true ((hmem _).2 ⟨_, hf, ef⟩)
    have e2 : decide (rget K (posS K inner iv n1 cf xs H T) H ∈ nearR K (fun a b => decide (κ a = κ b))
          ((runAdp K (nxtS inner iv n1 cf xs) H T).map Prod.snd)) =
        (List.range T).any (fun τ' => κ (rget K (posS K inner iv n1 cf xs H τ') H) == κ (rget K (posS K inner iv n1 cf xs H T) H)) := by
      cases h : (List.range T).any (fun τ' => κ (rget K (posS K inner iv n1 cf xs H τ') H) == κ (rget K (posS K inner iv n1 cf xs H T) H))
      · refine decide_eq_false (fun hm => ?_)
        unfold nearR at hm
        obtain ⟨_, hany⟩ := List.mem_filter.1 hm
        obtain ⟨u, hu, hk⟩ := List.any_eq_true.1 hany
        obtain ⟨τ, hτ, e⟩ := (hsnd u).1 hu
        have := List.any_eq_false.1 h τ (List.mem_range.2 hτ)
        exact this (by rw [e]; exact beq_iff_eq.2 (of_decide_eq_true hk))
      · obtain ⟨τ, hτ, hk⟩ := List.any_eq_true.1 h
        refine decide_eq_true ?_
        unfold nearR
        refine List.mem_filter.2 ⟨List.mem_range.2 (rget_lt hK _ _), List.any_eq_true.2 ⟨_, (hsnd _).2 ⟨τ, List.mem_range.1 hτ, rfl⟩, ?_⟩⟩
        exact decide_eq_true (beq_iff_eq.1 hk)
    unfold nearInc
    rw [e1, e2]

/-- **Chains that all meet saw near-collisions, without domain
    separation**: `n1` chains from distinct first positions (`hd`), equal
    positions forcing equal projections of the states whatever the blocks
    (`hpk2`), first positions never revisited later (`hcf`), all reaching
    one state after `L + 1` absorptions on a permutation table; then their
    joint run has at least `n1 - 1` fresh answers equal under `κ` to an
    earlier one. -/
theorem allMeet_near2 {K Kc : Nat} (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat}
    (hn1 : 0 < n1) (cf : Nat → Nat) (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv (cf a) ≠ inner iv (cf b))
    (xs : List Nat) {H : Nat} (hP : permB K H = true) (L : Nat)
    (hcf : ∀ τ τ', τ' < n1 → n1 ≤ τ → τ < n1 * (L + 1) → posS K inner iv n1 cf xs H τ ≠ posS K inner iv n1 cf xs H τ')
    {v : Nat} (hall : ∀ j, j < n1 → chain1 K inner iv (cf j :: xs) H (L + 1) = v) :
    n1 ≤ 1 + nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtS inner iv n1 cf xs) H (n1 * (L + 1))) := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) (hin 0 0)
  let pos := posS K inner iv n1 cf xs H
  let kap := fun τ => κ (rget K (pos τ) H)
  have step0 : ∀ j, j < n1 → pos j = inner iv (cf j) := fun j hj => by
    have := posS_step K inner iv hn1 cf xs H 0 j hj
    rw [Nat.zero_mul, Nat.zero_add] at this; exact this
  have prevpos : ∀ T, n1 ≤ T → pos T = inner (rget K (pos (T - n1)) H) (xs.getD (T / n1 - 1) 0) := fun T hT => by
    have hj := Nat.mod_lt T hn1
    have hq : 1 ≤ T / n1 := (Nat.le_div_iff_mul_le hn1).2 (by rw [Nat.one_mul]; exact hT)
    have hdm : T = T / n1 * n1 + T % n1 := by rw [Nat.mul_comm]; exact (Nat.div_add_mod T n1).symm
    have e1 : T = (T / n1 - 1 + 1) * n1 + T % n1 := by rw [Nat.sub_add_cancel hq]; exact hdm
    have e2 : T - n1 = (T / n1 - 1) * n1 + T % n1 := by
      have hge : n1 ≤ T / n1 * n1 := by
        calc n1 = 1 * n1 := (Nat.one_mul _).symm
          _ ≤ T / n1 * n1 := Nat.mul_le_mul_right _ hq
      rw [Nat.sub_mul, Nat.one_mul]; omega
    show posS K inner iv n1 cf xs H T = inner (rget K (posS K inner iv n1 cf xs H (T - n1)) H) _
    rw [e2]; conv => lhs; rw [e1]
    exact posS_next K inner iv hn1 cf xs H _ _ hj
  have hfin := labR_final n1 pos (fun τ => τ % n1) kap (fun τ => Nat.mod_lt τ hn1) (fun τ => hκ _)
    (fun τ τ' e => by show κ (rget K (pos τ) H) = κ (rget K (pos τ') H); rw [e])
    (n1 * (L + 1)) (pos (L * n1))
    (fun T τ0 hT hτ0 e _ => by
      rcases Nat.lt_or_ge τ0 n1 with h0 | h0
      · rcases Nat.lt_or_ge T n1 with h1 | h1
        · exfalso
          rw [step0 τ0 h0, step0 T h1] at e
          exact hd τ0 T h0 h1 (Nat.ne_of_lt hτ0) e
        · exact absurd e.symm (hcf T τ0 h0 h1 hT)
      · have h1 : n1 ≤ T := Nat.le_trans h0 (Nat.le_of_lt hτ0)
        refine ⟨T - n1, τ0 - n1, by omega, by omega, ?_, ?_, ?_⟩
        · show (T - n1) % n1 = T % n1
          conv => rhs; rw [← Nat.sub_add_cancel h1]
          rw [Nat.add_mod_right]
        · show (τ0 - n1) % n1 = τ0 % n1
          conv => rhs; rw [← Nat.sub_add_cancel h0]
          rw [Nat.add_mod_right]
        · show κ (rget K (pos (T - n1)) H) = κ (rget K (pos (τ0 - n1)) H)
          rw [prevpos T h1, prevpos τ0 h0] at e
          exact (hpk2 _ _ _ _ e).symm)
    (fun j hj => ⟨L * n1 + j, by
      calc L * n1 + j < L * n1 + n1 := Nat.add_lt_add_left hj _
        _ = n1 * (L + 1) := by rw [Nat.mul_comm n1, Nat.succ_mul],
      by show (L * n1 + j) % n1 = j; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj], by
      refine permB_inj hP (hin _ _) (hin _ _) ?_
      show rget K (posS K inner iv n1 cf xs H (L * n1 + j)) H = rget K (posS K inner iv n1 cf xs H (L * n1)) H
      rw [rget_posS, rget_posS]
      have a1 : (L * n1 + j) % n1 = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      have a2 : (L * n1 + j) / n1 = L := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn1, Nat.div_eq_of_lt hj, Nat.zero_add]
      have b1 : (L * n1) % n1 = 0 := Nat.mul_mod_left _ _
      have b2 : (L * n1) / n1 = L := Nat.mul_div_cancel _ hn1
      rw [a1, a2, b1, b2, hall j hj, hall 0 hn1]⟩)
  rw [nearN_runS hK inner κ iv hn1 cf xs H, Nat.add_comm]
  exact hfin

/-- **Chains that all meet are rare, without domain separation**: `n1`
    chains from distinct first positions, first positions never revisited,
    all reach one state after `L + 1` absorptions on at most
    `((0 + ⋯ + (n1 (L+1) - 1)) F)^(n1-1) / ((n1-1)! (K - n1 (L+1))^(n1-1))`
    of the permutation tables (`allMeet_near2`, `nearN_tail`). -/
theorem allMeet_countP2 {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn1 : 0 < n1)
    (cf : Nat → Nat) (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv (cf a) ≠ inner iv (cf b)) (xs : List Nat) (L : Nat)
    (hcf : ∀ H τ τ', τ' < n1 → n1 ≤ τ → τ < n1 * (L + 1) → posS K inner iv n1 cf xs H τ ≠ posS K inner iv n1 cf xs H τ') :
    fact (n1 - 1) * ((K - n1 * (L + 1)) ^ (n1 - 1) * sumTo (K ^ K) (fun H => indB (permB K H &&
        (List.range n1).all (fun j => chain1 K inner iv (cf j :: xs) H (L + 1) == chain1 K inner iv (cf 0 :: xs) H (L + 1))))) ≤
      (sumTo (n1 * (L + 1)) (fun j => j) * F) ^ (n1 - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hnx : ∀ l, nxtS inner iv n1 cf xs l < K := fun l => by unfold nxtS; split <;> exact hin _ _
  refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (sumTo_mono _ (fun H _ => ?_))))
    (nearN_tail hK (fun a b => decide (κ a = κ b)) (rel_symm κ) (fib_rel κ hF) (nxtS inner iv n1 cf xs) hnx (n1 * (L + 1)) (n1 - 1))
  cases hP : permB K H
  · exact Nat.zero_le _
  cases ha : (List.range n1).all (fun j => chain1 K inner iv (cf j :: xs) H (L + 1) == chain1 K inner iv (cf 0 :: xs) H (L + 1))
  · exact Nat.zero_le _
  · have hall : ∀ j, j < n1 → chain1 K inner iv (cf j :: xs) H (L + 1) = chain1 K inner iv (cf 0 :: xs) H (L + 1) :=
      fun j hj => beq_iff_eq.1 (List.all_eq_true.1 ha j (List.mem_range.2 hj))
    have hm := allMeet_near2 inner hin κ hκ hpk2 iv hn1 cf hd xs hP L (hcf H) hall
    have : n1 - 1 ≤ nearN K (fun a b => decide (κ a = κ b)) (runAdp K (nxtS inner iv n1 cf xs) H (n1 * (L + 1))) := by omega
    rw [decide_eq_true this]; exact Nat.le_refl _

/-- **Meeting tuples averaged over a uniform permutation, without domain
    separation**: first positions never revisited (`hcfC`), `(t-1)! (K - t (L+1))^(t-1)` times
    the summed `meetM` is at most `n1^t ((0 + ⋯ + (t (L+1) - 1)) F)^(t-1)` per
    permutation table. -/
theorem meetM_countP2 {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (hcfC : ∀ H c c' i, c < n1 → c' < n1 → 1 ≤ i → i ≤ L →
      inner (chain1 K inner iv (c :: xs) H i) ((c :: xs).getD i 0) ≠ inner iv c')
    {t : Nat} (ht : 0 < t) :
    fact (t - 1) * ((K - t * (L + 1)) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H)) ≤
      n1 ^ t * ((sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have e : sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) =
      sumTo (n1 ^ t) (fun a => sumTo (K ^ K) (fun H => indB (permB K H) * indB (injT n1 t a &&
        (List.range t).all (fun j => chain1 K inner iv (rget n1 j a :: xs) H (L + 1) ==
          chain1 K inner iv (rget n1 0 a :: xs) H (L + 1))))) := by
    unfold meetM
    rw [sumTo_congr _ (fun H _ => sumTo_mul _ _ _)]
    exact sumTo_exch _ (n1 ^ t) (K ^ K)
  rw [e, sumTo_mul, sumTo_mul]
  refine Nat.le_trans (sumTo_mono _ (fun a _ => ?_)) (Nat.le_of_eq (sumTo_const _ (n1 ^ t)))
  cases hi : injT n1 t a
  · have z : ∀ H, indB (permB K H) * indB (false && (List.range t).all (fun j => chain1 K inner iv (rget n1 j a :: xs) H (L + 1) ==
        chain1 K inner iv (rget n1 0 a :: xs) H (L + 1))) = 0 := fun H => by rw [Bool.false_and]; exact Nat.mul_zero _
    rw [sumTo_congr _ (fun H _ => z H), sumTo_const, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]; exact Nat.zero_le _
  · have hdT : ∀ i j, i < t → j < t → i ≠ j → inner iv (rget n1 i a) ≠ inner iv (rget n1 j a) := fun i j hi' hj hij =>
      hd _ _ (rget_lt hn _ _) (rget_lt hn _ _) (injT_ne hn t a hi i j hi' hj hij)
    have hcf : ∀ H τ τ', τ' < t → t ≤ τ → τ < t * (L + 1) →
        posS K inner iv t (fun j => rget n1 j a) xs H τ ≠ posS K inner iv t (fun j => rget n1 j a) xs H τ' := by
      intro H τ τ' h' hτ hτL
      have ej : τ = τ / t * t + τ % t := by rw [Nat.mul_comm]; exact (Nat.div_add_mod τ t).symm
      have e0 : τ' = 0 * t + τ' := by rw [Nat.zero_mul, Nat.zero_add]
      have hi1 : 1 ≤ τ / t := (Nat.le_div_iff_mul_le ht).2 (by rw [Nat.one_mul]; exact hτ)
      have hiL : τ / t ≤ L := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ht).2 (by rw [Nat.mul_comm]; exact hτL))
      rw [ej, e0, posS_step K inner iv ht _ xs H _ _ (Nat.mod_lt τ ht), posS_step K inner iv ht _ xs H 0 τ' h']
      exact hcfC H _ _ _ (rget_lt hn _ _) (rget_lt hn _ _) hi1 hiL
    have hc := allMeet_countP2 hK inner hin κ hκ hF hpk2 iv ht (fun j => rget n1 j a) hdT xs L hcf
    refine Nat.le_trans (Nat.le_of_eq ?_) hc
    congr 2
    refine sumTo_congr _ (fun H _ => ?_)
    rw [Bool.true_and, indB_and']


/-! ### Later blocks outside the first commitments' tag -/

/-- Every block of `xsOf X L i` carries a nonzero tag. -/
def nzOK (X L : Nat) (tb : Nat → Nat) (i : Nat) : Bool :=
  (List.range L).all (fun m => tb (rget X m i) != 0)

/-- **First positions are never revisited** when a position's tag is its
    block's (`hτ`), first commitments carry tag `0` and later blocks a
    nonzero tag. -/
theorem cf_of_tags {K : Nat} (inner : Nat → Nat → Nat) (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x)
    (iv n1 : Nat) (h0 : ∀ c, c < n1 → tb c = 0) (xs : List Nat) (L : Nat)
    (hxs : ∀ m, m < L → tb (xs.getD m 0) ≠ 0) :
    ∀ H c c' i, c < n1 → c' < n1 → 1 ≤ i → i ≤ L →
      inner (chain1 K inner iv (c :: xs) H i) ((c :: xs).getD i 0) ≠ inner iv c' := by
  intro H c c' i _ hc' hi hiL e
  have := congrArg τ e
  rw [hτ, hτ, h0 c' hc'] at this
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  exact hxs m (by omega) this

theorem nzOK_xsOf {X L : Nat} (tb : Nat → Nat) (i : Nat) (h : nzOK X L tb i = true) :
    ∀ m, m < L → tb ((xsOf X L i).getD m 0) ≠ 0 := fun m hm => by
  rw [xsOf_getD X L i m hm]; exact bne_iff_ne.1 (List.all_eq_true.1 h m (List.mem_range.2 hm))

/-- The tuple load for every nonzero-tagged later transcript. -/
def loadTU (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (tb : Nat → Nat) (X L t s0 H : Nat) : Nat :=
  (s0 - 1) + n1 * sumTo (X ^ L) (fun i => indB (nzOK X L tb i && decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H)))

theorem preimage_loadTU (K : Nat) (inner : Nat → Nat → Nat) (iv : Nat) {n1 : Nat} (hn : 0 < n1) (tb : Nat → Nat)
    {X : Nat} (hX : 0 < X) (L t s0 : Nat) (xs : List Nat) (hxs : ∀ m, m < L → xs.getD m 0 < X)
    (hnz : ∀ m, m < L → tb (xs.getD m 0) ≠ 0) (H v : Nat) :
    sumTo n1 (fun c => indB (decide (chain1 K inner iv (c :: xs) H (L + 1) = v))) ≤ loadTU K inner iv n1 tb X L t s0 H := by
  obtain ⟨i, hi, hag⟩ := xsOf_cover hX xs hxs
  have hch : ∀ c, chain1 K inner iv (c :: xs) H (L + 1) = chain1 K inner iv (c :: xsOf X L i) H (L + 1) :=
    fun c => chain1_congr K inner iv _ _ H (L + 1) (fun j hj => by
      cases j with
      | zero => rfl
      | succ j => exact hag j (Nat.lt_of_succ_lt_succ hj))
  have hok : nzOK X L tb i = true := List.all_eq_true.2 (fun m hm => by
    have hm' := List.mem_range.1 hm
    rw [← xsOf_getD X L i m hm', ← hag m hm']; exact bne_iff_ne.2 (hnz m hm'))
  rw [sumTo_congr _ (fun c _ => by rw [hch c])]
  refine Nat.le_trans (preimage_loadT K inner iv hn (xsOf X L i) L t s0 H v) ?_
  unfold loadT loadTU
  refine Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_trans ?_ (le_sumTo (fun i => indB (nzOK X L tb i &&
    decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H))) _ hi))) _
  rw [hok, Bool.true_and]; exact Nat.le_refl _

/-- **Markov for meeting tuples**: per nonzero-tagged later block list. -/
theorem meet_markov2 {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (xs : List Nat) (L : Nat)
    (hcfC : ∀ H c c' i, c < n1 → c' < n1 → 1 ≤ i → i ≤ L →
      inner (chain1 K inner iv (c :: xs) H i) ((c :: xs).getD i 0) ≠ inner iv c')
    {t : Nat} (ht : 0 < t) (s0 : Nat) :
    fact (t - 1) * (K - t * (L + 1)) ^ (t - 1) * (ffac s0 t * sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H)))) ≤
      n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  have hm0 := meetM_countP2 hK inner hin κ hκ hF hpk2 iv hn hd xs L hcfC ht
  have mk : ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H))) ≤
      sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) := by
    rw [sumTo_mul]
    refine sumTo_mono _ (fun H _ => ?_)
    cases permB K H
    · simp [indB]
    · by_cases h : ffac s0 t ≤ meetM K inner iv n1 xs L t H
      · rw [decide_eq_true h]; simp only [Bool.true_and, show indB true = 1 from rfl, Nat.mul_one, Nat.one_mul]; exact h
      · rw [decide_eq_false h]; simp [indB]
  calc fact (t - 1) * (K - t * (L + 1)) ^ (t - 1) * (ffac s0 t * sumTo (K ^ K) (fun H =>
        indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 xs L t H))))
      ≤ fact (t - 1) * (K - t * (L + 1)) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H) :=
        Nat.mul_le_mul_left _ mk
    _ = fact (t - 1) * ((K - t * (L + 1)) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H) * meetM K inner iv n1 xs L t H)) :=
        Nat.mul_assoc _ _ _
    _ ≤ _ := by rw [Nat.mul_assoc (n1 ^ t)]; exact hm0

/-- **The nonzero-tagged tuple load averaged**: `Q = (t-1)! (K - t (L+1))^(t-1)`,
    `f = s0 (s0-1) ⋯ (s0-t+1)`; `Q f` times the summed `loadTU` is at most
    `Q f (s0 - 1) + n1 X^L n1^t ((0 + ⋯ + (t (L+1) - 1)) F)^(t-1)` per
    permutation table. -/
theorem loadTU_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x)
    (h0 : ∀ c, c < n1 → tb c = 0) (X L : Nat) {t : Nat} (ht : 0 < t) (s0 : Nat) :
    fact (t - 1) * (K - t * (L + 1)) ^ (t - 1) * ffac s0 t * sumTo (K ^ K) (fun H => indB (permB K H) * loadTU K inner iv n1 tb X L t s0 H) ≤
      (fact (t - 1) * (K - t * (L + 1)) ^ (t - 1) * ffac s0 t * (s0 - 1) +
        n1 * (X ^ L * (n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1)))) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
  let bad := fun i H => indB (permB K H && (nzOK X L tb i && decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H)))
  have each : ∀ i, fact (t - 1) * (K - t * (L + 1)) ^ (t - 1) * (ffac s0 t * sumTo (K ^ K) (fun H => bad i H)) ≤
      n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
    intro i
    cases hok : nzOK X L tb i
    · have z : sumTo (K ^ K) (fun H => bad i H) = 0 :=
        Eq.trans (sumTo_congr _ (fun H _ => by show indB (permB K H && (nzOK X L tb i && _)) = 0; rw [hok]; simp [indB]))
          (Eq.trans (sumTo_const 0 _) (Nat.mul_zero _))
      rw [z, Nat.mul_zero, Nat.mul_zero]; exact Nat.zero_le _
    · have hs := cf_of_tags (K := K) inner τ tb hτ iv n1 h0 (xsOf X L i) L (nzOK_xsOf tb i hok)
      have hm := meet_markov2 hK inner hin κ hκ hF hpk2 iv hn hd (xsOf X L i) L hs ht s0
      refine Nat.le_trans (Nat.le_of_eq ?_) hm
      have z : sumTo (K ^ K) (fun H => bad i H) = sumTo (K ^ K) (fun H =>
          indB (permB K H && decide (ffac s0 t ≤ meetM K inner iv n1 (xsOf X L i) L t H))) :=
        sumTo_congr _ (fun H _ => by show indB (permB K H && (nzOK X L tb i && _)) = _; rw [hok, Bool.true_and])
      rw [z]
  have e : ∀ H, indB (permB K H) * loadTU K inner iv n1 tb X L t s0 H = indB (permB K H) * (s0 - 1) +
      n1 * sumTo (X ^ L) (fun i => bad i H) := fun H => by
    unfold loadTU
    rw [Nat.mul_add, Nat.mul_left_comm, sumTo_mul]
    congr 2
    exact sumTo_congr _ (fun i _ => indB_and' _ _)
  have e2 : sumTo (K ^ K) (fun H => indB (permB K H) * (s0 - 1)) = (s0 - 1) * sumTo (K ^ K) (fun H => indB (permB K H)) := by
    rw [sumTo_mul]; exact sumTo_congr _ (fun H _ => Nat.mul_comm _ _)
  rw [sumTo_congr _ (fun H _ => e H), sumTo_add, e2, ← sumTo_mul, sumTo_exch _ (X ^ L) (K ^ K)]
  generalize hPi : sumTo (K ^ K) (fun H => indB (permB K H)) = Pi0 at *
  generalize hQ : fact (t - 1) * (K - t * (L + 1)) ^ (t - 1) = Q at *
  generalize hW : n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1) = W at *
  generalize hf : ffac s0 t = f at *
  have hs : Q * (f * sumTo (X ^ L) (fun i => sumTo (K ^ K) (fun H => bad i H))) ≤ X ^ L * (W * Pi0) := by
    rw [sumTo_mul, sumTo_mul]
    refine Nat.le_trans (sumTo_mono _ (fun i _ => ?_)) (Nat.le_of_eq (sumTo_const _ (X ^ L)))
    exact each i
  calc Q * f * ((s0 - 1) * Pi0 + n1 * sumTo (X ^ L) (fun i => sumTo (K ^ K) (fun H => bad i H)))
      = Q * f * (s0 - 1) * Pi0 + n1 * (Q * (f * sumTo (X ^ L) (fun i => sumTo (K ^ K) (fun H => bad i H)))) := by
        rw [Nat.mul_add]; congr 1 <;> ac_rfl
    _ ≤ Q * f * (s0 - 1) * Pi0 + n1 * (X ^ L * (W * Pi0)) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _
    _ = _ := by rw [Nat.add_mul]; ac_rfl

/-- **`SudChallenger`'s spread hypotheses at every permutation table, `L + 1`
    absorptions**: the index `φ m w` the state after the first commitment
    `m % n1` and the later blocks `enc (m / n1) w`, each below `X` and
    tagged nonzero; the table's `δs' = δs loadTU` meets `hsp1` and
    `hφsp` for every `d`, `rest`, `w` and `v` (`s0 ≥ 2`). -/
theorem loadTU_hsp {D W : Type} {K NS1 n1 δs X : Nat} (inner : Nat → Nat → Nat) (iv : Nat) (tb : Nat → Nat) (hX : 0 < X) (L t : Nat)
    (enc : Nat → W → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (hnz : ∀ r w i, i < L → tb ((enc r w).getD i 0) ≠ 0)
    (Com1 : D → Nat → Nat) (hr1 : ∀ d σ, Com1 d σ < n1)
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) {s0 : Nat} (hs0 : 2 ≤ s0) (H : Nat) :
    (∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs * loadTU K inner iv n1 tb X L t s0 H) ∧
      (∀ d rest w v, sumTo NS1 (fun σ1 => indB (decide
        ((fun m' w => chain1 K inner iv ((m' % n1) :: enc (m' / n1) w) H (L + 1)) (Com1 d σ1 + n1 * rest) w = v))) ≤
        δs * loadTU K inner iv n1 tb X L t s0 H) := by
  have h1 : 1 ≤ loadTU K inner iv n1 tb X L t s0 H := Nat.le_trans (Nat.le_sub_of_add_le hs0) (Nat.le_add_right _ _)
  refine ⟨fun d v => Nat.le_trans (hsp1 d v) (Nat.le_trans (Nat.le_of_eq (Nat.mul_one δs).symm)
    (Nat.mul_le_mul_left _ h1)), fun d rest w v => ?_⟩
  have hn1 : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (hr1 d 0)
  have em : ∀ σ1, (Com1 d σ1 + n1 * rest) % n1 = Com1 d σ1 ∧ (Com1 d σ1 + n1 * rest) / n1 = rest := fun σ1 =>
    ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hr1 d σ1)],
     by rw [Nat.add_mul_div_left _ _ hn1, Nat.div_eq_of_lt (hr1 d σ1), Nat.zero_add]⟩
  let φ := fun c => chain1 K inner iv (c :: enc rest w) H (L + 1)
  have e : ∀ σ1, (fun m' w => chain1 K inner iv ((m' % n1) :: enc (m' / n1) w) H (L + 1)) (Com1 d σ1 + n1 * rest) w =
      φ (Com1 d σ1) := fun σ1 => by
    show chain1 K inner iv (((Com1 d σ1 + n1 * rest) % n1) :: enc ((Com1 d σ1 + n1 * rest) / n1) w) H (L + 1) = _
    rw [(em σ1).1, (em σ1).2]
  rw [sumTo_congr _ (fun σ1 _ => by rw [e σ1]), sumTo_split_pos (Com1 d) (hr1 d)]
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
  exact Nat.mul_le_mul_left _ (preimage_loadTU K inner iv hn1 tb hX L t s0 (enc rest w) (henc rest w) (hnz rest w) H v)

theorem loadTU_δs_countP {K Kc F : Nat} (hK : 0 < K) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < K) (κ : Nat → Nat)
    (hκ : ∀ u, κ u < Kc) (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat) {n1 : Nat} (hn : 0 < n1)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b) (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x)
    (h0 : ∀ c, c < n1 → tb c = 0) (X L : Nat) {t : Nat} (ht : 0 < t) (s0 δs : Nat) :
    fact (t - 1) * (K - t * (L + 1)) ^ (t - 1) * ffac s0 t *
        sumTo (K ^ K) (fun H => indB (permB K H) * (δs * loadTU K inner iv n1 tb X L t s0 H)) ≤
      δs * ((fact (t - 1) * (K - t * (L + 1)) ^ (t - 1) * ffac s0 t * (s0 - 1) +
        n1 * (X ^ L * (n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1)))) * sumTo (K ^ K) (fun H => indB (permB K H))) := by
  have h := loadTU_countP hK inner hin κ hκ hF hpk2 iv hn hd τ tb hτ h0 X L ht s0
  rw [sumTo_congr _ (fun H _ => Nat.mul_left_comm _ _ _), ← sumTo_mul, Nat.mul_left_comm]
  exact Nat.mul_le_mul_left _ h

/-- The spread the permutation `H` gives proof `ix`: `δ0 ix loadTU`. -/
def δsU (K : Nat) (inner : Nat → Nat → Nat) (iv n1 : Nat) (tb : Nat → Nat) (X L t s0 : Nat) (δ0 : Nat → Nat) (H ix : Nat) : Nat :=
  δ0 ix * loadTU K inner iv n1 tb X L t s0 H


/-- **The full-width instance meets `hpk2`**: with the block overwriting
    the low digit, equal positions mean equal kept parts, so equal
    capacities, whatever the blocks. -/
theorem hpk2_satPT {R1 R2 C : Nat} (hR1 : 0 < R1) (hR2 : 0 < R2) :
    ∀ s s' x x', x % R1 + R1 * ((s / R1) % (R2 * C)) = x' % R1 + R1 * ((s' / R1) % (R2 * C)) →
      ((s / R1) % (R2 * C)) / R2 = ((s' / R1) % (R2 * C)) / R2 := by
  intro s s' x x' e
  have h1 := congrArg (· / R1) e
  simp only [Nat.add_mul_div_left _ _ hR1, Nat.div_eq_of_lt (Nat.mod_lt _ hR1), Nat.zero_add] at h1
  rw [h1]

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_interleaveS` averaged over a uniform permutation, the index
    after the first commitment and `L` later blocks outside the first
    commitments' tag** (`loadφA`): at each permutation table `P` with
    `δsU P = δ0 loadTU` (`loadTU_hsp`); the error the permutation-weighted
    sum of the tables' errors (`zkbT_avgW`). -/
theorem sud_interleaveLU {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x) (h0 : ∀ c, c < n1 → tb c = 0)
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (hnz : ∀ r w i, i < L → tb ((enc r w).getD i 0) ≠ 0) (δ0 : Nat → Nat)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n, ZKBT (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) *
        (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H))))
      (KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n)
      (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
      (fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x)
      (fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x))
      (fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x)
      (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsU Kp inner iv n1 tb X L t s0 δ0 P n))))))) n))) := by
  intro n
  exact zkbT_avgW (fun P => indB (permB Kp P)) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
    (fun P => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n)) (fun P => (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n)) (fun P => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n))
    (fun P => (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsU Kp inner iv n1 tb X L t s0 δ0 P n))))))) n)) (fun P _ hw =>
    sud_interleaveS φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp
      hK2 hK4 (loadφA Kp inner iv n1 L enc P) (fun _ _ _ => rget_lt hKp _ _) hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
      Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 (δsU Kp inner iv n1 tb X L t s0 δ0 P)
      (fun ix => (loadTU_hsp inner iv tb hX L t enc henc hnz (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).1)
      (fun ix => (loadTU_hsp inner iv tb hX L t enc henc hnz (Com1 ix) (hr1 ix) (hsp1 ix) hs0 P).2) isQ nxtQ n)


set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
/-- **`sud_interleaveLU` with a number for its error**: `Kq = (t-1)!
    (Kp - t (L+1))^(t-1) s0 (s0-1) ⋯ (s0-t+1)` times the averaged real count
    is at most `Kq` times the averaged simulation plus `errPowD` at the
    errors `Kq W ε` and each spread `δ0 i (Kq (s0 - 1) + n1 X^L n1^t
    ((0 + ⋯ + (t (L+1) - 1)) F)^(t-1)) W`, `W` the number of permutation
    tables (`avg_err_bound`, `loadTU_δs_countP`). -/
theorem sud_interleaveLUN {V Wv P1 P2 P3 W1 W2 W3 : Type} {kr kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 K4 n1 kr (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    {Kp : Nat} (hKp : 0 < Kp) (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (iv : Nat)
    (hd : ∀ a b, a < n1 → b < n1 → a ≠ b → inner iv a ≠ inner iv b)
    (τ tb : Nat → Nat) (hτ : ∀ s x, τ (inner s x) = tb x) (h0 : ∀ c, c < n1 → tb c = 0)
    {X : Nat} (hX : 0 < X) (L : Nat) (enc : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → List Nat) (henc : ∀ r w i, i < L → (enc r w).getD i 0 < X)
    (hnz : ∀ r w i, i < L → tb ((enc r w).getD i 0) ≠ 0) (δ0 : Nat → Nat) (hn1 : 0 < n1) {F : Nat} (hF : ∀ v, sumTo Kp (fun u => indB (decide (κ u = v))) ≤ F)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n (E : Nat × (Nat × Nat × Nat × Nat) → _ → Bool),
      (fact (t - 1) * (Kp - t * (L + 1)) ^ (t - 1) * ffac s0 t) * ((KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E H ((fun PH x => (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out)) n) PH.2 x) H x))))) ≤
        (fact (t - 1) * (Kp - t * (L + 1)) ^ (t - 1) * ffac s0 t) * (fun (f : Nat × (Nat × Nat × Nat × Nat) → Nat) => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => f (P, H)))) (fun H => (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n) (fun c => (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n) (fun x => indB (E ((fun PH c x => (PH.1, (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c)) n) PH.2 c x)) H c x) ((fun PH c x => (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc PH.1) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sv)) n) PH.2 c x) H c x))))) +
        errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => (fact (t - 1) * (Kp - t * (L + 1)) ^ (t - 1) * ffac s0 t) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))) * (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) i) (fun i => (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x))))))) i ((fun i => δ0 i * ((fact (t - 1) * (Kp - t * (L + 1)) ^ (t - 1) * ffac s0 t * (s0 - 1) + n1 * (X ^ L * (n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1)))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) i)) n := by
  intro n E
  have h := sud_interleaveLU (kq := kq) φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 hKp inner hin κ hκ hpk2 iv hd τ tb hτ h0 hX L enc henc hnz δ0 hsp1 ht hs0 isQ nxtQ n
  have hb := (avg_err_bound (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε) (Kp ^ Kp) (fun P => indB (permB Kp P))
      (fun P i => δsU Kp inner iv n1 tb X L t s0 δ0 P i) (fun n x => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * kr)) n *
            cond (isQ n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 (loadφA Kp inner iv n1 L enc 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 kr φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * x)))))))
      (fun i x => wrap_scale (lin_sum4 _ _ _ _) (lin_sum4 _ _ _ _) (lin_smPowD (fun _ => lin_sm _ _ _ _) i) _ _ _ _ _ x)
      (fact (t - 1) * (Kp - t * (L + 1)) ^ (t - 1) * ffac s0 t) (fun i => δ0 i * ((fact (t - 1) * (Kp - t * (L + 1)) ^ (t - 1) * ffac s0 t * (s0 - 1) + n1 * (X ^ L * (n1 ^ t * (sumTo (t * (L + 1)) (fun j => j) * F) ^ (t - 1)))) * (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) (fun i => loadTU_δs_countP hKp inner hin κ hκ hF hpk2 iv hn1 hd τ tb hτ h0 X L ht s0 (δ0 i)) n)
  exact zkbT_err_le h _ _ hb E

end

end Circuit

