import Ski.Circuit.BaseBus

/-!
# The bus lemma, for any tables

On a balanced bus, a message some sender sends with count `1` is matched by
a provider: some provider row sends that tuple with a nonzero count
(`bus_hit_on`).  A **sender** is a table whose messages on the bus weigh
at least `1` and have counts `0` or `1` (`SenderOn`); a **provider** is
any other table.  The senders' counts are bits, and Plonky3's height
check keeps their number below `P`, so they cannot cancel in the field.
-/

namespace Circuit

/-- A sum of small elements, each with its own bound. -/
theorem fold_val_le {α : Type} (f : α → F) (w : α → Nat) : ∀ (l : List α), (∀ a ∈ l, (f a).val ≤ w a) →
    (l.map w).sum < P →
    (l.foldr (fun a acc => f a + acc) 0).val ≤ (l.map w).sum ∧
      ∀ a ∈ l, (f a).val ≤ (l.foldr (fun a acc => f a + acc) 0).val
  | [], _, _ => ⟨Nat.zero_le _, fun _ h => nomatch h⟩
  | a :: l, hb, hs => by
    have ha := hb a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons] at hs
    obtain ⟨ih1, ih2⟩ := fold_val_le f w l (fun b hb' => hb b (List.mem_cons_of_mem _ hb')) (by omega)
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    have hlt : (f a).val + (l.foldr (fun a acc => f a + acc) 0).val < P := by omega
    rw [Fin.val_add, Nat.mod_eq_of_lt hlt]
    refine ⟨by omega, fun b hb' => ?_⟩
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih2 b hb') (Nat.le_add_left _ _)

/-- The weights of a table's messages. -/
def wsum (A : AirD) : Nat := A.inters.foldr (fun I a => I.weight + a) 0

theorem wsum_ge : ∀ (l : List Inter), (∀ I ∈ l, 1 ≤ I.weight) → l.length ≤ l.foldr (fun I a => I.weight + a) 0
  | [], _ => Nat.le_refl _
  | I :: l, h => by
    simp only [List.length_cons, List.foldr_cons]
    have := h I List.mem_cons_self
    have := wsum_ge l (fun J hJ => h J (List.mem_cons_of_mem _ hJ))
    omega

theorem heights_sum : ∀ (ts : List (AirD × Table)),
    ts.foldr (fun p acc => wsum p.1 * p.2.h + acc) 0 = (ts.map fun p => wsum p.1 * p.2.h).sum
  | [] => rfl
  | p :: ts => by simp only [List.foldr_cons, List.map_cons, List.sum_cons, heights_sum ts]

/-- A sender: every message weighs at least `1`, and on bus `B` every row's
    count is `0` or `1`. -/
def Sender (B : String) (p : AirD × Table) : Prop :=
  (∀ I ∈ p.1.inters, 1 ≤ I.weight) ∧
    ∀ r, r < p.2.h → ∀ I ∈ p.1.inters, I.bus = B → (I.count.eval (p.2.env r)).val ≤ 1

/-- A sender on bus `B` only: its messages on `B` weigh at least `1`, and
    their counts are `0` or `1`.  Its other messages may weigh `0`. -/
def SenderOn (B : String) (p : AirD × Table) : Prop :=
  (∀ I ∈ p.1.inters, I.bus = B → 1 ≤ I.weight) ∧
    ∀ r, r < p.2.h → ∀ I ∈ p.1.inters, I.bus = B → (I.count.eval (p.2.env r)).val ≤ 1

theorem Sender.on {B : String} {p : AirD × Table} (h : Sender B p) : SenderOn B p :=
  ⟨fun I hI _ => h.1 I hI, h.2⟩

/-- The messages on `B` number at most their weights. -/
theorem wsumOn_le : ∀ (l : List Inter) (B : String), (∀ I ∈ l, I.bus = B → 1 ≤ I.weight) →
    (l.map fun I => if I.bus = B then 1 else 0).sum ≤ l.foldr (fun I a => I.weight + a) 0
  | [], _, _ => Nat.le_refl _
  | I :: l, B, h => by
    simp only [List.map_cons, List.sum_cons, List.foldr_cons]
    have ih := wsumOn_le l B (fun J hJ => h J (List.mem_cons_of_mem _ hJ))
    split
    · next hb => have := h I List.mem_cons_self hb; omega
    · omega

/-- **The bus lemma**: a message a sender sends with count `1` is matched
    by a provider row sending its tuple with a nonzero count.  Only the
    senders' messages on the bus need weigh at least `1`. -/
theorem bus_hit_on {ts : List (AirD × Table)} {B : String} {v : List F}
    (hbal : Balanced ts) (hH : HeightsOK ts) (prov : AirD × Table → Bool)
    (hsend : ∀ p ∈ ts, prov p = false → SenderOn B p)
    (hit : ∃ p ∈ ts, prov p = false ∧ ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = B ∧
      I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ p ∈ ts, prov p = true ∧ ∃ r, r < p.2.h ∧ rowSends p.1 p.2 B v r ≠ 0 := by
  cases hany : ts.any (fun p => prov p && (List.range p.2.h).any (fun r => !decide (rowSends p.1 p.2 B v r = 0))) with
  | true =>
    obtain ⟨p, hp, e⟩ := List.any_eq_true.1 hany
    simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, Bool.not_eq_true',
      decide_eq_false_iff_not] at e
    obtain ⟨hpr, r, hr, hne⟩ := e
    exact ⟨p, hp, hpr, r, hr, hne⟩
  | false =>
    exfalso
    have hno : ∀ p ∈ ts, prov p = true → ∀ r, r < p.2.h → rowSends p.1 p.2 B v r = 0 := by
      intro p hp hpr r hr
      have := List.any_eq_false.1 hany p hp
      rw [hpr, Bool.true_and] at this
      by_cases h0 : rowSends p.1 p.2 B v r = 0
      · exact h0
      · exfalso; apply this
        exact List.any_eq_true.2 ⟨r, List.mem_range.2 hr, by rw [decide_eq_false h0]; rfl⟩
    -- a sender's row, as a number
    have hrow : ∀ p ∈ ts, prov p = false → ∀ r, r < p.2.h →
        (rowSends p.1 p.2 B v r).val ≤ wsum p.1 ∧
        ∀ I ∈ p.1.inters, ((if I.bus = B ∧ I.fields.map (fun e => e.eval (p.2.env r)) = v then
          I.count.eval (p.2.env r) else 0) : F).val ≤ (rowSends p.1 p.2 B v r).val := by
      intro p hp hpr r hr
      have hs := hsend p hp hpr
      have hw := wsumOn_le p.1.inters B hs.1
      have hl : (p.1.inters.map fun I => if I.bus = B then 1 else 0).sum < P := by
        have hH' : (ts.map fun p => wsum p.1 * p.2.h).sum < P := by
          rw [← heights_sum]; exact hH
        have hp1 : wsum p.1 * p.2.h ≤ (ts.map fun p => wsum p.1 * p.2.h).sum :=
          le_sum_of_mem (List.mem_map.2 ⟨p, hp, rfl⟩)
        have hwh : wsum p.1 ≤ wsum p.1 * p.2.h :=
          Nat.le_mul_of_pos_right _ (Nat.lt_of_le_of_lt (Nat.zero_le r) hr)
        exact Nat.lt_of_le_of_lt hw (Nat.lt_of_le_of_lt hwh (Nat.lt_of_le_of_lt hp1 hH'))
      have hfv := fold_val_le (fun (I : Inter) => (if I.bus = B ∧ I.fields.map (fun e => e.eval (p.2.env r)) = v then
          I.count.eval (p.2.env r) else 0 : F)) (fun (I : Inter) => if I.bus = B then 1 else 0) p.1.inters
        (fun I hI => by
        rcases (inferInstance : Decidable (I.bus = B)) with hb | hb
        · rw [if_neg (fun h => hb h.1), if_neg hb]; exact Nat.le_refl _
        · rw [if_pos hb]
          split
          · exact hs.2 r hr I hI hb
          · exact Nat.zero_le _) hl
      exact ⟨Nat.le_trans hfv.1 hw, hfv.2⟩
    -- a sender's table, as a number
    have htab : ∀ p ∈ ts, prov p = false →
        (tableSends p.1 p.2 B v).val ≤ wsum p.1 * p.2.h ∧
        ∀ r, r < p.2.h → (rowSends p.1 p.2 B v r).val ≤ (tableSends p.1 p.2 B v).val := by
      intro p hp hpr
      have hH' : (ts.map fun p => wsum p.1 * p.2.h).sum < P := by rw [← heights_sum]; exact hH
      have hp1 : wsum p.1 * p.2.h ≤ (ts.map fun p => wsum p.1 * p.2.h).sum :=
        le_sum_of_mem (List.mem_map.2 ⟨p, hp, rfl⟩)
      have hb : ∀ r ∈ List.range p.2.h, (rowSends p.1 p.2 B v r).val ≤ wsum p.1 := fun r hr =>
        (hrow p hp hpr r (List.mem_range.1 hr)).1
      have hlt : (List.range p.2.h).length * wsum p.1 < P := by
        rw [List.length_range, Nat.mul_comm]; exact Nat.lt_of_le_of_lt hp1 hH'
      obtain ⟨h1, h2⟩ := fold_val (fun r => rowSends p.1 p.2 B v r) (wsum p.1) (List.range p.2.h) hb hlt
      rw [List.length_range, Nat.mul_comm] at h1
      exact ⟨h1, fun r hr => h2 r (List.mem_range.2 hr)⟩
    -- all tables, as a number
    have hall := fold_val_le (fun p => tableSends p.1 p.2 B v) (fun p => wsum p.1 * p.2.h) ts
      (fun p hp => by
        cases hpr : prov p with
        | false => exact (htab p hp hpr).1
        | true =>
          have : tableSends p.1 p.2 B v = 0 :=
            fold_zero _ _ (fun r hr => hno p hp hpr r (List.mem_range.1 hr))
          rw [this]; exact Nat.zero_le _)
      (by rw [← heights_sum]; exact hH)
    have h0 := hbal B v
    obtain ⟨p, hp, hpr, r, hr, I, hI, hbus, hf, hc⟩ := hit
    have e1 := (hrow p hp hpr r hr).2 I hI
    rw [if_pos ⟨hbus, hf⟩, hc] at e1
    have e2 := (htab p hp hpr).2 r hr
    have e3 := hall.2 p hp
    rw [h0] at e3
    exact absurd (Nat.le_trans e1 (Nat.le_trans e2 e3)) (by decide)


/-- **The bus lemma**, for senders whose every message weighs at least `1`. -/
theorem bus_hit {ts : List (AirD × Table)} {B : String} {v : List F}
    (hbal : Balanced ts) (hH : HeightsOK ts) (prov : AirD × Table → Bool)
    (hsend : ∀ p ∈ ts, prov p = false → Sender B p)
    (hit : ∃ p ∈ ts, prov p = false ∧ ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = B ∧
      I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ p ∈ ts, prov p = true ∧ ∃ r, r < p.2.h ∧ rowSends p.1 p.2 B v r ≠ 0 :=
  bus_hit_on hbal hH prov (fun p hp hpr => (hsend p hp hpr).on) hit

end Circuit
