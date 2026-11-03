import Ski.Circuit.Bus
import Ski.Circuit.BaseTable

/-!
# The bus lemma for buses between private tables

`Ski/Circuit/Bus.lean`'s lemma matches a sender's message to a provider.
A bus between private tables, as the `dec` jet's `decn`, `decb`, `decd` and
`decx`, has no provider: every table both sends (count `1`) and receives
(count `-1`).  **`bus_match`**: on a balanced bus whose every message's
count is `0`, `1` or `-1` on every row (`SignedOn`), a message sent with
count `1` is received with count `-1` by some row, and one received is
sent.  The counts are numbers below `P` by Plonky3's height check, so
balance in the field is balance in the numbers (`hitsAll_eq`).
-/

namespace Circuit

/-- Membership in a literal list, by position: no decision procedure. -/
macro "mem_tac" : tactic => `(tactic| repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

/-- A table whose messages on `B` weigh at least `1` and have counts `0`,
    `1` or `-1` on every row. -/
def SignedOn (B : String) (p : AirD × Table) : Prop :=
  (∀ I ∈ p.1.inters, I.bus = B → 1 ≤ I.weight) ∧
    ∀ r, r < p.2.h → ∀ I ∈ p.1.inters, I.bus = B →
      I.count.eval (p.2.env r) = 0 ∨ I.count.eval (p.2.env r) = 1 ∨ I.count.eval (p.2.env r) = -1

/-- Whether message `I` of row `r` is `v` on `B` with count `s`. -/
def hitI (T : Table) (B : String) (v : List F) (s : F) (r : Nat) (I : Inter) : Nat :=
  if I.bus = B ∧ I.fields.map (fun e => e.eval (T.env r)) = v ∧ I.count.eval (T.env r) = s then 1 else 0

def hitsRow (A : AirD) (T : Table) (B : String) (v : List F) (s : F) (r : Nat) : Nat :=
  A.inters.foldr (fun I acc => hitI T B v s r I + acc) 0

def hitsTab (A : AirD) (T : Table) (B : String) (v : List F) (s : F) : Nat :=
  (List.range T.h).foldr (fun r acc => hitsRow A T B v s r + acc) 0

def hitsAll (ts : List (AirD × Table)) (B : String) (v : List F) (s : F) : Nat :=
  ts.foldr (fun p acc => hitsTab p.1 p.2 B v s + acc) 0

/-- `(a - b) + (c - d) = (a + c) - (b + d)`, by normal forms. -/
theorem sub_add_sub (a b c d : F) : (a - b) + (c - d) = (a + c) - (b + d) :=
  E.eval_eq_of_norm (e := .add (.sub (.atom (.main 0 0)) (.atom (.main 0 1))) (.sub (.atom (.main 0 2)) (.atom (.main 0 3))))
    (e' := .sub (.add (.atom (.main 0 0)) (.atom (.main 0 2))) (.add (.atom (.main 0 1)) (.atom (.main 0 3)))) (by decide)
    (fun | .main 0 0 => a | .main 0 1 => b | .main 0 2 => c | .main 0 3 => d | _ => 0)

theorem foldr_pos {α : Type} (f : α → Nat) : ∀ (l : List α), 0 < l.foldr (fun x acc => f x + acc) 0 →
    ∃ x ∈ l, 0 < f x
  | [], h => absurd h (Nat.lt_irrefl 0)
  | x :: l, h => by
    simp only [List.foldr_cons] at h
    rcases Nat.eq_zero_or_pos (f x) with h0 | h0
    · obtain ⟨y, hy, hpos⟩ := foldr_pos f l (by omega)
      exact ⟨y, List.mem_cons_of_mem _ hy, hpos⟩
    · exact ⟨x, List.mem_cons_self, h0⟩

theorem le_foldr {α : Type} (f : α → Nat) : ∀ {l : List α} {x : α}, x ∈ l → f x ≤ l.foldr (fun x acc => f x + acc) 0
  | _ :: l, x, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_foldr f (l := l) h; omega

theorem foldr_le_mul {α : Type} (f : α → Nat) (w : Nat) : ∀ (l : List α), (∀ x ∈ l, f x ≤ w) →
    l.foldr (fun x acc => f x + acc) 0 ≤ l.length * w
  | [], _ => Nat.zero_le _
  | x :: l, h => by
    simp only [List.foldr_cons, List.length_cons, Nat.succ_mul]
    have := h x List.mem_cons_self
    have := foldr_le_mul f w l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem foldr_ofN {α : Type} (f : α → Nat) : ∀ (l : List α),
    ofN (l.foldr (fun x acc => f x + acc) 0) = l.foldr (fun x acc => ofN (f x) + acc) 0
  | [] => rfl
  | x :: l => by simp only [List.foldr_cons, ofN_add, foldr_ofN f l]

theorem foldr_sub {α : Type} (g : α → F) (f₁ f₂ : α → Nat) : ∀ (l : List α), (∀ x ∈ l, g x = ofN (f₁ x) - ofN (f₂ x)) →
    l.foldr (fun x acc => g x + acc) 0 =
      ofN (l.foldr (fun x acc => f₁ x + acc) 0) - ofN (l.foldr (fun x acc => f₂ x + acc) 0)
  | [], _ => by show (0 : F) = ofN 0 - ofN 0; decide
  | x :: l, h => by
    simp only [List.foldr_cons]
    rw [h x List.mem_cons_self, foldr_sub g f₁ f₂ l (fun y hy => h y (List.mem_cons_of_mem _ hy)), sub_add_sub,
      ofN_add, ofN_add]

section

variable {B : String} {v : List F}

theorem hitI_sends {T : Table} {r : Nat} {I : Inter}
    (hc : I.bus = B → I.count.eval (T.env r) = 0 ∨ I.count.eval (T.env r) = 1 ∨ I.count.eval (T.env r) = -1) :
    (if I.bus = B ∧ I.fields.map (fun e => e.eval (T.env r)) = v then I.count.eval (T.env r) else 0) =
      ofN (hitI T B v 1 r I) - ofN (hitI T B v (-1) r I) := by
  unfold hitI
  by_cases hb : I.bus = B ∧ I.fields.map (fun e => e.eval (T.env r)) = v
  · rw [if_pos hb]
    rcases hc hb.1 with h0 | h1 | hm
    · rw [h0, if_neg (fun h => absurd h.2.2 (by decide)), if_neg (fun h => absurd h.2.2 (by decide))]; decide
    · rw [h1, if_pos ⟨hb.1, hb.2, rfl⟩, if_neg (fun h => absurd h.2.2 (by decide))]; decide
    · rw [hm, if_neg (fun h => absurd h.2.2 (by decide)), if_pos ⟨hb.1, hb.2, rfl⟩]; decide
  · rw [if_neg hb, if_neg (fun h => hb ⟨h.1, h.2.1⟩), if_neg (fun h => hb ⟨h.1, h.2.1⟩)]; decide

theorem rowSends_hits {p : AirD × Table} (hs : SignedOn B p) {r : Nat} (hr : r < p.2.h) :
    rowSends p.1 p.2 B v r = ofN (hitsRow p.1 p.2 B v 1 r) - ofN (hitsRow p.1 p.2 B v (-1) r) :=
  foldr_sub _ _ _ p.1.inters (fun I hI => hitI_sends (fun hb => hs.2 r hr I hI hb))

theorem tableSends_hits {p : AirD × Table} (hs : SignedOn B p) :
    tableSends p.1 p.2 B v = ofN (hitsTab p.1 p.2 B v 1) - ofN (hitsTab p.1 p.2 B v (-1)) :=
  foldr_sub _ _ _ (List.range p.2.h) (fun r hr => rowSends_hits hs (List.mem_range.1 hr))

theorem allSends_hits {ts : List (AirD × Table)} (hs : ∀ p ∈ ts, SignedOn B p) :
    ts.foldr (fun p acc => tableSends p.1 p.2 B v + acc) 0 = ofN (hitsAll ts B v 1) - ofN (hitsAll ts B v (-1)) :=
  foldr_sub _ _ _ ts (fun p hp => tableSends_hits (hs p hp))

theorem hitI_le (T : Table) (s : F) (r : Nat) (I : Inter) : hitI T B v s r I ≤ if I.bus = B then 1 else 0 := by
  unfold hitI
  by_cases hb : I.bus = B
  · rw [if_pos hb]; split <;> omega
  · rw [if_neg hb, if_neg (fun h => hb h.1)]; exact Nat.le_refl _

theorem hitsRow_le {p : AirD × Table} (hs : SignedOn B p) (s : F) (r : Nat) :
    hitsRow p.1 p.2 B v s r ≤ wsum p.1 := by
  have h1 : ∀ (l : List Inter), l.foldr (fun I acc => hitI p.2 B v s r I + acc) 0 ≤
      (l.map fun I => if I.bus = B then 1 else 0).sum := by
    intro l
    induction l with
    | nil => exact Nat.le_refl _
    | cons I l ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      have := hitI_le (B := B) (v := v) p.2 s r I
      omega
  exact Nat.le_trans (h1 p.1.inters) (wsumOn_le p.1.inters B hs.1)

theorem hitsTab_le {p : AirD × Table} (hs : SignedOn B p) (s : F) :
    hitsTab p.1 p.2 B v s ≤ wsum p.1 * p.2.h := by
  have := foldr_le_mul (fun r => hitsRow p.1 p.2 B v s r) (wsum p.1) (List.range p.2.h)
    (fun r _ => hitsRow_le hs s r)
  rw [List.length_range, Nat.mul_comm] at this
  exact this

theorem hitsAll_lt {ts : List (AirD × Table)} (hH : HeightsOK ts) (hs : ∀ p ∈ ts, SignedOn B p) (s : F) :
    hitsAll ts B v s < P := by
  have h1 : ∀ (l : List (AirD × Table)), (∀ p ∈ l, SignedOn B p) →
      hitsAll l B v s ≤ l.foldr (fun p acc => wsum p.1 * p.2.h + acc) 0 := by
    intro l
    induction l with
    | nil => intro _; exact Nat.le_refl _
    | cons p l ih =>
      intro hl
      simp only [hitsAll, List.foldr_cons] at ih ⊢
      have := hitsTab_le (v := v) (hl p List.mem_cons_self) s
      have := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      omega
  exact Nat.lt_of_le_of_lt (h1 ts hs) hH

/-- **On a balanced signed bus, as many messages are sent as received**, for
    every tuple. -/
theorem hitsAll_eq {ts : List (AirD × Table)} (hbal : Balanced ts) (hH : HeightsOK ts)
    (hs : ∀ p ∈ ts, SignedOn B p) : hitsAll ts B v 1 = hitsAll ts B v (-1) := by
  have e := hbal B v
  rw [allSends_hits hs] at e
  exact ofN_inj (hitsAll_lt hH hs 1) (hitsAll_lt hH hs (-1)) (sub_eq_zero e)

theorem hitsAll_pos {ts : List (AirD × Table)} {s : F}
    (hit : ∃ p ∈ ts, ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = B ∧
      I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = s) :
    0 < hitsAll ts B v s := by
  obtain ⟨p, hp, r, hr, I, hI, hb, hf, hc⟩ := hit
  have h1 : hitI p.2 B v s r I = 1 := by unfold hitI; rw [if_pos ⟨hb, hf, hc⟩]
  have h2 := le_foldr (fun I => hitI p.2 B v s r I) hI
  have h3 := le_foldr (fun r => hitsRow p.1 p.2 B v s r) (List.mem_range.2 hr)
  have h4 := le_foldr (fun p => hitsTab p.1 p.2 B v s) hp
  simp only [hitsRow, hitsTab, hitsAll] at *
  omega

theorem hit_of_pos {ts : List (AirD × Table)} {s : F} (h : 0 < hitsAll ts B v s) :
    ∃ p ∈ ts, ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = B ∧
      I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = s := by
  obtain ⟨p, hp, h1⟩ := foldr_pos _ ts h
  obtain ⟨r, hr, h2⟩ := foldr_pos _ _ h1
  obtain ⟨I, hI, h3⟩ := foldr_pos _ _ h2
  unfold hitI at h3
  split at h3
  · next hc => exact ⟨p, hp, r, List.mem_range.1 hr, I, hI, hc⟩
  · exact absurd h3 (Nat.lt_irrefl 0)

/-- **The bus lemma between private tables**: on a balanced bus whose counts
    are `0`, `1` or `-1`, a tuple sent with count `1` is received, with
    count `-1`, by some row of some table. -/
theorem bus_match {ts : List (AirD × Table)} (hbal : Balanced ts) (hH : HeightsOK ts)
    (hs : ∀ p ∈ ts, SignedOn B p)
    (hit : ∃ p ∈ ts, ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = B ∧
      I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1) :
    ∃ p ∈ ts, ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = B ∧
      I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = -1 := by
  have h := hitsAll_pos hit
  rw [hitsAll_eq hbal hH hs] at h
  exact hit_of_pos h

/-- **The converse**: a tuple received is sent. -/
theorem bus_match' {ts : List (AirD × Table)} (hbal : Balanced ts) (hH : HeightsOK ts)
    (hs : ∀ p ∈ ts, SignedOn B p)
    (hit : ∃ p ∈ ts, ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = B ∧
      I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = -1) :
    ∃ p ∈ ts, ∃ r, r < p.2.h ∧ ∃ I ∈ p.1.inters, I.bus = B ∧
      I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = 1 := by
  have h := hitsAll_pos hit
  rw [← hitsAll_eq hbal hH hs] at h
  exact hit_of_pos h

end

end Circuit
