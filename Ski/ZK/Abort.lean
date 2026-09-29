import Ski.ZK.Generic
import Ski.ZK.Terminal

/-!
# How often a zero denominator aborts an honest proof

Plonky3's prover inverts the denominator of every message with a nonzero
multiplicity (`p3_lookup`, `logup.rs`; a zero multiplicity gets the
placeholder `1`), and panics on a zero.  `Aborts` counts every message,
a superset of that event, so the bound is conservative.  A denominator is
`prefix(bus) - fingerprint(fields)`, and the prefix is `α + (bus + 1) γ`
(`challenges.rs`), with `γ` a power of `β`: the challenge `α` plus an
offset free of `α`.  So for each message exactly one `α` zeroes it, and
for any tables, any `β` and any blinding, at most one `α` per message
aborts the proof (`abort_count`): the number of messages out of the
`P^4` challenges.  The bound holds for every witness, so however the abort
event depends on the witness, it moves the proof's distribution by at
most that fraction.
-/

namespace Circuit

/-- Every message of a set of tables. -/
def allEntries (ts : List (AirD × Table)) : List ((String × List F) × F) :=
  ts.flatMap fun p => entries p.1 p.2

/-- **The prover aborts**: some message's denominator is zero. -/
def Aborts (pre : String → EF) (β : EF) (ts : List (AirD × Table)) : Bool :=
  (allEntries ts).any fun e => decide (den pre β e.1.1 e.1.2 = EF.zero)

/-- Plonky3's bus prefixes: `α` plus an offset free of `α`. -/
def prefixOf (α : EF) (off : String → EF) : String → EF := fun b => α.add (off b)

/-- A sum over a list. -/
def natSum {α : Type} (l : List α) (f : α → Nat) : Nat := l.foldr (fun a acc => f a + acc) 0

theorem any_le {α : Type} (p : α → Bool) : ∀ l : List α,
    (if l.any p then 1 else 0) ≤ natSum l (fun e => if p e then 1 else 0)
  | [] => Nat.le_refl 0
  | a :: l => by
    have ih := any_le p l
    show (if (p a || l.any p) then 1 else 0) ≤ (if p a then 1 else 0) + natSum l _
    cases p a
    · exact Nat.le_trans ih (Nat.le_add_left _ _)
    · exact Nat.le_add_right _ _

theorem sumTo_natSum {α : Type} (g : Nat → α → Nat) (n : Nat) : ∀ l : List α,
    sumTo n (fun i => natSum l (g i)) = natSum l (fun e => sumTo n (fun i => g i e))
  | [] => by
    show sumTo n (fun _ => 0) = 0
    rw [sumTo_const, Nat.mul_zero]
  | a :: l => by
    show sumTo n (fun i => g i a + natSum l (g i)) = sumTo n (fun i => g i a) + natSum l _
    rw [sumTo_add, sumTo_natSum g n l]

theorem natSum_le {α : Type} {f g : α → Nat} : ∀ l : List α, (∀ e ∈ l, f e ≤ g e) → natSum l f ≤ natSum l g
  | [], _ => Nat.le_refl 0
  | a :: l, h => Nat.add_le_add (h a List.mem_cons_self)
      (natSum_le l (fun e he => h e (List.mem_cons_of_mem a he)))

theorem natSum_one {α : Type} : ∀ l : List α, natSum l (fun _ => 1) = l.length
  | [] => rfl
  | a :: l => by
    show 1 + natSum l _ = l.length + 1
    rw [natSum_one l, Nat.add_comm]

theorem sub_eq_zero_iff (x y : EF) : x.sub y = EF.zero ↔ x = y :=
  ⟨fun h => by have e := EF.sub_add_cancel x y; rw [h, EF.zero_add] at e; exact e.symm,
   fun h => by rw [h, EF.sub_self]⟩

theorem prefix_den (α o h : EF) : (α.add o).sub h = α.sub (h.sub o) :=
  Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).sub (Q.var 2)) (q := (Q.var 0).sub ((Q.var 2).sub (Q.var 1)))
    (by decide) (env3 α o h)

theorem toEF_eq {a : Tup} {t : EF} : a.toEF = t ↔ a = ⟨t.x0, t.x1, t.x2, t.x3⟩ :=
  ⟨fun h => by rw [← h]; rfl, fun h => by rw [h]; rfl⟩

/-- **One challenge per message zeroes its denominator.** -/
theorem den_one (off : String → EF) (β : EF) (bus : String) (l : List F) :
    sumTo Q4 (fun i => if decide (den (prefixOf (Tup.dec i).toEF off) β bus l = EF.zero) then 1 else 0) = 1 := by
  let t := (hornerL β l).sub (off bus)
  let a0 : Tup := ⟨t.x0, t.x1, t.x2, t.x3⟩
  have key : ∀ a : Tup, den (prefixOf a.toEF off) β bus l = EF.zero ↔ a = a0 := by
    intro a
    show ((a.toEF).add (off bus)).sub (hornerL β l) = EF.zero ↔ _
    rw [prefix_den, sub_eq_zero_iff]
    exact toEF_eq
  refine sumTo_one Q4 (Tup.enc_lt a0) ?_ (fun i hi hne => ?_)
  · rw [Tup.dec_enc, decide_eq_true ((key a0).2 rfl)]; rfl
  · rw [decide_eq_false (fun h => hne (by rw [← (key _).1 h, Tup.enc_dec hi]))]; rfl

/-- **The abort bound**: for any bus offsets, any `β` and any tables, at
    most one challenge `α` per message aborts the prover, out of `P^4`. -/
theorem abort_count (off : String → EF) (β : EF) (ts : List (AirD × Table)) :
    sumTo Q4 (fun i => if Aborts (prefixOf (Tup.dec i).toEF off) β ts then 1 else 0) ≤ (allEntries ts).length := by
  let g : Nat → ((String × List F) × F) → Nat := fun i e =>
    if decide (den (prefixOf (Tup.dec i).toEF off) β e.1.1 e.1.2 = EF.zero) then 1 else 0
  calc sumTo Q4 (fun i => if Aborts (prefixOf (Tup.dec i).toEF off) β ts then 1 else 0)
      ≤ sumTo Q4 (fun i => natSum (allEntries ts) (g i)) := sumTo_mono Q4 (fun i _ => any_le _ _)
    _ = natSum (allEntries ts) (fun e => sumTo Q4 (fun i => g i e)) := sumTo_natSum g Q4 _
    _ = natSum (allEntries ts) (fun _ => 1) := by
        refine Nat.le_antisymm (natSum_le _ (fun e _ => ?_)) (natSum_le _ (fun e _ => ?_))
        · exact Nat.le_of_eq (den_one off β e.1.1 e.1.2)
        · exact Nat.le_of_eq (den_one off β e.1.1 e.1.2).symm
    _ = (allEntries ts).length := natSum_one _

/-- The number of messages: each table's height times its interactions. -/
theorem entries_length (A : AirD) (T : Table) : (entries A T).length = T.h * A.inters.length := by
  unfold entries
  rw [List.length_flatMap]
  have : ∀ n, (List.map (fun r => (A.inters.map fun I =>
      ((I.bus, I.fields.map (fun e => e.eval (T.env r))), I.count.eval (T.env r))).length) (List.range n)).sum =
      n * A.inters.length := by
    intro n
    induction n with
    | zero => rw [Nat.zero_mul]; rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_map, Nat.add_zero,
        Nat.succ_mul]
  exact this T.h

end Circuit
