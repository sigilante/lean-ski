import Ski.Circuit.ProbeSat
import Ski.Circuit.CompComplete

/-!
# What tables send on a bus, counted in one pass

`tableSends A T bus v` sums, over every row and every interaction on
`bus`, the counts of the messages equal to `v`.  Evaluated for each of a
memory table's addresses it costs the table's rows once per address.
Here the same counts come from one pass:

- `sendsOn A T bus` lists every `(tuple, count)` a table sends on `bus`,
  and `tableSends A T bus v` is the sum of the counts whose tuple is `v`
  (`tableSends_eq`);
- `multArr A l` adds each listed count into its address's slot, when the
  tuple is that address's `tupleOf A`; slot `m` is then the sum over `l` of
  the counts with tuple `tupleOf A m` (`multArr_get`), for `A` shorter
  than `P`;
- so a memory table's multiplicity column, `memTable5`'s or
  `memTableC`'s column 4, is `multArr` of its senders' messages
  (`memTable5_mult`, `memTableC_mult`).

`lake exe composed check-p2-tables` uses it to compare the memory's
multiplicities with Lean's definition.
-/

namespace Circuit

/-- Every `(tuple, count)` that `A`'s table `T` sends on `bus`, row by row. -/
def sendsOn (A : AirD) (T : Table) (bus : String) : List (List F × F) :=
  (List.range T.h).flatMap fun r => A.inters.filterMap fun I =>
    if I.bus = bus then some (I.fields.map (fun e => e.eval (T.env r)), I.count.eval (T.env r)) else none

/-- The counts in `l` whose tuple is `v`. -/
def sumMatch (l : List (List F × F)) (v : List F) : F :=
  l.foldr (fun p acc => (if p.1 = v then p.2 else 0) + acc) 0

theorem sumMatch_nil (v : List F) : sumMatch [] v = 0 := rfl

theorem sumMatch_cons (p : List F × F) (l : List (List F × F)) (v : List F) :
    sumMatch (p :: l) v = (if p.1 = v then p.2 else 0) + sumMatch l v := rfl

theorem sumMatch_append (l₁ l₂ : List (List F × F)) (v : List F) :
    sumMatch (l₁ ++ l₂) v = sumMatch l₁ v + sumMatch l₂ v := by
  induction l₁ with
  | nil => rw [List.nil_append, sumMatch_nil, zero_add']
  | cons p l ih => rw [List.cons_append, sumMatch_cons, sumMatch_cons, ih, add_assoc']

/-- One row's interactions, as `rowSends` folds them. -/
theorem inters_eq (T : Table) (bus : String) (v : List F) (r : Nat) : ∀ is : List Inter,
    is.foldr (fun I acc =>
      (if I.bus = bus ∧ I.fields.map (fun e => e.eval (T.env r)) = v then I.count.eval (T.env r) else 0) + acc) 0 =
    sumMatch (is.filterMap fun I =>
      if I.bus = bus then some (I.fields.map (fun e => e.eval (T.env r)), I.count.eval (T.env r)) else none) v
  | [] => rfl
  | I :: is => by
    rw [List.foldr_cons, inters_eq T bus v r is, List.filterMap_cons]
    by_cases hb : I.bus = bus
    · rw [if_pos hb, sumMatch_cons]
      by_cases hv : I.fields.map (fun e => e.eval (T.env r)) = v
      · rw [if_pos ⟨hb, hv⟩, if_pos hv]
      · rw [if_neg (fun h => hv h.2), if_neg hv]
    · rw [if_neg (fun h => hb h.1), if_neg hb, zero_add']

theorem rows_eq (A : AirD) (T : Table) (bus : String) (v : List F) : ∀ rs : List Nat,
    rs.foldr (fun r acc => rowSends A T bus v r + acc) 0 =
    sumMatch (rs.flatMap fun r => A.inters.filterMap fun I =>
      if I.bus = bus then some (I.fields.map (fun e => e.eval (T.env r)), I.count.eval (T.env r)) else none) v
  | [] => rfl
  | r :: rs => by
    rw [List.foldr_cons, List.flatMap_cons, sumMatch_append, rows_eq A T bus v rs]
    unfold rowSends
    rw [inters_eq]

/-- **A table's sends are its listed messages'.** -/
theorem tableSends_eq (A : AirD) (T : Table) (bus : String) (v : List F) :
    tableSends A T bus v = sumMatch (sendsOn A T bus) v :=
  rows_eq A T bus v (List.range T.h)

-- ---------------------------------------------------------------------------
-- One pass over the messages, by address
-- ---------------------------------------------------------------------------

/-- Add `p`'s count into its address's slot, when its tuple is that
    address's in `A`. -/
def multStep (A : List Cell) (arr : Array F) (p : List F × F) : Array F :=
  match p.1 with
  | x :: _ => if x.val < arr.size ∧ p.1 = tupleOf A x.val then arr.modify x.val (· + p.2) else arr
  | [] => arr

/-- Each address's count, over the listed messages. -/
def multArr (A : List Cell) (l : List (List F × F)) : Array F :=
  l.foldl (multStep A) (Array.replicate A.length 0)

theorem multStep_size (A : List Cell) (arr : Array F) (p : List F × F) :
    (multStep A arr p).size = arr.size := by
  obtain ⟨v, c⟩ := p
  cases v with
  | nil => rfl
  | cons x xs =>
    show (if x.val < arr.size ∧ x :: xs = tupleOf A x.val then arr.modify x.val (· + c) else arr).size = _
    by_cases hc : x.val < arr.size ∧ x :: xs = tupleOf A x.val
    · rw [if_pos hc]; exact Array.size_modify
    · rw [if_neg hc]

theorem foldl_size (A : List Cell) : ∀ (l : List (List F × F)) (arr : Array F),
    (l.foldl (multStep A) arr).size = arr.size
  | [], _ => rfl
  | p :: l, arr => by rw [List.foldl_cons, foldl_size A l, multStep_size]

/-- A tuple that is `tupleOf A m` starts with `m`. -/
theorem head_of_tuple {A : List Cell} {m : Nat} {x : F} {xs : List F} (hmP : m < P)
    (h : x :: xs = tupleOf A m) : x.val = m := by
  have h1 : x = ofN m := (List.cons.inj h).1
  rw [h1, val_ofN hmP]

theorem multStep_get (A : List Cell) (arr : Array F) (v : List F) (c : F) (m : Nat)
    (hm : m < arr.size) (hmP : m < P) :
    (multStep A arr (v, c))[m]? = some (arr[m] + (if v = tupleOf A m then c else 0)) := by
  cases v with
  | nil =>
    have : ¬ ([] : List F) = tupleOf A m := fun h => nomatch h
    show arr[m]? = _
    rw [if_neg this, add_zero', Array.getElem?_eq_getElem hm]
  | cons x xs =>
    show (if x.val < arr.size ∧ x :: xs = tupleOf A x.val then arr.modify x.val (· + c) else arr)[m]? = _
    by_cases hc : x.val < arr.size ∧ x :: xs = tupleOf A x.val
    · rw [if_pos hc, Array.getElem?_modify]
      by_cases hxm : x.val = m
      · subst hxm
        rw [if_pos rfl, Array.getElem?_eq_getElem hm, if_pos hc.2]; rfl
      · have : ¬ x :: xs = tupleOf A m := fun h => hxm (head_of_tuple hmP h)
        rw [if_neg hxm, if_neg this, add_zero', Array.getElem?_eq_getElem hm]
    · have : ¬ x :: xs = tupleOf A m := by
        intro h
        have hx := head_of_tuple hmP h
        apply hc
        refine ⟨by rw [hx]; exact hm, ?_⟩
        rw [hx]; exact h
      rw [if_neg hc, if_neg this, add_zero', Array.getElem?_eq_getElem hm]

theorem multArr_go (A : List Cell) (m : Nat) (hmP : m < P) : ∀ (l : List (List F × F)) (arr : Array F)
    (hm : m < arr.size),
    (l.foldl (multStep A) arr)[m]? = some (arr[m] + sumMatch l (tupleOf A m))
  | [], arr, hm => by rw [sumMatch_nil, add_zero', List.foldl_nil, Array.getElem?_eq_getElem hm]
  | (v, c) :: l, arr, hm => by
    have hm' : m < (multStep A arr (v, c)).size := by rw [multStep_size]; exact hm
    rw [List.foldl_cons, multArr_go A m hmP l _ hm']
    have h := multStep_get A arr v c m hm hmP
    rw [Array.getElem?_eq_getElem hm'] at h
    rw [Option.some.inj h, sumMatch_cons, add_assoc']

/-- **Slot `m` is the sum of the counts with tuple `tupleOf A m`.** -/
theorem multArr_get (A : List Cell) (hA : A.length < P) (l : List (List F × F)) (m : Nat) (hm : m < A.length) :
    (multArr A l)[m]? = some (sumMatch l (tupleOf A m)) := by
  have hr : m < (Array.replicate A.length (0 : F)).size := by rw [Array.size_replicate]; exact hm
  unfold multArr
  rw [multArr_go A m (Nat.lt_trans hm hA) l _ hr, Array.getElem_replicate, zero_add']

/-- **The memory's multiplicity column, in one pass**: `memTable5`'s
    column 4 at address `m` is slot `m` of `multArr` over its five
    senders' messages on `mem`. -/
theorem memTable5_mult (A : List Cell) (hA : A.length < P) (cpu prog pop instw pw : AirD) (C Pg Po Iw Pw : Table)
    (m : Nat) (hm : m < A.length) :
    (multArr A (sendsOn cpu C "mem" ++ sendsOn prog Pg "mem" ++ sendsOn pop Po "mem" ++
        sendsOn instw Iw "mem" ++ sendsOn pw Pw "mem"))[m]? =
      some ((memTable5 A cpu prog pop instw pw C Pg Po Iw Pw).main m 4) := by
  rw [multArr_get A hA _ m hm]
  show some (sumMatch _ _) = some (tableSends cpu C "mem" (tupleOf A m) + (tableSends prog Pg "mem" (tupleOf A m) +
      (tableSends pop Po "mem" (tupleOf A m) + (tableSends instw Iw "mem" (tupleOf A m) +
        tableSends pw Pw "mem" (tupleOf A m)))))
  rw [sumMatch_append, sumMatch_append, sumMatch_append, sumMatch_append, tableSends_eq, tableSends_eq,
    tableSends_eq, tableSends_eq, tableSends_eq, add_assoc', add_assoc', add_assoc']

/-- **The memory's multiplicity column, in one pass**, for the memory
    tables of three senders (`memTableC`: the composed, Sudoku and
    hidden-term circuits). -/
theorem memTableC_mult (A : List Cell) (hA : A.length < P) (cpu prog wit : AirD) (C Pg Wt : Table)
    (m : Nat) (hm : m < A.length) :
    (multArr A (sendsOn cpu C "mem" ++ sendsOn prog Pg "mem" ++ sendsOn wit Wt "mem"))[m]? =
      some ((memTableC A cpu prog wit C Pg Wt).main m 4) := by
  rw [multArr_get A hA _ m hm]
  show some (sumMatch _ _) = some (tableSends cpu C "mem" (tupleOf A m) + (tableSends prog Pg "mem" (tupleOf A m) +
      tableSends wit Wt "mem" (tupleOf A m)))
  rw [sumMatch_append, sumMatch_append, tableSends_eq, tableSends_eq, tableSends_eq, add_assoc']

end Circuit
