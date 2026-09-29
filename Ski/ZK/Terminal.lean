import Ski.ZK.Chain
import Ski.Circuit.CompTable

/-!
# LogUp terminals, as Plonky3 computes them

Plonky3 publishes one terminal per table: the sum, over its rows and its
messages, of `count / (prefix(bus) - fingerprint(fields))`, the
fingerprint by Horner's rule in `β` and the bus prefix any fixed element
(`p3_lookup`: `α` offset by the bus's index).  `terminal` is that sum, the
inverse zero at zero.

- **Balanced tables' terminals sum to zero** (`logup_sum`): LogUp's
  completeness, grouping the messages by bus and tuple.
- **Setting a blinding message on row 0 adds its term** (`terminal_setBlind`).
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Sums in the extension
-- ---------------------------------------------------------------------------

namespace EF

theorem ofF_add (a b : F) : ofF (a + b) = (ofF a).add (ofF b) := by
  apply ext
  · rfl
  · exact (zero_add' 0).symm
  · exact (zero_add' 0).symm
  · exact (zero_add' 0).symm

theorem add_mul (x y z : EF) : (x.add y).mul z = (x.mul z).add (y.mul z) := by
  rw [mul_comm, mul_add, mul_comm z, mul_comm z]

theorem ofF_zero_mul (g : EF) : (ofF 0).mul g = zero := zero_mul g

theorem add_left_comm (x y z : EF) : x.add (y.add z) = y.add (x.add z) := by
  rw [← add_assoc, add_comm x y, add_assoc]

end EF

/-- A list's sum in the extension. -/
def sumL {α : Type} (f : α → EF) (l : List α) : EF := l.foldr (fun a acc => (f a).add acc) EF.zero

theorem sumL_nil {α : Type} (f : α → EF) : sumL f [] = EF.zero := rfl
theorem sumL_cons {α : Type} (f : α → EF) (a : α) (l : List α) : sumL f (a :: l) = (f a).add (sumL f l) := rfl

theorem sumL_append {α : Type} (f : α → EF) : ∀ l m : List α, sumL f (l ++ m) = (sumL f l).add (sumL f m)
  | [], m => (EF.zero_add _).symm
  | a :: l, m => by rw [List.cons_append, sumL_cons, sumL_cons, sumL_append f l m, EF.add_assoc]

theorem sumL_congr {α : Type} {f g : α → EF} : ∀ l : List α, (∀ a ∈ l, f a = g a) → sumL f l = sumL g l
  | [], _ => rfl
  | a :: l, h => by
    rw [sumL_cons, sumL_cons, h a List.mem_cons_self, sumL_congr l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem sumL_add {α : Type} (f g : α → EF) : ∀ l : List α, sumL (fun a => (f a).add (g a)) l = (sumL f l).add (sumL g l)
  | [] => (EF.add_zero _).symm
  | a :: l => by
    rw [sumL_cons, sumL_cons, sumL_cons, sumL_add f g l]
    rw [EF.add_assoc, EF.add_assoc, EF.add_left_comm (g a)]

theorem sumL_zero {α : Type} : ∀ l : List α, sumL (fun _ => EF.zero) l = EF.zero
  | [] => rfl
  | _ :: l => by rw [sumL_cons, sumL_zero l, EF.zero_add]

theorem sumL_flatMap {α β : Type} (f : β → EF) (g : α → List β) : ∀ l : List α,
    sumL f (l.flatMap g) = sumL (fun a => sumL f (g a)) l
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, sumL_append, sumL_flatMap f g l, sumL_cons]

-- ---------------------------------------------------------------------------
-- Grouping by key
-- ---------------------------------------------------------------------------

/-- The counts a list gives key `k`. -/
def countOf {K : Type} [DecidableEq K] (L : List (K × F)) (k : K) : F :=
  L.foldr (fun e acc => (if e.1 = k then e.2 else 0) + acc) 0

theorem sumL_filter {K : Type} (f : K × F → EF) (p : K × F → Bool) : ∀ L : List (K × F),
    sumL f L = (sumL f (L.filter p)).add (sumL f (L.filter (fun e => !p e)))
  | [] => (EF.add_zero _).symm
  | e :: L => by
    rw [sumL_cons, sumL_filter f p L]
    cases hp : p e
    · rw [List.filter_cons_of_neg (by rw [hp]; decide), List.filter_cons_of_pos (by rw [hp]; rfl), sumL_cons,
        EF.add_left_comm]
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by rw [hp]; decide), sumL_cons, EF.add_assoc]

theorem sumL_samekey {K : Type} [DecidableEq K] (g : K → EF) (k0 : K) : ∀ L : List (K × F),
    (∀ e ∈ L, e.1 = k0) → sumL (fun e => (EF.ofF e.2).mul (g e.1)) L = (EF.ofF (countOf L k0)).mul (g k0)
  | [], _ => (EF.ofF_zero_mul _).symm
  | e :: L, h => by
    rw [sumL_cons, sumL_samekey g k0 L (fun e' he' => h e' (List.mem_cons_of_mem _ he')), h e List.mem_cons_self]
    show _ = (EF.ofF ((if e.1 = k0 then e.2 else 0) + countOf L k0)).mul (g k0)
    rw [if_pos (h e List.mem_cons_self), EF.ofF_add, EF.add_mul]

theorem countOf_cons {K : Type} [DecidableEq K] (e : K × F) (L : List (K × F)) (k : K) :
    countOf (e :: L) k = (if e.1 = k then e.2 else 0) + countOf L k := rfl

theorem countOf_filter_ne {K : Type} [DecidableEq K] (k0 k : K) (hk : k ≠ k0) : ∀ L : List (K × F),
    countOf (L.filter (fun e => !decide (e.1 = k0))) k = countOf L k
  | [] => rfl
  | e :: L => by
    rw [countOf_cons]
    rcases (inferInstance : Decidable (e.1 = k0)) with h | h
    · rw [List.filter_cons_of_pos (by simp only [decide_eq_false h, Bool.not_false]), countOf_cons,
        countOf_filter_ne k0 k hk L]
    · rw [List.filter_cons_of_neg (by simp only [decide_eq_true h, Bool.not_true]; decide),
        countOf_filter_ne k0 k hk L, if_neg (by rw [h]; exact Ne.symm hk), zero_add']

theorem countOf_filter_eq {K : Type} [DecidableEq K] (k0 : K) : ∀ L : List (K × F),
    countOf (L.filter (fun e => !decide (e.1 = k0))) k0 = 0
  | [] => rfl
  | e :: L => by
    rcases (inferInstance : Decidable (e.1 = k0)) with h | h
    · rw [List.filter_cons_of_pos (by simp only [decide_eq_false h, Bool.not_false]), countOf_cons,
        countOf_filter_eq k0 L, if_neg h, add_zero']
    · rw [List.filter_cons_of_neg (by simp only [decide_eq_true h, Bool.not_true]; decide), countOf_filter_eq k0 L]

/-- **Messages whose counts cancel key by key contribute nothing**, whatever
    each key's weight. -/
theorem group_zero {K : Type} [DecidableEq K] (g : K → EF) : ∀ (n : Nat) (L : List (K × F)), L.length ≤ n →
    (∀ k, countOf L k = 0) → sumL (fun e => (EF.ofF e.2).mul (g e.1)) L = EF.zero
  | 0, [], _, _ => rfl
  | n + 1, [], _, _ => rfl
  | n + 1, e :: L, hl, h => by
    let k0 := e.1
    rw [sumL_cons, sumL_filter _ (fun e' => decide (e'.1 = k0)) L,
      sumL_samekey g k0 _ (fun e' he' => of_decide_eq_true (List.mem_filter.1 he').2)]
    have hc : e.2 + countOf (L.filter (fun e' => decide (e'.1 = k0))) k0 = 0 := by
      have := h k0
      rw [countOf_cons, if_pos rfl] at this
      have e2 : countOf L k0 = countOf (L.filter (fun e' => decide (e'.1 = k0))) k0 +
          countOf (L.filter (fun e' => !decide (e'.1 = k0))) k0 := by
        clear this hl h
        induction L with
        | nil => exact (zero_add' 0).symm
        | cons e' L ih =>
          rcases (inferInstance : Decidable (e'.1 = k0)) with h' | h'
          · rw [List.filter_cons_of_neg (by simp only [decide_eq_false h']; decide),
              List.filter_cons_of_pos (by simp only [decide_eq_false h', Bool.not_false]), countOf_cons, countOf_cons,
              if_neg h', zero_add', zero_add', ih]
          · rw [List.filter_cons_of_pos (by simp only [decide_eq_true h']), List.filter_cons_of_neg
              (by simp only [decide_eq_true h', Bool.not_true]; decide), countOf_cons, countOf_cons, if_pos h', ih,
              add_assoc']
      rw [e2, countOf_filter_eq, add_zero'] at this
      exact this
    rw [← EF.add_assoc, ← EF.add_mul, ← EF.ofF_add, hc, EF.ofF_zero_mul, EF.zero_add]
    refine group_zero g n _ (Nat.le_trans (List.length_filter_le _ _) (by simp only [List.length_cons] at hl; omega))
      (fun k => ?_)
    rcases (inferInstance : Decidable (k = k0)) with hk | hk
    · rw [countOf_filter_ne k0 k hk]
      have := h k
      rw [countOf_cons, if_neg (fun e' => hk e'.symm), zero_add'] at this
      exact this
    · rw [hk]; exact countOf_filter_eq k0 L

-- ---------------------------------------------------------------------------
-- The terminal
-- ---------------------------------------------------------------------------

/-- A tuple's fingerprint, by Horner's rule in `β`. -/
def hornerL (β : EF) (l : List F) : EF := l.foldl (fun acc e => (acc.mul β).add (EF.ofF e)) EF.zero

/-- A message's LogUp denominator. -/
def den (pre : String → EF) (β : EF) (bus : String) (l : List F) : EF := (pre bus).sub (hornerL β l)

/-- A message's term: its count over its denominator. -/
def msgTerm (pre : String → EF) (β : EF) (I : Inter) (ρ : Atom → F) : EF :=
  (EF.ofF (I.count.eval ρ)).mul (den pre β I.bus (I.fields.map (fun e => e.eval ρ))).inv

def rowTerm (pre : String → EF) (β : EF) (A : AirD) (T : Table) (r : Nat) : EF :=
  sumL (fun I => msgTerm pre β I (T.env r)) A.inters

/-- **A table's LogUp terminal**, as Plonky3 accumulates it: rows, then
    messages. -/
def terminal (pre : String → EF) (β : EF) (A : AirD) (T : Table) : EF :=
  sumL (fun r => rowTerm pre β A T r) (List.range T.h)

/-- A table's messages, as keys (bus and tuple) with counts. -/
def entries (A : AirD) (T : Table) : List ((String × List F) × F) :=
  (List.range T.h).flatMap fun r => A.inters.map fun I =>
    ((I.bus, I.fields.map (fun e => e.eval (T.env r))), I.count.eval (T.env r))

theorem sumL_map {α β : Type} (f : β → EF) (h : α → β) : ∀ l : List α, sumL f (l.map h) = sumL (fun a => f (h a)) l
  | [] => rfl
  | a :: l => by rw [List.map_cons, sumL_cons, sumL_cons, sumL_map f h l]

theorem terminal_entries (pre : String → EF) (β : EF) (A : AirD) (T : Table) :
    terminal pre β A T = sumL (fun e => (EF.ofF e.2).mul (den pre β e.1.1 e.1.2).inv) (entries A T) := by
  unfold terminal entries rowTerm
  rw [sumL_flatMap]
  refine sumL_congr _ (fun r _ => ?_)
  rw [sumL_map]
  rfl

theorem countOf_append {K : Type} [DecidableEq K] (k : K) : ∀ L M : List (K × F),
    countOf (L ++ M) k = countOf L k + countOf M k
  | [], M => (zero_add' _).symm
  | e :: L, M => by rw [List.cons_append, countOf_cons, countOf_cons, countOf_append k L M, add_assoc']

theorem countOf_entries (A : AirD) (T : Table) (bus : String) (v : List F) :
    countOf (entries A T) (bus, v) = tableSends A T bus v := by
  unfold entries tableSends
  generalize List.range T.h = rs
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons, countOf_append, ih, List.foldr_cons]
    congr 1
    unfold rowSends
    generalize A.inters = is
    induction is with
    | nil => rfl
    | cons I is ih2 =>
      rw [List.map_cons, countOf_cons, ih2, List.foldr_cons]
      congr 1
      rcases (inferInstance : Decidable (I.bus = bus ∧ I.fields.map (fun e => e.eval (T.env r)) = v)) with h | h
      · rw [if_neg h, if_neg (fun e => h (by
          rw [Prod.mk.injEq] at e; exact e))]
      · rw [if_pos h, if_pos (by rw [h.1, h.2])]

/-- **LogUp's completeness**: balanced tables' terminals sum to zero, for
    every challenge. -/
theorem logup_sum (pre : String → EF) (β : EF) (ts : List (AirD × Table)) (h : Balanced ts) :
    sumL (fun p => terminal pre β p.1 p.2) ts = EF.zero := by
  rw [sumL_congr ts (fun p _ => terminal_entries pre β p.1 p.2),
    ← sumL_flatMap (fun e => (EF.ofF e.2).mul (den pre β e.1.1 e.1.2).inv)
      (fun p : AirD × Table => entries p.1 p.2) ts]
  have hz : ∀ k, countOf (ts.flatMap (fun p : AirD × Table => entries p.1 p.2)) k = 0 := by
    intro k
    obtain ⟨bus, v⟩ := k
    have hb := h bus v
    rw [← hb]
    clear hb h
    induction ts with
    | nil => rfl
    | cons p ts ih =>
      rw [List.flatMap_cons, countOf_append, ih, countOf_entries, List.foldr_cons]
  have key := group_zero (K := String × List F) (fun k => (den pre β k.1 k.2).inv)
    (ts.flatMap (fun p : AirD × Table => entries p.1 p.2)).length
    (ts.flatMap (fun p : AirD × Table => entries p.1 p.2)) (Nat.le_refl _) hz
  exact key

-- ---------------------------------------------------------------------------
-- Setting a blinding message
-- ---------------------------------------------------------------------------

/-- **A table with a blinding message on row 0**: the tuple `a` at columns
    `c … c + 3`, the flag at `c + 4`. -/
def Table.setBlind (T : Table) (c : Nat) (a : Tup) : Table :=
  ⟨T.h, fun r col => if r = 0 then
      (if col = c then a.t0 else if col = c + 1 then a.t1 else if col = c + 2 then a.t2
       else if col = c + 3 then a.t3 else if col = c + 4 then 1 else T.main r col)
    else T.main r col, T.pre⟩

/-- A leaf off the blinding columns. -/
def avoid (c : Nat) : Atom → Bool
  | .main _ i => !(decide (c ≤ i) && decide (i < c + 5))
  | _ => true

theorem env_setBlind {T : Table} {c : Nat} (a : Tup) (r : Nat) {t : Atom} (h : avoid c t = true) :
    (T.setBlind c a).env r t = T.env r t := by
  cases t with
  | main o i =>
    have hi : ¬ (c ≤ i ∧ i < c + 5) := by
      intro ⟨h1, h2⟩; simp only [avoid, decide_eq_true h1, decide_eq_true h2, Bool.and_self, Bool.not_true] at h
      exact Bool.false_ne_true h
    have hne : ∀ k, k < 5 → i ≠ c + k := by
      intro k hk e
      exact hi ⟨by omega, by omega⟩
    show (if (r + o) % T.h = 0 then _ else T.main ((r + o) % T.h) i) = T.main ((r + o) % T.h) i
    split
    · rw [if_neg (show ¬ i = c from hne 0 (by decide)), if_neg (hne 1 (by decide)), if_neg (hne 2 (by decide)),
        if_neg (hne 3 (by decide)), if_neg (hne 4 (by decide))]; rfl
    · rfl
  | pre o i => rfl
  | first => rfl
  | last => rfl
  | trans => rfl

/-- An interaction off the blinding columns. -/
def Inter.avoids (c : Nat) (I : Inter) : Bool :=
  I.count.onlyAtoms (avoid c) && I.fields.all (·.onlyAtoms (avoid c))

theorem msgTerm_setBlind (pre : String → EF) (β : EF) {c : Nat} {I : Inter} (hI : I.avoids c = true) (T : Table)
    (a : Tup) (r : Nat) : msgTerm pre β I ((T.setBlind c a).env r) = msgTerm pre β I (T.env r) := by
  unfold Inter.avoids at hI
  rw [Bool.and_eq_true, List.all_eq_true] at hI
  have cong := E.eval_congr (p := avoid c) (ρ := (T.setBlind c a).env r) (ρ' := T.env r)
    (fun t ht => env_setBlind (T := T) (c := c) a r ht)
  unfold msgTerm
  rw [cong _ hI.1, List.map_congr_left (fun e he => cong e (hI.2 e he))]

/-- A blinding message: the tuple at `c … c + 3`, counted by the flag at
    `c + 4`, positively or negatively. -/
def blindInter (bus : String) (c : Nat) (neg : Bool) : Inter :=
  ⟨bus, 1, if neg then .neg (.atom (.main 0 (c + 4))) else .atom (.main 0 (c + 4)),
    [.atom (.main 0 c), .atom (.main 0 (c + 1)), .atom (.main 0 (c + 2)), .atom (.main 0 (c + 3))]⟩

def sgn (neg : Bool) : F := if neg then -1 else 1

theorem hornerL_four (β : EF) (a : Tup) : hornerL β [a.t0, a.t1, a.t2, a.t3] = horner β a := by
  show ((((((((EF.zero.mul β).add (EF.ofF a.t0)).mul β).add (EF.ofF a.t1)).mul β).add (EF.ofF a.t2)).mul β).add
    (EF.ofF a.t3)) = horner β a
  rw [EF.zero_mul, EF.zero_add]; rfl

theorem msgTerm_blind_row0 (pre : String → EF) (β : EF) (bus : String) {c : Nat} (neg : Bool) (T : Table)
    (a : Tup) : msgTerm pre β (blindInter bus c neg) ((T.setBlind c a).env 0) =
      (EF.ofF (sgn neg)).mul (blindTerm β (pre bus) a) := by
  have e : ∀ j, (T.setBlind c a).env 0 (.main 0 j) = (T.setBlind c a).main 0 j := fun j => by
    show (T.setBlind c a).main ((0 + 0) % T.h) j = _; rw [Nat.zero_add, Nat.zero_mod]
  have v0 : (T.setBlind c a).main 0 c = a.t0 := by dsimp only [Table.setBlind]; rw [if_pos rfl, if_pos rfl]
  have v1 : (T.setBlind c a).main 0 (c + 1) = a.t1 := by
    dsimp only [Table.setBlind]; rw [if_pos rfl, if_neg (by omega), if_pos rfl]
  have v2 : (T.setBlind c a).main 0 (c + 2) = a.t2 := by
    dsimp only [Table.setBlind]; rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_pos rfl]
  have v3 : (T.setBlind c a).main 0 (c + 3) = a.t3 := by
    dsimp only [Table.setBlind]; rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  have v4 : (T.setBlind c a).main 0 (c + 4) = 1 := by
    dsimp only [Table.setBlind]
    rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  unfold msgTerm blindInter blindTerm den
  simp only [List.map_cons, List.map_nil, E.eval, e, v0, v1, v2, v3]
  rw [hornerL_four]
  congr 2
  cases neg
  · show (T.setBlind c a).env 0 (.main 0 (c + 4)) = sgn false; rw [e, v4]; rfl
  · show -((T.setBlind c a).env 0 (.main 0 (c + 4))) = sgn true; rw [e, v4]; rfl

theorem msgTerm_blind_off (pre : String → EF) (β : EF) (bus : String) {c : Nat} (neg : Bool) (T : Table)
    (hz : ∀ r, r < T.h → T.main r (c + 4) = 0) {r : Nat} (hr : r < T.h) (ρ : Atom → F)
    (hρ : ρ (.main 0 (c + 4)) = T.main r (c + 4)) : msgTerm pre β (blindInter bus c neg) ρ = EF.zero := by
  unfold msgTerm blindInter
  have hc : (if neg then E.neg (.atom (.main 0 (c + 4))) else .atom (.main 0 (c + 4))).eval ρ = 0 := by
    cases neg
    · show ρ _ = 0; rw [hρ, hz r hr]
    · show -(ρ _) = 0; rw [hρ, hz r hr]; decide
  rw [hc]; exact EF.ofF_zero_mul _

theorem sumL_range_single (δ : Nat → EF) (x : EF) {h : Nat} (hh : 0 < h) (h0 : δ 0 = x)
    (hr : ∀ r, 0 < r → δ r = EF.zero) : sumL δ (List.range h) = x := by
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
  rw [List.range_succ_eq_map, sumL_cons, sumL_map, h0,
    sumL_congr _ (fun r _ => hr (r + 1) (Nat.succ_pos r)), sumL_zero, EF.add_zero]

/-- **Setting a blinding message on row 0 adds its term to the terminal**,
    when the table's flag was clear and no other message reads the
    blinding columns. -/
theorem terminal_setBlind (pre : String → EF) (β : EF) {A : AirD} {L1 L2 : List Inter} {bus : String} {c : Nat}
    {neg : Bool} (hA : A.inters = L1 ++ blindInter bus c neg :: L2) (h1 : ∀ I ∈ L1, I.avoids c = true)
    (h2 : ∀ I ∈ L2, I.avoids c = true) (T : Table) (hh : 0 < T.h) (hz : ∀ r, r < T.h → T.main r (c + 4) = 0)
    (a : Tup) :
    terminal pre β A (T.setBlind c a) = (terminal pre β A T).add ((EF.ofF (sgn neg)).mul (blindTerm β (pre bus) a)) := by
  let δ : Nat → EF := fun r => if r = 0 then (EF.ofF (sgn neg)).mul (blindTerm β (pre bus) a) else EF.zero
  have hrow : ∀ r, r < T.h → rowTerm pre β A (T.setBlind c a) r = (rowTerm pre β A T r).add (δ r) := by
    intro r hr
    unfold rowTerm
    rw [hA, sumL_append, sumL_append, sumL_cons, sumL_cons,
      sumL_congr L1 (fun I hI => msgTerm_setBlind pre β (h1 I hI) T a r),
      sumL_congr L2 (fun I hI => msgTerm_setBlind pre β (h2 I hI) T a r)]
    have eT : msgTerm pre β (blindInter bus c neg) (T.env r) = EF.zero :=
      msgTerm_blind_off pre β bus neg T hz hr _ (by show T.main ((r + 0) % T.h) (c + 4) = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hr])
    rw [eT, EF.zero_add]
    rcases Nat.decEq r 0 with h0 | h0
    · rw [msgTerm_blind_off pre β bus neg T hz hr ((T.setBlind c a).env r) (by
        show (T.setBlind c a).main ((r + 0) % T.h) (c + 4) = _
        rw [Nat.add_zero, Nat.mod_eq_of_lt hr]; dsimp only [Table.setBlind]; rw [if_neg h0])]
      show _ = EF.add _ (if r = 0 then (EF.ofF (sgn neg)).mul (blindTerm β (pre bus) a) else EF.zero)
      rw [if_neg h0, EF.zero_add, EF.add_zero]
    · subst h0
      rw [msgTerm_blind_row0]
      show _ = ((sumL _ L1).add (sumL _ L2)).add (if 0 = 0 then (EF.ofF (sgn neg)).mul (blindTerm β (pre bus) a) else EF.zero)
      rw [if_pos rfl, EF.add_assoc, EF.add_comm (sumL _ L2)]
  unfold terminal
  show sumL (fun r => rowTerm pre β A (T.setBlind c a) r) (List.range T.h) = _
  rw [sumL_congr _ (fun r hr => hrow r (List.mem_range.1 hr)), sumL_add,
    sumL_range_single δ _ hh (if_pos rfl) (fun r hr => if_neg (by omega))]

end Circuit
