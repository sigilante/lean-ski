import Ski.Circuit.BaseTable

/-!
# Chains on a balanced bus

A chain bus carries messages `key ‖ level ‖ state`.  Each active row of a
chain table receives one message and sends the next: from node
`(ℓ, s)` to node `(ℓ + 1, s')`, an edge.  A balanced bus is then flow
conservation at every node, with a supply where the CPU starts the chain
and a demand where it ends it (`Edges.Conserve`).

Levels rise by one in the field, so a cycle needs a multiple of `P`
edges, more than the table has.  Hence:

- `Edges.noFlow`: with no supply and no demand, no edge is active;
- `Edges.path`: with a supply at `(0, s₀)` and a demand at `(k, rest)`,
  the active edges are exactly one path `e 0, …, e (k-1)` through levels
  `0, …, k-1`, from `s₀` to `rest`.

The walks pick edges with `List.find?`, so nothing here uses choice.
-/

namespace Circuit

/-- `f 0 + … + f (n-1)`. -/
def sumTo : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

theorem sumTo_add (f g : Nat → Nat) : ∀ n, sumTo n (fun q => f q + g q) = sumTo n f + sumTo n g
  | 0 => rfl
  | n + 1 => by
    show sumTo n (fun q => f q + g q) + (f n + g n) = sumTo n f + f n + (sumTo n g + g n)
    rw [sumTo_add f g n]; omega

theorem sumTo_congr {f g : Nat → Nat} : ∀ n, (∀ q, q < n → f q = g q) → sumTo n f = sumTo n g
  | 0, _ => rfl
  | n + 1, h => by
    show sumTo n f + f n = sumTo n g + g n
    rw [sumTo_congr n (fun q hq => h q (Nat.lt_succ_of_lt hq)), h n (Nat.lt_succ_self n)]

theorem sumTo_pos {f : Nat → Nat} : ∀ n, 0 < sumTo n f → ∃ q, q < n ∧ 0 < f q
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, h => by
    show ∃ q, q < n + 1 ∧ 0 < f q
    rcases Nat.eq_zero_or_pos (f n) with h0 | h0
    · have h' : 0 < sumTo n f := by
        have e : sumTo (n + 1) f = sumTo n f + f n := rfl
        rw [e, h0, Nat.add_zero] at h; exact h
      obtain ⟨q, hq, hf⟩ := sumTo_pos n h'
      exact ⟨q, Nat.lt_succ_of_lt hq, hf⟩
    · exact ⟨n, Nat.lt_succ_self n, h0⟩

theorem sumTo_ge {f : Nat → Nat} : ∀ n q, q < n → f q ≤ sumTo n f
  | 0, _, hq => absurd hq (Nat.not_lt_zero _)
  | n + 1, q, hq => by
    show f q ≤ sumTo n f + f n
    rcases Nat.lt_or_ge q n with h | h
    · exact Nat.le_trans (sumTo_ge n q h) (Nat.le_add_right _ _)
    · rw [Nat.le_antisymm (Nat.le_of_lt_succ hq) h]; exact Nat.le_add_left _ _

/-- A sum of indicators of one point. -/
theorem sumTo_single (x : Nat) (b : Bool) : ∀ n, x < n →
    sumTo n (fun q => if q = x then (if b then 1 else 0) else 0) = if b then 1 else 0
  | 0, hx => absurd hx (Nat.not_lt_zero _)
  | n + 1, hx => by
    show sumTo n _ + (if n = x then (if b then 1 else 0) else 0) = _
    rcases Nat.lt_or_ge x n with h | h
    · rw [sumTo_single x b n h, if_neg (Nat.ne_of_gt h), Nat.add_zero]
    · have e : n = x := Nat.le_antisymm h (Nat.le_of_lt_succ hx)
      rw [if_pos e, sumTo_congr n (g := fun _ => 0) (fun q hq => if_neg (by omega))]
      show sumTo n (fun _ => 0) + _ = _
      have z : ∀ m, sumTo m (fun _ => 0) = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m ih => show sumTo m _ + 0 = 0; rw [ih]
      rw [z, Nat.zero_add]

-- ---------------------------------------------------------------------------
-- Pigeonhole
-- ---------------------------------------------------------------------------

/-- **Pigeonhole**: `H + 1` values below `H` repeat. -/
theorem pigeon : ∀ (H : Nat) (f : Nat → Nat), (∀ n, n ≤ H → f n < H) →
    ∃ a b, a < b ∧ b ≤ H ∧ f a = f b
  | 0, f, h => absurd (h 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | H + 1, f, h => by
    cases hany : (List.range (H + 1)).any (fun n => f n == f (H + 1)) with
    | true =>
      obtain ⟨a, ha, e⟩ := List.any_eq_true.1 hany
      exact ⟨a, H + 1, List.mem_range.1 ha, Nat.le_refl _, beq_iff_eq.1 e⟩
    | false =>
      have hne : ∀ n, n ≤ H → f n ≠ f (H + 1) := fun n hn e =>
        List.any_eq_false.1 hany n (List.mem_range.2 (Nat.lt_succ_of_le hn)) (beq_iff_eq.2 e)
      let g := fun n => if f n = H then f (H + 1) else f n
      have hg : ∀ n, n ≤ H → g n < H := by
        intro n hn
        show (if f n = H then f (H + 1) else f n) < H
        have h1 := h n (Nat.le_succ_of_le hn)
        have h2 := h (H + 1) (Nat.le_refl _)
        rcases Nat.decEq (f n) H with e | e
        · rw [if_neg e]; omega
        · rw [if_pos e]
          have : f (H + 1) ≠ H := fun e' => hne n hn (by rw [e, e'])
          omega
      obtain ⟨a, b, hab, hb, e⟩ := pigeon H g hg
      refine ⟨a, b, hab, Nat.le_succ_of_le hb, ?_⟩
      have ea : g a = if f a = H then f (H + 1) else f a := rfl
      have eb : g b = if f b = H then f (H + 1) else f b := rfl
      rcases Nat.decEq (f a) H with ha | ha <;> rcases Nat.decEq (f b) H with hb' | hb'
      · rw [ea, eb, if_neg ha, if_neg hb'] at e; exact e
      · rw [ea, eb, if_neg ha, if_pos hb'] at e; exact absurd e (hne a (Nat.le_of_lt (Nat.lt_of_lt_of_le hab hb)))
      · rw [ea, eb, if_pos ha, if_neg hb'] at e; exact absurd e.symm (hne b hb)
      · rw [ha, hb']

-- ---------------------------------------------------------------------------
-- Edges
-- ---------------------------------------------------------------------------

theorem add_left_cancelF {a x y : F} (h : a + x = a + y) : x = y := by
  have e : ∀ z : F, z = -a + (a + z) := fun z => by rw [← add_assoc', neg_add_cancel', zero_add']
  rw [e x, e y, h]

/-- A node: a level and a state. -/
abbrev Node := F × List F

/-- A chain table's rows as edges: row `q`, when active, goes from
    `(lvl q, src q)` to `(lvl q + 1, dst q)`. -/
structure Edges where
  H : Nat
  act : Nat → Bool
  lvl : Nat → F
  src : Nat → List F
  dst : Nat → List F

namespace Edges

variable (E : Edges)

def inN (q : Nat) : Node := (E.lvl q, E.src q)
def outN (q : Nat) : Node := (E.lvl q + 1, E.dst q)

/-- The active edges leaving `v`, and entering it. -/
def cntIn (v : Node) : Nat := sumTo E.H fun q => if E.act q && decide (E.inN q = v) then 1 else 0
def cntOut (v : Node) : Nat := sumTo E.H fun q => if E.act q && decide (E.outN q = v) then 1 else 0

def oneIf (a : Option Node) (v : Node) : Nat := if a = some v then 1 else 0

/-- **Flow conservation**, with a supply at `a` and a demand at `b`. -/
def Conserve (a b : Option Node) : Prop := ∀ v, E.cntOut v + oneIf a v = E.cntIn v + oneIf b v

/-- The first active edge leaving `v`. -/
def next (v : Node) : Option Nat := (List.range E.H).find? fun q => E.act q && decide (E.inN q = v)

theorem next_some {v : Node} {q : Nat} (h : E.next v = some q) : q < E.H ∧ E.act q = true ∧ E.inN q = v := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  rw [Bool.and_eq_true, decide_eq_true_iff] at hp
  exact ⟨List.mem_range.1 hm, hp.1, hp.2⟩

theorem next_of_cnt {v : Node} (h : 0 < E.cntIn v) : ∃ q, E.next v = some q := by
  obtain ⟨q, hq, hf⟩ := sumTo_pos E.H h
  cases hn : E.next v with
  | some q' => exact ⟨q', rfl⟩
  | none =>
    exfalso
    have hno := List.find?_eq_none.1 hn q (List.mem_range.2 hq)
    cases hb : (E.act q && decide (E.inN q = v)) with
    | true => exact hno hb
    | false => rw [hb] at hf; exact absurd hf (by decide)

theorem cntIn_pos {q : Nat} (hq : q < E.H) (ha : E.act q = true) : 0 < E.cntIn (E.inN q) :=
  Nat.lt_of_lt_of_le (by rw [ha]; show 0 < if decide (E.inN q = E.inN q) = true then 1 else 0
                         rw [if_pos (decide_eq_true rfl)]; decide)
    (sumTo_ge (f := fun q' => if E.act q' && decide (E.inN q' = E.inN q) then 1 else 0) E.H q hq)

theorem cntOut_pos {q : Nat} (hq : q < E.H) (ha : E.act q = true) : 0 < E.cntOut (E.outN q) :=
  Nat.lt_of_lt_of_le (by rw [ha]; show 0 < if decide (E.outN q = E.outN q) = true then 1 else 0
                         rw [if_pos (decide_eq_true rfl)]; decide)
    (sumTo_ge (f := fun q' => if E.act q' && decide (E.outN q' = E.outN q) then 1 else 0) E.H q hq)

/-- The walk from `v`, one active edge at a time, stopping when none leaves. -/
def walk (v : Node) : Nat → Node
  | 0 => v
  | n + 1 =>
    match E.next (walk v n) with
    | some q => E.outN q
    | none => walk v n

theorem walk_succ (v : Node) (n : Nat) : E.walk v (n + 1) =
    match E.next (E.walk v n) with
    | some q => E.outN q
    | none => E.walk v n := rfl

/-- Along a walk that has not stopped, the level rises by one per step. -/
theorem walk_lvl (v : Node) : ∀ n, (∀ m, m < n → E.next (E.walk v m) ≠ none) →
    (E.walk v n).1 = v.1 + ofN n
  | 0, _ => by show v.1 = v.1 + ofN 0; rw [ofN_zero, add_zero']
  | n + 1, h => by
    have ih := walk_lvl v n (fun m hm => h m (Nat.lt_succ_of_lt hm))
    cases hn : E.next (E.walk v n) with
    | none => exact absurd hn (h n (Nat.lt_succ_self n))
    | some q =>
      have e : E.walk v (n + 1) = E.outN q := by rw [walk_succ, hn]
      obtain ⟨_, _, hin⟩ := E.next_some hn
      rw [e]
      show E.lvl q + 1 = _
      have : E.lvl q = (E.walk v n).1 := congrArg Prod.fst hin
      rw [this, ih, ofN_add, ofN_one, add_assoc']

/-- **A walk stops within `H` steps**: its edges cannot repeat. -/
theorem walk_stops (hH : E.H < P) (v : Node) : ∃ m, m ≤ E.H ∧ E.next (E.walk v m) = none := by
  cases hany : (List.range (E.H + 1)).any (fun m => (E.next (E.walk v m)).isNone) with
  | true =>
    obtain ⟨m, hm, e⟩ := List.any_eq_true.1 hany
    refine ⟨m, Nat.le_of_lt_succ (List.mem_range.1 hm), ?_⟩
    cases h : E.next (E.walk v m) with
    | none => rfl
    | some _ => rw [h] at e; cases e
  | false =>
    exfalso
    have hs : ∀ m, m ≤ E.H → E.next (E.walk v m) ≠ none := by
      intro m hm e
      have := List.any_eq_false.1 hany m (List.mem_range.2 (Nat.lt_succ_of_le hm))
      rw [e] at this; exact this rfl
    let f := fun m => (E.next (E.walk v m)).getD 0
    have hf : ∀ m, m ≤ E.H → E.next (E.walk v m) = some (f m) := by
      intro m hm
      show E.next (E.walk v m) = some ((E.next (E.walk v m)).getD 0)
      cases h : E.next (E.walk v m) with
      | none => exact absurd h (hs m hm)
      | some q => rfl
    obtain ⟨a, b, hab, hb, e⟩ := pigeon E.H f (fun m hm => (E.next_some (hf m hm)).1)
    have ia := (E.next_some (hf a (Nat.le_of_lt (Nat.lt_of_lt_of_le hab hb)))).2.2
    have ib := (E.next_some (hf b hb)).2.2
    rw [e] at ia
    have la := E.walk_lvl v a (fun m hm => hs m (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_trans hm hab) hb)))
    have lb := E.walk_lvl v b (fun m hm => hs m (Nat.le_of_lt (Nat.lt_of_lt_of_le hm hb)))
    have : E.walk v a = E.walk v b := by rw [← ia, ← ib]
    rw [this, lb] at la
    have := ofN_inj (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hab hb) (Nat.le_of_lt hH))
      (Nat.lt_of_le_of_lt hb hH) (add_left_cancelF la).symm
    exact Nat.lt_irrefl a (this ▸ hab)

/-- **No supply, no flow**: without a start or an end, no edge is active. -/
theorem noFlow (hH : E.H < P) (hc : E.Conserve none none) : ∀ q, q < E.H → E.act q = false := by
  intro q0 hq0
  cases ha : E.act q0 with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨m, _, hm⟩ := E.walk_stops hH (E.inN q0)
    have go : ∀ n, E.next (E.walk (E.inN q0) n) ≠ none := by
      intro n
      induction n with
      | zero =>
        obtain ⟨q, hq⟩ := E.next_of_cnt (E.cntIn_pos hq0 ha)
        show E.next (E.inN q0) ≠ none; rw [hq]; exact fun h => nomatch h
      | succ n ih =>
        cases hn : E.next (E.walk (E.inN q0) n) with
        | none => exact absurd hn ih
        | some q =>
          have e : E.walk (E.inN q0) (n + 1) = E.outN q := by rw [walk_succ, hn]
          obtain ⟨hq, hqa, _⟩ := E.next_some hn
          have h1 := E.cntOut_pos hq hqa
          have h2 := hc (E.outN q)
          simp only [oneIf, reduceCtorEq, if_false, Nat.add_zero] at h2
          rw [h2] at h1
          obtain ⟨q', hq'⟩ := E.next_of_cnt h1
          rw [e, hq']; exact fun h => nomatch h
    exact go m hm

/-- The first point at which a test holds, below one where it does. -/
theorem exists_first (p : Nat → Bool) : ∀ n, p n = true → ∃ m, m ≤ n ∧ p m = true ∧ ∀ j, j < m → p j = false
  | n, h => by
    cases hany : (List.range n).any p with
    | false =>
      refine ⟨n, Nat.le_refl n, h, fun j hj => ?_⟩
      have := List.any_eq_false.1 hany j (List.mem_range.2 hj)
      cases hp : p j with
      | false => rfl
      | true => exact absurd hp this
    | true =>
      obtain ⟨j, hj, pj⟩ := List.any_eq_true.1 hany
      have hj' := List.mem_range.1 hj
      obtain ⟨m, hm, pm, hmin⟩ := exists_first p j pj
      exact ⟨m, Nat.le_trans hm (Nat.le_of_lt hj'), pm, hmin⟩
  termination_by n => n
  decreasing_by exact List.mem_range.1 hj

/-- Indicators split on a test. -/
theorem ind_split (a b c : Bool) :
    (if a && c then 1 else 0) = (if a && !b && c then 1 else 0) + (if a && b && c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **Reindexing a sum over a path**: the rows on an injective path,
    counted over the table, are counted over the path. -/
theorem sumTo_path (H : Nat) (act : Nat → Bool) (X : Nat → Bool) (e : Nat → Nat) :
    ∀ k, (∀ i, i < k → e i < H ∧ act (e i) = true) → (∀ i j, i < k → j < k → e i = e j → i = j) →
    sumTo H (fun q => if act q && (List.range k).any (fun i => e i == q) && X q then 1 else 0) =
      sumTo k (fun i => if X (e i) then 1 else 0)
  | 0, _, _ => by
    show sumTo H _ = 0
    have z : ∀ m, sumTo m (fun q => if act q && (List.range 0).any (fun i => e i == q) && X q then 1 else 0) = 0 := by
      intro m; induction m with
      | zero => rfl
      | succ m ih =>
        show sumTo m _ + _ = 0
        rw [ih, Nat.zero_add]
        show (if (act m && (List.range 0).any (fun i => e i == m) && X m) = true then 1 else 0) = 0
        rw [List.range_zero, List.any_nil, Bool.and_false, Bool.false_and]; rfl
    exact z H
  | k + 1, he, hinj => by
    have ih := sumTo_path H act X e k (fun i hi => he i (Nat.lt_succ_of_lt hi))
      (fun i j hi hj => hinj i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj))
    obtain ⟨hkH, hka⟩ := he k (Nat.lt_succ_self k)
    have split : ∀ q, q < H → (if act q && (List.range (k + 1)).any (fun i => e i == q) && X q then 1 else 0) =
        (if act q && (List.range k).any (fun i => e i == q) && X q then 1 else 0) +
        (if q = e k then (if X (e k) then 1 else 0) else 0) := by
      intro q _
      rw [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      rcases Nat.decEq q (e k) with hq | hq
      · rw [if_neg hq]
        have : (e k == q) = false := beq_false_of_ne (fun h => hq h.symm)
        rw [this, Bool.or_false, Nat.add_zero]
      · subst hq
        rw [if_pos rfl, show (e k == e k) = true from beq_self_eq_true' (e k), Bool.or_true, hka]
        have hnot : (List.range k).any (fun i => e i == e k) = false := by
          apply List.any_eq_false.2
          intro i hi h
          have := hinj i k (Nat.lt_succ_of_lt (List.mem_range.1 hi)) (Nat.lt_succ_self k) (beq_iff_eq.1 h)
          have hik := List.mem_range.1 hi
          rw [this] at hik
          exact Nat.lt_irrefl k hik
        rw [hnot]
        cases X (e k) <;> rfl
    rw [sumTo_congr H split, sumTo_add, ih, sumTo_single (e k) (X (e k)) H hkH]
    rfl

/-- The telescope of a walk's nodes. -/
theorem telescope (w : Nat → Node) (v : Node) : ∀ k,
    sumTo k (fun i => if w i = v then 1 else 0) + (if w k = v then 1 else 0) =
      (if w 0 = v then 1 else 0) + sumTo k (fun i => if w (i + 1) = v then 1 else 0)
  | 0 => by show 0 + _ = _ + 0; rw [Nat.zero_add, Nat.add_zero]
  | k + 1 => by
    have ih := telescope w v k
    show sumTo k (fun i => if w i = v then 1 else 0) + (if w k = v then 1 else 0) + (if w (k + 1) = v then 1 else 0) =
      (if w 0 = v then 1 else 0) + (sumTo k (fun i => if w (i + 1) = v then 1 else 0) + (if w (k + 1) = v then 1 else 0))
    omega

/-- **One supply, one demand: one path.**  With a supply at `(0, s₀)` and a
    demand at `(k, rest)`, the active edges are exactly a path through the
    levels `0, …, k-1`, from `s₀` to `rest`. -/
theorem path (hH : E.H < P) {k : Nat} (hk : k < P) {s0 rest : List F}
    (hc : E.Conserve (some ((0 : F), s0)) (some (ofN k, rest))) :
    ∃ (e : Nat → Nat) (st : Nat → List F), st 0 = s0 ∧ st k = rest ∧
      (∀ i, i < k → e i < E.H ∧ E.act (e i) = true ∧ E.lvl (e i) = ofN i ∧
        E.src (e i) = st i ∧ E.dst (e i) = st (i + 1)) ∧
      ∀ q, q < E.H → E.act q = true → ∃ i, i < k ∧ e i = q := by
  let v0 : Node := ((0 : F), s0)
  let sink : Node := (ofN k, rest)
  let w := E.walk v0
  obtain ⟨m0, hm0, hn0⟩ := E.walk_stops hH v0
  let test := fun m => decide (w m = sink) || (E.next (w m)).isNone
  have ht : test m0 = true := by
    show (decide (w m0 = sink) || (E.next (w m0)).isNone) = true
    rw [show w m0 = E.walk v0 m0 from rfl, hn0, Option.isNone_none, Bool.or_true]
  obtain ⟨m, hm, hmt, hmin⟩ := exists_first test m0 ht
  -- before `m`, the walk steps and misses the sink
  have before : ∀ j, j < m → w j ≠ sink ∧ E.next (w j) ≠ none := by
    intro j hj
    have := hmin j hj
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
    refine ⟨this.1, fun h => ?_⟩
    have := this.2; rw [h] at this; cases this
  -- at `m`, the walk is at the sink
  have atSink : w m = sink := by
    cases hs : decide (w m = sink) with
    | true => exact of_decide_eq_true hs
    | false =>
      exfalso
      have hne : w m ≠ sink := of_decide_eq_false hs
      have hnone : E.next (w m) = none := by
        have := hmt
        change (decide (w m = sink) || (E.next (w m)).isNone) = true at this
        rw [hs, Bool.false_or] at this
        cases h : E.next (w m) with
        | none => rfl
        | some _ => rw [h] at this; cases this
      have hpos : 0 < E.cntIn (w m) := by
        have hcv := hc (w m)
        have e1 : oneIf (some (ofN k, rest)) (w m) = 0 := if_neg (fun h => hne (Option.some.inj h).symm)
        rw [e1, Nat.add_zero] at hcv
        rw [← hcv]
        cases m with
        | zero => show 0 < E.cntOut v0 + oneIf (some v0) v0; rw [show oneIf (some v0) v0 = 1 from if_pos rfl]; omega
        | succ j =>
          have hj := (before j (Nat.lt_succ_self j)).2
          cases hq : E.next (w j) with
          | none => exact absurd hq hj
          | some q =>
            obtain ⟨hqH, hqa, _⟩ := E.next_some hq
            have e2 : w (j + 1) = E.outN q := by
              show E.walk v0 (j + 1) = _; rw [walk_succ]; show (match E.next (w j) with | some q => _ | none => _) = _
              rw [hq]
            rw [e2]
            exact Nat.lt_of_lt_of_le (E.cntOut_pos hqH hqa) (Nat.le_add_right _ _)
      obtain ⟨q, hq⟩ := E.next_of_cnt hpos
      rw [hnone] at hq; cases hq
  -- the levels: `m` is `k`
  have hlvl : ∀ i, i ≤ m → (w i).1 = ofN i := by
    intro i hi
    have := E.walk_lvl v0 i (fun j hj => (before j (Nat.lt_of_lt_of_le hj hi)).2)
    rw [this]; show (0 : F) + ofN i = ofN i; rw [zero_add']
  have hmk : m = k := by
    have e := hlvl m (Nat.le_refl m)
    rw [atSink] at e
    exact (ofN_inj hk (Nat.lt_of_le_of_lt (Nat.le_trans hm hm0) hH) e).symm
  subst hmk
  -- the path
  let e := fun i => (E.next (w i)).getD 0
  have he : ∀ i, i < m → E.next (w i) = some (e i) := by
    intro i hi
    show E.next (w i) = some ((E.next (w i)).getD 0)
    cases h : E.next (w i) with
    | none => exact absurd h (before i hi).2
    | some q => rfl
  have hstep : ∀ i, i < m → w (i + 1) = E.outN (e i) := by
    intro i hi
    show E.walk v0 (i + 1) = _
    rw [walk_succ]; show (match E.next (w i) with | some q => _ | none => _) = _
    rw [he i hi]
  have hpath : ∀ i, i < m → e i < E.H ∧ E.act (e i) = true ∧ E.inN (e i) = w i := fun i hi => E.next_some (he i hi)
  refine ⟨e, fun i => (w i).2, rfl, by show (w m).2 = rest; rw [atSink], fun i hi => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hpath i hi
    refine ⟨h1, h2, ?_, congrArg Prod.snd h3, ?_⟩
    · rw [show E.lvl (e i) = (E.inN (e i)).1 from rfl, h3, hlvl i (Nat.le_of_lt hi)]
    · show E.dst (e i) = (w (i + 1)).2; rw [hstep i hi]; rfl
  · -- every active edge is on the path: the rest carries no flow
    have hinj : ∀ i j, i < m → j < m → e i = e j → i = j := by
      intro i j hi hj hij
      have : (E.inN (e i)).1 = (E.inN (e j)).1 := by rw [hij]
      rw [(hpath i hi).2.2, (hpath j hj).2.2, hlvl i (Nat.le_of_lt hi), hlvl j (Nat.le_of_lt hj)] at this
      exact ofN_inj (Nat.lt_trans hi hk) (Nat.lt_trans hj hk) this
    let onPath := fun q => (List.range m).any (fun i => e i == q)
    let E' : Edges := ⟨E.H, fun q => E.act q && !onPath q, E.lvl, E.src, E.dst⟩
    have hre : ∀ i, i < m → e i < E.H ∧ E.act (e i) = true := fun i hi => ⟨(hpath i hi).1, (hpath i hi).2.1⟩
    have cIn : ∀ v, E.cntIn v = E'.cntIn v + sumTo m (fun i => if w i = v then 1 else 0) := by
      intro v
      show sumTo E.H _ = sumTo E.H _ + _
      rw [sumTo_congr E.H (fun q _ => ind_split (E.act q) (onPath q) (decide (E.inN q = v))), sumTo_add]
      congr 1
      rw [sumTo_path E.H E.act (fun q => decide (E.inN q = v)) e m hre hinj]
      apply sumTo_congr m
      intro i hi
      rw [(hpath i hi).2.2]
      simp only [decide_eq_true_eq]
    have cOut : ∀ v, E.cntOut v = E'.cntOut v + sumTo m (fun i => if w (i + 1) = v then 1 else 0) := by
      intro v
      show sumTo E.H _ = sumTo E.H _ + _
      rw [sumTo_congr E.H (fun q _ => ind_split (E.act q) (onPath q) (decide (E.outN q = v))), sumTo_add]
      congr 1
      rw [sumTo_path E.H E.act (fun q => decide (E.outN q = v)) e m hre hinj]
      apply sumTo_congr m
      intro i hi
      rw [← hstep i hi]
      simp only [decide_eq_true_eq]
    have hc' : E'.Conserve none none := by
      intro v
      have h1 := hc v
      have h2 := telescope w v m
      rw [cIn, cOut] at h1
      have o1 : oneIf (some ((0 : F), s0)) v = if w 0 = v then 1 else 0 := by
        show (if some v0 = some v then 1 else 0) = _
        cases hv : decide (v0 = v) with
        | true =>
          rw [if_pos (congrArg some (of_decide_eq_true hv)), if_pos (show w 0 = v from of_decide_eq_true hv)]
        | false =>
          rw [if_neg (fun h => of_decide_eq_false hv (Option.some.inj h)),
            if_neg (show ¬ w 0 = v from of_decide_eq_false hv)]
      have o2 : oneIf (some (ofN m, rest)) v = if w m = v then 1 else 0 := by
        rw [atSink]
        show (if some sink = some v then 1 else 0) = _
        cases hv : decide (sink = v) with
        | true => rw [if_pos (congrArg some (of_decide_eq_true hv)), if_pos (of_decide_eq_true hv)]
        | false =>
          rw [if_neg (fun h => of_decide_eq_false hv (Option.some.inj h)), if_neg (of_decide_eq_false hv)]
      rw [o1, o2] at h1
      show E'.cntOut v + 0 = E'.cntIn v + 0
      omega
    intro q hq ha
    have := E'.noFlow hH hc' q hq
    show ∃ i, i < m ∧ e i = q
    have hon : onPath q = true := by
      cases ho : onPath q with
      | true => rfl
      | false =>
        have e1 : E'.act q = (E.act q && !onPath q) := rfl
        rw [ho, ha] at e1
        rw [e1] at this; cases this
    obtain ⟨i, hi, hiq⟩ := List.any_eq_true.1 hon
    exact ⟨i, List.mem_range.1 hi, beq_iff_eq.1 hiq⟩

end Edges

end Circuit
