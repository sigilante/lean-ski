import Ski.Circuit.Expr

/-!
# AIRs as data, and what a proof of them establishes

An AIR (`AirD`) is what Plonky3's symbolic builder records: polynomial
constraints over the columns, and **interactions**, messages on a named
bus, each a tuple of expressions with a signed count and a per-row weight
bound.  A **table** is its trace: a height and its cells.

**What an accepted proof gives** (assumed of Plonky3; `Sat`, `Balanced`):
- every constraint vanishes on every row of its table (the STARK's
  soundness), with the next row of the last row the first, and the
  selectors `1` on their rows and `0` elsewhere;
- on every bus, for every tuple, the counts sent with that tuple sum to
  zero over all the tables (LogUp's soundness, with Plonky3's check that
  the weighted heights stay below `P`, `HeightsOK`);
- a preprocessed table is the verifier's own (`PreIs`);
- every table has at most `2^27` rows (`TwoAdic`): BabyBear's two-adic
  subgroups, the STARK's evaluation domains, have at most `2^27` points.

These are the assumptions; everything below them is proved.
-/

namespace Circuit

/-- A message on a bus: its tuple, its signed count, the bound on that
    count per row. -/
structure Inter where
  bus : String
  weight : Nat
  count : E
  fields : List E
  deriving Repr

/-- An AIR: its widths, constraints, interactions and preprocessed table. -/
structure AirD where
  name : String
  width : Nat
  pre : Nat
  cons : List E
  inters : List Inter
  pretrace : List (List F)
  deriving Repr

/-- A table: its height and its cells, main and preprocessed. -/
structure Table where
  h : Nat
  main : Nat → Nat → F
  pre : Nat → Nat → F

/-- The leaves' values at row `r`: a column at an offset reads the row that
    many below, wrapping at the end; the selectors are `1` on their rows. -/
def Table.env (T : Table) (r : Nat) : Atom → F
  | .main o i => T.main ((r + o) % T.h) i
  | .pre o i => T.pre ((r + o) % T.h) i
  | .first => if r = 0 then 1 else 0
  | .last => if r + 1 = T.h then 1 else 0
  | .trans => if r + 1 = T.h then 0 else 1

/-- **Every constraint vanishes on every row.** -/
def Sat (A : AirD) (T : Table) : Prop :=
  0 < T.h ∧ ∀ c ∈ A.cons, ∀ r, r < T.h → c.eval (T.env r) = 0

/-- The preprocessed table is the AIR's own. -/
def PreIs (A : AirD) (T : Table) : Prop :=
  T.h = A.pretrace.length ∧ ∀ r i, r < T.h → i < A.pre → T.pre r i = (A.pretrace.getD r []).getD i 0

/-- What one row of one AIR sends on `bus` with tuple `v`. -/
def rowSends (A : AirD) (T : Table) (bus : String) (v : List F) (r : Nat) : F :=
  A.inters.foldr (fun I acc =>
    (if I.bus = bus ∧ I.fields.map (fun e => e.eval (T.env r)) = v then I.count.eval (T.env r) else 0) + acc) 0

/-- What a table sends on `bus` with tuple `v`, over its rows. -/
def tableSends (A : AirD) (T : Table) (bus : String) (v : List F) : F :=
  (List.range T.h).foldr (fun r acc => rowSends A T bus v r + acc) 0

/-- **The buses balance**: for every bus and tuple, the counts sent over
    all the tables sum to zero. -/
def Balanced (ts : List (AirD × Table)) : Prop :=
  ∀ bus v, ts.foldr (fun p acc => tableSends p.1 p.2 bus v + acc) 0 = 0

/-- Plonky3's height check: the weighted heights stay below `P`. -/
def HeightsOK (ts : List (AirD × Table)) : Prop :=
  ts.foldr (fun p acc => (p.1.inters.foldr (fun I a => I.weight + a) 0) * p.2.h + acc) 0 < P

/-- The tables fit BabyBear's two-adic domains. -/
def TwoAdic (ts : List (AirD × Table)) : Prop :=
  ∀ p ∈ ts, p.2.h ≤ 2 ^ 27

-- ---------------------------------------------------------------------------
-- Building AIRs as the Rust does
-- ---------------------------------------------------------------------------

namespace B

def col (i : Nat) : E := .atom (.main 0 i)
def nxt (i : Nat) : E := .atom (.main 1 i)
def prec (i : Nat) : E := .atom (.pre 0 i)
def c (n : Nat) : E := .const (ofN n)
def one : E := c 1
def zero : E := c 0

/-- `sum`, as the Rust folds it. -/
def sum (xs : List E) : E := xs.foldl .add zero

/-- `assert_bool x`: `x (x - 1)`. -/
def bool (x : E) : E := .mul x (.sub x one)
/-- `assert_eq a b`: `a - b`. -/
def eq (a b : E) : E := .sub a b
def whenFirst (x : E) : E := .mul (.atom .first) x
def whenLast (x : E) : E := .mul (.atom .last) x
def whenTrans (x : E) : E := .mul (.atom .trans) x

end B

-- ---------------------------------------------------------------------------
-- Two AIRs the same up to normal forms
-- ---------------------------------------------------------------------------

/-- Two messages the same: bus, weight, and the normal forms of the count
    and the fields. -/
def interEqB (a b : Inter) : Bool :=
  a.bus == b.bus && a.weight == b.weight && a.count.norm == b.count.norm &&
    a.fields.map E.norm == b.fields.map E.norm

/-- **Two AIRs the same**: names, widths, preprocessed tables, and each
    constraint and message the same up to normal form, in order. -/
def sameAirB (a b : AirD) : Bool :=
  a.name == b.name && a.width == b.width && a.pre == b.pre && a.pretrace == b.pretrace &&
    a.cons.map E.norm == b.cons.map E.norm &&
    a.inters.length == b.inters.length && (a.inters.zip b.inters).all fun p => interEqB p.1 p.2

def sameAirsB : List AirD → List AirD → Bool
  | [], [] => true
  | a :: as, b :: bs => sameAirB a b && sameAirsB as bs
  | _, _ => false

theorem map_norm_eval {as bs : List E} (h : as.map E.norm = bs.map E.norm) (ρ : Atom → F) :
    as.map (fun e => e.eval ρ) = bs.map (fun e => e.eval ρ) := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons _ _ => cases h
  | cons a as ih =>
    cases bs with
    | nil => cases h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨E.eval_eq_of_norm h.1 ρ, ih h.2⟩

theorem interEqB_sound {a b : Inter} (h : interEqB a b = true) (ρ : Atom → F) :
    a.bus = b.bus ∧ a.weight = b.weight ∧ a.count.eval ρ = b.count.eval ρ ∧
      a.fields.map (fun e => e.eval ρ) = b.fields.map (fun e => e.eval ρ) := by
  unfold interEqB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, E.eval_eq_of_norm h3 ρ, map_norm_eval h4 ρ⟩

theorem rowSends_eq {as bs : List Inter} (hl : as.length = bs.length)
    (h : (as.zip bs).all (fun p => interEqB p.1 p.2) = true) (ρ : Atom → F) (bus : String) (v : List F) :
    as.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ) = v then I.count.eval ρ else 0) + acc) 0 =
    bs.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ) = v then I.count.eval ρ else 0) + acc) 0 := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons _ _ => cases hl
  | cons a as ih =>
    cases bs with
    | nil => cases hl
    | cons b bs =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
      obtain ⟨hb, hw, hc, hf⟩ := interEqB_sound h.1 ρ
      simp only [List.foldr_cons]
      rw [ih (by simpa using hl) h.2, hb, hc, hf]

/-- **AIRs the comparison calls the same are the same**: the same tables
    satisfy them, their preprocessed tables are the same, and every row
    sends the same on every bus. -/
theorem sameAirB_sound {a b : AirD} (h : sameAirB a b = true) :
    (∀ T, Sat a T ↔ Sat b T) ∧ (∀ T, PreIs a T ↔ PreIs b T) ∧
      (∀ T bus v r, rowSends a T bus v r = rowSends b T bus v r) ∧
      a.inters.map (·.weight) = b.inters.map (·.weight) := by
  unfold sameAirB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hpre⟩, hpt⟩, hcons⟩, hl⟩, hall⟩ := h
  have hc : ∀ ρ, a.cons.map (fun e => e.eval ρ) = b.cons.map (fun e => e.eval ρ) :=
    map_norm_eval hcons
  have hcl : a.cons.length = b.cons.length := by
    simpa using congrArg List.length hcons
  refine ⟨fun T => ?_, fun T => ?_, fun T bus v r => rowSends_eq hl hall (T.env r) bus v, ?_⟩
  · unfold Sat
    constructor
    · rintro ⟨hh, hs⟩
      refine ⟨hh, fun c hc' r hr => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
      have e := congrArg (fun l => l[i]?) (hc (T.env r))
      simp only [List.getElem?_map] at e
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)] at e
      simp only [Option.map_some, Option.some.injEq] at e
      rw [← e]
      exact hs _ (List.getElem_mem _) r hr
    · rintro ⟨hh, hs⟩
      refine ⟨hh, fun c hc' r hr => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
      have e := congrArg (fun l => l[i]?) (hc (T.env r))
      simp only [List.getElem?_map] at e
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (l := b.cons) (by omega)] at e
      simp only [Option.map_some, Option.some.injEq] at e
      rw [e]
      exact hs _ (List.getElem_mem _) r hr
  · unfold PreIs
    rw [hpre, hpt]
  · have : ∀ (as bs : List Inter), as.length = bs.length →
        (as.zip bs).all (fun p => interEqB p.1 p.2) = true → as.map (·.weight) = bs.map (·.weight) := by
      intro as
      induction as with
      | nil => intro bs hl _; cases bs with
        | nil => rfl
        | cons _ _ => cases hl
      | cons a as ih =>
        intro bs hl h
        cases bs with
        | nil => cases hl
        | cons b bs =>
          simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
          obtain ⟨_, hw, _, _⟩ := interEqB_sound h.1 (fun _ => 0)
          simp only [List.map_cons, hw, ih bs (by simpa using hl) h.2]
    exact this _ _ hl hall

-- ---------------------------------------------------------------------------
-- Acceptance, and its transfer between AIRs the comparison calls the same
-- ---------------------------------------------------------------------------

/-- **What an accepted proof of a list of AIRs gives**: one table per AIR,
    each satisfying its AIR, the preprocessed ones the verifier's, the bus
    balanced, and the heights within Plonky3's check and the field's
    domains. -/
def Accepted (As : List AirD) (ts : List Table) : Prop :=
  As.length = ts.length ∧ (∀ p ∈ As.zip ts, Sat p.1 p.2 ∧ (p.1.pre = 0 ∨ PreIs p.1 p.2)) ∧
    Balanced (As.zip ts) ∧ HeightsOK (As.zip ts) ∧ TwoAdic (As.zip ts)

theorem sameAirsB_length : ∀ {As Bs : List AirD}, sameAirsB As Bs = true → As.length = Bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [sameAirsB, Bool.and_eq_true] at h
    simp only [List.length_cons, sameAirsB_length h.2]

theorem sameAirB_pre {a b : AirD} (h : sameAirB a b = true) : a.pre = b.pre := by
  unfold sameAirB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.2

theorem interEqB_symm {a b : Inter} (h : interEqB a b = true) : interEqB b a = true := by
  unfold interEqB at *
  simp only [Bool.and_eq_true, beq_iff_eq] at *
  exact ⟨⟨⟨h.1.1.1.symm, h.1.1.2.symm⟩, h.1.2.symm⟩, h.2.symm⟩

theorem zip_all_symm : ∀ (as bs : List Inter), (as.zip bs).all (fun p => interEqB p.1 p.2) = true →
    (bs.zip as).all (fun p => interEqB p.1 p.2) = true
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨interEqB_symm h.1, zip_all_symm as bs h.2⟩

theorem sameAirB_symm {a b : AirD} (h : sameAirB a b = true) : sameAirB b a = true := by
  unfold sameAirB at *
  simp only [Bool.and_eq_true, beq_iff_eq] at *
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨⟨⟨⟨⟨⟨h1.symm, h2.symm⟩, h3.symm⟩, h4.symm⟩, h5.symm⟩, h6.symm⟩, zip_all_symm _ _ h7⟩

theorem sameAirsB_symm : ∀ {As Bs : List AirD}, sameAirsB As Bs = true → sameAirsB Bs As = true
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [sameAirsB, Bool.and_eq_true] at h ⊢
    exact ⟨sameAirB_symm h.1, sameAirsB_symm h.2⟩

/-- **Acceptance transfers** between AIRs the comparison calls the same. -/
theorem accepted_transfer : ∀ {As Bs : List AirD} {ts : List Table}, sameAirsB As Bs = true →
    Accepted As ts → Accepted Bs ts
  | As, Bs, ts, hs, ⟨hl, hsat, hbal, hht, htwo⟩ => by
    have hlen := sameAirsB_length hs
    -- pointwise facts over the three lists
    have key : ∀ (As Bs : List AirD) (ts : List Table), sameAirsB As Bs = true →
        (∀ p ∈ As.zip ts, Sat p.1 p.2 ∧ (p.1.pre = 0 ∨ PreIs p.1 p.2)) →
        (∀ p ∈ Bs.zip ts, Sat p.1 p.2 ∧ (p.1.pre = 0 ∨ PreIs p.1 p.2)) ∧
        (∀ bus v, (As.zip ts).foldr (fun p acc => tableSends p.1 p.2 bus v + acc) 0 =
          (Bs.zip ts).foldr (fun p acc => tableSends p.1 p.2 bus v + acc) 0) ∧
        (As.zip ts).foldr (fun p acc => (p.1.inters.foldr (fun I a => I.weight + a) 0) * p.2.h + acc) 0 =
          (Bs.zip ts).foldr (fun p acc => (p.1.inters.foldr (fun I a => I.weight + a) 0) * p.2.h + acc) 0 ∧
        (Bs.zip ts).map (·.2) = (As.zip ts).map (·.2) := by
      intro As
      induction As with
      | nil =>
        intro Bs ts hs _
        cases Bs with
        | nil => exact ⟨fun _ h => (nomatch h), fun _ _ => rfl, rfl, rfl⟩
        | cons _ _ => simp [sameAirsB] at hs
      | cons a As ih =>
        intro Bs ts hs hp
        cases Bs with
        | nil => simp [sameAirsB] at hs
        | cons b Bs =>
          simp only [sameAirsB, Bool.and_eq_true] at hs
          obtain ⟨hsat', hpre', hrow', hw'⟩ := sameAirB_sound hs.1
          have hpre0 := sameAirB_pre hs.1
          cases ts with
          | nil => exact ⟨fun _ h => (nomatch h), fun _ _ => rfl, rfl, rfl⟩
          | cons T ts =>
            have hp0 := hp (a, T) List.mem_cons_self
            obtain ⟨i1, i2, i3, i4⟩ := ih Bs ts hs.2 (fun p hp' => hp p (List.mem_cons_of_mem _ hp'))
            have hts : ∀ bus v, tableSends a T bus v = tableSends b T bus v := by
              intro bus v
              unfold tableSends
              congr 1
              funext r acc
              rw [hrow' T bus v r]
            have hwt : a.inters.foldr (fun I x => I.weight + x) 0 = b.inters.foldr (fun I x => I.weight + x) 0 := by
              have : ∀ l : List Inter, l.foldr (fun I x => I.weight + x) 0 = (l.map (·.weight)).foldr (· + ·) 0 := by
                intro l; induction l with
                | nil => rfl
                | cons _ _ ih => simp only [List.foldr_cons, List.map_cons, ih]
              rw [this, this, hw']
            refine ⟨fun p hp' => ?_, fun bus v => ?_, ?_, ?_⟩
            · rcases List.mem_cons.1 hp' with rfl | hp'
              · refine ⟨(hsat' T).1 hp0.1, ?_⟩
                rcases hp0.2 with h0 | h0
                · exact .inl (hpre0 ▸ h0)
                · exact .inr ((hpre' T).1 h0)
              · exact i1 p hp'
            · simp only [List.zip_cons_cons, List.foldr_cons]
              rw [hts, i2]
            · simp only [List.zip_cons_cons, List.foldr_cons]
              rw [hwt, i3]
            · simp only [List.zip_cons_cons, List.map_cons, i4]
    obtain ⟨k1, k2, k3, k4⟩ := key As Bs ts hs hsat
    refine ⟨hlen ▸ hl, k1, fun bus v => (k2 bus v) ▸ hbal bus v, ?_, ?_⟩
    · unfold HeightsOK; rw [← k3]; exact hht
    · intro p hp
      have : p.2 ∈ (Bs.zip ts).map (·.2) := List.mem_map.2 ⟨p, hp, rfl⟩
      rw [k4] at this
      obtain ⟨q, hq, e⟩ := List.mem_map.1 this
      rw [← e]; exact htwo q hq

end Circuit
