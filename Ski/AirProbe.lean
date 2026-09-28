import Ski.AirJet
import Ski.InstOpen
import Ski.ProbeTree

set_option linter.unusedSectionVars false

open Term

/-!
# The AIR with probe segments: an output, bound

A probe run applies a term to atom markers and ends at the marker of the
constructor it is (`Air.air_probe`).  To read a whole value, each field is
probed in turn (`Ski/Decode.lean`, `Ski/ProbeTree.lean`).  This module
does that in one table: the table's rows fall into **segments**, one per
node of the value's probe tree in depth-first order.

- A segment starts from a term applied to its own block of marker atoms,
  and runs (machine transitions and jet instantiations) until the head is
  the expected constructor's marker with exactly that constructor's
  fields on the stack.
- A **probe row** ends a segment and starts the next.  It takes the next
  segment's term from its parent segment's fields, writes the next block
  of markers, and applies the term to them as application cells, which
  the machine then unwinds.

**The theorems.**
- `planOf`: the segments of a probe tree, depth first, their marker
  blocks consecutive (`planOf_consec`).
- `decV_of_segs`: the assembly.  If every segment's start term, applied
  to its fresh markers, weakly reduces to the expected marker applied to
  the segment's fields, and every child's start term is its parent's
  field, then the root's term reads as the tree.
- `air_probe_sound`: a table the AIR with probe segments accepts, for the
  plan of `v`, proves that the term reads as `v`; with the bridge,
  `Decodes t o` (`air_probe_decodes`).
-/

namespace Air

open Mach Probe

-- ---------------------------------------------------------------------------
-- The plan: a probe tree's segments, depth first
-- ---------------------------------------------------------------------------

/-- A probe segment: its markers are the atoms `base … base + k - 1`; the
    term it probes is the `ctor`-th of `k` constructors, with `arity`
    fields; it reads field `field` of segment `parent`. -/
structure Seg where
  base : Nat
  k : Nat
  ctor : Nat
  arity : Nat
  parent : Nat
  field : Nat
  deriving Repr, DecidableEq

/-- The markers a list of segments takes, in all. -/
def kSum : List Seg → Nat
  | [] => 0
  | s :: ss => s.k + kSum ss

mutual
  /-- The segments of `v`, which reads field `field` of segment `parent`,
      with markers from `base` and first index `idx`. -/
  def planGo : V → Nat → Nat → Nat → Nat → List Seg
    | .node c k ch, parent, field, base, idx =>
      ⟨base, k, c, ch.length, parent, field⟩ :: planKids ch idx 0 (base + k) (idx + 1)
  /-- The segments of the fields `vs` of segment `parent`, from field `i`. -/
  def planKids : List V → Nat → Nat → Nat → Nat → List Seg
    | [], _, _, _, _ => []
    | v :: vs, parent, i, base, idx =>
      planGo v parent i base idx ++
        planKids vs parent (i + 1) (base + kSum (planGo v parent i base idx))
          (idx + (planGo v parent i base idx).length)
end

/-- **The plan of a probe tree**, markers from `b0`. -/
def planOf (v : V) (b0 : Nat) : List Seg := planGo v 0 0 b0 0

theorem kSum_append : ∀ (a b : List Seg), kSum (a ++ b) = kSum a + kSum b
  | [], _ => by simp [kSum]
  | s :: a, b => by simp [kSum, kSum_append a b]; omega

/-- Marker blocks laid end to end from `b`. -/
def Consec : List Seg → Nat → Prop
  | [], _ => True
  | s :: l, b => s.base = b ∧ Consec l (b + s.k)

theorem Consec.append : ∀ {a c : List Seg} {b : Nat}, Consec a b → Consec c (b + kSum a) →
    Consec (a ++ c) b
  | [], _, b, _, hc => by simpa [kSum] using hc
  | s :: a, c, b, ha, hc => ⟨ha.1, Consec.append ha.2 (by rw [kSum, ← Nat.add_assoc] at hc; exact hc)⟩

mutual
  theorem planGo_consec : ∀ (v : V) (parent field base idx : Nat),
      Consec (planGo v parent field base idx) base
    | .node _ k ch, _, _, base, idx => ⟨rfl, planKids_consec ch idx 0 (base + k) (idx + 1)⟩
  theorem planKids_consec : ∀ (vs : List V) (parent i base idx : Nat),
      Consec (planKids vs parent i base idx) base
    | [], _, _, _, _ => trivial
    | v :: vs, parent, i, base, idx =>
      Consec.append (planGo_consec v parent i base idx) (planKids_consec vs parent (i + 1) _ _)
end

theorem Consec.head : ∀ {l : List Seg} {b : Nat} {s : Seg}, Consec l b → l[0]? = some s → s.base = b
  | [], _, _, _, h => by cases h
  | _ :: _, _, _, hc, h => by cases h; exact hc.1

theorem Consec.next : ∀ {l : List Seg} {b j : Nat} {s s' : Seg}, Consec l b →
    l[j]? = some s → l[j + 1]? = some s' → s'.base = s.base + s.k
  | [], _, _, _, _, _, h, _ => by cases h
  | x :: l, b, 0, s, s', hc, h, h' => by
    simp at h h'
    subst h
    exact (hc.2.head (by simpa using h')).trans (by rw [hc.1])
  | x :: l, b, j + 1, s, s', hc, h, h' => Consec.next hc.2 (by simpa using h) (by simpa using h')

-- Each segment after the first reads a field of an earlier one.
mutual
  theorem planGo_parent : ∀ (v : V) (parent field base idx q : Nat) (s : Seg),
      (planGo v parent field base idx)[q]? = some s →
      (q = 0 ∧ s.parent = parent) ∨ (idx ≤ s.parent ∧ s.parent < idx + q)
    | .node _ _ _, _, _, _, _, 0, s, h => by
      simp [planGo] at h
      exact .inl ⟨rfl, by rw [← h]⟩
    | .node c k ch, parent, field, base, idx, q + 1, s, h => by
      simp only [planGo, List.getElem?_cons_succ] at h
      rcases planKids_parent ch idx 0 (base + k) (idx + 1) q s h with e | ⟨h1, h2⟩
      · exact .inr ⟨by omega, by omega⟩
      · exact .inr ⟨by omega, by omega⟩
  theorem planKids_parent : ∀ (vs : List V) (parent i base idx q : Nat) (s : Seg),
      (planKids vs parent i base idx)[q]? = some s →
      s.parent = parent ∨ (idx ≤ s.parent ∧ s.parent < idx + q)
    | [], _, _, _, _, _, _, h => by simp [planKids] at h
    | v :: vs, parent, i, base, idx, q, s, h => by
      simp only [planKids] at h
      by_cases hq : q < (planGo v parent i base idx).length
      · rw [List.getElem?_append_left hq] at h
        rcases planGo_parent v parent i base idx q s h with ⟨_, e⟩ | ⟨h1, h2⟩
        · exact .inl e
        · exact .inr ⟨h1, h2⟩
      · rw [List.getElem?_append_right (by omega)] at h
        rcases planKids_parent vs parent (i + 1) _ _ _ s h with e | ⟨h1, h2⟩
        · exact .inl e
        · exact .inr ⟨by omega, by omega⟩
end

theorem planOf_consec (v : V) (b0 : Nat) : Consec (planOf v b0) b0 := planGo_consec v 0 0 b0 0

theorem planOf_parent {v : V} {b0 j : Nat} {s : Seg} (hj : 0 < j) (h : (planOf v b0)[j]? = some s) :
    s.parent < j := by
  rcases planGo_parent v 0 0 b0 0 j s h with ⟨e, _⟩ | ⟨_, h2⟩
  · omega
  · omega

-- ---------------------------------------------------------------------------
-- Slices of a plan
-- ---------------------------------------------------------------------------

/-- `s` occurs in `plan` from index `idx`. -/
def Slice (plan : List Seg) (idx : Nat) (s : List Seg) : Prop :=
  ∀ i, i < s.length → plan[idx + i]? = s[i]?

theorem Slice.cons {plan : List Seg} {idx : Nat} {x : Seg} {s : List Seg}
    (h : Slice plan idx (x :: s)) : plan[idx]? = some x ∧ Slice plan (idx + 1) s := by
  refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
  have := h (i + 1) (by simp; omega)
  rw [show idx + (i + 1) = idx + 1 + i by omega] at this
  simpa using this

theorem Slice.append {plan : List Seg} {idx : Nat} {a b : List Seg}
    (h : Slice plan idx (a ++ b)) : Slice plan idx a ∧ Slice plan (idx + a.length) b := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := h i (by simp; omega)
    rw [List.getElem?_append_left hi] at this
    exact this
  · have := h (a.length + i) (by simp; omega)
    rw [List.getElem?_append_right (by omega), show a.length + i - a.length = i by omega,
      ← Nat.add_assoc] at this
    exact this

-- ---------------------------------------------------------------------------
-- The assembly: segments that probe, read as the tree
-- ---------------------------------------------------------------------------

section Assembly

variable [Kit]

/-- **What a table gives of each segment**: its start term `F j` is fresh
    below its markers, and applied to them weakly reduces to the expected
    marker applied to the segment's fields `A j`; a later segment's start
    term is its parent's field. -/
structure SegsOK (plan : List Seg) (F : Nat → OTerm) (A : Nat → List OTerm) : Prop where
  fresh : ∀ j s, plan[j]? = some s → Fresh s.base (F j)
  run : ∀ j s, plan[j]? = some s →
    OWSteps (appO (F j) (vars s.base) s.k) (appL (.var (s.ctor + s.base)) (A j)) ∧
      (A j).length = s.arity
  link : ∀ j s, 0 < j → plan[j]? = some s → s.field < (A s.parent).length →
    (A s.parent)[s.field]? = some (F j)

mutual
  theorem decV_go {plan : List Seg} {F : Nat → OTerm} {A : Nat → List OTerm} (h : SegsOK plan F A) :
      ∀ (v : V) (parent field base idx : Nat), Slice plan idx (planGo v parent field base idx) →
        DecV (F idx) v
    | .node c k ch, parent, field, base, idx, hs => by
      unfold planGo at hs
      obtain ⟨h0, hk⟩ := hs.cons
      obtain ⟨hrun, hlen⟩ := h.run idx _ h0
      obtain ⟨A', hA', hall⟩ := owsteps_spine hrun
      have hkids := decV_kids h ch idx 0 (base + k) (idx + 1) (Nat.succ_pos idx) hk (by rw [Nat.zero_add]; exact hlen)
      rw [List.drop_zero] at hkids
      exact DecV.of_probe (h.fresh idx _ h0) hA' (DecVs.of_allw hall hkids)
  theorem decV_kids {plan : List Seg} {F : Nat → OTerm} {A : Nat → List OTerm} (h : SegsOK plan F A) :
      ∀ (vs : List V) (parent i base idx : Nat), 0 < idx → Slice plan idx (planKids vs parent i base idx) →
        (A parent).length = i + vs.length → DecVs ((A parent).drop i) vs
    | [], parent, i, _, _, _, _, hl => by
      rw [List.drop_eq_nil_of_le (Nat.le_of_eq (hl.trans (Nat.add_zero i)))]
      trivial
    | v :: vs, parent, i, base, idx, hpos, hs, hl => by
      rw [List.length_cons] at hl
      have hi : i < (A parent).length := by
        rw [hl]; exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
      have hl' : (A parent).length = i + 1 + vs.length := by
        rw [hl, Nat.add_comm vs.length 1, Nat.add_assoc]
      unfold planKids at hs
      obtain ⟨h1, h2⟩ := hs.append
      -- the child's first segment reads field `i` of `parent`
      have hfirst : ∃ s, plan[idx]? = some s ∧ s.parent = parent ∧ s.field = i := by
        cases v with
        | node c k ch =>
          have := h1 0 (by unfold planGo; exact Nat.zero_lt_succ _)
          rw [Nat.add_zero] at this
          unfold planGo at this
          exact ⟨_, this, rfl, rfl⟩
      have hFv : DecV (F idx) v := decV_go h v parent i base idx h1
      have hget : (A parent)[i]? = some (F idx) := by
        obtain ⟨s, hs, hp, hf⟩ := hfirst
        have := h.link idx s hpos hs (by rw [hp, hf]; exact hi)
        rwa [hp, hf] at this
      have hrest := decV_kids h vs parent (i + 1) _ _ (Nat.lt_of_lt_of_le hpos (Nat.le_add_right _ _)) h2 hl'
      rw [List.drop_eq_getElem_cons hi]
      have e : (A parent)[i]'hi = F idx := by
        rw [List.getElem?_eq_getElem hi] at hget
        exact Option.some.inj hget
      rw [e]
      exact ⟨hFv, hrest⟩
end

end Assembly

-- ---------------------------------------------------------------------------
-- The rows
-- ---------------------------------------------------------------------------

/-- A stack of the pointers `ps`, top first, from address `c`, on a nil. -/
def stkCells : List Nat → Nat → List Cell
  | [], _ => [.nil]
  | p :: ps, c => .cons p (c + 1) :: stkCells ps (c + 1)

/-- The cells a probe row writes from `c`: the markers `b … b + k - 1`, then
    a stack of them, the first on top. -/
def pcells (b k c : Nat) : List Cell :=
  (List.range k).map (fun i => .atom (b + i)) ++ stkCells ((List.range k).map (c + ·)) (c + k)

/-- **The probe constraint** of one row, starting segment `s` on the term
    at `F`: the markers and their stack written at the counter.  The next
    row has `F` at the head and the markers on the stack. -/
def probeRowG (g : Nat → Option Cell) (s : Seg) (F : Nat) (r : Row) : Option Row :=
  if wrsG g r.ctr (pcells s.base s.k r.ctr) then
    some ⟨F, r.ctr + s.k, r.ctr + (pcells s.base s.k r.ctr).length⟩
  else none

/-- The same, over the memory table. -/
def probeRow (M : List Cell) (s : Seg) (F : Nat) (r : Row) : Option Row :=
  probeRowG (fun a => M[a]?) s F r

/-- **The end constraint** of segment `s`, with fields `ps`: the head is
    the marker of constructor `s.ctor`, and the stack is exactly the
    pointers `ps`, `s.arity` of them, on a nil. -/
def endRowG (g : Nat → Option Cell) (s : Seg) (ps : List Nat) (r : Row) : Bool :=
  rdG g r.ctr r.hd == some (.atom (s.ctor + s.base)) &&
    match popR g r.ctr s.arity r.stk with
    | some (qs, rest) => qs == ps && rdG g r.ctr rest == some .nil
    | none => false

/-- The same, over the memory table. -/
def endRow (M : List Cell) (s : Seg) (ps : List Nat) (r : Row) : Bool :=
  endRowG (fun a => M[a]?) s ps r

/-- A row within a segment: it steps, instantiates a jet at a listed root,
    or has halted and repeats. -/
def NormRow (M : List Cell) (roots : List (Nat × Nat)) (jets : List Jet) (r r' : Row) : Prop :=
  stepRow M r = some r' ∨
    (∃ g J, (r.hd, g) ∈ roots ∧ jets[g]? = some J ∧ instRow M J r = some r') ∨
    (haltRow M r = true ∧ r' = r)

/-- The pointer segment `j` probes: the loaded term's root for the first,
    else its parent's field. -/
def fptr (plan : List Seg) (fld : Nat → List Nat) (hd0 : Nat) (j : Nat) : Nat :=
  if j = 0 then hd0 else
    match plan[j]? with
    | some s => ((fld s.parent)[s.field]?).getD 0
    | none => 0

/-- **The AIR with probe segments accepts** a table over `M`, from the
    state `m0`, for the public roots, jets and plan.  Segment `j` starts at
    row `p j` with a probe row, and ends at row `p (j + 1)`, where its
    fields are `fld j`; the table's last row is `p plan.length`.  Every
    other row is a row within a segment. -/
structure AcceptsP (M : List Cell) (m0 : Mach) (roots : List (Nat × Nat)) (jets : List Jet)
    (plan : List Seg) (p : Nat → Nat) (fld : Nat → List Nat) (row : Nat → Row) : Prop where
  nonempty : 0 < plan.length
  heap0 : M.take (row 0).ctr = m0.heap
  hd0 : (row 0).hd = m0.hd
  ctr0 : (row 0).ctr = m0.heap.length
  p0 : p 0 = 0
  pmono : ∀ j, j < plan.length → p j < p (j + 1)
  probe : ∀ j s, plan[j]? = some s →
    probeRow M s (fptr plan fld (row 0).hd j) (row (p j)) = some (row (p j + 1))
  fields : ∀ j s, 0 < j → plan[j]? = some s → s.field < (fld s.parent).length
  norm : ∀ i, i < p plan.length → (∀ j, j < plan.length → i ≠ p j) →
    NormRow M roots jets (row i) (row (i + 1))
  ends : ∀ j s, plan[j]? = some s → endRow M s (fld j) (row (p (j + 1))) = true

-- ---------------------------------------------------------------------------
-- Atoms: only the markers
-- ---------------------------------------------------------------------------

/-- Every atom in `h` is below `B`. -/
def AB (h : List Cell) (B : Nat) : Prop := ∀ n, Cell.atom n ∈ h → n < B

theorem AB.append {h ws : List Cell} {B : Nat} (h1 : AB h B) (h2 : AB ws B) : AB (h ++ ws) B :=
  fun n hn => (List.mem_append.1 hn).elim (h1 n) (h2 n)

theorem AB.mono {h : List Cell} {B B' : Nat} (hh : AB h B) (hB : B ≤ B') : AB h B' :=
  fun n hn => Nat.lt_of_lt_of_le (hh n hn) hB

theorem AB.take {h : List Cell} {B : Nat} (hh : AB h B) (c : Nat) : AB (h.take c) B :=
  fun n hn => hh n (List.mem_of_mem_take hn)

/-- An open term read from a heap whose atoms are below `B` is fresh below `B`. -/
theorem fresh_of_AB {h : List Cell} {B : Nat} (hh : AB h B) :
    ∀ {f a : Nat} {u : OTerm}, otermAt h f a = some u → Fresh B u
  | 0, _, _, hu => by cases hu
  | f + 1, a, u, hu => by
    intro i hi
    rcases otermAt_cell hu with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨n, hc, e⟩ | ⟨g, x, tg, tx, _, hg, hx, e⟩
    · subst e; cases hi
    · subst e; cases hi
    · subst e; cases hi
    · subst e
      cases hi
      exact hh i (List.mem_of_getElem? hc)
    · subst e
      cases hi with
      | left _ hl => exact fresh_of_AB hh hg i hl
      | right _ hr => exact fresh_of_AB hh hx i hr

theorem stkCells_AB : ∀ (ps : List Nat) (c B : Nat), AB (stkCells ps c) B
  | [], _, _ => by intro n hn; simp [stkCells] at hn
  | p :: ps, c, B => by
    intro n hn
    simp only [stkCells, List.mem_cons, reduceCtorEq, false_or] at hn
    exact stkCells_AB ps (c + 1) B n hn

theorem pcells_AB (b k c : Nat) : AB (pcells b k c) (b + k) := by
  intro n hn
  unfold pcells at hn
  rcases List.mem_append.1 hn with h | h
  · obtain ⟨i, hi, e⟩ := List.mem_map.1 h
    cases e
    rw [List.mem_range] at hi
    omega
  · exact stkCells_AB _ _ _ n h

theorem stepG_AB {g : Nat → Option Cell} {c hd stk h' s' : Nat} {ws : List Cell}
    (h : stepG g c hd stk = some (h', s', ws)) (B : Nat) : AB ws B := by
  intro n hn
  unfold stepG at h
  repeat' split at h
  all_goals (cases h <;> simp at hn)

theorem icells_AB (env : Nat → Nat) (B : Nat) : ∀ (c : Nat) (t : OTerm), AB (icells env c t).1 B
  | _, .S => by intro n hn; simp [icells] at hn
  | _, .K => by intro n hn; simp [icells] at hn
  | _, .I => by intro n hn; simp [icells] at hn
  | _, .var _ => by intro n hn; simp [icells] at hn
  | c, .app f a => by
    intro n hn
    simp only [icells, List.mem_append, List.mem_cons, reduceCtorEq, List.not_mem_nil,
      or_false] at hn
    rcases hn with (h | h)
    · exact icells_AB env B c f n h
    · exact icells_AB env B _ a n h

theorem load_AB (t : Term) (B : Nat) : AB (load t).heap B := by
  have : ∀ (t : Term) (h : List Cell), AB h B → AB (build h t).1 B := by
    intro t
    induction t with
    | S => intro h hh; exact hh.append (by intro n hn; simp at hn)
    | K => intro h hh; exact hh.append (by intro n hn; simp at hn)
    | I => intro h hh; exact hh.append (by intro n hn; simp at hn)
    | app f a ihf iha =>
      intro h hh
      exact (iha _ (ihf h hh)).append (by intro n hn; simp at hn)
  exact (this t [] (by intro n hn; simp at hn)).append (by intro n hn; simp at hn)

-- ---------------------------------------------------------------------------
-- One row at a time
-- ---------------------------------------------------------------------------

theorem wrs_len {M : List Cell} {c : Nat} {ws : List Cell} (hc : c ≤ M.length)
    (h : wrs M c ws = true) : c + ws.length ≤ M.length := by
  have hl := congrArg List.length (take_of_wrs h)
  rw [List.length_take, List.length_append, take_length hc] at hl
  omega

/-- A probe row writes its cells at the counter. -/
theorem probeRow_spec {M : List Cell} {s : Seg} {F : Nat} {r r' : Row} (hc : r.ctr ≤ M.length)
    (h : probeRow M s F r = some r') :
    r'.hd = F ∧ r'.stk = r.ctr + s.k ∧ r'.ctr = r.ctr + (pcells s.base s.k r.ctr).length ∧
      M.take r'.ctr = M.take r.ctr ++ pcells s.base s.k r.ctr ∧ r'.ctr ≤ M.length := by
  unfold probeRow probeRowG at h
  split at h
  · next hw =>
    cases h
    rw [← wrs_G] at hw
    exact ⟨rfl, rfl, rfl, take_of_wrs hw, wrs_len hc hw⟩
  · cases h

/-- A row within a segment writes no atom, and is a jetted step or none. -/
theorem normRow_spec {M : List Cell} {roots : List (Nat × Nat)} {jets : List Jet} {c0 : Nat}
    (hroots : RootsOK (M.take c0) roots jets) {r r' : Row} (hc0 : c0 ≤ r.ctr)
    (hc : r.ctr ≤ M.length) (h : NormRow M roots jets r r') :
    r.ctr ≤ r'.ctr ∧ r'.ctr ≤ M.length ∧ JSteps (st M r) (st M r') ∧
      ∃ ws, M.take r'.ctr = M.take r.ctr ++ ws ∧ ∀ B, AB ws B := by
  rcases h with hs | ⟨g, J, hm, hJ, hI⟩ | hh
  · obtain ⟨hm, hc'⟩ := stepRow_mstep hc hs
    unfold stepRow at hs
    cases hg : stepG (rd M r.ctr) r.ctr r.hd r.stk with
    | none => rw [hg] at hs; cases hs
    | some q =>
      obtain ⟨h1, s1, ws⟩ := q
      rw [hg] at hs
      dsimp only at hs
      cases hw : wrs M r.ctr ws with
      | false => rw [hw] at hs; cases hs
      | true =>
        rw [hw, if_pos rfl] at hs
        cases hs
        exact ⟨by show _ ≤ _ + _; omega, hc', .step (.mach hm) (.refl _),
          ws, take_of_wrs hw, stepG_AB hg⟩
  · obtain ⟨hj, hc'⟩ := instRow_jstep hroots hc0 hc hm hJ hI
    unfold instRow instRowG at hI
    cases hp : popR (fun a => M[a]?) r.ctr J.xs.length r.stk with
    | none => rw [hp] at hI; cases hI
    | some q =>
      obtain ⟨ps, rest⟩ := q
      rw [hp] at hI
      dsimp only at hI
      split at hI
      · next hw =>
        cases hI
        rw [← wrs_G] at hw
        exact ⟨by show _ ≤ _ + _; omega, hc', .step hj (.refl _), _, take_of_wrs hw,
          fun B => icells_AB _ B _ _⟩
      · cases hI
  · rw [hh.2]
    exact ⟨Nat.le_refl _, hc, .refl _, [], by simp, fun B n hn => by cases hn⟩

/-- A stack of pointers, written, reads back as their terms. -/
theorem stkCells_ostack {heap : List Cell} : ∀ (ps : List Nat) (Ns : List OTerm) (c f : Nat),
    (∀ q, q < (stkCells ps c).length → heap[c + q]? = (stkCells ps c)[q]?) →
    OPtrsOK heap 1 ps Ns → ostackAt heap (f + ps.length + 1) c = some Ns
  | [], [], c, f, hw, _ => by
    have := hw 0 (by simp [stkCells])
    simp [stkCells] at this
    unfold ostackAt
    rw [this]
  | p :: ps, N :: Ns, c, f, hw, hok => by
    have h0 := hw 0 (by simp [stkCells])
    simp [stkCells] at h0
    have ih := stkCells_ostack ps Ns (c + 1) f (fun q hq => by
      have := hw (q + 1) (by simp [stkCells]; omega)
      rw [show c + (q + 1) = c + 1 + q by omega] at this
      simpa [stkCells] using this) hok.2
    rw [show f + (p :: ps).length + 1 = (f + ps.length + 1) + 1 by simp; omega]
    unfold ostackAt
    rw [h0]
    dsimp only
    rw [otermAt_mono hok.1 (by omega), ih]
  | [], _ :: _, _, _, _, hok => by cases hok
  | _ :: _, [], _, _, _, hok => by cases hok

theorem appL_range (t : OTerm) (ks : Nat → OTerm) : ∀ k : Nat,
    appL t ((List.range k).map ks) = appO t ks k
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.map_append, appL_app, appL_range t ks k]
    rfl

theorem markers_ok (heap : List Cell) (b c : Nat) : ∀ k : Nat,
    (∀ i, i < k → heap[c + i]? = some (.atom (b + i))) →
    OPtrsOK heap 1 ((List.range k).map (c + ·)) ((List.range k).map (vars b))
  | 0, _ => trivial
  | k + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append]
    have ih := markers_ok heap b c k (fun i hi => h i (by omega))
    have hl : ∀ {ps : List Nat} {Ns : List OTerm} {p : Nat} {N : OTerm},
        OPtrsOK heap 1 ps Ns → otermAt heap 1 p = some N → OPtrsOK heap 1 (ps ++ [p]) (Ns ++ [N]) := by
      intro ps
      induction ps with
      | nil =>
        intro Ns p N hok hp
        cases Ns with
        | nil => exact ⟨hp, trivial⟩
        | cons _ _ => cases hok
      | cons q ps ihp =>
        intro Ns p N hok hp
        cases Ns with
        | nil => cases hok
        | cons M Ns => exact ⟨hok.1, ihp hok.2 hp⟩
    refine hl ih ?_
    unfold otermAt
    rw [h k (by omega)]
    show some (OTerm.var (b + k)) = some (OTerm.var (k + b))
    rw [Nat.add_comm]

/-- **A probe row starts its segment**: the next state reads back as the
    probed term applied to the segment's markers. -/
theorem probeRow_decode {M : List Cell} {s : Seg} {F : Nat} {r r' : Row} {Ft : OTerm}
    (hc : r.ctr ≤ M.length) (h : probeRow M s F r = some r')
    (hF : otermAt (M.take r.ctr) (r.ctr + 1) F = some Ft) :
    odecode (st M r') = some (appO Ft (vars s.base) s.k) := by
  obtain ⟨hhd, hstk, hctr, htake, hc'⟩ := probeRow_spec hc h
  have hlen : (M.take r'.ctr).length = r'.ctr := take_length hc'
  rw [← appL_range]
  apply odecode_of
  · show otermAt (M.take r'.ctr) ((M.take r'.ctr).length + 1) r'.hd = some Ft
    rw [htake, hhd]
    refine otermAt_grow hF ?_
    rw [List.length_append, take_length hc]
    omega
  · show ostackAt (M.take r'.ctr) ((M.take r'.ctr).length + 1) r'.stk = some _
    have hat : ∀ q, q < (pcells s.base s.k r.ctr).length →
        (M.take r'.ctr)[r.ctr + q]? = (pcells s.base s.k r.ctr)[q]? := by
      intro q hq
      rw [htake, List.getElem?_append_right (by rw [take_length hc]; omega), take_length hc,
        show r.ctr + q - r.ctr = q by omega]
    have hpl : (pcells s.base s.k r.ctr).length = s.k + (s.k + 1) := by
      unfold pcells
      have : ∀ (ps : List Nat) c, (stkCells ps c).length = ps.length + 1 := by
        intro ps; induction ps with
        | nil => intro c; rfl
        | cons _ _ ih => intro c; simp [stkCells, ih]
      simp [this]
    have hok := markers_ok (M.take r'.ctr) s.base r.ctr s.k (fun i hi => by
      rw [hat i (by omega)]
      unfold pcells
      rw [List.getElem?_append_left (by simpa using hi)]
      simp [hi])
    have hst := stkCells_ostack ((List.range s.k).map (r.ctr + ·)) ((List.range s.k).map (vars s.base))
      (r.ctr + s.k) (r'.ctr - s.k) (fun q hq => by
        rw [show r.ctr + s.k + q = r.ctr + (s.k + q) by omega, hat (s.k + q) (by
          rw [hpl]; have : (stkCells ((List.range s.k).map (r.ctr + ·)) (r.ctr + s.k)).length ≤ s.k + 1 := by
            have : ∀ (ps : List Nat) c, (stkCells ps c).length = ps.length + 1 := by
              intro ps; induction ps with
              | nil => intro c; rfl
              | cons _ _ ih => intro c; simp [stkCells, ih]
            rw [this]; simp
          omega)]
        unfold pcells
        rw [List.getElem?_append_right (by simp), show s.k + q - ((List.range s.k).map _).length = q by simp])
      hok
    have e : r'.ctr - s.k + ((List.range s.k).map (r.ctr + ·)).length + 1 =
        (M.take r'.ctr).length + 1 := by
      rw [hlen, List.length_map, List.length_range]
      rw [hpl] at hctr
      omega
    rw [hstk, ← e]
    exact hst

/-- **An end row reads its segment's fields**: the state reads back as
    the constructor's marker applied to the terms at the fields. -/
theorem endRow_decode {M : List Cell} {s : Seg} {ps : List Nat} {r : Row} {u : OTerm}
    (hc : r.ctr ≤ M.length) (hd : odecode (st M r) = some u) (h : endRow M s ps r = true) :
    ∃ Ns, u = appL (.var (s.ctor + s.base)) Ns ∧ Ns.length = s.arity ∧
      OPtrsOK (M.take r.ctr) (r.ctr + 1) ps Ns := by
  have hlen : (M.take r.ctr).length = r.ctr := take_length hc
  obtain ⟨hdT, args, h1, h2, hu⟩ := odecode_eq hd
  change otermAt (M.take r.ctr) ((M.take r.ctr).length + 1) r.hd = some hdT at h1
  change ostackAt (M.take r.ctr) ((M.take r.ctr).length + 1) r.stk = some args at h2
  rw [hlen] at h1 h2
  unfold endRow endRowG at h
  rw [Bool.and_eq_true, beq_iff_eq, ← rd_G, rd_eq] at h
  obtain ⟨ha, hp⟩ := h
  have hv : hdT = .var (s.ctor + s.base) := by
    rcases otermAt_cell h1 with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨n, e, ev⟩ | ⟨_, _, _, _, e, _⟩
    · rw [ha] at e; cases e
    · rw [ha] at e; cases e
    · rw [ha] at e; cases e
    · rw [ha] at e; cases e; exact ev
    · rw [ha] at e; cases e
  rw [popR_popN] at hp
  cases hq : popN (M.take r.ctr) s.arity r.stk with
  | none => rw [hq] at hp; cases hp
  | some q =>
    obtain ⟨qs, rest⟩ := q
    rw [hq] at hp
    dsimp only at hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, rd_eq] at hp
    obtain ⟨hqs, hnil⟩ := hp
    subst hqs
    obtain ⟨Ns, restT, G, _, hargs, hlN, _, hok, hrest⟩ := popN_ospec s.arity hq h2
    have hr : restT = [] := by
      cases G with
      | zero => unfold ostackAt at hrest; cases hrest
      | succ G =>
        rcases ostackAt_cell hrest with ⟨_, e⟩ | ⟨_, _, _, _, e, _⟩
        · exact e
        · rw [hnil] at e; cases e
    refine ⟨Ns, ?_, hlN, hok⟩
    rw [hu, hv, hargs, hr, List.append_nil]

theorem _root_.Mach.JSteps.snoc_all {m m1 m2 : Mach} (h : JSteps m m1) (h2 : JSteps m1 m2) :
    JSteps m m2 := by
  induction h with
  | refl _ => exact h2
  | step h1 _ ih => exact .step h1 (ih h2)

-- ---------------------------------------------------------------------------
-- Soundness
-- ---------------------------------------------------------------------------

theorem otermAt_take {M : List Cell} {c c' f f' a : Nat} {u : OTerm} (hcc : c ≤ c')
    (hf : f ≤ f') (h : otermAt (M.take c) f a = some u) :
    otermAt (M.take c') f' a = some u := by
  have e : M.take c' = M.take c ++ (M.take c').drop c := by
    have ht : (M.take c').take c = M.take c := by rw [List.take_take, Nat.min_eq_left hcc]
    calc M.take c' = (M.take c').take c ++ (M.take c').drop c := (List.take_append_drop _ _).symm
      _ = _ := by rw [ht]
  rw [e]
  exact otermAt_grow h hf

end Air

namespace Mach

theorem OPtrsOK.get {h : List Cell} {F : Nat} : ∀ {ps : List Nat} {Ns : List OTerm} {i : Nat},
    OPtrsOK h F ps Ns → i < ps.length →
    ∃ a N, ps[i]? = some a ∧ Ns[i]? = some N ∧ otermAt h F a = some N
  | [], _, _, _, hi => by simp at hi
  | _ :: _, [], _, hok, _ => by cases hok
  | p :: ps, N :: Ns, 0, hok, _ => ⟨p, N, rfl, rfl, hok.1⟩
  | _ :: ps, _ :: Ns, i + 1, hok, hi => get (ps := ps) (Ns := Ns) (i := i) hok.2 (by simp at hi; omega)

theorem OPtrsOK.map_getD {h : List Cell} {F : Nat} (d : OTerm) : ∀ {ps : List Nat} {Ns : List OTerm},
    OPtrsOK h F ps Ns → ps.map (fun a => (otermAt h F a).getD d) = Ns
  | [], [], _ => rfl
  | _ :: _, _ :: _, hok => by
    simp only [List.map_cons, hok.1, Option.getD_some, map_getD d hok.2]
  | [], _ :: _, hok => by cases hok
  | _ :: _, [], hok => by cases hok

theorem OPtrsOK.length {h : List Cell} {F : Nat} : ∀ {ps : List Nat} {Ns : List OTerm},
    OPtrsOK h F ps Ns → ps.length = Ns.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, hok => by simp [length hok.2]
  | [], _ :: _, hok => by cases hok
  | _ :: _, [], hok => by cases hok

end Mach

namespace Air

open Mach Probe

theorem load_otermAt (t : Term) :
    otermAt (load t).heap ((load t).heap.length + 1) (load t).hd = some t.toO := by
  obtain ⟨_, _, l, ht⟩ := build_spec t []
  refine otermAt_of_termAt (termAt_mono (termAt_append ht) ?_)
  show _ ≤ ((build [] t).1 ++ [Cell.nil]).length + 1
  rw [length_concat]
  omega

/-- The term segment `j` probes, read at its probe row. -/
def Fp (M : List Cell) (plan : List Seg) (p : Nat → Nat) (fld : Nat → List Nat) (row : Nat → Row)
    (j : Nat) : OTerm :=
  (otermAt (M.take (row (p j)).ctr) ((row (p j)).ctr + 1) (fptr plan fld (row 0).hd j)).getD .S

/-- The fields of segment `j`, read at its end row. -/
def Ap (M : List Cell) (p : Nat → Nat) (fld : Nat → List Nat) (row : Nat → Row) (j : Nat) :
    List OTerm :=
  (fld j).map fun a => (otermAt (M.take (row (p (j + 1))).ctr) ((row (p (j + 1))).ctr + 1) a).getD .S

theorem pmono_le {p : Nat → Nat} {n : Nat} (hp : ∀ j, j < n → p j < p (j + 1)) :
    ∀ {a b : Nat}, a ≤ b → b ≤ n → p a ≤ p b := by
  intro a b hab hb
  induction b with
  | zero => rw [Nat.le_zero.1 hab]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hab with h | h
    · exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_of_lt (hp b (by omega)))
    · rw [h]; exact Nat.le_refl _

theorem not_start {p : Nat → Nat} {n j i : Nat} (hp : ∀ j, j < n → p j < p (j + 1)) (hj : j < n)
    (h1 : p j < i) (h2 : i < p (j + 1)) : ∀ j', j' < n → i ≠ p j' := by
  intro j' hj' e
  subst e
  rcases Nat.lt_or_ge j j' with h | h
  · have := pmono_le hp (show j + 1 ≤ j' by omega) (by omega)
    omega
  · have := pmono_le hp h (by omega)
    omega

section Sound

variable {M : List Cell} {t : Term} {roots : List (Nat × Nat)} {jets : List Jet} {plan : List Seg}
  {p : Nat → Nat} {fld : Nat → List Nat} {row : Nat → Row}

theorem AcceptsP.c0 (h : AcceptsP M (load t) roots jets plan p fld row) : (row 0).ctr ≤ M.length := by
  have := congrArg List.length h.heap0
  rw [List.length_take, ← h.ctr0] at this
  omega

/-- Counters: every row's lies between the first row's and the table's
    length, and grows. -/
theorem AcceptsP.ctrs (h : AcceptsP M (load t) roots jets plan p fld row)
    (hroots : RootsOK (load t).heap roots jets) :
    ∀ i, i ≤ p plan.length → (row 0).ctr ≤ (row i).ctr ∧ (row i).ctr ≤ M.length ∧
      (0 < i → (row (i - 1)).ctr ≤ (row i).ctr) := by
  have hr0 : RootsOK (M.take (row 0).ctr) roots jets := by rw [h.heap0]; exact hroots
  intro i
  induction i with
  | zero => intro _; exact ⟨Nat.le_refl _, h.c0, by omega⟩
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2, _⟩ := ih (by omega)
    cases hb : (List.range plan.length).any (fun j => p j == i) with
    | true =>
      obtain ⟨j, hj, e⟩ := List.any_eq_true.1 hb
      rw [List.mem_range] at hj
      rw [beq_iff_eq] at e
      subst e
      obtain ⟨s, hs⟩ : ∃ s, plan[j]? = some s := ⟨plan[j], List.getElem?_eq_getElem hj⟩
      obtain ⟨_, _, hctr, _, hc'⟩ := probeRow_spec h2 (h.probe j s hs)
      exact ⟨by omega, hc', fun _ => by rw [Nat.add_sub_cancel]; omega⟩
    | false =>
      have hn : ∀ j, j < plan.length → i ≠ p j := by
        intro j hj e
        have : (List.range plan.length).any (fun j => p j == i) = true :=
          List.any_eq_true.2 ⟨j, List.mem_range.2 hj, beq_iff_eq.2 e.symm⟩
        rw [hb] at this; cases this
      obtain ⟨hle, hc', _, _⟩ := normRow_spec hr0 h1 h2 (h.norm i (by omega) hn)
      exact ⟨by omega, hc', fun _ => by rw [Nat.add_sub_cancel]; exact hle⟩

theorem AcceptsP.ctr_mono (h : AcceptsP M (load t) roots jets plan p fld row)
    (hroots : RootsOK (load t).heap roots jets) :
    ∀ {a b : Nat}, a ≤ b → b ≤ p plan.length → (row a).ctr ≤ (row b).ctr := by
  intro a b hab hb
  induction b with
  | zero => rw [Nat.le_zero.1 hab]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hab with hl | hl
    · have := (h.ctrs hroots (b + 1) hb).2.2 (by omega)
      rw [Nat.add_sub_cancel] at this
      exact Nat.le_trans (ih (by omega) (by omega)) this
    · rw [hl]; exact Nat.le_refl _

/-- A segment's rows are a jetted run that writes no atom. -/
theorem AcceptsP.run (h : AcceptsP M (load t) roots jets plan p fld row)
    (hroots : RootsOK (load t).heap roots jets) {j : Nat} (hj : j < plan.length) :
    ∀ b, p j + 1 ≤ b → b ≤ p (j + 1) →
      JSteps (st M (row (p j + 1))) (st M (row b)) ∧
      ∀ B, AB (M.take (row (p j + 1)).ctr) B → AB (M.take (row b).ctr) B := by
  have hr0 : RootsOK (M.take (row 0).ctr) roots jets := by rw [h.heap0]; exact hroots
  have hpn : p (j + 1) ≤ p plan.length := pmono_le h.pmono (by omega) (Nat.le_refl _)
  intro b hb1 hb2
  induction b with
  | zero => exact absurd hb1 (Nat.not_succ_le_zero _)
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hb1 with hl | hl
    · obtain ⟨hJ, hA⟩ := ih (by omega) (by omega)
      obtain ⟨h1, h2, _⟩ := h.ctrs hroots b (by omega)
      obtain ⟨_, _, hJ1, ws, hws, hwa⟩ := normRow_spec hr0 h1 h2
        (h.norm b (by omega) (not_start h.pmono hj (by omega) (by omega)))
      refine ⟨?_, fun B hB => ?_⟩
      · exact (JSteps.snoc_all hJ hJ1)
      · rw [hws]; exact (hA B hB).append (hwa B)
    · rw [← hl]
      exact ⟨.refl _, fun _ hB => hB⟩

/-- What the table proves of segment `j`. -/
def SegFact (M : List Cell) (plan : List Seg) (p : Nat → Nat) (fld : Nat → List Nat)
    (row : Nat → Row) (j : Nat) : Prop :=
  ∃ s, plan[j]? = some s ∧ Fresh s.base (Fp M plan p fld row j) ∧
    OWSteps (appO (Fp M plan p fld row j) (vars s.base) s.k)
      (appL (.var (s.ctor + s.base)) (Ap M p fld row j)) ∧
    (Ap M p fld row j).length = s.arity ∧
    OPtrsOK (M.take (row (p (j + 1))).ctr) ((row (p (j + 1))).ctr + 1) (fld j) (Ap M p fld row j)

/-- The term a segment probes is read at its probe row, from the loaded
    term or its parent's fields. -/
theorem AcceptsP.readF (h : AcceptsP M (load t) roots jets plan p fld row)
    (hroots : RootsOK (load t).heap roots jets)
    (hpar : ∀ j s, 0 < j → plan[j]? = some s → s.parent < j)
    {j : Nat} (hj : j < plan.length) (hsf : ∀ j', j' < j → SegFact M plan p fld row j') :
    otermAt (M.take (row (p j)).ctr) ((row (p j)).ctr + 1) (fptr plan fld (row 0).hd j) =
      some (Fp M plan p fld row j) ∧
    (j = 0 → Fp M plan p fld row j = t.toO) ∧
    (∀ s, 0 < j → plan[j]? = some s →
      ∃ a, (fld s.parent)[s.field]? = some a ∧ fptr plan fld (row 0).hd j = a ∧
        (Ap M p fld row s.parent)[s.field]? = some (Fp M plan p fld row j)) := by
  have hpn : p j ≤ p plan.length := pmono_le h.pmono (by omega) (Nat.le_refl _)
  have hcj := (h.ctrs hroots (p j) hpn).2.1
  -- the pointer reads
  have hrd : ∃ u, otermAt (M.take (row (p j)).ctr) ((row (p j)).ctr + 1) (fptr plan fld (row 0).hd j) =
      some u ∧ (j = 0 → u = t.toO) ∧ (∀ s, 0 < j → plan[j]? = some s →
      ∃ a, (fld s.parent)[s.field]? = some a ∧ fptr plan fld (row 0).hd j = a ∧
        (Ap M p fld row s.parent)[s.field]? = some u) := by
    cases j with
    | zero =>
      refine ⟨t.toO, ?_, fun _ => rfl, fun _ h0 => absurd h0 (Nat.lt_irrefl 0)⟩
      rw [h.p0, h.heap0, h.ctr0]
      unfold fptr
      rw [if_pos rfl, h.hd0]
      exact load_otermAt t
    | succ j =>
      obtain ⟨s, hs⟩ : ∃ s, plan[j + 1]? = some s := ⟨plan[j + 1], List.getElem?_eq_getElem hj⟩
      have hq := hpar (j + 1) s (by omega) hs
      obtain ⟨s', hs', _, _, hlA, hok⟩ := hsf s.parent hq
      have hfl := h.fields (j + 1) s (by omega) hs
      obtain ⟨a, N, ha, hN, hr⟩ := hok.get hfl
      have hfp : fptr plan fld (row 0).hd (j + 1) = a := by
        unfold fptr
        rw [if_neg (by omega), hs]
        dsimp only
        rw [ha]
        rfl
      have hle : (row (p (s.parent + 1))).ctr ≤ (row (p (j + 1))).ctr :=
        h.ctr_mono hroots (pmono_le h.pmono (by omega) (by omega)) hpn
      refine ⟨N, ?_, fun e => absurd e (by omega), fun s2 _ hs2 => ?_⟩
      · rw [hfp]
        exact otermAt_take hle (by omega) hr
      · rw [hs] at hs2
        cases hs2
        refine ⟨a, ha, hfp, ?_⟩
        rw [← hok.map_getD .S] at hN
        exact hN
  obtain ⟨u, hu, h0, hlink⟩ := hrd
  have hF : Fp M plan p fld row j = u := by unfold Fp; rw [hu]; rfl
  rw [hF]
  exact ⟨hu, h0, hlink⟩

/-- **Segment by segment**: the table proves each segment's facts. -/
theorem AcceptsP.segs (h : AcceptsP M (load t) roots jets plan p fld row)
    (hroots : RootsOK (load t).heap roots jets) {b0 : Nat} (hcons : Consec plan b0)
    (hpar : ∀ j s, 0 < j → plan[j]? = some s → s.parent < j) :
    ∀ j, j ≤ plan.length → (∀ j', j' < j → SegFact M plan p fld row j') ∧
      (∀ s, plan[j]? = some s → AB (M.take (row (p j)).ctr) s.base) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ h0 => absurd h0 (Nat.not_lt_zero _), fun s _ => ?_⟩
    rw [h.p0, h.heap0]
    exact load_AB t _
  | succ j ih =>
    intro hj
    obtain ⟨hsf, hab⟩ := ih (by omega)
    obtain ⟨s, hs⟩ : ∃ s, plan[j]? = some s := ⟨plan[j], List.getElem?_eq_getElem (by omega)⟩
    have hpn : p (j + 1) ≤ p plan.length := pmono_le h.pmono (by omega) (Nat.le_refl _)
    have hpj : p j + 1 ≤ p (j + 1) := h.pmono j (by omega)
    have hcj := (h.ctrs hroots (p j) (by omega)).2.1
    obtain ⟨hrd, _, _⟩ := h.readF hroots hpar (j := j) (by omega) hsf
    have hfresh : Fresh s.base (Fp M plan p fld row j) :=
      fresh_of_AB (hab s hs) hrd
    have hpr := h.probe j s hs
    have hdec := probeRow_decode hcj hpr hrd
    obtain ⟨_, _, _, htake, _⟩ := probeRow_spec hcj hpr
    have hab1 : AB (M.take (row (p j + 1)).ctr) (s.base + s.k) := by
      rw [htake]
      exact ((hab s hs).mono (by omega)).append (pcells_AB _ _ _)
    obtain ⟨hJ, hA⟩ := h.run hroots (j := j) (by omega) (p (j + 1)) hpj (Nat.le_refl _)
    obtain ⟨u, hu, hw⟩ := ojsteps_owsteps hdec hJ
    have hce := (h.ctrs hroots (p (j + 1)) hpn).2.1
    obtain ⟨Ns, hun, hlN, hok⟩ := endRow_decode hce hu (h.ends j s hs)
    have hAp : Ap M p fld row j = Ns := hok.map_getD .S
    refine ⟨fun j' hj' => ?_, fun s' hs' => ?_⟩
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with hl | hl
      · exact hsf j' hl
      · subst hl
        refine ⟨s, hs, hfresh, ?_, by rw [hAp]; exact hlN, by rw [hAp]; exact hok⟩
        rw [hAp, ← hun]
        exact hw
    · rw [Consec.next hcons hs hs']
      exact hA _ hab1

/-- **The segments of an accepted table probe**, as the assembly asks. -/
theorem AcceptsP.segsOK (h : AcceptsP M (load t) roots jets plan p fld row)
    (hroots : RootsOK (load t).heap roots jets) {b0 : Nat} (hcons : Consec plan b0)
    (hpar : ∀ j s, 0 < j → plan[j]? = some s → s.parent < j) :
    SegsOK plan (Fp M plan p fld row) (Ap M p fld row) ∧ Fp M plan p fld row 0 = t.toO := by
  obtain ⟨hsf, _⟩ := h.segs hroots hcons hpar plan.length (Nat.le_refl _)
  have hlt : ∀ {j s}, plan[j]? = some s → j < plan.length := by
    intro j s hs
    rcases Nat.lt_or_ge j plan.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at hs; cases hs
  refine ⟨⟨fun j s hs => ?_, fun j s hs => ?_, fun j s hj hs hf => ?_⟩, ?_⟩
  · obtain ⟨s', hs', hfr, _⟩ := hsf j (hlt hs)
    rw [hs] at hs'; cases hs'
    exact hfr
  · obtain ⟨s', hs', _, hw, hl, _⟩ := hsf j (hlt hs)
    rw [hs] at hs'; cases hs'
    exact ⟨hw, hl⟩
  · have hsf' : ∀ j', j' < j → SegFact M plan p fld row j' := fun j' hj' => hsf j' (by
      have := hlt hs; omega)
    obtain ⟨_, _, hlink⟩ := h.readF hroots hpar (hlt hs) hsf'
    obtain ⟨_, _, _, e⟩ := hlink s hj hs
    exact e
  · exact (h.readF hroots hpar (j := 0) h.nonempty (fun _ h0 => absurd h0 (Nat.not_lt_zero _))).2.1 rfl

/-- **Soundness of the AIR with probe segments.**  A table it accepts for
    the plan of `v`, from a loaded term whose roots are licensed, proves
    that the term reads as `v`. -/
theorem air_probe_sound [Kit] {v : V} {b0 : Nat}
    (h : AcceptsP M (load t) roots jets (planOf v b0) p fld row)
    (hroots : RootsOK (load t).heap roots jets) : DecV t.toO v := by
  obtain ⟨hok, h0⟩ := h.segsOK hroots (planOf_consec v b0) (fun _ _ hj hs => planOf_parent hj hs)
  have := decV_go hok v 0 0 b0 0 (fun i _ => by rw [Nat.zero_add]; rfl)
  rw [h0] at this
  exact this

/-- **The output, bound.**  A table the AIR with probe segments accepts for
    the plan of the outcome `o`'s probe tree proves that the term decodes
    to `o`. -/
theorem air_probe_decodes [Kit] {o : Outcome} {v : V} {b0 : Nat} (hv : toV o = some v)
    (h : AcceptsP M (load t) roots jets (planOf v b0) p fld row)
    (hroots : RootsOK (load t).heap roots jets) : Decodes t o :=
  decodes_of_decV hv (air_probe_sound h hroots)

end Sound

-- ---------------------------------------------------------------------------
-- The checker, over arrays
-- ---------------------------------------------------------------------------

/-- A row within a segment, decided over a reader. -/
def normB (g : Nat → Option Cell) (roots : List (Nat × Nat)) (jets : List Jet) (r r' : Row) : Bool :=
  decide (stepRowG g r = some r') ||
    roots.any (fun (a, j) => a == r.hd &&
      match jets[j]? with
      | some J => decide (instRowG g J r = some r')
      | none => false) ||
    (haltRowG g r && decide (r' = r))

theorem normB_sound {M : List Cell} {roots : List (Nat × Nat)} {jets : List Jet} {r r' : Row}
    (h : normB (fun a => M[a]?) roots jets r r' = true) : NormRow M roots jets r r' := by
  unfold normB at h
  rw [Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_iff] at h
  rcases h with (hs | ha) | hh
  · left; rw [stepRow_G]; exact hs
  · right; left
    obtain ⟨⟨a, j⟩, hm, hj⟩ := List.any_eq_true.1 ha
    rw [Bool.and_eq_true, beq_iff_eq] at hj
    obtain ⟨ha', hJ⟩ := hj
    cases hjj : jets[j]? with
    | none => rw [hjj] at hJ; cases hJ
    | some J =>
      rw [hjj, decide_eq_true_iff] at hJ
      subst ha'
      exact ⟨j, J, hm, hjj, hJ⟩
  · right; right
    rw [Bool.and_eq_true, decide_eq_true_iff] at hh
    exact ⟨by rw [haltRow_G]; exact hh.1, hh.2⟩

/-- Segment `j`'s probe row, end row and field check, over a reader. -/
def segB (g : Nat → Option Cell) (plan : List Seg) (P : Nat → Nat) (fl : Nat → List Nat)
    (row : Nat → Row) (j : Nat) : Bool :=
  match plan[j]? with
  | some s =>
    decide (probeRowG g s (fptr plan fl (row 0).hd j) (row (P j)) = some (row (P j + 1))) &&
      endRowG g s (fl j) (row (P (j + 1))) &&
      (j == 0 || decide (s.field < (fl s.parent).length))
  | none => false

/-- **The AIR with probe segments, checked** on a table over arrays: the
    memory, the segments' start rows (the last entry is the last row), the
    segments' fields, and the rows. -/
def checkPA (A : Array Cell) (t : Term) (roots : List (Nat × Nat)) (jets : List Jet)
    (plan : List Seg) (starts : Array Nat) (flds : Array (List Nat)) (R : Array Row) : Bool :=
  let g := fun a => A[a]?
  let P := fun j => starts.getD j 0
  let fl := fun j => flds.getD j []
  let row := fun i => R.getD i ⟨0, 0, 0⟩
  rootsOKB (load t).heap roots jets && decide (0 < plan.length) &&
    decide (A.toList.take (row 0).ctr = (load t).heap) && decide ((row 0).hd = (load t).hd) &&
    decide ((row 0).ctr = (load t).heap.length) && decide (P 0 = 0) &&
    decide (R.size = P plan.length + 1) &&
    (List.range plan.length).all (fun j => decide (P j < P (j + 1))) &&
    (List.range plan.length).all (segB g plan P fl row) &&
    (List.range (P plan.length)).all (fun i =>
      (List.range plan.length).any (fun j => P j == i) || normB g roots jets (row i) (row (i + 1)))

/-- **`checkPA` is sound**: a table it accepts, the AIR with probe
    segments accepts, with licensed roots. -/
theorem checkPA_sound {A : Array Cell} {t : Term} {roots : List (Nat × Nat)} {jets : List Jet}
    {plan : List Seg} {starts : Array Nat} {flds : Array (List Nat)} {R : Array Row}
    (h : checkPA A t roots jets plan starts flds R = true) :
    RootsOK (load t).heap roots jets ∧
      AcceptsP A.toList (load t) roots jets plan (fun j => starts.getD j 0) (fun j => flds.getD j [])
        (fun i => R.getD i ⟨0, 0, 0⟩) := by
  unfold checkPA at h
  dsimp only at h
  rw [getElem?_fun] at h
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, hn⟩, h0⟩, h1⟩, h2⟩, hp0⟩, _⟩, hmono⟩, hseg⟩, hnorm⟩ := h
  have hseg' : ∀ j s, plan[j]? = some s →
      probeRow A.toList s (fptr plan (fun j => flds.getD j []) (R.getD 0 ⟨0, 0, 0⟩).hd j)
          (R.getD (starts.getD j 0) ⟨0, 0, 0⟩) = some (R.getD (starts.getD j 0 + 1) ⟨0, 0, 0⟩) ∧
        endRow A.toList s (flds.getD j []) (R.getD (starts.getD (j + 1) 0) ⟨0, 0, 0⟩) = true ∧
        (0 < j → s.field < (flds.getD s.parent []).length) := by
    intro j s hs
    have hj : j < plan.length := by
      rcases Nat.lt_or_ge j plan.length with hl | hl
      · exact hl
      · rw [List.getElem?_eq_none hl] at hs; cases hs
    have := List.all_eq_true.1 hseg j (List.mem_range.2 hj)
    unfold segB at this
    rw [hs] at this
    simp only [Bool.and_eq_true, decide_eq_true_iff, Bool.or_eq_true, beq_iff_eq] at this
    obtain ⟨⟨hpr, hend⟩, hf⟩ := this
    refine ⟨hpr, hend, fun hpos => ?_⟩
    rcases hf with e | hf
    · exact absurd e (Nat.pos_iff_ne_zero.1 hpos)
    · exact hf
  refine ⟨rootsOKB_sound hr, hn, h0, h1, h2, hp0,
    fun j hj => decide_eq_true_iff.1 (List.all_eq_true.1 hmono j (List.mem_range.2 hj)), ?_, ?_, ?_, ?_⟩
  · exact fun j s hs => (hseg' j s hs).1
  · exact fun j s hj hs => (hseg' j s hs).2.2 hj
  · intro i hi hne
    have := List.all_eq_true.1 hnorm i (List.mem_range.2 hi)
    rw [Bool.or_eq_true] at this
    rcases this with ha | hb
    · obtain ⟨j, hj, e⟩ := List.any_eq_true.1 ha
      rw [beq_iff_eq] at e
      exact absurd e.symm (hne j (List.mem_range.1 hj))
    · exact normB_sound hb
  · exact fun j s hs => (hseg' j s hs).2.1

/-- **A checked probe table binds the output**: a table `checkPA` accepts
    for the plan of the outcome `o`'s probe tree proves that the term
    decodes to `o`. -/
theorem checkPA_decodes [Kit] {A : Array Cell} {t : Term} {roots : List (Nat × Nat)}
    {jets : List Jet} {o : Outcome} {v : V} {b0 : Nat} {starts : Array Nat}
    {flds : Array (List Nat)} {R : Array Row} (hv : toV o = some v)
    (h : checkPA A t roots jets (planOf v b0) starts flds R = true) : Decodes t o := by
  obtain ⟨hr, ha⟩ := checkPA_sound h
  exact air_probe_decodes hv ha hr

end Air
