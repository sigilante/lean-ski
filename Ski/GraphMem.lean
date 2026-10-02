import Ski.Graph
import Ski.RWMem

open Term Graph

/-!
# Graph reduction under a read-write memory argument

`Ski/Graph.lean` proves graph reduction correct against L1, and
`Ski/RWMem.lean` proves the timestamped memory check sound for a trace of
single accesses.  This file joins them.

**One access a step** (`ustep`).  The machine `gstep` reads up to four
cells and writes up to three in one transition.  `ustep` refines it into
steps of exactly one memory access each, a read and a write of one
address, over registers: the root, the head, the spine, the allocation
counter, a phase, and three saved addresses.  A read that changes nothing
writes back what it read.  One `gstep` is one to six `ustep`s
(`sim_some`), and from a state in the invariant a halted `gstep` halts
`ustep` in one step (`sim_none`).  Once halted, `ustep` accesses address `0` and writes it
back, so a halted trace pads to any length.

**The statement** (`Accepts t M n rows nF fin`).  The prover gives `n`
rows, each the registers and the cell and time it read; the verifier
computes each row's address and written cell from its registers and read
cell, and checks: the first registers are `t` loaded, each row's
registers follow from the last row's, the registers after the last row
are halted, and the accesses pass the memory check of `Ski/RWMem.lean`
over `M` cells starting from `t`'s loaded heap (`initMem t`).

- `accepts_sound`: an accepted trace is the honest one, so the graph
  machine halts from `t`, and `t` evaluates under L1 (`Eval t u`) with
  the machine's value having `u`'s head and arity.
- `accepts_complete`: if the graph machine halts from `t`, the honest
  trace is accepted at every budget `n` from its halting step on, given
  `M` above every address it touches.
- `accepts_unique`: at each budget the accepted rows are unique.

So the budget-exact statement "`t` halts within `n` accesses", with `n`
public, is accepted exactly at the budgets where the refined machine has
halted (`accepts_halted`, `accepts_of_halted`, given `M` above the honest
addresses), every budget from the first halting step on, and its trace is
unique at each.
The spine is a register list here; a circuit would keep it in memory too,
and none is built.
-/

namespace GraphMem

inductive Phase where
  | fetch | i1 | k1 | k2 | s1 | s2 | s3 | s4 | s5 | halt
  deriving DecidableEq, Repr

structure Regs where
  root : Nat
  hd : Nat
  spine : List Nat
  len : Nat
  ph : Phase
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr

/-- The address a step accesses. -/
def addrOf (r : Regs) : Nat :=
  match r.ph, r.spine with
  | .fetch, _ => r.hd
  | .i1, s :: _ => s
  | .k1, s :: _ => s
  | .k2, _ :: s :: _ => s
  | .s1, s :: _ => s
  | .s2, _ :: s :: _ => s
  | .s3, _ :: _ :: s :: _ => s
  | .s4, _ => r.len
  | .s5, _ => r.len + 1
  | _, _ => 0

/-- The registers after a step that read `c`, and the cell it writes. -/
def next (r : Regs) (c : GCell) : Regs × GCell :=
  match r.ph with
  | .fetch =>
    match c, r.spine with
    | .app f _, _ => ({ r with hd := f, spine := r.hd :: r.spine }, c)
    | .ind p, _ => ({ r with hd := p }, c)
    | .I, _ :: _ => ({ r with ph := .i1 }, c)
    | .K, _ :: _ :: _ => ({ r with ph := .k1 }, c)
    | .S, _ :: _ :: _ :: _ => ({ r with ph := .s1 }, c)
    | _, _ => ({ r with ph := .halt }, c)
  | .i1 =>
    match c, r.spine with
    | .app _ x, s :: rest => (⟨r.root, s, rest, r.len, .fetch, 0, 0, 0⟩, .ind x)
    | _, _ => ({ r with ph := .halt }, c)
  | .k1 =>
    match c with
    | .app _ x => ({ r with ph := .k2, x := x }, c)
    | _ => ({ r with ph := .halt }, c)
  | .k2 =>
    match c, r.spine with
    | .app _ _, _ :: s2 :: rest => (⟨r.root, s2, rest, r.len, .fetch, 0, 0, 0⟩, .ind r.x)
    | _, _ => ({ r with ph := .halt }, c)
  | .s1 =>
    match c with
    | .app _ x => ({ r with ph := .s2, x := x }, c)
    | _ => ({ r with ph := .halt }, c)
  | .s2 =>
    match c with
    | .app _ y => ({ r with ph := .s3, y := y }, c)
    | _ => ({ r with ph := .halt }, c)
  | .s3 =>
    match c with
    | .app _ z => ({ r with ph := .s4, z := z }, .app r.len (r.len + 1))
    | _ => ({ r with ph := .halt }, c)
  | .s4 => ({ r with ph := .s5 }, .app r.x r.z)
  | .s5 =>
    match r.spine with
    | _ :: _ :: s3 :: rest => (⟨r.root, s3, rest, r.len + 2, .fetch, 0, 0, 0⟩, .app r.y r.z)
    | _ => ({ r with ph := .halt }, c)
  | .halt => (r, c)

/-- Write one cell of a memory. -/
def upd (mem : Nat → GCell) (a : Nat) (w : GCell) : Nat → GCell := fun b => if b = a then w else mem b

/-- One step over a memory. -/
def ustep (s : Regs × (Nat → GCell)) : Regs × (Nat → GCell) :=
  ((next s.1 (s.2 (addrOf s.1))).1, upd s.2 (addrOf s.1) (next s.1 (s.2 (addrOf s.1))).2)

def ustepN : Nat → Regs × (Nat → GCell) → Regs × (Nat → GCell)
  | 0, s => s
  | n + 1, s => ustepN n (ustep s)

theorem ustepN_add : ∀ (a b : Nat) (s : Regs × (Nat → GCell)), ustepN (a + b) s = ustepN b (ustepN a s)
  | 0, b, s => by rw [Nat.zero_add]; rfl
  | a + 1, b, s => by
    rw [Nat.add_right_comm]
    exact ustepN_add a b (ustep s)

theorem upd_self (mem : Nat → GCell) (a : Nat) : upd mem a (mem a) = mem :=
  funext fun b => by
    unfold upd
    by_cases h : b = a
    · rw [if_pos h, h]
    · rw [if_neg h]

theorem upd_eq {mem : Nat → GCell} {a : Nat} {c : GCell} (h : mem a = c) : upd mem a c = mem := by
  rw [← h]; exact upd_self mem a

/-- The registers of a machine state, between transitions. -/
def enc (m : GM) : Regs := ⟨m.root, m.hd, m.spine, m.heap.length, .fetch, 0, 0, 0⟩

/-- A memory holds a heap. -/
def Rep (mem : Nat → GCell) (h : Heap) : Prop := ∀ a, a < h.length → h[a]? = some (mem a)

theorem Rep.get {mem : Nat → GCell} {h : Heap} (hr : Rep mem h) {a : Nat} {c : GCell}
    (e : h[a]? = some c) : mem a = c := by
  have := hr a (lt_of_get e)
  rw [e] at this
  exact (Option.some.inj this).symm

theorem Rep.set {mem : Nat → GCell} {h : Heap} (hr : Rep mem h) (a : Nat) (c : GCell) :
    Rep (upd mem a c) (h.set a c) := by
  intro b hb
  rw [List.length_set] at hb
  unfold upd
  by_cases e : b = a
  · rw [if_pos e, e, List.getElem?_set_self (e ▸ hb)]
  · rw [if_neg e, List.getElem?_set_ne (Ne.symm e)]
    exact hr b hb

-- ---------------------------------------------------------------------------
-- One transition is a few steps
-- ---------------------------------------------------------------------------

theorem ustep_eq (r : Regs) (mem : Nat → GCell) :
    ustep (r, mem) = ((next r (mem (addrOf r))).1, upd mem (addrOf r) (next r (mem (addrOf r))).2) := rfl

/-- **A transition is one to six steps**, none of them halted before the end. -/
theorem sim_some {m m' : GM} {b : Bool} {mem : Nat → GCell} (hs : gstep m = some (m', b))
    (hr : Rep mem m.heap) :
    ∃ d mem', 0 < d ∧ ustepN d (enc m, mem) = (enc m', mem') ∧ Rep mem' m'.heap ∧
      ∀ j, j < d → (ustepN j (enc m, mem)).1.ph ≠ .halt := by
  have g := gstep_sound hs
  cases g with
  | @unwind h r c f x sp e =>
    have mc := hr.get e
    refine ⟨1, mem, Nat.zero_lt_one, ?_, hr, ?_⟩
    · show ustep (enc ⟨h, r, c, sp⟩, mem) = _
      rw [ustep_eq]
      simp only [enc, addrOf, next, mc, upd_eq mc]
    · intro j hj
      rw [Nat.lt_one_iff.1 hj]
      intro e; cases e
  | @follow h r c p sp e =>
    have mc := hr.get e
    refine ⟨1, mem, Nat.zero_lt_one, ?_, hr, ?_⟩
    · show ustep (enc ⟨h, r, c, sp⟩, mem) = _
      rw [ustep_eq]
      simp only [enc, addrOf, next, mc, upd_eq mc]
    · intro j hj
      rw [Nat.lt_one_iff.1 hj]
      intro e; cases e
  | @I h r c s1 f1 x rest ec e1 =>
    have mc := hr.get ec
    have m1 := hr.get e1
    have st1 : ustep (enc ⟨h, r, c, s1 :: rest⟩, mem) =
        (⟨r, c, s1 :: rest, h.length, .i1, 0, 0, 0⟩, mem) := by
      rw [ustep_eq]
      simp only [enc, addrOf, next, mc, upd_eq mc]
    have st2 : ustep ((⟨r, c, s1 :: rest, h.length, .i1, 0, 0, 0⟩ : Regs), mem) =
        (⟨r, s1, rest, h.length, .fetch, 0, 0, 0⟩, upd mem s1 (.ind x)) := by
      rw [ustep_eq]
      simp only [addrOf, next, m1]
    refine ⟨2, upd mem s1 (.ind x), by decide, ?_, ?_, ?_⟩
    · show ustepN 1 (ustep _) = _
      rw [st1]
      show ustep _ = _
      rw [st2]
      simp only [enc, List.length_set]
    · exact hr.set s1 (.ind x)
    · intro j hj
      match j, hj with
      | 0, _ => intro e; cases e
      | 1, _ =>
        show (ustep _).1.ph ≠ _
        rw [st1]; intro e; cases e
  | @K h r c s1 s2 f1 x f2 y rest ec e1 e2 =>
    have mc := hr.get ec
    have m1 := hr.get e1
    have m2 := hr.get e2
    have st1 : ustep (enc ⟨h, r, c, s1 :: s2 :: rest⟩, mem) =
        (⟨r, c, s1 :: s2 :: rest, h.length, .k1, 0, 0, 0⟩, mem) := by
      rw [ustep_eq]
      simp only [enc, addrOf, next, mc, upd_eq mc]
    have st2 : ustep ((⟨r, c, s1 :: s2 :: rest, h.length, .k1, 0, 0, 0⟩ : Regs), mem) =
        (⟨r, c, s1 :: s2 :: rest, h.length, .k2, x, 0, 0⟩, mem) := by
      rw [ustep_eq]
      simp only [addrOf, next, m1, upd_eq m1]
    have st3 : ustep ((⟨r, c, s1 :: s2 :: rest, h.length, .k2, x, 0, 0⟩ : Regs), mem) =
        (⟨r, s2, rest, h.length, .fetch, 0, 0, 0⟩, upd mem s2 (.ind x)) := by
      rw [ustep_eq]
      simp only [addrOf, next, m2]
    refine ⟨3, upd mem s2 (.ind x), by decide, ?_, ?_, ?_⟩
    · show ustepN 2 (ustep _) = _
      rw [st1]
      show ustepN 1 (ustep _) = _
      rw [st2]
      show ustep _ = _
      rw [st3]
      simp only [enc, List.length_set]
    · exact hr.set s2 (.ind x)
    · intro j hj
      match j, hj with
      | 0, _ => intro e; cases e
      | 1, _ =>
        show (ustep _).1.ph ≠ _
        rw [st1]; intro e; cases e
      | 2, _ =>
        show (ustepN 1 (ustep _)).1.ph ≠ _
        rw [st1]
        show (ustep _).1.ph ≠ _
        rw [st2]; intro e; cases e
  | @S h r c s1 s2 s3 f1 x f2 y f3 z rest ec e1 e2 e3 =>
    have mc := hr.get ec
    have m1 := hr.get e1
    have m2 := hr.get e2
    have m3 := hr.get e3
    have hl3 := lt_of_get e3
    let L := h.length
    let mem3 := upd mem s3 (.app L (L + 1))
    let mem4 := upd mem3 L (.app x z)
    let mem5 := upd mem4 (L + 1) (.app y z)
    have st1 : ustep (enc ⟨h, r, c, s1 :: s2 :: s3 :: rest⟩, mem) =
        (⟨r, c, s1 :: s2 :: s3 :: rest, L, .s1, 0, 0, 0⟩, mem) := by
      rw [ustep_eq]
      simp only [enc, addrOf, next, mc, upd_eq mc]
      rfl
    have st2 : ustep ((⟨r, c, s1 :: s2 :: s3 :: rest, L, .s1, 0, 0, 0⟩ : Regs), mem) =
        (⟨r, c, s1 :: s2 :: s3 :: rest, L, .s2, x, 0, 0⟩, mem) := by
      rw [ustep_eq]
      simp only [addrOf, next, m1, upd_eq m1]
    have st3 : ustep ((⟨r, c, s1 :: s2 :: s3 :: rest, L, .s2, x, 0, 0⟩ : Regs), mem) =
        (⟨r, c, s1 :: s2 :: s3 :: rest, L, .s3, x, y, 0⟩, mem) := by
      rw [ustep_eq]
      simp only [addrOf, next, m2, upd_eq m2]
    have st4 : ustep ((⟨r, c, s1 :: s2 :: s3 :: rest, L, .s3, x, y, 0⟩ : Regs), mem) =
        (⟨r, c, s1 :: s2 :: s3 :: rest, L, .s4, x, y, z⟩, mem3) := by
      rw [ustep_eq]
      simp only [addrOf, next, m3]
      rfl
    have st5 : ustep ((⟨r, c, s1 :: s2 :: s3 :: rest, L, .s4, x, y, z⟩ : Regs), mem3) =
        (⟨r, c, s1 :: s2 :: s3 :: rest, L, .s5, x, y, z⟩, mem4) := by
      rw [ustep_eq]
      simp only [addrOf, next]
      rfl
    have st6 : ustep ((⟨r, c, s1 :: s2 :: s3 :: rest, L, .s5, x, y, z⟩ : Regs), mem4) =
        (⟨r, s3, rest, L + 2, .fetch, 0, 0, 0⟩, mem5) := by
      rw [ustep_eq]
      simp only [addrOf, next]
      rfl
    refine ⟨6, mem5, by decide, ?_, ?_, ?_⟩
    · show ustepN 5 (ustep _) = _
      rw [st1]
      show ustepN 4 (ustep _) = _
      rw [st2]
      show ustepN 3 (ustep _) = _
      rw [st3]
      show ustepN 2 (ustep _) = _
      rw [st4]
      show ustepN 1 (ustep _) = _
      rw [st5]
      show ustep _ = _
      rw [st6]
      simp only [enc, List.length_set, List.length_append]
      rfl
    · intro b hb
      simp only [List.length_set, List.length_append] at hb
      show _ = some (mem5 b)
      simp only [mem5, mem4, mem3, upd]
      by_cases b1 : b = L + 1
      · rw [if_pos b1, b1, List.getElem?_set_ne (Nat.ne_of_lt (Nat.lt_succ_of_lt hl3)),
          List.getElem?_append_right (Nat.le_succ _), Nat.succ_sub (Nat.le_refl _), Nat.sub_self]
        rfl
      · rw [if_neg b1]
        by_cases b0 : b = L
        · rw [if_pos b0, b0, List.getElem?_set_ne (Nat.ne_of_lt hl3),
            List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        · rw [if_neg b0]
          have bl : b < L := by
            rcases Nat.lt_or_ge b L with l | l
            · exact l
            · exfalso
              rcases Nat.lt_or_eq_of_le l with l' | l'
              · exact b1 (Nat.le_antisymm (Nat.le_of_lt_succ (by simpa using hb)) l')
              · exact b0 l'.symm
          by_cases b3 : b = s3
          · rw [if_pos b3, b3, List.getElem?_set_self]
            rw [List.length_append]
            exact Nat.lt_of_lt_of_le hl3 (Nat.le_add_right _ _)
          · rw [if_neg b3, List.getElem?_set_ne (Ne.symm b3), List.getElem?_append_left bl]
            exact hr b bl
    · intro j hj
      match j, hj with
      | 0, _ => intro e; cases e
      | 1, _ =>
        show (ustep _).1.ph ≠ _
        rw [st1]; intro e; cases e
      | 2, _ =>
        show (ustepN 1 (ustep _)).1.ph ≠ _
        rw [st1]
        show (ustep _).1.ph ≠ _
        rw [st2]; intro e; cases e
      | 3, _ =>
        show (ustepN 2 (ustep _)).1.ph ≠ _
        rw [st1]
        show (ustepN 1 (ustep _)).1.ph ≠ _
        rw [st2]
        show (ustep _).1.ph ≠ _
        rw [st3]; intro e; cases e
      | 4, _ =>
        show (ustepN 3 (ustep _)).1.ph ≠ _
        rw [st1]
        show (ustepN 2 (ustep _)).1.ph ≠ _
        rw [st2]
        show (ustepN 1 (ustep _)).1.ph ≠ _
        rw [st3]
        show (ustep _).1.ph ≠ _
        rw [st4]; intro e; cases e
      | 5, _ =>
        show (ustepN 4 (ustep _)).1.ph ≠ _
        rw [st1]
        show (ustepN 3 (ustep _)).1.ph ≠ _
        rw [st2]
        show (ustepN 2 (ustep _)).1.ph ≠ _
        rw [st3]
        show (ustepN 1 (ustep _)).1.ph ≠ _
        rw [st4]
        show (ustep _).1.ph ≠ _
        rw [st5]; intro e; cases e

theorem ustepN_succ (j : Nat) (s : Regs × (Nat → GCell)) : ustepN (j + 1) s = ustep (ustepN j s) :=
  ustepN_add j 1 s

/-- A halted machine stays halted, its memory unchanged. -/
theorem ustep_halt {r : Regs} (mem : Nat → GCell) (h : r.ph = .halt) : ustep (r, mem) = (r, mem) := by
  obtain ⟨root, hd, sp, len, ph, x, y, z⟩ := r
  subst h
  rw [ustep_eq]
  simp only [addrOf, next, upd_self]

theorem ustepN_halt {r : Regs} (mem : Nat → GCell) (h : r.ph = .halt) : ∀ n, ustepN n (r, mem) = (r, mem)
  | 0 => rfl
  | n + 1 => by
    show ustepN n (ustep (r, mem)) = _
    rw [ustep_halt mem h]
    exact ustepN_halt mem h n

theorem halted_le {s : Regs × (Nat → GCell)} {N n : Nat} (hN : (ustepN N s).1.ph = .halt) (hn : N ≤ n) :
    (ustepN n s).1.ph = .halt := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [ustepN_add]
  have e : ustepN N s = ((ustepN N s).1, (ustepN N s).2) := rfl
  rw [e, ustepN_halt _ hN]
  exact hN

/-- **A halted transition is a halted step**, for a machine in its invariant. -/
theorem sim_none {m : GM} {D : Term} {mem : Nat → GCell} (hs : gstep m = none) (hi : Inv m D)
    (hr : Rep mem m.heap) : (ustep (enc m, mem)).1.ph = .halt := by
  obtain ⟨h, r, c, sp⟩ := m
  obtain ⟨⟨n, dr⟩, hsp⟩ := hi
  obtain ⟨H, nH, as, dH, _, ha⟩ := dec_spine dr sp c hsp
  obtain ⟨cell, hc⟩ := dH.cell
  have mc := hr.get hc
  rw [ustep_eq]
  cases cell with
  | app f x => simp only [gstep, hc] at hs; cases hs
  | ind p => simp only [gstep, hc] at hs; cases hs
  | I =>
    cases ha with
    | nil => simp only [enc, addrOf, next, mc]
    | cons e1 _ _ => simp only [gstep, hc, e1] at hs; cases hs
  | K =>
    cases ha with
    | nil => simp only [enc, addrOf, next, mc]
    | cons e1 _ ha =>
      cases ha with
      | nil => simp only [enc, addrOf, next, mc]
      | cons e2 _ _ => simp only [gstep, hc, e1, e2] at hs; cases hs
  | S =>
    cases ha with
    | nil => simp only [enc, addrOf, next, mc]
    | cons e1 _ ha =>
      cases ha with
      | nil => simp only [enc, addrOf, next, mc]
      | cons e2 _ ha =>
        cases ha with
        | nil => simp only [enc, addrOf, next, mc]
        | cons e3 _ _ => simp only [gstep, hc, e1, e2, e3] at hs; cases hs

/-- **Steps halt only where transitions do.** -/
theorem halts_of_steps : ∀ (B n : Nat), n ≤ B → ∀ {m : GM} {mem : Nat → GCell}, Rep mem m.heap →
    (ustepN n (enc m, mem)).1.ph = .halt → ∃ k m' c, grun k m = some (m', c) := by
  intro B
  induction B with
  | zero =>
    intro n hn m mem _ hh
    rw [Nat.le_zero.1 hn] at hh
    cases hh
  | succ B ih =>
    intro n hn m mem hr hh
    cases hs : gstep m with
    | none => exact ⟨1, m, 0, grun_halt 0 hs⟩
    | some p =>
      obtain ⟨m', b⟩ := p
      obtain ⟨d, mem', dpos, hd, hr', nh⟩ := sim_some hs hr
      rcases Nat.lt_or_ge n d with l | l
      · exact absurd hh (nh n l)
      · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le l
        rw [ustepN_add, hd] at hh
        have he : e ≤ B := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
          (Nat.lt_add_of_pos_left dpos) hn)
        obtain ⟨k, m'', c, hk⟩ := ih e he hr' hh
        exact ⟨k + 1, m'', _, grun_step hs hk⟩

/-- **Transitions halt only where steps do.** -/
theorem steps_of_halts : ∀ (k : Nat) {m m' : GM} {c : Nat} {D : Term} {mem : Nat → GCell},
    grun k m = some (m', c) → Inv m D → Rep mem m.heap → ∃ N, (ustepN N (enc m, mem)).1.ph = .halt
  | 0, _, _, _, _, _, hr, _, _ => by cases hr
  | k + 1, m, m', c, D, mem, hk, hi, hr => by
    cases hs : gstep m with
    | none => exact ⟨1, sim_none hs hi hr⟩
    | some p =>
      obtain ⟨m1, b⟩ := p
      cases hk1 : grun k m1 with
      | none => simp only [grun, hs, hk1] at hk; cases hk
      | some q =>
        obtain ⟨d, mem', _, hd, hr', _⟩ := sim_some hs hr
        obtain ⟨D1, hi1, _⟩ := gstep_inv (gstep_sound hs) hi
        obtain ⟨N, hN⟩ := steps_of_halts k hk1 hi1 hr'
        refine ⟨d + N, ?_⟩
        rw [ustepN_add, hd]
        exact hN

-- ---------------------------------------------------------------------------
-- The statement and its memory check
-- ---------------------------------------------------------------------------

/-- A row of the trace: the registers, and the cell and time the step read. -/
structure Row where
  regs : Regs
  rv : GCell
  rt : Nat

/-- A row's access: its address and written cell are computed, not given. -/
def opOf (w : Row) : RWMem.Op GCell := ⟨addrOf w.regs, w.rv, w.rt, (next w.regs w.rv).2⟩

/-- Memory before the run: `t` loaded, `S` beyond. -/
def initMem (t : Term) : Nat → GCell := fun a => ((loadT t []).1[a]?).getD .S

theorem rep_init (t : Term) : Rep (initMem t) (gload t).heap := by
  intro a ha
  have ha' : a < (loadT t []).1.length := ha
  show (loadT t []).1[a]? = some (((loadT t []).1[a]?).getD .S)
  rw [List.getElem?_eq_getElem ha']
  rfl

/-- **The statement "`t` halts within `n` steps"**, checked by a read-write
    memory argument over `M` cells: the first registers are `t` loaded,
    each row follows from the last, the registers after the last row are
    halted, and the accesses balance with read times in order. -/
def Accepts (t : Term) (M n : Nat) (rows : Nat → Row) (nF : Nat) (fin : Nat → RWMem.Tup GCell) : Prop :=
  0 < n ∧ (rows 0).regs = enc (gload t) ∧
  (∀ j, j + 1 < n → (rows (j + 1)).regs = (next (rows j).regs (rows j).rv).1) ∧
  (next (rows (n - 1)).regs (rows (n - 1)).rv).1.ph = .halt ∧
  RWMem.Balanced (fun j => opOf (rows j)) n M (initMem t) nF fin ∧
  RWMem.TimesOK (fun j => opOf (rows j)) n

/-- Memory after replaying the first `j` writes over `f`. -/
def memAt (ops : Nat → RWMem.Op GCell) (f : Nat → GCell) : Nat → Nat → GCell
  | 0 => f
  | j + 1 => upd (memAt ops f j) (ops j).addr (ops j).wv

/-- The last write is the replayed memory. -/
theorem expected_memAt (ops : Nat → RWMem.Op GCell) (f : Nat → GCell) (a : Nat) :
    ∀ j, (RWMem.expected ops f a j).1 = memAt ops f j a
  | 0 => rfl
  | j + 1 => by
    have hl : RWMem.lastW ops a (j + 1) = if (ops j).addr = a then some j else RWMem.lastW ops a j := rfl
    unfold RWMem.expected
    rw [hl]
    show _ = (if a = (ops j).addr then (ops j).wv else memAt ops f j a)
    by_cases e : (ops j).addr = a
    · rw [if_pos e, if_pos e.symm]
    · rw [if_neg e, if_neg (Ne.symm e)]
      exact expected_memAt ops f a j

/-- An accepted trace is the honest run, step for step. -/
theorem accepts_honest {t : Term} {M n : Nat} {rows : Nat → Row} {nF : Nat} {fin : Nat → RWMem.Tup GCell}
    (hA : Accepts t M n rows nF fin) :
    ∀ j, j < n → ustepN j (enc (gload t), initMem t) =
      ((rows j).regs, memAt (fun i => opOf (rows i)) (initMem t) j) ∧
      (rows j).rv = memAt (fun i => opOf (rows i)) (initMem t) j (addrOf (rows j).regs) := by
  obtain ⟨_, h0, hstep, _, hb, ht⟩ := hA
  have reads := RWMem.rw_sound hb ht
  have rv : ∀ j, j < n →
      (rows j).rv = memAt (fun i => opOf (rows i)) (initMem t) j (addrOf (rows j).regs) := fun j hj => by
    have e := congrArg Prod.fst (reads j hj)
    rw [expected_memAt] at e
    exact e
  intro j
  induction j with
  | zero => intro hn; exact ⟨by rw [h0]; rfl, rv 0 hn⟩
  | succ j ih =>
    intro hn
    obtain ⟨e, _⟩ := ih (Nat.lt_of_succ_lt hn)
    refine ⟨?_, rv _ hn⟩
    rw [ustepN_succ, e, ustep_eq, ← rv j (Nat.lt_of_succ_lt hn), hstep j hn]
    rfl

/-- An accepted budget is one at which the refined machine has halted. -/
theorem accepts_halted {t : Term} {M n : Nat} {rows : Nat → Row} {nF : Nat} {fin : Nat → RWMem.Tup GCell}
    (hA : Accepts t M n rows nF fin) : (ustepN n (enc (gload t), initMem t)).1.ph = .halt := by
  have hpos := hA.1
  have hlast := hA.2.2.2.1
  obtain ⟨e, rvl⟩ := accepts_honest hA (n - 1) (Nat.sub_lt hpos Nat.zero_lt_one)
  have hn : ustepN n (enc (gload t), initMem t) = ustepN (n - 1 + 1) (enc (gload t), initMem t) := by
    rw [Nat.sub_add_cancel hpos]
  rw [hn, ustepN_succ, e, ustep_eq, ← rvl]
  exact hlast

/-- **Soundness.**  An accepted trace means the graph machine halts from
    `t`, and `t` evaluates under L1 to a value whose head and arity the
    machine's has. -/
theorem accepts_sound {t : Term} {M n : Nat} {rows : Nat → Row} {nF : Nat} {fin : Nat → RWMem.Tup GCell}
    (hA : Accepts t M n rows nF fin) :
    ∃ k m' c, grun k (gload t) = some (m', c) ∧
      ∃ v nv u, Dec m'.heap m'.root v nv ∧ Eval t u ∧ spineOf v = spineOf u := by
  have hh := accepts_halted hA
  obtain ⟨k, m', c, hk⟩ := halts_of_steps n n (Nat.le_refl n) (rep_init t) hh
  exact ⟨k, m', c, hk, graph_spine hk⟩

theorem lastW_congr {ops ops' : Nat → RWMem.Op GCell} {a : Nat} : ∀ j,
    (∀ i, i < j → (ops i).addr = (ops' i).addr) → RWMem.lastW ops a j = RWMem.lastW ops' a j
  | 0, _ => rfl
  | j + 1, h => by
    show (if (ops j).addr = a then some j else RWMem.lastW ops a j) =
      (if (ops' j).addr = a then some j else RWMem.lastW ops' a j)
    rw [h j (Nat.lt_succ_self j), lastW_congr j fun i hi => h i (Nat.lt_succ_of_lt hi)]

theorem expected_congr {ops ops' : Nat → RWMem.Op GCell} {f : Nat → GCell} {a j : Nat}
    (h : ∀ i, i < j → (ops i).addr = (ops' i).addr ∧ (ops i).wv = (ops' i).wv) :
    RWMem.expected ops f a j = RWMem.expected ops' f a j := by
  unfold RWMem.expected
  rw [lastW_congr j fun i hi => (h i hi).1]
  cases hl : RWMem.lastW ops' a j with
  | none => rfl
  | some i =>
    show ((ops i).wv, i + 1) = ((ops' i).wv, i + 1)
    rw [(h i (RWMem.lastW_some ops' hl).1).2]

section
variable (t : Term)

/-- The honest run's start. -/
def s0 : Regs × (Nat → GCell) := (enc (gload t), initMem t)

/-- The honest accesses, read times left out. -/
def opsH (j : Nat) : RWMem.Op GCell :=
  ⟨addrOf (ustepN j (s0 t)).1, (ustepN j (s0 t)).2 (addrOf (ustepN j (s0 t)).1), 0,
    (next (ustepN j (s0 t)).1 ((ustepN j (s0 t)).2 (addrOf (ustepN j (s0 t)).1))).2⟩

/-- The honest rows, each read time the last write's. -/
def rowsH (j : Nat) : Row :=
  ⟨(ustepN j (s0 t)).1, (ustepN j (s0 t)).2 (addrOf (ustepN j (s0 t)).1),
    (RWMem.expected (opsH t) (initMem t) (addrOf (ustepN j (s0 t)).1) j).2⟩
end

theorem memAt_honest (t : Term) : ∀ j, (ustepN j (s0 t)).2 = memAt (fun i => opOf (rowsH t i)) (initMem t) j
  | 0 => rfl
  | j + 1 => by
    rw [ustepN_succ]
    have ih := memAt_honest t j
    show upd (ustepN j (s0 t)).2 _ _ =
      upd (memAt (fun i => opOf (rowsH t i)) (initMem t) j) (opOf (rowsH t j)).addr (opOf (rowsH t j)).wv
    rw [← ih]
    rfl

/-- **A halted budget is accepted**: if the refined machine has halted by
    step `n`, the honest rows are accepted at `n`, over any `M` above the
    addresses they touch. -/
theorem accepts_of_halted {t : Term} {n M : Nat} (hN : (ustepN n (s0 t)).1.ph = .halt)
    (hM : ∀ j, j < n → addrOf (rowsH t j).regs < M) :
    Accepts t M n (rowsH t) M (RWMem.curT (fun i => opOf (rowsH t i)) (initMem t) n) := by
  have hpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with z | p
    · subst z; cases hN
    · exact p
  have reads : ∀ j, j < n → ((opOf (rowsH t j)).rv, (opOf (rowsH t j)).rt) =
      RWMem.expected (fun i => opOf (rowsH t i)) (initMem t) (opOf (rowsH t j)).addr j := by
    intro j _
    have e1 : (opOf (rowsH t j)).rv = (RWMem.expected (fun i => opOf (rowsH t i)) (initMem t)
        (opOf (rowsH t j)).addr j).1 := by
      rw [expected_memAt, ← memAt_honest]
      rfl
    have e2 : (opOf (rowsH t j)).rt = (RWMem.expected (fun i => opOf (rowsH t i)) (initMem t)
        (opOf (rowsH t j)).addr j).2 := by
      show (RWMem.expected (opsH t) (initMem t) _ j).2 = _
      rw [expected_congr (ops := opsH t) (ops' := fun i => opOf (rowsH t i)) fun i _ => ⟨rfl, rfl⟩]
      rfl
    rw [e1, e2]
  obtain ⟨hb, ht⟩ := RWMem.rw_complete (ops := fun i => opOf (rowsH t i)) (f := initMem t) (n := n) (M := M)
    hM reads
  refine ⟨hpos, rfl, fun j _ => ?_, ?_, hb, ht⟩
  · show (ustepN (j + 1) (s0 t)).1 = _
    rw [ustepN_succ]
    rfl
  · have h := hN
    rw [← Nat.sub_add_cancel hpos, ustepN_succ] at h
    exact h

/-- **Completeness, at every budget.**  If the graph machine halts from
    `t`, some `N` steps reach the halt, and for every budget `n ≥ N` the
    honest rows are accepted over any `M` above the addresses they touch. -/
theorem accepts_complete {t : Term} {k c : Nat} {m' : GM} (hk : grun k (gload t) = some (m', c)) :
    ∃ N, 0 < N ∧ ∀ n M, N ≤ n → (∀ j, j < n → addrOf (rowsH t j).regs < M) →
      Accepts t M n (rowsH t) M (RWMem.curT (fun i => opOf (rowsH t i)) (initMem t) n) := by
  obtain ⟨N, hN⟩ := steps_of_halts k hk (inv_load t) (rep_init t)
  have Npos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with z | p
    · subst z; cases hN
    · exact p
  exact ⟨N, Npos, fun n M hn hM => accepts_of_halted (halted_le hN hn) hM⟩

/-- **The accepted trace is unique at each budget.** -/
theorem accepts_unique {t : Term} {M n : Nat} {rows rows' : Nat → Row} {nF nF' : Nat}
    {fin fin' : Nat → RWMem.Tup GCell} (hA : Accepts t M n rows nF fin) (hA' : Accepts t M n rows' nF' fin') :
    ∀ j, j < n → (rows j).regs = (rows' j).regs ∧ (rows j).rv = (rows' j).rv ∧ (rows j).rt = (rows' j).rt := by
  have regs_rv : ∀ j, j < n → (rows j).regs = (rows' j).regs ∧ (rows j).rv = (rows' j).rv := by
    intro j hj
    obtain ⟨e, r⟩ := accepts_honest hA j hj
    obtain ⟨e', r'⟩ := accepts_honest hA' j hj
    have eq := e.symm.trans e'
    have g1 : (rows j).regs = (rows' j).regs := congrArg Prod.fst eq
    have g2 : memAt (fun i => opOf (rows i)) (initMem t) j = memAt (fun i => opOf (rows' i)) (initMem t) j :=
      congrArg Prod.snd eq
    refine ⟨g1, ?_⟩
    rw [r, r', g2, g1]
  intro j hj
  obtain ⟨g1, g2⟩ := regs_rv j hj
  refine ⟨g1, g2, ?_⟩
  have t1 := congrArg Prod.snd (RWMem.rw_sound hA.2.2.2.2.1 hA.2.2.2.2.2 j hj)
  have t2 := congrArg Prod.snd (RWMem.rw_sound hA'.2.2.2.2.1 hA'.2.2.2.2.2 j hj)
  have ea : (opOf (rows j)).addr = (opOf (rows' j)).addr := by
    show addrOf _ = addrOf _
    rw [g1]
  refine t1.trans (Eq.trans ?_ t2.symm)
  rw [ea]
  refine congrArg Prod.snd (expected_congr fun i hi => ?_)
  obtain ⟨h1, h2⟩ := regs_rv i (Nat.lt_trans hi hj)
  constructor
  · show addrOf _ = addrOf _
    rw [h1]
  · show (next _ _).2 = (next _ _).2
    rw [h1, h2]

end GraphMem
