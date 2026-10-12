import Ski.ZK.CompPSD
import Ski.Circuit.BaseComplete
import Ski.Circuit.CompHeap
import Ski.InstOpen
import Ski.ComposedText

/-!
# From an accepted witness to an accepted run, within a budget

`composeC` starts from a run of the composed machine that the AIR with
segments accepts (`CRel`).  This file builds one from the circuit's
witness, literal bits `ρ` and a region whose witness term `w` makes every
statement term evaluate to `K` (`EvalRel`), whenever the run fits the
statement's heights.

**The composed run** (`citer`) is deterministic: the machine steps
(`mstep`); at a halt it restarts at the next segment's root over the nil,
and at the last segment's halt it stays.  Each segment starts from a state
reading back its term applied to the bits and the witness
(`cMachine_decode`), which evaluates to `K`, so the machine reaches a
halted state reading back `K` (`reach_of_evalF`).  **The budget**
(`CBudget`) is that the run is in its last segment, halted, by a step
`T < 2^R`, on a heap of at most `2^Lm` cells: a bounded property of the
run, which running the machine checks; `Ski/ZK/CompRunEx.lean` proves it
by kernel evaluation for the released `∨` statement.  `CRel`'s caps
(heights `2^20`, bits and region `2^8` cells) bound what any statement
can fit: a realizer whose evaluation needs more has no run.  Under it the
run's rows, over its last heap padded to `2^Lm` cells, are accepted
(`acceptsC_of_eval`), and so are in `CRel` (`crel_of_eval`).
-/

namespace Circuit

open Term Mach Air Compose CompM Stmt Wit

-- ---------------------------------------------------------------------------
-- Closed reads
-- ---------------------------------------------------------------------------

/-- **A closed open read is a read**: a cell that reads back, as an open
    term, as a closed term's image reads back as that term. -/
theorem termAt_of_otermAt {heap : List Cell} : ∀ {F a : Nat} {u : Term},
    otermAt heap F a = some u.toO → termAt heap F a = some u
  | 0, _, _, h => by cases h
  | F + 1, a, u, h => by
    unfold otermAt at h
    unfold termAt
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | S => cases u <;> cases h; rfl
      | K => cases u <;> cases h; rfl
      | I => cases u <;> cases h; rfl
      | atom n => cases u <;> cases h
      | nil => cases h
      | cons _ _ => cases h
      | app g x =>
        dsimp only at h ⊢
        cases hg : otermAt heap F g with
        | none => rw [hg] at h; cases h
        | some tg =>
          cases hx : otermAt heap F x with
          | none => rw [hg, hx] at h; cases h
          | some tx =>
            rw [hg, hx] at h
            cases u with
            | S => cases h
            | K => cases h
            | I => cases h
            | app ug ux =>
              cases h
              rw [termAt_of_otermAt hg, termAt_of_otermAt hx]

-- ---------------------------------------------------------------------------
-- The composed run
-- ---------------------------------------------------------------------------

section
variable (roots : List Nat) (nilA n : Nat)

/-- **One step of the composed run**: a machine transition; at a halt, the
    next segment's root over the nil; at the last segment's halt, stay. -/
def cadv (p : Mach × Nat) : Mach × Nat :=
  match mstep p.1 with
  | some m' => (m', p.2)
  | none => if p.2 + 1 < n then (⟨p.1.heap, roots.getD (p.2 + 1) 0, nilA⟩, p.2 + 1) else p

/-- `i` steps of the composed run. -/
def citer : Nat → Mach × Nat → Mach × Nat
  | 0, p => p
  | i + 1, p => citer i (cadv roots nilA n p)

theorem citer_succ' : ∀ (i : Nat) (p : Mach × Nat), citer roots nilA n (i + 1) p = cadv roots nilA n (citer roots nilA n i p)
  | 0, _ => rfl
  | i + 1, p => citer_succ' i (cadv roots nilA n p)

theorem citer_add : ∀ (i j : Nat) (p : Mach × Nat), citer roots nilA n (i + j) p = citer roots nilA n j (citer roots nilA n i p)
  | i, 0, p => rfl
  | i, j + 1, p => by
    rw [show i + (j + 1) = (i + j) + 1 by omega, citer_succ', citer_succ', citer_add i j p]

theorem cadv_prefix (p : Mach × Nat) : ∃ cs, (cadv roots nilA n p).1.heap = p.1.heap ++ cs := by
  unfold cadv
  cases h : mstep p.1 with
  | some m' => exact mstep_append h
  | none =>
    dsimp only
    split
    · exact ⟨[], by simp⟩
    · exact ⟨[], by simp⟩

theorem citer_prefix (p : Mach × Nat) : ∀ i j, ∃ cs,
    (citer roots nilA n (i + j) p).1.heap = (citer roots nilA n i p).1.heap ++ cs
  | _, 0 => ⟨[], by simp⟩
  | i, j + 1 => by
    obtain ⟨cs, hc⟩ := citer_prefix p i j
    obtain ⟨ds, hd⟩ := cadv_prefix roots nilA n (citer roots nilA n (i + j) p)
    refine ⟨cs ++ ds, ?_⟩
    rw [show i + (j + 1) = (i + j) + 1 by omega, citer_succ', hd, hc, List.append_assoc]

end

-- ---------------------------------------------------------------------------
-- A first index
-- ---------------------------------------------------------------------------

/-- The least `i < B` with `f i`, or `B`. -/
def findIdx (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | B + 1 => if findIdx f B < B then findIdx f B else if f B then B else B + 1

theorem findIdx_le (f : Nat → Bool) : ∀ B, findIdx f B ≤ B
  | 0 => Nat.le_refl 0
  | B + 1 => by
    have := findIdx_le f B
    unfold findIdx
    split
    · omega
    · split <;> omega

theorem findIdx_none (f : Nat → Bool) : ∀ B, ∀ i, i < findIdx f B → f i = false
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | B + 1, i, h => by
    have ih := findIdx_none f B
    have hle := findIdx_le f B
    unfold findIdx at h
    split at h
    · exact ih i h
    · have e : findIdx f B = B := by omega
      split at h
      · exact ih i (by omega)
      · rcases Nat.lt_or_ge i B with hi | hi
        · exact ih i (by omega)
        · have : i = B := by omega
          subst this
          rename_i hf
          simpa using hf

theorem findIdx_some (f : Nat → Bool) : ∀ B, findIdx f B < B → f (findIdx f B) = true
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | B + 1, h => by
    have ih := findIdx_some f B
    unfold findIdx at h ⊢
    split
    · rename_i hl; exact ih hl
    · split
      · rename_i _ hf; exact hf
      · split at h
        · omega
        · exact absurd h (Nat.lt_irrefl _)

/-- **The least index**: when some `i < B` has `f i`, `findIdx` is the
    least. -/
theorem findIdx_least (f : Nat → Bool) (B : Nat) {i : Nat} (hi : i < B) (hf : f i = true) :
    findIdx f B ≤ i ∧ f (findIdx f B) = true := by
  have hle : findIdx f B ≤ i := by
    rcases Nat.lt_or_ge i (findIdx f B) with h | h
    · rw [findIdx_none f B i h] at hf; cases hf
    · exact h
  exact ⟨hle, findIdx_some f B (by omega)⟩

-- ---------------------------------------------------------------------------
-- Halting at `K` over the empty stack
-- ---------------------------------------------------------------------------

theorem apps_app_ne_K : ∀ (x y : Term) (as : List Term), apps (x ⬝ y) as ≠ .K
  | _, _, [] => fun h => by cases h
  | x, y, a :: as => apps_app_ne_K (x ⬝ y) a as

theorem apps_eq_K {t : Term} {args : List Term} (h : apps t args = .K) : t = .K ∧ args = [] := by
  cases args with
  | nil => exact ⟨h, rfl⟩
  | cons a as =>
    exact absurd h (apps_app_ne_K t a as)

theorem termAt_K {heap : List Cell} {f a : Nat} (h : termAt heap f a = some .K) : heap[a]? = some .K := by
  cases f with
  | zero => cases h
  | succ f =>
    unfold termAt at h
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | K => rfl
      | S => cases h
      | I => cases h
      | atom _ => cases h
      | nil => cases h
      | cons _ _ => cases h
      | app g x =>
        dsimp only at h
        cases hg : termAt heap f g with
        | none => rw [hg] at h; cases h
        | some tg =>
          cases hx : termAt heap f x with
          | none => rw [hg, hx] at h; cases h
          | some tx => rw [hg, hx] at h; cases h

theorem stackAt_nil {heap : List Cell} {f a : Nat} (h : stackAt heap f a = some []) : heap[a]? = some .nil := by
  cases f with
  | zero => cases h
  | succ f =>
    unfold stackAt at h
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | nil => rfl
      | cons x r =>
        dsimp only at h
        cases hx : termAt heap (f + 1) x with
        | none => rw [hx] at h; cases h
        | some tx =>
          cases hr : stackAt heap f r with
          | none => rw [hx, hr] at h; cases h
          | some rest => rw [hx, hr] at h; cases h
      | _ => cases h

/-- **A state reading back `K` has `K` at its head over the empty stack.** -/
theorem decode_K {m : Mach} (h : decode m = some .K) : m.heap[m.hd]? = some .K ∧ m.heap[m.stk]? = some .nil := by
  obtain ⟨th, args, h1, h2, e⟩ := decode_eq h
  obtain ⟨rfl, rfl⟩ := apps_eq_K e.symm
  exact ⟨termAt_K h1, stackAt_nil h2⟩

-- ---------------------------------------------------------------------------
-- A segment
-- ---------------------------------------------------------------------------

section
variable {roots : List Nat} {nilA n : Nat}

/-- **A segment runs to `K`**: from a state reading back a term that
    evaluates to `K`, the composed run follows the machine, staying in its
    segment, until it halts on a state reading back `K`. -/
theorem seg_run {m : Mach} {j : Nat} {t : Term} (hd : decode m = some t) (he : Eval t .K) :
    ∃ k, (∀ i, i ≤ k → citer roots nilA n i (m, j) = (iterM i m, j)) ∧
      (∀ i, i < k → mstep (iterM i m) = some (iterM (i + 1) m)) ∧
      mstep (iterM k m) = none ∧ decode (iterM k m) = some .K := by
  obtain ⟨N, hN⟩ := evalF_complete he
  obtain ⟨m', c, hr, hstop, hv⟩ := reach_of_evalF hN (hsize m) (Nat.le_refl _) hd
  obtain ⟨k, hstep, hfin⟩ := iterM_of_reach hr hstop
  have hk : iterM k m = m' := hfin k (Nat.le_refl k)
  refine ⟨k, ?_, hstep, by rw [hk]; exact hstop, by rw [hk]; exact hv⟩
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [citer_succ', ih (by omega)]
    unfold cadv
    rw [hstep i (by omega)]

/-- The run's segment never decreases, and steps up by at most one. -/
theorem cadv_seg (p : Mach × Nat) :
    (cadv roots nilA n p).2 = p.2 ∨ ((cadv roots nilA n p).2 = p.2 + 1 ∧ mstep p.1 = none ∧ p.2 + 1 < n) := by
  unfold cadv
  cases h : mstep p.1 with
  | some m' => exact .inl rfl
  | none =>
    dsimp only
    split
    · rename_i hlt; exact .inr ⟨rfl, rfl, hlt⟩
    · exact .inl rfl

theorem citer_seg_mono (p : Mach × Nat) : ∀ i j, (citer roots nilA n i p).2 ≤ (citer roots nilA n (i + j) p).2
  | _, 0 => Nat.le_refl _
  | i, j + 1 => by
    have := citer_seg_mono p i j
    rw [show i + (j + 1) = (i + j) + 1 by omega, citer_succ']
    rcases cadv_seg (roots := roots) (nilA := nilA) (n := n) (citer roots nilA n (i + j) p) with h | ⟨h, _⟩ <;> omega

theorem citer_seg_lt (p : Mach × Nat) (h0 : p.2 < n) : ∀ i, (citer roots nilA n i p).2 < n
  | 0 => h0
  | i + 1 => by
    rw [citer_succ']
    rcases cadv_seg (roots := roots) (nilA := nilA) (n := n) (citer roots nilA n i p) with h | ⟨h, _, hl⟩
    · rw [h]; exact citer_seg_lt p h0 i
    · omega

end

-- ---------------------------------------------------------------------------
-- The composed machine's segments
-- ---------------------------------------------------------------------------

section
variable {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Ps : List Term} {w : Term}

/-- The composed machine's roots, nil, segment count and start. -/
abbrev croots (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) : List Nat :=
  (cHeap ρ shp region Ps).2
abbrev cnil (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) : Nat :=
  (cHeap ρ shp region Ps).1.length
abbrev cp0 (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) : Mach × Nat :=
  (cMachine ρ shp region Ps, 0)
/-- The composed run from the start. -/
abbrev crun (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) (i : Nat) : Mach × Nat :=
  citer (croots ρ shp region Ps) (cnil ρ shp region Ps) Ps.length i (cp0 ρ shp region Ps)

/-- **A segment's start reads back its term** applied to the bits and the
    witness, over any heap the run has grown from the composed machine's. -/
theorem decode_start (hw : cWitness ρ (BT.nleaves shp) region = some w) {j : Nat} {P : Term}
    (hP : Ps[j]? = some P) (cs : List Cell) :
    decode ⟨(cMachine ρ shp region Ps).heap ++ cs, (croots ρ shp region Ps).getD j 0, cnil ρ shp region Ps⟩ =
      some (P ⬝ (fillB shp ρ 0).enc ⬝ w) := by
  have ho := (cMachine_decode (Ps := Ps) hw).2 j P hP
  have ht : termAt (cMachine ρ shp region Ps).heap ((cMachine ρ shp region Ps).heap.length + 1)
      ((croots ρ shp region Ps).getD j 0) = some (P ⬝ (fillB shp ρ 0).enc ⬝ w) :=
    termAt_of_otermAt (u := P ⬝ (fillB shp ρ 0).enc ⬝ w) ho
  have ht' := termAt_grow (cs := cs) ht (k := ((cMachine ρ shp region Ps).heap ++ cs).length + 1)
    (by simp)
  have hnil : ((cMachine ρ shp region Ps).heap ++ cs)[cnil ρ shp region Ps]? = some .nil := by
    show ((cHeap ρ shp region Ps).1 ++ [Cell.nil] ++ cs)[(cHeap ρ shp region Ps).1.length]? = _
    simp
  have hs : stackAt ((cMachine ρ shp region Ps).heap ++ cs) (((cMachine ρ shp region Ps).heap ++ cs).length + 1)
      (cnil ρ shp region Ps) = some [] := by
    unfold stackAt
    rw [hnil]
  unfold decode
  dsimp only
  rw [ht', hs]
  rfl

/-- The run's machines grow the composed machine's heap. -/
theorem crun_heap (i : Nat) : ∃ cs, (crun ρ shp region Ps i).1.heap = (cMachine ρ shp region Ps).heap ++ cs := by
  obtain ⟨cs, hc⟩ := citer_prefix (croots ρ shp region Ps) (cnil ρ shp region Ps) Ps.length
    (cp0 ρ shp region Ps) 0 i
  rw [Nat.zero_add] at hc
  exact ⟨cs, hc⟩

/-- A segment's data: its first index `s`, its steps `k`, staying in the
    segment, stepping, and halting on a state reading back `K`. -/
def SegData (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) (j s k : Nat) : Prop :=
  (crun ρ shp region Ps s).2 = j ∧
  (∀ i, i < s → (crun ρ shp region Ps i).2 < j) ∧
  (∀ i, i ≤ k → (crun ρ shp region Ps (s + i)).2 = j) ∧
  (∀ i, i < k → mstep (crun ρ shp region Ps (s + i)).1 = some (crun ρ shp region Ps (s + i + 1)).1) ∧
  mstep (crun ρ shp region Ps (s + k)).1 = none ∧ decode (crun ρ shp region Ps (s + k)).1 = some .K

/-- From a segment's start, its run. -/
theorem seg_from (hw : cWitness ρ (BT.nleaves shp) region = some w)
    (hev : EvalRel (Ps, SameShape shp) (fillB shp ρ 0) w) {j s : Nat} (hj : j < Ps.length) {cs : List Cell}
    (hs : crun ρ shp region Ps s =
      (⟨(cMachine ρ shp region Ps).heap ++ cs, (croots ρ shp region Ps).getD j 0, cnil ρ shp region Ps⟩, j))
    (hbefore : ∀ i, i < s → (crun ρ shp region Ps i).2 < j) :
    ∃ k, SegData ρ shp region Ps j s k := by
  obtain ⟨P, hP⟩ : ∃ P, Ps[j]? = some P := ⟨Ps[j], List.getElem?_eq_getElem hj⟩
  have hd := decode_start hw hP cs
  have he : Eval (P ⬝ (fillB shp ρ 0).enc ⬝ w) .K := hev.2 P (List.mem_of_getElem? hP)
  obtain ⟨k, hrun, hstep, hstop, hK⟩ := seg_run (roots := croots ρ shp region Ps) (nilA := cnil ρ shp region Ps)
    (n := Ps.length) (j := j) hd he
  have hc : ∀ i, i ≤ k → crun ρ shp region Ps (s + i) =
      (iterM i ⟨(cMachine ρ shp region Ps).heap ++ cs, (croots ρ shp region Ps).getD j 0, cnil ρ shp region Ps⟩, j) := by
    intro i hi
    show citer _ _ _ (s + i) _ = _
    rw [citer_add]
    show citer _ _ _ i (crun ρ shp region Ps s) = _
    rw [hs]
    exact hrun i hi
  refine ⟨k, by rw [hs], hbefore, fun i hi => by rw [hc i hi], fun i hi => ?_, by rw [hc k (Nat.le_refl k)]; exact hstop,
    by rw [hc k (Nat.le_refl k)]; exact hK⟩
  rw [hc i (by omega), show s + i + 1 = s + (i + 1) by omega, hc (i + 1) (by omega)]
  exact hstep i hi

/-- **Every segment runs to `K`.** -/
theorem segs (hw : cWitness ρ (BT.nleaves shp) region = some w)
    (hev : EvalRel (Ps, SameShape shp) (fillB shp ρ 0) w) :
    ∀ j, j < Ps.length → ∃ s k, SegData ρ shp region Ps j s k
  | 0, hj => by
    have hs : crun ρ shp region Ps 0 =
        (⟨(cMachine ρ shp region Ps).heap ++ [], (croots ρ shp region Ps).getD 0 0, cnil ρ shp region Ps⟩, 0) := by
      show (cMachine ρ shp region Ps, 0) = _
      rw [List.append_nil]
      rfl
    obtain ⟨k, hk⟩ := seg_from hw hev hj hs (fun i hi => absurd hi (Nat.not_lt_zero _))
    exact ⟨0, k, hk⟩
  | j + 1, hj => by
    obtain ⟨s, k, hj0, hbef, hin, _, hstop, _⟩ := segs hw hev j (by omega)
    obtain ⟨cs, hcs⟩ := crun_heap (ρ := ρ) (shp := shp) (region := region) (Ps := Ps) (s + k)
    have hnext : crun ρ shp region Ps (s + k + 1) =
        (⟨(cMachine ρ shp region Ps).heap ++ cs, (croots ρ shp region Ps).getD (j + 1) 0, cnil ρ shp region Ps⟩, j + 1) := by
      show citer _ _ _ (s + k + 1) _ = _
      rw [citer_succ']
      show cadv _ _ _ (crun ρ shp region Ps (s + k)) = _
      unfold cadv
      rw [hstop]
      dsimp only
      rw [hin k (Nat.le_refl k), if_pos hj, hcs]
    have hbef' : ∀ i, i < s + k + 1 → (crun ρ shp region Ps i).2 < j + 1 := by
      intro i hi
      rcases Nat.lt_or_ge i s with h | h
      · have := hbef i h; omega
      · have := hin (i - s) (by omega)
        rw [show s + (i - s) = i by omega] at this
        omega
    obtain ⟨k', hk'⟩ := seg_from hw hev hj hnext hbef'
    exact ⟨s + k + 1, k', hk'⟩

end

-- ---------------------------------------------------------------------------
-- The accepted run
-- ---------------------------------------------------------------------------

section
variable {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Ps : List Term} {w : Term}

/-- **Segment ends**: segment `j` ends at the first step, up to `T`, in it
    with no transition. -/
def cend (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) (T j : Nat) : Nat :=
  findIdx (fun i => (crun ρ shp region Ps i).2 == j && (mstep (crun ρ shp region Ps i).1).isNone) (T + 1)

theorem crun_seg_mono {i i' : Nat} (h : i ≤ i') : (crun ρ shp region Ps i).2 ≤ (crun ρ shp region Ps i').2 := by
  have := citer_seg_mono (roots := croots ρ shp region Ps) (nilA := cnil ρ shp region Ps) (n := Ps.length)
    (cp0 ρ shp region Ps) i (i' - i)
  rwa [show i + (i' - i) = i' by omega] at this

/-- **A segment ends where its data says**, by `T` when the run is halted in
    its last segment at `T`. -/
theorem cend_eq {T j s k : Nat} (hj : j < Ps.length) (hT : (crun ρ shp region Ps T).2 = Ps.length - 1)
    (hTs : mstep (crun ρ shp region Ps T).1 = none) (hd : SegData ρ shp region Ps j s k) :
    cend ρ shp region Ps T j = s + k ∧ s + k ≤ T := by
  obtain ⟨_, hbef, hin, hstep, hstop, _⟩ := hd
  have hle : s + k ≤ T := by
    rcases Nat.lt_or_ge T (s + k) with h | h
    · rcases Nat.lt_or_ge T s with h' | h'
      · have := hbef T h'; omega
      · have hm := hstep (T - s) (by omega)
        rw [show s + (T - s) = T by omega, hTs] at hm
        cases hm
    · exact h
  refine ⟨?_, hle⟩
  have hf : ((fun i => (crun ρ shp region Ps i).2 == j && (mstep (crun ρ shp region Ps i).1).isNone) (s + k)) = true := by
    show ((crun ρ shp region Ps (s + k)).2 == j && (mstep (crun ρ shp region Ps (s + k)).1).isNone) = true
    rw [hin k (Nat.le_refl k), hstop]
    show (j == j && true) = true
    have hb : (j == j) = true := by
      show decide (j = j) = true
      exact decide_eq_true rfl
    rw [hb]
    rfl
  obtain ⟨hl, hft⟩ := findIdx_least (fun i => (crun ρ shp region Ps i).2 == j &&
    (mstep (crun ρ shp region Ps i).1).isNone) (T + 1) (i := s + k) (by omega) hf
  show findIdx (fun i => (crun ρ shp region Ps i).2 == j && (mstep (crun ρ shp region Ps i).1).isNone) (T + 1) = s + k
  generalize findIdx (fun i => (crun ρ shp region Ps i).2 == j &&
    (mstep (crun ρ shp region Ps i).1).isNone) (T + 1) = x at hl hft
  rcases Nat.lt_or_ge x (s + k) with h | h
  · exfalso
    rw [Bool.and_eq_true] at hft
    obtain ⟨hseg0, hnone⟩ := hft
    have hseg := eq_of_beq hseg0
    rcases Nat.lt_or_ge x s with h' | h'
    · have := hbef x h'; omega
    · have hm := hstep (x - s) (by omega)
      rw [show s + (x - s) = x by omega] at hm
      rw [hm] at hnone
      cases hnone
  · exact Nat.le_antisymm hl h

/-- **The run's rows are accepted.**  From literal bits and a region whose
    witness makes every statement term evaluate to `K`, with the run in its
    last segment and halted at step `T`, the composed run's rows over its
    heap at `T`, padded with nils, are accepted by the AIR with segments. -/
theorem acceptsC_of_eval (hw : cWitness ρ (BT.nleaves shp) region = some w)
    (hev : EvalRel (Ps, SameShape shp) (fillB shp ρ 0) w) (hn : 0 < Ps.length) {T : Nat}
    (hT : (crun ρ shp region Ps T).2 = Ps.length - 1) (hTs : mstep (crun ρ shp region Ps T).1 = none)
    (pad : Nat) :
    AcceptsC ((crun ρ shp region Ps T).1.heap ++ List.replicate pad .nil) (cMachine ρ shp region Ps)
      (cHeap ρ shp region Ps).2 (cHeap ρ shp region Ps).1.length Ps.length (cend ρ shp region Ps T)
      (fun i => regs (crun ρ shp region Ps i).1) := by
  let M := (crun ρ shp region Ps T).1.heap ++ List.replicate pad .nil
  have pre : ∀ i, i ≤ T → M.take (crun ρ shp region Ps i).1.heap.length = (crun ρ shp region Ps i).1.heap := by
    intro i hi
    obtain ⟨cs, hc⟩ := citer_prefix (croots ρ shp region Ps) (cnil ρ shp region Ps) Ps.length
      (cp0 ρ shp region Ps) i (T - i)
    rw [show i + (T - i) = T by omega] at hc
    exact take_of_prefix (h := (crun ρ shp region Ps i).1.heap) (cs := cs ++ List.replicate pad .nil)
      (by show _ ++ _ = _; rw [hc, List.append_assoc])
  -- every segment, with its end
  have hseg := segs hw hev
  have ends : ∀ j, j < Ps.length → ∃ s k, SegData ρ shp region Ps j s k ∧
      cend ρ shp region Ps T j = s + k ∧ s + k ≤ T := by
    intro j hj
    obtain ⟨s, k, hd⟩ := hseg j hj
    exact ⟨s, k, hd, cend_eq hj hT hTs hd⟩
  have hrestart : ∀ j, j + 1 < Ps.length → crun ρ shp region Ps (cend ρ shp region Ps T j + 1) =
      (⟨(crun ρ shp region Ps (cend ρ shp region Ps T j)).1.heap, (cHeap ρ shp region Ps).2.getD (j + 1) 0,
        (cHeap ρ shp region Ps).1.length⟩, j + 1) := by
    intro j hj
    obtain ⟨s, k, ⟨_, _, hin, _, hstop, _⟩, he, _⟩ := ends j (by omega)
    show citer _ _ _ (cend ρ shp region Ps T j + 1) _ = _
    rw [citer_succ']
    show cadv _ _ _ (crun ρ shp region Ps (cend ρ shp region Ps T j)) = _
    rw [he]
    unfold cadv
    rw [hstop]
    dsimp only
    rw [hin k (Nat.le_refl k), if_pos hj]
  refine {
    npos := hn
    heap0 := pre 0 (Nat.zero_le _)
    hd0 := rfl
    stk0 := rfl
    ctr0 := rfl
    emono := fun j hj => ?_
    restart := fun j hj => ?_
    trans := fun i hi hne => ?_
    ends := fun j hj => ?_ }
  · -- the ends increase
    obtain ⟨s, k, ⟨_, _, hin, _⟩, he, _⟩ := ends j (by omega)
    obtain ⟨s', k', ⟨_, _, hin', _⟩, he', _⟩ := ends (j + 1) hj
    rw [he, he']
    rcases Nat.lt_or_ge (s + k) (s' + k') with h | h
    · exact h
    · exfalso
      have := crun_seg_mono (ρ := ρ) (shp := shp) (region := region) (Ps := Ps) h
      rw [hin k (Nat.le_refl k), hin' k' (Nat.le_refl k')] at this
      omega
  · -- the restart
    rw [hrestart j hj]
    rfl
  · -- inside a segment, a transition
    have hlt : (crun ρ shp region Ps i).2 < Ps.length :=
      citer_seg_lt (roots := croots ρ shp region Ps) (nilA := cnil ρ shp region Ps) (n := Ps.length)
        (cp0 ρ shp region Ps) hn i
    obtain ⟨s, k, ⟨hs0, hbef, hin, hstep, _⟩, he, hle⟩ := ends (crun ρ shp region Ps i).2 hlt
    obtain ⟨sl, kl, _, hel, hlel⟩ := ends (Ps.length - 1) (by omega)
    have hsi : s ≤ i := by
      rcases Nat.lt_or_ge i s with h | h
      · have := hbef i h; omega
      · exact h
    have hik : i < s + k := by
      rcases Nat.lt_or_ge i (s + k) with h | h
      · exact h
      · exfalso
        by_cases hj : (crun ρ shp region Ps i).2 + 1 < Ps.length
        · rcases Nat.lt_or_ge (s + k) i with h' | h'
          · have hr := hrestart _ hj
            rw [he] at hr
            have hm := crun_seg_mono (ρ := ρ) (shp := shp) (region := region) (Ps := Ps)
              (show s + k + 1 ≤ i by omega)
            rw [hr] at hm
            dsimp only at hm
            omega
          · exact hne _ hj (by rw [he]; omega)
        · have e1 : (crun ρ shp region Ps i).2 = Ps.length - 1 := by omega
          rw [e1] at he
          rw [hel] at hi
          have : s + k = sl + kl := by rw [← he, ← hel]
          omega
    have hm := hstep (i - s) (by omega)
    rw [show s + (i - s) = i by omega] at hm
    have hiT : i + 1 ≤ T := by
      have hi' := hi
      rw [hel] at hi'
      omega
    left
    exact mstep_stepRow (pre i (by omega)) (pre (i + 1) hiT) hm
  · -- the ends read `K` over the nil
    obtain ⟨s, k, ⟨_, _, _, _, _, hK⟩, he, hle⟩ := ends j hj
    obtain ⟨h1, h2⟩ := decode_K hK
    have hp := pre (s + k) hle
    show rd M (regs (crun ρ shp region Ps (cend ρ shp region Ps T j)).1).ctr
        (regs (crun ρ shp region Ps (cend ρ shp region Ps T j)).1).hd = some .K ∧
      rd M (regs (crun ρ shp region Ps (cend ρ shp region Ps T j)).1).ctr
        (regs (crun ρ shp region Ps (cend ρ shp region Ps T j)).1).stk = some .nil
    rw [he]
    unfold regs
    dsimp only
    rw [rd_eq, rd_eq, hp]
    exact ⟨h1, h2⟩

end

-- ---------------------------------------------------------------------------
-- The budget, and the run in `CRel`
-- ---------------------------------------------------------------------------

section
variable {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Ps : List Term} {w : Term}

theorem croots_lt (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true) (x : Nat) :
    (croots ρ shp region Ps).getD x 0 < (cMachine ρ shp region Ps).heap.length := by
  have hf := (cMachine_fits ρ shp region Ps hr).2
  have hpos : 0 < (cMachine ρ shp region Ps).heap.length := by
    show 0 < ((cHeap ρ shp region Ps).1 ++ [Cell.nil]).length
    simp
  rw [List.getD_eq_getElem?_getD]
  cases h : (croots ρ shp region Ps)[x]? with
  | none => exact hpos
  | some r => exact hf r (List.mem_of_getElem? h)

/-- **The run's machines are well formed**: their cells point into the heap,
    and their head and stack are on it. -/
theorem crun_fits (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true) :
    ∀ i, MFits (crun ρ shp region Ps i).1
  | 0 => by
    refine ⟨(cMachine_fits ρ shp region Ps hr).1, croots_lt hr 0, ?_⟩
    show (cHeap ρ shp region Ps).1.length < ((cHeap ρ shp region Ps).1 ++ [Cell.nil]).length
    simp
  | i + 1 => by
    have ih := crun_fits hr i
    show MFits (citer _ _ _ (i + 1) _).1
    rw [citer_succ']
    show MFits (cadv _ _ _ (crun ρ shp region Ps i)).1
    unfold cadv
    cases hs : mstep (crun ρ shp region Ps i).1 with
    | some m' => exact mstep_fits ih hs
    | none =>
      dsimp only
      split
      · obtain ⟨cs, hcs⟩ := crun_heap (ρ := ρ) (shp := shp) (region := region) (Ps := Ps) i
        have hle : (cMachine ρ shp region Ps).heap.length ≤ (crun ρ shp region Ps i).1.heap.length := by
          rw [hcs, List.length_append]; omega
        refine ⟨ih.1, Nat.lt_of_lt_of_le (croots_lt hr _) hle, Nat.lt_of_lt_of_le ?_ hle⟩
        show (cHeap ρ shp region Ps).1.length < ((cHeap ρ shp region Ps).1 ++ [Cell.nil]).length
        simp
      · exact ih

end

/-- **The budget**: the composed run of the statement, from the bits and
    the region, is halted in its last segment by a step `T < 2^R`, on a
    heap of at most `2^Lm` cells: a bounded property of the run, which
    running the machine checks (`or_budget`, by kernel evaluation). -/
def CBudget (s : CStmt) (ρ : Nat → Bool) (region : List Cell) : Prop :=
  ∃ T, T < 2 ^ s.R ∧ (crun ρ s.shp region s.Ps T).2 = s.Ps.length - 1 ∧
    mstep (crun ρ s.shp region s.Ps T).1 = none ∧ (crun ρ s.shp region s.Ps T).1.heap.length ≤ 2 ^ s.Lm

/-- **An accepted witness within the budget has a run in `CRel`**: literal
    bits and a well-formed region of the statement's size, whose witness
    makes every statement term evaluate to `K`, give an accepted run of the
    composed machine within the statement's heights, when the run fits
    them (`CBudget`). -/
theorem crel_of_eval (s : CStmt) (hR : s.R ≤ 20) (hLm : s.Lm ≤ 20) (hNW : BT.nleaves s.shp + s.W ≤ 2 ^ 8)
    {ρ : Nat → Bool} {region : List Cell} {w : Term} (hrl : region.length = s.W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves s.shp + 3 + i) c = true)
    (hw : cWitness ρ (BT.nleaves s.shp) region = some w)
    (hev : EvalRel (s.Ps, SameShape s.shp) (fillB s.shp ρ 0) w) (hn : 0 < s.Ps.length)
    (hB : CBudget s ρ region) :
    ∃ A e row, CRel s ⟨ρ, region, A, e, row⟩ := by
  obtain ⟨T, hTR, hT, hTs, hTL⟩ := hB
  let H := (crun ρ s.shp region s.Ps T).1.heap
  refine ⟨H ++ List.replicate (2 ^ s.Lm - H.length) .nil, cend ρ s.shp region s.Ps T,
    fun i => regs (crun ρ s.shp region s.Ps i).1, hR, hLm, hNW, hrl, hr,
    acceptsC_of_eval hw hev hn hT hTs _, fits_pad (crun_fits hr T).1 _, ?_, ?_⟩
  · show (H ++ List.replicate (2 ^ s.Lm - H.length) Cell.nil).length = 2 ^ s.Lm
    rw [List.length_append, List.length_replicate]
    have : H.length = (crun ρ s.shp region s.Ps T).1.heap.length := rfl
    omega
  · obtain ⟨sl, kl, hd⟩ := segs hw hev (s.Ps.length - 1) (by omega)
    obtain ⟨he, hle⟩ := cend_eq (by omega) hT hTs hd
    show cend ρ s.shp region s.Ps T (s.Ps.length - 1) < 2 ^ s.R
    omega

-- ---------------------------------------------------------------------------
-- The circuit's witness from a formula's
-- ---------------------------------------------------------------------------

/-- The formula's shape, cleared, is the shape of its accepted bits. -/
theorem same_of_shape : ∀ (M : MF) (β : BT), Compose.Shape M β → SameShape (clear M) β
  | .atom _ _, .leaf _, _ => trivial
  | .atom _ _, .node _ _, h => h.elim
  | .and _ _, .leaf _, h => h.elim
  | .or _ _, .leaf _, h => h.elim
  | .and A B, .node l r, ⟨ha, hb⟩ => ⟨same_of_shape A l ha, same_of_shape B r hb⟩
  | .or A B, .node l r, ⟨ha, hb⟩ => ⟨same_of_shape A l ha, same_of_shape B r hb⟩

/-- A bit tree's leaves, left to right. -/
def leafAt : BT → Nat → Bool
  | .leaf b, _ => b
  | .node l r, i => if i < BT.nleaves l then leafAt l i else leafAt r (i - BT.nleaves l)

theorem nleaves_same : ∀ (a b : BT), SameShape a b → BT.nleaves a = BT.nleaves b
  | .leaf _, .leaf _, _ => rfl
  | .leaf _, .node _ _, h => h.elim
  | .node _ _, .leaf _, h => h.elim
  | .node l r, .node l' r', ⟨hl, hr⟩ => by
    show BT.nleaves l + BT.nleaves r = BT.nleaves l' + BT.nleaves r'
    rw [nleaves_same l l' hl, nleaves_same r r' hr]

/-- **Filling a shape with a tree's leaves gives the tree.** -/
theorem fillB_leafAt : ∀ (shp β : BT), SameShape shp β → ∀ (ρ : Nat → Bool) (off : Nat),
    (∀ i, i < BT.nleaves β → ρ (off + i) = leafAt β i) → fillB shp ρ off = β
  | .leaf _, .leaf b, _, ρ, off, h => by
    show BT.leaf (ρ off) = BT.leaf b
    have := h 0 (by show 0 < 1; omega)
    rw [Nat.add_zero] at this
    rw [this]; rfl
  | .leaf _, .node _ _, hs, _, _, _ => hs.elim
  | .node _ _, .leaf _, hs, _, _, _ => hs.elim
  | .node l r, .node l' r', ⟨hl, hr⟩, ρ, off, h => by
    show BT.node (fillB l ρ off) (fillB r ρ (off + BT.nleaves l)) = BT.node l' r'
    have el := nleaves_same l l' hl
    rw [fillB_leafAt l l' hl ρ off (fun i hi => by
        have := h i (by show i < BT.nleaves l' + BT.nleaves r'; omega)
        rw [this]; show (if i < BT.nleaves l' then leafAt l' i else _) = _; rw [if_pos hi]),
      fillB_leafAt r r' hr ρ (off + BT.nleaves l) (fun i hi => by
        have := h (BT.nleaves l' + i) (by show _ < BT.nleaves l' + BT.nleaves r'; omega)
        rw [show off + BT.nleaves l + i = off + (BT.nleaves l' + i) by omega, this]
        show (if BT.nleaves l' + i < BT.nleaves l' then _ else leafAt r' (BT.nleaves l' + i - BT.nleaves l')) = _
        rw [if_neg (by omega), show BT.nleaves l' + i - BT.nleaves l' = i by omega])]

/-- `build` writes the term's cells after the heap, its root last. -/
theorem build_len : ∀ (t : Term) (h : List Cell),
    (build h t).1.length = h.length + tsize t ∧ (build h t).2 + 1 = (build h t).1.length
  | .S, h => by simp [build, alloc, tsize]
  | .K, h => by simp [build, alloc, tsize]
  | .I, h => by simp [build, alloc, tsize]
  | .app f a, h => by
    have h1 := build_len f h
    have h2 := build_len a (build h f).1
    show (alloc (build (build h f).1 a).1 (.app (build h f).2 (build (build h f).1 a).2)).1.length = _ ∧
      (alloc (build (build h f).1 a).1 (.app (build h f).2 (build (build h f).1 a).2)).2 + 1 =
      (alloc (build (build h f).1 a).1 (.app (build h f).2 (build (build h f).1 a).2)).1.length
    simp only [alloc, List.length_append, List.length_singleton]
    refine ⟨?_, by first | rfl | trivial⟩
    rw [h2.1, h1.1]
    simp only [tsize]
    omega

/-- `build` keeps a heap well formed: each cell points below itself. -/
theorem build_wf : ∀ (t : Term) (h : List Cell), WF h → WF (build h t).1
  | .S, h, hw => by
    intro i c hc
    simp only [build, alloc] at hc
    rcases Nat.lt_or_ge i h.length with hi | hi
    · rw [List.getElem?_append_left hi] at hc; exact hw i c hc
    · rw [List.getElem?_append_right hi] at hc
      cases hj : i - h.length with
      | zero => rw [hj] at hc; cases hc; rfl
      | succ _ => rw [hj] at hc; simp at hc
  | .K, h, hw => by
    intro i c hc
    simp only [build, alloc] at hc
    rcases Nat.lt_or_ge i h.length with hi | hi
    · rw [List.getElem?_append_left hi] at hc; exact hw i c hc
    · rw [List.getElem?_append_right hi] at hc
      cases hj : i - h.length with
      | zero => rw [hj] at hc; cases hc; rfl
      | succ _ => rw [hj] at hc; simp at hc
  | .I, h, hw => by
    intro i c hc
    simp only [build, alloc] at hc
    rcases Nat.lt_or_ge i h.length with hi | hi
    · rw [List.getElem?_append_left hi] at hc; exact hw i c hc
    · rw [List.getElem?_append_right hi] at hc
      cases hj : i - h.length with
      | zero => rw [hj] at hc; cases hc; rfl
      | succ _ => rw [hj] at hc; simp at hc
  | .app f a, h, hw => by
    have w1 := build_wf f h hw
    have w2 := build_wf a (build h f).1 w1
    have l1 := build_len f h
    have l2 := build_len a (build h f).1
    obtain ⟨cs, e2, _⟩ := build_spec a (build h f).1
    intro i c hc
    change (alloc (build (build h f).1 a).1 (.app (build h f).2 (build (build h f).1 a).2)).1[i]? = some c at hc
    simp only [alloc] at hc
    rcases Nat.lt_or_ge i (build (build h f).1 a).1.length with hi | hi
    · rw [List.getElem?_append_left hi] at hc; exact w2 i c hc
    · rw [List.getElem?_append_right hi] at hc
      cases hj : i - (build (build h f).1 a).1.length with
      | zero =>
        rw [hj] at hc
        cases hc
        have hi' : i = (build (build h f).1 a).1.length := by omega
        subst hi'
        show (decide ((build h f).2 < _) && decide ((build (build h f).1 a).2 < _)) = true
        have hl : (build h f).1.length ≤ (build (build h f).1 a).1.length := by rw [e2]; simp
        rw [decide_eq_true (by omega), decide_eq_true (by omega)]
        rfl
      | succ _ => rw [hj] at hc; simp at hc

/-- **The region `regionOf'` builds holds the witness**: it has the
    statement's `W` cells, is well formed after the bits' slots, and reads
    back `w` behind any bits. -/
theorem regionOf'_spec {N W : Nat} {w : Term} {region : List Cell} (h : ComposedText.regionOf' N W w = some region) :
    region.length = W ∧ (∀ i c, region[i]? = some c → cellOK (N + 3 + i) c = true) ∧
      ∀ ρ, cWitness ρ N region = some w := by
  unfold ComposedText.regionOf' at h
  dsimp only at h
  split at h
  · rename_i hn
    cases h
    let pre := List.replicate (N + 3) Cell.S ++ List.replicate (W - ((build (List.replicate (N + 3) Cell.S) w).1.length - (N + 3))) Cell.S
    have hl0 := (build_len w (List.replicate (N + 3) Cell.S)).1
    simp only [List.length_replicate] at hl0
    obtain ⟨cs, e, _, _⟩ := build_spec w pre
    have hlb := build_len w pre
    have hpre : pre.length = N + 3 + (W - tsize w) := by
      simp only [pre, List.length_append, List.length_replicate]; rw [hl0]; omega
    have hsz : tsize w ≤ W := by rw [hl0] at hn; omega
    have hdrop : (build pre w).1.drop (N + 3) =
        List.replicate (W - tsize w) Cell.S ++ cs := by
      rw [e]
      simp only [pre, hl0, show N + 3 + tsize w - (N + 3) = tsize w by omega, List.append_assoc]
      simp
    show ((build pre w).1.drop (N + 3)).length = W ∧
      (∀ i c, ((build pre w).1.drop (N + 3))[i]? = some c → cellOK (N + 3 + i) c = true) ∧
      ∀ ρ, cWitness ρ N ((build pre w).1.drop (N + 3)) = some w
    refine ⟨?_, ?_, ?_⟩
    · rw [hdrop, List.length_append, List.length_replicate]
      have := hlb.1
      rw [e, List.length_append, hpre] at this
      omega
    · intro i c hc
      have hwf : WF (build pre w).1 := build_wf w pre (by
        intro j c hc
        simp only [pre, List.getElem?_append, List.getElem?_replicate] at hc
        split at hc <;> (split at hc <;> cases hc <;> rfl))
      have : (build pre w).1[N + 3 + i]? = some c := by
        rw [← List.getElem?_drop]; exact hc
      exact hwf _ c this
    · intro ρ
      rw [hdrop]
      unfold cWitness witnessOf
      have hsl : (slotHeap ρ N ++ List.replicate (W - tsize w) Cell.S).length = pre.length := by
        rw [List.length_append, slotHeap_length, List.length_replicate, hpre]
      obtain ⟨cs', p, eb, eb'⟩ := build_shape w _ _ hsl
      have hcs : cs' = cs := by
        have h1 := congrArg Prod.fst eb'
        simp only at h1
        rw [e] at h1
        exact (List.append_cancel_left h1).symm
      subst hcs
      obtain ⟨_, _, _, hterm⟩ := build_spec w (slotHeap ρ N ++ List.replicate (W - tsize w) Cell.S)
      have hroot := (build_len w (slotHeap ρ N ++ List.replicate (W - tsize w) Cell.S)).2
      rw [eb] at hterm hroot
      dsimp only at hterm hroot
      rw [← List.append_assoc, ← hroot, show p + 1 - 1 = p by omega]
      exact hterm
  · cases h

-- ---------------------------------------------------------------------------
-- From a realizer to a proof
-- ---------------------------------------------------------------------------

/-- **An accepted witness within the budget has a run**: accepted bits `β`
    and witness `w`, with the bits read off `β` and the region `regionOf'`
    builds of `w`, at region size `W`, give a run in `CRel` when the
    composed machine's run fits the statement's heights (`CBudget`). -/
theorem accepted_run (M : MF) (W R Lm : Nat) (hR : R ≤ 20) (hLm : Lm ≤ 20)
    (hNW : BT.nleaves (clear M) + W ≤ 2 ^ 8) :
    ∀ β w, Accepts M β w →
      ∀ region, ComposedText.regionOf' (BT.nleaves (clear M)) W w = some region →
        CBudget ⟨clear M, stmtOf M, W, R, Lm⟩ (leafAt β) region →
        ∃ run : CRun', CRel ⟨clear M, stmtOf M, W, R, Lm⟩ run ∧ run.ρ = leafAt β ∧ run.region = region := by
  intro β w hacc region hreg hB
  have hsame := same_of_shape M β hacc.1
  have hfill : fillB (clear M) (leafAt β) 0 = β :=
    fillB_leafAt _ _ hsame _ 0 (fun i _ => by rw [Nat.zero_add])
  have hev : EvalRel (stmtOf M, SameShape (clear M)) (fillB (clear M) (leafAt β) 0) w := by
    rw [hfill]; exact ⟨hsame, hacc.2⟩
  obtain ⟨hrl, hrok, hw⟩ := regionOf'_spec hreg
  obtain ⟨A, e, row, hc⟩ := crel_of_eval ⟨clear M, stmtOf M, W, R, Lm⟩ hR hLm hNW hrl hrok (hw _) hev
    (stmtOf_pos M) hB
  exact ⟨_, hc, rfl, rfl⟩

/-- **Every realizer has a run, within the budget**: a realizer of the
    formula has accepted bits `β` and a witness `w` (`accepted_of_real`);
    with the bits read off `β` and the region `regionOf'` builds of `w`, at
    region size `W`, the composed machine's run, when it fits the
    statement's heights (`CBudget`), is in `CRel`. -/
theorem realizer_run (M : MF) (W R Lm : Nat) (hR : R ≤ 20) (hLm : Lm ≤ 20)
    (hNW : BT.nleaves (clear M) + W ≤ 2 ^ 8) :
    ∀ r, Real M.toForm r → ∃ β w, Accepts M β w ∧
      ∀ region, ComposedText.regionOf' (BT.nleaves (clear M)) W w = some region →
        CBudget ⟨clear M, stmtOf M, W, R, Lm⟩ (leafAt β) region →
        ∃ run : CRun', CRel ⟨clear M, stmtOf M, W, R, Lm⟩ run ∧ run.ρ = leafAt β ∧ run.region = region := by
  intro r hr
  obtain ⟨β, w, hacc⟩ := accepted_of_real hr
  exact ⟨β, w, hacc, accepted_run M W R Lm hR hLm hNW β w hacc⟩

/-- **The composed circuit's completeness from an accepted witness**: for
    accepted bits and witness whose run fits the budget, the run is in
    `CRel` and the prover proves it: its proofs verify (the assumed
    completeness), it aborts on at most `err` draws, and its proofs are
    within `err` of the simulator's. -/
theorem composeC_accepted {PV : Type} (off : EF → String → EF) (NR ε : Nat) (hNR : 0 < NR)
    (pcs : CStmt → CRun' → (Nat → Tup) → EF → EF → Nat → PV) (psim : CStmt → EF → EF → List EF → Nat → PV)
    (hpcs : ∀ s w, CRel s w → PCSCloseN off NR (ctv s w) (pcs s w) (psim s) ε)
    (verify : CStmt → PV × EF × EF × List EF × (EF × EF) → Prop)
    (ext : CStmt → PV × EF × EF × List EF × (EF × EF) → CRun')
    (complete : ∀ s w, CRel s w → ∀ (d : EF × EF × Nat × (Nat → Tup)) π,
      realVN off (ctabs s w) (ctv s w) (cpb s) (pcs s w) d.1 d.2.1 d.2.2.1 d.2.2.2 = some π → verify s π)
    (knowledge : ∀ s π, verify s π → CRel s (ext s π))
    (M : MF) (W R Lm : Nat) (hR : R ≤ 20) (hLm : Lm ≤ 20) (hNW : BT.nleaves (clear M) + W ≤ 2 ^ 8) :
    let ps := compPSD off NR ε hNR pcs psim hpcs verify ext complete knowledge
    let s : CStmt := ⟨clear M, stmtOf M, W, R, Lm⟩
    ∀ β w, Accepts M β w →
      ∀ region, ComposedText.regionOf' (BT.nleaves (clear M)) W w = some region →
        CBudget s (leafAt β) region → ∃ run : CRun', CRel s run ∧ run.ρ = leafAt β ∧ run.region = region ∧
          (∀ d π, ps.prove s run d = some π → ps.verify s π) ∧
          cnt ps.draws (ps.prove s run) (fun o => o.isNone) ≤ ps.err s ∧
          CloseD ps.draws (ps.err s) (ps.prove s run) (ps.sim s) := by
  intro ps s β w hacc region hreg hB
  obtain ⟨run, hc, hρ, hreg'⟩ := accepted_run M W R Lm hR hLm hNW β w hacc region hreg hB
  exact ⟨run, hc, hρ, hreg', ps.complete s run hc, ps.aborts_le hc, ps.zk s run hc⟩

/-- **The composed circuit's completeness from a realizer** (`composeD`'s
    first clause, for the circuit): every realizer of the formula has
    accepted bits and a witness whose run, within the budget, the prover
    proves: its proofs verify (the assumed completeness), it aborts on at
    most `err` draws, and its proofs are within `err` of the simulator's. -/
theorem composeC_realizer {PV : Type} (off : EF → String → EF) (NR ε : Nat) (hNR : 0 < NR)
    (pcs : CStmt → CRun' → (Nat → Tup) → EF → EF → Nat → PV) (psim : CStmt → EF → EF → List EF → Nat → PV)
    (hpcs : ∀ s w, CRel s w → PCSCloseN off NR (ctv s w) (pcs s w) (psim s) ε)
    (verify : CStmt → PV × EF × EF × List EF × (EF × EF) → Prop)
    (ext : CStmt → PV × EF × EF × List EF × (EF × EF) → CRun')
    (complete : ∀ s w, CRel s w → ∀ (d : EF × EF × Nat × (Nat → Tup)) π,
      realVN off (ctabs s w) (ctv s w) (cpb s) (pcs s w) d.1 d.2.1 d.2.2.1 d.2.2.2 = some π → verify s π)
    (knowledge : ∀ s π, verify s π → CRel s (ext s π))
    (M : MF) (W R Lm : Nat) (hR : R ≤ 20) (hLm : Lm ≤ 20) (hNW : BT.nleaves (clear M) + W ≤ 2 ^ 8) :
    let ps := compPSD off NR ε hNR pcs psim hpcs verify ext complete knowledge
    let s : CStmt := ⟨clear M, stmtOf M, W, R, Lm⟩
    ∀ r, Real M.toForm r → ∃ β w, Accepts M β w ∧
      ∀ region, ComposedText.regionOf' (BT.nleaves (clear M)) W w = some region →
        CBudget s (leafAt β) region → ∃ run : CRun', CRel s run ∧ run.ρ = leafAt β ∧ run.region = region ∧
          (∀ d π, ps.prove s run d = some π → ps.verify s π) ∧
          cnt ps.draws (ps.prove s run) (fun o => o.isNone) ≤ ps.err s ∧
          CloseD ps.draws (ps.err s) (ps.prove s run) (ps.sim s) := by
  intro ps s r hr
  obtain ⟨β, w, hacc, hrun⟩ := realizer_run M W R Lm hR hLm hNW r hr
  refine ⟨β, w, hacc, fun region hreg hB => ?_⟩
  obtain ⟨run, hc, hρ, hreg'⟩ := hrun region hreg hB
  exact ⟨run, hc, hρ, hreg', ps.complete s run hc, ps.aborts_le hc, ps.zk s run hc⟩

end Circuit
