/-!
# A read-write memory argument

L2's heap is write-once, so its memory argument checks only that each read
was written (`Ski/Heap.lean`).  Graph reduction overwrites cells
(`Ski/Graph.lean`), and a read must return the *last* write.  This file
proves the generic timestamped multiset check of offline memory checking
(Blum, Evans, Gemmell, Kannan and Naor, 1991) sound and complete for a
trace of accesses, each one read and one write.  Instantiating it on
`gstep`'s accesses (several reads, up to three writes, and a write-back
for each read without a write) is not done here.

Realised in a circuit, the check needs more than this file states: times
below the field's characteristic (`n < p`), a range check for `rt j ≤ j`,
counts below `p` if the balance is LogUp's (`n + nF < p`), the tuple
compression's collision term, and `f` and `M` fixed by the verifier.

**The check.**  Operation `j` accesses address `addr j`: it reads a tuple
`(addr j, rv j, rt j)` and writes `(addr j, wv j, j + 1)`, its time.
Memory starts with `(a, f a, 0)` at each `a < M`, and the prover ends it
with any tuples `fin`.  The verifier checks that
- every read's time is earlier than its operation's: `rt j ≤ j`;
- the multisets balance: `init ⊎ writes = reads ⊎ fin`, as counts of
  every tuple (`Balanced`).

**Soundness** (`rw_sound`): every read returns the value and time of the
last write to its address before it, or the initial value at time `0`.

The proof is by strong induction on the operation.  The tuples on the left
are distinct: initial tuples by address, writes by time, and the two kinds
by time.  So a read of a stale write `j` would leave that tuple read twice:
once here, and once by the first later access to the address, which by
induction read it correctly.  The right side would then count it twice.
-/

namespace RWMem

variable {V : Type} [DecidableEq V]

/-- One access: the address, the value and time read, the value written. -/
structure Op (V : Type) where
  addr : Nat
  rv : V
  rt : Nat
  wv : V

abbrev Tup (V : Type) := Nat × V × Nat

/-- How many `j < n` satisfy `p`. -/
def cnt (n : Nat) (p : Nat → Bool) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => cnt n p + (p n).toNat

section
variable (ops : Nat → Op V) (n M : Nat) (f : Nat → V) (nF : Nat) (fin : Nat → Tup V)

def initT (a : Nat) : Tup V := (a, f a, 0)
def wT (j : Nat) : Tup V := ((ops j).addr, (ops j).wv, j + 1)
def rT (j : Nat) : Tup V := ((ops j).addr, (ops j).rv, (ops j).rt)

/-- The multiset check, as counts: `init ⊎ writes = reads ⊎ fin`. -/
def Balanced : Prop := ∀ x : Tup V,
  cnt M (fun a => decide (initT f a = x)) + cnt n (fun j => decide (wT ops j = x)) =
    cnt n (fun j => decide (rT ops j = x)) + cnt nF (fun k => decide (fin k = x))

/-- Each read's time is before its operation's. -/
def TimesOK : Prop := ∀ j, j < n → (ops j).rt ≤ j

/-- The last operation before `i` that accessed `a`. -/
def lastW (a : Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 => if (ops i).addr = a then some i else lastW a i

/-- What a read of `a` before operation `i` should return: the last
    write's value and time, or the initial value at time `0`. -/
def expected (a i : Nat) : V × Nat :=
  match lastW ops a i with
  | some j => ((ops j).wv, j + 1)
  | none => (f a, 0)
end

-- ---------------------------------------------------------------------------
-- Counting
-- ---------------------------------------------------------------------------

theorem cnt_pos {p : Nat → Bool} : ∀ {n j : Nat}, j < n → p j = true → 1 ≤ cnt n p
  | n + 1, j, hj, hp => by
    show 1 ≤ cnt n p + _
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact Nat.le_trans (cnt_pos h hp) (Nat.le_add_right _ _)
    · rw [← h, hp]
      exact Nat.le_add_left _ _

theorem cnt_two {p : Nat → Bool} : ∀ {n j k : Nat}, j < n → k < n → j < k →
    p j = true → p k = true → 2 ≤ cnt n p
  | n + 1, j, k, hj, hk, hjk, pj, pk => by
    show 2 ≤ cnt n p + _
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · exact Nat.le_trans (cnt_two (Nat.lt_trans hjk h) h hjk pj pk) (Nat.le_add_right _ _)
    · rw [← h, pk]
      exact Nat.succ_le_succ (cnt_pos hjk pj)

theorem cnt_exists {p : Nat → Bool} : ∀ {n : Nat}, 1 ≤ cnt n p → ∃ j, j < n ∧ p j = true
  | 0, h => absurd h (Nat.not_succ_le_zero 0)
  | n + 1, h => by
    cases hp : p n with
    | true => exact ⟨n, Nat.lt_succ_self n, hp⟩
    | false =>
      have h' : 1 ≤ cnt n p := by
        have e : cnt (n + 1) p = cnt n p + 0 := by show cnt n p + _ = _; rw [hp]; rfl
        rw [e] at h
        exact h
      obtain ⟨j, hj, pj⟩ := cnt_exists h'
      exact ⟨j, Nat.lt_succ_of_lt hj, pj⟩

theorem cnt_zero {p : Nat → Bool} : ∀ {n : Nat}, (∀ j, j < n → p j = false) → cnt n p = 0
  | 0, _ => rfl
  | n + 1, h => by
    show cnt n p + _ = 0
    rw [h n (Nat.lt_succ_self n), cnt_zero (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    rfl

theorem cnt_le_one {p : Nat → Bool} : ∀ {n : Nat},
    (∀ j k, j < n → k < n → p j = true → p k = true → j = k) → cnt n p ≤ 1
  | 0, _ => Nat.zero_le _
  | n + 1, h => by
    show cnt n p + _ ≤ 1
    cases hp : p n with
    | false =>
      exact cnt_le_one (fun j k hj hk pj pk =>
        h j k (Nat.lt_succ_of_lt hj) (Nat.lt_succ_of_lt hk) pj pk)
    | true =>
      have z : cnt n p = 0 := cnt_zero fun j hj => by
        cases pj : p j with
        | false => rfl
        | true =>
          have e := h j n (Nat.lt_succ_of_lt hj) (Nat.lt_succ_self n) pj hp
          exact absurd e (Nat.ne_of_lt hj)
      rw [z]
      exact Nat.le_refl 1

/-- Either `p` fails up to `m`, or there is a least `k ≤ m` where it holds. -/
theorem least_or_none (p : Nat → Bool) : ∀ m : Nat,
    (∀ k, k ≤ m → p k = false) ∨ ∃ k, k ≤ m ∧ p k = true ∧ ∀ k', k' < k → p k' = false
  | 0 => by
    cases h : p 0 with
    | false => exact .inl fun k hk => by rw [Nat.le_zero.1 hk]; exact h
    | true => exact .inr ⟨0, Nat.le_refl 0, h, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | m + 1 => by
    rcases least_or_none p m with h | ⟨k, hk, pk, hmin⟩
    · cases hp : p (m + 1) with
      | false =>
        exact .inl fun k hk => by
          rcases Nat.lt_or_eq_of_le hk with h' | h'
          · exact h k (Nat.le_of_lt_succ h')
          · rw [h']; exact hp
      | true => exact .inr ⟨m + 1, Nat.le_refl _, hp, fun k' hk' => h k' (Nat.le_of_lt_succ hk')⟩
    · exact .inr ⟨k, Nat.le_succ_of_le hk, pk, hmin⟩

theorem least {p : Nat → Bool} {m : Nat} (h : p m = true) :
    ∃ k, k ≤ m ∧ p k = true ∧ ∀ k', k' < k → p k' = false := by
  rcases least_or_none p m with h' | h'
  · rw [h' m (Nat.le_refl m)] at h; cases h
  · exact h'

-- ---------------------------------------------------------------------------
-- The last access
-- ---------------------------------------------------------------------------

section
variable (ops : Nat → Op V)

omit [DecidableEq V] in
theorem lastW_some {a : Nat} : ∀ {i j : Nat}, lastW ops a i = some j →
    j < i ∧ (ops j).addr = a ∧ ∀ k, j < k → k < i → (ops k).addr ≠ a
  | i + 1, j, h => by
    unfold lastW at h
    by_cases e : (ops i).addr = a
    · rw [if_pos e] at h
      cases h
      exact ⟨Nat.lt_succ_self _, e, fun k hk hk' => absurd hk' (Nat.not_lt.2 hk)⟩
    · rw [if_neg e] at h
      obtain ⟨h1, h2, h3⟩ := lastW_some h
      refine ⟨Nat.lt_succ_of_lt h1, h2, fun k hk hk' => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk') with l | l
      · exact h3 k hk l
      · rw [l]; exact e

omit [DecidableEq V] in
theorem lastW_none {a : Nat} : ∀ {i : Nat}, lastW ops a i = none → ∀ k, k < i → (ops k).addr ≠ a
  | i + 1, h, k, hk => by
    unfold lastW at h
    by_cases e : (ops i).addr = a
    · rw [if_pos e] at h; cases h
    · rw [if_neg e] at h
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with l | l
      · exact lastW_none h k l
      · rw [l]; exact e

omit [DecidableEq V] in
theorem lastW_of {a j : Nat} (hja : (ops j).addr = a) : ∀ {i : Nat}, j < i →
    (∀ k, j < k → k < i → (ops k).addr ≠ a) → lastW ops a i = some j
  | i + 1, hj, h => by
    unfold lastW
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with l | l
    · rw [if_neg (h i l (Nat.lt_succ_self i))]
      exact lastW_of hja l fun k hk hk' => h k hk (Nat.lt_succ_of_lt hk')
    · rw [← l, if_pos hja]

omit [DecidableEq V] in
theorem lastW_none_of {a : Nat} : ∀ {i : Nat}, (∀ k, k < i → (ops k).addr ≠ a) → lastW ops a i = none
  | 0, _ => rfl
  | i + 1, h => by
    unfold lastW
    rw [if_neg (h i (Nat.lt_succ_self i))]
    exact lastW_none_of fun k hk => h k (Nat.lt_succ_of_lt hk)

end

-- ---------------------------------------------------------------------------
-- Soundness
-- ---------------------------------------------------------------------------

section
variable {ops : Nat → Op V} {n M : Nat} {f : Nat → V} {nF : Nat} {fin : Nat → Tup V}

/-- The left side holds each tuple at most once. -/
theorem left_le_one (x : Tup V) :
    cnt M (fun a => decide (initT f a = x)) + cnt n (fun j => decide (wT ops j = x)) ≤ 1 := by
  have hi : cnt M (fun a => decide (initT f a = x)) ≤ 1 :=
    cnt_le_one fun j k _ _ pj pk => by
      have e := (of_decide_eq_true pj).trans (of_decide_eq_true pk).symm
      exact congrArg Prod.fst e
  have hw : cnt n (fun j => decide (wT ops j = x)) ≤ 1 :=
    cnt_le_one fun j k _ _ pj pk => by
      have e := (of_decide_eq_true pj).trans (of_decide_eq_true pk).symm
      exact Nat.succ.inj (congrArg (fun t => t.2.2) e)
  rcases Nat.eq_zero_or_pos (cnt M (fun a => decide (initT f a = x))) with z | z
  · rw [z, Nat.zero_add]; exact hw
  · obtain ⟨a, _, pa⟩ := cnt_exists z
    have ea : initT f a = x := of_decide_eq_true pa
    have zw : cnt n (fun j => decide (wT ops j = x)) = 0 := cnt_zero fun j _ => by
      cases pj : decide (wT ops j = x) with
      | false => rfl
      | true =>
        have e := (of_decide_eq_true pj).trans ea.symm
        exact absurd (congrArg (fun t => t.2.2) e) (Nat.succ_ne_zero j)
    rw [zw]
    exact hi

/-- Two reads of one tuple unbalance the check. -/
theorem no_double (hb : Balanced ops n M f nF fin) {j k : Nat} (hj : j < n) (hk : k < n) (hjk : j < k)
    (e : rT ops j = rT ops k) : False := by
  have two : 2 ≤ cnt n (fun i => decide (rT ops i = rT ops k)) :=
    cnt_two hj hk hjk (decide_eq_true e) (decide_eq_true rfl)
  have := hb (rT ops k)
  have le := left_le_one (ops := ops) (n := n) (M := M) (f := f) (rT ops k)
  rw [this] at le
  exact absurd (Nat.le_trans two (Nat.le_trans (Nat.le_add_right _ _) le)) (by decide)

/-- One operation's read, given every earlier one's. -/
theorem rw_step (hb : Balanced ops n M f nF fin) (ht : TimesOK ops n) {i : Nat} (hn : i < n)
    (ih : ∀ k, k < i → ((ops k).rv, (ops k).rt) = expected ops f (ops k).addr k) :
    ((ops i).rv, (ops i).rt) = expected ops f (ops i).addr i := by
  have pos : 1 ≤ cnt n (fun j => decide (rT ops j = rT ops i)) := cnt_pos hn (decide_eq_true rfl)
  have lpos : 1 ≤ cnt M (fun a => decide (initT f a = rT ops i)) +
      cnt n (fun j => decide (wT ops j = rT ops i)) := by
    rw [hb (rT ops i)]
    exact Nat.le_trans pos (Nat.le_add_right _ _)
  -- an earlier access to the address that read the same value and time
  have stale : ∀ k, k < i → ((ops k).rv, (ops k).rt) = ((ops i).rv, (ops i).rt) →
      (ops k).addr = (ops i).addr → False := fun k hk e ea =>
    no_double hb (Nat.lt_trans hk hn) hn hk (by
      show ((ops k).addr, ((ops k).rv, (ops k).rt)) = ((ops i).addr, ((ops i).rv, (ops i).rt))
      rw [ea, e])
  rcases Nat.eq_zero_or_pos (cnt M (fun a => decide (initT f a = rT ops i))) with z | z
  · -- the tuple read was written by an operation `j`
    rw [z, Nat.zero_add] at lpos
    obtain ⟨j, _, pj⟩ := cnt_exists lpos
    have ej : wT ops j = rT ops i := of_decide_eq_true pj
    have ea : (ops j).addr = (ops i).addr := congrArg Prod.fst ej
    have ev : (ops j).wv = (ops i).rv := congrArg (fun t => t.2.1) ej
    have et : j + 1 = (ops i).rt := congrArg (fun t => t.2.2) ej
    have jle' : j + 1 ≤ i := by rw [et]; exact ht i hn
    have jlt : j < i := jle'
    cases hl : lastW ops (ops i).addr i with
    | none => exact absurd ea (lastW_none ops hl j jlt)
    | some js =>
      obtain ⟨hjs, ajs, nojs⟩ := lastW_some ops hl
      have jle : j ≤ js := Nat.not_lt.1 fun h => nojs j h jlt ea
      rcases Nat.lt_or_eq_of_le jle with l | l
      · -- a later write `js` exists: the first access after `j` read `j`'s tuple too
        obtain ⟨k, hk, pk, hmin⟩ := least (p := fun k => decide (j < k ∧ (ops k).addr = (ops i).addr))
          (m := js) (decide_eq_true ⟨l, ajs⟩)
        obtain ⟨jk, ak⟩ := of_decide_eq_true pk
        have klt : k < i := Nat.lt_of_le_of_lt hk hjs
        have lk : lastW ops (ops i).addr k = some j :=
          lastW_of ops ea jk fun k' h1 h2 hk' => of_decide_eq_false (hmin k' h2) ⟨h1, hk'⟩
        have rk := ih k klt
        simp only [expected, ak, lk] at rk
        exact (stale k klt (rk.trans (by rw [ev, et])) ak).elim
      · subst l
        simp only [expected, hl]
        rw [ev, et]
  · -- the tuple read is an initial one
    obtain ⟨a', _, pa⟩ := cnt_exists z
    have ea : initT f a' = rT ops i := of_decide_eq_true pa
    have e1 : a' = (ops i).addr := congrArg Prod.fst ea
    have ev : f a' = (ops i).rv := congrArg (fun t => t.2.1) ea
    have et : 0 = (ops i).rt := congrArg (fun t => t.2.2) ea
    cases hl : lastW ops (ops i).addr i with
    | none =>
      simp only [expected, hl]
      rw [← ev, ← et, e1]
    | some js =>
      -- the first access to the address read the initial tuple too
      obtain ⟨hjs, ajs, _⟩ := lastW_some ops hl
      obtain ⟨k, hk, pk, hmin⟩ := least (p := fun k => decide ((ops k).addr = (ops i).addr))
        (m := js) (decide_eq_true ajs)
      have ak : (ops k).addr = (ops i).addr := of_decide_eq_true pk
      have klt : k < i := Nat.lt_of_le_of_lt hk hjs
      have lk : lastW ops (ops i).addr k = none :=
        lastW_none_of ops fun k' h hk' => of_decide_eq_false (hmin k' h) hk'
      have rk := ih k klt
      simp only [expected, ak, lk] at rk
      exact (stale k klt (rk.trans (by rw [← ev, ← et, e1])) ak).elim

/-- **The read-write memory argument is sound.**  If the multisets balance
    and every read's time is before its operation's, every read returns the
    value and time of the last write to its address, or the initial value
    at time `0`. -/
theorem rw_sound (hb : Balanced ops n M f nF fin) (ht : TimesOK ops n) :
    ∀ i, i < n → ((ops i).rv, (ops i).rt) = expected ops f (ops i).addr i := by
  have all : ∀ B i, i ≤ B → i < n → ((ops i).rv, (ops i).rt) = expected ops f (ops i).addr i := by
    intro B
    induction B with
    | zero =>
      intro i hi hn
      exact rw_step hb ht hn fun k hk => absurd (Nat.lt_of_lt_of_le hk hi) (Nat.not_lt_zero _)
    | succ B ih =>
      intro i hi hn
      exact rw_step hb ht hn fun k hk =>
        ih k (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hk hi)) (Nat.lt_trans hk hn)
  exact fun i hn => all i i (Nat.le_refl i) hn

end

-- ---------------------------------------------------------------------------
-- Completeness: an honest run balances
-- ---------------------------------------------------------------------------

theorem cnt_congr {p q : Nat → Bool} : ∀ {M : Nat}, (∀ b, b < M → p b = q b) → cnt M p = cnt M q
  | 0, _ => rfl
  | M + 1, h => by
    show cnt M p + _ = cnt M q + _
    rw [cnt_congr (fun b hb => h b (Nat.lt_succ_of_lt hb)), h M (Nat.lt_succ_self M)]

/-- Overwriting one entry of a table of tuples moves one count. -/
theorem cnt_set {g g' : Nat → Tup V} {a : Nat} (x y : Tup V) (hy : g' a = y)
    (ho : ∀ b, b ≠ a → g' b = g b) : ∀ M, a < M →
    cnt M (fun b => decide (g' b = x)) + (decide (g a = x)).toNat =
      cnt M (fun b => decide (g b = x)) + (decide (y = x)).toNat
  | M + 1, ha => by
    show cnt M _ + _ + _ = cnt M _ + _ + _
    dsimp only
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ha) with l | l
    · have ih := cnt_set x y hy ho M l
      rw [ho M (Nat.ne_of_gt l)]
      exact (Nat.add_right_comm _ _ _).trans ((congrArg (· + _) ih).trans (Nat.add_right_comm _ _ _))
    · subst l
      rw [cnt_congr (fun b hb => by rw [ho b (Nat.ne_of_lt hb)]), hy]
      exact Nat.add_right_comm _ _ _

section
variable (ops : Nat → Op V) (f : Nat → V)

/-- The honest final tuple of address `a` after `n` operations. -/
def curT (n a : Nat) : Tup V := (a, expected ops f a n)
end

variable {ops : Nat → Op V} {f : Nat → V}

omit [DecidableEq V] in
theorem curT_succ (n a : Nat) :
    curT ops f (n + 1) a = if (ops n).addr = a then (a, (ops n).wv, n + 1) else curT ops f n a := by
  have hl : lastW ops a (n + 1) = if (ops n).addr = a then some n else lastW ops a n := rfl
  unfold curT expected
  rw [hl]
  by_cases e : (ops n).addr = a
  · rw [if_pos e, if_pos e]
  · rw [if_neg e, if_neg e]

theorem arith {Iw Wn w1 R r1 C1 Cn : Nat} (h1 : Iw + Wn = R + Cn) (h2 : C1 + r1 = Cn + w1) :
    Iw + (Wn + w1) = R + r1 + C1 := by
  omega

/-- **Completeness.**  An honest run, every read the last write, every
    address below `M`, with the honest final tuples, passes the check. -/
theorem rw_complete {n M : Nat} (ha : ∀ j, j < n → (ops j).addr < M)
    (hr : ∀ j, j < n → ((ops j).rv, (ops j).rt) = expected ops f (ops j).addr j) :
    Balanced ops n M f M (curT ops f n) ∧ TimesOK ops n := by
  refine ⟨?_, fun j hj => ?_⟩
  · intro x
    induction n with
    | zero =>
      show cnt M _ + 0 = 0 + cnt M _
      rw [Nat.add_zero, Nat.zero_add]
      rfl
    | succ n ih =>
      have ih := ih (fun j hj => ha j (Nat.lt_succ_of_lt hj)) (fun j hj => hr j (Nat.lt_succ_of_lt hj))
      have hs := cnt_set (g := curT ops f n) (g' := curT ops f (n + 1)) (a := (ops n).addr) x (wT ops n)
        (by rw [curT_succ, if_pos rfl]; rfl)
        (fun b hb => by rw [curT_succ, if_neg (Ne.symm hb)]) M (ha n (Nat.lt_succ_self n))
      have er : curT ops f n (ops n).addr = rT ops n := by
        show ((ops n).addr, expected ops f (ops n).addr n) = ((ops n).addr, ((ops n).rv, (ops n).rt))
        rw [hr n (Nat.lt_succ_self n)]
      rw [er] at hs
      show cnt M _ + (cnt n _ + _) = cnt n _ + _ + cnt M _
      exact arith ih hs
  · have e := hr j hj
    unfold expected at e
    cases hl : lastW ops (ops j).addr j with
    | none =>
      rw [hl] at e
      have e2 : (ops j).rt = 0 := congrArg Prod.snd e
      rw [e2]
      exact Nat.zero_le j
    | some i =>
      rw [hl] at e
      have e2 : (ops j).rt = i + 1 := congrArg Prod.snd e
      rw [e2]
      exact (lastW_some ops hl).1

end RWMem
