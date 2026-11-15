import Ski.Fan

open Term

/-!
# The converse: moduli for oracle functionals give the decidable fan theorem

`Fan.fanDelta_localO`: under the decidable fan theorem every oracle-total
functional has a modulus.  This module proves the converse, so the two are
equivalent over the base gate (`fanDelta_iff`).

**The functional.**  Given a decidable bar `B : List Bool → Bool`, code it as
the stream `βB B n := B (decode n)` and build the oracle functional `FB B`
that, on a stream `α`, scans `n = 0, 1, …`, looks up `B (α|n)` in the coded
stream, and at the first hit returns bit `n` of `α`:

    FB B α  =  α (h α),   h α the least n with B (α|n).

If `FB B` has a modulus `m` and some word `w` of length `m` has no barred
prefix, take `α` through `w`; its first hit `h α` is at or beyond `m`.  Flip
bit `h α`.  The first hit is unchanged, the output flips, and the first `m`
bits are unchanged: no modulus `m`.  So every word of length `m` has a barred
prefix, which is the decidable fan theorem.  (The textbook proof uses an
ℕ-valued functional and boundedness; the bit at the first hit keeps it
Bool-valued, so the paper's Bool-valued lift theory is the hypothesis.)

**The machinery.**
- `HeadO`: head reduction in the oracle calculus, as a relation; `HeadO.of_run`
  proves a trace by running `Fan.runO`, so the closed-combinator traces below
  are checked by evaluation.
- The index of the current prefix is a Church numeral `c` whose only use is to
  drop `enc w` cells from the coded stream: `IsIdx n c`.  `succC` and `dbl`
  update it; the index of `w ++ [b]` is `2·enc w + 1 + b` (`encStep`), which
  `decode` inverts.
- The loop is a self-applicative fixed point, `Xk k`, unrolling to `body`;
  `shape` is what head reduction of `body self c bs s` reaches.  The
  combinators were produced by bracket abstraction (Curry's rules and eta,
  as in `Ski/Abs.lean`) from

      body self c bs s = look c bs (hd s) (s (cont self c bs))
      look c bs        = hd (c tl bs)
      cont self c bs   = λ b s'. self (upd c b) bs s'
      upd c b          = b (succ (succ (dbl c))) (succ (dbl c))

- `loopSem` is the loop's meaning as a Lean function; `loop_run` says the
  loop computes it; `loopSem_spec` says it is the bit at the first hit.

Everything here uses only `propext` and `Quot.sound`.
-/

namespace FanReverse

open NoLift LiftBool Search CantorLift CantorTotal OracleFan Fan

-- ---------------------------------------------------------------------------
-- Head reduction as a relation
-- ---------------------------------------------------------------------------

/-- `u` is reached from `t` by head steps. -/
def HeadO (t u : TermO) : Prop := ∃ n, StepsNO n t u

theorem HeadO.refl (t : TermO) : HeadO t t := ⟨0, .refl t⟩

theorem HeadO.single {t u : TermO} (h : StepO t u) : HeadO t u := ⟨1, .step h (.refl u)⟩

theorem stepsNO_headO {n : Nat} {t u : TermO} (h : StepsNO n t u) {v : TermO} (h' : HeadO u v) :
    HeadO t v := by
  induction h with
  | refl => exact h'
  | step hs _ ih =>
    obtain ⟨m, hm⟩ := ih h'
    exact ⟨m + 1, .step hs hm⟩

theorem HeadO.trans {t u v : TermO} (h : HeadO t u) (h' : HeadO u v) : HeadO t v := by
  obtain ⟨n, hn⟩ := h
  exact stepsNO_headO hn h'

theorem stepsNO_left {n : Nat} {t u : TermO} (h : StepsNO n t u) (x : TermO) :
    StepsNO n (t ⬝ₚ x) (u ⬝ₚ x) := by
  induction h with
  | refl t => exact .refl _
  | step hs _ ih => exact .step (.left x hs) ih

theorem HeadO.left {t u : TermO} (h : HeadO t u) (x : TermO) : HeadO (t ⬝ₚ x) (u ⬝ₚ x) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, stepsNO_left hn x⟩

/-- A trace checked by evaluation. -/
theorem HeadO.of_run (n : Nat) {t u : TermO} (h : runO n t = u) : HeadO t u := by
  obtain ⟨k, _, hs⟩ := runO_steps n t
  exact ⟨k, h ▸ hs⟩

/-- Applying a term that reaches an oracle cell reads its first bit. -/
theorem HeadO.ora {t : TermO} {β : Nat → Bool} (h : HeadO t (.ora β)) (k : TermO) :
    HeadO (t ⬝ₚ k) (k ⬝ₚ emb (boolT (β 0)) ⬝ₚ .ora (shift β)) :=
  (h.left k).trans (.single (.ora β k))

-- ---------------------------------------------------------------------------
-- Shifted streams
-- ---------------------------------------------------------------------------

def shiftN : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, β => β
  | n + 1, β => shift (shiftN n β)

theorem shiftN_apply : ∀ (n : Nat) (β : Nat → Bool) (i : Nat), shiftN n β i = β (i + n)
  | 0, _, _ => rfl
  | n + 1, β, i => by
    show shiftN n β (i + 1) = β (i + (n + 1))
    rw [shiftN_apply n β (i + 1)]
    exact congrArg β (by omega)

theorem shiftN_shiftN (a b : Nat) (β : Nat → Bool) : shiftN a (shiftN b β) = shiftN (a + b) β := by
  funext i
  rw [shiftN_apply, shiftN_apply, shiftN_apply]
  exact congrArg β (by omega)

-- ---------------------------------------------------------------------------
-- The combinators
-- ---------------------------------------------------------------------------

/-- `tl = λ s. s (K I)`. -/
def tlO : TermO := .S ⬝ₚ .I ⬝ₚ (.K ⬝ₚ (.K ⬝ₚ .I))
/-- `hd = λ s. s K`. -/
def hdO : TermO := .S ⬝ₚ .I ⬝ₚ (.K ⬝ₚ .K)
/-- Church successor, `λ c f x. f (c f x)`. -/
def succC : TermO := .S ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S) ⬝ₚ .K)
/-- Church doubling, `λ c f. c (f ∘ f)`. -/
def dbl : TermO :=
  .S ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S) ⬝ₚ .K) ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S) ⬝ₚ .K) ⬝ₚ .I))
/-- `look = λ c bs. hd (c tl bs)`. -/
def look : TermO :=
  .S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ hdO))) ⬝ₚ (.S ⬝ₚ .I ⬝ₚ (.K ⬝ₚ tlO))
/-- `upd = λ c b. b (succ (succ (dbl c))) (succ (dbl c))`. -/
def upd : TermO :=
  .S ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ .I)) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .K) ⬝ₚ
    (.S ⬝ₚ (.K ⬝ₚ succC) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ succC) ⬝ₚ dbl))))) ⬝ₚ
  (.S ⬝ₚ (.K ⬝ₚ .K) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ succC) ⬝ₚ dbl))
/-- `cont = λ self c bs b s'. self (upd c b) bs s'`. -/
def cont : TermO :=
  .S ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S))) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .K))) ⬝ₚ
    (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S))) ⬝ₚ (.S ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .K) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S) ⬝ₚ .K))) ⬝ₚ
    (.K ⬝ₚ upd)))))) ⬝ₚ (.K ⬝ₚ (.K ⬝ₚ .K))
/-- `body = λ self c bs s. look c bs (hd s) (s (cont self c bs))`. -/
def body : TermO :=
  .S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S))) ⬝ₚ
    (.S ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .S))) ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .K))) ⬝ₚ look))) ⬝ₚ
    (.K ⬝ₚ (.K ⬝ₚ hdO))))))) ⬝ₚ
  (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ .I)))))) ⬝ₚ
    (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .K))))) ⬝ₚ cont))
/-- `M = λ m. body (m m)`; the loop is `M M`, unrolled as `Xk`. -/
def M : TermO := .S ⬝ₚ (.K ⬝ₚ body) ⬝ₚ (.S ⬝ₚ .I ⬝ₚ .I)

def iterI : Nat → TermO → TermO
  | 0, t => t
  | k + 1, t => .I ⬝ₚ iterI k t

/-- The loop, after `k` unrollings: `S I I (I^k M)`. -/
def Xk (k : Nat) : TermO := .S ⬝ₚ .I ⬝ₚ .I ⬝ₚ iterI k M

-- What head reduction of `body self c bs s` reaches, in three parts.
def lookPart (c bs : TermO) : TermO :=
  c ⬝ₚ (.K ⬝ₚ tlO ⬝ₚ c) ⬝ₚ bs ⬝ₚ (.K ⬝ₚ .K ⬝ₚ (.S ⬝ₚ .I ⬝ₚ (.K ⬝ₚ tlO) ⬝ₚ c ⬝ₚ bs))
def hdPart (c bs s : TermO) : TermO := .K ⬝ₚ (.K ⬝ₚ hdO) ⬝ₚ c ⬝ₚ bs ⬝ₚ s
def W : TermO :=
  .S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ .I)))))) ⬝ₚ
    (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .K))))) ⬝ₚ cont)
def wPart (self c bs s : TermO) : TermO := W ⬝ₚ self ⬝ₚ c ⬝ₚ bs ⬝ₚ s
def shape (self c bs s : TermO) : TermO := lookPart c bs ⬝ₚ hdPart c bs s ⬝ₚ wPart self c bs s

-- ---------------------------------------------------------------------------
-- Traces, by evaluation
-- ---------------------------------------------------------------------------

theorem M_unroll (x c bs s : TermO) :
    HeadO (M ⬝ₚ x ⬝ₚ c ⬝ₚ bs ⬝ₚ s) (shape (.S ⬝ₚ .I ⬝ₚ .I ⬝ₚ x) c bs s) :=
  HeadO.of_run 35 rfl

theorem iterI_head : ∀ (k : Nat) (t x : TermO), HeadO (iterI k t ⬝ₚ x) (t ⬝ₚ x)
  | 0, _, _ => HeadO.refl _
  | k + 1, t, x => (HeadO.single (.left x (.I _))).trans (iterI_head k t x)

theorem Xk_unroll (k : Nat) (c bs s : TermO) :
    HeadO (Xk k ⬝ₚ c ⬝ₚ bs ⬝ₚ s) (shape (Xk (k + 1)) c bs s) := by
  have h1 : HeadO (Xk k ⬝ₚ c ⬝ₚ bs ⬝ₚ s)
      (iterI k M ⬝ₚ (.I ⬝ₚ iterI k M) ⬝ₚ c ⬝ₚ bs ⬝ₚ s) := HeadO.of_run 2 rfl
  have h2 := (((iterI_head k M (.I ⬝ₚ iterI k M)).left c).left bs).left s
  exact h1.trans (h2.trans (M_unroll _ c bs s))

-- ---------------------------------------------------------------------------
-- Tails, heads, and Church indices
-- ---------------------------------------------------------------------------

/-- `f` drops `k` cells from any term that reaches an oracle cell. -/
def Shifts (k : Nat) (f : TermO) : Prop :=
  ∀ t β, HeadO t (.ora β) → HeadO (f ⬝ₚ t) (.ora (shiftN k β))

/-- `c` is an index `n`: it iterates any `k`-dropper `n` times. -/
def IsIdx (n : Nat) (c : TermO) : Prop :=
  ∀ k f, Shifts k f → ∀ t β, HeadO t (.ora β) → HeadO (c ⬝ₚ f ⬝ₚ t) (.ora (shiftN (n * k) β))

theorem shifts_tl : Shifts 1 tlO := by
  intro t β h
  have h1 : HeadO (tlO ⬝ₚ t) (t ⬝ₚ (.K ⬝ₚ (.K ⬝ₚ .I) ⬝ₚ t)) := HeadO.of_run 2 rfl
  exact h1.trans ((h.ora _).trans (HeadO.of_run 3 rfl))

theorem shifts_Ktl (c : TermO) : Shifts 1 (.K ⬝ₚ tlO ⬝ₚ c) := by
  intro t β h
  exact (HeadO.of_run 1 rfl).trans (shifts_tl t β h)

/-- The doubled dropper that `dbl` builds. -/
theorem shifts_double {k : Nat} {f : TermO} (hf : Shifts k f) (c : TermO) :
    Shifts (k + k) (.K ⬝ₚ (succC ⬝ₚ .I) ⬝ₚ c ⬝ₚ f) := by
  intro t β h
  have h1 : HeadO (.K ⬝ₚ (succC ⬝ₚ .I) ⬝ₚ c ⬝ₚ f ⬝ₚ t) (f ⬝ₚ (.I ⬝ₚ f ⬝ₚ t)) := HeadO.of_run 6 rfl
  have h2 : HeadO (.I ⬝ₚ f ⬝ₚ t) (.ora (shiftN k β)) :=
    (HeadO.single (.left t (.I f))).trans (hf t β h)
  have h3 := hf _ _ h2
  rw [shiftN_shiftN] at h3
  exact h1.trans h3

theorem isIdx_c0 : IsIdx 0 (.K ⬝ₚ .I) := by
  intro k f _ t β h
  rw [Nat.zero_mul]
  exact (HeadO.of_run 2 rfl).trans h

theorem isIdx_headO {n : Nat} {c c' : TermO} (h : HeadO c c') (hc : IsIdx n c') : IsIdx n c :=
  fun k f hf t β ht => ((h.left f).left t).trans (hc k f hf t β ht)

theorem isIdx_succ {n : Nat} {c : TermO} (hc : IsIdx n c) : IsIdx (n + 1) (succC ⬝ₚ c) := by
  intro k f hf t β ht
  have h1 : HeadO (succC ⬝ₚ c ⬝ₚ f ⬝ₚ t) (f ⬝ₚ (c ⬝ₚ f ⬝ₚ t)) := HeadO.of_run 5 rfl
  have h2 := hf _ _ (hc k f hf t β ht)
  rw [shiftN_shiftN] at h2
  have e : k + n * k = (n + 1) * k := by rw [Nat.succ_mul, Nat.add_comm]
  rw [e] at h2
  exact h1.trans h2

theorem isIdx_dbl {n : Nat} {c : TermO} (hc : IsIdx n c) : IsIdx (n + n) (dbl ⬝ₚ c) := by
  intro k f hf t β ht
  have h1 : HeadO (dbl ⬝ₚ c ⬝ₚ f ⬝ₚ t) (c ⬝ₚ (.K ⬝ₚ (succC ⬝ₚ .I) ⬝ₚ c ⬝ₚ f) ⬝ₚ t) := HeadO.of_run 5 rfl
  have h2 := hc (k + k) _ (shifts_double hf c) t β ht
  have e : n * (k + k) = (n + n) * k := by rw [Nat.mul_add, Nat.add_mul]
  rw [e] at h2
  exact h1.trans h2

/-- The index of `w ++ [b]` from the index of `w`. -/
def encStep (k : Nat) : Bool → Nat
  | true => k + k + 1 + 1
  | false => k + k + 1

theorem isIdx_upd {n : Nat} {c : TermO} (hc : IsIdx n c) (b : Bool) (self : TermO) :
    IsIdx (encStep n b) (.K ⬝ₚ upd ⬝ₚ self ⬝ₚ c ⬝ₚ emb (boolT b)) := by
  cases b with
  | true =>
    have h1 : HeadO (.K ⬝ₚ upd ⬝ₚ self ⬝ₚ c ⬝ₚ emb (boolT true))
        (succC ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ succC) ⬝ₚ dbl ⬝ₚ c)) := HeadO.of_run 15 rfl
    have h2 : HeadO (.S ⬝ₚ (.K ⬝ₚ succC) ⬝ₚ dbl ⬝ₚ c) (succC ⬝ₚ (dbl ⬝ₚ c)) := HeadO.of_run 2 rfl
    exact isIdx_headO h1 (isIdx_succ (isIdx_headO h2 (isIdx_succ (isIdx_dbl hc))))
  | false =>
    have h1 : HeadO (.K ⬝ₚ upd ⬝ₚ self ⬝ₚ c ⬝ₚ emb (boolT false))
        (succC ⬝ₚ (dbl ⬝ₚ c)) := HeadO.of_run 16 rfl
    exact isIdx_headO h1 (isIdx_succ (isIdx_dbl hc))

-- ---------------------------------------------------------------------------
-- The three parts of the body
-- ---------------------------------------------------------------------------

/-- `look c bs` reads bit `n` of the coded stream when `c` is index `n`. -/
theorem look_spec {n : Nat} {c bs : TermO} {β : Nat → Bool} (hc : IsIdx n c)
    (hbs : HeadO bs (.ora β)) (x y : TermO) :
    HeadO (lookPart c bs ⬝ₚ x ⬝ₚ y) (emb (boolT (β n)) ⬝ₚ x ⬝ₚ y) := by
  have h1 := hc 1 _ (shifts_Ktl c) bs β hbs
  have h2 := (h1.ora (.K ⬝ₚ .K ⬝ₚ (.S ⬝ₚ .I ⬝ₚ (.K ⬝ₚ tlO) ⬝ₚ c ⬝ₚ bs))).trans (HeadO.of_run 2 rfl)
  have e : shiftN (n * 1) β 0 = β n := by rw [shiftN_apply]; simp
  rw [e] at h2
  exact (h2.left x).left y

/-- `hd s` reads the first bit of the stream. -/
theorem hd_spec {c bs s : TermO} {α : Nat → Bool} (hs : HeadO s (.ora α)) :
    HeadO (hdPart c bs s) (emb (boolT (α 0))) := by
  have h1 : HeadO (hdPart c bs s) (s ⬝ₚ (.K ⬝ₚ .K ⬝ₚ s)) := HeadO.of_run 4 rfl
  exact h1.trans ((hs.ora _).trans (HeadO.of_run 2 rfl))

/-- The continuation: read a bit, update the index, recurse. -/
theorem w_spec {self c bs s : TermO} {α : Nat → Bool} (hs : HeadO s (.ora α)) :
    HeadO (wPart self c bs s)
      (self ⬝ₚ (.K ⬝ₚ upd ⬝ₚ self ⬝ₚ c ⬝ₚ emb (boolT (α 0))) ⬝ₚ
        (.K ⬝ₚ (.K ⬝ₚ .K) ⬝ₚ self ⬝ₚ c ⬝ₚ bs ⬝ₚ emb (boolT (α 0))) ⬝ₚ .ora (shift α)) := by
  have h1 : HeadO (wPart self c bs s)
      (s ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ (.S ⬝ₚ (.K ⬝ₚ .K))))) ⬝ₚ cont ⬝ₚ self ⬝ₚ c ⬝ₚ bs ⬝ₚ s)) :=
    HeadO.of_run 8 rfl
  exact h1.trans ((hs.ora _).trans (HeadO.of_run 37 rfl))

theorem bs_spec {bs : TermO} {β : Nat → Bool} (h : HeadO bs (.ora β)) (self c b : TermO) :
    HeadO (.K ⬝ₚ (.K ⬝ₚ .K) ⬝ₚ self ⬝ₚ c ⬝ₚ bs ⬝ₚ b) (.ora β) :=
  (HeadO.of_run 3 rfl).trans h

-- ---------------------------------------------------------------------------
-- Coding the bar as a stream
-- ---------------------------------------------------------------------------

def enc (w : List Bool) : Nat := w.foldl encStep 0

theorem enc_append (w : List Bool) (b : Bool) : enc (w ++ [b]) = encStep (enc w) b := by
  simp [enc, List.foldl_append]

def decode : Nat → List Bool
  | 0 => []
  | n + 1 => decode (n / 2) ++ [n % 2 == 1]
termination_by n => n
decreasing_by all_goals simp_wf; omega

theorem decode_encStep (k : Nat) : ∀ b, decode (encStep k b) = decode k ++ [b]
  | true => by
    show decode ((k + k + 1) + 1) = decode k ++ [true]
    rw [decode]
    have h1 : (k + k + 1) / 2 = k := by omega
    have h2 : (k + k + 1) % 2 = 1 := by omega
    rw [h1, h2]; rfl
  | false => by
    show decode ((k + k) + 1) = decode k ++ [false]
    rw [decode]
    have h1 : (k + k) / 2 = k := by omega
    have h2 : (k + k) % 2 = 0 := by omega
    rw [h1, h2]; rfl

theorem decode_foldl : ∀ (w : List Bool) (k : Nat), decode (w.foldl encStep k) = decode k ++ w
  | [], _ => by simp
  | b :: w, k => by
    rw [List.foldl_cons, decode_foldl w, decode_encStep, List.append_assoc]; rfl

theorem decode_enc (w : List Bool) : decode (enc w) = w := by
  have := decode_foldl w 0
  rw [decode] at this
  simpa [enc] using this

/-- The bar, coded as a stream. -/
def βB (B : List Bool → Bool) : Nat → Bool := fun n => B (decode n)

theorem βB_enc (B : List Bool → Bool) (w : List Bool) : βB B (enc w) = B w := by
  simp [βB, decode_enc]

-- ---------------------------------------------------------------------------
-- The loop and its meaning
-- ---------------------------------------------------------------------------

/-- What the loop computes, with fuel `n`: at the first barred prefix, the
    next bit of the stream. -/
def loopSem (B : List Bool → Bool) : Nat → List Bool → (Nat → Bool) → Bool
  | 0, _, α => α 0
  | n + 1, w, α => if B w then α 0 else loopSem B n (w ++ [α 0]) (shift α)

theorem append_pre_succ (w : List Bool) (α : Nat → Bool) (n : Nat) :
    (w ++ [α 0]) ++ pre (shift α) n = w ++ pre α (n + 1) := by
  rw [List.append_assoc]; rfl

/-- **The loop computes `loopSem`.** -/
theorem loop_run (B : List Bool → Bool) : ∀ (n : Nat) (w : List Bool) (α : Nat → Bool)
    (c bs : TermO) (k : Nat), IsIdx (enc w) c → HeadO bs (.ora (βB B)) →
    B (w ++ pre α n) = true →
    HeadO (Xk k ⬝ₚ c ⬝ₚ bs ⬝ₚ .ora α) (emb (boolT (loopSem B n w α))) := by
  intro n
  induction n with
  | zero =>
    intro w α c bs k hc hbs hB
    have h1 := Xk_unroll k c bs (.ora α)
    have h2 := look_spec hc hbs (hdPart c bs (.ora α)) (wPart (Xk (k + 1)) c bs (.ora α))
    rw [βB_enc] at h2
    have hw : B w = true := by
      rw [show pre α 0 = [] from rfl, List.append_nil] at hB; exact hB
    rw [hw] at h2
    exact h1.trans (h2.trans ((HeadO.single (.K _ _)).trans (hd_spec (HeadO.refl _))))
  | succ n ih =>
    intro w α c bs k hc hbs hB
    have h1 := Xk_unroll k c bs (.ora α)
    have h2 := look_spec hc hbs (hdPart c bs (.ora α)) (wPart (Xk (k + 1)) c bs (.ora α))
    rw [βB_enc] at h2
    cases hw : B w with
    | true =>
      rw [hw] at h2
      simp only [loopSem, hw, if_true]
      exact h1.trans (h2.trans ((HeadO.single (.K _ _)).trans (hd_spec (HeadO.refl _))))
    | false =>
      rw [hw] at h2
      simp only [loopSem, hw]
      refine h1.trans (h2.trans ((HeadO.of_run 2 rfl).trans ((w_spec (HeadO.refl _)).trans ?_)))
      refine ih (w ++ [α 0]) (shift α) _ _ (k + 1) ?_ (bs_spec hbs _ _ _) ?_
      · rw [enc_append]; exact isIdx_upd hc (α 0) _
      · rw [append_pre_succ]; exact hB

/-- **`loopSem` is the bit at the first barred prefix.** -/
theorem loopSem_spec (B : List Bool → Bool) : ∀ (n : Nat) (w : List Bool) (α : Nat → Bool),
    B (w ++ pre α n) = true →
    ∃ j, j ≤ n ∧ B (w ++ pre α j) = true ∧ (∀ i, i < j → B (w ++ pre α i) = false) ∧
      loopSem B n w α = α j := by
  intro n
  induction n with
  | zero =>
    intro w α hB
    exact ⟨0, Nat.le_refl _, hB, fun i hi => absurd hi (Nat.not_lt_zero i), rfl⟩
  | succ n ih =>
    intro w α hB
    cases hw : B w with
    | true =>
      refine ⟨0, Nat.zero_le _, by rw [show pre α 0 = [] from rfl, List.append_nil]; exact hw,
        fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
      simp [loopSem, hw]
    | false =>
      obtain ⟨j, hj, hBj, hmin, hsem⟩ := ih (w ++ [α 0]) (shift α) (by rw [append_pre_succ]; exact hB)
      refine ⟨j + 1, by omega, by rw [← append_pre_succ]; exact hBj, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => rw [show pre α 0 = [] from rfl, List.append_nil]; exact hw
        | succ i => rw [← append_pre_succ]; exact hmin i (by omega)
      · simp only [loopSem, hw]
        exact hsem

-- ---------------------------------------------------------------------------
-- The functional
-- ---------------------------------------------------------------------------

/-- **The functional**: the bit of `α` at the first length barred by `B`. -/
def FB (B : List Bool → Bool) : TermO := Xk 0 ⬝ₚ (.K ⬝ₚ .I) ⬝ₚ .ora (βB B)

theorem FB_run (B : List Bool → Bool) {α : Nat → Bool} {n : Nat} (h : B (pre α n) = true) :
    HeadO (FB B ⬝ₚ .ora α) (emb (boolT (loopSem B n [] α))) :=
  loop_run B n [] α _ _ 0 isIdx_c0 (HeadO.refl _) (by simpa using h)

theorem FB_total (B : List Bool → Bool) (hB : ∀ α : Nat → Bool, ∃ n, B (pre α n) = true) :
    OracleTotalO (FB B) := by
  intro α
  obtain ⟨n, hn⟩ := hB α
  obtain ⟨k, hk⟩ := FB_run B hn
  exact ⟨k, _, hk⟩

-- ---------------------------------------------------------------------------
-- Determinism, and the flip
-- ---------------------------------------------------------------------------

theorem boolT_emb_inj {b b' : Bool} (h : emb (boolT b) = emb (boolT b')) : b = b' := by
  cases b <;> cases b' <;> first | rfl | cases h

/-- Two head runs to booleans agree. -/
theorem headO_stepsNO_eq {t : TermO} {b b' : Bool} {k : Nat} (h : HeadO t (emb (boolT b)))
    (h' : StepsNO k t (emb (boolT b'))) : b = b' := by
  obtain ⟨n, hn⟩ := h
  have e1 := runO_of_steps hn (whnf_boolT b) (max n k) (Nat.le_max_left n k)
  have e2 := runO_of_steps h' (whnf_boolT b') (max n k) (Nat.le_max_right n k)
  exact boolT_emb_inj (e1.symm.trans e2)

/-- Flip bit `j`. -/
def flip (α : Nat → Bool) (j : Nat) : Nat → Bool := fun i => if i = j then !α i else α i

theorem pre_flip (α : Nat → Bool) (j : Nat) : ∀ i, i ≤ j → pre α i = pre (flip α j) i := by
  intro i hi
  rw [← agree_iff_pre]
  intro l hl
  unfold flip
  rw [if_neg (by omega)]

-- ---------------------------------------------------------------------------
-- The converse, and the equivalence
-- ---------------------------------------------------------------------------

/-- **Moduli give the decidable fan theorem.**  If every oracle-total functional
    has a modulus over the oracle points, every decidable bar is uniform. -/
theorem localO_fanDelta (h : ∀ F : TermO, OracleTotalO F → ∃ m φ, LocalO m φ F) : FanDelta := by
  intro B hB
  obtain ⟨m, φ, hφ⟩ := h (FB B) (FB_total B hB)
  -- the table reads the bit at the first hit
  have key : ∀ (α : Nat → Bool) (j : Nat), B (pre α j) = true →
      (∀ i, i < j → B (pre α i) = false) → φ (pre α m) = α j := by
    intro α j hj hmin
    obtain ⟨n, hn⟩ := hB α
    obtain ⟨j', _, hBj', hmin', hsem⟩ := loopSem_spec B n [] α (by simpa using hn)
    simp only [List.nil_append] at hBj' hmin'
    have hjj : j' = j := by
      rcases Nat.lt_trichotomy j' j with hlt | heq | hgt
      · rw [hmin j' hlt] at hBj'; cases hBj'
      · exact heq
      · rw [hmin' j hgt] at hj; cases hj
    obtain ⟨k, _, hs⟩ := hφ α
    have := headO_stepsNO_eq (FB_run B hn) hs
    rw [hsem, hjj] at this
    exact this.symm
  refine ⟨m, fun w hw => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hB (wordBits w)
  obtain ⟨j, _, hBj, hmin, _⟩ := loopSem_spec B n₀ [] (wordBits w) (by simpa using hn₀)
  simp only [List.nil_append] at hBj hmin
  by_cases hjm : j ≤ m
  · refine ⟨j, hjm, ?_⟩
    rw [← pre_word w j (by omega)]
    exact hBj
  · exfalso
    have h0 := key (wordBits w) j hBj hmin
    have h1 := key (flip (wordBits w) j) j (by rw [← pre_flip _ j j (Nat.le_refl j)]; exact hBj)
      (fun i hi => by rw [← pre_flip _ j i (by omega)]; exact hmin i hi)
    rw [← pre_flip _ j m (by omega), h0] at h1
    unfold flip at h1
    rw [if_pos rfl] at h1
    cases hb : wordBits w j <;> rw [hb] at h1 <;> cases h1

/-- **The calibration.**  Over the base gate, the decidable fan theorem is
    exactly "every oracle-total functional has a modulus". -/
theorem fanDelta_iff : FanDelta ↔ ∀ F : TermO, OracleTotalO F → ∃ m φ, LocalO m φ F :=
  ⟨fun hfan _ hF => fanDelta_localO hfan hF, localO_fanDelta⟩

end FanReverse
