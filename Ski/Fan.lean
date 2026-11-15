import Ski.OracleBar

open Term

/-!
# The fan step from the decidable fan theorem

`OracleFan.cantor_fan` proves that an oracle-total functional is m-local by the
fan theorem for an *arbitrary* bar (`OracleFan.fan`, by König's lemma, classical),
applied to the bar `Leaf F w` ("F is constant on the cylinder of w"), which is
not decidable.  This module shows that the **decidable** fan theorem is enough.

- `FanDelta`: the decidable fan theorem, as a proposition.  Every decidable bar
  (a `List Bool → Bool` that every stream meets) is uniform.
- `fanDelta_classical : FanDelta`, from `OracleFan.fan`.  Classical; not in the gate.
- `stepO?`, `runO`: a computable step function and a fuel-bounded evaluator for
  the oracle calculus, sound and complete for `StepO`.
- `Rel r`: two oracle terms that agree except at oracle cells whose streams
  agree on their first `r` bits.  One head step preserves `Rel` at one less bit
  (`Rel.step`); so a run of `k ≤ n` steps on `ora α` is a run on every `ora β`
  with the same first `n` bits (`transfer`).  This is pointwise continuity with
  the run length as its modulus, and it is why a *decidable* bar exists.
- `barF F w`: run `F ⬝ ora (w ++ false^ω)` for `|w|` steps and ask whether a
  boolean came out.  Decidable, and a bar when `F` is oracle-total.
- `fanDelta_localO`: under `FanDelta`, every oracle-total functional (with or
  without oracle constants inside it) has a modulus over the oracle points.
- `fanDelta_cantor_fan`: under `FanDelta`, every oracle-total CL functional is
  m-local in the paper's sense (`Search.Local`).  This replaces the classical
  step of `OracleFan.cantor_fan` by a hypothesis.

Everything but `fanDelta_classical` uses only `propext` and `Quot.sound`.
-/

namespace Fan

open NoLift LiftBool Search CantorLift CantorTotal OracleFan

-- ---------------------------------------------------------------------------
-- The decidable fan theorem
-- ---------------------------------------------------------------------------

/-- **The decidable fan theorem.**  A decidable bar that every stream meets is
    met by every word of some one length `m`, at a prefix. -/
def FanDelta : Prop :=
  ∀ B : List Bool → Bool, (∀ α : Nat → Bool, ∃ n, B (pre α n) = true) →
    ∃ m, ∀ w : List Bool, w.length = m → ∃ j, j ≤ m ∧ B (w.take j) = true

/-- Classically, `FanDelta` holds (König's lemma, `OracleFan.fan`). -/
theorem fanDelta_classical : FanDelta := fun B hB => fan (fun w => B w = true) hB

-- ---------------------------------------------------------------------------
-- Prefixes
-- ---------------------------------------------------------------------------

/-- `α` and `β` agree on their first `n` bits. -/
def Agree (n : Nat) (α β : Nat → Bool) : Prop := ∀ i, i < n → α i = β i

theorem agree_refl (n : Nat) (α : Nat → Bool) : Agree n α α := fun _ _ => rfl

theorem agree_mono {n n' : Nat} (h : n' ≤ n) {α β : Nat → Bool} (ha : Agree n α β) : Agree n' α β :=
  fun i hi => ha i (Nat.lt_of_lt_of_le hi h)

theorem agree_shift {n : Nat} {α β : Nat → Bool} (ha : Agree (n + 1) α β) :
    Agree n (shift α) (shift β) :=
  fun i hi => ha (i + 1) (by omega)

theorem agree_iff_pre : ∀ (n : Nat) (α β : Nat → Bool), Agree n α β ↔ pre α n = pre β n
  | 0, α, β => ⟨fun _ => rfl, fun _ i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, α, β => by
    constructor
    · intro ha
      show α 0 :: pre (shift α) n = β 0 :: pre (shift β) n
      rw [ha 0 (by omega), (agree_iff_pre n _ _).1 (agree_shift ha)]
    · intro h i hi
      have h' : α 0 :: pre (shift α) n = β 0 :: pre (shift β) n := h
      simp only [List.cons.injEq] at h'
      cases i with
      | zero => exact h'.1
      | succ i => exact (agree_iff_pre n _ _).2 h'.2 i (by omega)

theorem pre_take : ∀ (j m : Nat) (α : Nat → Bool), j ≤ m → (pre α m).take j = pre α j
  | 0, _, _, _ => rfl
  | j + 1, 0, _, h => absurd h (by omega)
  | j + 1, m + 1, α, h => by
    show (α 0 :: pre (shift α) m).take (j + 1) = α 0 :: pre (shift α) j
    rw [List.take_succ_cons, pre_take j m (shift α) (by omega)]

theorem pre_wordBits (w : List Bool) : pre (wordBits w) w.length = w := by
  rw [pre_word w w.length (Nat.le_refl _), List.take_length]

-- ---------------------------------------------------------------------------
-- A computable step function and a bounded evaluator
-- ---------------------------------------------------------------------------

/-- The root redexes of the oracle calculus. -/
def headStep : TermO → Option TermO
  | .I ⬝ₚ x => some x
  | .K ⬝ₚ x ⬝ₚ _ => some x
  | .S ⬝ₚ f ⬝ₚ g ⬝ₚ x => some (f ⬝ₚ x ⬝ₚ (g ⬝ₚ x))
  | .ora α ⬝ₚ k => some (k ⬝ₚ emb (boolT (α 0)) ⬝ₚ .ora (shift α))
  | _ => none

/-- One head step, or `none` at a weak head normal form. -/
def stepO? : TermO → Option TermO
  | .app f x =>
    match headStep (f ⬝ₚ x) with
    | some u => some u
    | none => (stepO? f).map (· ⬝ₚ x)
  | _ => none

theorem headStep_sound : ∀ {t u : TermO}, headStep t = some u → StepO t u := by
  intro t u h
  unfold headStep at h
  split at h
  · cases h; exact .I _
  · cases h; exact .K _ _
  · cases h; exact .S _ _ _
  · cases h; exact .ora _ _
  · cases h

/-- A term that steps is not the head of a root redex: `headStep` looks three
    applications deep, and a stepping head has `app` at every one. -/
theorem headStep_app_of_step {f f' : TermO} (h : StepO f f') (x : TermO) :
    headStep (f ⬝ₚ x) = none := by
  cases h with
  | S => rfl
  | K => rfl
  | I => rfl
  | ora => rfl
  | left y h' =>
    cases h' with
    | S => rfl
    | K => rfl
    | I => rfl
    | ora => rfl
    | left z h'' => cases h'' <;> rfl

theorem stepO?_whnf {v : TermO} (hv : WhnfO v) : stepO? v = none := by
  cases hv <;> rfl

theorem stepO?_sound : ∀ {t u : TermO}, stepO? t = some u → StepO t u
  | .S, _, h | .K, _, h | .I, _, h | .ora _, _, h => by cases h
  | .app f x, u, h => by
    unfold stepO? at h
    split at h
    · cases h; exact headStep_sound (by assumption)
    · obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.1 h
      exact .left _ (stepO?_sound hf')

theorem stepO?_complete {t u : TermO} (h : StepO t u) : stepO? t = some u := by
  induction h with
  | S f g x => rfl
  | K x y => rfl
  | I x => rfl
  | ora α k => rfl
  | left x h ih =>
    rename_i f f'
    show (match headStep (f ⬝ₚ x) with
      | some u => some u
      | none => (stepO? f).map (· ⬝ₚ x)) = some (f' ⬝ₚ x)
    rw [headStep_app_of_step h x]
    simp [ih]

/-- Run for at most `n` steps; stop at a weak head normal form. -/
def runO : Nat → TermO → TermO
  | 0, t => t
  | n + 1, t =>
    match stepO? t with
    | some u => runO n u
    | none => t

theorem runO_whnf {v : TermO} (hv : WhnfO v) : ∀ n, runO n v = v
  | 0 => rfl
  | n + 1 => by simp [runO, stepO?_whnf hv]

/-- A run that reaches a whnf in `k ≤ m` steps is what `runO m` computes. -/
theorem runO_of_steps {k : Nat} {t v : TermO} (h : StepsNO k t v) :
    WhnfO v → ∀ m, k ≤ m → runO m t = v := by
  induction h with
  | refl t => intro hv m _; exact runO_whnf hv m
  | step hs _ ih =>
    intro hv m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [runO, stepO?_complete hs]
    exact ih hv m' (by omega)

/-- `runO n t` is reached from `t` in at most `n` steps. -/
theorem runO_steps : ∀ (n : Nat) (t : TermO), ∃ k, k ≤ n ∧ StepsNO k t (runO n t)
  | 0, t => ⟨0, Nat.le_refl _, .refl t⟩
  | n + 1, t => by
    cases h : stepO? t with
    | none => exact ⟨0, by omega, by simp only [runO, h]; exact .refl t⟩
    | some u =>
      obtain ⟨k, hk, hs⟩ := runO_steps n u
      exact ⟨k + 1, by omega, by simp only [runO, h]; exact .step (stepO?_sound h) hs⟩

-- ---------------------------------------------------------------------------
-- Runs depend only on the bits they read
-- ---------------------------------------------------------------------------

/-- Equal up to oracle cells whose streams agree on their first `r` bits. -/
inductive Rel (r : Nat) : TermO → TermO → Prop
  | S : Rel r .S .S
  | K : Rel r .K .K
  | I : Rel r .I .I
  | ora {α β : Nat → Bool} (h : Agree r α β) : Rel r (.ora α) (.ora β)
  | app {f g x y : TermO} (hf : Rel r f g) (hx : Rel r x y) : Rel r (f ⬝ₚ x) (g ⬝ₚ y)

theorem Rel.refl (r : Nat) : ∀ t : TermO, Rel r t t
  | .S => .S
  | .K => .K
  | .I => .I
  | .ora α => .ora (agree_refl r α)
  | .app f x => .app (Rel.refl r f) (Rel.refl r x)

theorem Rel.mono {r r' : Nat} (h : r' ≤ r) {t u : TermO} (hr : Rel r t u) : Rel r' t u := by
  induction hr with
  | S => exact .S
  | K => exact .K
  | I => exact .I
  | ora ha => exact .ora (agree_mono h ha)
  | app _ _ ihf ihx => exact .app ihf ihx

/-- A term without oracles is related only to itself. -/
theorem Rel.emb_left {r : Nat} : ∀ (t : Term) {u : TermO}, Rel r (emb t) u → u = emb t
  | .S, _, h => by cases h; rfl
  | .K, _, h => by cases h; rfl
  | .I, _, h => by cases h; rfl
  | .app f x, _, h => by
    cases h with
    | app hf hx => rw [Rel.emb_left f hf, Rel.emb_left x hx]; rfl

/-- One head step on the left is mirrored on the right, at one bit less. -/
theorem Rel.step {r : Nat} {t t' u : TermO} (h : Rel (r + 1) t u) (hs : StepO t t') :
    ∃ u', StepO u u' ∧ Rel r t' u' := by
  induction hs generalizing u with
  | S f g x =>
    cases h with | app h1 hx =>
    cases h1 with | app h2 hg =>
    cases h2 with | app h3 hf =>
    cases h3 with | S =>
    exact ⟨_, .S _ _ _, .app (.app (Rel.mono (by omega) hf) (Rel.mono (by omega) hx))
      (.app (Rel.mono (by omega) hg) (Rel.mono (by omega) hx))⟩
  | K x y =>
    cases h with | app h1 hy =>
    cases h1 with | app h2 hx =>
    cases h2 with | K =>
    exact ⟨_, .K _ _, Rel.mono (by omega) hx⟩
  | I x =>
    cases h with | app h1 hx =>
    cases h1 with | I =>
    exact ⟨_, .I _, Rel.mono (by omega) hx⟩
  | ora α k =>
    cases h with | app h1 hk =>
    cases h1 with | ora ha =>
    rename_i β
    refine ⟨_, .ora β _, .app (.app (Rel.mono (by omega) hk) ?_) (.ora (agree_shift ha))⟩
    rw [ha 0 (by omega)]
    exact Rel.refl r _
  | left x hs ih =>
    cases h with | app hf hx =>
    obtain ⟨g', hg', hrel⟩ := ih hf
    exact ⟨_, .left _ hg', .app hrel (Rel.mono (by omega) hx)⟩

/-- `n` steps on the left are mirrored on the right, at `n` bits less. -/
theorem Rel.stepsN {k n : Nat} {t t' u : TermO} (h : Rel (k + n) t u) (hs : StepsNO n t t') :
    ∃ u', StepsNO n u u' ∧ Rel k t' u' := by
  induction hs generalizing u with
  | refl t => exact ⟨u, .refl u, h⟩
  | step h1 _ ih =>
    obtain ⟨u1, hu1, hrel⟩ := Rel.step h h1
    obtain ⟨u', hu', hrel'⟩ := ih hrel
    exact ⟨u', .step hu1 hu', hrel'⟩

/-- **Pointwise continuity with the run length as modulus.**  A run of `k ≤ n`
    steps of `F ⬝ ora α` to a boolean is a run of `F ⬝ ora β` to the same
    boolean whenever `β` has the same first `n` bits. -/
theorem transfer {n k : Nat} {F : TermO} {α β : Nat → Bool} {b : Bool} (ha : Agree n α β)
    (h : StepsNO k (F ⬝ₚ .ora α) (emb (boolT b))) (hk : k ≤ n) :
    StepsNO k (F ⬝ₚ .ora β) (emb (boolT b)) := by
  have hrel : Rel ((n - k) + k) (F ⬝ₚ .ora α) (F ⬝ₚ .ora β) := by
    rw [Nat.sub_add_cancel hk]
    exact .app (Rel.refl n F) (.ora ha)
  obtain ⟨u', hu', hrel'⟩ := Rel.stepsN hrel h
  rw [Rel.emb_left _ hrel'] at hu'
  exact hu'

-- ---------------------------------------------------------------------------
-- The decidable bar
-- ---------------------------------------------------------------------------

/-- Read a boolean off a weak head normal form: `K` is true, `K I` is false. -/
def isBoolT? : TermO → Option Bool
  | .K => some true
  | .K ⬝ₚ .I => some false
  | _ => none

theorem isBoolT?_emb : ∀ b : Bool, isBoolT? (emb (boolT b)) = some b
  | true => rfl
  | false => rfl

theorem isBoolT?_some : ∀ {t : TermO} {b : Bool}, isBoolT? t = some b → t = emb (boolT b) := by
  intro t b h
  unfold isBoolT? at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

/-- Oracle totality for a term of the oracle calculus: `F ⬝ ora α` reaches a
    boolean for every `α`.  `F` may itself contain oracle constants. -/
def OracleTotalO (F : TermO) : Prop :=
  ∀ α : Nat → Bool, ∃ n b, StepsNO n (F ⬝ₚ .ora α) (emb (boolT b))

theorem oracleTotalO_emb {F : Term} (h : OracleTotal F) : OracleTotalO (emb F) := h

/-- A modulus over the oracle points: `F ⬝ ora α` reads the boolean `φ (α|m)`,
    in at most `m` steps. -/
def LocalO (m : Nat) (φ : List Bool → Bool) (F : TermO) : Prop :=
  ∀ α : Nat → Bool, ∃ k, k ≤ m ∧ StepsNO k (F ⬝ₚ .ora α) (emb (boolT (φ (pre α m))))

/-- **The decidable bar.**  Run `F` on `w` padded with `false`, for `|w|` steps,
    and ask whether a boolean came out. -/
def barF (F : TermO) (w : List Bool) : Bool :=
  (isBoolT? (runO w.length (F ⬝ₚ .ora (wordBits w)))).isSome

/-- The table: the boolean `F` reads on `w` padded with `false` in `m` steps. -/
def resF (F : TermO) (m : Nat) (w : List Bool) : Bool :=
  (isBoolT? (runO m (F ⬝ₚ .ora (wordBits w)))).getD false

/-- A barred word fixes `F` on every stream through it, within `|w|` steps. -/
theorem barF_sound {F : TermO} {w : List Bool} (h : barF F w = true) :
    ∃ b, ∀ α : Nat → Bool, pre α w.length = w →
      ∃ k, k ≤ w.length ∧ StepsNO k (F ⬝ₚ .ora α) (emb (boolT b)) := by
  unfold barF at h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
  refine ⟨b, fun α hα => ?_⟩
  obtain ⟨k, hk, hs⟩ := runO_steps w.length (F ⬝ₚ .ora (wordBits w))
  rw [isBoolT?_some hb] at hs
  refine ⟨k, hk, transfer ?_ hs hk⟩
  rw [agree_iff_pre, pre_wordBits, hα]

theorem whnf_boolT (b : Bool) : WhnfO (emb (boolT b)) := by
  cases b
  · exact .K1 _
  · exact .K

/-- An oracle-total functional's runs make `barF` a bar. -/
theorem barF_bar {F : TermO} (hF : OracleTotalO F) : ∀ α : Nat → Bool, ∃ n, barF F (pre α n) = true := by
  intro α
  obtain ⟨n, b, h⟩ := hF α
  refine ⟨n, ?_⟩
  have ha : Agree n α (wordBits (pre α n)) := by
    rw [agree_iff_pre]
    have := pre_wordBits (pre α n)
    rw [KleeneTree.pre_length] at this
    exact this.symm
  have hs := transfer ha h (Nat.le_refl n)
  unfold barF
  rw [KleeneTree.pre_length, runO_of_steps hs (whnf_boolT b) n (Nat.le_refl n), isBoolT?_emb]
  rfl

-- ---------------------------------------------------------------------------
-- The fan step under FanDelta
-- ---------------------------------------------------------------------------

/-- **The fan step at Cantor space, from the decidable fan theorem.**  Every
    oracle-total functional of the oracle calculus has a modulus over the
    oracle points.  Constructive given `FanDelta`. -/
theorem fanDelta_localO (hfan : FanDelta) {F : TermO} (hF : OracleTotalO F) :
    ∃ m φ, LocalO m φ F := by
  obtain ⟨m, hm⟩ := hfan (barF F) (barF_bar hF)
  refine ⟨m, resF F m, fun α => ?_⟩
  obtain ⟨j, hj, hbar⟩ := hm (pre α m) (KleeneTree.pre_length α m)
  rw [pre_take j m α hj] at hbar
  obtain ⟨b, hb⟩ := barF_sound hbar
  rw [KleeneTree.pre_length] at hb
  -- the run on α
  obtain ⟨k, hk, hs⟩ := hb α rfl
  -- the run on the padded word, to read the table
  obtain ⟨k', hk', hs'⟩ := hb (wordBits (pre α m)) (by rw [pre_word _ _ (by rw [KleeneTree.pre_length]; exact hj), pre_take j m α hj])
  have hres : resF F m (pre α m) = b := by
    unfold resF
    rw [runO_of_steps hs' (whnf_boolT b) m (by omega), isBoolT?_emb]
    rfl
  exact ⟨k, by omega, by rw [hres]; exact hs⟩

/-- **`cantor_fan` from the decidable fan theorem.**  Every oracle-total CL
    functional is m-local in the sense of `Search.Local`.  The modulus is one
    more than the fan's bound, by `OracleFan.oracle_local`. -/
theorem fanDelta_cantor_fan (hfan : FanDelta) {F : Term} (hF : OracleTotal F) :
    ∃ m φ, Local m φ F := by
  obtain ⟨m, φ, hl⟩ := fanDelta_localO hfan (oracleTotalO_emb hF)
  refine ⟨m + 1, fun w => φ (w.take m), fun w hw s hs => ?_⟩
  obtain ⟨k, hk, hrun⟩ := hl (wordBits w)
  have hpre : pre (wordBits w) m = w.take m := pre_word w m (by omega)
  rw [hpre] at hrun
  apply oracle_local hrun s
  rw [pre_word w (k + 1) (by omega)]
  exact take_prefix w (k + 1) hs

end Fan
