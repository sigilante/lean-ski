import Ski.S10Capsule
open Term HnfS

/-!
# S10 (Clock Closure), milestones M3–M4: the countdown reader

Plan: `notes/S10-CLOCK-PLAN.md` §2.2, with W10.1 (σ opened as `lam W₁ s` in a 7-step head
segment; the case `m = 0` split off) and W10.2 (the term-level statement needs pure-S tags).

The reader `reader Ws g = S S (reg g (RD σ)) tw7 (S tw4 tw7) tw8` runs a program
`σ = prog Ws` of `m = |Ws|` layers `lam W s = S (SS) (SS W) s` over the base `A = SSS`, with a
register `reg g = KCAP^g BOT`.  The capture frame is `cap σ c = [g1, σ, reg c (RD σ)]`.

**M3, segments** (every one a single kernel evaluation of `qrun` with free variables):
* `prefix28`: `args (reader Ws (c+1))` runs 28 quiet steps to `cap σ c` (σ, `reg c` free);
* `zero21`: `args (reader Ws 0)` fires after 21 steps (σ free);
* `head7`: `[g1, lam W s, Q]` →7→ `[S, W, s, Q]` (W, s, Q free);
* `layer`: `[S, W, lam W' s, Q]` →5→ `[S, W', s, Q]` with an explicit two-entry deposit;
* `tail11`: `[S, W, A, KCAP C (RD σ)]` →11→ `cap`-shaped `[g1, σ, C (RD σ)]` (W, C, σ free);
* `exit4`: `[S, W, A, BOT (RD σ)]` fires after 4 steps;
* `m = 0`: `rev0` (13 steps) and `exit0` (6 steps) with σ = A.

**M4.** `layers` (induction on the word), `revolution` (`5m + 13`), `exit_fires` (`5m + 6`),
and `reader_fires`: for every `Ws : List Term` and every `g`, the first firing is after
`21 + (5m+13)g` head steps (firing index `22 + (5m+13)g`).  `reader_fires_term` transfers it
to head reduction of the term under `∀ W ∈ Ws, PureS W`.
-/

namespace S10

def FOD : Term := SS ⬝ SS
def g1 : Term := S ⬝ (S ⬝ S ⬝ FOD)
def RD : Term := S ⬝ g1
def KCAP : Term := S ⬝ SS ⬝ (S ⬝ (S ⬝ SS))

/-- A program layer `Λ(SS·W, s)`. -/
def lam (W s : Term) : Term := S ⬝ SS ⬝ (SS ⬝ W) ⬝ s

/-- The program `σ(W₁ ⋯ W_m)` over the base `A`. -/
def prog : List Term → Term
  | [] => A
  | W :: Ws => lam W (prog Ws)

/-- The register `KCAP^c · BOT`. -/
def reg : Nat → Term
  | 0 => BOT
  | c + 1 => KCAP ⬝ reg c

def reader (Ws : List Term) (g : Nat) : Term :=
  S ⬝ S ⬝ (reg g ⬝ (RD ⬝ prog Ws)) ⬝ tw 7 ⬝ (S ⬝ tw 4 ⬝ tw 7) ⬝ tw 8

/-- The capture frame. -/
def cap (σ : Term) (c : Nat) : List Term := [g1, σ, reg c ⬝ (RD ⬝ σ)]

/-- The last tag of a word, starting from `W`. -/
def lastW : Term → List Term → Term
  | W, [] => W
  | _, W' :: Ws => lastW W' Ws

/-! ## M3: segments -/

theorem prefix28 (σ C : Term) :
    QuietD 28 (args (S ⬝ S ⬝ (KCAP ⬝ C ⬝ (RD ⬝ σ)) ⬝ tw 7 ⬝ (S ⬝ tw 4 ⬝ tw 7) ⬝ tw 8))
      [g1, σ, C ⬝ (RD ⬝ σ)] :=
  Quiet.of_qrun_take (k := 3) rfl

theorem zero21 (σ : Term) :
    ∀ R, FiresAt (args (S ⬝ S ⬝ (BOT ⬝ (RD ⬝ σ)) ⬝ tw 7 ⬝ (S ⬝ tw 4 ⬝ tw 7) ⬝ tw 8) ++ R) 21 :=
  firesAt_of_qrun rfl

theorem head7 (W s Q : Term) : QuietD 7 [g1, lam W s, Q] [S, W, s, Q] :=
  Quiet.of_qrun_take (k := 4) rfl

/-- The layer lemma (plan §2.2), with its deposit displayed. -/
theorem layer (W W' s Q : Term) :
    Quiet 5 [S, W, lam W' s, Q]
      ([S, W', s, Q] ++ [s ⬝ (SS ⬝ W' ⬝ s) ⬝ Q, W ⬝ lam W' s ⬝ Q]) :=
  Quiet.of_qrun rfl

theorem tail11 (W C σ : Term) :
    QuietD 11 [S, W, A, KCAP ⬝ C ⬝ (RD ⬝ σ)] [g1, σ, C ⬝ (RD ⬝ σ)] :=
  Quiet.of_qrun_take (k := 3) rfl

theorem exit4 (W σ : Term) : ∀ R, FiresAt ([S, W, A, BOT ⬝ (RD ⬝ σ)] ++ R) 4 :=
  firesAt_of_qrun rfl

theorem rev0 (C : Term) : QuietD 13 [g1, A, KCAP ⬝ C ⬝ (RD ⬝ A)] [g1, A, C ⬝ (RD ⬝ A)] :=
  Quiet.of_qrun_take (k := 3) rfl

theorem exit0 : ∀ R, FiresAt ([g1, A, BOT ⬝ (RD ⬝ A)] ++ R) 6 :=
  firesAt_of_qrun rfl

/-! ## M4: layers, revolution, exit, the theorem -/

/-- The layers of a word: `5·|Ws|` quiet steps, every tag a free term. -/
theorem layers : ∀ (Ws : List Term) (W Q : Term),
    QuietD (5 * Ws.length) [S, W, prog Ws, Q] [S, lastW W Ws, A, Q]
  | [], W, Q => ⟨[], by
      show Quiet 0 [S, W, A, Q] ([S, W, A, Q] ++ [])
      rw [List.append_nil]; exact Quiet.refl _⟩
  | W' :: Ws, W, Q => by
    have h₁ : QuietD 5 [S, W, prog (W' :: Ws), Q] [S, W', prog Ws, Q] := ⟨_, layer W W' _ Q⟩
    have h := h₁.trans (layers Ws W' Q)
    refine h.cast ?_
    simp only [List.length_cons, Nat.mul_succ]; omega

/-- One revolution: `5m + 13` quiet steps from capture `c + 1` to capture `c`. -/
theorem revolution (Ws : List Term) (c : Nat) :
    QuietD (5 * Ws.length + 13) (cap (prog Ws) (c + 1)) (cap (prog Ws) c) := by
  match Ws with
  | [] => exact rev0 (reg c)
  | W₁ :: Ws' =>
    have h₁ := head7 W₁ (prog Ws') (reg (c + 1) ⬝ (RD ⬝ prog (W₁ :: Ws')))
    have h₂ := layers Ws' W₁ (reg (c + 1) ⬝ (RD ⬝ prog (W₁ :: Ws')))
    have h₃ := tail11 (lastW W₁ Ws') (reg c) (prog (W₁ :: Ws'))
    have h := (h₁.trans h₂).trans h₃
    refine h.cast ?_
    simp only [List.length_cons, Nat.mul_succ]; omega

/-- The exit: from capture 0 the first firing is after `5m + 6` steps. -/
theorem exit_fires (Ws : List Term) :
    ∀ R, FiresAt (cap (prog Ws) 0 ++ R) (5 * Ws.length + 6) := by
  match Ws with
  | [] => exact exit0
  | W₁ :: Ws' =>
    have h₁ := head7 W₁ (prog Ws') (BOT ⬝ (RD ⬝ prog (W₁ :: Ws')))
    have h₂ := layers Ws' W₁ (BOT ⬝ (RD ⬝ prog (W₁ :: Ws')))
    have h := (h₁.trans h₂).fires (exit4 (lastW W₁ Ws') (prog (W₁ :: Ws')))
    have e : 7 + 5 * Ws'.length + 4 = 5 * (W₁ :: Ws').length + 6 := by
      simp only [List.length_cons, Nat.mul_succ]; omega
    rw [e] at h
    exact h

/-- The revolutions as one Iter (`Clock.iter` / `iter_fires`). -/
theorem captures_fire (Ws : List Term) : ∀ c R,
    FiresAt (cap (prog Ws) c ++ R)
      ((5 * Ws.length + 6) + psum (fun _ => 5 * Ws.length + 13) c) :=
  iter_fires (cap (prog Ws)) (fun _ => 5 * Ws.length + 13) (5 * Ws.length + 6)
    (revolution Ws) (exit_fires Ws)

theorem args_reader_succ (Ws : List Term) (c : Nat) :
    args (reader Ws (c + 1)) =
      args (S ⬝ S ⬝ (KCAP ⬝ reg c ⬝ (RD ⬝ prog Ws)) ⬝ tw 7 ⬝ (S ⬝ tw 4 ⬝ tw 7) ⬝ tw 8) := rfl

/-- **The countdown reader, every tail.** -/
theorem reader_fires_append (Ws : List Term) (g : Nat) :
    ∀ R, FiresAt (args (reader Ws g) ++ R) (21 + (5 * Ws.length + 13) * g) := by
  intro R
  cases g with
  | zero => exact zero21 (prog Ws) R
  | succ c =>
    rw [args_reader_succ]
    have h := (prefix28 (prog Ws) (reg c)).fires (captures_fire Ws c) R
    rw [psum_const] at h
    have e : 28 + (5 * Ws.length + 6 + (5 * Ws.length + 13) * c) =
        21 + (5 * Ws.length + 13) * (c + 1) := by
      rw [Nat.mul_succ]
      generalize (5 * Ws.length + 13) * c = X
      omega
    rw [e] at h
    exact h

/-- **The countdown reader** (frame level, every program `Ws : List Term`, every `g`): the
first firing is after `21 + (5m+13)g` head steps, i.e. firing index `22 + (5m+13)g`. -/
theorem reader_fires (Ws : List Term) (g : Nat) :
    FiresAt (args (reader Ws g)) (21 + (5 * Ws.length + 13) * g) := by
  have := reader_fires_append Ws g []
  simpa using this

/-- The reader as a clock on `(program, register)`. -/
def readerClock : Clock (List Term × Nat) where
  frame p := args (reader p.1 p.2)
  H _ := true
  T p := 21 + (5 * p.1.length + 13) * p.2
  fire p _ := reader_fires_append p.1 p.2
  quiet _ h := Bool.noConfusion h

/-! ## Term level (W10.2) -/

theorem pure_FOD : PureS FOD := .app pure_SS pure_SS
theorem pure_g1 : PureS g1 := .app .S (.app (.app .S .S) pure_FOD)
theorem pure_RD : PureS RD := .app .S pure_g1
theorem pure_KCAP : PureS KCAP := .app (.app .S pure_SS) (.app .S (.app .S pure_SS))

theorem pure_lam {W s : Term} (hW : PureS W) (hs : PureS s) : PureS (lam W s) :=
  .app (.app (.app .S pure_SS) (.app pure_SS hW)) hs

theorem pure_prog : ∀ {Ws : List Term}, (∀ W ∈ Ws, PureS W) → PureS (prog Ws)
  | [], _ => pure_A
  | W :: Ws, h => pure_lam (h W (by simp)) (pure_prog (fun W' hW' => h W' (by simp [hW'])))

theorem pure_reg : ∀ c, PureS (reg c)
  | 0 => pure_BOT
  | c + 1 => .app pure_KCAP (pure_reg c)

theorem pure_reader {Ws : List Term} (h : ∀ W ∈ Ws, PureS W) (g : Nat) :
    PureS (reader Ws g) :=
  .app (.app (.app (.app (.app .S .S) (.app (pure_reg g) (.app pure_RD (pure_prog h))))
    (pure_tw 7)) (.app (.app .S (pure_tw 4)) (pure_tw 7))) (pure_tw 8)

/-- **The countdown reader on terms**: for pure-S tags, the `(21 + (5m+13)g)`-th head reduct
of `reader Ws g` is `S F ⋯` and no earlier head reduct is. -/
theorem reader_fires_term (Ws : List Term) (h : ∀ W ∈ Ws, PureS W) (g : Nat) :
    TFiresAt (reader Ws g) (21 + (5 * Ws.length + 13) * g) :=
  TFiresAt.of_firesAt (pure_reader h g) (reader_fires Ws g)

end S10
