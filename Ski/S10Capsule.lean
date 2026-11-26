import Ski.S10Closure
open Term HnfS

/-!
# S10 (Clock Closure), milestone M2: the four-leaf countdown `K4 = S(SSS)` (and `C6`)

Plan: `notes/S10-CLOCK-PLAN.md` §2.3, with W10.7 (the capsule register is defined by
structural recursion, not `Nat.iterate`).

The capsule `capsule C g = (C (C ⋯ (C BOT))) A tw7 (S tw4 tw7) tw8 tw5` (`g` copies of `C`).
Its frame is `[A, V, A] ++ pads` for `K4` with `V` the rest of the register.  One revolution
of `K4` is 5 quiet head steps from `[A, K4 V, A]` to `[A, V, A]` plus a deposit, with `V` a
free variable (`k4_rev`); at `V = BOT` the fifth step's seat is `F` (`k4_exit`).  So
`K4` fires after `5g` head steps (index `5g + 1`), by `iter_fires`.  `C6 = S(S(S(SSS)))` is
the same with 7-step revolutions and boundary `[S K4, V, A]`.
-/

namespace S10

def SS : Term := S ⬝ S
def A : Term := SS ⬝ S
def BOT : Term := S ⬝ F ⬝ F
def K4 : Term := S ⬝ A
def C6 : Term := S ⬝ (S ⬝ (S ⬝ A))

/-- The register `C^g · BOT`, by structural recursion (W10.7). -/
def creg (C : Term) : Nat → Term
  | 0 => BOT
  | g + 1 => C ⬝ creg C g

/-- The padding arguments of a capsule. -/
def pads : List Term := [tw 7, S ⬝ tw 4 ⬝ tw 7, tw 8, tw 5]

def capsule (C : Term) (g : Nat) : Term :=
  creg C g ⬝ A ⬝ tw 7 ⬝ (S ⬝ tw 4 ⬝ tw 7) ⬝ tw 8 ⬝ tw 5

/-! ## K4 -/

def k4bnd (c : Nat) : List Term := [A, creg K4 c, A]

/-- One K4 revolution, `V` free: 5 quiet steps from `[A, K4 V, A]` to `[A, V, A]`. -/
theorem k4_rev (V : Term) : QuietD 5 [A, K4 ⬝ V, A] [A, V, A] :=
  Quiet.of_qrun_take (k := 3) rfl

/-- The K4 exit: from `[A, BOT, A]` the seat after 5 steps is `F`. -/
theorem k4_exit : ∀ R, FiresAt ([A, BOT, A] ++ R) 5 := firesAt_of_qrun rfl

theorem args_capsule_zero (C : Term) : args (capsule C 0) = [F, F, A] ++ pads := rfl

theorem capsule_zero_fires (C : Term) : FiresAt (args (capsule C 0)) 0 := by
  have := firesAt_of_qrun (n := 0) (a := args (capsule C 0)) rfl []
  simpa using this

theorem args_capsule_K4 (c : Nat) : args (capsule K4 (c + 1)) = k4bnd c ++ pads := rfl

theorem k4_iter : ∀ g R, FiresAt (k4bnd g ++ R) (5 + psum (fun _ => 5) g) :=
  iter_fires k4bnd (fun _ => 5) 5 (fun c => k4_rev (creg K4 c)) k4_exit

/-- **K4 countdown**: first firing after `5g` head steps (firing index `5g + 1`). -/
theorem k4_fires (g : Nat) : FiresAt (args (capsule K4 g)) (5 * g) := by
  cases g with
  | zero => exact capsule_zero_fires K4
  | succ c =>
    rw [args_capsule_K4]
    have := k4_iter c pads
    rw [psum_const] at this
    have e : 5 + 5 * c = 5 * (c + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    rw [e] at this
    exact this

/-! ## C6 -/

def c6bnd (c : Nat) : List Term := [S ⬝ K4, creg C6 c, A]

theorem c6_rev (V : Term) : QuietD 7 [S ⬝ K4, C6 ⬝ V, A] [S ⬝ K4, V, A] :=
  Quiet.of_qrun_take (k := 3) rfl

theorem c6_exit : ∀ R, FiresAt ([S ⬝ K4, BOT, A] ++ R) 7 := firesAt_of_qrun rfl

theorem args_capsule_C6 (c : Nat) : args (capsule C6 (c + 1)) = c6bnd c ++ pads := rfl

theorem c6_iter : ∀ g R, FiresAt (c6bnd g ++ R) (7 + psum (fun _ => 7) g) :=
  iter_fires c6bnd (fun _ => 7) 7 (fun c => c6_rev (creg C6 c)) c6_exit

/-- **C6 countdown**: first firing after `7g` head steps (firing index `7g + 1`). -/
theorem c6_fires (g : Nat) : FiresAt (args (capsule C6 g)) (7 * g) := by
  cases g with
  | zero => exact capsule_zero_fires C6
  | succ c =>
    rw [args_capsule_C6]
    have := c6_iter c pads
    rw [psum_const] at this
    have e : 7 + 7 * c = 7 * (c + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    rw [e] at this
    exact this

/-! ## Clocks and the term-level statements -/

/-- The K4 capsule family as a clock (`H ≡ true`, `T g = 5g`). -/
def k4Clock : Clock Nat where
  frame g := args (capsule K4 g)
  H _ := true
  T g := 5 * g
  fire g _ R := (k4_fires g).append R
  quiet _ h := Bool.noConfusion h

def c6Clock : Clock Nat where
  frame g := args (capsule C6 g)
  H _ := true
  T g := 7 * g
  fire g _ R := (c6_fires g).append R
  quiet _ h := Bool.noConfusion h

theorem pure_tw : ∀ n, PureS (tw n)
  | 0 => .S
  | 1 => .S
  | n + 2 => .app .S (pure_tw (n + 1))

theorem pure_F : PureS F := .app (.app .S (pure_tw 8)) (pure_tw 8)
theorem pure_SS : PureS SS := .app .S .S
theorem pure_A : PureS A := .app pure_SS .S
theorem pure_BOT : PureS BOT := .app (.app .S pure_F) pure_F
theorem pure_K4 : PureS K4 := .app .S pure_A
theorem pure_C6 : PureS C6 := .app .S (.app .S (.app .S pure_A))

theorem pure_creg {C : Term} (hC : PureS C) : ∀ g, PureS (creg C g)
  | 0 => pure_BOT
  | g + 1 => .app hC (pure_creg hC g)

theorem pure_capsule {C : Term} (hC : PureS C) (g : Nat) : PureS (capsule C g) :=
  .app (.app (.app (.app (.app (pure_creg hC g) pure_A) (pure_tw 7))
    (.app (.app .S (pure_tw 4)) (pure_tw 7))) (pure_tw 8)) (pure_tw 5)

/-- K4 at the term level: the `5g`-th head reduct is `S F ⋯`, and no earlier one is. -/
theorem k4_fires_term (g : Nat) : TFiresAt (capsule K4 g) (5 * g) :=
  TFiresAt.of_firesAt (pure_capsule pure_K4 g) (k4_fires g)

theorem c6_fires_term (g : Nat) : TFiresAt (capsule C6 g) (7 * g) :=
  TFiresAt.of_firesAt (pure_capsule pure_C6 g) (c6_fires g)

end S10
