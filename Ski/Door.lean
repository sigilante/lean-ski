import Ski.Entropy
import Ski.Front
open Term

/-!
# A kernel is a door: its arms pulled by axis

skijack's `SPEC.md` §4.1 fixes a kernel's shape as Arvo's: a door
`[[poke [peek load]] state]`, whose arms a runtime pulls by Nock axis and
applies to the whole kernel, `(4@k) k ev`.  This file states what a pull
is in SKI.

## The terms

skijack compiles a cell `[a b]` to its prelude's `pair` applied to `a`
and `b`, and an axis `n@e`, `n ≥ 1`, to the chain of `hd` and `tl` its
binary digits spell (`Front.pickC` over `Front.axisSteps`), in a program
that does not redefine or shadow `pair`, `hd` or `tl`.  The prelude's `pair`, `hd`
and `tl` are `pairT`, `fstT` and `sndT` of `Ski/Realize.lean`, term for
term (`pair_eq`, `hd_eq`, `tl_eq`); `fstT` and `sndT` are also
`Entropy.hdT` and `Entropy.tlT`.

## What is proved

- `pick_at`, `pull_at`: for any tree of cells over any leaves, the pull
  along a path, and so of axis `n ≥ 1` (`pull_at`), weakly reduces to the
  subtree Nock's slot gives at `n`.
- `door_poke`, `door_peek`, `door_load`, `door_state`, `door_battery`:
  axes 4, 10, 11, 3 and 2 of `[[poke [peek load]] st]`.
- `pull_poke` and its siblings: the Nock 9 pull `(4@k) k ev` reduces to
  `poke k ev`.  `Entropy.pokeT` is this pull (`pokeT_eq`).

## Selection is not inspection

Every theorem here holds for arbitrary terms at the leaves, `Ω` among
them (`pick_omega`).  The reductions are uniform in the leaves: one fixed
context, the pull, returns each arm as its own term, whatever it is.  This
is the positive side of `no_quote` (`Ski/Quote.lean`), by analogy rather
than by a theorem joining them: no combinator takes a live term to its
encoding, and none is needed to reach a kernel's arms.
-/

namespace Door

/-- `nat === Zero | Suc nat`, a file whose compilation holds skijack's
    prelude: `pair`, `hd` and `tl` among it. -/
def preludeC : List Nat :=
  [110, 97, 116, 32, 61, 61, 61, 32, 90, 101, 114, 111, 32, 124, 32, 83, 117, 99, 32, 110, 97,
   116, 10]

theorem pair_eq : Front.termOf (Front.compileFile preludeC) (nm! "pair") = some pairT := by
  decide +kernel

theorem hd_eq : Front.termOf (Front.compileFile preludeC) (nm! "hd") = some fstT := by
  decide +kernel

theorem tl_eq : Front.termOf (Front.compileFile preludeC) (nm! "tl") = some sndT := by
  decide +kernel

theorem fstT_eq : fstT = Entropy.hdT := by decide

theorem sndT_eq : sndT = Entropy.tlT := by decide

/-- A tree of cells over arbitrary terms: Nock's noun, its atoms any
    terms. -/
inductive Noun
  | leaf (t : Term)
  | cell (l r : Noun)

/-- A noun as skijack compiles it: each cell `pair l r`. -/
def Noun.toT : Noun → Term
  | .leaf t => t
  | .cell l r => pairT ⬝ l.toT ⬝ r.toT

/-- The subtree along a path, `false` for the head and `true` for the
    tail; Nock's slot `/` at axis `n ≥ 1` is `at (Front.axisSteps n)`.
    At `0`, where Nock crashes and skijack refuses the axis,
    `Front.axisSteps 0` is empty. -/
def Noun.at : Noun → List Bool → Option Noun
  | x, [] => some x
  | .cell l _, false :: bs => l.at bs
  | .cell _ r, true :: bs => r.at bs
  | .leaf _, _ :: _ => none

/-- The pull along a path, the first step innermost, as `Front.pickC`
    builds it. -/
def pickT (e : Term) : List Bool → Term
  | [] => e
  | b :: bs => pickT ((if b then sndT else fstT) ⬝ e) bs

/-- Axis `n` of `e`: `n@e` as skijack compiles it, for `n ≥ 1` and the
    prelude's `hd` and `tl` in scope.  `pull 0 e` is `e`, where skijack
    refuses axis `0`. -/
def pull (n : Nat) (e : Term) : Term := pickT e (Front.axisSteps n)

theorem hd_pair (a b : Term) : WSteps (fstT ⬝ (pairT ⬝ a ⬝ b)) a :=
  (fstT_beta _).trans ((pairT_beta a b K).trans (.single (.K a b)))

theorem tl_pair (a b : Term) : WSteps (sndT ⬝ (pairT ⬝ a ⬝ b)) b :=
  (sndT_beta _).trans ((pairT_beta a b (K ⬝ I)).trans
    (.step (.left _ (.K _ _)) (.single (.I _))))

theorem pickT_cong {e e' : Term} (h : WSteps e e') :
    ∀ bs, WSteps (pickT e bs) (pickT e' bs)
  | [] => h
  | _ :: bs => pickT_cong (WSteps.right _ h) bs

/-- **The pull is the slot.**  Along any path the noun has, the pull of
    any term that reduces to the noun reduces to the subtree there. -/
theorem pick_at : ∀ (bs : List Bool) (x y : Noun) (e : Term),
    x.at bs = some y → WSteps e x.toT → WSteps (pickT e bs) y.toT
  | [], x, y, e, h, he => by
    obtain rfl : x = y := by simpa [Noun.at] using h
    exact he
  | false :: bs, .cell l r, y, e, h, he =>
    pick_at bs l y _ h ((WSteps.right _ he).trans (hd_pair _ _))
  | true :: bs, .cell l r, y, e, h, he =>
    pick_at bs r y _ h ((WSteps.right _ he).trans (tl_pair _ _))
  | _ :: _, .leaf _, _, _, h, _ => by simp [Noun.at] at h

theorem pull_at {n : Nat} {x y : Noun} (h : x.at (Front.axisSteps n) = some y) :
    WSteps (pull n x.toT) y.toT :=
  pick_at _ x y _ h (.refl _)

/-- The door `[[poke [peek load]] st]`. -/
def door (poke peek load st : Term) : Noun :=
  .cell (.cell (.leaf poke) (.cell (.leaf peek) (.leaf load))) (.leaf st)

/-- The door as skijack compiles it, with the prelude's `pair` in scope. -/
def doorT (poke peek load st : Term) : Term := (door poke peek load st).toT

section
variable (poke peek load st : Term)

theorem door_poke : WSteps (pull 4 (doorT poke peek load st)) poke :=
  pull_at (y := .leaf poke) rfl

theorem door_peek : WSteps (pull 10 (doorT poke peek load st)) peek :=
  pull_at (y := .leaf peek) rfl

theorem door_load : WSteps (pull 11 (doorT poke peek load st)) load :=
  pull_at (y := .leaf load) rfl

theorem door_state : WSteps (pull 3 (doorT poke peek load st)) st :=
  pull_at (y := .leaf st) rfl

theorem door_battery :
    WSteps (pull 2 (doorT poke peek load st)) (pairT ⬝ poke ⬝ (pairT ⬝ peek ⬝ load)) :=
  pull_at (y := .cell (.leaf poke) (.cell (.leaf peek) (.leaf load))) rfl

/-- **Nock 9's pull**: arm 4 applied to the whole kernel, then the event. -/
theorem pull_poke (ev : Term) :
    WSteps (pull 4 (doorT poke peek load st) ⬝ doorT poke peek load st ⬝ ev)
      (poke ⬝ doorT poke peek load st ⬝ ev) :=
  WSteps.left _ (WSteps.left _ (door_poke ..))

theorem pull_peek (path : Term) :
    WSteps (pull 10 (doorT poke peek load st) ⬝ doorT poke peek load st ⬝ path)
      (peek ⬝ doorT poke peek load st ⬝ path) :=
  WSteps.left _ (WSteps.left _ (door_peek ..))

theorem pull_load (old : Term) :
    WSteps (pull 11 (doorT poke peek load st) ⬝ doorT poke peek load st ⬝ old)
      (load ⬝ doorT poke peek load st ⬝ old) :=
  WSteps.left _ (WSteps.left _ (door_load ..))

end

/-- `Entropy.pokeT`, the poke of the proved entropy statement, is the
    Nock 9 pull of arm 4. -/
theorem pokeT_eq (k ev : Term) : Entropy.pokeT k ev = pull 4 k ⬝ k ⬝ ev := by
  simp only [Entropy.pokeT, pull, show Front.axisSteps 4 = [false, false] from by decide,
    pickT, fstT_eq]
  rfl

/-- `Ω = S I I (S I I)`, which reduces to itself in three steps. -/
def omega : Term := S ⬝ I ⬝ I ⬝ (S ⬝ I ⬝ I)

/-- `door_poke` at `Ω`: the pull returns the arm as it stands, whatever it
    is.  Its divergence is not proved here. -/
theorem pick_omega (peek load st : Term) :
    WSteps (pull 4 (doorT omega peek load st)) omega :=
  door_poke ..

end Door
