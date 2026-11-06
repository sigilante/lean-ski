import Ski.KleeneTree

open Term

/-!
# Where the Cantor fan step is classical

`OracleFan.cantor_fan_w`: an oracle-total functional is m-local.  Its proof
has three parts.
- **Pointwise moduli** (`OracleFan.oracle_local_w`): every oracle point has its
  own modulus.  This is the simulation, and it is constructive.
- **The fan theorem**: the pointwise moduli give one uniform bar.  This is
  classical.
- **From a bar to a table.**  This is constructive.

This module isolates the middle part.

- `OBar F w`, an inductive bar.  F is barred at `w` when it is constant on every
  CL term with prefix `w` (a leaf), or when both one-bit extensions of `w` are
  barred (a node).  So `OBar F []` says that F's query tree is well-founded.
- `obar_iff_local`: `OBar F []` holds iff F is m-local for some m.
  Constructive: axioms `propext`, `Quot.sound`.
- `pointwise_obar`: if every path through the binary tree meets a leaf, then
  `OBar F []`.  This is the fan theorem for this bar, classical, and the only
  classical step (`cantor_fan_bar`).

The classical step cannot be removed by working in the term model.
`KleeneTree.no_lift_cantor_total'` is its failure there: over the definable
streams, pointwise totality does not give a bar.  A Kleene tree is a definable
infinite tree with no definable path, which is the classical
counterexample to the fan theorem for computable points.
-/

namespace OracleBar

open NoLift LiftBool Search CantorLift CantorTotal OracleFan

/-- `F` is constant on every CL term with prefix `w`. -/
def Leaf (F : Term) (w : List Bool) : Prop :=
  ∃ b : Bool, ∀ s, HasPrefix w s → WSteps (F ⬝ s) (boolT b)

/-- **The inductive bar.** -/
inductive OBar (F : Term) : List Bool → Prop
  | leaf {w : List Bool} : Leaf F w → OBar F w
  | node {w : List Bool} : OBar F (w ++ [false]) → OBar F (w ++ [true]) → OBar F w

-- ---------------------------------------------------------------------------
-- A bar is a modulus, constructively
-- ---------------------------------------------------------------------------

theorem hasPrefix_append : ∀ (w v : List Bool) {s : Term}, HasPrefix (w ++ v) s → HasPrefix w s
  | [], _, _, _ => trivial
  | b :: w, v, s, ⟨s', h1, h2⟩ => ⟨s', h1, hasPrefix_append w v h2⟩

theorem prefix_take_tail : ∀ (w : List Bool) (c : Bool) (v : List Bool) (k : Nat) {s : Term},
    HasPrefix (w ++ c :: v) s → HasPrefix (w ++ [c] ++ v.take k) s
  | [], c, v, k, s, ⟨s', h1, h2⟩ => ⟨s', h1, take_prefix v k h2⟩
  | b :: w, c, v, k, s, ⟨s', h1, h2⟩ => ⟨s', h1, prefix_take_tail w c v k h2⟩

/-- A barred word fixes `F` on all extensions of a uniform length. -/
theorem obar_table {F : Term} {w : List Bool} (h : OBar F w) :
    ∃ m, ∃ φ : List Bool → Bool, ∀ v : List Bool, v.length = m →
      ∀ s, HasPrefix (w ++ v) s → WSteps (F ⬝ s) (boolT (φ v)) := by
  induction h with
  | @leaf w hl =>
    obtain ⟨b, hb⟩ := hl
    exact ⟨0, fun _ => b, fun v _ s hs => hb s (hasPrefix_append w v hs)⟩
  | @node w _ _ ih0 ih1 =>
    obtain ⟨m0, φ0, h0⟩ := ih0
    obtain ⟨m1, φ1, h1⟩ := ih1
    refine ⟨max m0 m1 + 1, fun v => match v with
      | false :: v' => φ0 (v'.take m0)
      | true :: v' => φ1 (v'.take m1)
      | [] => false, ?_⟩
    intro v hv s hs
    match v, hv, hs with
    | false :: v', hv', hs' =>
      have hl' : v'.length = max m0 m1 := by simpa using hv'
      have hle : m0 ≤ max m0 m1 := Nat.le_max_left _ _
      exact h0 _ (by simp; omega) s (prefix_take_tail w false v' m0 hs')
    | true :: v', hv', hs' =>
      have hl' : v'.length = max m0 m1 := by simpa using hv'
      have hle : m1 ≤ max m0 m1 := Nat.le_max_right _ _
      exact h1 _ (by simp; omega) s (prefix_take_tail w true v' m1 hs')

/-- **A bar at the root is a modulus.** -/
theorem obar_local {F : Term} (h : OBar F []) : ∃ m φ, Local m φ F := by
  obtain ⟨m, φ, hφ⟩ := obar_table h
  exact ⟨m, φ, fun w hw s hs => hφ w hw s (by simpa using hs)⟩

/-- **A modulus is a bar.** -/
theorem local_obar {F : Term} {m : Nat} {φ : List Bool → Bool} (h : Local m φ F) : OBar F [] := by
  suffices key : ∀ k (w : List Bool), w.length + k = m → OBar F w from key m [] (by simp)
  intro k
  induction k with
  | zero => intro w hw; exact .leaf ⟨φ w, fun s hs => h w (by omega) s hs⟩
  | succ k ih =>
    intro w hw
    exact .node (ih _ (by simp; omega)) (ih _ (by simp; omega))

/-- **Bars and moduli coincide, constructively.** -/
theorem obar_iff_local (F : Term) : OBar F [] ↔ ∃ m φ, Local m φ F :=
  ⟨obar_local, fun ⟨_, _, h⟩ => local_obar h⟩

-- ---------------------------------------------------------------------------
-- The classical step
-- ---------------------------------------------------------------------------

/-- **The fan theorem for this bar.**  If every path meets a leaf, `F` is
    barred at the root.  Classical (by `OracleFan.fan`). -/
theorem pointwise_obar {F : Term} (h : ∀ α : Nat → Bool, ∃ n, Leaf F (CantorTotal.pre α n)) :
    OBar F [] := by
  obtain ⟨m, hm⟩ := fan (Leaf F) h
  suffices key : ∀ k (w : List Bool), w.length + k = m → OBar F w from key m [] (by simp)
  intro k
  induction k with
  | zero =>
    intro w hw
    obtain ⟨j, _, b, hb⟩ := hm w (by omega)
    exact .leaf ⟨b, fun s hs => hb s (take_prefix w j hs)⟩
  | succ k ih =>
    intro w hw
    exact .node (ih _ (by simp; omega)) (ih _ (by simp; omega))

/-- **The Cantor fan step, factored.**  Pointwise moduli (constructive), then
    the fan theorem (`pointwise_obar`, the classical step), then the bar to a
    table (constructive). -/
theorem cantor_fan_bar {F : Term} (hF : OracleTotalW F) : ∃ m φ, Local m φ F := by
  apply obar_local
  apply pointwise_obar
  intro α
  obtain ⟨n, v, b, hrun, hv, hb⟩ := hF α
  obtain ⟨N, hN⟩ := oracle_local_w hrun hv hb
  exact ⟨N, b, hN⟩

end OracleBar
