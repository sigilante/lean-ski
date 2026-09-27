import Ski.Fuel
import SkiZk.Traversable

/-!
# SKI execution is traversable

The compute side of the Pure Nock decomposition, for SKI.  A node's state is
the opcode it resolves: `S`, `K` or `I` when the node's term contracts, and
`halt` when it is a weak head normal form.  Normal order contracts at the
head of the spine, so the opcode of a contracting term is its head
combinator.  A node's data is the pair (current term, claimed result).

The local verifier `Fc` checks one contraction: a `halt` node's term has no
redex and equals the claimed result; any other node's state is its term's
head, and its one child carries the contractum and the same claimed result.
The trees `Fc` accepts are chains, one node per contraction plus the halt,
and they correspond one to one with `Eval` (`execution_traversable`).  The
leaf state is `halt` and every other state has fanout 1
(`execution_stateTraversable`).
-/

open Term

namespace SkiZk

/-- The opcode a node resolves. -/
inductive Op
  | S | K | I | halt
  deriving DecidableEq, Repr

/-- The head combinator of a term's spine. -/
def head : Term → Op
  | .S => .S
  | .K => .K
  | .I => .I
  | .app f _ => head f

theorem head_ne_halt (t : Term) : head t ≠ .halt := by
  induction t with
  | S => intro h; cases h
  | K => intro h; cases h
  | I => intro h; cases h
  | app f _ ihf => exact ihf

/-- A compute label: opcode, current term, claimed result. -/
abbrev CLabel := Op × (Term × Term)

/-- The local verifier of one contraction, `𝓛(F_comp, 1)`. -/
def Fc (l : CLabel) (o : List (Option CLabel)) : Prop :=
  (l.1 = .halt ∧ o = [none] ∧ step? l.2.1 = none ∧ l.2.2 = l.2.1) ∨
  (l.1 = head l.2.1 ∧ ∃ t' s', step? l.2.1 = some t' ∧ o = [some (s', (t', l.2.2))])

/-- `Eval`, as a language of (term, result) pairs. -/
def EvalLang (p : Term × Term) : Prop := Eval p.1 p.2

/-- The chain for `k` step-attempts from `t`, claiming `v`. -/
def chain : Nat → Term → Term → SLT CLabel
  | 0, t, v => .node (.halt, (t, v)) []
  | k + 1, t, v =>
    match step? t with
    | none => .node (.halt, (t, v)) []
    | some t' => .node (head t, (t, v)) [chain k t' v]

theorem outs_one {L : Type} (c : SLT L) : outs 1 [c] = [some c.label] := rfl

theorem Fc_leaf {l : CLabel} (h : Fc l [none]) :
    l.1 = .halt ∧ step? l.2.1 = none ∧ l.2.2 = l.2.1 := by
  cases h with
  | inl h => exact ⟨h.1, h.2.2⟩
  | inr h =>
    cases h.2 with
    | intro t' h' =>
      cases h' with
      | intro s' h'' => cases h''.2

theorem Fc_node {l : CLabel} {c : CLabel} (h : Fc l [some c]) :
    l.1 = head l.2.1 ∧ step? l.2.1 = some c.2.1 ∧ c.2.2 = l.2.2 := by
  cases h with
  | inl h => cases h.2.1
  | inr h =>
    cases h.2 with
    | intro t' h' =>
      cases h' with
      | intro s' h'' =>
        cases h''.2
        exact ⟨h.1, h''.1, rfl⟩

theorem Fc_not_leaf {l : CLabel} {t' : Term} (h : step? l.2.1 = some t') : ¬ Fc l [none] := by
  intro hF
  have := (Fc_leaf hF).2.1
  rw [h] at this
  cases this

/-- A valid node with children has exactly one. -/
theorem rvt_node_single {cs : List (SLT CLabel)}
    (hne : cs ≠ []) (hlen : cs.length ≤ 1) : ∃ c, cs = [c] := by
  match cs, hne, hlen with
  | [c], _, _ => exact ⟨c, rfl⟩
  | _ :: _ :: _, _, h => simp at h

/-- Soundness: every valid tree's root data is an evaluation. -/
theorem rvt_eval {t : SLT CLabel} (h : RVT Fc 1 t) : EvalLang t.label.2 := by
  induction h with
  | leaf hF =>
    have hl := Fc_leaf hF
    show Eval _ _
    simp only [SLT.label]
    rw [hl.2.2]
    exact ⟨.refl _, step?_none hl.2.1⟩
  | node hne hlen hF _ _ ih =>
    cases rvt_node_single hne hlen with
    | intro c hc =>
      subst hc
      have hn := Fc_node hF
      have hc := ih c (List.mem_singleton_self c)
      show Eval _ _
      unfold EvalLang at hc
      rw [hn.2.2] at hc
      exact ⟨.step (step?_sound hn.2.1) hc.1, hc.2⟩

/-- Completeness: a successful fuelled run builds a valid chain. -/
theorem chain_rvt : ∀ {k : Nat} {t v : Term}, evalF k t = some v →
    RVT Fc 1 (chain k t v) ∧ (chain k t v).label.2 = (t, v)
  | 0, _, _, h => by simp [evalF] at h
  | k + 1, t, v, h => by
    cases hs : step? t with
    | none =>
      simp only [evalF, hs] at h
      cases h
      simp only [chain, hs]
      exact ⟨.leaf (.inl ⟨rfl, rfl, hs, rfl⟩), rfl⟩
    | some t' =>
      simp only [evalF, hs] at h
      have ih := chain_rvt h
      simp only [chain, hs]
      refine ⟨.node (List.cons_ne_nil _ _) (by simp) ?_ (Fc_not_leaf hs) ?_, rfl⟩
      · rw [outs_one]
        refine .inr ⟨rfl, t', (chain k t' v).label.1, hs, ?_⟩
        rw [← ih.2]
      · intro c hc
        rw [List.mem_singleton] at hc
        rw [hc]
        exact ih.1

theorem eval_rvt {p : Term × Term} (h : EvalLang p) :
    ∃ t, RVT Fc 1 t ∧ t.label.2 = p := by
  cases evalF_complete h with
  | intro k hk => exact ⟨chain k p.1 p.2, chain_rvt hk⟩

/-- Uniqueness: a valid tree is determined by its root data. -/
theorem exec_unique {t₁ : SLT CLabel} (h₁ : RVT Fc 1 t₁) :
    ∀ {t₂}, RVT Fc 1 t₂ → t₁.label.2 = t₂.label.2 → t₁ = t₂ := by
  induction h₁ with
  | @leaf l hF =>
    intro t₂ h₂ he
    have hl := Fc_leaf hF
    cases h₂ with
    | @leaf l₂ hF₂ =>
      have hl₂ := Fc_leaf hF₂
      have : l = l₂ := Prod.ext (hl.1.trans hl₂.1.symm) he
      rw [this]
    | node hne hlen hF₂ _ _ =>
      cases rvt_node_single hne hlen with
      | intro c hc =>
        subst hc
        rw [outs_one] at hF₂
        have hn := Fc_node hF₂
        simp only [SLT.label] at he
        rw [← he, hl.2.1] at hn
        cases hn.2.1
  | @node l cs hne hlen hF _ _ ih =>
    intro t₂ h₂ he
    cases rvt_node_single hne hlen with
    | intro c hc =>
      subst hc
      rw [outs_one] at hF
      have hn := Fc_node hF
      cases h₂ with
      | @leaf l₂ hF₂ =>
        have hl₂ := Fc_leaf hF₂
        simp only [SLT.label] at he
        rw [he, hl₂.2.1] at hn
        cases hn.2.1
      | @node l₂ cs₂ hne₂ hlen₂ hF₂ _ hcs₂ =>
        cases rvt_node_single hne₂ hlen₂ with
        | intro c₂ hc₂ =>
          subst hc₂
          rw [outs_one] at hF₂
          have hn₂ := Fc_node hF₂
          simp only [SLT.label] at he
          have hstep := hn.2.1
          rw [he, hn₂.2.1] at hstep
          have hcc : c.label.2 = c₂.label.2 :=
            Prod.ext (Option.some.inj hstep).symm (hn.2.2.trans ((congrArg (fun p => p.2) he).trans hn₂.2.2.symm))
          have e := ih c (List.mem_singleton_self c) (hcs₂ c₂ (List.mem_singleton_self c₂)) hcc
          have el : l = l₂ := Prod.ext (by rw [hn.1, hn₂.1, he]) he
          rw [e, el]

/-- **SKI execution is traversable**: valid compute trees correspond one to
    one with evaluations. -/
theorem execution_traversable : Traversable EvalLang Fc 1 :=
  traversable_of (fun t => t.label.2) rvt_eval eval_rvt
    (fun h₁ h₂ he => exec_unique h₁ h₂ he)

/-- **State–data separation**: `halt` is the leaf state and the opcodes
    `S`, `K`, `I` have fanout 1. -/
def execution_stateTraversable : StateTraversable Fc 1 where
  leafSt s := s = .halt
  fanout _ := 1
  leaf_iff := by
    intro t h
    cases h with
    | leaf hF => exact ⟨fun _ => rfl, fun _ => (Fc_leaf hF).1⟩
    | @node l cs hne hlen hF _ _ =>
      cases rvt_node_single hne hlen with
      | intro c hc =>
        subst hc
        rw [outs_one] at hF
        have hn := Fc_node hF
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exact absurd (hn.1.symm.trans h) (head_ne_halt _)
        · cases h
  fanout_pos _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  fanout_shape := by
    intro s d o hs hF
    cases hF with
    | inl h => exact absurd h.1 hs
    | inr h =>
      cases h.2 with
      | intro t' h' =>
        cases h' with
        | intro s' h'' => exact ⟨[(s', (t', d.2))], rfl, h''.2⟩

end SkiZk
