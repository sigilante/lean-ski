import Ski.Basic
import Nock.NounValidation
import SkiZk.Traversable

/-!
# SKI terms as Pure Nock nouns; memory is traversable

A term is stored as a noun: `S`, `K`, `I` are the atoms 0, 1, 2 and
application is a cell.  `toNoun` is injective, so a memory table holding
nouns holds terms, and Pure Nock's noun validation (`Noun_Validation`)
checks each stored term with a transcript of `2λ − 1` rows for `λ` leaves.

The memory verifier `Fm` has four states: a cell node has fanout 2 and its
children carry the head and tail; an atom node is a leaf and its state names
the combinator.  The trees `Fm` accepts correspond one to one with the nouns
that encode terms (`memory_traversable`).
-/

open Term Nock

namespace SkiZk

/-- The noun that stores a term. -/
def toNoun : Term → Noun
  | .S => .atom 0
  | .K => .atom 1
  | .I => .atom 2
  | .app f x => .cell (toNoun f) (toNoun x)

theorem toNoun_injective : Function.Injective toNoun := by
  intro t
  induction t with
  | S => intro u h; cases u <;> simp_all [toNoun]
  | K => intro u h; cases u <;> simp_all [toNoun]
  | I => intro u h; cases u <;> simp_all [toNoun]
  | app f x ihf ihx =>
    intro u h
    cases u with
    | S => simp [toNoun] at h
    | K => simp [toNoun] at h
    | I => simp [toNoun] at h
    | app g y =>
      simp only [toNoun, Noun.cell.injEq] at h
      rw [ihf h.1, ihx h.2]

/-- Every stored term passes Pure Nock's noun validation. -/
theorem toNoun_validates (t : Term) :
    ∃ T : Transcript, checkValidNoun (toNoun t) T = Result.accept ∧
      T.length = 2 * (toNoun t).leaves - 1 :=
  (Noun_Validation (toNoun t) _).1 rfl

/-- The nouns that store terms. -/
def TermNoun (n : Noun) : Prop := ∃ t, toNoun t = n

/-- Memory states. -/
inductive MSt
  | cell | S | K | I
  deriving DecidableEq, Repr

abbrev MLabel := MSt × Noun

/-- The state a noun's node carries. -/
def stOf : Noun → MSt
  | .atom 0 => .S
  | .atom 1 => .K
  | .atom _ => .I
  | .cell _ _ => .cell

/-- The local verifier of one memory node, `𝓛(F_mem, 2)`. -/
def Fm (l : MLabel) (o : List (Option MLabel)) : Prop :=
  ((l.2 = .atom 0 ∨ l.2 = .atom 1 ∨ l.2 = .atom 2) ∧ l.1 = stOf l.2 ∧ o = [none, none]) ∨
  (l.1 = .cell ∧ ∃ a b sa sb, l.2 = .cell a b ∧ o = [some (sa, a), some (sb, b)])

/-- The memory tree of a term. -/
def mtree : Term → SLT MLabel
  | .S => .node (.S, .atom 0) []
  | .K => .node (.K, .atom 1) []
  | .I => .node (.I, .atom 2) []
  | .app f x => .node (.cell, toNoun (f ⬝ x)) [mtree f, mtree x]

theorem mtree_label (t : Term) : (mtree t).label = (stOf (toNoun t), toNoun t) := by
  cases t <;> rfl

theorem Fm_leaf {l : MLabel} (h : Fm l [none, none]) :
    (l.2 = .atom 0 ∨ l.2 = .atom 1 ∨ l.2 = .atom 2) ∧ l.1 = stOf l.2 := by
  cases h with
  | inl h => exact ⟨h.1, h.2.1⟩
  | inr h =>
    cases h.2 with
    | intro a h' =>
      cases h' with
      | intro b h'' =>
        cases h'' with
        | intro sa h''' =>
          cases h''' with
          | intro sb h4 => cases h4.2

/-- A valid internal node is a cell with exactly two children, which carry
    its head and tail. -/
theorem Fm_node {l : MLabel} {cs : List (SLT MLabel)} (hne : cs ≠ []) (hlen : cs.length ≤ 2)
    (h : Fm l (outs 2 cs)) :
    ∃ c₁ c₂, cs = [c₁, c₂] ∧ l.1 = .cell ∧ l.2 = .cell c₁.label.2 c₂.label.2 := by
  match cs, hne, hlen, h with
  | [c], _, _, h =>
    cases h with
    | inl h => cases h.2.2
    | inr h =>
      cases h.2 with
      | intro a h' =>
        cases h' with
        | intro b h'' =>
          cases h'' with
          | intro sa h''' =>
            cases h''' with
            | intro sb h4 => simp [outs] at h4
  | [c₁, c₂], _, _, h =>
    cases h with
    | inl h => cases h.2.2
    | inr h =>
      cases h.2 with
      | intro a h' =>
        cases h' with
        | intro b h'' =>
          cases h'' with
          | intro sa h''' =>
            cases h''' with
            | intro sb h4 =>
              simp only [outs, List.map, List.length, Nat.sub_self, List.replicate,
                List.append_nil, List.cons.injEq, Option.some.injEq, and_true] at h4
              refine ⟨c₁, c₂, rfl, h.1, ?_⟩
              rw [h4.1, h4.2.1, h4.2.2]
  | _ :: _ :: _ :: _, _, h, _ => simp at h

/-- In a valid tree a node's state is determined by its noun. -/
theorem rvt_state {t : SLT MLabel} (h : RVT Fm 2 t) : t.label.1 = stOf t.label.2 := by
  cases h with
  | leaf hF => exact (Fm_leaf hF).2
  | node hne hlen hF _ _ =>
    cases Fm_node hne hlen hF with
    | intro c₁ h =>
      cases h with
      | intro c₂ h =>
        simp only [SLT.label]
        rw [h.2.2, h.2.1]
        rfl

theorem rvt_termNoun {t : SLT MLabel} (h : RVT Fm 2 t) : TermNoun t.label.2 := by
  induction h with
  | leaf hF =>
    cases (Fm_leaf hF).1 with
    | inl h => exact ⟨.S, h.symm⟩
    | inr h =>
      cases h with
      | inl h => exact ⟨.K, h.symm⟩
      | inr h => exact ⟨.I, h.symm⟩
  | node hne hlen hF _ _ ih =>
    cases Fm_node hne hlen hF with
    | intro c₁ h =>
      cases h with
      | intro c₂ h =>
        cases h.1
        cases ih c₁ (by simp) with
        | intro f hf =>
          cases ih c₂ (by simp) with
          | intro x hx => exact ⟨f ⬝ x, by simp only [toNoun, SLT.label]; rw [hf, hx, h.2.2]⟩

theorem mtree_rvt (t : Term) : RVT Fm 2 (mtree t) := by
  induction t with
  | S => exact .leaf (.inl ⟨.inl rfl, rfl, rfl⟩)
  | K => exact .leaf (.inl ⟨.inr (.inl rfl), rfl, rfl⟩)
  | I => exact .leaf (.inl ⟨.inr (.inr rfl), rfl, rfl⟩)
  | app f x ihf ihx =>
    refine .node (List.cons_ne_nil _ _) (by simp) ?_ ?_ ?_
    · refine .inr ⟨rfl, toNoun f, toNoun x, stOf (toNoun f), stOf (toNoun x), rfl, ?_⟩
      simp only [outs, List.map, mtree_label, List.length, Nat.sub_self, List.replicate,
        List.append_nil]
    · intro hF
      cases (Fm_leaf hF).1 with
      | inl h => cases h
      | inr h => cases h with
        | inl h => cases h
        | inr h => cases h
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      cases hc with
      | inl h => rw [h]; exact ihf
      | inr h => rw [h]; exact ihx

theorem termNoun_rvt {n : Noun} (h : TermNoun n) : ∃ t, RVT Fm 2 t ∧ t.label.2 = n := by
  cases h with
  | intro t ht => exact ⟨mtree t, mtree_rvt t, by rw [mtree_label, ht]⟩

theorem mem_unique {t₁ : SLT MLabel} (h₁ : RVT Fm 2 t₁) :
    ∀ {t₂}, RVT Fm 2 t₂ → t₁.label.2 = t₂.label.2 → t₁ = t₂ := by
  induction h₁ with
  | @leaf l hF =>
    intro t₂ h₂ he
    have hs₂ := rvt_state h₂
    cases h₂ with
    | @leaf l₂ hF₂ =>
      simp only [SLT.label] at he hs₂
      have : l = l₂ := Prod.ext ((Fm_leaf hF).2.trans (he ▸ hs₂.symm)) he
      rw [this]
    | node hne hlen hF₂ _ _ =>
      cases Fm_node hne hlen hF₂ with
      | intro c₁ h =>
        cases h with
        | intro c₂ h =>
          simp only [SLT.label] at he
          have ha := (Fm_leaf hF).1
          rw [he, h.2.2] at ha
          cases ha with
          | inl h => cases h
          | inr h => cases h with
            | inl h => cases h
            | inr h => cases h
  | @node l cs hne hlen hF _ _ ih =>
    intro t₂ h₂ he
    cases Fm_node hne hlen hF with
    | intro c₁ h =>
      cases h with
      | intro c₂ h =>
        cases h with
        | intro hcs h =>
          subst hcs
          cases h₂ with
          | @leaf l₂ hF₂ =>
            simp only [SLT.label] at he
            have ha := (Fm_leaf hF₂).1
            rw [← he, h.2] at ha
            cases ha with
            | inl h => cases h
            | inr h => cases h with
              | inl h => cases h
              | inr h => cases h
          | @node l₂ cs₂ hne₂ hlen₂ hF₂ _ hcs₂ =>
            cases Fm_node hne₂ hlen₂ hF₂ with
            | intro d₁ h' =>
              cases h' with
              | intro d₂ h' =>
                cases h' with
                | intro hcs' h' =>
                  subst hcs'
                  simp only [SLT.label] at he
                  have hn := h.2.symm.trans (he.trans h'.2)
                  simp only [Noun.cell.injEq] at hn
                  have e₁ := ih c₁ (by simp) (hcs₂ d₁ (by simp)) hn.1
                  have e₂ := ih c₂ (by simp) (hcs₂ d₂ (by simp)) hn.2
                  have el : l = l₂ := Prod.ext (h.1.trans h'.1.symm) he
                  rw [e₁, e₂, el]

/-- **SKI memory is traversable**: valid memory trees correspond one to one
    with the nouns that store terms. -/
theorem memory_traversable : Traversable TermNoun Fm 2 :=
  traversable_of (fun t => t.label.2) rvt_termNoun termNoun_rvt
    (fun h₁ h₂ he => mem_unique h₁ h₂ he)

/-- **State–data separation**: the atom states are the leaf states and
    `cell` has fanout 2. -/
def memory_stateTraversable : StateTraversable Fm 2 where
  leafSt s := s ≠ .cell
  fanout _ := 2
  leaf_iff := by
    intro t h
    have hs := rvt_state h
    cases h with
    | leaf hF =>
      refine ⟨fun _ => rfl, fun _ => ?_⟩
      simp only [SLT.label]
      have hl := Fm_leaf hF
      rw [hl.2]
      cases hl.1 with
      | inl h => rw [h]; intro h; cases h
      | inr h => cases h with
        | inl h => rw [h]; intro h; cases h
        | inr h => rw [h]; intro h; cases h
    | node hne hlen hF _ _ =>
      cases Fm_node hne hlen hF with
      | intro c₁ h =>
        cases h with
        | intro c₂ h =>
          refine ⟨fun hl => absurd h.2.1 hl, fun hc => ?_⟩
          rw [h.1] at hc
          cases hc
  fanout_pos _ _ := ⟨by decide, Nat.le_refl 2⟩
  fanout_shape := by
    intro s d o hs hF
    cases hF with
    | inl h =>
      exfalso
      apply hs
      show s ≠ .cell
      rw [show s = stOf d from h.2.1]
      cases h.1 with
      | inl h' => rw [show d = _ from h']; intro c; cases c
      | inr h' => cases h' with
        | inl h' => rw [show d = _ from h']; intro c; cases c
        | inr h' => rw [show d = _ from h']; intro c; cases c
    | inr h =>
      cases h.2 with
      | intro a h' =>
        cases h' with
        | intro b h'' =>
          cases h'' with
          | intro sa h''' =>
            cases h''' with
            | intro sb h4 => exact ⟨[(sa, a), (sb, b)], rfl, h4.2⟩

end SkiZk
