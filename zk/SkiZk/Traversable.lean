import Mathlib.Logic.Function.Defs

/-!
# Recursively verifiable trees and traversability

The definitions of the Pure Nock paper (`paper/main.tex` of `pure-nock-lean`,
Def. RVT at line 683, Def. traversable at 750, Def.
state_data_separation at 768), stated over an arbitrary label type.  Pure
Nock formalizes nouns, validation and fingerprints; it states these three
definitions only in prose, so they are formalized here.

A stateful labeled tree carries a label at every node and at most `n`
children.  The paper pads a node's child labels to `n` with `⊥`; `outs`
does the same with `none`.  A tree is recursively verifiable over a local
verifier `F` when every internal node passes `F` against its children's
labels, every child is recursively verifiable, and a node is a leaf exactly
when `F` accepts it against `n` copies of `⊥`.
-/

namespace SkiZk

/-- A stateful labeled tree (the paper's `𝓛_SLT`). -/
inductive SLT (L : Type) where
  | node : L → List (SLT L) → SLT L

namespace SLT

variable {L : Type}

def label : SLT L → L
  | .node l _ => l

def children : SLT L → List (SLT L)
  | .node _ cs => cs

end SLT

/-- The `n` output labels of a node: the children's labels, padded with `⊥`. -/
def outs {L : Type} (n : Nat) (cs : List (SLT L)) : List (Option L) :=
  cs.map (fun c => some c.label) ++ List.replicate (n - cs.length) none

/-- The paper's `𝓛^{F,n}_RVT`.  `F l o` is membership of `(l, o)` in the
    labeling language `𝓛(F, n)`. -/
inductive RVT {L : Type} (F : L → List (Option L) → Prop) (n : Nat) : SLT L → Prop
  | leaf {l : L} (h : F l (List.replicate n none)) : RVT F n (.node l [])
  | node {l : L} {cs : List (SLT L)} (hne : cs ≠ []) (hlen : cs.length ≤ n)
      (hF : F l (outs n cs)) (hleaf : ¬ F l (List.replicate n none))
      (hcs : ∀ c ∈ cs, RVT F n c) : RVT F n (.node l cs)

/-- Def. state_data_separation: labels split as state × data, a set of leaf
    states marks exactly the leaves, and every other state `s` fixes a
    fanout in `[1, n]`: `F` accepts `(s, d)` only against `fanout s`
    non-null outputs followed by `⊥`s. -/
structure StateTraversable {St D : Type} (F : St × D → List (Option (St × D)) → Prop)
    (n : Nat) where
  leafSt : St → Prop
  fanout : St → Nat
  leaf_iff : ∀ {t : SLT (St × D)}, RVT F n t → (leafSt t.label.1 ↔ t.children = [])
  fanout_pos : ∀ s, ¬ leafSt s → 1 ≤ fanout s ∧ fanout s ≤ n
  fanout_shape : ∀ {s d o}, ¬ leafSt s → F (s, d) o →
    ∃ xs : List (St × D), xs.length = fanout s ∧
      o = xs.map some ++ List.replicate (n - fanout s) none

/-- Def. traversable, for one component (`k = 1`): a bijection between the
    language's accepted instances and the recursively verifiable trees. -/
def Traversable {X L : Type} (lang : X → Prop) (F : L → List (Option L) → Prop) (n : Nat) :
    Prop :=
  ∃ φ : {x // lang x} → {t // RVT F n t}, Function.Bijective φ

/-- A language is traversable when some key read off a tree's labels is
    sound (every tree's key is accepted), complete (every accepted instance
    is some tree's key) and unique (a tree is determined by its key). -/
theorem traversable_of {X L : Type} {lang : X → Prop} {F : L → List (Option L) → Prop}
    {n : Nat} (key : SLT L → X)
    (sound : ∀ {t}, RVT F n t → lang (key t))
    (complete : ∀ {x}, lang x → ∃ t, RVT F n t ∧ key t = x)
    (unique : ∀ {t₁ t₂}, RVT F n t₁ → RVT F n t₂ → key t₁ = key t₂ → t₁ = t₂) :
    Traversable lang F n := by
  refine ⟨fun x => ⟨Classical.choose (complete x.2), (Classical.choose_spec (complete x.2)).1⟩,
    ?_, ?_⟩
  · intro x y h
    have hx := (Classical.choose_spec (complete x.2)).2
    have hy := (Classical.choose_spec (complete y.2)).2
    have h' := congrArg (fun t : {t // RVT F n t} => key t.1) h
    simp only at h'
    rw [hx, hy] at h'
    exact Subtype.ext h'
  · intro t
    refine ⟨⟨key t.1, sound t.2⟩, ?_⟩
    have hs := Classical.choose_spec (complete (sound t.2))
    exact Subtype.ext (unique hs.1 t.2 hs.2)

end SkiZk
