import Ski.ComposeX

set_option linter.unusedSectionVars false

open Term

/-!
# Incremental composition without recursion

A chain of proofs: each stage proves a statement of its own, by its own
prover, and later stages' statements are computed from earlier ones,
including the values they publish (the hand-off).  The verifier checks
every proof and that each statement is the one the chain computes; no
proof verifies another, so the cost grows with the chain, and nothing is
recursive.

**The construction** (`chain2`).  From proof systems for two relations and
a public link from the first stage's statements to the second's, a proof
system for the chain relation: the first stage's relation, and the
second's at the linked statement.  It is complete, knowledge-sound (the
two extractors, each at its own statement) and zero knowledge, the
simulator the pair of the stages' simulators.  It is a proof system of the
same kind, so chains of any length are `chain2` iterated.

Zero knowledge is stated for the pair of distributions, indistinguishable
when each component is (`ChainIndist`): the assumption that the two
proofs' randomness is independent, under which the standard hybrid
argument gives the joint indistinguishability.  The hybrid argument itself
is not formalized; the interface's indistinguishability is abstract.

**For composed statements** (`chainX_real`): two statements that share a
public hand-off value `o`, each a formula over `o`, proved separately,
prove the conjunction of the two formulas, its realizer the pair of the
read-backs.  The statement digest each proof carries
(`bench/plonky3/src/stmt.rs`) binds `o` into that proof's transcript, so a
prover cannot change the hand-off after its challenges.  A hidden hand-off
needs a binding commitment in its place, which needs a hash computed
outside the reduction: a data jet (`Ski/DataJet.lean`).
-/

namespace Chain

open Compose

/-- **A proof system** for a relation over statements `T` and witnesses
    `W`, the interface of `Compose.EvalPS` with the witness type free:
    complete, knowledge-sound by an extractor, zero knowledge by a
    simulator, idealized. -/
structure PS (T W : Type) (R : T → W → Prop) where
  Proof : Type
  Dist : Type
  prove : T → W → Dist
  supp : Dist → Proof → Prop
  verify : T → Proof → Prop
  ext : T → Proof → W
  sim : T → Dist
  indist : Dist → Dist → Prop
  indist_equiv : Equivalence indist
  complete : ∀ t w, R t w → (∃ π, supp (prove t w) π) ∧ ∀ π, supp (prove t w) π → verify t π
  knowledge : ∀ t π, verify t π → R t (ext t π)
  zk : ∀ t w, R t w → indist (prove t w) (sim t)

/-- The composed statements' interface is one. -/
def ofEval {T : Type} {R : T → BT → Term → Prop} (ps : EvalPS T R) : PS T (BT × Term) (fun t w => R t w.1 w.2) where
  Proof := ps.Proof
  Dist := ps.Dist
  prove t w := ps.prove t w.1 w.2
  supp := ps.supp
  verify := ps.verify
  ext := ps.ext
  sim := ps.sim
  indist := ps.indist
  indist_equiv := ps.indist_equiv
  complete t w h := ps.complete t w.1 w.2 h
  knowledge t π h := ps.knowledge t π h
  zk t w h := ps.zk t w.1 w.2 h

/-- Two distributions, sampled independently, are indistinguishable from
    two others when each is from its own. -/
def ChainIndist {D₁ D₂ : Type} (i₁ : D₁ → D₁ → Prop) (i₂ : D₂ → D₂ → Prop) (d d' : D₁ × D₂) : Prop :=
  i₁ d.1 d'.1 ∧ i₂ d.2 d'.2

/-- **A two-stage chain.**  The second stage's statement is the link of the
    first's; a chain proof is a proof of each; the chain relation is the
    first stage's relation and the second's at the linked statement. -/
def chain2 {T₁ T₂ W₁ W₂ : Type} {R₁ : T₁ → W₁ → Prop} {R₂ : T₂ → W₂ → Prop}
    (ps₁ : PS T₁ W₁ R₁) (ps₂ : PS T₂ W₂ R₂) (link : T₁ → T₂) :
    PS T₁ (W₁ × W₂) (fun t w => R₁ t w.1 ∧ R₂ (link t) w.2) where
  Proof := ps₁.Proof × ps₂.Proof
  Dist := ps₁.Dist × ps₂.Dist
  prove t w := (ps₁.prove t w.1, ps₂.prove (link t) w.2)
  supp d π := ps₁.supp d.1 π.1 ∧ ps₂.supp d.2 π.2
  verify t π := ps₁.verify t π.1 ∧ ps₂.verify (link t) π.2
  ext t π := (ps₁.ext t π.1, ps₂.ext (link t) π.2)
  sim t := (ps₁.sim t, ps₂.sim (link t))
  indist := ChainIndist ps₁.indist ps₂.indist
  indist_equiv := {
    refl := fun d => ⟨ps₁.indist_equiv.refl _, ps₂.indist_equiv.refl _⟩
    symm := fun h => ⟨ps₁.indist_equiv.symm h.1, ps₂.indist_equiv.symm h.2⟩
    trans := fun h h' => ⟨ps₁.indist_equiv.trans h.1 h'.1, ps₂.indist_equiv.trans h.2 h'.2⟩ }
  complete t w h := by
    obtain ⟨⟨π₁, h₁⟩, v₁⟩ := ps₁.complete t w.1 h.1
    obtain ⟨⟨π₂, h₂⟩, v₂⟩ := ps₂.complete (link t) w.2 h.2
    exact ⟨⟨(π₁, π₂), h₁, h₂⟩, fun π hπ => ⟨v₁ π.1 hπ.1, v₂ π.2 hπ.2⟩⟩
  knowledge t π h := ⟨ps₁.knowledge t π.1 h.1, ps₂.knowledge (link t) π.2 h.2⟩
  zk t w h := ⟨ps₁.zk t w.1 h.1, ps₂.zk (link t) w.2 h.2⟩

/-- **The chain's knowledge soundness**, spelled out: a chain proof that
    verifies yields, by the stages' extractors, witnesses for both stages,
    the second at the statement the first's links to. -/
theorem chain2_knowledge {T₁ T₂ W₁ W₂ : Type} {R₁ : T₁ → W₁ → Prop} {R₂ : T₂ → W₂ → Prop}
    (ps₁ : PS T₁ W₁ R₁) (ps₂ : PS T₂ W₂ R₂) (link : T₁ → T₂) (t : T₁) (π₁ : ps₁.Proof) (π₂ : ps₂.Proof)
    (h₁ : ps₁.verify t π₁) (h₂ : ps₂.verify (link t) π₂) :
    R₁ t (ps₁.ext t π₁) ∧ R₂ (link t) (ps₂.ext (link t) π₂) :=
  (chain2 ps₁ ps₂ link).knowledge t (π₁, π₂) ⟨h₁, h₂⟩

/-- A three-stage chain is `chain2` iterated: its relation is the three
    stages' in turn. -/
theorem chain3_rel {T₁ T₂ T₃ W₁ W₂ W₃ : Type} {R₁ : T₁ → W₁ → Prop} {R₂ : T₂ → W₂ → Prop}
    {R₃ : T₃ → W₃ → Prop} (ps₁ : PS T₁ W₁ R₁) (ps₂ : PS T₂ W₂ R₂) (ps₃ : PS T₃ W₃ R₃)
    (l₁ : T₁ → T₂) (l₂ : T₁ → T₃) (t : T₁) (π : (chain2 (chain2 ps₁ ps₂ l₁) ps₃ l₂).Proof)
    (h : (chain2 (chain2 ps₁ ps₂ l₁) ps₃ l₂).verify t π) :
    R₁ t (ps₁.ext t π.1.1) ∧ R₂ (l₁ t) (ps₂.ext (l₁ t) π.1.2) ∧ R₃ (l₂ t) (ps₃.ext (l₂ t) π.2) := by
  have := (chain2 (chain2 ps₁ ps₂ l₁) ps₃ l₂).knowledge t π h
  exact ⟨this.1.1, this.1.2, this.2⟩

-- ---------------------------------------------------------------------------
-- Composed statements that share a public hand-off
-- ---------------------------------------------------------------------------

/-- **Two composed statements over a shared public value `o`, proved
    separately, prove the conjunction of their formulas**: the realizer is
    the pair of the two read-backs. -/
theorem chainX_real {F₁ F₂ : Term → XS} {o : Term} {β₁ β₂ : BT} {w₁ w₂ : Term}
    (hw₁ : (F₁ o).wf = true) (hw₂ : (F₂ o).wf = true)
    (h₁ : AcceptsX (F₁ o).toXF β₁ w₁) (h₂ : AcceptsX (F₂ o).toXF β₂ w₂) :
    Real (.and ((F₁ o).toXF.form []) ((F₂ o).toXF.form []))
      (pairT (readBackX (F₁ o).toXF β₁ w₁ []) (readBackX (F₂ o).toXF β₂ w₂ [])) :=
  ⟨_, _, pairT_app _ _, real_of_acceptedXS h₁ hw₁, real_of_acceptedXS h₂ hw₂⟩

/-- **The chain of two composed statements over the interface**: the chain
    of the composed proof system with itself, the second statement linked
    from the first through the hand-off, is knowledge-sound to the
    conjunction of the two formulas. -/
theorem chainX_knowledge (ps : EvalPS EvalStmt EvalRel) (F₁ F₂ : Term → XS) (o : Term)
    (hw₁ : (F₁ o).wf = true) (hw₂ : (F₂ o).wf = true)
    (π : (chain2 (ofEval ps) (ofEval ps) (fun _ => evalStmtOfX (F₂ o).toXF)).Proof)
    (h : (chain2 (ofEval ps) (ofEval ps) (fun _ => evalStmtOfX (F₂ o).toXF)).verify (evalStmtOfX (F₁ o).toXF) π) :
    Real (.and ((F₁ o).toXF.form []) ((F₂ o).toXF.form []))
      (pairT (readBackX (F₁ o).toXF (ps.ext (evalStmtOfX (F₁ o).toXF) π.1).1 (ps.ext (evalStmtOfX (F₁ o).toXF) π.1).2 [])
        (readBackX (F₂ o).toXF (ps.ext (evalStmtOfX (F₂ o).toXF) π.2).1 (ps.ext (evalStmtOfX (F₂ o).toXF) π.2).2 [])) := by
  have hk := (chain2 (ofEval ps) (ofEval ps) (fun _ => evalStmtOfX (F₂ o).toXF)).knowledge _ π h
  exact chainX_real hw₁ hw₂ hk.1 hk.2

end Chain
