import Ski.JetTable
import Ski.Composed

open Term

/-!
# Public closures: jets over a heap with private cells

The jet check reads whole terms: `RootsOK` reads the term under each root
and under each global a body names (`Jet.genv`).  In the composed heap
(`CompM.cHeap`) the addresses `[3, 3 + N + W)` are private, the bit slots
and the witness region, and public cells point into them: the encoding of
the bits, and each statement's application to the witness.  A check over
the blank heap, which is what the verifier holds, then says nothing about
the filled heap the run uses; a global at the first `S` of the blank heap,
the region, would compute whatever the prover wrote there.

**The rule** (Avon's `docs/ZK-JETS.md` §4): admit a root or a global only
when every cell `termAt` visits from it lies outside the private addresses
(`pubAtG`).  Two heaps that agree outside them read the same term there
(`termAt_public`).  So the decided checks `rootsOKB` and `publicB` over the
blank heap give `RootsOK` over every filled one of the same size
(`rootsOK_filled`), the hypothesis the jet steps read (`JStep.inst`,
`instRow_jstep`).  An instantiation's arguments are unconstrained: they are
pointers on the stack, and `inst_sound_g` substitutes them as arguments.

`JetTable.jetTable` applies the rule when given the private addresses,
skipping any cell whose closure reaches one, for roots and for globals
alike; `jetStmtC` is the verifier's check of a composed statement's jet
table (`jetStmtC_sound`).
-/

namespace Air

open Mach Compose CompM

/-- **Every cell `termAt` visits from `a` is public**, and is a term cell,
    through the reader `g` with fuel `f`. -/
def pubAtG (g : Nat → Option Cell) (priv : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, a =>
    !priv a &&
      match g a with
      | some .S => true
      | some .K => true
      | some .I => true
      | some (.app u x) => pubAtG g priv f u && pubAtG g priv f x
      | _ => false

/-- **Two readers agreeing on the public addresses read the same term at a
    public closure**, and see the same closure. -/
theorem termAtG_public {g g' : Nat → Option Cell} {priv : Nat → Bool}
    (hag : ∀ i, priv i = false → g i = g' i) :
    ∀ f a, pubAtG g priv f a = true → termAtG g' f a = termAtG g f a ∧ pubAtG g' priv f a = true
  | 0, _, h => by cases h
  | f + 1, a, h => by
    unfold pubAtG at h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hp, hc⟩ := h
    have e : g' a = g a := (hag a hp).symm
    unfold termAtG pubAtG
    rw [e, hp]
    cases hga : g a with
    | none => rw [hga] at hc; cases hc
    | some c =>
      rw [hga] at hc
      cases c with
      | app u x =>
        dsimp only at hc ⊢
        rw [Bool.and_eq_true] at hc
        obtain ⟨hu, hx⟩ := termAtG_public hag f u hc.1
        obtain ⟨xu, xx⟩ := termAtG_public hag f x hc.2
        rw [hu, xu, hx, xx]
        exact ⟨rfl, rfl⟩
      | S => exact ⟨rfl, rfl⟩
      | K => exact ⟨rfl, rfl⟩
      | I => exact ⟨rfl, rfl⟩
      | nil => cases hc
      | cons _ _ => cases hc
      | atom _ => cases hc

/-- **`termAt_public`**: two heaps agreeing on the public addresses read the
    same term at a public closure. -/
theorem termAt_public {h h' : List Cell} {priv : Nat → Bool}
    (hag : ∀ i, priv i = false → h[i]? = h'[i]?) {f a : Nat}
    (hp : pubAtG (fun i => h[i]?) priv f a = true) : termAt h' f a = termAt h f a := by
  rw [termAt_G, termAt_G]
  exact (termAtG_public (g := fun i => h[i]?) (g' := fun i => h'[i]?) hag f a hp).1

/-- One root and its jet's globals, public, through a reader. -/
def pubJetB (g : Nat → Option Cell) (priv : Nat → Bool) (F : Nat) (jets : List Jet) (a j : Nat) : Bool :=
  pubAtG g priv F a &&
    match jets[j]? with
    | some J => J.body.vars.all fun x => J.xs.contains x || pubAtG g priv F (J.genv x)
    | none => true

/-- **Public closures, decided**: every cell `RootsOK` reads, over an array
    copy of the heap, lies outside `priv`. -/
def publicB (h0 : List Cell) (priv : Nat → Bool) (roots : List (Nat × Nat)) (jets : List Jet) : Bool :=
  let A := h0.toArray
  roots.all fun (a, j) => pubJetB (fun i => A[i]?) priv (h0.length + 1) jets a j

/-- **Public closures**: the root and each global its jet's body uses. -/
def PublicJ (priv : Nat → Bool) (h0 : List Cell) (roots : List (Nat × Nat)) (jets : List Jet) : Prop :=
  ∀ a g, (a, g) ∈ roots →
    pubAtG (fun i => h0[i]?) priv (h0.length + 1) a = true ∧
    ∀ J, jets[g]? = some J → ∀ x, Occ x J.body → x ∉ J.xs →
      pubAtG (fun i => h0[i]?) priv (h0.length + 1) (J.genv x) = true

theorem publicB_sound {h0 : List Cell} {priv : Nat → Bool} {roots : List (Nat × Nat)} {jets : List Jet}
    (h : publicB h0 priv roots jets = true) : PublicJ priv h0 roots jets := by
  intro a g hm
  have hA : (fun (i : Nat) => h0.toArray[i]?) = (fun (i : Nat) => h0[i]?) := by
    funext i; simp
  have h1 : pubJetB (fun i => h0.toArray[i]?) priv (h0.length + 1) jets a g = true :=
    List.all_eq_true.1 h (a, g) hm
  rw [hA] at h1
  unfold pubJetB at h1
  rw [Bool.and_eq_true] at h1
  refine ⟨h1.1, fun J hJ x hx hn => ?_⟩
  have h2 := h1.2
  rw [hJ] at h2
  have hx' : x ∈ J.body.vars := (OTerm.mem_vars x J.body).1 (OTerm.mem_of_occ hx)
  have := List.all_eq_true.1 h2 x hx'
  rw [Bool.or_eq_true] at this
  rcases this with hc | hs
  · exact absurd (List.contains_iff_mem.1 hc) hn
  · exact hs

/-- **Licensed roots carry to a heap that agrees on the public addresses**,
    of the same length, when their closures are public. -/
theorem rootsOK_public {h0 h1 : List Cell} {priv : Nat → Bool} {roots : List (Nat × Nat)} {jets : List Jet}
    (hr : RootsOK h0 roots jets) (hp : PublicJ priv h0 roots jets)
    (hag : ∀ i, priv i = false → h0[i]? = h1[i]?) (hl : h1.length = h0.length) :
    RootsOK h1 roots jets := by
  intro a g hm
  obtain ⟨J, hJ, γ, ht, hgl⟩ := hr a g hm
  obtain ⟨pa, pg⟩ := hp a g hm
  refine ⟨J, hJ, γ, ?_, fun x hx hn => ?_⟩
  · rw [hl, termAt_public hag pa]; exact ht
  · rw [hl, termAt_public hag (pg J hJ x hx hn)]; exact hgl x hx hn

-- ---------------------------------------------------------------------------
-- The composed heap
-- ---------------------------------------------------------------------------

/-- The composed heap's private addresses: `N` bit slots and a region of
    `W` cells, from address 3. -/
def privC (N W : Nat) (a : Nat) : Bool := decide (3 ≤ a) && decide (a < 3 + N + W)

theorem privC_false {N W a : Nat} (h : privC N W a = false) : a < 3 ∨ N + 3 + W ≤ a := by
  unfold privC at h
  rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not] at h
  rcases h with h | h
  · exact .inl (Nat.lt_of_not_le h)
  · refine .inr ?_
    rw [Nat.add_comm N 3]
    exact Nat.le_of_not_lt h

/-- **Licensed over the blank heap, licensed over every filled one.**  The
    verifier checks the roots (`rootsOKB`) and their closures (`publicB`)
    over the composed heap with every bit clear and the region `S` cells;
    the roots are then licensed over the heap of every witness with a
    region of `W` cells. -/
theorem rootsOK_filled {shp : BT} {W : Nat} {Ps : List Term} {roots : List (Nat × Nat)} {jets : List Jet}
    (hr : rootsOKB (CompM.cMachine (fun _ => false) shp (List.replicate W .S) Ps).heap roots jets = true)
    (hp : publicB (CompM.cMachine (fun _ => false) shp (List.replicate W .S) Ps).heap
      (privC (BT.nleaves shp) W) roots jets = true)
    (ρ : Nat → Bool) (region : List Cell) (hW : region.length = W) :
    RootsOK (CompM.cMachine ρ shp region Ps).heap roots jets := by
  have hl : (List.replicate W Cell.S).length = region.length := by rw [List.length_replicate, hW]
  have hpub := CompM.cMachine_public (fun _ => false) ρ shp (List.replicate W .S) region Ps hl
  refine rootsOK_public (rootsOKB_sound hr) (publicB_sound hp) (fun i hi => ?_) hpub.2.2.2.1.symm
  refine hpub.2.2.2.2.2 i ?_
  rw [List.length_replicate]
  exact privC_false hi

-- ---------------------------------------------------------------------------
-- The verifier's check of a composed statement's jet table
-- ---------------------------------------------------------------------------

/-- **The jet table of a composed statement**, over its blank heap, with
    the closure rule. -/
def jetTableC (shp : BT) (W : Nat) (Ps : List Term) (tmpls : List (List Nat × OTerm)) :
    List (Nat × Nat) × List Jet :=
  JetTable.jetTable (CompM.cMachine (fun _ => false) shp (List.replicate W .S) Ps).heap tmpls
    (priv := privC (BT.nleaves shp) W)

/-- **The verifier's check**: the text is the jet table Lean computes from
    the templates over the statement's blank heap, its roots licensed and
    their closures public. -/
def jetStmtC (text : String) (shp : BT) (W : Nat) (Ps : List Term) (tmpls : List (List Nat × OTerm)) : Bool :=
  let h := (CompM.cMachine (fun _ => false) shp (List.replicate W .S) Ps).heap
  let (roots, jets) := jetTableC shp W Ps tmpls
  text == JetTable.tableText roots jets && rootsOKB h roots jets && publicB h (privC (BT.nleaves shp) W) roots jets

/-- **An accepted jet table is licensed for every witness**: its roots are
    licensed over the heap of every fill of the statement's bits and a
    region of `W` cells.  What is licensed is the table Lean recomputes;
    the text is tied to it by byte equality alone, and the prover's reader
    of the text (`parse_jets`, `bench/plonky3/src/jets.rs`) is trusted to
    read it back, as for the corpus's `jets statement`.  The text is not
    injective on `Jet`s (it drops variable names), only on the cells an
    instantiation writes (`symCells_icells`). -/
theorem jetStmtC_sound {text : String} {shp : BT} {W : Nat} {Ps : List Term} {tmpls : List (List Nat × OTerm)}
    (h : jetStmtC text shp W Ps tmpls = true) (ρ : Nat → Bool) (region : List Cell) (hW : region.length = W) :
    RootsOK (CompM.cMachine ρ shp region Ps).heap (jetTableC shp W Ps tmpls).1 (jetTableC shp W Ps tmpls).2 := by
  unfold jetStmtC at h
  simp only [Bool.and_eq_true] at h
  exact rootsOK_filled h.1.2 h.2 ρ region hW

end Air
