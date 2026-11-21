import Ski.HnfSound
open Term

/-!
# Productive S-terms: the easy half of *Dance of the Starlings*, Question 5

A closed S-term is *productive* when its Böhm tree has no ⊥.  `Pk k t` says the Böhm tree
of `t` is defined to depth `k`, read off head reduction (`HnfSound.HeadChain`): `t` head-
reduces to a frame of at most two items, each of which satisfies `Pk (k-1)`.

`clsTable` is a 39-class S-model (class 0 = `S`, class 37 = rejected, absorbing).  This
module proves, inside the axiom gate, that every term of a non-rejected class is productive
(`easy`).  The converse (every rejected term is non-productive) is the hard half; it is
certified outside Lean (`notes/checks/s15/cert/`) and is **not** claimed here.  All facts
about the table are finite checks by `decide +kernel`.
-/

namespace HnfProd
open HnfS HnfSound

def clsTable : List (List Nat) := [
  [1, 2, 4, 5, 8, 9, 10, 11, 9, 18, 9, 18, 19, 10, 18, 18, 18, 20, 18, 9, 18, 8, 9, 18, 18, 18, 18, 18, 20, 18, 9, 9, 18, 18, 18, 18, 18, 37, 9],
  [3, 6, 12, 13, 21, 22, 13, 7, 30, 9, 31, 20, 12, 13, 32, 15, 16, 17, 18, 38, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38],
  [7, 14, 15, 23, 33, 33, 23, 33, 33, 33, 33, 33, 33, 23, 33, 33, 33, 27, 33, 33, 33, 33, 33, 33, 24, 33, 27, 27, 27, 29, 33, 33, 33, 33, 24, 27, 24, 37, 33],
  [6, 15, 24, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [16, 25, 27, 24, 24, 29, 24, 24, 29, 29, 29, 29, 24, 24, 29, 29, 29, 24, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [17, 26, 24, 34, 24, 24, 34, 24, 24, 24, 24, 24, 24, 34, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 29, 24, 24, 24, 24, 24, 24, 24, 37, 24],
  [13, 23, 24, 34, 24, 29, 36, 29, 29, 29, 29, 29, 24, 36, 29, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [15, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29, 29, 29, 29, 29, 29, 37, 29, 37, 37, 37, 37, 29, 29, 29, 29, 37, 37, 37, 37, 29],
  [27, 27, 24, 24, 24, 29, 24, 24, 29, 29, 29, 29, 24, 24, 29, 29, 29, 24, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [28, 35, 24, 36, 24, 24, 36, 24, 24, 24, 24, 24, 24, 36, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 29, 24, 24, 24, 24, 24, 24, 24, 37, 24],
  [24, 24, 24, 24, 24, 29, 24, 29, 29, 29, 29, 29, 24, 24, 29, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [7, 33, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [13, 33, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [24, 36, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 37, 29, 37, 29, 29, 29, 29, 29, 37, 37, 37, 37, 37, 37, 37, 29, 29, 29, 37, 37, 37, 37, 37, 29],
  [29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 37, 29, 37, 29, 29, 29, 29, 29, 37, 37, 37, 37, 37, 37, 37, 29, 29, 37, 37, 37, 37, 37, 37, 29],
  [24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29, 29, 29, 29, 29, 29, 37, 29, 37, 37, 37, 37, 29, 29, 29, 29, 37, 37, 37, 37, 29],
  [23, 29, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [35, 27, 24, 24, 24, 29, 24, 24, 29, 29, 29, 29, 24, 24, 29, 29, 29, 24, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [24, 24, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [16, 33, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [17, 27, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [24, 29, 29, 29, 29, 29, 29, 37, 29, 29, 29, 29, 29, 29, 37, 37, 37, 37, 29, 29, 29, 29, 29, 37, 37, 37, 37, 37, 37, 37, 29, 29, 37, 37, 37, 37, 37, 37, 29],
  [29, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [29, 24, 29, 29, 29, 29, 29, 37, 29, 29, 29, 29, 29, 29, 37, 37, 37, 37, 29, 29, 29, 29, 29, 37, 37, 37, 37, 37, 37, 37, 29, 29, 37, 37, 37, 37, 37, 37, 29],
  [34, 29, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [29, 29, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [33, 29, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [27, 27, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [28, 27, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29],
  [24, 24, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 37, 29, 37, 29, 29, 29, 29, 29, 37, 37, 37, 37, 37, 37, 37, 29, 29, 29, 37, 37, 37, 37, 37, 29],
  [29, 29, 29, 29, 29, 29, 29, 37, 29, 29, 29, 29, 29, 29, 37, 37, 37, 37, 29, 29, 29, 29, 29, 37, 37, 37, 37, 37, 37, 37, 29, 29, 37, 37, 37, 37, 37, 37, 29],
  [36, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [24, 29, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [24, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37],
  [35, 27, 29, 24, 29, 29, 24, 29, 29, 29, 29, 29, 29, 24, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 37, 29]]

def reachPairs : List (Nat × Nat) := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (7, 12), (8, 8), (8, 10), (9, 9), (9, 10), (9, 12), (9, 17), (10, 10), (11, 10), (11, 11), (12, 12), (13, 12), (14, 13), (15, 12), (15, 14), (16, 12), (16, 15), (17, 12), (17, 16), (18, 9), (18, 10), (18, 12), (18, 17), (18, 18), (18, 19), (18, 20), (18, 27), (18, 28), (19, 10), (20, 10), (20, 12), (20, 20), (21, 12), (22, 12), (23, 12), (23, 21), (24, 12), (24, 21), (24, 22), (24, 23), (24, 25), (24, 26), (24, 30), (24, 32), (24, 33), (24, 34), (25, 12), (25, 22), (26, 12), (26, 24), (27, 12), (27, 14), (27, 21), (27, 22), (27, 26), (27, 30), (27, 32), (28, 12), (28, 26), (29, 12), (29, 21), (29, 22), (29, 23), (29, 25), (29, 26), (29, 30), (29, 31), (29, 32), (29, 33), (29, 34), (29, 35), (29, 37), (30, 12), (31, 12), (32, 12), (33, 12), (33, 21), (33, 29), (33, 30), (34, 12), (34, 33), (35, 12), (35, 26), (35, 32), (36, 12), (36, 32), (37, 9), (37, 10), (37, 12), (37, 18), (37, 20), (37, 21), (37, 22), (37, 23), (37, 25), (37, 26), (37, 27), (37, 28), (37, 29), (37, 30), (37, 31), (37, 32), (37, 33), (37, 34), (37, 36), (37, 37), (38, 12)]

/-- The class algebra. -/
def γ (a b : Nat) : Nat := (clsTable.getD a []).getD b 37

/-- The class of a term (`K` and `I` are rejected; only pure S-terms matter). -/
def cls : Term → Nat
  | .S => 0
  | .K => 37
  | .I => 37
  | .app f x => γ (cls f) (cls x)

def r39 : List Nat := List.range 39

def closedB : Bool := r39.all fun a => r39.all fun b => decide (γ a b < 39)
def slawB : Bool :=
  r39.all fun a => r39.all fun b => r39.all fun c => γ (γ (γ 0 a) b) c == γ (γ a c) (γ b c)
def absorbB : Bool := r39.all fun a => γ 37 a == 37 && γ a 37 == 37
def startB : Bool := reachPairs.contains (0, 0)
def pairsClosedB : Bool :=
  reachPairs.all fun p => reachPairs.all fun q => reachPairs.contains (γ p.1 q.1, β p.2 q.2)
def b1B : Bool := reachPairs.all fun p => p.1 == 37 || p.2 != 36

theorem closedB_eq : closedB = true := by decide +kernel
theorem slawB_eq : slawB = true := by decide +kernel
theorem absorbB_eq : absorbB = true := by decide +kernel
theorem startB_eq : startB = true := by decide +kernel
theorem pairsClosedB_eq : pairsClosedB = true := by decide +kernel
theorem b1B_eq : b1B = true := by decide +kernel

theorem γ_lt {a b : Nat} (ha : a < 39) (hb : b < 39) : γ a b < 39 := by
  have h := closedB_eq
  simp only [closedB, r39, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h a ha b hb

/-- The class table is an S-model: all 59,319 triples. -/
theorem slaw {a b c : Nat} (ha : a < 39) (hb : b < 39) (hc : c < 39) :
    γ (γ (γ 0 a) b) c = γ (γ a c) (γ b c) := by
  have h := slawB_eq
  simp only [slawB, r39, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h a ha b hb c hc

theorem absorbL {a : Nat} (ha : a < 39) : γ 37 a = 37 := by
  have h := absorbB_eq
  simp only [absorbB, r39, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact (h a ha).1

theorem absorbR {a : Nat} (ha : a < 39) : γ a 37 = 37 := by
  have h := absorbB_eq
  simp only [absorbB, r39, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact (h a ha).2

theorem cls_lt {t : Term} (ht : PureS t) : cls t < 39 := by
  induction ht with
  | S => decide
  | app _ _ ihf ihx => exact γ_lt ihf ihx

/-- The class is invariant under one weak step of a pure S-term. -/
theorem wstep_cls {t t' : Term} (h : WStep t t') (ht : PureS t) : cls t' = cls t := by
  induction h with
  | S f g x =>
    obtain ⟨h1, hx⟩ := ht.app_inv
    obtain ⟨h2, hg⟩ := h1.app_inv
    obtain ⟨_, hf⟩ := h2.app_inv
    simp only [cls]
    exact (slaw (cls_lt hf) (cls_lt hg) (cls_lt hx)).symm
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | left x _ ih => simp only [cls, ih ht.app_inv.1]
  | right f _ ih => simp only [cls, ih ht.app_inv.2]

theorem wsteps_cls {t u : Term} (h : WSteps t u) (ht : PureS t) : cls u = cls t := by
  induction h with
  | refl => rfl
  | step h1 _ ih =>
    have hp := (HnfS.wstep_pure h1 ht).1
    exact (ih hp).trans (wstep_cls h1 ht)

/-- Every pure S-term's (class, block) pair is one of the 115 reachable pairs. -/
theorem pair_mem {t : Term} (ht : PureS t) : (cls t, fold t) ∈ reachPairs := by
  induction ht with
  | S =>
    have h := startB_eq
    simp only [startB, List.contains_iff_mem] at h
    simpa [cls, fold] using h
  | app _ _ ihf ihx =>
    have h := pairsClosedB_eq
    simp only [pairsClosedB, List.all_eq_true, List.contains_iff_mem] at h
    simpa [cls, fold] using h _ ihf _ ihx

/-- Table fact b1: a non-rejected term has a head normal form block. -/
theorem b1 {t : Term} (ht : PureS t) (hc : cls t ≠ 37) : fold t ≠ 36 := by
  have h := b1B_eq
  simp only [b1B, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h _ (pair_mem ht) with h | h
  · exact absurd h hc
  · exact h

/-- Rejection is absorbing along a frame: a rejected frame item rejects the term. -/
theorem spine_absorb {t : Term} (ht : PureS t) :
    ∀ a ∈ spine t, cls a = 37 → cls t = 37 := by
  induction ht with
  | S => intro a ha; simp [spine] at ha
  | app hf hx ihf _ =>
    intro a ha hca
    simp only [spine, List.mem_append, List.mem_singleton] at ha
    simp only [cls]
    rcases ha with ha | rfl
    · rw [ihf a ha hca]; exact absorbL (cls_lt hx)
    · rw [hca]; exact absorbR (cls_lt hf)

/-- A head chain of a pure S-term is a weak reduction. -/
theorem headChain_wsteps {t u : Term} (h : HeadChain t u) (ht : PureS t) : WSteps t u := by
  induction h with
  | refl => exact .refl _
  | @step t' v u₁ u₂ u₃ rest hs hS _ ih =>
    have hw : WStep t' (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := by
      rw [hS]; exact wstep_foldl (.S u₁ u₂ u₃) rest
    exact .step hw (ih (HnfS.wstep_pure hw ht).1)

/-- The Böhm tree of `t` is defined to depth `k`, read off head reduction. -/
def Pk : Nat → Term → Prop
  | 0, _ => True
  | k + 1, t => ∃ u, HeadChain t u ∧ (spine u).length ≤ 2 ∧ ∀ a ∈ spine u, Pk k a

/-- **The easy half of Question 5.**  Every closed pure-S term whose class is not the
rejecting class 37 is productive: its Böhm tree is defined to every depth. -/
theorem easy {t : Term} (ht : PureS t) (hc : cls t ≠ 37) : ∀ k, Pk k t := by
  intro k
  induction k generalizing t with
  | zero => trivial
  | succ k ih =>
    obtain ⟨u, hch, hl, _⟩ := sound_head t ht (b1 ht hc)
    have hw := headChain_wsteps hch ht
    have hu := (HnfS.fold_wsteps hw ht).1
    have hcu : cls u ≠ 37 := by rw [wsteps_cls hw ht]; exact hc
    refine ⟨u, hch, hl, fun a ha => ih (spine_pure hu a ha) ?_⟩
    intro h37; exact hcu (spine_absorb hu a ha h37)

end HnfProd
