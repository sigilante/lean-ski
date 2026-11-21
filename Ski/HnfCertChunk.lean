import Ski.HnfCertClaim

/-!
# Chunking the kernel checks

The claim checks are evaluated by `decide +kernel` on subtrees of the claim tree (`CBST.sub`,
addressed by a path) and on single nodes' items, in generated modules `Ski/HnfCertK/*`, and
reassembled here by `all_node`.  List checks are split into `take`/`drop` pieces.
-/

namespace HnfCert

/-- The subtree at a path (`false` = left, `true` = right). -/
def CBST.sub : CBST → List Bool → CBST
  | t, [] => t
  | .leaf, _ :: _ => .leaf
  | .node _ _ l r, b :: p => (if b then r else l).sub p

def CBST.items : CBST → List Claim
  | .leaf => []
  | .node _ i _ _ => i

theorem CBST.sub_append : ∀ (t : CBST) (p q : List Bool), (t.sub p).sub q = t.sub (p ++ q)
  | t, [], q => rfl
  | .leaf, _ :: _, [] => rfl
  | .leaf, _ :: _, _ :: _ => rfl
  | .node _ _ l r, b :: p, q => by
    simp only [CBST.sub, List.cons_append]
    cases b <;> exact CBST.sub_append _ p q

theorem all_node (f : Claim → Bool) (t : CBST) (hl : ((t.sub [false]).toList.all f) = true)
    (hi : (t.items.all f) = true) (hr : ((t.sub [true]).toList.all f) = true) : (t.toList.all f) = true := by
  cases t with
  | leaf => rfl
  | node k i l r =>
    have hl' : l.toList.all f = true := hl
    have hr' : r.toList.all f = true := hr
    have hi' : i.all f = true := hi
    show (l.toList ++ i ++ r.toList).all f = true
    rw [List.all_append, List.all_append, hl', hi', hr']; rfl

/-- Reassemble a node from its children and items, at a path. -/
theorem all_at (f : Claim → Bool) (p : List Bool)
    (hl : ((CBST_.sub (p ++ [false])).toList.all f) = true)
    (hi : ((CBST_.sub p).items.all f) = true)
    (hr : ((CBST_.sub (p ++ [true])).toList.all f) = true) : ((CBST_.sub p).toList.all f) = true := by
  rw [← CBST.sub_append] at hl hr
  exact all_node f _ hl hi hr

theorem all_take_drop {α : Type} (f : α → Bool) (l : List α) (n : Nat)
    (h1 : (l.take n).all f = true) (h2 : (l.drop n).all f = true) : l.all f = true := by
  rw [← List.take_append_drop n l, List.all_append, h1, h2]; rfl

/-- One step of a `drop` chain: rows `a .. a+n` and the rest after them. -/
theorem all_step {α : Type} (f : α → Bool) (l : List α) (a n : Nat)
    (h1 : ((l.drop a).take n).all f = true) (h2 : (l.drop (a + n)).all f = true) :
    (l.drop a).all f = true := by
  refine all_take_drop f (l.drop a) n h1 ?_
  rw [List.drop_drop]; exact h2

def rootRow (a : Nat) : Bool :=
  ACCS.all fun b =>
    let s := dxN a b
    accN s || s % 64 == 36 || !(lookup (.A (mkV a) (mkV b))).isEmpty

theorem rootsCovered_eq : rootsCovered = ACCS.all rootRow := rfl

theorem all_claims (h : (CBST_.sub []).toList.all checkClaim = true) : ∀ c ∈ CLAIMS, checkClaim c = true := by
  intro c hc
  have := List.all_eq_true.mp h c
  exact this hc

end HnfCert
