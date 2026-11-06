import Ski.ComposedOS

/-!
# Statement layouts

A composed statement's heap can be laid out as a tree (`cHeapO`) or
shared (`cHeapOS`).  The composed circuits read three facts off a layout:
its roots decode as the verifiers applied to the bits and the witness, its
public part does not depend on the bits or the region's contents, and its
fields are small.  `Layout` bundles a heap function with those three
facts, so a theorem about the composed `dec` circuit is proved once, for
any layout, and holds for both: `treeL` (the audited statements, whose
names keep their tree form) and `sharedL`.
-/

namespace CompM

open Mach Stmt Compose Wit BExpr Circuit

/-- The machine of a heap function: its heap, the first root, an empty
    stack past it. -/
def mkMach (H : (Nat → Bool) → BT → List Cell → List OTerm → List Cell × List Nat)
    (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm) : Mach :=
  ⟨(H ρ shp region Vs).1 ++ [.nil], (H ρ shp region Vs).2.getD 0 0, (H ρ shp region Vs).1.length⟩

/-- **A statement layout**: a heap function and the facts the composed
    circuits read off it. -/
structure Layout where
  heap : (Nat → Bool) → BT → List Cell → List OTerm → List Cell × List Nat
  roots_length : ∀ (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm),
    (heap ρ shp region Vs).2.length = Vs.length
  decode : ∀ {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Vs : List OTerm} {w : Term},
    cWitness ρ (BT.nleaves shp) region = some w →
    (heap ρ shp region Vs).2.length = Vs.length ∧
    ∀ j V, Vs[j]? = some V →
      otermAt (mkMach heap ρ shp region Vs).heap ((mkMach heap ρ shp region Vs).heap.length + 1)
        ((heap ρ shp region Vs).2.getD j 0) =
        some (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO)
  pub : ∀ (ρ ρ' : Nat → Bool) (shp : BT) (region region' : List Cell) (Vs : List OTerm),
    region.length = region'.length →
    (mkMach heap ρ shp region Vs).hd = (mkMach heap ρ' shp region' Vs).hd ∧
    (mkMach heap ρ shp region Vs).stk = (mkMach heap ρ' shp region' Vs).stk ∧
    (heap ρ shp region Vs).2 = (heap ρ' shp region' Vs).2 ∧
    (mkMach heap ρ shp region Vs).heap.length = (mkMach heap ρ' shp region' Vs).heap.length ∧
    (mkMach heap ρ shp region Vs).heap.take (BT.nleaves shp + 3 + region.length) =
      slotHeap ρ (BT.nleaves shp) ++ region ∧
    ∀ i, (i < 3 ∨ BT.nleaves shp + 3 + region.length ≤ i) →
      (mkMach heap ρ shp region Vs).heap[i]? = (mkMach heap ρ' shp region' Vs).heap[i]?
  fitsB : ∀ (Bd : Nat) (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm),
    (∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true) →
    (∀ V ∈ Vs, ∀ x, Occ x V → x < Bd) →
    FitsB Bd (mkMach heap ρ shp region Vs).heap ∧
      (∀ r ∈ (heap ρ shp region Vs).2, r < (mkMach heap ρ shp region Vs).heap.length) ∧
      combRoot ρ shp region < (mkMach heap ρ shp region Vs).heap.length

/-- A layout's machine. -/
abbrev Layout.mach (L : Layout) := mkMach L.heap

/-- `Layout.pub`, its machine written `L.mach`. -/
theorem Layout.pubM (L : Layout) (ρ ρ' : Nat → Bool) (shp : BT) (region region' : List Cell) (Vs : List OTerm)
    (hl : region.length = region'.length) :
    (L.mach ρ shp region Vs).hd = (L.mach ρ' shp region' Vs).hd ∧
    (L.mach ρ shp region Vs).stk = (L.mach ρ' shp region' Vs).stk ∧
    (L.heap ρ shp region Vs).2 = (L.heap ρ' shp region' Vs).2 ∧
    (L.mach ρ shp region Vs).heap.length = (L.mach ρ' shp region' Vs).heap.length ∧
    (L.mach ρ shp region Vs).heap.take (BT.nleaves shp + 3 + region.length) =
      slotHeap ρ (BT.nleaves shp) ++ region ∧
    ∀ i, (i < 3 ∨ BT.nleaves shp + 3 + region.length ≤ i) →
      (L.mach ρ shp region Vs).heap[i]? = (L.mach ρ' shp region' Vs).heap[i]? :=
  L.pub ρ ρ' shp region region' Vs hl

/-- `Layout.fitsB`, its machine written `L.mach`. -/
theorem Layout.fitsBM (L : Layout) (Bd : Nat) (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    (hv : ∀ V ∈ Vs, ∀ x, Occ x V → x < Bd) :
    FitsB Bd (L.mach ρ shp region Vs).heap ∧
      (∀ r ∈ (L.heap ρ shp region Vs).2, r < (L.mach ρ shp region Vs).heap.length) ∧
      combRoot ρ shp region < (L.mach ρ shp region Vs).heap.length :=
  L.fitsB Bd ρ shp region Vs hr hv


theorem cMachineO_eq : cMachineO = mkMach cHeapO := rfl

theorem addStmtsO_roots_len (pe wr : Nat) : ∀ (Vs : List OTerm) (h : List Cell),
    (addStmtsO pe wr h Vs).2.length = Vs.length
  | [], _ => rfl
  | P :: Vs, h => by
    show ((addStmtsO pe wr _ Vs).2).length + 1 = Vs.length + 1
    rw [addStmtsO_roots_len pe wr Vs]

theorem addStmtsOS_roots_len (pe wr : Nat) : ∀ (Vs : List OTerm) (h : List Cell) (m : Memo),
    (addStmtsOS pe wr h m Vs).2.length = Vs.length
  | [], _, _ => rfl
  | P :: Vs, h, m => by
    show ((addStmtsOS pe wr _ _ Vs).2).length + 1 = Vs.length + 1
    rw [addStmtsOS_roots_len pe wr Vs]
theorem cMachineOS_eq : cMachineOS = mkMach cHeapOS := rfl

/-- **The tree layout**, the audited one: `cHeapO`. -/
def treeL : Layout where
  heap := cHeapO
  roots_length _ _ _ _ := addStmtsO_roots_len _ _ _ _
  decode := cMachineO_decode
  pub := cMachineO_public
  fitsB := cMachineO_fitsB

/-- **The shared layout**: `cHeapOS`, one cell per distinct subterm. -/
def sharedL : Layout where
  heap := cHeapOS
  roots_length _ _ _ _ := addStmtsOS_roots_len _ _ _ _ _
  decode := cMachineOS_decode
  pub := cMachineOS_public
  fitsB := cMachineOS_fitsB

theorem treeL_mach : treeL.mach = cMachineO := rfl
theorem treeL_heap : treeL.heap = cHeapO := rfl

/-- A layout's machine with the bits clear and the region blank. -/
def Layout.blankM (L : Layout) (shp : BT) (W : Nat) (Vs : List OTerm) : Mach :=
  L.mach (fun _ => false) shp (List.replicate W .S) Vs

def Layout.blankRoots (L : Layout) (shp : BT) (W : Nat) (Vs : List OTerm) : List Nat :=
  (L.heap (fun _ => false) shp (List.replicate W .S) Vs).2

theorem Layout.blank_prefix (L : Layout) (shp : BT) (W : Nat) (Vs : List OTerm) :
    3 + BT.nleaves shp + W ≤ (L.blankM shp W Vs).heap.length := by
  have this : (L.blankM shp W Vs).heap.take (BT.nleaves shp + 3 + (List.replicate W Cell.S).length) =
      slotHeap (fun _ => false) (BT.nleaves shp) ++ List.replicate W .S :=
    (L.pub (fun _ => false) (fun _ => false) shp (List.replicate W .S) (List.replicate W .S) Vs
      rfl).2.2.2.2.1
  have hl := congrArg List.length this
  simp only [List.length_take, List.length_append, slotHeap_length, List.length_replicate] at hl
  omega

theorem Layout.blankRoots_length (L : Layout) (shp : BT) (W : Nat) (Vs : List OTerm) :
    (L.blankRoots shp W Vs).length = Vs.length := L.roots_length _ _ _ _

theorem treeL_blankM : treeL.blankM = Circuit.blankMO := rfl
theorem treeL_blankRoots : treeL.blankRoots = Circuit.blankRootsO := rfl

end CompM
