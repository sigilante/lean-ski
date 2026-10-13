import Ski.ZK.ROMFamilyM

/-!
# The Merkle leaves as the committed polynomials' rows

`ROMInstM` and `ROMFamilyM` take the tie of the leaves to the committed data
as hypotheses: distinct leaves at distinct positions (`hdist`), positions in
range (`hlt`), each salt spreading (`hs`), and the opened values fixing the
opened leaves' positions (`hposO`).  Here they are met by a model of the
leaves: leaf `l` holds every committed polynomial's value at its point
`xs l k` in group `k`'s domain (`rowAt`), its position its index, its salt
and a hash `h` of its row (`posRows`).  The opened leaves are those whose
point in each opened group lies in that group's query set (`isOfRows`);
where `opF` agrees there, the rows agree (`rowAt_opF`), so `hposO` holds
(`posRows_hposO`), with `hdist`, `hlt` (`n = L NSl Mh`, given `0 < NSl`,
`0 < Mh`) and `hs` at `s = 1` (given `0 < L`).

The conclusion holds for the opened set `isOfRows` picks; `ROMMerkleIdx`
shows it is the set of queried indices when the query sets hold those
leaves' points.  Not modelled: that the query
sets `S16`, `S10`, `SP` are the points of indices FRI draws (agreeing with
`pcsZ`, `friX`); Plonky3's mixed-height
tree, which hashes a shorter matrix's rows into the internal layer of its
height (`compress_and_inject`) rather than into the leaf, the per-group
point `xs l k` standing for the row shift; its per-matrix salts, here one
salt per leaf; the leaf index in the hash input (Plonky3 hashes the row and
salt alone, so leaves with equal rows and salts collide, a term counted
in `ROMMerkleColl` and `ROMInstMC` for positions without the index, not
for these rows); and the hash's binding, which zero knowledge does not use.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- A leaf's row: every committed polynomial's value at the leaf's point in
    its group's domain, `xs l k` for group `k` (the groups `mk` that `opF`
    opens; groups of different heights read the leaf at different points). -/
def rowAt (xs : Nat → Nat → F) (mk : List Nat) (d : List (List (List F))) (l : Nat) : List (List F) :=
  (mk.zip d).map (fun p => p.2.map (fun poly => fval (xs l p.1) poly))

/-- The leaves opened at the query points `Ss`: those whose point in each
    opened group lies in that group's query set. -/
def isOfRows (Ss : List (List F)) (mk : List Nat) (xs : Nat → Nat → F) (l : Nat) : Bool :=
  mk.all (fun k => decide (xs l k ∈ Ss.getD k []))

/-- A leaf's position: its index, its salt, and a hash `h` of its row. -/
def posRows (xs : Nat → Nat → F) (mk : List Nat) (h : List (List F) → Nat) (L NSl Mh : Nat)
    (d : List (List (List F))) (l a : Nat) : Nat :=
  l + L * (a % NSl + NSl * (h (rowAt xs mk d l) % Mh))

theorem fval_of_map {x : F} {p p' : List F} : ∀ (S : List F), x ∈ S →
    S.map (fun s => fval s p) = S.map (fun s => fval s p') → fval x p = fval x p'
  | [], hx, _ => absurd hx (List.not_mem_nil)
  | s :: S, hx, e => by
    simp only [List.map_cons, List.cons.injEq] at e
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact e.1
    · exact fval_of_map S hx' e.2

theorem polys_of_map {x : F} {S : List F} (hx : x ∈ S) : ∀ (q q' : List (List F)),
    q.map (fun poly => S.map (fun s => fval s poly)) = q'.map (fun poly => S.map (fun s => fval s poly)) →
    q.map (fun poly => fval x poly) = q'.map (fun poly => fval x poly)
  | [], [], _ => rfl
  | [], _ :: _, e => absurd e (by simp)
  | _ :: _, [], e => absurd e (by simp)
  | p :: q, p' :: q', e => by
    simp only [List.map_cons, List.cons.injEq] at e ⊢
    exact ⟨fval_of_map S hx e.1, polys_of_map hx q q' e.2⟩

/-- **The opened values fix the opened leaves' rows**: where `opF` agrees,
    every leaf whose point lies in each opened group's query set has the
    same row. -/
theorem rowAt_opF {Ss : List (List F)} {xs : Nat → Nat → F} {l : Nat} : ∀ (mk : List Nat) (d d' : List (List (List F))),
    opF Ss mk d = opF Ss mk d' → isOfRows Ss mk xs l = true → rowAt xs mk d l = rowAt xs mk d' l
  | [], _, _, _, _ => by simp [rowAt]
  | _ :: _, [], [], _, _ => rfl
  | _ :: _, [], _ :: _, e, _ => absurd e (by simp [opF])
  | _ :: _, _ :: _, [], e, _ => absurd e (by simp [opF])
  | k :: ks, q :: qs, q' :: qs', e, hi => by
    simp only [opF, List.zip_cons_cons, List.map_cons, List.cons.injEq] at e
    simp only [isOfRows, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hi
    simp only [rowAt, List.zip_cons_cons, List.map_cons, List.cons.injEq]
    exact ⟨polys_of_map hi.1 q q' e.1, rowAt_opF ks qs qs' e.2 hi.2⟩

theorem posRows_mod {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {L NSl Mh : Nat}
    (d : List (List (List F))) {l : Nat} (hl : l < L) (a : Nat) :
    posRows xs mk h L NSl Mh d l a % L = l := by
  unfold posRows; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- Distinct leaves have distinct positions. -/
theorem posRows_dist {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {L NSl Mh : Nat} :
    ∀ d l l' a b, l < L → l' < L → l ≠ l' → posRows xs mk h L NSl Mh d l a ≠ posRows xs mk h L NSl Mh d l' b :=
  fun d l l' a b hl hl' hne e => hne (by rw [← posRows_mod d hl a, e, posRows_mod d hl' b])

/-- Positions lie below `L NSl Mh`. -/
theorem posRows_lt {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {L NSl Mh : Nat}
    (hN : 0 < NSl) (hMh : 0 < Mh) : ∀ d l a, l < L → posRows xs mk h L NSl Mh d l a < L * (NSl * Mh) := by
  intro d l a hl
  unfold posRows
  have h1 : a % NSl + NSl * (h (rowAt xs mk d l) % Mh) + 1 ≤ NSl * Mh := by
    have ha : a % NSl + 1 ≤ NSl := Nat.mod_lt _ hN
    have hm : h (rowAt xs mk d l) % Mh + 1 ≤ Mh := Nat.mod_lt _ hMh
    calc a % NSl + NSl * (h (rowAt xs mk d l) % Mh) + 1 = (a % NSl + 1) + NSl * (h (rowAt xs mk d l) % Mh) := by
          rw [Nat.add_right_comm]
      _ ≤ NSl + NSl * (h (rowAt xs mk d l) % Mh) := Nat.add_le_add_right ha _
      _ = NSl * (h (rowAt xs mk d l) % Mh + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ NSl * Mh := Nat.mul_le_mul_left _ hm
  calc l + L * (a % NSl + NSl * (h (rowAt xs mk d l) % Mh)) < L + L * (a % NSl + NSl * (h (rowAt xs mk d l) % Mh)) :=
        Nat.add_lt_add_right hl _
    _ = L * (a % NSl + NSl * (h (rowAt xs mk d l) % Mh) + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ L * (NSl * Mh) := Nat.mul_le_mul_left _ h1

/-- A leaf's salt fixes its position: one salt per value (`s = 1`). -/
theorem posRows_spread {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {L NSl Mh : Nat}
    (hL : 0 < L) : ∀ d l v, sumTo NSl (fun x => indB (decide (posRows xs mk h L NSl Mh d l x = v))) ≤ 1 := by
  intro d l v
  have key : ∀ x, x < NSl → indB (decide (posRows xs mk h L NSl Mh d l x = v)) ≤ indB (decide (x = (v - l) / L % NSl)) := by
    intro x hx
    cases e : decide (posRows xs mk h L NSl Mh d l x = v)
    · exact Nat.zero_le _
    · have ev : posRows xs mk h L NSl Mh d l x = v := of_decide_eq_true e
      have hx' : x = (v - l) / L % NSl := by
        rw [← ev]; unfold posRows
        rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hL, Nat.add_mul_mod_self_left, Nat.mod_mod,
          Nat.mod_eq_of_lt hx]
      rw [decide_eq_true hx']; exact Nat.le_refl _
  exact Nat.le_trans (sumTo_mono _ key) (sumTo_indEq _ NSl).1

/-- **`hposO` is met by the rows' positions** at `opF`'s opened set: a leaf
    whose point lies in every opened group's query set has its row, and so
    its position, fixed by the opened values (`rowAt_opF`). -/
theorem posRows_hposO {xs : Nat → Nat → F} {mk : List Nat} {h : List (List F) → Nat} {L NSl Mh : Nat} (Ss : List (List F)) :
    ∀ d d', opF Ss mk d = opF Ss mk d' → ∀ l a, isOfRows Ss mk xs l = true →
      posRows xs mk h L NSl Mh d l a = posRows xs mk h L NSl Mh d' l a := by
  intro d d' e l a hi
  unfold posRows; rw [rowAt_opF mk d d' e hi]

end Circuit
