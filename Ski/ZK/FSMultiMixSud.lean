import Ski.ZK.FSMultiMix

/-!
# The Sudoku proof's spread for interleaving

`fs4_interleave` asks of each proof its bound, its read list and the spread
`hsp` of every programmed coordinate.  For the Sudoku proof the first two
are `sud_fs4T` and `sudFS4T_hrd` (`sudFS4T_hrdD`); here the third: each
coordinate of a simulated point determines its first commitment, directly,
as its low digit mod `n1`, or through the read-back `dg` of the query hash
(`digitOf`, `coord_digit`), so the commitment's spread bounds every
coordinate's (`sudFS4T_hsp`, by `spread_sum`).  Not shown: the composed
statement written out for `n` Sudoku proofs and query phases; the
hidden-term and composed circuits.
-/

set_option autoImplicit false
namespace Circuit
open ZKF

/-- The first commitment a programmed coordinate's value `v` in table `tab`
    forces. -/
def digitOf (n1 : Nat) (dg : Nat → Nat) (tab v : Nat) : Nat :=
  match tab with
  | 0 => v
  | 1 => v % n1
  | 2 => v % n1
  | _ => dg v

theorem coord_digit {n1 : Nat} (dg : Nat → Nat) (p : Nat × Nat × Nat × Nat) (_h0 : p.1 < n1)
    (h1 : p.2.1 % n1 = p.1) (h2 : p.2.2.1 % n1 = p.1) (h3 : dg p.2.2.2 = p.1) (tab v : Nat)
    (e : coord4 tab p = v) : p.1 = digitOf n1 dg tab v := by
  match tab, e with
  | 0, e => exact e
  | 1, e => change p.2.1 = v at e; show p.1 = v % n1; rw [← e, h1]
  | 2, e => change p.2.2.1 = v at e; show p.1 = v % n1; rw [← e, h2]
  | j + 3, e => change p.2.2.2 = v at e; show p.1 = dg v; rw [← e, h3]

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **The Sudoku proof's programmed coordinates spread** as its first
    commitment does. -/
theorem sudFS4T_hsp {V Wv P1 P2 P3 : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool) (dg : Nat → Nat)
    (hdg : ∀ m w, dg (φ m w) = m % n1) (hr1 : ∀ d σ, Com1 d σ < n1) {δs : Nat}
    (hsp1 : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com1 d σ = v))) ≤ δs) :
    ∀ c tab v, (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sm 2 (fun x => indB (decide (coord4 tab ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).pts c x) = v))) ≤
      (sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).NS * ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).NR * (Q4 ^ 2 * δs)) := by
  intro c tab v
  have hl : Lin ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sm 2) := lin_sm _ _ _ _
  refine Nat.le_trans (sm_mono ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sm 2) hl (g := fun x => indB (decide (((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).pts c x).1 = digitOf n1 dg tab v)))
    (fun x => ?_)) ?_
  · cases e : decide (coord4 tab ((sudFS4T off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).pts c x) = v)
    · exact Nat.zero_le _
    · have h := coord_digit dg _ (hr1 _ _)
        ((Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 _ _)))
        ((Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 _ _)))
        ((hdg _ _).trans ((Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (hr1 _ _)))) tab v
        (of_decide_eq_true e)
      rw [decide_eq_true h]; exact Nat.le_refl _
  · dsimp only [FS4DT.sm, sudFS4T]
    exact spread_sum Com1 _ hsp1 _

end
end Circuit
