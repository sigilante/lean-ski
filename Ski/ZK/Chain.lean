import Ski.ZK.Count

/-!
# Blinding along a chain hides the terminals

Plonky3 publishes one LogUp terminal per table.  In the zero-knowledge
circuits three private tables carry the witness: the witness table, the
CPU and the memory.  Two blinding messages, each a fresh uniform tuple,
run along them: `blind_a` from the witness table to the CPU, `blind_b`
from the CPU to the memory.  So their terminals are
`X_W + u`, `X_C - u + v`, `X_M - v` (`chainView`), where `u` and `v` are
the two messages' terms and `X` the unblinded terminals.

For a generic combiner challenge, two witnesses whose unblinded terminals
have the same sum give the same distribution of published terminals over
the blinding (`chain_hides`): a bijection of the blinding carries one onto
the other.  The honest prover succeeds unless a blinding denominator is
zero (`Pole`), at most `2 P^4` of the `P^8` choices (`pole_count`); on the
rest the two distributions differ by at most that (`chain_hides_valid`).
-/

namespace Circuit

open ZKF

/-- The published terminals of the witness table, the CPU and the memory. -/
structure View3 where
  tw : EF
  tc : EF
  tm : EF

/-- **The blinded terminals**, from the unblinded ones `x` and the two
    blinding tuples. -/
def chainView (β preA preB : EF) (x : View3) (a b : Tup) : View3 :=
  ⟨x.tw.add (blindTerm β preA a), (x.tc.sub (blindTerm β preA a)).add (blindTerm β preB b),
    x.tm.sub (blindTerm β preB b)⟩

def View3.sum (x : View3) : EF := (x.tw.add x.tc).add x.tm

/-- Four elements as leaves. -/
def env4 (a b c d : EF) : Atom → F
  | .main 0 0 => a.x0 | .main 0 1 => a.x1 | .main 0 2 => a.x2 | .main 0 3 => a.x3
  | .main 0 4 => b.x0 | .main 0 5 => b.x1 | .main 0 6 => b.x2 | .main 0 7 => b.x3
  | .main 0 8 => c.x0 | .main 0 9 => c.x1 | .main 0 10 => c.x2 | .main 0 11 => c.x3
  | .main 0 12 => d.x0 | .main 0 13 => d.x1 | .main 0 14 => d.x2 | .main 0 15 => d.x3
  | _ => 0

/-- Eight elements as leaves. -/
def env8 (a b c d e f g h : EF) : Atom → F
  | .main 0 0 => a.x0
  | .main 0 1 => a.x1
  | .main 0 2 => a.x2
  | .main 0 3 => a.x3
  | .main 0 4 => b.x0
  | .main 0 5 => b.x1
  | .main 0 6 => b.x2
  | .main 0 7 => b.x3
  | .main 0 8 => c.x0
  | .main 0 9 => c.x1
  | .main 0 10 => c.x2
  | .main 0 11 => c.x3
  | .main 0 12 => d.x0
  | .main 0 13 => d.x1
  | .main 0 14 => d.x2
  | .main 0 15 => d.x3
  | .main 0 16 => e.x0
  | .main 0 17 => e.x1
  | .main 0 18 => e.x2
  | .main 0 19 => e.x3
  | .main 0 20 => f.x0
  | .main 0 21 => f.x1
  | .main 0 22 => f.x2
  | .main 0 23 => f.x3
  | .main 0 24 => g.x0
  | .main 0 25 => g.x1
  | .main 0 26 => g.x2
  | .main 0 27 => g.x3
  | .main 0 28 => h.x0
  | .main 0 29 => h.x1
  | .main 0 30 => h.x2
  | .main 0 31 => h.x3
  | _ => 0

theorem ef_shift_w (xw xw' u : EF) : xw'.add (u.add (xw.sub xw')) = xw.add u :=
  Q.eq_of_norm (p := (Q.var 1).add ((Q.var 2).add ((Q.var 0).sub (Q.var 1)))) (q := (Q.var 0).add (Q.var 2))
    (by decide) (env3 xw xw' u)

theorem ef_shift_m (xm xm' v : EF) : xm'.sub (v.add (xm'.sub xm)) = xm.sub v :=
  Q.eq_of_norm (p := (Q.var 1).sub ((Q.var 2).add ((Q.var 1).sub (Q.var 0)))) (q := (Q.var 0).sub (Q.var 2))
    (by decide) (env3 xm xm' v)

theorem ef_shift_c (w c m w' c' m' u v : EF) (hs : (w.add c).add m = (w'.add c').add m') :
    (c'.sub (u.add (w.sub w'))).add (v.add (m'.sub m)) = (c.sub u).add v := by
  -- `c' = w + c + m - w' - m'`
  have e : c' = (((w.add c).add m).sub w').sub m' := by
    rw [hs]
    exact (Q.eq_of_norm (p := (((Q.var 0).add (Q.var 1)).add (Q.var 2)).sub (Q.var 0) |>.sub (Q.var 2))
      (q := Q.var 1) (by decide) (env3 w' c' m')).symm
  rw [e]
  exact Q.eq_of_norm
    (p := (((((Q.var 0).add (Q.var 1)).add (Q.var 2)).sub (Q.var 4) |>.sub (Q.var 6)).sub
      ((Q.var 7).add ((Q.var 0).sub (Q.var 4)))).add ((Q.var 3).add ((Q.var 6).sub (Q.var 2))))
    (q := ((Q.var 1).sub (Q.var 7)).add (Q.var 3)) (by decide)
    (env8 w c m v w' c' m' u)

-- ---------------------------------------------------------------------------
-- The chain hides the terminals
-- ---------------------------------------------------------------------------

/-- Shifting a blinding term by `δ`, as a map of tuples. -/
def shiftTup (β pre δ : EF) (a : Tup) : Tup := blindPre β pre ((blindTerm β pre a).add δ)
def unshiftTup (β pre δ : EF) (a : Tup) : Tup := blindPre β pre ((blindTerm β pre a).sub δ)

theorem shift_term {β : EF} (hg : Generic β) (pre δ : EF) (a : Tup) :
    blindTerm β pre (shiftTup β pre δ a) = (blindTerm β pre a).add δ := blindTerm_pre hg _ _

theorem unshift_shift {β : EF} (hg : Generic β) (pre δ : EF) (a : Tup) :
    unshiftTup β pre δ (shiftTup β pre δ a) = a := by
  unfold unshiftTup; rw [shift_term hg, EF.add_neg_cancel, blindPre_term hg]

theorem shift_unshift {β : EF} (hg : Generic β) (pre δ : EF) (a : Tup) :
    shiftTup β pre δ (unshiftTup β pre δ a) = a := by
  unfold shiftTup unshiftTup; rw [blindTerm_pre hg, EF.sub_add_cancel, blindPre_term hg]

theorem view_shift {β : EF} (hg : Generic β) (preA preB : EF) (x x' : View3) (hs : x.sum = x'.sum) (a b : Tup) :
    chainView β preA preB x' (shiftTup β preA (x.tw.sub x'.tw) a) (shiftTup β preB (x'.tm.sub x.tm) b) =
      chainView β preA preB x a b := by
  unfold chainView
  rw [shift_term hg, shift_term hg, ef_shift_w, ef_shift_m, ef_shift_c _ _ _ _ _ _ _ _ hs]

/-- **The chain hides the terminals**: for a generic `β`, two witnesses
    whose unblinded terminals have the same sum publish identically
    distributed terminals, over the blinding. -/
theorem chain_hides {β : EF} (hg : Generic β) (preA preB : EF) (x x' : View3) (hs : x.sum = x'.sum)
    (E : View3 → Bool) :
    count2 (fun a b => E (chainView β preA preB x a b)) = count2 (fun a b => E (chainView β preA preB x' a b)) := by
  have h := count2_bij (fun a b => E (chainView β preA preB x' a b))
    (unshift_shift hg preA (x.tw.sub x'.tw)) (shift_unshift hg preA (x.tw.sub x'.tw))
    (unshift_shift hg preB (x'.tm.sub x.tm)) (shift_unshift hg preB (x'.tm.sub x.tm))
  simp only [view_shift hg preA preB x x' hs] at h
  exact h

-- ---------------------------------------------------------------------------
-- The prover's failures
-- ---------------------------------------------------------------------------

/-- **A pole**: a blinding denominator is zero, and the honest prover's
    proof fails. -/
def Pole (β preA preB : EF) (a b : Tup) : Bool :=
  decide (preA.sub (horner β a) = EF.zero) || decide (preB.sub (horner β b) = EF.zero)

theorem sumTo_mono {f g : Nat → Nat} : ∀ n, (∀ i, i < n → f i ≤ g i) → sumTo n f ≤ sumTo n g
  | 0, _ => Nat.le_refl 0
  | n + 1, h => Nat.add_le_add (sumTo_mono n (fun i hi => h i (by omega))) (h n (by omega))

theorem sumTo_one {f : Nat → Nat} {x : Nat} : ∀ n, x < n → f x = 1 → (∀ i, i < n → i ≠ x → f i = 0) → sumTo n f = 1
  | 0, hx, _, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, hx, h1, h0 => by
    show sumTo n f + f n = 1
    rcases Nat.lt_or_ge x n with h' | h'
    · rw [sumTo_one n h' h1 (fun i hi hne => h0 i (by omega) hne), h0 n (by omega) (by omega)]
    · have : x = n := by omega
      subst this
      have z : sumTo x f = 0 := by
        have : ∀ m, m ≤ x → sumTo m f = 0 := by
          intro m; induction m with
          | zero => intro _; rfl
          | succ m ih => intro hm; show sumTo m f + f m = 0; rw [ih (by omega), h0 m (by omega) (by omega)]
        exact this x (Nat.le_refl _)
      rw [z, h1]

/-- Exactly one tuple zeroes a denominator. -/
theorem pole_one {β : EF} (hg : Generic β) (pre : EF) :
    sumTo Q4 (fun i => if decide (pre.sub (horner β (Tup.dec i)) = EF.zero) then 1 else 0) = 1 := by
  let a0 := combInv β pre
  have key : ∀ a, pre.sub (horner β a) = EF.zero ↔ a = a0 := by
    intro a
    constructor
    · intro h
      have e : horner β a = pre := by
        have := EF.sub_add_cancel pre (horner β a)
        rw [h, EF.zero_add] at this; exact this
      show a = combInv β pre
      rw [← e, combInv_horner hg]
    · intro h; rw [h, horner_combInv hg, EF.sub_self]
  refine sumTo_one Q4 (Tup.enc_lt a0) ?_ (fun i hi hne => ?_)
  · rw [Tup.dec_enc, decide_eq_true ((key a0).2 rfl)]; rfl
  · rw [decide_eq_false (fun h => hne (by rw [← (key _).1 h, Tup.enc_dec hi]))]; rfl

theorem ite_or_le (p q : Bool) : (if (p || q) then 1 else 0) ≤ (if p then 1 else 0) + (if q then 1 else 0) := by
  cases p <;> cases q <;> decide

theorem sumTo_const (c : Nat) : ∀ n, sumTo n (fun _ => c) = n * c
  | 0 => by rw [Nat.zero_mul]; rfl
  | n + 1 => by show sumTo n (fun _ => c) + c = (n + 1) * c; rw [sumTo_const c n, Nat.succ_mul]

/-- **At most `2 P^4` of the `P^8` blinding pairs are poles.** -/
theorem pole_count {β : EF} (hg : Generic β) (preA preB : EF) : count2 (Pole β preA preB) ≤ 2 * Q4 := by
  unfold count2 Pole
  let fa : Nat → Nat := fun i => if decide (preA.sub (horner β (Tup.dec i)) = EF.zero) then 1 else 0
  let fb : Nat → Nat := fun j => if decide (preB.sub (horner β (Tup.dec j)) = EF.zero) then 1 else 0
  have h1 : sumTo Q4 fa = 1 := pole_one hg preA
  have h2 : sumTo Q4 fb = 1 := pole_one hg preB
  have step : ∀ i, sumTo Q4 (fun j => fa i + fb j) = Q4 * fa i + 1 := by
    intro i; rw [sumTo_add, h2, sumTo_const]
  calc sumTo Q4 (fun i => sumTo Q4 fun j => if (decide (preA.sub (horner β (Tup.dec i)) = EF.zero) ||
          decide (preB.sub (horner β (Tup.dec j)) = EF.zero)) then 1 else 0)
      ≤ sumTo Q4 (fun i => sumTo Q4 fun j => fa i + fb j) :=
        sumTo_mono Q4 (fun i _ => sumTo_mono Q4 (fun j _ => ite_or_le _ _))
    _ = sumTo Q4 (fun i => Q4 * fa i + 1) := sumTo_congr Q4 (fun i _ => step i)
    _ = Q4 * 1 + Q4 * 1 := by rw [sumTo_add, ← sumTo_mul, h1, sumTo_const]
    _ = 2 * Q4 := by omega

theorem count2_mono {p q : Tup → Tup → Bool} (h : ∀ a b, p a b = true → q a b = true) : count2 p ≤ count2 q := by
  unfold count2
  refine sumTo_mono Q4 (fun i _ => sumTo_mono Q4 (fun j _ => ?_))
  cases hp : p (Tup.dec i) (Tup.dec j) with
  | false => rw [if_neg (by decide)]; exact Nat.zero_le _
  | true => rw [if_pos rfl, if_pos (h _ _ hp)]; exact Nat.le_refl 1

theorem count2_split (c e : Tup → Tup → Bool) :
    count2 e = count2 (fun a b => !c a b && e a b) + count2 (fun a b => c a b && e a b) := by
  unfold count2
  rw [← sumTo_add]
  refine sumTo_congr Q4 (fun i _ => ?_)
  rw [← sumTo_add]
  refine sumTo_congr Q4 (fun j _ => ?_)
  show (if e (Tup.dec i) (Tup.dec j) = true then 1 else 0) =
    (if (!c (Tup.dec i) (Tup.dec j) && e (Tup.dec i) (Tup.dec j)) = true then 1 else 0) +
      (if (c (Tup.dec i) (Tup.dec j) && e (Tup.dec i) (Tup.dec j)) = true then 1 else 0)
  generalize c (Tup.dec i) (Tup.dec j) = x
  generalize e (Tup.dec i) (Tup.dec j) = y
  cases x <;> cases y <;> decide

/-- **On the honest prover's successful runs**, two witnesses' published
    terminals differ in distribution by at most `2 P^4` of the `P^8`
    blinding pairs: statistical distance below `2^-121`. -/
theorem chain_hides_valid {β : EF} (hg : Generic β) (preA preB : EF) (x x' : View3) (hs : x.sum = x'.sum)
    (E : View3 → Bool) :
    count2 (fun a b => !Pole β preA preB a b && E (chainView β preA preB x a b)) ≤
      count2 (fun a b => !Pole β preA preB a b && E (chainView β preA preB x' a b)) + 2 * Q4 := by
  have h1 : count2 (fun a b => !Pole β preA preB a b && E (chainView β preA preB x a b)) ≤
      count2 (fun a b => E (chainView β preA preB x a b)) :=
    count2_mono (fun a b h => by rw [Bool.and_eq_true] at h; exact h.2)
  have h2 := count2_split (Pole β preA preB) (fun a b => E (chainView β preA preB x' a b))
  have h3 : count2 (fun a b => Pole β preA preB a b && E (chainView β preA preB x' a b)) ≤ count2 (Pole β preA preB) :=
    count2_mono (fun a b h => by rw [Bool.and_eq_true] at h; exact h.1)
  have h4 := pole_count hg preA preB
  rw [chain_hides hg preA preB x x' hs] at h1
  omega

end Circuit
