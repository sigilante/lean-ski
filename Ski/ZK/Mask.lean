import Ski.ZK.FPoly

/-!
# Random rows hide a column's openings

Plonky3's hiding PCS (`p3-fri` 0.8.0, `HidingFriPcs::commit`) interleaves
every committed trace column with random rows: the column of height `h`
becomes one of height `2h`, the trace on half its points and uniform
values on the other half, and its polynomial is the interpolant through
all `2h`.  The verifier then sees its values at the queried points, which
lie in a coset disjoint from the trace's.

**`mask_hides`**: for trace points `T` and random points `R`, `n` each, all
distinct, and opened points `S`, at most `n` and none in `T`, the values
of the column at `S` have one distribution for every trace: for two traces
`t`, `t'` and every event `E`, as many random vectors `r` (of the `P^n`)
put the openings of `(t, r)` in `E` as put those of `(t', r)`.  The
bijection is a shift of the randomness: with `D` the interpolant of
`t' - t` on `T` and `0` on `S`, the column of `(t', r + D|_R)` is the
column of `(t, r)` plus `D`, which vanishes at `S` (`fagree`).

`vsum n` sums over the `P^n` vectors of `F^n`, digit by digit; a shift
by a fixed vector permutes them (`vsum_shift`).
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Vectors over `F`, numbered
-- ---------------------------------------------------------------------------

/-- A sum over all the vectors of `F^n`, digit by digit. -/
def vsum : Nat → (List F → Nat) → Nat
  | 0, f => f []
  | n + 1, f => sumTo P (fun d => vsum n (fun l => f (ofN d :: l)))

theorem vsum_congr : ∀ n {f g : List F → Nat}, (∀ r, r.length = n → f r = g r) → vsum n f = vsum n g
  | 0, _, _, h => h [] rfl
  | n + 1, _, _, h => congrArg (sumTo P) (funext fun _ =>
      vsum_congr n (fun l hl => h _ (by rw [List.length_cons, hl])))

/-- A shift of one digit permutes the digits. -/
theorem sumTo_shiftF (g : F → Nat) (c : F) : sumTo P (fun d => g (ofN d + c)) = sumTo P (fun d => g (ofN d)) := by
  have e : (fun d => g (ofN d + c)) = fun d => (fun j => g (ofN j)) (ofN d + c).val := funext fun d => by
    show g (ofN d + c) = g (ofN (ofN d + c).val); rw [ofN_val]
  rw [e]
  refine sumTo_perm (fun j => g (ofN j)) P (fun d => (ofN d + c).val) (fun d => (ofN d - c).val)
    (fun _ _ => Fin.isLt _) (fun _ _ => Fin.isLt _) (fun d hd => ?_) (fun d hd => ?_)
  · show (ofN (ofN d + c).val - c).val = d
    rw [ofN_val, show ofN d + c - c = ofN d from fid (e := v 0 + v 1 - v 1) (e' := v 0) (by decide) [ofN d, c],
      val_ofN hd]
  · show (ofN (ofN d - c).val + c).val = d
    rw [ofN_val, show ofN d - c + c = ofN d from fid (e := v 0 - v 1 + v 1) (e' := v 0) (by decide) [ofN d, c],
      val_ofN hd]

def vadd (r c : List F) : List F := List.zipWith (· + ·) r c
def vsub (r c : List F) : List F := List.zipWith (· - ·) r c

theorem vadd_length (r c : List F) : (vadd r c).length = min r.length c.length := List.length_zipWith ..
theorem vsub_length (r c : List F) : (vsub r c).length = min r.length c.length := List.length_zipWith ..

theorem vsub_vadd : ∀ (r c : List F), r.length = c.length → vsub (vadd r c) c = r
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: r, b :: c, h => by
    show (a + b - b) :: vsub (vadd r c) c = a :: r
    rw [vsub_vadd r c (by simp only [List.length_cons] at h; omega),
      show a + b - b = a from fid (e := v 0 + v 1 - v 1) (e' := v 0) (by decide) [a, b]]

theorem vadd_vsub : ∀ (r c : List F), r.length = c.length → vadd (vsub r c) c = r
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: r, b :: c, h => by
    show (a - b + b) :: vadd (vsub r c) c = a :: r
    rw [vadd_vsub r c (by simp only [List.length_cons] at h; omega),
      show a - b + b = a from fid (e := v 0 - v 1 + v 1) (e' := v 0) (by decide) [a, b]]

/-- **A shift by a fixed vector permutes the vectors.** -/
theorem vsum_shift : ∀ (n : Nat) (c : List F), c.length = n → ∀ f : List F → Nat,
    vsum n (fun r => f (vadd r c)) = vsum n f
  | 0, [], _, _ => rfl
  | 0, _ :: _, h, _ => nomatch h
  | n + 1, [], h, _ => nomatch h
  | n + 1, c0 :: c, hc, f => by
    have hc' : c.length = n := by simp only [List.length_cons] at hc; omega
    show sumTo P (fun d => vsum n (fun l => f (vadd (ofN d :: l) (c0 :: c)))) =
      sumTo P (fun d => vsum n (fun l => f (ofN d :: l)))
    rw [show (fun d => vsum n (fun l => f (vadd (ofN d :: l) (c0 :: c)))) =
        fun d => vsum n (fun l => f ((ofN d + c0) :: l)) from
      funext fun d => vsum_shift n c hc' (fun l => f ((ofN d + c0) :: l))]
    exact sumTo_shiftF (fun a => vsum n (fun l => f (a :: l))) c0

/-- The digits split: a sum over `F^(a+b)` is one over `F^a` of sums over
    `F^b`. -/
theorem vsum_append (b : Nat) : ∀ (a : Nat) (f : List F → Nat),
    vsum (a + b) f = vsum a (fun x => vsum b (fun y => f (x ++ y)))
  | 0, f => by rw [Nat.zero_add]; rfl
  | a + 1, f => by
    rw [Nat.succ_add]
    show sumTo P (fun d => vsum (a + b) (fun l => f (ofN d :: l))) = sumTo P (fun d => vsum a _)
    exact congrArg (sumTo P) (funext fun d => vsum_append b a (fun l => f (ofN d :: l)))

theorem vsum_sumTo (k : Nat) : ∀ (m : Nat) (h : Nat → List F → Nat),
    sumTo k (fun d => vsum m (h d)) = vsum m (fun y => sumTo k (fun d => h d y))
  | 0, _ => rfl
  | m + 1, h => by
    show sumTo k (fun d => sumTo P (fun e => vsum m (fun l => h d (ofN e :: l)))) =
      sumTo P (fun e => vsum m (fun l => sumTo k (fun d => h d (ofN e :: l))))
    rw [sumTo_exch]
    exact congrArg (sumTo P) (funext fun e => vsum_sumTo k m (fun d l => h d (ofN e :: l)))

/-- **The sums exchange.** -/
theorem vsum_comm (m : Nat) : ∀ (n : Nat) (g : List F → List F → Nat),
    vsum n (fun x => vsum m (g x)) = vsum m (fun y => vsum n (fun x => g x y))
  | 0, _ => rfl
  | n + 1, g => by
    show sumTo P (fun d => vsum n (fun x => vsum m (g (ofN d :: x)))) = vsum m (fun y => sumTo P _)
    rw [show (fun d => vsum n (fun x => vsum m (g (ofN d :: x)))) =
        fun d => vsum m (fun y => vsum n (fun x => g (ofN d :: x) y)) from
      funext fun d => vsum_comm m n (fun x => g (ofN d :: x))]
    exact vsum_sumTo P m (fun d y => vsum n (fun x => g (ofN d :: x) y))

-- ---------------------------------------------------------------------------
-- The masked column
-- ---------------------------------------------------------------------------

/-- The column through the trace `t` at `T` and the random values `r` at `R`. -/
def mcol (T R t r : List F) : List F := finterp (T.zip t ++ R.zip r)

/-- Its values at the opened points `S`. -/
def mopen (T R S t r : List F) : List F := S.map (fun s => fval s (mcol T R t r))

theorem zip_mem {L V : List F} {i : Nat} (hi : i < L.length) (hl : L.length = V.length) :
    (L[i], V[i]'(hl ▸ hi)) ∈ L.zip V := by
  have h' : i < (L.zip V).length := by rw [List.length_zip, ← hl, Nat.min_self]; exact hi
  have := List.getElem_mem h'
  rwa [List.getElem_zip] at this

theorem map_fst_zip' {L V : List F} (hl : L.length = V.length) : (L.zip V).map Prod.fst = L :=
  List.map_fst_zip (by omega)

section
variable {T R S : List F} {n : Nat} (hT : T.length = n) (hR : R.length = n) (hTR : (T ++ R).Nodup)
  (hTS : (T ++ S).Nodup) (hS : S.length ≤ n)
include hT hR hTR hTS hS

/-- **Random rows hide a column's openings**: at most `n` opened points,
    none a trace point, take every value vector equally often over the
    random rows, whatever the trace. -/
theorem mask_hides (t t' : List F) (ht : t.length = n) (ht' : t'.length = n) (E : List F → Bool) :
    vsum n (fun r => if E (mopen T R S t r) then 1 else 0) = vsum n (fun r => if E (mopen T R S t' r) then 1 else 0) := by
  -- the difference: `t' - t` on `T`, zero on `S`
  obtain ⟨D, hD⟩ : ∃ D, D = finterp (T.zip (vsub t' t) ++ S.map (fun s => (s, (0 : F)))) := ⟨_, rfl⟩
  have hvl : (vsub t' t).length = n := by rw [vsub_length, ht, ht', Nat.min_self]
  have hDnd : ((T.zip (vsub t' t) ++ S.map (fun s => (s, (0 : F)))).map Prod.fst).Nodup := by
    rw [List.map_append, map_fst_zip' (by rw [hT, hvl]), List.map_map,
      show (Prod.fst ∘ fun s => (s, (0 : F))) = id from funext fun _ => rfl, List.map_id]
    exact hTS
  have hDT : ∀ i (hi : i < n), fval (T[i]'(by omega)) D = t'[i]'(by omega) - t[i]'(by omega) := by
    intro i hi
    have := finterp_eval _ hDnd _ (List.mem_append_left _ (zip_mem (V := vsub t' t) (i := i) (by omega)
      (by rw [hT, hvl])))
    rw [hD, this]
    show (vsub t' t)[i] = _
    unfold vsub; rw [List.getElem_zipWith]
  have hDS : ∀ s ∈ S, fval s D = 0 := fun s hs => by
    rw [hD]; exact finterp_eval _ hDnd (s, 0) (List.mem_append_right _ (List.mem_map.2 ⟨s, hs, rfl⟩))
  have hDl : D.length ≤ n + n := by
    have := finterp_length (T.zip (vsub t' t) ++ S.map (fun s => (s, (0 : F))))
    simp only [List.length_append, List.length_zip, List.length_map, hT, hvl, Nat.min_self] at this
    rw [hD]
    omega
  obtain ⟨c, hcD⟩ : ∃ c, c = R.map (fun x => fval x D) := ⟨_, rfl⟩
  have hc : c.length = n := by rw [hcD, List.length_map, hR]
  -- the shifted randomness opens as the original
  have key : ∀ r : List F, r.length = n → mopen T R S t' (vadd r c) = mopen T R S t r := by
    intro r hr
    have hrc : (vadd r c).length = n := by rw [vadd_length, hr, hc, Nat.min_self]
    have hnd : ((T.zip t' ++ R.zip (vadd r c)).map Prod.fst).Nodup := by
      rw [List.map_append, map_fst_zip' (by rw [hT, ht']), map_fst_zip' (by rw [hR, hrc])]; exact hTR
    have hnd0 : ((T.zip t ++ R.zip r).map Prod.fst).Nodup := by
      rw [List.map_append, map_fst_zip' (by rw [hT, ht]), map_fst_zip' (by rw [hR, hr])]; exact hTR
    have hpl : (mcol T R t' (vadd r c)).length ≤ n + n := by
      have := finterp_length (T.zip t' ++ R.zip (vadd r c))
      simp only [List.length_append, List.length_zip, hT, ht', hR, hrc, Nat.min_self] at this
      exact this
    have hql : (fcadd (mcol T R t r) D).length ≤ n + n := by
      have h1 := fcadd_length (mcol T R t r) D
      have h2 := finterp_length (T.zip t ++ R.zip r)
      simp only [List.length_append, List.length_zip, hT, ht, hR, hr, Nat.min_self] at h2
      exact Nat.le_trans h1 (Nat.max_le.2 ⟨h2, hDl⟩)
    have agree : ∀ x ∈ T ++ R, fval x (mcol T R t' (vadd r c)) = fval x (fcadd (mcol T R t r) D) := by
      intro x hx
      rw [fval_fcadd]
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        have hi' : i < n := by omega
        unfold mcol
        rw [finterp_eval _ hnd _ (List.mem_append_left _ (zip_mem (V := t') hi (by rw [hT, ht']))),
          finterp_eval _ hnd0 _ (List.mem_append_left _ (zip_mem (V := t) hi (by rw [hT, ht]))), hDT i hi']
        exact fid (e := v 0) (e' := v 1 + (v 0 - v 1)) (by decide) [t'[i]'(by omega), t[i]'(by omega)]
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        unfold mcol
        rw [finterp_eval _ hnd _ (List.mem_append_right _ (zip_mem (V := vadd r c) hi (by rw [hR, hrc]))),
          finterp_eval _ hnd0 _ (List.mem_append_right _ (zip_mem (V := r) hi (by rw [hR, hr])))]
        show (vadd r c)[i] = _
        unfold vadd
        rw [List.getElem_zipWith]
        show _ + c[i] = _
        simp only [hcD, List.getElem_map]
    have hall := fagree hpl hql (T ++ R) hTR (by rw [List.length_append, hT, hR]) agree
    unfold mopen
    refine List.map_congr_left (fun s hs => ?_)
    rw [hall s, fval_fcadd, hDS s hs, add_zero']
  -- count
  rw [← vsum_shift n c hc (fun r => if E (mopen T R S t' r) then 1 else 0)]
  exact vsum_congr n (fun r hr => by
    show (if E (mopen T R S t r) = true then 1 else 0) = (if E (mopen T R S t' (vadd r c)) = true then 1 else 0)
    rw [key r hr])

end

end Circuit
