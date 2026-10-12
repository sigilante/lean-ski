import Ski.ZK.Fri

/-!
# FRI's view hides: the random codewords cancel the columns' change

FRI receives, for each committed matrix, its columns batched by powers of
the challenge `α` (`batch`, `wcomb`): the reduced opening at a point `z` is
`α^off (P(X) - P(z))/(X - z)` for `P = Σ_col α^col f_col`, so FRI's whole
view (every layer's commitment, every query's siblings, the last layer) is
a function of these batched polynomials.  Plonky3's hiding PCS appends to
every matrix at least four random codeword columns (`with_random_cols`,
`num_random_codewords ≥ Challenge::DIMENSION`).

The column masks hide by a shift: under a fixed shift of the masks the
columns of one trace are another's plus fixed polynomials vanishing at the
opened points (`mask_shift_ood`, `masks_shift`, `masks_shift_multi`), and
likewise the quotient's chunks under a shift of their random polynomials
(`chunkPolys_rel`).  The codewords absorb the change: when
`1, α, α², α³` are independent over `F` (`(mz α).det ≠ 0`), each `α^k`
has coordinates over `F` in the basis `α^w, …, α^(w+3)` (`lam`), and
shifting the first four codewords by `-Σ_k lam_k[j] D_k` (`cwShift`)
leaves each matrix's batched polynomial unchanged at every point
(`mat_cancel`, `four_gam`), while the codewords' own openings stay put,
the shift vanishing where the differences do (`cwShift_vanish`).  A trace
matrix's codeword is the interpolant of its random values, and shifting
the values shifts it (`cw_rel`, `cws_rel`).

`fri_hides` assembles this: when a count-keeping shift `φ` of the base
randomness turns the real base view into the simulated one and changes
each matrix's columns by polynomials vanishing at its points, and the
codewords' randomness can be shifted by each matrix's `cwShift`, the real
and simulated views, with the codewords' openings and FRI's view of every
batched polynomial, have one distribution.

Scope.  `fri_hides` takes the base shift, the matrices' differences and
the codewords' shift as hypotheses.  The column masks' shift is proved
(`masks_shift_multi`); the quotient chunks' change under a shift is
proved (`chunkPolys_rel`), but its vanishing at the opened points, the
quotient chunk matrices' codewords (randomized like the chunks), and the
instance for the composed PCS (`pcsChunk` with codewords and FRI) are not
assembled here.  Merkle salts and Fiat–Shamir stay assumed.
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Polynomials that differ by given polynomials
-- ---------------------------------------------------------------------------

/-- Each polynomial of the first list is the second's plus the third's, at
    every point of the extension. -/
def PolyRel : List (List F) → List (List F) → List (List F) → Prop
  | p' :: ps', p :: ps, D :: Ds => (∀ z : EF, fvalE z p' = (fvalE z p).add (fvalE z D)) ∧ PolyRel ps' ps Ds
  | [], [], [] => True
  | _, _, _ => False

theorem fval_of_fvalE {p' p D : List F} (h : ∀ z : EF, fvalE z p' = (fvalE z p).add (fvalE z D)) (x : F) :
    fval x p' = fval x p + fval x D := by
  refine congrArg EF.x0 (?_ : EF.ofF (fval x p') = EF.ofF (fval x p + fval x D))
  rw [ofF_fval, h, EF.ofF_add, ofF_fval, ofF_fval]

theorem rel_of_fzero {A B D : List F} (h : FZero (fcdiff A (fcadd B D))) (z : EF) :
    fvalE z A = (fvalE z B).add (fvalE z D) := by
  have e := fvalE_fzero z _ h
  rw [fvalE_fcdiff, fvalE_fcadd] at e
  exact (sub_eq_zero_iff _ _).1 e

/-- Vanishing at the opened points. -/
def Vanish (S : List F) (Z : List EF) (D : List F) : Prop := (∀ s ∈ S, fval s D = 0) ∧ ∀ z ∈ Z, fvalE z D = EF.zero

theorem polyRel_length : ∀ {ps' ps Ds : List (List F)}, PolyRel ps' ps Ds → ps'.length = ps.length
  | [], [], [], _ => rfl
  | _ :: _, _ :: _, _ :: _, ⟨_, hr⟩ => by
    simp only [List.length_cons]; rw [polyRel_length hr]
  | [], _ :: _, _, h => nomatch h
  | [], [], _ :: _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | _ :: _, _ :: _, [], h => nomatch h

theorem polyRel_append : ∀ {ps' ps Ds qs' qs Es : List (List F)}, PolyRel ps' ps Ds → PolyRel qs' qs Es →
    PolyRel (ps' ++ qs') (ps ++ qs) (Ds ++ Es)
  | [], [], [], _, _, _, _, h => h
  | _ :: _, _ :: _, _ :: _, _, _, _, ⟨h, hr⟩, h' => ⟨h, polyRel_append hr h'⟩
  | [], _ :: _, _, _, _, _, h, _ => nomatch h
  | [], [], _ :: _, _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, _, _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h, _ => nomatch h

theorem chunk_last (q q' V n W Wk : EF) :
    q'.add (V.mul (n.mul (W.add Wk))) = (q.add (V.mul (n.mul W))).add ((q'.sub q).add (V.mul (n.mul Wk))) :=
  Q.eq_of_norm (p := (Q.var 1).add ((Q.var 2).mul ((Q.var 3).mul ((Q.var 4).add (Q.var 5)))))
    (q := ((Q.var 0).add ((Q.var 2).mul ((Q.var 3).mul (Q.var 4)))).add
      (((Q.var 1).sub (Q.var 0)).add ((Q.var 2).mul ((Q.var 3).mul (Q.var 5)))))
    (by decide) (env8 q q' V n W Wk EF.zero EF.zero)

theorem cancel4 (A B X : EF) : (A.add X).add (B.add X.neg) = A.add B :=
  Q.eq_of_norm (p := ((Q.var 0).add (Q.var 2)).add ((Q.var 1).add (Q.var 2).neg)) (q := (Q.var 0).add (Q.var 1))
    (by decide) (env3 A B X)

theorem openAll_eq_map (T R S : List F) (Z : List EF) (n : Nat) : ∀ (ts : List (List F)) (rs : List F),
    openAll T R S Z n ts rs = (mpolys T R n ts rs).map (fun p => (S.map (fun s => fval s p), Z.map (fun z => fvalE z p)))
  | [], _ => rfl
  | t :: ts, rs => by
    show (mopen T R S t (rs.take n), Z.map (fun z => fvalE z (mcol T R t (rs.take n)))) :: openAll T R S Z n ts (rs.drop n) =
      (S.map (fun s => fval s (mcol T R t (rs.take n))), Z.map (fun z => fvalE z (mcol T R t (rs.take n)))) ::
        (mpolys T R n ts (rs.drop n)).map _
    rw [openAll_eq_map T R S Z n ts (rs.drop n)]
    rfl

/-- **Related polynomials open alike** where the differences vanish. -/
theorem open_of_rel (S : List F) (Z : List EF) : ∀ (ps' ps Ds : List (List F)), PolyRel ps' ps Ds →
    (∀ D ∈ Ds, Vanish S Z D) →
    ps'.map (fun p => (S.map (fun s => fval s p), Z.map (fun z => fvalE z p))) =
      ps.map (fun p => (S.map (fun s => fval s p), Z.map (fun z => fvalE z p)))
  | [], [], [], _, _ => rfl
  | p' :: ps', p :: ps, D :: Ds, ⟨h, hr⟩, hv => by
    obtain ⟨hvS, hvZ⟩ := hv D List.mem_cons_self
    rw [List.map_cons, List.map_cons, open_of_rel S Z ps' ps Ds hr (fun D' hD => hv D' (List.mem_cons_of_mem _ hD))]
    congr 2
    · exact List.map_congr_left (fun s hs => by rw [fval_of_fvalE h, hvS s hs, add_zero'])
    · exact List.map_congr_left (fun z hz => by rw [h, hvZ z hz, EF.add_zero])
  | [], _ :: _, _, h, _ => nomatch h
  | [], [], _ :: _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | _ :: _, _ :: _, [], h, _ => nomatch h

theorem vadd_append_split {a : Nat} {rs c C : List F} (hc : c.length = a) (hr : a ≤ rs.length) :
    vadd rs (c ++ C) = vadd (rs.take a) c ++ vadd (rs.drop a) C := by
  conv => lhs; rw [← List.take_append_drop a rs]
  unfold vadd
  exact List.zipWith_append (by rw [List.length_take, hc]; omega)

-- ---------------------------------------------------------------------------
-- The masks' shift, column by column and group by group
-- ---------------------------------------------------------------------------

section
variable {T R S : List F} {Z : List EF} {n : Nat} (hT : T.length = n) (hR : R.length = n) (hTR : (T ++ R).Nodup)
  (hTS : ∀ x ∈ T, x ∉ S) (hZ : ∀ z ∈ Z, ∀ x : F, EF.ofF x ≠ z) (hn : S.length + 4 * Z.length ≤ n)
include hT hR hTR hTS hZ hn

/-- **The masks' shift for many columns**: a shift of the random rows under
    which the columns `ts'` are the columns `ts` plus fixed polynomials
    vanishing at the opened points. -/
theorem masks_shift : ∀ (ts ts' : List (List F)), ts.length = ts'.length → (∀ t ∈ ts, t.length = n) →
    (∀ t ∈ ts', t.length = n) →
    ∃ (C : List F) (Ds : List (List F)), C.length = ts.length * n ∧ (∀ D ∈ Ds, Vanish S Z D) ∧
      ∀ rs : List F, rs.length = ts.length * n → PolyRel (mpolys T R n ts' (vadd rs C)) (mpolys T R n ts rs) Ds
  | [], [], _, _, _ => ⟨[], [], (Nat.zero_mul n).symm, ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => trivial⟩⟩
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h
  | t :: ts, t' :: ts', hl, h1, h2 => by
    obtain ⟨c, D, hc, hDS, hDZ, key⟩ := mask_shift_ood hT hR hTR hTS hZ hn t t' (h1 t List.mem_cons_self)
      (h2 t' List.mem_cons_self)
    obtain ⟨C, Ds, hC, hDs, hrel⟩ := masks_shift ts ts' (by simp only [List.length_cons] at hl; omega)
      (fun u hu => h1 u (List.mem_cons_of_mem _ hu)) (fun u hu => h2 u (List.mem_cons_of_mem _ hu))
    refine ⟨c ++ C, D :: Ds, ?_, fun D' hD' => ?_, fun rs hr => ?_⟩
    · rw [List.length_append, hc, hC, List.length_cons, Nat.succ_mul]; omega
    · rcases List.mem_cons.1 hD' with rfl | hD'
      · exact ⟨hDS, hDZ⟩
      · exact hDs D' hD'
    · have hrn : n ≤ rs.length := by rw [hr, List.length_cons, Nat.succ_mul]; omega
      have hrt : (rs.take n).length = n := by rw [List.length_take]; omega
      have hrd : (rs.drop n).length = ts.length * n := by
        rw [List.length_drop, hr, List.length_cons, Nat.succ_mul]; omega
      have hvt : (vadd (rs.take n) c).length = n := by rw [vadd_length, hrt, hc, Nat.min_self]
      rw [vadd_append_split hc hrn]
      show PolyRel (mcol T R t' ((vadd (rs.take n) c ++ vadd (rs.drop n) C).take n) ::
          mpolys T R n ts' ((vadd (rs.take n) c ++ vadd (rs.drop n) C).drop n))
        (mcol T R t (rs.take n) :: mpolys T R n ts (rs.drop n)) (D :: Ds)
      rw [List.take_left' hvt, List.drop_left' hvt]
      exact ⟨rel_of_fzero (key (rs.take n) hrt), hrel (rs.drop n) hrd⟩

end

/-- Every group's masked column polynomials, the randomness split as
    `openMulti` splits it. -/
def mpolysMulti : List MGroup → List (List (List F)) → List F → List (List (List F))
  | g :: gs, ts :: tss, rs => mpolys g.T g.R g.n ts (rs.take (ts.length * g.n)) ::
      mpolysMulti gs tss (rs.drop (ts.length * g.n))
  | _, _, _ => []

/-- Group by group, the columns are related and the differences vanish at
    the group's opened points. -/
def RelMulti : List MGroup → List (List (List F)) → List (List (List F)) → List (List (List F)) → Prop
  | g :: gs, ps' :: pss', ps :: pss, Ds :: Dss => (PolyRel ps' ps Ds ∧ ∀ D ∈ Ds, Vanish g.S g.Z D) ∧
      RelMulti gs pss' pss Dss
  | [], [], [], [] => True
  | _, _, _, _ => False

theorem openMulti_eq : ∀ (gs : List MGroup) (tss : List (List (List F))) (rs : List F),
    openMulti gs tss rs = List.zipWith (fun (g : MGroup) (ps : List (List F)) =>
      ps.map (fun p => (g.S.map (fun s => fval s p), g.Z.map (fun z => fvalE z p)))) gs (mpolysMulti gs tss rs)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | g :: gs, ts :: tss, rs => by
    show openAll g.T g.R g.S g.Z g.n ts (rs.take (ts.length * g.n)) :: openMulti gs tss (rs.drop (ts.length * g.n)) = _
    rw [openAll_eq_map, openMulti_eq gs tss]
    rfl

theorem openMulti_of_rel : ∀ (gs : List MGroup) (pss' pss Dss : List (List (List F))), RelMulti gs pss' pss Dss →
    List.zipWith (fun (g : MGroup) (ps : List (List F)) =>
      ps.map (fun p => (g.S.map (fun s => fval s p), g.Z.map (fun z => fvalE z p)))) gs pss' =
    List.zipWith (fun (g : MGroup) (ps : List (List F)) =>
      ps.map (fun p => (g.S.map (fun s => fval s p), g.Z.map (fun z => fvalE z p)))) gs pss
  | [], [], [], [], _ => rfl
  | g :: gs, ps' :: pss', ps :: pss, Ds :: Dss, ⟨⟨hr, hv⟩, hrest⟩ => by
    rw [List.zipWith_cons_cons, List.zipWith_cons_cons, open_of_rel g.S g.Z ps' ps Ds hr hv,
      openMulti_of_rel gs pss' pss Dss hrest]
  | [], _ :: _, _, _, h => nomatch h
  | [], [], _ :: _, _, h => nomatch h
  | [], [], [], _ :: _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], h => nomatch h

/-- **The masks' shift for every group**: a shift of the column masks under
    which the columns `tss'` are the columns `tss` plus fixed polynomials
    vanishing at each group's opened points. -/
theorem masks_shift_multi : ∀ (gs : List MGroup) (tss tss' : List (List (List F))),
    (∀ g ∈ gs, g.OK) → Shaped gs tss → Shaped gs tss' → tss.map List.length = tss'.map List.length →
    ∃ (C : List F) (Dss : List (List (List F))), C.length = mtotal gs (tss.map List.length) ∧
      ∀ rs : List F, rs.length = mtotal gs (tss.map List.length) →
        RelMulti gs (mpolysMulti gs tss' (vadd rs C)) (mpolysMulti gs tss rs) Dss
  | [], [], [], _, _, _, _ => ⟨[], [], rfl, fun _ _ => trivial⟩
  | [], _ :: _, _, _, h, _, _ => nomatch h
  | [], [], _ :: _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, h, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, h, _ => nomatch h
  | g :: gs, ts :: tss, ts' :: tss', hok, ⟨h1, hs⟩, ⟨h2, hs'⟩, hl => by
    obtain ⟨hT, hR, hTR, hTS, hZ, hn⟩ := hok g List.mem_cons_self
    simp only [List.map_cons, List.cons.injEq] at hl
    obtain ⟨hl1, hl2⟩ := hl
    obtain ⟨c, Ds, hc, hDs, hrel⟩ := masks_shift hT hR hTR hTS hZ hn ts ts' hl1 h1 h2
    obtain ⟨C, Dss, hC, hrel'⟩ := masks_shift_multi gs tss tss' (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      hs hs' hl2
    refine ⟨c ++ C, Ds :: Dss, ?_, fun rs hr => ?_⟩
    · show (c ++ C).length = ts.length * g.n + mtotal gs (tss.map List.length)
      rw [List.length_append, hc, hC]
    · have hr' : rs.length = ts.length * g.n + mtotal gs (tss.map List.length) := hr
      have hrn : ts.length * g.n ≤ rs.length := by omega
      have hrt : (rs.take (ts.length * g.n)).length = ts.length * g.n := by rw [List.length_take]; omega
      have hrd : (rs.drop (ts.length * g.n)).length = mtotal gs (tss.map List.length) := by
        rw [List.length_drop]; omega
      have hvt : (vadd (rs.take (ts.length * g.n)) c).length = ts'.length * g.n := by
        rw [vadd_length, hrt, hc, Nat.min_self, hl1]
      rw [vadd_append_split hc hrn]
      show RelMulti (g :: gs)
        (mpolys g.T g.R g.n ts' ((vadd (rs.take (ts.length * g.n)) c ++ vadd (rs.drop (ts.length * g.n)) C).take
            (ts'.length * g.n)) ::
          mpolysMulti gs tss' ((vadd (rs.take (ts.length * g.n)) c ++ vadd (rs.drop (ts.length * g.n)) C).drop
            (ts'.length * g.n)))
        (mpolys g.T g.R g.n ts (rs.take (ts.length * g.n)) :: mpolysMulti gs tss (rs.drop (ts.length * g.n)))
        (Ds :: Dss)
      rw [List.take_left' hvt, List.drop_left' hvt]
      exact ⟨⟨hrel _ hrt, hDs⟩, hrel' _ hrd⟩

-- ---------------------------------------------------------------------------
-- Four random codewords cancel any change of the columns
-- ---------------------------------------------------------------------------

/-- `x^n`. -/
def apow (x : EF) : Nat → EF
  | 0 => EF.one
  | n + 1 => x.mul (apow x n)

theorem apow_add (x : EF) (a : Nat) : ∀ b, apow x (a + b) = (apow x a).mul (apow x b)
  | 0 => by rw [Nat.add_zero]; show _ = (apow x a).mul EF.one; rw [EF.mul_one]
  | b + 1 => by
    show x.mul (apow x (a + b)) = (apow x a).mul (x.mul (apow x b))
    rw [apow_add x a b, ← EF.mul_assoc, EF.mul_comm x, EF.mul_assoc]

/-- **`α^k` in the basis `α^w, α^(w+1), α^(w+2), α^(w+3)`**: the four
    coordinates over `F`, by `solve_spec`. -/
def lam (α : EF) (w k : Nat) : List F :=
  let e := (apow α k).mul (apow α w).inv
  (mz α).solve e.x0 e.x1 e.x2 e.x3

/-- **Codeword `j`'s shift**, before its sign: `Σ_k lam_k[j] · D_k`, the
    columns counted from `off`. -/
def gam (α : EF) (w j : Nat) : Nat → List (List F) → List F
  | _, [] => []
  | off, D :: Ds => fcadd (fcscale ((lam α w off).getD j 0) D) (gam α w j (off + 1) Ds)

/-- The columns' weighted sum at `z`, `Σ_k α^(off+k) D_k(z)`, FRI's
    batching of one matrix. -/
def wcomb (α : EF) (z : EF) : Nat → List (List F) → EF
  | _, [] => EF.zero
  | off, D :: Ds => ((apow α off).mul (fvalE z D)).add (wcomb α z (off + 1) Ds)

theorem fvalE_gam (α z : EF) (w j : Nat) : ∀ (off : Nat) (Ds : List (List F)),
    fvalE z (gam α w j off Ds) = match Ds with
      | [] => EF.zero
      | D :: Ds' => ((EF.ofF ((lam α w off).getD j 0)).mul (fvalE z D)).add (fvalE z (gam α w j (off + 1) Ds'))
  | _, [] => rfl
  | off, D :: Ds => by
    show fvalE z (fcadd (fcscale _ D) _) = _
    rw [fvalE_fcadd, fvalE_fcscale]

theorem lam_four (α : EF) (w kk : Nat) : ∃ a b c d : F, lam α w kk = [a, b, c, d] := ⟨_, _, _, _, rfl⟩

theorem cancel_aw (aw P d : EF) (h : aw.mul aw.inv = EF.one) : (aw.mul (P.mul aw.inv)).mul d = P.mul d := by
  rw [mulE_swap3 aw P aw.inv, h, EF.mul_one]

theorem half_step (l0 l1 d G0 G1 o p1 : EF) :
    (((l0.mul d).add G0).mul o).add (((l1.mul d).add G1).mul p1) =
      (((l0.mul o).add (l1.mul p1)).mul d).add ((G0.mul o).add (G1.mul p1)) :=
  Q.eq_of_norm
    (p := ((((Q.var 0).mul (Q.var 2)).add (Q.var 3)).mul (Q.var 5)).add ((((Q.var 1).mul (Q.var 2)).add (Q.var 4)).mul (Q.var 6)))
    (q := ((((Q.var 0).mul (Q.var 5)).add ((Q.var 1).mul (Q.var 6))).mul (Q.var 2)).add
      (((Q.var 3).mul (Q.var 5)).add ((Q.var 4).mul (Q.var 6))))
    (by decide) (env8 l0 l1 d G0 G1 o p1 EF.zero)

theorem pair_join (A B C D d : EF) : ((A.mul d).add B).add ((C.mul d).add D) = ((A.add C).mul d).add (B.add D) :=
  Q.eq_of_norm (p := (((Q.var 0).mul (Q.var 4)).add (Q.var 1)).add (((Q.var 2).mul (Q.var 4)).add (Q.var 3)))
    (q := (((Q.var 0).add (Q.var 2)).mul (Q.var 4)).add ((Q.var 1).add (Q.var 3))) (by decide)
    (env8 A B C D d EF.zero EF.zero EF.zero)

theorem distrib_aw (aw T d U : EF) : aw.mul ((T.mul d).add U) = ((aw.mul T).mul d).add (aw.mul U) :=
  Q.eq_of_norm (p := (Q.var 0).mul (((Q.var 1).mul (Q.var 2)).add (Q.var 3)))
    (q := (((Q.var 0).mul (Q.var 1)).mul (Q.var 2)).add ((Q.var 0).mul (Q.var 3))) (by decide) (env4 aw T d U)

/-- `aw · (G0 + G1 α + G2 α² + G3 α³)` for the four codeword sums. -/
def four (α aw G0 G1 G2 G3 : EF) : EF :=
  aw.mul (((G0.mul EF.one).add (G1.mul α)).add ((G2.mul (α.mul α)).add (G3.mul ((α.mul α).mul α))))

/-- **The codewords' sums recombine to the columns'**: with `α^w ≠ 0`,
    `α^w Σ_j α^j Σ_k lam_k[j] D_k(z) = Σ_k α^(off+k) D_k(z)`. -/
theorem four_gam {α : EF} (hd : (mz α).det ≠ 0) (haw : ∀ w, apow α w ≠ EF.zero) (w : Nat) (z : EF) :
    ∀ (off : Nat) (Ds : List (List F)),
    four α (apow α w) (fvalE z (gam α w 0 off Ds)) (fvalE z (gam α w 1 off Ds)) (fvalE z (gam α w 2 off Ds))
      (fvalE z (gam α w 3 off Ds)) = wcomb α z off Ds
  | _, [] => by
    show four α (apow α w) EF.zero EF.zero EF.zero EF.zero = EF.zero
    unfold four
    rw [EF.zero_mul, EF.zero_mul, EF.zero_mul, EF.zero_mul, EF.add_zero, EF.add_zero, EF.mul_zero]
  | off, D :: Ds => by
    rw [fvalE_gam, fvalE_gam, fvalE_gam, fvalE_gam]
    show four α (apow α w) _ _ _ _ = ((apow α off).mul (fvalE z D)).add (wcomb α z (off + 1) Ds)
    rw [← four_gam hd haw w z (off + 1) Ds]
    obtain ⟨a, b, c, d, hl⟩ := lam_four α w off
    have hs := solve_spec α hd ((apow α off).mul (apow α w).inv)
    rw [show (mz α).solve ((apow α off).mul (apow α w).inv).x0 ((apow α off).mul (apow α w).inv).x1
        ((apow α off).mul (apow α w).inv).x2 ((apow α off).mul (apow α w).inv).x3 = lam α w off from rfl, hl,
      fvalE4] at hs
    rw [hl]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    unfold four
    rw [half_step, half_step, pair_join, distrib_aw, hs, cancel_aw _ _ _ (EF.mul_inv (haw w))]

/-- **The codewords' shift** for a matrix of `w` columns whose
    differences are `Ds`: `-gam_j` for the first four codewords, nothing
    for the rest. -/
def cwShift (α : EF) (w ncw : Nat) (Ds : List (List F)) : List (List F) :=
  (List.range ncw).map fun j => if j < 4 then fcscale (-1) (gam α w j 0 Ds) else []

theorem wcomb_append (α z : EF) : ∀ (off : Nat) (A B : List (List F)),
    wcomb α z off (A ++ B) = (wcomb α z off A).add (wcomb α z (off + A.length) B)
  | off, [], B => by show wcomb α z off B = EF.zero.add (wcomb α z (off + 0) B); rw [EF.zero_add, Nat.add_zero]
  | off, D :: A, B => by
    show ((apow α off).mul (fvalE z D)).add (wcomb α z (off + 1) (A ++ B)) =
      (((apow α off).mul (fvalE z D)).add (wcomb α z (off + 1) A)).add (wcomb α z (off + (A.length + 1)) B)
    rw [wcomb_append α z (off + 1) A B, EF.add_assoc, show off + 1 + A.length = off + (A.length + 1) by omega]

theorem rel_step (a p D W W' : EF) : (a.mul (p.add D)).add (W.add W') = ((a.mul p).add W).add ((a.mul D).add W') :=
  Q.eq_of_norm (p := ((Q.var 0).mul ((Q.var 1).add (Q.var 2))).add ((Q.var 3).add (Q.var 4)))
    (q := (((Q.var 0).mul (Q.var 1)).add (Q.var 3)).add (((Q.var 0).mul (Q.var 2)).add (Q.var 4))) (by decide)
    (env8 a p D W W' EF.zero EF.zero EF.zero)

/-- Related columns batch to the original batch plus the differences'. -/
theorem wcomb_rel (α z : EF) : ∀ (off : Nat) (ps' ps Ds : List (List F)), PolyRel ps' ps Ds →
    wcomb α z off ps' = (wcomb α z off ps).add (wcomb α z off Ds)
  | _, [], [], [], _ => by show EF.zero = EF.zero.add EF.zero; rw [EF.add_zero]
  | off, p' :: ps', p :: ps, D :: Ds, ⟨h, hr⟩ => by
    show ((apow α off).mul (fvalE z p')).add (wcomb α z (off + 1) ps') =
      (((apow α off).mul (fvalE z p)).add (wcomb α z (off + 1) ps)).add
        (((apow α off).mul (fvalE z D)).add (wcomb α z (off + 1) Ds))
    rw [h z, wcomb_rel α z (off + 1) ps' ps Ds hr, rel_step]
  | _, [], _ :: _, _, h => nomatch h
  | _, [], [], _ :: _, h => nomatch h
  | _, _ :: _, [], _, h => nomatch h
  | _, _ :: _, _ :: _, [], h => nomatch h

theorem wcomb_nils (α z : EF) : ∀ (off : Nat) (L : List Nat),
    wcomb α z off (L.map (fun _ => ([] : List F))) = EF.zero
  | _, [] => rfl
  | off, _ :: L => by
    show ((apow α off).mul (fvalE z [])).add (wcomb α z (off + 1) (L.map _)) = EF.zero
    rw [wcomb_nils α z (off + 1) L, show fvalE z ([] : List F) = EF.zero from rfl, EF.mul_zero, EF.add_zero]

theorem cwA (p0 p1 p2 p3 G0 G1 G2 G3 : EF) :
    (p0.mul (EF.one.neg.mul G0)).add ((p1.mul (EF.one.neg.mul G1)).add
      ((p2.mul (EF.one.neg.mul G2)).add ((p3.mul (EF.one.neg.mul G3)).add EF.zero))) =
    ((p0.mul G0).add ((p1.mul G1).add ((p2.mul G2).add (p3.mul G3)))).neg :=
  Q.eq_of_norm
    (p := ((Q.var 0).mul ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 4))).add (((Q.var 1).mul
      ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 5))).add (((Q.var 2).mul ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 6))).add
      (((Q.var 3).mul ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 7))).add (⟨k 0, k 0, k 0, k 0⟩ : Q)))))
    (q := (((Q.var 0).mul (Q.var 4)).add (((Q.var 1).mul (Q.var 5)).add (((Q.var 2).mul (Q.var 6)).add
      ((Q.var 3).mul (Q.var 7))))).neg)
    (by decide) (env8 p0 p1 p2 p3 G0 G1 G2 G3)

theorem cwB (aw α a2 a3 G0 G1 G2 G3 : EF) :
    (aw.mul G0).add (((α.mul aw).mul G1).add (((a2.mul aw).mul G2).add ((a3.mul aw).mul G3))) =
      aw.mul (((G0.mul EF.one).add (G1.mul α)).add ((G2.mul a2).add (G3.mul a3))) :=
  Q.eq_of_norm
    (p := ((Q.var 0).mul (Q.var 4)).add ((((Q.var 1).mul (Q.var 0)).mul (Q.var 5)).add ((((Q.var 2).mul (Q.var 0)).mul
      (Q.var 6)).add (((Q.var 3).mul (Q.var 0)).mul (Q.var 7)))))
    (q := (Q.var 0).mul ((((Q.var 4).mul (⟨k 1, k 0, k 0, k 0⟩ : Q)).add ((Q.var 5).mul (Q.var 1))).add
      (((Q.var 6).mul (Q.var 2)).add ((Q.var 7).mul (Q.var 3)))))
    (by decide) (env8 aw α a2 a3 G0 G1 G2 G3)

theorem cwC (aw α G0 G1 G2 G3 : EF) :
    (aw.mul G0).add (((α.mul aw).mul G1).add (((α.mul (α.mul aw)).mul G2).add ((α.mul (α.mul (α.mul aw))).mul G3))) =
      four α aw G0 G1 G2 G3 := by
  unfold four
  rw [← EF.mul_assoc α α aw, ← EF.mul_assoc α (α.mul α) aw, EF.mul_comm α (α.mul α)]
  exact cwB aw α (α.mul α) ((α.mul α).mul α) G0 G1 G2 G3

/-- **The first four codewords' shift batches to minus the columns'**. -/
theorem wcomb_cwShift (α z : EF) (w : Nat) (Ds : List (List F)) (ncw : Nat) (hncw : 4 ≤ ncw) :
    wcomb α z w (cwShift α w ncw Ds) = (four α (apow α w) (fvalE z (gam α w 0 0 Ds)) (fvalE z (gam α w 1 0 Ds))
      (fvalE z (gam α w 2 0 Ds)) (fvalE z (gam α w 3 0 Ds))).neg := by
  obtain ⟨m, rfl⟩ : ∃ m, ncw = 4 + m := ⟨ncw - 4, by omega⟩
  have hr : List.range (4 + m) = [0, 1, 2, 3] ++ (List.range m).map (· + 4) := by
    rw [List.range_add]; simp only [Nat.add_comm]; rfl
  unfold cwShift
  rw [hr, List.map_append, wcomb_append]
  have hn : ((List.range m).map (· + 4)).map (fun j => if j < 4 then fcscale (-1) (gam α w j 0 Ds) else []) =
      ((List.range m).map (· + 4)).map (fun _ => ([] : List F)) :=
    List.map_congr_left (fun j hj => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hj
      rw [if_neg (by omega)])
  rw [hn, wcomb_nils, EF.add_zero]
  show ((apow α w).mul (fvalE z (fcscale (-1) (gam α w 0 0 Ds)))).add
    (((apow α (w + 1)).mul (fvalE z (fcscale (-1) (gam α w 1 0 Ds)))).add
    (((apow α (w + 1 + 1)).mul (fvalE z (fcscale (-1) (gam α w 2 0 Ds)))).add
    (((apow α (w + 1 + 1 + 1)).mul (fvalE z (fcscale (-1) (gam α w 3 0 Ds)))).add EF.zero))) = _
  rw [fvalE_fcscale, fvalE_fcscale, fvalE_fcscale, fvalE_fcscale, ofF_neg', show EF.ofF 1 = EF.one from rfl, cwA]
  exact congrArg EF.neg (cwC _ _ _ _ _ _)

/-- **A matrix's random codewords cancel its columns' change**: with
    `1, α, α², α³` independent and four codewords, columns that change by
    `Ds` and codewords that change by `cwShift` batch, at every point, as
    before. -/
theorem mat_cancel {α : EF} (hd : (mz α).det ≠ 0) (haw : ∀ w, apow α w ≠ EF.zero) {w ncw : Nat} (hncw : 4 ≤ ncw)
    {ps' ps Ds cws' cws : List (List F)} (hl : ps.length = w) (hr : PolyRel ps' ps Ds)
    (hc : PolyRel cws' cws (cwShift α w ncw Ds)) (z : EF) :
    wcomb α z 0 (ps' ++ cws') = wcomb α z 0 (ps ++ cws) := by
  have hl' : ps'.length = w := by rw [← hl]; exact polyRel_length hr
  rw [wcomb_append, wcomb_append, hl, hl', Nat.zero_add, wcomb_rel α z 0 ps' ps Ds hr, wcomb_rel α z w cws' cws _ hc,
    wcomb_cwShift α z w Ds ncw hncw, ← four_gam hd haw w z 0 Ds]
  exact cancel4 _ _ _

/-- The codewords' shift vanishes where every difference does. -/
theorem gam_vanish (α : EF) (w j : Nat) {S : List F} {Z : List EF} :
    ∀ (off : Nat) (Ds : List (List F)), (∀ D ∈ Ds, Vanish S Z D) → Vanish S Z (gam α w j off Ds)
  | _, [], _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | off, D :: Ds, h => by
    obtain ⟨hS, hZ⟩ := gam_vanish α w j (off + 1) Ds (fun D' hD' => h D' (List.mem_cons_of_mem _ hD'))
    obtain ⟨hS0, hZ0⟩ := h D List.mem_cons_self
    refine ⟨fun s hs => ?_, fun z hz => ?_⟩
    · show fval s (fcadd (fcscale _ D) _) = 0
      rw [fval_fcadd, fval_fcscale, hS0 s hs, hS s hs, mul_zero', add_zero']
    · show fvalE z (fcadd (fcscale _ D) _) = EF.zero
      rw [fvalE_fcadd, fvalE_fcscale, hZ0 z hz, hZ z hz, EF.mul_zero, EF.add_zero]

theorem cwShift_vanish (α : EF) (w ncw : Nat) {S : List F} {Z : List EF} (Ds : List (List F))
    (h : ∀ D ∈ Ds, Vanish S Z D) : ∀ G ∈ cwShift α w ncw Ds, Vanish S Z G := by
  intro G hG
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hG
  split
  · obtain ⟨hS, hZ⟩ := gam_vanish α w j 0 Ds h
    refine ⟨fun s hs => ?_, fun z hz => ?_⟩
    · rw [fval_fcscale, hS s hs, mul_zero']
    · rw [fvalE_fcscale, hZ z hz, EF.mul_zero]
  · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

-- ---------------------------------------------------------------------------
-- A codeword's shift through its random values
-- ---------------------------------------------------------------------------

/-- **A codeword**: the interpolant of its random values on its domain. -/
def cwPoly (Dom vals : List F) : List F := finterp (Dom.zip vals)

/-- **Shifting a codeword's values by `G`'s adds `G`** to it, `G` of at
    most `|Dom|` coefficients. -/
theorem cw_rel {Dom : List F} (hD : Dom.Nodup) {G vals : List F} (hv : vals.length = Dom.length)
    (hG : G.length ≤ Dom.length) (z : EF) :
    fvalE z (cwPoly Dom (vadd vals (Dom.map (fval · G)))) = (fvalE z (cwPoly Dom vals)).add (fvalE z G) := by
  have hgl : (Dom.map (fval · G)).length = Dom.length := List.length_map _
  have hvl : (vadd vals (Dom.map (fval · G))).length = Dom.length := by rw [vadd_length, hv, hgl, Nat.min_self]
  have hnd' : ((Dom.zip (vadd vals (Dom.map (fval · G)))).map Prod.fst).Nodup := by
    rw [map_fst_zip' (by rw [hvl])]; exact hD
  have hnd0 : ((Dom.zip vals).map Prod.fst).Nodup := by rw [map_fst_zip' (by rw [hv])]; exact hD
  refine rel_of_fzero (fagree_zero (N := Dom.length) ?_ ?_ Dom hD rfl (fun x hx => ?_)) z
  · have := finterp_length (Dom.zip (vadd vals (Dom.map (fval · G))))
    rw [List.length_zip, hvl, Nat.min_self] at this; exact this
  · have h1 := fcadd_length (finterp (Dom.zip vals)) G
    have h2 := finterp_length (Dom.zip vals)
    rw [List.length_zip, hv, Nat.min_self] at h2
    exact Nat.le_trans h1 (Nat.max_le.2 ⟨h2, hG⟩)
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    unfold cwPoly
    rw [fval_fcadd, finterp_eval _ hnd' _ (zip_mem (V := vadd vals (Dom.map (fval · G))) hi (by rw [hvl])),
      finterp_eval _ hnd0 _ (zip_mem (V := vals) hi (by rw [hv]))]
    show (vadd vals (Dom.map (fval · G)))[i]'(by rw [hvl]; exact hi) = _
    unfold vadd
    rw [List.getElem_zipWith, List.getElem_map]

/-- `k` codewords read `L` values each from `rs`. -/
def cwPolys (Dom : List F) (L : Nat) : Nat → List F → List (List F)
  | 0, _ => []
  | k + 1, rs => cwPoly Dom (rs.take L) :: cwPolys Dom L k (rs.drop L)

/-- The shift of `k` codewords' values by the polynomials `Gs`. -/
def cwVals (Dom : List F) : List (List F) → List F
  | [] => []
  | G :: Gs => Dom.map (fval · G) ++ cwVals Dom Gs

theorem cwVals_length (Dom : List F) : ∀ Gs : List (List F), (cwVals Dom Gs).length = Gs.length * Dom.length
  | [] => by show 0 = 0 * _; rw [Nat.zero_mul]
  | G :: Gs => by
    show (Dom.map (fval · G) ++ cwVals Dom Gs).length = (Gs.length + 1) * Dom.length
    rw [List.length_append, List.length_map, cwVals_length Dom Gs, Nat.succ_mul, Nat.add_comm]

/-- **The codewords' values shifted by `Gs`** are the codewords plus `Gs`. -/
theorem cws_rel {Dom : List F} (hD : Dom.Nodup) : ∀ (Gs : List (List F)) (rs : List F),
    (∀ G ∈ Gs, G.length ≤ Dom.length) → rs.length = Gs.length * Dom.length →
    PolyRel (cwPolys Dom Dom.length Gs.length (vadd rs (cwVals Dom Gs))) (cwPolys Dom Dom.length Gs.length rs) Gs
  | [], _, _, _ => trivial
  | G :: Gs, rs, hG, hr => by
    have hrn : Dom.length ≤ rs.length := by rw [hr, List.length_cons, Nat.succ_mul]; omega
    have hrt : (rs.take Dom.length).length = Dom.length := by rw [List.length_take]; omega
    have hrd : (rs.drop Dom.length).length = Gs.length * Dom.length := by
      rw [List.length_drop, hr, List.length_cons, Nat.succ_mul]; omega
    have hml : (Dom.map (fval · G)).length = Dom.length := List.length_map _
    have hvt : (vadd (rs.take Dom.length) (Dom.map (fval · G))).length = Dom.length := by
      rw [vadd_length, hrt, hml, Nat.min_self]
    show PolyRel (cwPoly Dom ((vadd rs (Dom.map (fval · G) ++ cwVals Dom Gs)).take Dom.length) ::
        cwPolys Dom Dom.length Gs.length ((vadd rs (Dom.map (fval · G) ++ cwVals Dom Gs)).drop Dom.length))
      (cwPoly Dom (rs.take Dom.length) :: cwPolys Dom Dom.length Gs.length (rs.drop Dom.length)) (G :: Gs)
    rw [vadd_append_split hml hrn, List.take_left' hvt, List.drop_left' hvt]
    exact ⟨cw_rel hD hrt (hG G List.mem_cons_self), cws_rel hD Gs (rs.drop Dom.length)
      (fun G' hG' => hG G' (List.mem_cons_of_mem _ hG')) hrd⟩

-- ---------------------------------------------------------------------------
-- The chunks' polynomials, and their change under a shift
-- ---------------------------------------------------------------------------

/-- **A chunk's polynomial**: `q + c · fvan H · r`. -/
def chunkPoly (H : List F) (c : F) (q r : List F) : List F := fcadd q (fcscale c (fmul (fvan H) r))

theorem fvalE_chunkPoly (H : List F) (c : F) (q r : List F) (z : EF) :
    fvalE z (chunkPoly H c q r) = chunkAtE H c q r z := by
  unfold chunkPoly chunkAtE
  rw [fvalE_fcadd, fvalE_fcscale, fvalE_fmul, EF.mul_assoc]

theorem fval_chunkPoly (H : List F) (c : F) (q r : List F) (x : F) : fval x (chunkPoly H c q r) = chunkAt H c q r x := by
  unfold chunkPoly chunkAt
  rw [fval_fcadd, fval_fcscale, fval_fmul, mul_assoc']

/-- The chunks other than the last, their random polynomials read `h`
    coefficients a chunk. -/
def firstPolys (h : Nat) : List Chunk → List (List F) → List F → List (List F)
  | ch :: cs, q :: qs, rs => chunkPoly ch.H ch.c q (rs.take h) :: firstPolys h cs qs (rs.drop h)
  | _, _, _ => []

/-- **Every chunk's polynomial**, the last with `-Σ m_i r_i`. -/
def chunkPolys (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql rs : List F) :
    List (List F) :=
  firstPolys h cs qs rs ++ [chunkPoly Hl cl ql (fcscale (-1) (wsumR h cs rs))]

/-- The chunks' changes: the data's change plus `c · fvan H` times the
    random polynomials' shift. -/
def firstDiffs (h : Nat) : List Chunk → List (List F) → List (List F) → List F → List (List F)
  | ch :: cs, q :: qs, q' :: qs', K => chunkPoly ch.H ch.c (fcdiff q' q) (K.take h) :: firstDiffs h cs qs qs' (K.drop h)
  | _, _, _, _ => []

def chunkDiffs (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) (qs qs' : List (List F)) (ql ql' K : List F) :
    List (List F) :=
  firstDiffs h cs qs qs' K ++ [chunkPoly Hl cl (fcdiff ql' ql) (fcscale (-1) (wsumR h cs K))]

theorem chunk_step (q q' V r k : EF) : q'.add (V.mul (r.add k)) = (q.add (V.mul r)).add ((q'.sub q).add (V.mul k)) :=
  Q.eq_of_norm (p := (Q.var 1).add ((Q.var 2).mul ((Q.var 3).add (Q.var 4))))
    (q := ((Q.var 0).add ((Q.var 2).mul (Q.var 3))).add (((Q.var 1).sub (Q.var 0)).add ((Q.var 2).mul (Q.var 4))))
    (by decide) (env8 q q' V r k EF.zero EF.zero EF.zero)

theorem chunkPoly_rel (H : List F) (c : F) (q q' r k : List F) (hk : r.length = k.length) (z : EF) :
    fvalE z (chunkPoly H c q' (vadd r k)) = (fvalE z (chunkPoly H c q r)).add (fvalE z (chunkPoly H c (fcdiff q' q) k)) := by
  rw [fvalE_chunkPoly, fvalE_chunkPoly, fvalE_chunkPoly]
  unfold chunkAtE
  rw [fvalE_vadd z r k hk, fvalE_fcdiff]
  exact chunk_step _ _ _ _ _

theorem firstPolys_rel (h : Nat) : ∀ (cs : List Chunk) (qs qs' : List (List F)) (rs K : List F),
    qs.length = cs.length → qs'.length = cs.length → rs.length = cs.length * h → K.length = cs.length * h →
    PolyRel (firstPolys h cs qs' (vadd rs K)) (firstPolys h cs qs rs) (firstDiffs h cs qs qs' K)
  | [], [], [], _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, _, h1, _, _, _ => nomatch h1
  | [], [], _ :: _, _, _, _, h2, _, _ => nomatch h2
  | _ :: _, [], _, _, _, h1, _, _, _ => nomatch h1
  | _ :: _, _ :: _, [], _, _, _, h2, _, _ => nomatch h2
  | ch :: cs, q :: qs, q' :: qs', rs, K, h1, h2, hr, hK => by
    have ht : (rs.take h).length = (K.take h).length := by rw [List.length_take, List.length_take, hr, hK]
    have hr' : (rs.drop h).length = cs.length * h := by rw [List.length_drop, hr, List.length_cons, Nat.succ_mul]; omega
    have hK' : (K.drop h).length = cs.length * h := by rw [List.length_drop, hK, List.length_cons, Nat.succ_mul]; omega
    show PolyRel (chunkPoly ch.H ch.c q' ((vadd rs K).take h) :: firstPolys h cs qs' ((vadd rs K).drop h))
      (chunkPoly ch.H ch.c q (rs.take h) :: firstPolys h cs qs (rs.drop h))
      (chunkPoly ch.H ch.c (fcdiff q' q) (K.take h) :: firstDiffs h cs qs qs' (K.drop h))
    unfold vadd
    rw [List.take_zipWith, List.drop_zipWith]
    exact ⟨chunkPoly_rel ch.H ch.c q q' (rs.take h) (K.take h) ht,
      firstPolys_rel h cs qs qs' (rs.drop h) (K.drop h) (by simp only [List.length_cons] at h1; omega)
        (by simp only [List.length_cons] at h2; omega) hr' hK'⟩

/-- **A shift changes the chunks by fixed polynomials**: the data's change
    plus `c · fvan H` times the random polynomials' shift, the last's by
    `-Σ m_i K_i`. -/
theorem chunkPolys_rel (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) (qs qs' : List (List F)) (ql ql' rs K : List F)
    (h1 : qs.length = cs.length) (h2 : qs'.length = cs.length) (hr : rs.length = cs.length * h)
    (hK : K.length = cs.length * h) :
    PolyRel (chunkPolys h cs Hl cl qs' ql' (vadd rs K)) (chunkPolys h cs Hl cl qs ql rs)
      (chunkDiffs h cs Hl cl qs qs' ql ql' K) := by
  unfold chunkPolys chunkDiffs
  refine polyRel_append (firstPolys_rel h cs qs qs' rs K h1 h2 hr hK) ⟨fun z => ?_, trivial⟩
  rw [fvalE_chunkPoly, fvalE_chunkPoly, fvalE_chunkPoly]
  unfold chunkAtE
  rw [fvalE_fcscale, fvalE_fcscale, fvalE_fcscale, wsumR_vaddE z h cs rs K hr hK, fvalE_fcdiff]
  exact chunk_last _ _ _ _ _ _

-- ---------------------------------------------------------------------------
-- FRI's view hides
-- ---------------------------------------------------------------------------

/-- **A committed matrix**: its opened points, its column count `w`, and
    its random codewords' count. -/
structure Mat where
  S : List F
  Z : List EF
  w : Nat
  ncw : Nat

/-- A list of polynomials opened at `S` and `Z`. -/
def openPolys (S : List F) (Z : List EF) (ps : List (List F)) : List (List F × List EF) :=
  ps.map fun p => (S.map (fun s => fval s p), Z.map (fun z => fvalE z p))

/-- **What FRI receives**: each matrix's columns and codewords batched by
    powers of `α`, as a function on the extension. -/
def batch (α : EF) (Ps Cs : List (List (List F))) : List (EF → EF) :=
  List.zipWith (fun P C => fun z => wcomb α z 0 (P ++ C)) Ps Cs

/-- The matrices' columns are related, the differences vanish at each
    matrix's points, and each matrix has its `w` columns. -/
def RelAll : List Mat → List (List (List F)) → List (List (List F)) → List (List (List F)) → Prop
  | m :: ms, P' :: Ps', P :: Ps, Ds :: Dss => (PolyRel P' P Ds ∧ (∀ D ∈ Ds, Vanish m.S m.Z D) ∧ P.length = m.w) ∧
      RelAll ms Ps' Ps Dss
  | [], [], [], [] => True
  | _, _, _, _ => False

/-- The codewords are related by each matrix's `cwShift`. -/
def CwRel (α : EF) : List Mat → List (List (List F)) → List (List (List F)) → List (List (List F)) → Prop
  | m :: ms, C' :: Cs', C :: Cs, Ds :: Dss => PolyRel C' C (cwShift α m.w m.ncw Ds) ∧ CwRel α ms Cs' Cs Dss
  | [], [], [], [] => True
  | _, _, _, _ => False

theorem batch_eq {α : EF} (hd : (mz α).det ≠ 0) (haw : ∀ w, apow α w ≠ EF.zero) :
    ∀ (ms : List Mat) (Ps' Ps Cs' Cs Dss : List (List (List F))), (∀ m ∈ ms, 4 ≤ m.ncw) →
    RelAll ms Ps' Ps Dss → CwRel α ms Cs' Cs Dss → batch α Ps' Cs' = batch α Ps Cs
  | [], [], [], [], [], [], _, _, _ => rfl
  | m :: ms, P' :: Ps', P :: Ps, C' :: Cs', C :: Cs, Ds :: Dss, hn, ⟨⟨hr, _, hw⟩, hR⟩, ⟨hc, hC⟩ => by
    unfold batch
    rw [List.zipWith_cons_cons, List.zipWith_cons_cons]
    congr 1
    · funext z
      exact mat_cancel hd haw (hn m List.mem_cons_self) hw hr hc z
    · exact batch_eq hd haw ms Ps' Ps Cs' Cs Dss (fun m' hm' => hn m' (List.mem_cons_of_mem _ hm')) hR hC
  | [], _ :: _, _, _, _, _, _, h, _ => nomatch h
  | [], [], _ :: _, _, _, _, _, h, _ => nomatch h
  | [], [], [], _, _, _ :: _, _, h, _ => nomatch h
  | [], [], [], _ :: _, _, [], _, _, h => nomatch h
  | [], [], [], [], _ :: _, [], _, _, h => nomatch h
  | _ :: _, [], _, _, _, _, _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, _, _, h, _ => nomatch h
  | _ :: _, _ :: _, _ :: _, _, _, [], _, h, _ => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _ :: _, _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _ :: _, _, _, h => nomatch h

theorem cwOpen_eq {α : EF} : ∀ (ms : List Mat) (Ps' Ps Cs' Cs Dss : List (List (List F))),
    RelAll ms Ps' Ps Dss → CwRel α ms Cs' Cs Dss →
    List.zipWith (fun (m : Mat) C => openPolys m.S m.Z C) ms Cs' = List.zipWith (fun (m : Mat) C => openPolys m.S m.Z C) ms Cs
  | [], _, _, _, _, _, _, _ => rfl
  | m :: ms, P' :: Ps', P :: Ps, C' :: Cs', C :: Cs, Ds :: Dss, ⟨⟨_, hv, _⟩, hR⟩, ⟨hc, hC⟩ => by
    rw [List.zipWith_cons_cons, List.zipWith_cons_cons, cwOpen_eq ms Ps' Ps Cs' Cs Dss hR hC]
    exact congrArg (· :: _) (open_of_rel m.S m.Z C' C _ hc (cwShift_vanish α m.w m.ncw Ds hv))
  | _ :: _, [], _, _, _, _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h, _ => nomatch h
  | _ :: _, _ :: _, _ :: _, _, _, [], h, _ => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _ :: _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _ :: _, _, h => nomatch h

/-- **FRI's view hides**: when a shift `φ` of the base randomness, which
    keeps every count, turns the real base view into the simulated one and
    changes each matrix's columns by polynomials vanishing at its opened
    points, and the codewords' randomness can be shifted by each matrix's
    `cwShift`, then the real and simulated views with the codewords'
    openings and FRI's view of every batched polynomial have one
    distribution. -/
theorem fri_hides {A V : Type} {α : EF} (hd : (mz α).det ≠ 0) (haw : ∀ w, apow α w ≠ EF.zero)
    (ms : List Mat) (hn : ∀ m ∈ ms, 4 ≤ m.ncw) {N1 N2 : Nat}
    (Br Bs : List F → A) (Pr Ps : List F → List (List (List F))) (Cw : List F → List (List (List F)))
    (fri : List (EF → EF) → V) (φ : List F → List F)
    (hφ : ∀ g : List F → Nat, vsum N1 (fun ρ => g (φ ρ)) = vsum N1 g)
    (hB : ∀ ρ : List F, ρ.length = N1 → Bs (φ ρ) = Br ρ)
    (Dss : List F → List (List (List F))) (hP : ∀ ρ : List F, ρ.length = N1 → RelAll ms (Ps (φ ρ)) (Pr ρ) (Dss ρ))
    (vec : List F → List F) (hvec : ∀ ρ : List F, ρ.length = N1 → (vec ρ).length = N2)
    (hC : ∀ ρ γ : List F, ρ.length = N1 → γ.length = N2 → CwRel α ms (Cw (vadd γ (vec ρ))) (Cw γ) (Dss ρ))
    (E : A → List (List (List F × List EF)) → V → Bool) :
    vsum N1 (fun ρ => vsum N2 (fun γ =>
        if E (Br ρ) (List.zipWith (fun (m : Mat) C => openPolys m.S m.Z C) ms (Cw γ)) (fri (batch α (Pr ρ) (Cw γ)))
        then 1 else 0)) =
      vsum N1 (fun ρ => vsum N2 (fun γ =>
        if E (Bs ρ) (List.zipWith (fun (m : Mat) C => openPolys m.S m.Z C) ms (Cw γ)) (fri (batch α (Ps ρ) (Cw γ)))
        then 1 else 0)) := by
  rw [← hφ (fun ρ => vsum N2 (fun γ =>
    if E (Bs ρ) (List.zipWith (fun (m : Mat) C => openPolys m.S m.Z C) ms (Cw γ)) (fri (batch α (Ps ρ) (Cw γ)))
    then 1 else 0))]
  refine vsum_congr N1 (fun ρ hρ => ?_)
  conv => rhs; rw [← vsum_shift N2 (vec ρ) (hvec ρ hρ)]
  refine vsum_congr N2 (fun γ hγ => ?_)
  rw [hB ρ hρ, cwOpen_eq ms _ _ _ _ _ (hP ρ hρ) (hC ρ γ hρ hγ),
    batch_eq hd haw ms _ _ _ _ _ hn (hP ρ hρ) (hC ρ γ hρ hγ)]

end Circuit
