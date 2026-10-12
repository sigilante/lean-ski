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

A quotient table's chunk matrices carry codewords randomized like the
chunks themselves (values on each chunk's domain plus `v_i r_i`, the last
cancelling).  Their shift is the combination, with each codeword's
coefficients (`ccoef`), of the base columns' data changes through the
values (`cΔ`, `cvals`) and of their random polynomials' shifts (`cR`,
`rcomb`, with `wsumR_rcomb` for the last chunk); at every chunk the
shifted codewords are the originals plus that chunk's `cwShift`
(`cw_entry`, `cw_rows`).

Scope.  `fri_hides` takes the base shift, the matrices' differences and
the codewords' shift as hypotheses; this file proves each for its kind of
matrix (`masks_shift_multi`, `chunkPolys_rel` with `vanish_of_open_rel`
and `chunks_shiftV`, `cws_rel`, `cw_rows`) and the count-keeping
dependent shift (`vsum_dshift`).  The instance for the composed PCS,
`pcsChunk` with every matrix's codewords and FRI's view, assembling these
through the tables' rows, is not written here.  Merkle salts and
Fiat–Shamir stay assumed.
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

theorem add_left_cancel_zero {a d : F} (h : a + d = a) : d = 0 := by
  have e : d = (a + d) - a := fid (e := v 1) (e' := (v 0 + v 1) - v 0) (by decide) [a, d]
  rw [e, h, sub_self']

theorem addE_left_cancel_zero {a d : EF} (h : a.add d = a) : d = EF.zero := by
  have e : d = (a.add d).sub a :=
    Q.eq_of_norm (p := Q.var 1) (q := ((Q.var 0).add (Q.var 1)).sub (Q.var 0)) (by decide) (env3 a d EF.zero)
  rw [e, h, EF.sub_self]

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
    ∃ (C : List F) (Ds : List (List F)), C.length = ts.length * n ∧ (∀ D ∈ Ds, Vanish S Z D ∧ D.length ≤ n + n) ∧
      ∀ rs : List F, rs.length = ts.length * n → PolyRel (mpolys T R n ts' (vadd rs C)) (mpolys T R n ts rs) Ds
  | [], [], _, _, _ => ⟨[], [], (Nat.zero_mul n).symm, ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => trivial⟩⟩
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h
  | t :: ts, t' :: ts', hl, h1, h2 => by
    obtain ⟨c, D, hc, hDl, hDS, hDZ, key⟩ := mask_shift_ood hT hR hTR hTS hZ hn t t' (h1 t List.mem_cons_self)
      (h2 t' List.mem_cons_self)
    obtain ⟨C, Ds, hC, hDs, hrel⟩ := masks_shift ts ts' (by simp only [List.length_cons] at hl; omega)
      (fun u hu => h1 u (List.mem_cons_of_mem _ hu)) (fun u hu => h2 u (List.mem_cons_of_mem _ hu))
    refine ⟨c ++ C, D :: Ds, ?_, fun D' hD' => ?_, fun rs hr => ?_⟩
    · rw [List.length_append, hc, hC, List.length_cons, Nat.succ_mul]; omega
    · rcases List.mem_cons.1 hD' with rfl | hD'
      · exact ⟨⟨hDS, hDZ⟩, hDl⟩
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
  | g :: gs, ps' :: pss', ps :: pss, Ds :: Dss => (PolyRel ps' ps Ds ∧ ∀ D ∈ Ds, Vanish g.S g.Z D ∧ D.length ≤ g.n + g.n) ∧
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
    rw [List.zipWith_cons_cons, List.zipWith_cons_cons, open_of_rel g.S g.Z ps' ps Ds hr (fun D hD => (hv D hD).1),
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

/-- A list of polynomials opened at `S` and `Z`. -/
def openPolys (S : List F) (Z : List EF) (ps : List (List F)) : List (List F × List EF) :=
  ps.map fun p => (S.map (fun s => fval s p), Z.map (fun z => fvalE z p))

theorem firstView_eq (S : List F) (Zc : List EF) (h : Nat) : ∀ (cs : List Chunk) (qs : List (List F)) (rs : List F),
    firstView S Zc h cs qs rs = openPolys S Zc (firstPolys h cs qs rs)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | ch :: cs, q :: qs, rs => by
    show (S.map (chunkAt ch.H ch.c q (rs.take h)), Zc.map (chunkAtE ch.H ch.c q (rs.take h))) ::
        firstView S Zc h cs qs (rs.drop h) =
      (S.map (fun s => fval s (chunkPoly ch.H ch.c q (rs.take h))),
        Zc.map (fun z => fvalE z (chunkPoly ch.H ch.c q (rs.take h)))) :: openPolys S Zc (firstPolys h cs qs (rs.drop h))
    rw [firstView_eq S Zc h cs qs (rs.drop h)]
    congr 2
    · exact List.map_congr_left (fun s _ => (fval_chunkPoly _ _ _ _ s).symm)
    · exact List.map_congr_left (fun z _ => (fvalE_chunkPoly _ _ _ _ z).symm)

/-- **A column's opened chunks are its chunk polynomials' openings**. -/
theorem chunksView_eq (S : List F) (Zc : List EF) (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F)
    (qs : List (List F)) (ql rs : List F) :
    chunksView S Zc h cs Hl cl qs ql rs = openPolys S Zc (chunkPolys h cs Hl cl qs ql rs) := by
  unfold chunksView chunkPolys openPolys
  rw [List.map_append, ← openPolys, ← firstView_eq]
  congr 3
  · exact List.map_congr_left (fun s _ => (fval_chunkPoly _ _ _ _ s).symm)
  · exact List.map_congr_left (fun z _ => (fvalE_chunkPoly _ _ _ _ z).symm)

/-- **Related polynomials that open alike differ by polynomials vanishing
    there**. -/
theorem vanish_of_open_rel (S : List F) (Z : List EF) : ∀ (ps' ps Ds : List (List F)), PolyRel ps' ps Ds →
    openPolys S Z ps' = openPolys S Z ps → ∀ D ∈ Ds, Vanish S Z D
  | [], [], [], _, _ => fun _ h => absurd h List.not_mem_nil
  | p' :: ps', p :: ps, D :: Ds, ⟨h, hr⟩, ho => by
    unfold openPolys at ho
    rw [List.map_cons, List.map_cons, List.cons.injEq] at ho
    obtain ⟨h0, ho⟩ := ho
    rw [Prod.mk.injEq] at h0
    intro D' hD'
    rcases List.mem_cons.1 hD' with rfl | hD'
    · refine ⟨fun s hs => ?_, fun z hz => ?_⟩
      · have e : fval s p' = fval s p := List.map_inj_left.1 h0.1 s hs
        have e2 := fval_of_fvalE h s
        rw [e] at e2
        exact (add_left_cancel_zero e2.symm)
      · have e : fvalE z p' = fvalE z p := List.map_inj_left.1 h0.2 z hz
        have e2 := h z
        rw [e] at e2
        exact (addE_left_cancel_zero e2.symm)
    · exact vanish_of_open_rel S Z ps' ps Ds hr ho D' hD'
  | [], _ :: _, _, h, _ => nomatch h
  | [], [], _ :: _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | _ :: _, _ :: _, [], h, _ => nomatch h

/-- **A shift that depends on the earlier digits keeps every count**: the
    first `a` digits shifted by `C`, the rest by `K` of the first. -/
theorem vsum_dshift (a b : Nat) (C : List F) (hC : C.length = a) (K : List F → List F)
    (hK : ∀ x : List F, x.length = a → (K x).length = b) (g : List F → Nat) :
    vsum (a + b) (fun ρ => g (vadd (ρ.take a) C ++ vadd (ρ.drop a) (K (ρ.take a)))) = vsum (a + b) g := by
  rw [vsum_append b, vsum_append b]
  have e1 : vsum a (fun x => vsum b (fun y => g (vadd ((x ++ y).take a) C ++ vadd ((x ++ y).drop a) (K ((x ++ y).take a))))) =
      vsum a (fun x => vsum b (fun y => g (vadd x C ++ vadd y (K x)))) :=
    vsum_congr a (fun x hx => vsum_congr b (fun y _ => by rw [List.take_left' hx, List.drop_left' hx]))
  rw [e1]
  have e2 : vsum a (fun x => vsum b (fun y => g (vadd x C ++ vadd y (K x)))) =
      vsum a (fun x => vsum b (fun y => g (vadd x C ++ y))) :=
    vsum_congr a (fun x hx => vsum_shift b (K x) (hK x hx) (fun y => g (vadd x C ++ y)))
  rw [e2]
  exact vsum_shift a C hC (fun x => vsum b (fun y => g (x ++ y)))

-- ---------------------------------------------------------------------------
-- Linear combinations of polynomials
-- ---------------------------------------------------------------------------

/-- `Σ_k coef (off + k) · D_k`. -/
def lc (coef : Nat → F) : Nat → List (List F) → List F
  | _, [] => []
  | off, D :: Ds => fcadd (fcscale (coef off) D) (lc coef (off + 1) Ds)

/-- The combination's value: `Σ_k coef (off + k) · D_k(z)`. -/
def lcv (coef : Nat → F) (z : EF) : Nat → List (List F) → EF
  | _, [] => EF.zero
  | off, D :: Ds => ((EF.ofF (coef off)).mul (fvalE z D)).add (lcv coef z (off + 1) Ds)

theorem fvalE_lc (coef : Nat → F) (z : EF) : ∀ (off : Nat) (Ds : List (List F)),
    fvalE z (lc coef off Ds) = lcv coef z off Ds
  | _, [] => rfl
  | off, D :: Ds => by
    show fvalE z (fcadd (fcscale _ D) _) = _
    rw [fvalE_fcadd, fvalE_fcscale, fvalE_lc coef z (off + 1) Ds]
    rfl

theorem gam_lc (α : EF) (w j : Nat) : ∀ (off : Nat) (Ds : List (List F)),
    gam α w j off Ds = lc (fun k => (lam α w k).getD j 0) off Ds
  | _, [] => rfl
  | off, D :: Ds => by
    show fcadd _ (gam α w j (off + 1) Ds) = fcadd _ (lc _ (off + 1) Ds)
    rw [gam_lc α w j (off + 1) Ds]

/-- Values that agree term by term combine alike. -/
theorem lcv_congr (coef : Nat → F) (z : EF) : ∀ (off : Nat) (As Bs : List (List F)), As.length = Bs.length →
    (∀ i (ha : i < As.length) (hb : i < Bs.length), fvalE z (As[i]'ha) = fvalE z (Bs[i]'hb)) →
    lcv coef z off As = lcv coef z off Bs
  | _, [], [], _, _ => rfl
  | off, A :: As, B :: Bs, hl, h => by
    show ((EF.ofF (coef off)).mul (fvalE z A)).add (lcv coef z (off + 1) As) =
      ((EF.ofF (coef off)).mul (fvalE z B)).add (lcv coef z (off + 1) Bs)
    have h0 : fvalE z A = fvalE z B := h 0 (Nat.succ_pos _) (Nat.succ_pos _)
    rw [h0, lcv_congr coef z (off + 1) As Bs
      (by simp only [List.length_cons] at hl; omega) (fun i ha hb => h (i + 1) (Nat.succ_lt_succ ha) (Nat.succ_lt_succ hb))]
  | _, [], _ :: _, hl, _ => nomatch hl
  | _, _ :: _, [], hl, _ => nomatch hl

theorem lc_step (c q V r W1 W2 : EF) :
    (c.mul (q.add (V.mul r))).add (W1.add (V.mul W2)) = ((c.mul q).add W1).add (V.mul ((c.mul r).add W2)) :=
  Q.eq_of_norm (p := ((Q.var 0).mul ((Q.var 1).add ((Q.var 2).mul (Q.var 3)))).add ((Q.var 4).add ((Q.var 2).mul (Q.var 5))))
    (q := (((Q.var 0).mul (Q.var 1)).add (Q.var 4)).add ((Q.var 2).mul (((Q.var 0).mul (Q.var 3)).add (Q.var 5))))
    (by decide) (env8 c q V r W1 W2 EF.zero EF.zero)

/-- **A combination of chunk polynomials of one domain is the chunk
    polynomial of the combinations**. -/
theorem lcv_chunkPoly (coef : Nat → F) (H : List F) (c : F) (z : EF) : ∀ (off : Nat) (qs rs : List (List F)),
    qs.length = rs.length →
    lcv coef z off (List.zipWith (chunkPoly H c) qs rs) = chunkAtE H c (lc coef off qs) (lc coef off rs) z
  | _, [], [], _ => by
    show EF.zero = (fvalE z []).add (((EF.ofF c).mul (fvalE z (fvan H))).mul (fvalE z []))
    show EF.zero = EF.zero.add (((EF.ofF c).mul (fvalE z (fvan H))).mul EF.zero)
    rw [EF.mul_zero, EF.add_zero]
  | off, q :: qs, r :: rs, hl => by
    rw [List.zipWith_cons_cons]
    show ((EF.ofF (coef off)).mul (fvalE z (chunkPoly H c q r))).add (lcv coef z (off + 1) (List.zipWith (chunkPoly H c) qs rs)) =
      chunkAtE H c (lc coef off (q :: qs)) (lc coef off (r :: rs)) z
    rw [lcv_chunkPoly coef H c z (off + 1) qs rs (by simp only [List.length_cons] at hl; omega), fvalE_chunkPoly]
    unfold chunkAtE
    rw [fvalE_lc, fvalE_lc, fvalE_lc, fvalE_lc]
    show ((EF.ofF (coef off)).mul ((fvalE z q).add (((EF.ofF c).mul (fvalE z (fvan H))).mul (fvalE z r)))).add
        ((lcv coef z (off + 1) qs).add (((EF.ofF c).mul (fvalE z (fvan H))).mul (lcv coef z (off + 1) rs))) =
      (((EF.ofF (coef off)).mul (fvalE z q)).add (lcv coef z (off + 1) qs)).add
        (((EF.ofF c).mul (fvalE z (fvan H))).mul (((EF.ofF (coef off)).mul (fvalE z r)).add (lcv coef z (off + 1) rs)))
    exact lc_step _ _ _ _ _ _
  | _, [], _ :: _, hl => nomatch hl
  | _, _ :: _, [], hl => nomatch hl

/-- `Σ_k coef (off + k) · v_k` over values. -/
def lcvF (coef : Nat → F) : Nat → List EF → EF
  | _, [] => EF.zero
  | off, x :: xs => ((EF.ofF (coef off)).mul x).add (lcvF coef (off + 1) xs)

theorem lcv_eq (coef : Nat → F) (z : EF) : ∀ (off : Nat) (Ds : List (List F)),
    lcv coef z off Ds = lcvF coef off (Ds.map (fvalE z))
  | _, [] => rfl
  | off, D :: Ds => by
    show _ = ((EF.ofF (coef off)).mul (fvalE z D)).add (lcvF coef (off + 1) (Ds.map (fvalE z)))
    rw [← lcv_eq coef z (off + 1) Ds]; rfl

theorem lcvF_zero {X : Type} (coef : Nat → F) : ∀ (off : Nat) (L : List X), lcvF coef off (L.map (fun _ => EF.zero)) = EF.zero
  | _, [] => rfl
  | off, _ :: L => by
    show ((EF.ofF (coef off)).mul EF.zero).add (lcvF coef (off + 1) (L.map _)) = EF.zero
    rw [lcvF_zero coef (off + 1) L, EF.mul_zero, EF.add_zero]

theorem lcvF_smul {X : Type} (coef : Nat → F) (a : EF) (g : X → EF) : ∀ (off : Nat) (L : List X),
    lcvF coef off (L.map (fun x => a.mul (g x))) = a.mul (lcvF coef off (L.map g))
  | _, [] => by show EF.zero = a.mul EF.zero; rw [EF.mul_zero]
  | off, x :: L => by
    show ((EF.ofF (coef off)).mul (a.mul (g x))).add (lcvF coef (off + 1) (L.map _)) =
      a.mul (((EF.ofF (coef off)).mul (g x)).add (lcvF coef (off + 1) (L.map g)))
    rw [lcvF_smul coef a g (off + 1) L, mulE_swap3, EF.mul_add]

theorem lcvF_step (c a g h' G H' : EF) :
    (c.mul ((a.mul g).add h')).add ((a.mul G).add H') = (a.mul ((c.mul g).add G)).add ((c.mul h').add H') :=
  Q.eq_of_norm (p := ((Q.var 0).mul (((Q.var 1).mul (Q.var 2)).add (Q.var 3))).add (((Q.var 1).mul (Q.var 4)).add (Q.var 5)))
    (q := ((Q.var 1).mul (((Q.var 0).mul (Q.var 2)).add (Q.var 4))).add (((Q.var 0).mul (Q.var 3)).add (Q.var 5)))
    (by decide) (env8 c a g h' G H' EF.zero EF.zero)

theorem lcvF_lin {X : Type} (coef : Nat → F) (a : EF) (g h' : X → EF) : ∀ (off : Nat) (L : List X),
    lcvF coef off (L.map (fun x => (a.mul (g x)).add (h' x))) =
      (a.mul (lcvF coef off (L.map g))).add (lcvF coef off (L.map h'))
  | _, [] => by show EF.zero = (a.mul EF.zero).add EF.zero; rw [EF.mul_zero, EF.add_zero]
  | off, x :: L => by
    show ((EF.ofF (coef off)).mul ((a.mul (g x)).add (h' x))).add (lcvF coef (off + 1) (L.map _)) =
      (a.mul (((EF.ofF (coef off)).mul (g x)).add (lcvF coef (off + 1) (L.map g)))).add
        (((EF.ofF (coef off)).mul (h' x)).add (lcvF coef (off + 1) (L.map h')))
    rw [lcvF_lin coef a g h' (off + 1) L]
    exact lcvF_step _ _ _ _ _ _

theorem lc_length (coef : Nat → F) {B : Nat} : ∀ (off : Nat) (Ds : List (List F)), (∀ D ∈ Ds, D.length ≤ B) →
    (lc coef off Ds).length ≤ B
  | _, [], _ => Nat.zero_le _
  | off, D :: Ds, h => by
    have h1 := fcadd_length (fcscale (coef off) D) (lc coef (off + 1) Ds)
    rw [fcscale_length] at h1
    have h2 := lc_length coef (off + 1) Ds (fun D' hD' => h D' (List.mem_cons_of_mem _ hD'))
    have h3 := h D List.mem_cons_self
    exact Nat.le_trans h1 (Nat.max_le.2 ⟨h3, h2⟩)

/-- **The combined shift of the chunks' random polynomials**: chunk by
    chunk, the combination of every column's slice, padded to `h`. -/
def rcomb (coef : Nat → F) (h : Nat) : List Chunk → List (List F) → List F
  | [], _ => []
  | _ :: cs, Ks => padTo h (lc coef 0 (Ks.map (·.take h))) ++ rcomb coef h cs (Ks.map (·.drop h))

theorem rcomb_length (coef : Nat → F) (h : Nat) : ∀ (cs : List Chunk) (Ks : List (List F)),
    (rcomb coef h cs Ks).length = cs.length * h
  | [], _ => (Nat.zero_mul h).symm
  | _ :: cs, Ks => by
    show (padTo h _ ++ rcomb coef h cs _).length = (cs.length + 1) * h
    rw [List.length_append, padTo_length (lc_length coef 0 _ (fun D hD => by
      obtain ⟨K, _, rfl⟩ := List.mem_map.1 hD; exact List.length_take_le _ _)), rcomb_length coef h cs, Nat.succ_mul,
      Nat.add_comm]

/-- **The last chunk's weighted sum commutes with the combination**:
    `Σ_i m_i (Σ_k coef_k K_k)_i = Σ_k coef_k Σ_i m_i (K_k)_i`. -/
theorem wsumR_rcomb (coef : Nat → F) (h : Nat) (z : EF) : ∀ (cs : List Chunk) (Ks : List (List F)),
    fvalE z (wsumR h cs (rcomb coef h cs Ks)) = lcvF coef 0 (Ks.map (fun K => fvalE z (wsumR h cs K)))
  | [], Ks => by
    show EF.zero = lcvF coef 0 (Ks.map (fun _ => EF.zero))
    exact (lcvF_zero coef 0 Ks).symm
  | ch :: cs, Ks => by
    have hp : (padTo h (lc coef 0 (Ks.map (·.take h)))).length = h := padTo_length (lc_length coef 0 _ (fun D hD => by
      obtain ⟨K, _, rfl⟩ := List.mem_map.1 hD; exact List.length_take_le _ _))
    show fvalE z (fcadd (fcscale ch.m ((padTo h _ ++ rcomb coef h cs _).take h))
        (wsumR h cs ((padTo h _ ++ rcomb coef h cs _).drop h))) = _
    rw [List.take_left' hp, List.drop_left' hp, fvalE_fcadd, fvalE_fcscale, wsumR_rcomb coef h z cs]
    unfold padTo
    rw [fvalE_pad, fvalE_lc, lcv_eq, List.map_map, List.map_map]
    have e : (fun K => fvalE z (wsumR h (ch :: cs) K)) =
        fun K => ((EF.ofF ch.m).mul ((fvalE z ∘ fun x => x.take h) K)).add ((fun K => fvalE z (wsumR h cs K)) (K.drop h)) := by
      funext K
      show fvalE z (fcadd (fcscale ch.m (K.take h)) (wsumR h cs (K.drop h))) = _
      rw [fvalE_fcadd, fvalE_fcscale]; rfl
    rw [e, lcvF_lin]
    rfl

-- ---------------------------------------------------------------------------
-- Relations entry by entry, and rows of columns
-- ---------------------------------------------------------------------------

/-- Related entry by entry. -/
def RelAt (ps' ps Ds : List (List F)) : Prop :=
  ps'.length = ps.length ∧ Ds.length = ps.length ∧
    ∀ i (h' : i < ps'.length) (h : i < ps.length) (hD : i < Ds.length) (z : EF),
      fvalE z (ps'[i]'h') = (fvalE z (ps[i]'h)).add (fvalE z (Ds[i]'hD))

theorem relAt_of_polyRel : ∀ {ps' ps Ds : List (List F)}, PolyRel ps' ps Ds → RelAt ps' ps Ds
  | [], [], [], _ => ⟨rfl, rfl, fun i h' => absurd h' (Nat.not_lt_zero _)⟩
  | p' :: ps', p :: ps, D :: Ds, ⟨h, hr⟩ => by
    obtain ⟨l1, l2, hi⟩ := relAt_of_polyRel hr
    refine ⟨by simp only [List.length_cons, l1], by simp only [List.length_cons, l2], fun i h1 h2 h3 z => ?_⟩
    cases i with
    | zero => exact h z
    | succ i => exact hi i _ _ _ z
  | [], _ :: _, _, h => nomatch h
  | [], [], _ :: _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | _ :: _, _ :: _, [], h => nomatch h

theorem polyRel_of_relAt : ∀ {ps' ps Ds : List (List F)}, RelAt ps' ps Ds → PolyRel ps' ps Ds
  | [], [], [], _ => trivial
  | p' :: ps', p :: ps, D :: Ds, ⟨l1, l2, hi⟩ =>
    ⟨fun z => hi 0 (Nat.succ_pos _) (Nat.succ_pos _) (Nat.succ_pos _) z,
      polyRel_of_relAt ⟨by simp only [List.length_cons] at l1; omega, by simp only [List.length_cons] at l2; omega,
        fun i h1 h2 h3 z => hi (i + 1) (Nat.succ_lt_succ h1) (Nat.succ_lt_succ h2) (Nat.succ_lt_succ h3) z⟩⟩
  | [], _ :: _, _, ⟨l1, _, _⟩ => nomatch l1
  | _ :: _, [], _, ⟨l1, _, _⟩ => nomatch l1
  | [], [], _ :: _, ⟨_, l2, _⟩ => nomatch l2
  | _ :: _, _ :: _, [], ⟨_, l2, _⟩ => nomatch l2

/-- **Rows of columns**: row `i` holds every column's `i`-th entry. -/
def rows (n : Nat) (cols : List (List (List F))) : List (List (List F)) :=
  (List.range n).map fun i => cols.map fun c => c.getD i []

theorem rows_length (n : Nat) (cols : List (List (List F))) : (rows n cols).length = n := by
  unfold rows; rw [List.length_map, List.length_range]

/-- **Columns related entry by entry give rows related entry by entry**. -/
theorem rows_rel (n : Nat) : ∀ (cs' cs Ds : List (List (List F))), cs'.length = cs.length → Ds.length = cs.length →
    (∀ k (h' : k < cs'.length) (h : k < cs.length) (hD : k < Ds.length),
      RelAt (cs'[k]'h') (cs[k]'h) (Ds[k]'hD) ∧ (cs[k]'h).length = n) →
    ∀ i (hi : i < n), RelAt ((rows n cs')[i]'(by rw [rows_length]; exact hi)) ((rows n cs)[i]'(by rw [rows_length]; exact hi))
      ((rows n Ds)[i]'(by rw [rows_length]; exact hi)) := by
  intro cs' cs Ds l1 l2 h i hi
  unfold rows
  simp only [List.getElem_map, List.getElem_range]
  refine ⟨by rw [List.length_map, List.length_map, l1], by rw [List.length_map, List.length_map, l2],
    fun k h1 h2 h3 z => ?_⟩
  rw [List.length_map] at h1 h2 h3
  simp only [List.getElem_map]
  obtain ⟨⟨m1, m2, hk⟩, hn⟩ := h k h1 h2 h3
  have hc : i < (cs[k]'h2).length := by rw [hn]; exact hi
  have hc' : i < (cs'[k]'h1).length := by rw [m1]; exact hc
  have hd : i < (Ds[k]'h3).length := by rw [m2]; exact hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc', Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd, Option.getD_some]
  exact hk i hc' hc hd z

/-- The `i`-th slice of `h` digits. -/
def sl (h i : Nat) (K : List F) : List F := (K.drop (i * h)).take h

theorem sl_succ (h i : Nat) (K : List F) : sl h (i + 1) K = sl h i (K.drop h) := by
  unfold sl; rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]

theorem firstPolys_length (h : Nat) : ∀ (cs : List Chunk) (qs : List (List F)) (rs : List F), qs.length = cs.length →
    (firstPolys h cs qs rs).length = cs.length
  | [], [], _, _ => rfl
  | _ :: cs, _ :: qs, rs, hl => by
    show (firstPolys h cs qs (rs.drop h)).length + 1 = cs.length + 1
    rw [firstPolys_length h cs qs (rs.drop h) (by simp only [List.length_cons] at hl; omega)]
  | [], _ :: _, _, hl => nomatch hl
  | _ :: _, [], _, hl => nomatch hl

theorem firstDiffs_length (h : Nat) : ∀ (cs : List Chunk) (qs qs' : List (List F)) (K : List F),
    qs.length = cs.length → qs'.length = cs.length → (firstDiffs h cs qs qs' K).length = cs.length
  | [], [], [], _, _, _ => rfl
  | _ :: cs, _ :: qs, _ :: qs', K, h1, h2 => by
    show (firstDiffs h cs qs qs' (K.drop h)).length + 1 = cs.length + 1
    rw [firstDiffs_length h cs qs qs' (K.drop h) (by simp only [List.length_cons] at h1; omega)
      (by simp only [List.length_cons] at h2; omega)]
  | [], _ :: _, _, _, h1, _ => nomatch h1
  | [], [], _ :: _, _, _, h2 => nomatch h2
  | _ :: _, [], _, _, h1, _ => nomatch h1
  | _ :: _, _ :: _, [], _, _, h2 => nomatch h2

theorem firstPolys_get (h : Nat) : ∀ (cs : List Chunk) (qs : List (List F)) (rs : List F) (hl : qs.length = cs.length)
    (i : Nat) (hi : i < cs.length),
    (firstPolys h cs qs rs)[i]'(by rw [firstPolys_length h cs qs rs hl]; exact hi) =
      chunkPoly (cs[i]'hi).H (cs[i]'hi).c (qs[i]'(by rw [hl]; exact hi)) (sl h i rs)
  | ch :: cs, q :: qs, rs, hl, 0, _ => by show chunkPoly ch.H ch.c q (rs.take h) = _; unfold sl; simp
  | ch :: cs, q :: qs, rs, hl, i + 1, hi => by
    rw [sl_succ]
    exact firstPolys_get h cs qs (rs.drop h) (by simp only [List.length_cons] at hl; omega) i
      (by simp only [List.length_cons] at hi; omega)
  | [], _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, hl, _, _ => nomatch hl

theorem firstDiffs_get (h : Nat) : ∀ (cs : List Chunk) (qs qs' : List (List F)) (K : List F) (h1 : qs.length = cs.length)
    (h2 : qs'.length = cs.length) (i : Nat) (hi : i < cs.length),
    (firstDiffs h cs qs qs' K)[i]'(by rw [firstDiffs_length h cs qs qs' K h1 h2]; exact hi) =
      chunkPoly (cs[i]'hi).H (cs[i]'hi).c (fcdiff (qs'[i]'(by rw [h2]; exact hi)) (qs[i]'(by rw [h1]; exact hi))) (sl h i K)
  | ch :: cs, q :: qs, q' :: qs', K, _, _, 0, _ => by
    show chunkPoly ch.H ch.c (fcdiff q' q) (K.take h) = _; unfold sl; simp
  | ch :: cs, q :: qs, q' :: qs', K, h1, h2, i + 1, hi => by
    rw [sl_succ]
    exact firstDiffs_get h cs qs qs' (K.drop h) (by simp only [List.length_cons] at h1; omega)
      (by simp only [List.length_cons] at h2; omega) i (by simp only [List.length_cons] at hi; omega)
  | [], _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h1, _, _, _ => nomatch h1
  | _ :: _, _ :: _, [], _, _, h2, _, _ => nomatch h2

theorem rcomb_sl (coef : Nat → F) (h : Nat) : ∀ (cs : List Chunk) (Ks : List (List F)) (i : Nat), i < cs.length →
    sl h i (rcomb coef h cs Ks) = padTo h (lc coef 0 (Ks.map (sl h i)))
  | ch :: cs, Ks, 0, _ => by
    have hp : (padTo h (lc coef 0 (Ks.map (·.take h)))).length = h := padTo_length (lc_length coef 0 _ (fun D hD => by
      obtain ⟨K, _, rfl⟩ := List.mem_map.1 hD; exact List.length_take_le _ _))
    show ((padTo h _ ++ rcomb coef h cs _).drop (0 * h)).take h = _
    rw [Nat.zero_mul, List.drop_zero, List.take_left' hp]
    congr 3
    funext K
    unfold sl; rw [Nat.zero_mul, List.drop_zero]
  | ch :: cs, Ks, i + 1, hi => by
    have hp : (padTo h (lc coef 0 (Ks.map (·.take h)))).length = h := padTo_length (lc_length coef 0 _ (fun D hD => by
      obtain ⟨K, _, rfl⟩ := List.mem_map.1 hD; exact List.length_take_le _ _))
    rw [sl_succ]
    show sl h i ((padTo h _ ++ rcomb coef h cs _).drop h) = _
    rw [List.drop_left' hp, rcomb_sl coef h cs (Ks.map (·.drop h)) i (by simp only [List.length_cons] at hi; omega),
      List.map_map]
    congr 3
    funext K
    exact (sl_succ h i K).symm
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)

-- ---------------------------------------------------------------------------
-- A quotient table's codewords
-- ---------------------------------------------------------------------------

/-- Codeword `j`'s coefficients: `-lam_k[j]` for the first four, zero for
    the rest. -/
def ccoef (α : EF) (w j : Nat) (k : Nat) : F := if j < 4 then -((lam α w k).getD j 0) else 0

theorem lcv_zero_coef (z : EF) : ∀ (off : Nat) (Ds : List (List F)), lcv (fun _ => (0 : F)) z off Ds = EF.zero
  | _, [] => rfl
  | off, D :: Ds => by
    show ((EF.ofF 0).mul (fvalE z D)).add (lcv _ z (off + 1) Ds) = EF.zero
    rw [lcv_zero_coef z (off + 1) Ds, show EF.ofF 0 = EF.zero from rfl, EF.zero_mul, EF.add_zero]

theorem lcv_neg (c : Nat → F) (z : EF) : ∀ (off : Nat) (Ds : List (List F)),
    lcv (fun k => -(c k)) z off Ds = (EF.ofF (-1)).mul (lcv c z off Ds)
  | _, [] => by show EF.zero = (EF.ofF (-1)).mul EF.zero; rw [EF.mul_zero]
  | off, D :: Ds => by
    show ((EF.ofF (-(c off))).mul (fvalE z D)).add (lcv _ z (off + 1) Ds) =
      (EF.ofF (-1)).mul (((EF.ofF (c off)).mul (fvalE z D)).add (lcv c z (off + 1) Ds))
    rw [lcv_neg c z (off + 1) Ds, ofF_neg', ofF_neg', show EF.ofF 1 = EF.one from rfl]
    exact Q.eq_of_norm (p := (((Q.var 0).neg).mul (Q.var 1)).add (((⟨k 1, k 0, k 0, k 0⟩ : Q).neg).mul (Q.var 2)))
      (q := ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg).mul (((Q.var 0).mul (Q.var 1)).add (Q.var 2))) (by decide)
      (env3 (EF.ofF (c off)) (fvalE z D) (lcv c z (off + 1) Ds))

/-- **A codeword's shift is the combination with its coefficients**. -/
theorem cwShift_get (α : EF) (w ncw : Nat) (Ds : List (List F)) (z : EF) (j : Nat) (hj : j < ncw) :
    fvalE z ((cwShift α w ncw Ds)[j]'(by unfold cwShift; rw [List.length_map, List.length_range]; exact hj)) =
      lcv (ccoef α w j) z 0 Ds := by
  unfold cwShift
  simp only [List.getElem_map, List.getElem_range]
  unfold ccoef
  by_cases h4 : j < 4
  · simp only [if_pos h4]
    rw [fvalE_fcscale, gam_lc, fvalE_lc, lcv_neg]
  · simp only [if_neg h4]
    rw [lcv_zero_coef]; rfl

/-- The codeword values' shift chunk by chunk: `Δ i` read on `H_i`. -/
def vsh : List Chunk → Nat → (Nat → List F) → List F
  | [], _, _ => []
  | ch :: cs, i, Δ => ch.H.map (fun x => fval x (Δ i)) ++ vsh cs (i + 1) Δ

/-- A codeword's whole values' shift, the last chunk's on `Hl`. -/
def cvals (cs : List Chunk) (Hl : List F) (Δ : Nat → List F) : List F := vsh cs 0 Δ ++ Hl.map (fun x => fval x (Δ cs.length))

theorem sl_vsh {h : Nat} : ∀ (cs : List Chunk) (off : Nat) (Δ : Nat → List F) (T : List F), (∀ ch ∈ cs, ch.H.length = h) →
    (∀ i (hi : i < cs.length), sl h i (vsh cs off Δ ++ T) = ((cs[i]'hi).H).map (fun x => fval x (Δ (off + i)))) ∧
      sl h cs.length (vsh cs off Δ ++ T) = T.take h
  | [], _, _, T, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), by
      show ((([] : List F) ++ T).drop (0 * h)).take h = T.take h
      rw [Nat.zero_mul, List.drop_zero, List.nil_append]⟩
  | ch :: cs, off, Δ, T, hH => by
    have hl : (ch.H.map (fun x => fval x (Δ off))).length = h := by rw [List.length_map]; exact hH ch List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := sl_vsh cs (off + 1) Δ T (fun c hc => hH c (List.mem_cons_of_mem _ hc))
    have e : vsh (ch :: cs) off Δ ++ T = ch.H.map (fun x => fval x (Δ off)) ++ (vsh cs (off + 1) Δ ++ T) := by
      show (ch.H.map (fun x => fval x (Δ off)) ++ vsh cs (off + 1) Δ) ++ T = _; rw [List.append_assoc]
    refine ⟨fun i hi => ?_, ?_⟩
    · cases i with
      | zero =>
        rw [e]; unfold sl; rw [Nat.zero_mul, List.drop_zero, List.take_left' hl]; rfl
      | succ i =>
        rw [e, sl_succ, List.drop_left' hl, ih1 i (by simp only [List.length_cons] at hi; omega),
          show off + 1 + i = off + (i + 1) by omega]
        rfl
    · rw [e, show (ch :: cs).length = cs.length + 1 from rfl, sl_succ, List.drop_left' hl, ih2]

theorem sl_vadd (h i : Nat) (a b : List F) : sl h i (vadd a b) = vadd (sl h i a) (sl h i b) := by
  unfold sl vadd; rw [List.drop_zipWith, List.take_zipWith]

/-- A map with each entry's index, from `off`. -/
def imap {β : Type} (f : Nat → β → List F) : Nat → List β → List (List F)
  | _, [] => []
  | i, x :: xs => f i x :: imap f (i + 1) xs

theorem imap_length {β : Type} (f : Nat → β → List F) : ∀ (off : Nat) (xs : List β), (imap f off xs).length = xs.length
  | _, [] => rfl
  | off, _ :: xs => by show (imap f (off + 1) xs).length + 1 = xs.length + 1; rw [imap_length f (off + 1) xs]

theorem imap_get {β : Type} (f : Nat → β → List F) : ∀ (off : Nat) (xs : List β) (i : Nat) (hi : i < xs.length),
    (imap f off xs)[i]'(by rw [imap_length]; exact hi) = f (off + i) (xs[i]'hi)
  | off, x :: xs, 0, _ => by show f off x = f (off + 0) x; rw [Nat.add_zero]
  | off, x :: xs, i + 1, hi => by
    rw [show off + (i + 1) = off + 1 + i by omega]
    exact imap_get f (off + 1) xs i (by simp only [List.length_cons] at hi; omega)
  | _, [], _, hi => absurd hi (Nat.not_lt_zero _)

/-- A codeword's chunk data: the interpolants of its values on each
    chunk's domain. -/
def cdata (h : Nat) (cs : List Chunk) (Hl vals : List F) : List (List F) × List F :=
  (imap (fun i (ch : Chunk) => cwPoly ch.H (sl h i vals)) 0 cs, cwPoly Hl (sl h cs.length vals))

theorem cdata_length (h : Nat) (cs : List Chunk) (Hl vals : List F) : (cdata h cs Hl vals).1.length = cs.length :=
  imap_length _ 0 cs

theorem sub_of_add (a b d : EF) (h : a = b.add d) : a.sub b = d := by
  rw [h]
  exact Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).sub (Q.var 0)) (q := Q.var 1) (by decide) (env3 b d EF.zero)

theorem chunkDiffs_length (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) (qs qs' : List (List F)) (ql ql' K : List F)
    (h1 : qs.length = cs.length) (h2 : qs'.length = cs.length) :
    (chunkDiffs h cs Hl cl qs qs' ql ql' K).length = cs.length + 1 := by
  unfold chunkDiffs; rw [List.length_append, firstDiffs_length h cs qs qs' K h1 h2]; rfl

/-- The `i`-th chunk's change, before or at the last. -/
theorem chunkDiffs_get (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) (qs qs' : List (List F)) (ql ql' K : List F)
    (h1 : qs.length = cs.length) (h2 : qs'.length = cs.length) (i : Nat) (hi : i < cs.length + 1) (z : EF) :
    fvalE z ((chunkDiffs h cs Hl cl qs qs' ql ql' K)[i]'(by rw [chunkDiffs_length h cs Hl cl qs qs' ql ql' K h1 h2]; exact hi)) =
      if hlt : i < cs.length then
        chunkAtE (cs[i]'hlt).H (cs[i]'hlt).c (fcdiff (qs'[i]'(by rw [h2]; exact hlt)) (qs[i]'(by rw [h1]; exact hlt)))
          (sl h i K) z
      else chunkAtE Hl cl (fcdiff ql' ql) (fcscale (-1) (wsumR h cs K)) z := by
  unfold chunkDiffs
  by_cases hlt : i < cs.length
  · rw [dif_pos hlt, List.getElem_append_left (by rw [firstDiffs_length h cs qs qs' K h1 h2]; exact hlt),
      firstDiffs_get h cs qs qs' K h1 h2 i hlt, fvalE_chunkPoly]
  · rw [dif_neg hlt, List.getElem_append_right (by rw [firstDiffs_length h cs qs qs' K h1 h2]; omega)]
    simp only [firstDiffs_length h cs qs qs' K h1 h2, List.getElem_singleton]
    rw [fvalE_chunkPoly]

section
variable {α : EF} {h : Nat} {cs : List Chunk} {Hl : List F} {cl : F} (w : Nat)
  (qs qs' : Nat → List (List F)) (ql ql' : Nat → List F) (K : Nat → List F)

/-- Chunk `i`'s data change in base column `k`. -/
def Qd (i k : Nat) : List F :=
  if i < cs.length then fcdiff ((qs' k).getD i []) ((qs k).getD i []) else fcdiff (ql' k) (ql k)

/-- Codeword `j`'s data shift at chunk `i`. -/
def cΔ (j i : Nat) : List F := lc (ccoef α w j) 0 ((List.range w).map (Qd (cs := cs) qs qs' ql ql' i))

/-- Codeword `j`'s random polynomials' shift. -/
def cR (j : Nat) : List F := rcomb (ccoef α w j) h cs ((List.range w).map K)

/-- Chunk `i`'s row of the base columns' changes. -/
def bRow (i : Nat) : List (List F) :=
  (List.range w).map fun k => (chunkDiffs h cs Hl cl (qs k) (qs' k) (ql k) (ql' k) (K k)).getD i []
end

theorem chunkAtE_congr (H : List F) (c : F) (q q' r r' : List F) (z : EF) (hq : fvalE z q = fvalE z q')
    (hr : fvalE z r = fvalE z r') : chunkAtE H c q r z = chunkAtE H c q' r' z := by
  unfold chunkAtE; rw [hq, hr]

theorem getD_eq_getElem' {L : List (List F)} {i : Nat} (hi : i < L.length) : L.getD i [] = L[i]'hi := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- **Codeword `j`'s chunk `i`, shifted, is the original plus the
    combination of the base columns' changes at chunk `i`**. -/
theorem cw_entry (α : EF) (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) (w j : Nat)
    (qs qs' : Nat → List (List F)) (ql ql' : Nat → List F) (K : Nat → List F)
    (hH : ∀ ch ∈ cs, ch.H.length = h ∧ ch.H.Nodup) (hHl : Hl.length = h) (hHn : Hl.Nodup)
    (hq : ∀ k, (qs k).length = cs.length ∧ (qs' k).length = cs.length ∧ (K k).length = cs.length * h)
    (hsz : ∀ k i, (Qd (cs := cs) qs qs' ql ql' i k).length ≤ h)
    (vals rr : List F) (hv : vals.length = (cs.length + 1) * h) (hr : rr.length = cs.length * h)
    (i : Nat) (hi : i < cs.length + 1) (z : EF) :
    let vals' := vadd vals (cvals cs Hl (cΔ (α := α) (cs := cs) w qs qs' ql ql' j))
    let rr' := vadd rr (cR (α := α) (h := h) (cs := cs) w K j)
    fvalE z ((chunkPolys h cs Hl cl (cdata h cs Hl vals').1 (cdata h cs Hl vals').2 rr')[i]'(by
        unfold chunkPolys; rw [List.length_append, firstPolys_length _ _ _ _ (cdata_length _ _ _ _)]; exact hi)) =
      (fvalE z ((chunkPolys h cs Hl cl (cdata h cs Hl vals).1 (cdata h cs Hl vals).2 rr)[i]'(by
        unfold chunkPolys; rw [List.length_append, firstPolys_length _ _ _ _ (cdata_length _ _ _ _)]; exact hi))).add
        (lcv (ccoef α w j) z 0 (bRow (h := h) (cs := cs) (Hl := Hl) (cl := cl) w qs qs' ql ql' K i)) := by
  intro vals' rr'
  have hKl : (cR (α := α) (h := h) (cs := cs) w K j).length = cs.length * h := rcomb_length _ _ _ _
  obtain ⟨l1, l2, hix⟩ := relAt_of_polyRel (chunkPolys_rel h cs Hl cl (cdata h cs Hl vals).1 (cdata h cs Hl vals').1
    (cdata h cs Hl vals).2 (cdata h cs Hl vals').2 rr (cR (α := α) (h := h) (cs := cs) w K j)
    (cdata_length _ _ _ _) (cdata_length _ _ _ _) hr hKl)
  have hlen : ∀ v r, (chunkPolys h cs Hl cl (cdata h cs Hl v).1 (cdata h cs Hl v).2 r).length = cs.length + 1 :=
    fun v r => by unfold chunkPolys; rw [List.length_append, firstPolys_length _ _ _ _ (cdata_length _ _ _ _)]; rfl
  rw [hix i (by rw [hlen]; exact hi) (by rw [hlen]; exact hi)
    (by rw [chunkDiffs_length _ _ _ _ _ _ _ _ _ (cdata_length _ _ _ _) (cdata_length _ _ _ _)]; exact hi) z]
  congr 1
  rw [chunkDiffs_get _ _ _ _ _ _ _ _ _ (cdata_length _ _ _ _) (cdata_length _ _ _ _) i hi z]
  have hHlen : ∀ ch ∈ cs, ch.H.length = h := fun ch hc => (hH ch hc).1
  have hΔl : ∀ i, (cΔ (α := α) (cs := cs) w qs qs' ql ql' j i).length ≤ h := fun i =>
    lc_length _ 0 _ (fun D hD => by obtain ⟨k, _, rfl⟩ := List.mem_map.1 hD; exact hsz k i)
  have hslv : ∀ i', i' < cs.length + 1 → (sl h i' vals).length = h := fun i' hi' => by
    unfold sl; rw [List.length_take, List.length_drop, hv]
    have : i' * h + h ≤ (cs.length + 1) * h := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right h hi'
    omega
  have hKs : ∀ D ∈ (List.range w).map K, D.length = cs.length * h := fun D hD => by
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hD; exact (hq k).2.2
  by_cases hlt : i < cs.length
  · rw [dif_pos hlt]
    obtain ⟨hHi, hHnd⟩ := hH _ (List.getElem_mem hlt)
    -- the data: the shifted codeword's chunk `i` is the original plus `cΔ j i`
    have hd' : (cdata h cs Hl vals').1[i]'(by rw [cdata_length]; exact hlt) =
        cwPoly (cs[i]'hlt).H (vadd (sl h i vals) ((cs[i]'hlt).H.map (fun x => fval x (cΔ (α := α) (cs := cs) w qs qs' ql ql' j i)))) := by
      unfold cdata
      rw [imap_get _ 0 cs i hlt, Nat.zero_add]
      show cwPoly _ (sl h i (vadd vals (cvals cs Hl _))) = _
      unfold cvals
      rw [sl_vadd h i vals]
      rw [(sl_vsh cs 0 (cΔ (α := α) (cs := cs) w qs qs' ql ql' j)
        (Hl.map (fun x => fval x (cΔ (α := α) (cs := cs) w qs qs' ql ql' j cs.length))) hHlen).1 i hlt, Nat.zero_add]
    have hd0 : (cdata h cs Hl vals).1[i]'(by rw [cdata_length]; exact hlt) = cwPoly (cs[i]'hlt).H (sl h i vals) := by
      unfold cdata; rw [imap_get _ 0 cs i hlt, Nat.zero_add]
    have hdat : fvalE z (fcdiff ((cdata h cs Hl vals').1[i]'(by rw [cdata_length]; exact hlt))
        ((cdata h cs Hl vals).1[i]'(by rw [cdata_length]; exact hlt))) =
        fvalE z (cΔ (α := α) (cs := cs) w qs qs' ql ql' j i) := by
      rw [fvalE_fcdiff, hd', hd0]
      exact sub_of_add _ _ _ (cw_rel hHnd (by rw [hslv i (by omega), hHi]) (by rw [hHi]; exact hΔl i) z)
    have hran : fvalE z (sl h i (cR (α := α) (h := h) (cs := cs) w K j)) =
        fvalE z (lc (ccoef α w j) 0 (((List.range w).map K).map (sl h i))) := by
      unfold cR; rw [rcomb_sl _ _ _ _ i hlt]; unfold padTo; rw [fvalE_pad]
    rw [chunkAtE_congr _ _ _ _ _ _ z hdat hran]
    unfold cΔ
    rw [← lcv_chunkPoly _ _ _ z 0 _ _ (by rw [List.length_map, List.length_map, List.length_map])]
    refine lcv_congr _ z 0 _ _ (by unfold bRow; rw [List.length_zipWith, List.length_map, List.length_map,
      List.length_map, List.length_map, Nat.min_self]) (fun k hk1 hk2 => ?_)
    have hkw : k < w := by unfold bRow at hk2; rw [List.length_map, List.length_range] at hk2; exact hk2
    unfold bRow
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    obtain ⟨h1, h2, _⟩ := hq k
    rw [getD_eq_getElem' (by rw [chunkDiffs_length _ _ _ _ _ _ _ _ _ h1 h2]; exact hi),
      chunkDiffs_get _ _ _ _ _ _ _ _ _ h1 h2 i hi z, dif_pos hlt, fvalE_chunkPoly]
    unfold Qd
    rw [if_pos hlt, getD_eq_getElem' (by rw [h2]; exact hlt), getD_eq_getElem' (by rw [h1]; exact hlt)]
  · rw [dif_neg hlt]
    have hie : i = cs.length := by omega
    subst hie
    have hTl : (Hl.map (fun x => fval x (cΔ (α := α) (cs := cs) w qs qs' ql ql' j cs.length))).length = h := by
      rw [List.length_map, hHl]
    have hd' : (cdata h cs Hl vals').2 =
        cwPoly Hl (vadd (sl h cs.length vals) (Hl.map (fun x => fval x (cΔ (α := α) (cs := cs) w qs qs' ql ql' j cs.length)))) := by
      show cwPoly Hl (sl h cs.length (vadd vals (cvals cs Hl _))) = _
      unfold cvals
      rw [sl_vadd h cs.length vals, (sl_vsh cs 0 (cΔ (α := α) (cs := cs) w qs qs' ql ql' j)
        (Hl.map (fun x => fval x (cΔ (α := α) (cs := cs) w qs qs' ql ql' j cs.length))) hHlen).2,
        List.take_of_length_le (by rw [hTl]; exact Nat.le_refl h)]
    have hdat : fvalE z (fcdiff (cdata h cs Hl vals').2 (cdata h cs Hl vals).2) =
        fvalE z (cΔ (α := α) (cs := cs) w qs qs' ql ql' j cs.length) := by
      rw [fvalE_fcdiff, hd']
      exact sub_of_add _ _ _ (cw_rel hHn (by rw [hslv cs.length (by omega), hHl]) (by rw [hHl]; exact hΔl _) z)
    have hran : fvalE z (fcscale (-1) (wsumR h cs (cR (α := α) (h := h) (cs := cs) w K j))) =
        fvalE z (lc (ccoef α w j) 0 (((List.range w).map K).map (fun K' => fcscale (-1) (wsumR h cs K')))) := by
      rw [fvalE_fcscale]
      unfold cR
      rw [wsumR_rcomb, fvalE_lc, lcv_eq, List.map_map, List.map_map, List.map_map]
      rw [show ((fvalE z ∘ fun K' => fcscale (-1) (wsumR h cs K')) ∘ K) =
          fun k => (EF.ofF (-1)).mul ((fun K' => fvalE z (wsumR h cs K')) (K k)) from
        funext fun k => by show fvalE z (fcscale (-1) (wsumR h cs (K k))) = _; rw [fvalE_fcscale]]
      rw [lcvF_smul]
      rfl
    rw [chunkAtE_congr _ _ _ _ _ _ z hdat hran]
    unfold cΔ
    rw [← lcv_chunkPoly _ _ _ z 0 _ _ (by rw [List.length_map, List.length_map, List.length_map])]
    refine lcv_congr _ z 0 _ _ (by unfold bRow; rw [List.length_zipWith, List.length_map, List.length_map,
      List.length_map, List.length_map, Nat.min_self]) (fun k hk1 hk2 => ?_)
    unfold bRow
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    obtain ⟨h1, h2, _⟩ := hq k
    rw [getD_eq_getElem' (by rw [chunkDiffs_length _ _ _ _ _ _ _ _ _ h1 h2]; exact hi),
      chunkDiffs_get _ _ _ _ _ _ _ _ _ h1 h2 cs.length hi z, dif_neg hlt, fvalE_chunkPoly]
    unfold Qd
    rw [if_neg hlt]

/-- A quotient table's codeword columns, each its chunks' polynomials. -/
def cwCols (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) (valsL rrL : List (List F)) : List (List (List F)) :=
  List.zipWith (fun v r => chunkPolys h cs Hl cl (cdata h cs Hl v).1 (cdata h cs Hl v).2 r) valsL rrL

/-- **A quotient table's codeword chunks absorb its columns' change**: at
    every chunk `i`, the codewords shifted by `cΔ` and `cR` are the
    originals plus that chunk's `cwShift`. -/
theorem cw_rows (α : EF) (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) (w ncw : Nat)
    (qs qs' : Nat → List (List F)) (ql ql' : Nat → List F) (K : Nat → List F)
    (hH : ∀ ch ∈ cs, ch.H.length = h ∧ ch.H.Nodup) (hHl : Hl.length = h) (hHn : Hl.Nodup)
    (hq : ∀ k, (qs k).length = cs.length ∧ (qs' k).length = cs.length ∧ (K k).length = cs.length * h)
    (hsz : ∀ k i, (Qd (cs := cs) qs qs' ql ql' i k).length ≤ h)
    (valsL rrL : List (List F)) (hvl : valsL.length = ncw) (hrl : rrL.length = ncw)
    (hv : ∀ v ∈ valsL, v.length = (cs.length + 1) * h) (hr : ∀ r ∈ rrL, r.length = cs.length * h)
    (i : Nat) (hi : i < cs.length + 1) :
    let valsL' := imap (fun j v => vadd v (cvals cs Hl (cΔ (α := α) (cs := cs) w qs qs' ql ql' j))) 0 valsL
    let rrL' := imap (fun j r => vadd r (cR (α := α) (h := h) (cs := cs) w K j)) 0 rrL
    PolyRel ((rows (cs.length + 1) (cwCols h cs Hl cl valsL' rrL'))[i]'(by rw [rows_length]; exact hi))
      ((rows (cs.length + 1) (cwCols h cs Hl cl valsL rrL))[i]'(by rw [rows_length]; exact hi))
      (cwShift α w ncw (bRow (h := h) (cs := cs) (Hl := Hl) (cl := cl) w qs qs' ql ql' K i)) := by
  intro valsL' rrL'
  have hlenC : ∀ v r, (chunkPolys h cs Hl cl (cdata h cs Hl v).1 (cdata h cs Hl v).2 r).length = cs.length + 1 :=
    fun v r => by unfold chunkPolys; rw [List.length_append, firstPolys_length _ _ _ _ (cdata_length _ _ _ _)]; rfl
  have hcl : (cwCols h cs Hl cl valsL rrL).length = ncw := by
    unfold cwCols; rw [List.length_zipWith, hvl, hrl, Nat.min_self]
  have hcl' : (cwCols h cs Hl cl valsL' rrL').length = ncw := by
    unfold cwCols; rw [List.length_zipWith, imap_length, imap_length, hvl, hrl, Nat.min_self]
  have hsh : (cwShift α w ncw (bRow (h := h) (cs := cs) (Hl := Hl) (cl := cl) w qs qs' ql ql' K i)).length = ncw := by
    unfold cwShift; rw [List.length_map, List.length_range]
  refine polyRel_of_relAt ⟨?_, ?_, fun j h1 h2 h3 z => ?_⟩
  · unfold rows; simp only [List.getElem_map, List.getElem_range, List.length_map, hcl, hcl']
  · unfold rows; simp only [List.getElem_map, List.getElem_range, List.length_map, hcl, hsh]
  · have hj : j < ncw := by rw [hsh] at h3; exact h3
    have hjv : j < valsL.length := by rw [hvl]; exact hj
    have hjr : j < rrL.length := by rw [hrl]; exact hj
    unfold rows
    simp only [List.getElem_map, List.getElem_range]
    rw [cwShift_get α w ncw _ z j hj]
    have e' : (cwCols h cs Hl cl valsL' rrL')[j]'(by rw [hcl']; exact hj) =
        chunkPolys h cs Hl cl (cdata h cs Hl (vadd (valsL[j]'hjv) (cvals cs Hl (cΔ (α := α) (cs := cs) w qs qs' ql ql' j)))).1
          (cdata h cs Hl (vadd (valsL[j]'hjv) (cvals cs Hl (cΔ (α := α) (cs := cs) w qs qs' ql ql' j)))).2
          (vadd (rrL[j]'hjr) (cR (α := α) (h := h) (cs := cs) w K j)) := by
      unfold cwCols; rw [List.getElem_zipWith, imap_get _ 0 valsL j hjv, imap_get _ 0 rrL j hjr, Nat.zero_add]
    have e0 : (cwCols h cs Hl cl valsL rrL)[j]'(by rw [hcl]; exact hj) =
        chunkPolys h cs Hl cl (cdata h cs Hl (valsL[j]'hjv)).1 (cdata h cs Hl (valsL[j]'hjv)).2 (rrL[j]'hjr) := by
      unfold cwCols; rw [List.getElem_zipWith]
    rw [getD_eq_getElem' (by rw [e', hlenC]; exact hi), getD_eq_getElem' (by rw [e0, hlenC]; exact hi)]
    simp only [e', e0]
    exact cw_entry α h cs Hl cl w j qs qs' ql ql' K hH hHl hHn hq hsz (valsL[j]'hjv) (rrL[j]'hjr)
      (hv _ (List.getElem_mem hjv)) (hr _ (List.getElem_mem hjr)) i hi z

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
