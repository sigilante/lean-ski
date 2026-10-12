import Ski.ZK.MaskQuot
import Ski.ZK.Solve4

/-!
# The quotient's chunks hide

Under hiding Plonky3 splits the quotient into chunks `q_i`, each on its own
domain `H_i`, and randomizes them (`get_quotient_ldes`, after ePrint
2024/1037): `q'_i = q_i + v_i r_i` for every chunk but the last, `v_i` the
vanishing polynomial of `H_i` and `r_i` uniform of `h` coefficients, and
`q'_l = q_l + v_l r_l` with `r_l = -Σ m_i r_i` (`m_i` its `mul_coeffs`), so
that the random terms cancel when the verifier recombines the chunks.  Each
quotient column (a base coordinate of the extension) is randomized alike
(`CSet`).  The proof opens every chunk at the query points and at `ζ`.

**What the verifier sees.**  At `ζ`, where the verifier recombines the
chunks, and at a query point off every domain, the opened chunks'
normalized sum `Σ m_i q'_i / v_i + q'_l / v_l`, which is the
recombination `Σ zp_i q'_i` over `cis_l ∏ v_j`, is `chunkJ` of the
chunks before randomization, whatever the random polynomials
(`chunks_recombineE`, `chunks_recombine`).  At a query point on a chunk's own
domain its mask vanishes and it opens bare; Plonky3's quotient domain and
its query coset share their shift, so this can happen (`Shows`).

**The chunks hide the rest.**  Two chunk data that agree there
(`Agree`) open with one distribution over the random polynomials
(`chunks_hide`): a shift of the random polynomials (`shiftK`) carries one
to the other.  Off its domain a chunk's shift is the difference over
`v_i`; on it the chunk's mask is free, and the first such chunk takes up
what the last chunk needs.  The shift reaches its values at the query
points and at `ζ` through `interpSZ`: an interpolant on the query points
plus four coefficients that reach any point of the extension at `ζ`
(`solve_spec`, `Ski/ZK/Solve4.lean`), when `1, ζ, ζ², ζ³` are independent
over `F` (`(mz ζ).det ≠ 0`): when `ζ` lies outside `F_{p²}`, which a
uniform `ζ` misses with probability `p^-2`, about `2^-62`
(`mz_gen_det` shows the condition can hold).  The canonical chunks, built from what the honest ones show
alone (`canonQs`, `canonQl`), show the same (`canon_shows`), so the
honest chunks open as they do (`chunks_sim`).

**The PCS.**  The view of every group's column openings, its quotient
values (`Ski/ZK/MaskQuot.lean`) and every quotient column's opened chunks
meets `PCSCloseN` with `ε = 0` (`pcsCloseN_chunks`), when what the honest
chunks show is a function of the challenges, the terminals and the column
openings (`RecOK`): on a domain the quotient there, off every domain the
quotient over `cis_l ∏ v_j`.  The transcript theorems then hold over that
view with no PCS term (`transcript_zkG_chunks` and the five circuits').

Scope.  The randomization polynomial opened with the quotient, the random
codeword columns appended to each chunk, FRI's layers, Merkle paths and
salts, and Fiat–Shamir stay assumed.  The points, `ζ` and the challenges
are fixed before the masks, in the public-coin model.  That the honest
chunks show the quotient, as `RecOK` states, is read from Plonky3's source
(the split of the quotient's evaluations, `get_zp_cis`), not proved.
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- Division by a vanishing polynomial
-- ---------------------------------------------------------------------------

theorem ofF_neg' (a : F) : EF.ofF (-a) = (EF.ofF a).neg :=
  have h : (0 : F) = -0 := (by decide : -(0 : F) = 0).symm
  EF.ext rfl h h h

/-- `fclin` at a point of the extension. -/
theorem fvalE_fclin (z : EF) (a : F) (p : List F) :
    fvalE z (fclin a p) = (z.sub (EF.ofF a)).mul (fvalE z p) := by
  unfold fclin
  rw [fvalE_fcadd, fvalE_cons, fvalE_fcscale, ofF_neg']
  exact Q.eq_of_norm (p := ((⟨k 0, k 0, k 0, k 0⟩ : Q).add ((Q.var 0).mul (Q.var 2))).add
      ((Q.var 1).neg.mul (Q.var 2)))
    (q := ((Q.var 0).sub (Q.var 1)).mul (Q.var 2)) (by decide) (env3 z (EF.ofF a) (fvalE z p))

theorem fvalE_fvan_cons (z : EF) (a : F) (L : List F) :
    fvalE z (fvan (a :: L)) = (z.sub (EF.ofF a)).mul (fvalE z (fvan L)) := fvalE_fclin z a (fvan L)

-- ---------------------------------------------------------------------------
-- Sums and padding of coefficient lists
-- ---------------------------------------------------------------------------

theorem fval_vadd (x : F) : ∀ (r k : List F), r.length = k.length →
    fval x (vadd r k) = fval x r + fval x k
  | [], [], _ => by show (0 : F) = 0 + 0; rw [add_zero']
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: r, b :: k, h => by
    show (a + b) + x * fval x (vadd r k) = (a + x * fval x r) + (b + x * fval x k)
    rw [fval_vadd x r k (by simp only [List.length_cons] at h; omega)]
    exact fid (e := (v 0 + v 1) + v 2 * (v 3 + v 4)) (e' := (v 0 + v 2 * v 3) + (v 1 + v 2 * v 4)) (by decide)
      [a, b, x, fval x r, fval x k]

theorem fvalE_vadd (z : EF) : ∀ (r k : List F), r.length = k.length →
    fvalE z (vadd r k) = (fvalE z r).add (fvalE z k)
  | [], [], _ => by show EF.zero = EF.zero.add EF.zero; rw [EF.add_zero]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: r, b :: k, h => by
    show (EF.ofF (a + b)).add (z.mul (fvalE z (vadd r k))) =
      ((EF.ofF a).add (z.mul (fvalE z r))).add ((EF.ofF b).add (z.mul (fvalE z k)))
    rw [fvalE_vadd z r k (by simp only [List.length_cons] at h; omega), EF.ofF_add]
    exact Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).add ((Q.var 2).mul ((Q.var 3).add (Q.var 4))))
      (q := ((Q.var 0).add ((Q.var 2).mul (Q.var 3))).add ((Q.var 1).add ((Q.var 2).mul (Q.var 4))))
      (by decide) (env8 (EF.ofF a) (EF.ofF b) z (fvalE z r) (fvalE z k) EF.zero EF.zero EF.zero)

theorem fval_pad (x : F) (m : Nat) : ∀ l : List F, fval x (l ++ List.replicate m 0) = fval x l
  | [] => by
    rw [List.nil_append, fval_fzero x _ (fun c hc => List.eq_of_mem_replicate hc)]; rfl
  | c :: l => by
    rw [List.cons_append]
    show c + x * fval x (l ++ List.replicate m 0) = c + x * fval x l
    rw [fval_pad x m l]

theorem fvalE_pad (z : EF) (m : Nat) : ∀ l : List F, fvalE z (l ++ List.replicate m 0) = fvalE z l
  | [] => by
    rw [List.nil_append, fvalE_fzero z _ (fun c hc => List.eq_of_mem_replicate hc)]; rfl
  | c :: l => by
    rw [List.cons_append, fvalE_cons, fvalE_cons, fvalE_pad z m l]

-- ---------------------------------------------------------------------------
-- One chunk
-- ---------------------------------------------------------------------------

/-- **A randomized chunk at a point**: Plonky3's `q + v_H · r`, the
    vanishing polynomial `v_H = c · ∏_{a ∈ H} (X - a)` of the chunk's
    domain `H`, and `r` the chunk's random polynomial. -/
def chunkAt (H : List F) (c : F) (q r : List F) (x : F) : F := fval x q + c * fval x (fvan H) * fval x r

/-- The same at a point of the extension. -/
def chunkAtE (H : List F) (c : F) (q r : List F) (z : EF) : EF :=
  (fvalE z q).add (((EF.ofF c).mul (fvalE z (fvan H))).mul (fvalE z r))

-- ---------------------------------------------------------------------------
-- Field facts
-- ---------------------------------------------------------------------------

theorem ofF_ne_zero {c : F} (hc : c ≠ 0) : EF.ofF c ≠ EF.zero := fun e => hc (congrArg EF.x0 e)

theorem fvalE_fvan_ne (z : EF) (hz : ∀ x : F, EF.ofF x ≠ z) : ∀ L : List F, fvalE z (fvan L) ≠ EF.zero
  | [] => by
    show (EF.ofF 1).add (z.mul EF.zero) ≠ EF.zero
    rw [EF.mul_zero, EF.add_zero]; exact EF.one_ne_zero
  | a :: L => by
    rw [fvalE_fvan_cons]
    intro e
    rcases EF.mul_eq_zero e with e | e
    · exact hz a ((sub_eq_zero_iff z (EF.ofF a)).1 e).symm
    · exact fvalE_fvan_ne z hz L e

theorem mul_ne_zero' {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := fun e =>
  (mul_eq_zero e).elim ha hb

theorem mulE_ne_zero {a b : EF} (ha : a ≠ EF.zero) (hb : b ≠ EF.zero) : a.mul b ≠ EF.zero := fun e =>
  (EF.mul_eq_zero e).elim ha hb

theorem shiftF (q q' V r k : F) (h : V * k = q - q') : q' + V * (r + k) = q + V * r := by
  have e : q' + V * (r + k) = (q' + V * r) + V * k :=
    fid (e := v 0 + v 1 * (v 2 + v 3)) (e' := (v 0 + v 1 * v 2) + v 1 * v 3) (by decide) [q', V, r, k]
  rw [e, h]
  exact fid (e := (v 0 + v 1 * v 2) + (v 3 - v 0)) (e' := v 3 + v 1 * v 2) (by decide) [q', V, r, q]

theorem shiftE (q q' V r k : EF) (h : V.mul k = q.sub q') : q'.add (V.mul (r.add k)) = q.add (V.mul r) := by
  have e : q'.add (V.mul (r.add k)) = (q'.add (V.mul r)).add (V.mul k) :=
    Q.eq_of_norm (p := (Q.var 0).add ((Q.var 1).mul ((Q.var 2).add (Q.var 3))))
      (q := ((Q.var 0).add ((Q.var 1).mul (Q.var 2))).add ((Q.var 1).mul (Q.var 3))) (by decide) (env4 q' V r k)
  rw [e, h]
  exact Q.eq_of_norm (p := ((Q.var 0).add ((Q.var 1).mul (Q.var 2))).add ((Q.var 3).sub (Q.var 0)))
    (q := (Q.var 3).add ((Q.var 1).mul (Q.var 2))) (by decide) (env4 q' V r q)

theorem mulE_swap3 (a b c : EF) : a.mul (b.mul c) = b.mul (a.mul c) :=
  Q.eq_of_norm (p := (Q.var 0).mul ((Q.var 1).mul (Q.var 2))) (q := (Q.var 1).mul ((Q.var 0).mul (Q.var 2)))
    (by decide) (env3 a b c)

theorem addE_sub_cancel (P e : EF) : P.add (e.sub P) = e :=
  Q.eq_of_norm (p := (Q.var 0).add ((Q.var 1).sub (Q.var 0))) (q := Q.var 1) (by decide) (env3 P e EF.zero)

theorem interp_last (P W e : EF) (hW : W ≠ EF.zero) : P.add (W.mul ((e.sub P).mul W.inv)) = e := by
  rw [mulE_swap3, EF.mul_inv hW, EF.mul_one, addE_sub_cancel]

theorem jsE_step (m a b i u w : EF) :
    (m.mul ((a.sub b).mul i)).add (u.sub w) = ((m.mul (a.mul i)).add u).sub ((m.mul (b.mul i)).add w) :=
  Q.eq_of_norm (p := ((Q.var 0).mul (((Q.var 1).sub (Q.var 2)).mul (Q.var 3))).add ((Q.var 4).sub (Q.var 5)))
    (q := (((Q.var 0).mul ((Q.var 1).mul (Q.var 3))).add (Q.var 4)).sub
      (((Q.var 0).mul ((Q.var 2).mul (Q.var 3))).add (Q.var 5))) (by decide) (env8 m a b i u w EF.zero EF.zero)

-- ---------------------------------------------------------------------------
-- The chunks of one quotient column
-- ---------------------------------------------------------------------------

/-- **A chunk other than the last**: its domain `H`, its vanishing
    polynomial's scale `c` (`v_H = c · ∏_{a ∈ H} (X - a)`), and its
    weight `m` in the last chunk's random polynomial (Plonky3's
    `mul_coeffs`, `cis_i / cis_last` from `get_zp_cis`). -/
structure Chunk where
  H : List F
  c : F
  m : F

/-- `Σ m_i r_i`, the chunks' random polynomials read `h` coefficients a
    chunk from `rs`. -/
def wsumR (h : Nat) : List Chunk → List F → List F
  | [], _ => []
  | ch :: cs, rs => fcadd (fcscale ch.m (rs.take h)) (wsumR h cs (rs.drop h))

/-- The opened values of the chunks other than the last, at the query
    points `S` and the out-of-domain points `Zc`. -/
def firstView (S : List F) (Zc : List EF) (h : Nat) : List Chunk → List (List F) → List F →
    List (List F × List EF)
  | ch :: cs, q :: qs, rs => (S.map (chunkAt ch.H ch.c q (rs.take h)), Zc.map (chunkAtE ch.H ch.c q (rs.take h))) ::
      firstView S Zc h cs qs (rs.drop h)
  | _, _, _ => []

/-- **The opened chunks**: those other than the last with their own
    random polynomials, and the last with `-Σ m_i r_i`, so that the
    random terms cancel in the recombination. -/
def chunksView (S : List F) (Zc : List EF) (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F)
    (qs : List (List F)) (ql : List F) (rs : List F) : List (List F × List EF) :=
  firstView S Zc h cs qs rs ++
    [(S.map (chunkAt Hl cl ql (fcscale (-1) (wsumR h cs rs))), Zc.map (chunkAtE Hl cl ql (fcscale (-1) (wsumR h cs rs))))]

/-- `Σ m_i q_i / v_i` over the chunks other than the last. -/
def jsumF (x : F) : List Chunk → List (List F) → F
  | ch :: cs, q :: qs => ch.m * (fval x q * finv (ch.c * fval x (fvan ch.H))) + jsumF x cs qs
  | _, _ => 0

def jsumE (z : EF) : List Chunk → List (List F) → EF
  | ch :: cs, q :: qs => ((EF.ofF ch.m).mul ((fvalE z q).mul ((EF.ofF ch.c).mul (fvalE z (fvan ch.H))).inv)).add
      (jsumE z cs qs)
  | _, _ => EF.zero

/-- **The chunks' recombination, normalized**: `q_l / v_l + Σ m_i q_i / v_i`.
    Plonky3's recombined quotient is `c_l ∏ v_j` times it at every point. -/
def chunkJ (x : F) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) : F :=
  fval x ql * finv (cl * fval x (fvan Hl)) + jsumF x cs qs

def chunkJE (z : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) : EF :=
  ((fvalE z ql).mul ((EF.ofF cl).mul (fvalE z (fvan Hl))).inv).add (jsumE z cs qs)

theorem wsumR_vadd (x : F) (h : Nat) : ∀ (cs : List Chunk) (rs K : List F), rs.length = cs.length * h →
    K.length = cs.length * h →
    fval x (wsumR h cs (vadd rs K)) = fval x (wsumR h cs rs) + fval x (wsumR h cs K)
  | [], _, _, _, _ => by show (0 : F) = 0 + 0; rw [add_zero']
  | ch :: cs, rs, K, hr, hK => by
    have hr' : (rs.drop h).length = cs.length * h := by
      rw [List.length_drop, hr, List.length_cons, Nat.succ_mul]; omega
    have hK' : (K.drop h).length = cs.length * h := by
      rw [List.length_drop, hK, List.length_cons, Nat.succ_mul]; omega
    have ht : (rs.take h).length = (K.take h).length := by
      rw [List.length_take, List.length_take, hr, hK]
    show fval x (fcadd (fcscale ch.m ((vadd rs K).take h)) (wsumR h cs ((vadd rs K).drop h))) =
      fval x (fcadd (fcscale ch.m (rs.take h)) (wsumR h cs (rs.drop h))) +
        fval x (fcadd (fcscale ch.m (K.take h)) (wsumR h cs (K.drop h)))
    unfold vadd
    rw [List.take_zipWith, List.drop_zipWith]
    rw [fval_fcadd, fval_fcadd, fval_fcadd, fval_fcscale, fval_fcscale, fval_fcscale,
      show List.zipWith (· + ·) (rs.take h) (K.take h) = vadd (rs.take h) (K.take h) from rfl,
      show List.zipWith (· + ·) (rs.drop h) (K.drop h) = vadd (rs.drop h) (K.drop h) from rfl,
      fval_vadd x _ _ ht, wsumR_vadd x h cs _ _ hr' hK']
    exact fid (e := v 0 * (v 1 + v 2) + (v 3 + v 4)) (e' := (v 0 * v 1 + v 3) + (v 0 * v 2 + v 4)) (by decide)
      [ch.m, fval x (rs.take h), fval x (K.take h), fval x (wsumR h cs (rs.drop h)), fval x (wsumR h cs (K.drop h))]

theorem addE5 (m a b c d : EF) :
    ((EF.ofF m.x0).mul (a.add b)).add (c.add d) = (((EF.ofF m.x0).mul a).add c).add (((EF.ofF m.x0).mul b).add d) :=
  Q.eq_of_norm (p := ((Q.var 0).mul ((Q.var 1).add (Q.var 2))).add ((Q.var 3).add (Q.var 4)))
    (q := (((Q.var 0).mul (Q.var 1)).add (Q.var 3)).add (((Q.var 0).mul (Q.var 2)).add (Q.var 4))) (by decide)
    (env8 (EF.ofF m.x0) a b c d EF.zero EF.zero EF.zero)

theorem wsumR_vaddE (z : EF) (h : Nat) : ∀ (cs : List Chunk) (rs K : List F), rs.length = cs.length * h →
    K.length = cs.length * h →
    fvalE z (wsumR h cs (vadd rs K)) = (fvalE z (wsumR h cs rs)).add (fvalE z (wsumR h cs K))
  | [], _, _, _, _ => by show EF.zero = EF.zero.add EF.zero; rw [EF.add_zero]
  | ch :: cs, rs, K, hr, hK => by
    have hr' : (rs.drop h).length = cs.length * h := by
      rw [List.length_drop, hr, List.length_cons, Nat.succ_mul]; omega
    have hK' : (K.drop h).length = cs.length * h := by
      rw [List.length_drop, hK, List.length_cons, Nat.succ_mul]; omega
    have ht : (rs.take h).length = (K.take h).length := by
      rw [List.length_take, List.length_take, hr, hK]
    show fvalE z (fcadd (fcscale ch.m ((vadd rs K).take h)) (wsumR h cs ((vadd rs K).drop h))) =
      (fvalE z (fcadd (fcscale ch.m (rs.take h)) (wsumR h cs (rs.drop h)))).add
        (fvalE z (fcadd (fcscale ch.m (K.take h)) (wsumR h cs (K.drop h))))
    unfold vadd
    rw [List.take_zipWith, List.drop_zipWith]
    rw [fvalE_fcadd, fvalE_fcadd, fvalE_fcadd, fvalE_fcscale, fvalE_fcscale, fvalE_fcscale,
      show List.zipWith (· + ·) (rs.take h) (K.take h) = vadd (rs.take h) (K.take h) from rfl,
      show List.zipWith (· + ·) (rs.drop h) (K.drop h) = vadd (rs.drop h) (K.drop h) from rfl,
      fvalE_vadd z _ _ ht, wsumR_vaddE z h cs _ _ hr' hK']
    exact addE5 ⟨ch.m, 0, 0, 0⟩ _ _ _ _

theorem lastF (ql ql' V W Wk : F) (h : V * Wk = ql' - ql) : ql' + V * (-1 * (W + Wk)) = ql + V * (-1 * W) := by
  have e : ql' + V * (-1 * (W + Wk)) = (ql' - V * Wk) + V * (-1 * W) :=
    fid (e := v 0 + v 1 * (k (-1) * (v 2 + v 3))) (e' := (v 0 - v 1 * v 3) + v 1 * (k (-1) * v 2)) (by decide)
      [ql', V, W, Wk]
  rw [e, h]
  exact congrArg (· + V * (-1 * W)) (fid (e := v 0 - (v 0 - v 1)) (e' := v 1) (by decide) [ql', ql])

theorem lastE (ql ql' V W Wk : EF) (h : V.mul Wk = ql'.sub ql) :
    ql'.add (V.mul ((EF.ofF (-1)).mul (W.add Wk))) = ql.add (V.mul ((EF.ofF (-1)).mul W)) := by
  rw [ofF_neg', show EF.ofF 1 = EF.one from rfl]
  have e : ql'.add (V.mul ((EF.one.neg).mul (W.add Wk))) = (ql'.sub (V.mul Wk)).add (V.mul ((EF.one.neg).mul W)) :=
    Q.eq_of_norm (p := (Q.var 0).add ((Q.var 1).mul ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul ((Q.var 2).add (Q.var 3)))))
      (q := ((Q.var 0).sub ((Q.var 1).mul (Q.var 3))).add ((Q.var 1).mul ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 2))))
      (by decide) (env4 ql' V W Wk)
  rw [e, h]
  exact congrArg (·.add (V.mul ((EF.one.neg).mul W)))
    (Q.eq_of_norm (p := (Q.var 0).sub ((Q.var 0).sub (Q.var 1))) (q := Q.var 1) (by decide) (env3 ql' ql EF.zero))

theorem jdiffF {ql ql' V fi a b Wk : F} (hV : V * fi = 1) (hJ : ql * fi + a = ql' * fi + b) (hW : Wk = a - b) :
    V * Wk = ql' - ql := by
  have e1 : a - b = (ql * fi + a) - (ql * fi + b) :=
    fid (e := v 0 - v 1) (e' := (v 2 * v 3 + v 0) - (v 2 * v 3 + v 1)) (by decide) [a, b, ql, fi]
  rw [hJ] at e1
  have e2 : (ql' * fi + b) - (ql * fi + b) = (ql' - ql) * fi :=
    fid (e := (v 0 * v 1 + v 2) - (v 3 * v 1 + v 2)) (e' := (v 0 - v 3) * v 1) (by decide) [ql', fi, b, ql]
  rw [hW, e1, e2, ← mul_assoc', mul_comm' V, mul_assoc', hV, mul_one']

theorem jdiffE {ql ql' V fi a b Wk : EF} (hV : V.mul fi = EF.one) (hJ : (ql.mul fi).add a = (ql'.mul fi).add b)
    (hW : Wk = a.sub b) : V.mul Wk = ql'.sub ql := by
  have e1 : a.sub b = ((ql.mul fi).add a).sub ((ql.mul fi).add b) :=
    Q.eq_of_norm (p := (Q.var 0).sub (Q.var 1))
      (q := (((Q.var 2).mul (Q.var 3)).add (Q.var 0)).sub (((Q.var 2).mul (Q.var 3)).add (Q.var 1))) (by decide)
      (env4 a b ql fi)
  rw [hJ] at e1
  have e2 : ((ql'.mul fi).add b).sub ((ql.mul fi).add b) = (ql'.sub ql).mul fi :=
    Q.eq_of_norm (p := (((Q.var 0).mul (Q.var 1)).add (Q.var 2)).sub (((Q.var 3).mul (Q.var 1)).add (Q.var 2)))
      (q := ((Q.var 0).sub (Q.var 3)).mul (Q.var 1)) (by decide) (env4 ql' fi b ql)
  rw [hW, e1, e2, ← EF.mul_assoc, EF.mul_comm V, EF.mul_assoc, hV, EF.mul_one]

-- ---------------------------------------------------------------------------
-- A polynomial over `F` through the query points and `ζ`
-- ---------------------------------------------------------------------------

/-- The distinct points of a list. -/
def dedupF : List F → List F
  | [] => []
  | x :: r => if x ∈ dedupF r then dedupF r else x :: dedupF r

theorem mem_dedupF {x : F} : ∀ {l : List F}, x ∈ dedupF l ↔ x ∈ l
  | [] => Iff.rfl
  | y :: r => by
    unfold dedupF
    by_cases hy : y ∈ dedupF r
    · rw [if_pos hy, mem_dedupF]
      exact ⟨List.mem_cons_of_mem _, fun h => (List.mem_cons.1 h).elim (fun e => e ▸ mem_dedupF.1 hy) id⟩
    · rw [if_neg hy, List.mem_cons, List.mem_cons, mem_dedupF]

theorem nodup_dedupF : ∀ l : List F, (dedupF l).Nodup
  | [] => List.nodup_nil
  | y :: r => by
    unfold dedupF
    by_cases hy : y ∈ dedupF r
    · rw [if_pos hy]; exact nodup_dedupF r
    · rw [if_neg hy]; exact List.nodup_cons.2 ⟨hy, nodup_dedupF r⟩

theorem length_dedupF : ∀ l : List F, (dedupF l).length ≤ l.length
  | [] => Nat.le_refl 0
  | y :: r => by
    unfold dedupF
    have := length_dedupF r
    split <;> simp only [List.length_cons] <;> omega

/-- **A polynomial over `F` with given values on `S` and at `ζ`**: the
    interpolant on `S`, plus `fvan S` times four coefficients that reach
    the rest at `ζ` (`solve_spec`). -/
def interpSZ (S : List F) (T : F → F) (ζ : EF) (e : EF) : List F :=
  let P1 := finterp ((dedupF S).map (fun x => (x, T x)))
  let W := fvan (dedupF S)
  let d := (e.sub (fvalE ζ P1)).mul (fvalE ζ W).inv
  fcadd P1 (fmul W ((mz ζ).solve d.x0 d.x1 d.x2 d.x3))

theorem interpSZ_spec (S : List F) (T : F → F) (ζ : EF) (e : EF) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hd : (mz ζ).det ≠ 0) :
    (interpSZ S T ζ e).length ≤ S.length + 4 ∧ (∀ x ∈ S, fval x (interpSZ S T ζ e) = T x) ∧
      fvalE ζ (interpSZ S T ζ e) = e := by
  have hnd : (((dedupF S).map (fun x => (x, T x))).map Prod.fst).Nodup := by
    rw [List.map_map]; exact (List.map_id' (dedupF S)).symm ▸ nodup_dedupF S
  have hW : fvalE ζ (fvan (dedupF S)) ≠ EF.zero := fvalE_fvan_ne ζ hζ _
  refine ⟨?_, fun x hx => ?_, ?_⟩
  · unfold interpSZ
    simp only
    have h6 : ∀ a b c d : F, (fmul (fvan (dedupF S)) ((mz ζ).solve a b c d)).length ≤ (dedupF S).length + 4 :=
      fun a b c d => by
        have := fmul_length (fvan (dedupF S)) ((mz ζ).solve a b c d) (by simp [M4.solve])
        have h4 := fvan_length (dedupF S)
        rw [solve_length] at this; omega
    refine Nat.le_trans (fcadd_length _ _) (Nat.max_le.2 ⟨?_, ?_⟩)
    · have h2 := finterp_length ((dedupF S).map (fun x => (x, T x)))
      have h5 := length_dedupF S
      rw [List.length_map] at h2; omega
    · have h5 := length_dedupF S
      exact Nat.le_trans (h6 _ _ _ _) (by omega)
  · have hx' : x ∈ dedupF S := mem_dedupF.2 hx
    have hmem : (x, T x) ∈ (dedupF S).map (fun x => (x, T x)) := List.mem_map.2 ⟨x, hx', rfl⟩
    unfold interpSZ
    simp only
    rw [fval_fcadd, fval_fmul, fvan_root x _ hx', zero_mul', add_zero', finterp_eval _ hnd _ hmem]
  · unfold interpSZ
    simp only
    rw [fvalE_fcadd, fvalE_fmul, solve_spec ζ hd]
    exact interp_last _ _ _ hW

-- ---------------------------------------------------------------------------
-- The shift of the chunks' random polynomials
-- ---------------------------------------------------------------------------

/-- `x` lies in some chunk's domain. -/
def inSome (x : F) (cs : List Chunk) : Bool := cs.any (fun ch => decide (x ∈ ch.H))

/-- `l` padded with zeros to `h` coefficients. -/
def padTo (h : Nat) (l : List F) : List F := l ++ List.replicate (h - l.length) 0

theorem padTo_length {h : Nat} {l : List F} (hl : l.length ≤ h) : (padTo h l).length = h := by
  unfold padTo; rw [List.length_append, List.length_replicate]; omega

/-- **One chunk's shift at a query point**: off the chunk's domain, the
    difference of the two chunks over the vanishing polynomial; on it,
    the first chunk there takes up what the last chunk needs, `L - A`
    over its weight, and later ones nothing. -/
def tgtF (A L : F → F) (seen : F → Bool) (ch : Chunk) (q q' : List F) (x : F) : F :=
  if x ∈ ch.H then (if seen x then 0 else (L x - A x) * finv ch.m)
  else (fval x q - fval x q') * finv (ch.c * fval x (fvan ch.H))

/-- The same at `ζ`, off every domain. -/
def tgtE (ζ : EF) (ch : Chunk) (q q' : List F) : EF :=
  ((fvalE ζ q).sub (fvalE ζ q')).mul ((EF.ofF ch.c).mul (fvalE ζ (fvan ch.H))).inv

/-- **The shift**: each chunk's interpolant through its targets
    (`interpSZ`), padded to `h` coefficients. -/
def shiftK (S : List F) (ζ : EF) (h : Nat) (A L : F → F) : (F → Bool) → List Chunk → List (List F) →
    List (List F) → List F
  | seen, ch :: cs, q :: qs, q' :: qs' => padTo h (interpSZ S (tgtF A L seen ch q q') ζ (tgtE ζ ch q q')) ++
      shiftK S ζ h A L (fun x => seen x || decide (x ∈ ch.H)) cs qs qs'
  | _, _, _, _ => []

/-- The chunks other than the last agree on their own domains. -/
def AgreeH (x : F) : List Chunk → List (List F) → List (List F) → Prop
  | ch :: cs, q :: qs, q' :: qs' => (x ∈ ch.H → fval x q = fval x q') ∧ AgreeH x cs qs qs'
  | _, _, _ => True

theorem fvan_zero_of_mem {x : F} {H : List F} (c : F) (hx : x ∈ H) : c * fval x (fvan H) = 0 := by
  rw [fvan_root x H hx, mul_zero']

theorem mul_swap3f (m c i : F) : m * (c * i) = (m * i) * c :=
  fid (e := v 0 * (v 1 * v 2)) (e' := (v 0 * v 2) * v 1) (by decide) [m, c, i]

theorem head_on_f (m q q' c a b : F) (hm : m ≠ 0) :
    m * (c * finv m) + (a - b + 0) = (m * (q * 0) + a - (m * (q' * 0) + b)) + c := by
  rw [mul_swap3f, mul_finv hm, one_mul']
  exact fid (e := v 0 + (v 1 - v 2 + k 0)) (e' := (v 3 * (v 4 * k 0) + v 1 - (v 3 * (v 5 * k 0) + v 2)) + v 0)
    (by decide) [c, a, b, m, q, q']

theorem head_on_t (m q q' a b : F) :
    m * 0 + (a - b + 0) = (m * (q * 0) + a - (m * (q' * 0) + b)) + 0 :=
  fid (e := v 0 * k 0 + (v 1 - v 2 + k 0)) (e' := (v 0 * (v 3 * k 0) + v 1 - (v 0 * (v 4 * k 0) + v 2)) + k 0)
    (by decide) [m, a, b, q, q']

theorem head_off (m q q' fi a b B : F) :
    m * ((q - q') * fi) + (a - b + B) = (m * (q * fi) + a - (m * (q' * fi) + b)) + B :=
  fid (e := v 0 * ((v 1 - v 2) * v 3) + (v 4 - v 5 + v 6))
    (e' := (v 0 * (v 1 * v 3) + v 4 - (v 0 * (v 2 * v 3) + v 5)) + v 6) (by decide) [m, q, q', fi, a, b, B]

/-- **The chunks' shift**: under it the chunks `qs'` open as `qs` at every
    query point and at `ζ`, and the weighted sum of the shift is the
    difference of the normalized sums, plus `L - A` where some chunk's
    domain holds the point and no earlier one took it up. -/
theorem shiftK_spec {S : List F} {ζ : EF} {h : Nat} (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hd : (mz ζ).det ≠ 0)
    (hn : S.length + 4 ≤ h) (A L : F → F) :
    ∀ (seen : F → Bool) (cs : List Chunk) (qs qs' : List (List F)), (∀ ch ∈ cs, ch.c ≠ 0 ∧ ch.m ≠ 0) →
      qs.length = cs.length → qs'.length = cs.length → (∀ x ∈ S, AgreeH x cs qs qs') →
      (shiftK S ζ h A L seen cs qs qs').length = cs.length * h ∧
      (∀ rs : List F, rs.length = cs.length * h →
        firstView S [ζ] h cs qs' (vadd rs (shiftK S ζ h A L seen cs qs qs')) = firstView S [ζ] h cs qs rs) ∧
      (∀ x ∈ S, fval x (wsumR h cs (shiftK S ζ h A L seen cs qs qs')) =
        (jsumF x cs qs - jsumF x cs qs') + (if (!seen x && inSome x cs) then L x - A x else 0)) ∧
      fvalE ζ (wsumR h cs (shiftK S ζ h A L seen cs qs qs')) = (jsumE ζ cs qs).sub (jsumE ζ cs qs')
  | _, [], [], [], _, _, _, _ => ⟨(Nat.zero_mul h).symm, fun _ _ => rfl,
      fun x _ => by
        rw [show inSome x [] = false from rfl, Bool.and_false, if_neg Bool.false_ne_true]
        show (0 : F) = (0 - 0) + 0; rw [sub_self', add_zero'],
      (EF.sub_self EF.zero).symm⟩
  | _, [], _ :: _, _, _, h1, _, _ => nomatch h1
  | _, [], _, _ :: _, _, _, h2, _ => nomatch h2
  | _, _ :: _, [], _, _, h1, _, _ => nomatch h1
  | _, _ :: _, _, [], _, _, h2, _ => nomatch h2
  | seen, ch :: cs, q :: qs, q' :: qs', hok, h1, h2, hag => by
    obtain ⟨hc, hm⟩ := hok ch List.mem_cons_self
    obtain ⟨hl, hS, hZ⟩ := interpSZ_spec S (tgtF A L seen ch q q') ζ (tgtE ζ ch q q') hζ hd
    let kk := padTo h (interpSZ S (tgtF A L seen ch q q') ζ (tgtE ζ ch q q'))
    have hkl : kk.length = h := padTo_length (by omega)
    have hkS : ∀ x ∈ S, fval x kk = tgtF A L seen ch q q' x := fun x hx => by
      show fval x (_ ++ _) = _; rw [fval_pad, hS x hx]
    have hkZ : fvalE ζ kk = tgtE ζ ch q q' := by show fvalE ζ (_ ++ _) = _; rw [fvalE_pad, hZ]
    let seen' : F → Bool := fun x => seen x || decide (x ∈ ch.H)
    obtain ⟨hKl, hKv, hKS, hKZ⟩ := shiftK_spec hζ hd hn A L seen' cs qs qs'
      (fun c hc' => hok c (List.mem_cons_of_mem _ hc')) (by simp only [List.length_cons] at h1; omega)
      (by simp only [List.length_cons] at h2; omega) (fun x hx => (hag x hx).2)
    have hK : shiftK S ζ h A L seen (ch :: cs) (q :: qs) (q' :: qs') = kk ++ shiftK S ζ h A L seen' cs qs qs' := rfl
    have hVZ : (EF.ofF ch.c).mul (fvalE ζ (fvan ch.H)) ≠ EF.zero :=
      mulE_ne_zero (ofF_ne_zero hc) (fvalE_fvan_ne ζ hζ ch.H)
    -- the chunk's own equation
    have hown : ∀ x ∈ S, ch.c * fval x (fvan ch.H) * fval x kk = fval x q - fval x q' := fun x hx => by
      rw [hkS x hx]
      unfold tgtF
      by_cases hxH : x ∈ ch.H
      · rw [fvan_zero_of_mem ch.c hxH, zero_mul', (hag x hx).1 hxH, sub_self']
      · rw [if_neg hxH]
        have hV : ch.c * fval x (fvan ch.H) ≠ 0 := mul_ne_zero' hc (fvan_ne x ch.H hxH)
        rw [mul_comm' (fval x q - fval x q'), ← mul_assoc', mul_finv hV, one_mul']
    have hownE : ((EF.ofF ch.c).mul (fvalE ζ (fvan ch.H))).mul (fvalE ζ kk) = (fvalE ζ q).sub (fvalE ζ q') := by
      rw [hkZ]; unfold tgtE; rw [EF.mul_comm, EF.mul_assoc, EF.mul_comm _ ((EF.ofF ch.c).mul _),
        EF.mul_inv hVZ, EF.mul_one]
    rw [hK]
    have hk1 : (kk ++ shiftK S ζ h A L seen' cs qs qs').take h = kk := List.take_left' hkl
    have hk2 : (kk ++ shiftK S ζ h A L seen' cs qs qs').drop h = shiftK S ζ h A L seen' cs qs qs' :=
      List.drop_left' hkl
    refine ⟨?_, fun rs hr => ?_, fun x hx => ?_, ?_⟩
    · rw [List.length_append, hkl, hKl, List.length_cons, Nat.succ_mul]; omega
    · have hrt : (rs.take h).length = h := by
        rw [List.length_take, hr, List.length_cons, Nat.succ_mul]; omega
      have hrd : (rs.drop h).length = cs.length * h := by
        rw [List.length_drop, hr, List.length_cons, Nat.succ_mul]; omega
      have ev : vadd rs (kk ++ shiftK S ζ h A L seen' cs qs qs') =
          vadd (rs.take h) kk ++ vadd (rs.drop h) (shiftK S ζ h A L seen' cs qs qs') := by
        conv => lhs; rw [← List.take_append_drop h rs]
        unfold vadd
        exact List.zipWith_append (by rw [hrt, hkl])
      have hvt : (vadd (rs.take h) kk).length = h := by rw [vadd_length, hrt, hkl, Nat.min_self]
      rw [ev]
      show (S.map (chunkAt ch.H ch.c q' ((vadd (rs.take h) kk ++ _).take h)),
          [ζ].map (chunkAtE ch.H ch.c q' ((vadd (rs.take h) kk ++ _).take h))) ::
          firstView S [ζ] h cs qs' ((vadd (rs.take h) kk ++ vadd (rs.drop h) (shiftK S ζ h A L seen' cs qs qs')).drop h) =
        (S.map (chunkAt ch.H ch.c q (rs.take h)), [ζ].map (chunkAtE ch.H ch.c q (rs.take h))) ::
          firstView S [ζ] h cs qs (rs.drop h)
      rw [List.take_left' hvt, List.drop_left' hvt, hKv _ hrd]
      congr 2
      · refine List.map_congr_left (fun x hx => ?_)
        unfold chunkAt
        rw [fval_vadd x _ _ (by rw [hrt, hkl])]
        exact shiftF _ _ _ _ _ (hown x hx)
      · refine List.map_congr_left (fun z hz => ?_)
        rw [List.mem_singleton.1 hz]
        unfold chunkAtE
        rw [fvalE_vadd ζ _ _ (by rw [hrt, hkl])]
        exact shiftE _ _ _ _ _ hownE
    · show fval x (fcadd (fcscale ch.m ((kk ++ _).take h)) (wsumR h cs ((kk ++ _).drop h))) =
        (ch.m * (fval x q * finv (ch.c * fval x (fvan ch.H))) + jsumF x cs qs -
          (ch.m * (fval x q' * finv (ch.c * fval x (fvan ch.H))) + jsumF x cs qs')) +
          (if (!seen x && (decide (x ∈ ch.H) || inSome x cs)) then L x - A x else 0)
      rw [hk1, hk2, fval_fcadd, fval_fcscale, hKS x hx, hkS x hx]
      unfold tgtF
      by_cases hxH : x ∈ ch.H
      · rw [if_pos hxH, fvan_zero_of_mem ch.c hxH]
        have hs' : seen' x = true := by show (seen x || decide (x ∈ ch.H)) = true; simp [hxH]
        rw [hs', show (decide (x ∈ ch.H) || inSome x cs) = true by simp [hxH], EF.finv_zero]
        cases hsx : seen x
        · simp only [Bool.not_true, Bool.false_and, Bool.not_false, Bool.false_eq_true, if_false]
          exact head_on_f _ _ _ _ _ _ hm
        · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
          exact head_on_t _ _ _ _ _
      · rw [if_neg hxH]
        have hs' : seen' x = seen x := by show (seen x || decide (x ∈ ch.H)) = seen x; simp [hxH]
        rw [hs', show (decide (x ∈ ch.H) || inSome x cs) = inSome x cs by simp [hxH]]
        exact head_off _ _ _ _ _ _ _
    · show fvalE ζ (fcadd (fcscale ch.m ((kk ++ _).take h)) (wsumR h cs ((kk ++ _).drop h))) =
        (((EF.ofF ch.m).mul ((fvalE ζ q).mul ((EF.ofF ch.c).mul (fvalE ζ (fvan ch.H))).inv)).add (jsumE ζ cs qs)).sub
          (((EF.ofF ch.m).mul ((fvalE ζ q').mul ((EF.ofF ch.c).mul (fvalE ζ (fvan ch.H))).inv)).add (jsumE ζ cs qs'))
      rw [hk1, hk2, fvalE_fcadd, fvalE_fcscale, hKZ, hkZ]
      exact jsE_step _ _ _ _ _ _

-- ---------------------------------------------------------------------------
-- The chunks hide all but what the verifier recombines
-- ---------------------------------------------------------------------------

/-- **Two chunk data that agree where the verifier can see them**: on
    each chunk's own domain (where its mask vanishes) the chunk's values,
    and off every domain the normalized recombination. -/
def Agree (S : List F) (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs qs' : List (List F))
    (ql ql' : List F) : Prop :=
  (∀ x ∈ S, AgreeH x cs qs qs') ∧ (∀ x ∈ S, x ∈ Hl → fval x ql = fval x ql') ∧
    (∀ x ∈ S, x ∉ Hl → inSome x cs = false → chunkJ x cs Hl cl qs ql = chunkJ x cs Hl cl qs' ql') ∧
    chunkJE ζ cs Hl cl qs ql = chunkJE ζ cs Hl cl qs' ql'

theorem last_none (ql ql' V a b : F) (hV : V ≠ 0) (hJ : ql * finv V + a = ql' * finv V + b) :
    V * (a - b + 0) = ql' - ql := by
  rw [add_zero']; exact jdiffF (mul_finv hV) hJ rfl

theorem add_sub_cancel_f (a l : F) : a + (l - a) = l :=
  fid (e := v 0 + (v 1 - v 0)) (e' := v 1) (by decide) [a, l]

theorem mul_div_cancel3 (V d : F) (hV : V ≠ 0) : V * (d * finv V) = d := by
  rw [mul_comm' d, ← mul_assoc', mul_finv hV, one_mul']

/-- **The explicit shift** of the chunks' random polynomials carrying
    `qs` to `qs'` (`shiftK` with the targets of `chunks_shiftV`). -/
def ckey (S : List F) (ζ : EF) (h : Nat) (cs : List Chunk) (Hl : List F) (cl : F) (qs qs' : List (List F))
    (ql ql' : List F) : List F :=
  shiftK S ζ h (fun x => jsumF x cs qs - jsumF x cs qs') (fun x => (fval x ql' - fval x ql) * finv (cl * fval x (fvan Hl)))
    (fun _ => false) cs qs qs'

/-- **The chunks' shift**: for two chunk data that agree where the
    verifier can see them, a shift of the random polynomials under which
    the second opens as the first. -/
theorem chunks_shiftV {S : List F} {ζ : EF} {h : Nat} (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hd : (mz ζ).det ≠ 0)
    (hn : S.length + 4 ≤ h) {cs : List Chunk} {Hl : List F} {cl : F}
    (hok : ∀ ch ∈ cs, ch.c ≠ 0 ∧ ch.m ≠ 0) (hcl : cl ≠ 0)
    {qs qs' : List (List F)} {ql ql' : List F} (h1 : qs.length = cs.length) (h2 : qs'.length = cs.length)
    (hag : Agree S ζ cs Hl cl qs qs' ql ql') :
    (ckey S ζ h cs Hl cl qs qs' ql ql').length = cs.length * h ∧ ∀ rs : List F, rs.length = cs.length * h →
      chunksView S [ζ] h cs Hl cl qs' ql' (vadd rs (ckey S ζ h cs Hl cl qs qs' ql ql')) =
        chunksView S [ζ] h cs Hl cl qs ql rs := by
  obtain ⟨hH, hHl, hJ, hJE⟩ := hag
  let A : F → F := fun x => jsumF x cs qs - jsumF x cs qs'
  let L : F → F := fun x => (fval x ql' - fval x ql) * finv (cl * fval x (fvan Hl))
  obtain ⟨hKl, hKv, hKS, hKZ⟩ := shiftK_spec hζ hd hn A L (fun _ => false) cs qs qs' hok h1 h2 hH
  let K := shiftK S ζ h A L (fun _ => false) cs qs qs'
  refine ⟨hKl, fun rs hr => ?_⟩
  unfold ckey chunksView
  rw [hKv rs hr]
  congr 3
  · refine List.map_congr_left (fun x hx => ?_)
    unfold chunkAt
    rw [fval_fcscale, fval_fcscale, wsumR_vadd x h cs rs K hr hKl]
    refine lastF _ _ _ _ _ ?_
    rw [hKS x hx]
    by_cases hxl : x ∈ Hl
    · rw [fvan_zero_of_mem cl hxl, zero_mul', hHl x hx hxl, sub_self']
    · have hV : cl * fval x (fvan Hl) ≠ 0 := mul_ne_zero' hcl (fvan_ne x Hl hxl)
      cases hs : inSome x cs
      · simp only [Bool.not_false, Bool.and_false, Bool.false_eq_true, if_false]
        exact last_none _ _ _ _ _ hV (hJ x hx hxl hs)
      · simp only [Bool.not_false, Bool.and_true, if_true]
        show cl * fval x (fvan Hl) * (A x + (L x - A x)) = fval x ql' - fval x ql
        rw [add_sub_cancel_f]
        exact mul_div_cancel3 _ _ hV
  · refine List.map_congr_left (fun z hz => ?_)
    rw [List.mem_singleton.1 hz]
    have hV : (EF.ofF cl).mul (fvalE ζ (fvan Hl)) ≠ EF.zero :=
      mulE_ne_zero (ofF_ne_zero hcl) (fvalE_fvan_ne ζ hζ Hl)
    unfold chunkAtE
    rw [fvalE_fcscale, fvalE_fcscale, wsumR_vaddE ζ h cs rs K hr hKl]
    exact lastE _ _ _ _ _ (jdiffE (EF.mul_inv hV) hJE hKZ)

/-- **The chunks hide all but what the verifier recombines**: two chunk
    data that agree where the verifier can see them (`Agree`) open with
    one distribution over the chunks' random polynomials. -/
theorem chunks_hide {S : List F} {ζ : EF} {h : Nat} (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hd : (mz ζ).det ≠ 0)
    (hn : S.length + 4 ≤ h) {cs : List Chunk} {Hl : List F} {cl : F}
    (hok : ∀ ch ∈ cs, ch.c ≠ 0 ∧ ch.m ≠ 0) (hcl : cl ≠ 0)
    {qs qs' : List (List F)} {ql ql' : List F} (h1 : qs.length = cs.length) (h2 : qs'.length = cs.length)
    (hag : Agree S ζ cs Hl cl qs qs' ql ql') (E : List (List F × List EF) → Bool) :
    vsum (cs.length * h) (fun rs => if E (chunksView S [ζ] h cs Hl cl qs ql rs) then 1 else 0) =
      vsum (cs.length * h) (fun rs => if E (chunksView S [ζ] h cs Hl cl qs' ql' rs) then 1 else 0) := by
  obtain ⟨hKl, he⟩ := chunks_shiftV hζ hd hn hok hcl h1 h2 hag
  let K := ckey S ζ h cs Hl cl qs qs' ql ql'
  rw [← vsum_shift _ K hKl (fun rs => if E (chunksView S [ζ] h cs Hl cl qs' ql' rs) then 1 else 0)]
  refine vsum_congr _ (fun rs hr => ?_)
  show (if E (chunksView S [ζ] h cs Hl cl qs ql rs) = true then 1 else 0) =
    (if E (chunksView S [ζ] h cs Hl cl qs' ql' (vadd rs K)) = true then 1 else 0)
  rw [he rs hr]

-- ---------------------------------------------------------------------------
-- Chunks with given views: the simulator's
-- ---------------------------------------------------------------------------

/-- Each chunk other than the last shows `tg` on its own domain. -/
def ShowsH (x : F) (tg : F → F) : List Chunk → List (List F) → Prop
  | ch :: cs, q :: qs => (x ∈ ch.H → fval x q = tg x) ∧ ShowsH x tg cs qs
  | _, _ => True

/-- **What chunks show the verifier**, `tg` on the query points and `tζ`
    at `ζ`: on a chunk's own domain the chunk's value, and off every
    domain the normalized recombination. -/
def Shows (S : List F) (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F)
    (tg : F → F) (tζ : EF) : Prop :=
  (∀ x ∈ S, ShowsH x tg cs qs) ∧ (∀ x ∈ S, x ∈ Hl → fval x ql = tg x) ∧
    (∀ x ∈ S, x ∉ Hl → inSome x cs = false → chunkJ x cs Hl cl qs ql = tg x) ∧
    chunkJE ζ cs Hl cl qs ql = tζ

theorem agreeH_of_shows (x : F) (tg : F → F) : ∀ (cs : List Chunk) (qs qs' : List (List F)),
    ShowsH x tg cs qs → ShowsH x tg cs qs' → AgreeH x cs qs qs'
  | _ :: cs, _ :: qs, _ :: qs', ⟨a, b⟩, ⟨a', b'⟩ =>
    ⟨fun hx => (a hx).trans (a' hx).symm, agreeH_of_shows x tg cs qs qs' b b'⟩
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _ => trivial

theorem agree_of_shows {S : List F} {ζ : EF} {cs : List Chunk} {Hl : List F} {cl : F} {qs qs' : List (List F)}
    {ql ql' : List F} {tg : F → F} {tζ : EF} (h : Shows S ζ cs Hl cl qs ql tg tζ)
    (h' : Shows S ζ cs Hl cl qs' ql' tg tζ) : Agree S ζ cs Hl cl qs qs' ql ql' :=
  ⟨fun x hx => agreeH_of_shows x tg cs qs qs' (h.1 x hx) (h'.1 x hx),
    fun x hx hl => (h.2.1 x hx hl).trans (h'.2.1 x hx hl).symm,
    fun x hx hl hs => (h.2.2.1 x hx hl hs).trans (h'.2.2.1 x hx hl hs).symm,
    h.2.2.2.trans h'.2.2.2.symm⟩

/-- **The canonical chunks**: each through `tg` on its own domain and zero
    elsewhere, the last through `tg` on its domain and `tg · v_l` off every
    domain, and `tζ · v_l(ζ)` at `ζ`. -/
def canonQs (S : List F) (ζ : EF) (tg : F → F) (cs : List Chunk) : List (List F) :=
  cs.map fun ch => interpSZ S (fun x => if x ∈ ch.H then tg x else 0) ζ EF.zero

def canonQl (S : List F) (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (tg : F → F) (tζ : EF) : List F :=
  interpSZ S (fun x => if x ∈ Hl then tg x else if inSome x cs then 0 else tg x * (cl * fval x (fvan Hl))) ζ
    (tζ.mul ((EF.ofF cl).mul (fvalE ζ (fvan Hl))))

theorem inSome_false {x : F} : ∀ {cs : List Chunk}, inSome x cs = false → ∀ ch ∈ cs, x ∉ ch.H
  | [], _, _, hc => nomatch hc
  | c :: cs, h, ch, hc => by
    have h' : (decide (x ∈ c.H) || inSome x cs) = false := h
    rw [Bool.or_eq_false_iff] at h'
    rcases List.mem_cons.1 hc with rfl | hc
    · exact of_decide_eq_false h'.1
    · exact inSome_false h'.2 ch hc

theorem canon_showsH {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hd : (mz ζ).det ≠ 0) (tg : F → F)
    {x : F} (hx : x ∈ S) : ∀ cs : List Chunk, ShowsH x tg cs (canonQs S ζ tg cs)
  | [] => trivial
  | ch :: cs => ⟨fun hH => by
      show fval x (interpSZ S (fun x => if x ∈ ch.H then tg x else 0) ζ EF.zero) = tg x
      rw [(interpSZ_spec S _ ζ EF.zero hζ hd).2.1 x hx, if_pos hH],
    canon_showsH hζ hd tg hx cs⟩

theorem jsumF_canon {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hd : (mz ζ).det ≠ 0) (tg : F → F)
    {x : F} (hx : x ∈ S) : ∀ cs : List Chunk, (∀ ch ∈ cs, x ∉ ch.H) → jsumF x cs (canonQs S ζ tg cs) = 0
  | [], _ => rfl
  | ch :: cs, hn => by
    show ch.m * (fval x (interpSZ S (fun x => if x ∈ ch.H then tg x else 0) ζ EF.zero) *
      finv (ch.c * fval x (fvan ch.H))) + jsumF x cs (canonQs S ζ tg cs) = 0
    rw [(interpSZ_spec S _ ζ EF.zero hζ hd).2.1 x hx, if_neg (hn ch List.mem_cons_self),
      jsumF_canon hζ hd tg hx cs (fun c hc => hn c (List.mem_cons_of_mem _ hc)), zero_mul', mul_zero', add_zero']

theorem jsumE_canon {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hd : (mz ζ).det ≠ 0) (tg : F → F) :
    ∀ cs : List Chunk, jsumE ζ cs (canonQs S ζ tg cs) = EF.zero
  | [] => rfl
  | ch :: cs => by
    show ((EF.ofF ch.m).mul ((fvalE ζ (interpSZ S (fun x => if x ∈ ch.H then tg x else 0) ζ EF.zero)).mul
      ((EF.ofF ch.c).mul (fvalE ζ (fvan ch.H))).inv)).add (jsumE ζ cs (canonQs S ζ tg cs)) = EF.zero
    rw [(interpSZ_spec S _ ζ EF.zero hζ hd).2.2, jsumE_canon hζ hd tg cs, EF.zero_mul, EF.mul_zero, EF.add_zero]

theorem mul_mul_finv (a V : F) (hV : V ≠ 0) : a * V * finv V = a := by
  rw [mul_assoc', mul_finv hV, mul_one']

theorem mulE_mul_inv (a V : EF) (hV : V ≠ EF.zero) : (a.mul V).mul V.inv = a := by
  rw [EF.mul_assoc, EF.mul_inv hV, EF.mul_one]

/-- **The canonical chunks show the targets**. -/
theorem canon_shows {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hd : (mz ζ).det ≠ 0) {cl : F}
    (hcl : cl ≠ 0) (cs : List Chunk) (Hl : List F) (tg : F → F) (tζ : EF) :
    Shows S ζ cs Hl cl (canonQs S ζ tg cs) (canonQl S ζ cs Hl cl tg tζ) tg tζ := by
  have hS := (interpSZ_spec S (fun x => if x ∈ Hl then tg x else if inSome x cs then 0
    else tg x * (cl * fval x (fvan Hl))) ζ (tζ.mul ((EF.ofF cl).mul (fvalE ζ (fvan Hl)))) hζ hd)
  refine ⟨fun x hx => canon_showsH hζ hd tg hx cs, fun x hx hl => ?_, fun x hx hl hs => ?_, ?_⟩
  · show fval x (interpSZ S _ ζ _) = tg x
    rw [hS.2.1 x hx, if_pos hl]
  · unfold chunkJ canonQl
    rw [hS.2.1 x hx, if_neg hl, hs, if_neg (by decide), jsumF_canon hζ hd tg hx cs (inSome_false hs), add_zero',
      mul_mul_finv _ _ (mul_ne_zero' hcl (fvan_ne x Hl hl))]
  · unfold chunkJE canonQl
    rw [hS.2.2, jsumE_canon hζ hd tg cs, EF.add_zero,
      mulE_mul_inv _ _ (mulE_ne_zero (ofF_ne_zero hcl) (fvalE_fvan_ne ζ hζ Hl))]

/-- **The chunks are simulated from what they show**: chunk data showing
    `tg` and `tζ` open, over the chunks' random polynomials, as the
    canonical chunks built from `tg` and `tζ` alone. -/
theorem chunks_sim {S : List F} {ζ : EF} {h : Nat} (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hd : (mz ζ).det ≠ 0)
    (hn : S.length + 4 ≤ h) {cs : List Chunk} {Hl : List F} {cl : F}
    (hok : ∀ ch ∈ cs, ch.c ≠ 0 ∧ ch.m ≠ 0) (hcl : cl ≠ 0)
    {qs : List (List F)} {ql : List F} (h1 : qs.length = cs.length) (tg : F → F) (tζ : EF)
    (hsh : Shows S ζ cs Hl cl qs ql tg tζ) (E : List (List F × List EF) → Bool) :
    vsum (cs.length * h) (fun rs => if E (chunksView S [ζ] h cs Hl cl qs ql rs) then 1 else 0) =
      vsum (cs.length * h) (fun rs =>
        if E (chunksView S [ζ] h cs Hl cl (canonQs S ζ tg cs) (canonQl S ζ cs Hl cl tg tζ) rs) then 1 else 0) :=
  chunks_hide hζ hd hn hok hcl h1 (by unfold canonQs; rw [List.length_map])
    (agree_of_shows hsh (canon_shows hζ hd hcl cs Hl tg tζ)) E

-- ---------------------------------------------------------------------------
-- The recombination the verifier computes
-- ---------------------------------------------------------------------------

/-- `Σ m_i · q'_i(x) / v_i(x)` over the opened chunks other than the last. -/
def rsumF (x : F) (h : Nat) : List Chunk → List (List F) → List F → F
  | ch :: cs, q :: qs, rs => ch.m * (chunkAt ch.H ch.c q (rs.take h) x * finv (ch.c * fval x (fvan ch.H))) +
      rsumF x h cs qs (rs.drop h)
  | _, _, _ => 0

theorem rstep (m q V r fi W J : F) (hV : V * fi = 1) :
    m * ((q + V * r) * fi) + (J + W) = m * (q * fi) + J + (m * r + W) := by
  have e : m * ((q + V * r) * fi) = m * (q * fi) + m * r * (V * fi) :=
    fid (e := v 0 * ((v 1 + v 2 * v 3) * v 4)) (e' := v 0 * (v 1 * v 4) + v 0 * v 3 * (v 2 * v 4)) (by decide)
      [m, q, V, r, fi]
  rw [e, hV, mul_one']
  exact fid (e := (v 0 + v 1) + (v 2 + v 3)) (e' := v 0 + v 2 + (v 1 + v 3)) (by decide)
    [m * (q * fi), m * r, J, W]

theorem rsumF_eq (x : F) (h : Nat) : ∀ (cs : List Chunk) (qs : List (List F)) (rs : List F),
    (∀ ch ∈ cs, ch.c * fval x (fvan ch.H) ≠ 0) → qs.length = cs.length →
    rsumF x h cs qs rs = jsumF x cs qs + fval x (wsumR h cs rs)
  | [], [], _, _, _ => by show (0 : F) = 0 + 0; rw [add_zero']
  | [], _ :: _, _, _, hl => nomatch hl
  | _ :: _, [], _, _, hl => nomatch hl
  | ch :: cs, q :: qs, rs, hV, hl => by
    show ch.m * ((fval x q + ch.c * fval x (fvan ch.H) * fval x (rs.take h)) * finv (ch.c * fval x (fvan ch.H))) +
        rsumF x h cs qs (rs.drop h) =
      (ch.m * (fval x q * finv (ch.c * fval x (fvan ch.H))) + jsumF x cs qs) +
        fval x (fcadd (fcscale ch.m (rs.take h)) (wsumR h cs (rs.drop h)))
    rw [rsumF_eq x h cs qs (rs.drop h) (fun c hc => hV c (List.mem_cons_of_mem _ hc))
      (by simp only [List.length_cons] at hl; omega), fval_fcadd, fval_fcscale]
    exact rstep _ _ _ _ _ _ _ (mul_finv (hV ch List.mem_cons_self))

theorem lstep (ql V W fi R : F) (hV : V * fi = 1) :
    R + W + (ql + V * (-1 * W)) * fi = R + ql * fi := by
  have e : (ql + V * (-1 * W)) * fi = ql * fi + (-1) * W * (V * fi) :=
    fid (e := (v 0 + v 1 * (k (-1) * v 2)) * v 3) (e' := v 0 * v 3 + k (-1) * v 2 * (v 1 * v 3)) (by decide)
      [ql, V, W, fi]
  rw [e, hV, mul_one']
  exact fid (e := v 0 + v 1 + (v 2 + k (-1) * v 1)) (e' := v 0 + v 2) (by decide) [R, W, ql * fi]

/-- **The recombination is the normalized one, whatever the randomness**,
    at a point of `F` off every domain (`chunks_recombineE` at `ζ`, where
    the verifier performs it): Plonky3 recombines the opened chunks as
    `Σ zp_i(x) q'_i(x)`, `zp_i = cis_i ∏_{j ≠ i} v_j`, which is
    `cis_l ∏_j v_j(x)` times `Σ m_i q'_i(x)/v_i(x) + q'_l(x)/v_l(x)`
    (`m_i = cis_i / cis_l`, Plonky3's `mul_coeffs`); that sum is
    `chunkJ`, the random polynomials cancelling. -/
theorem chunks_recombine {x : F} {h : Nat} {cs : List Chunk} {Hl : List F} {cl : F} {qs : List (List F)}
    {ql rs : List F} (hV : ∀ ch ∈ cs, ch.c * fval x (fvan ch.H) ≠ 0) (hVl : cl * fval x (fvan Hl) ≠ 0)
    (hl : qs.length = cs.length) :
    rsumF x h cs qs rs + chunkAt Hl cl ql (fcscale (-1) (wsumR h cs rs)) x * finv (cl * fval x (fvan Hl)) =
      chunkJ x cs Hl cl qs ql := by
  unfold chunkAt chunkJ
  rw [rsumF_eq x h cs qs rs hV hl, fval_fcscale, add_comm' (fval x ql * _) (jsumF x cs qs)]
  exact lstep _ _ _ _ _ (mul_finv hVl)

/-- `Σ m_i · q'_i(z) / v_i(z)` at a point of the extension. -/
def rsumE (z : EF) (h : Nat) : List Chunk → List (List F) → List F → EF
  | ch :: cs, q :: qs, rs => ((EF.ofF ch.m).mul ((chunkAtE ch.H ch.c q (rs.take h) z).mul
      ((EF.ofF ch.c).mul (fvalE z (fvan ch.H))).inv)).add (rsumE z h cs qs (rs.drop h))
  | _, _, _ => EF.zero

theorem rstepE1 (m q V r fi : EF) : m.mul ((q.add (V.mul r)).mul fi) = (m.mul (q.mul fi)).add ((m.mul r).mul (V.mul fi)) :=
  Q.eq_of_norm (p := (Q.var 0).mul (((Q.var 1).add ((Q.var 2).mul (Q.var 3))).mul (Q.var 4)))
    (q := ((Q.var 0).mul ((Q.var 1).mul (Q.var 4))).add (((Q.var 0).mul (Q.var 3)).mul ((Q.var 2).mul (Q.var 4))))
    (by decide) (env8 m q V r fi EF.zero EF.zero EF.zero)

theorem rstepE2 (a b J W : EF) : (a.add b).add (J.add W) = (a.add J).add (b.add W) :=
  Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).add ((Q.var 2).add (Q.var 3)))
    (q := ((Q.var 0).add (Q.var 2)).add ((Q.var 1).add (Q.var 3))) (by decide) (env4 a b J W)

theorem rsumE_eq (z : EF) (h : Nat) : ∀ (cs : List Chunk) (qs : List (List F)) (rs : List F),
    (∀ ch ∈ cs, (EF.ofF ch.c).mul (fvalE z (fvan ch.H)) ≠ EF.zero) → qs.length = cs.length →
    rsumE z h cs qs rs = (jsumE z cs qs).add (fvalE z (wsumR h cs rs))
  | [], [], _, _, _ => by show EF.zero = EF.zero.add EF.zero; rw [EF.add_zero]
  | [], _ :: _, _, _, hl => nomatch hl
  | _ :: _, [], _, _, hl => nomatch hl
  | ch :: cs, q :: qs, rs, hV, hl => by
    show ((EF.ofF ch.m).mul (((fvalE z q).add (((EF.ofF ch.c).mul (fvalE z (fvan ch.H))).mul (fvalE z (rs.take h)))).mul
        ((EF.ofF ch.c).mul (fvalE z (fvan ch.H))).inv)).add (rsumE z h cs qs (rs.drop h)) =
      (((EF.ofF ch.m).mul ((fvalE z q).mul ((EF.ofF ch.c).mul (fvalE z (fvan ch.H))).inv)).add (jsumE z cs qs)).add
        (fvalE z (fcadd (fcscale ch.m (rs.take h)) (wsumR h cs (rs.drop h))))
    rw [rsumE_eq z h cs qs (rs.drop h) (fun c hc => hV c (List.mem_cons_of_mem _ hc))
      (by simp only [List.length_cons] at hl; omega), fvalE_fcadd, fvalE_fcscale, rstepE1,
      EF.mul_inv (hV ch List.mem_cons_self), EF.mul_one, rstepE2]

theorem lstepE (ql V W fi R : EF) (hV : V.mul fi = EF.one) :
    (R.add W).add ((ql.add (V.mul ((EF.ofF (-1)).mul W))).mul fi) = (ql.mul fi).add R := by
  rw [ofF_neg', show EF.ofF 1 = EF.one from rfl]
  have e : (ql.add (V.mul (EF.one.neg.mul W))).mul fi = (ql.mul fi).add ((EF.one.neg.mul W).mul (V.mul fi)) :=
    Q.eq_of_norm (p := ((Q.var 0).add ((Q.var 1).mul ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 2)))).mul (Q.var 3))
      (q := ((Q.var 0).mul (Q.var 3)).add (((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 2)).mul ((Q.var 1).mul (Q.var 3))))
      (by decide) (env4 ql V W fi)
  rw [e, hV, EF.mul_one]
  exact Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).add ((Q.var 2).add ((⟨k 1, k 0, k 0, k 0⟩ : Q).neg.mul (Q.var 1))))
    (q := (Q.var 2).add (Q.var 0)) (by decide) (env3 R W (ql.mul fi))

/-- **The verifier's recombination at `ζ`**, where Plonky3 performs it:
    the opened chunks' normalized sum is `chunkJE`, the random
    polynomials cancelling, as `chunks_recombine` at the query points. -/
theorem chunks_recombineE {z : EF} {h : Nat} {cs : List Chunk} {Hl : List F} {cl : F} {qs : List (List F)}
    {ql rs : List F} (hV : ∀ ch ∈ cs, (EF.ofF ch.c).mul (fvalE z (fvan ch.H)) ≠ EF.zero)
    (hVl : (EF.ofF cl).mul (fvalE z (fvan Hl)) ≠ EF.zero) (hl : qs.length = cs.length) :
    (rsumE z h cs qs rs).add ((chunkAtE Hl cl ql (fcscale (-1) (wsumR h cs rs)) z).mul
      ((EF.ofF cl).mul (fvalE z (fvan Hl))).inv) = chunkJE z cs Hl cl qs ql := by
  unfold chunkAtE chunkJE
  rw [rsumE_eq z h cs qs rs hV hl, fvalE_fcscale]
  exact lstepE _ _ _ _ _ (EF.mul_inv hVl)

-- ---------------------------------------------------------------------------
-- Every quotient column's chunks, and the PCS
-- ---------------------------------------------------------------------------

/-- **The chunks of one quotient column**: the chunks other than the last,
    the last's domain and scale, the query points `S` and the
    out-of-domain point `ζ` they open at, their height `h`, and what they
    show the verifier (`Shows`) at each query point and at `ζ`, from the
    challenges, the published terminals and every group's column
    openings. -/
structure CSet where
  cs : List Chunk
  Hl : List F
  cl : F
  S : List F
  ζ : EF
  h : Nat
  JS : EF → EF → List EF → List (List (List F × List EF)) → F → F
  Jζ : EF → EF → List EF → List (List (List F × List EF)) → EF

/-- What a column's chunks ask: `ζ` off `F` and generating the extension,
    `|S| + 4 ≤ h`, nonzero scales and weights. -/
def CSet.OK (c : CSet) : Prop :=
  (∀ x : F, EF.ofF x ≠ c.ζ) ∧ (mz c.ζ).det ≠ 0 ∧ c.S.length + 4 ≤ c.h ∧ (∀ ch ∈ c.cs, ch.c ≠ 0 ∧ ch.m ≠ 0) ∧
    c.cl ≠ 0

/-- The random coefficients the chunks use. -/
def ctot : List CSet → Nat
  | [] => 0
  | c :: cs => c.cs.length * c.h + ctot cs

/-- **Every column's opened chunks**, the randomness split column by column. -/
def csView : List CSet → List (List (List F) × List F) → List F → List (List (List F × List EF))
  | c :: cs, d :: ds, cr => chunksView c.S [c.ζ] c.h c.cs c.Hl c.cl d.1 d.2 (cr.take (c.cs.length * c.h)) ::
      csView cs ds (cr.drop (c.cs.length * c.h))
  | _, _, _ => []

/-- The chunk data fit the columns and show the targets. -/
def RecOK : List CSet → List (List (List F) × List F) → (CSet → F → F) → (CSet → EF) → Prop
  | c :: cs, d :: ds, JS, JE => (d.1.length = c.cs.length ∧ Shows c.S c.ζ c.cs c.Hl c.cl d.1 d.2 (JS c) (JE c)) ∧
      RecOK cs ds JS JE
  | [], [], _, _ => True
  | _, _, _, _ => False

/-- The canonical chunks of every column, from the targets alone. -/
def canonData (csets : List CSet) (α β : EF) (v : List EF) (o : List (List (List F × List EF))) :
    List (List (List F) × List F) :=
  csets.map fun c => (canonQs c.S c.ζ (c.JS α β v o) c.cs, canonQl c.S c.ζ c.cs c.Hl c.cl (c.JS α β v o) (c.Jζ α β v o))

/-- **Every column's chunks are simulated from their recombinations**. -/
theorem csets_sim : ∀ (csets : List CSet) (ds : List (List (List F) × List F)) (α β : EF) (v : List EF)
    (o : List (List (List F × List EF))), (∀ c ∈ csets, c.OK) →
    RecOK csets ds (fun c => c.JS α β v o) (fun c => c.Jζ α β v o) →
    ∀ E : List (List (List F × List EF)) → Bool,
    vsum (ctot csets) (fun cr => if E (csView csets ds cr) then 1 else 0) =
      vsum (ctot csets) (fun cr => if E (csView csets (canonData csets α β v o) cr) then 1 else 0)
  | [], [], _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, _, _, _, h, _ => nomatch h
  | c :: csets, d :: ds, α, β, v, o, hok, ⟨⟨h1, hsh⟩, hrec⟩, E => by
    obtain ⟨hζ, hd, hn, hcs, hcl⟩ := hok c List.mem_cons_self
    have hok' : ∀ c' ∈ csets, c'.OK := fun c' hc => hok c' (List.mem_cons_of_mem _ hc)
    let a := c.cs.length * c.h
    let b := ctot csets
    let w : List (List F) × List F → List F → List (List F × List EF) :=
      fun d x => chunksView c.S [c.ζ] c.h c.cs c.Hl c.cl d.1 d.2 x
    let cd : List (List F) × List F :=
      (canonQs c.S c.ζ (c.JS α β v o) c.cs, canonQl c.S c.ζ c.cs c.Hl c.cl (c.JS α β v o) (c.Jζ α β v o))
    have split : ∀ (u : List (List F) × List F) (us : List (List (List F) × List F)) (x y : List F), x.length = a →
        csView (c :: csets) (u :: us) (x ++ y) = w u x :: csView csets us y := by
      intro u us x y hx
      show chunksView c.S [c.ζ] c.h c.cs c.Hl c.cl u.1 u.2 ((x ++ y).take a) :: csView csets us ((x ++ y).drop a) = _
      rw [List.take_left' hx, List.drop_left' hx]
    show vsum (a + b) _ = vsum (a + b) _
    rw [vsum_append b, vsum_append b]
    calc vsum a (fun x => vsum b (fun y => if E (csView (c :: csets) (d :: ds) (x ++ y)) then 1 else 0))
        = vsum a (fun x => vsum b (fun y => if E (w d x :: csView csets ds y) then 1 else 0)) :=
          vsum_congr _ (fun x hx => vsum_congr _ (fun y _ => by rw [split d ds x y hx]))
      _ = vsum a (fun x => vsum b (fun y => if E (w d x :: csView csets (canonData csets α β v o) y) then 1 else 0)) :=
          vsum_congr _ (fun x _ => csets_sim csets ds α β v o hok' hrec (fun L => E (w d x :: L)))
      _ = vsum b (fun y => vsum a (fun x => if E (w d x :: csView csets (canonData csets α β v o) y) then 1 else 0)) :=
          vsum_comm _ _ _
      _ = vsum b (fun y => vsum a (fun x => if E (w cd x :: csView csets (canonData csets α β v o) y) then 1 else 0)) :=
          vsum_congr _ (fun y _ => chunks_sim hζ hd hn hcs hcl h1 (c.JS α β v o) (c.Jζ α β v o) hsh
            (fun L => E (L :: csView csets (canonData csets α β v o) y)))
      _ = vsum a (fun x => vsum b (fun y => if E (w cd x :: csView csets (canonData csets α β v o) y) then 1 else 0)) :=
          (vsum_comm _ _ _).symm
      _ = vsum a (fun x => vsum b (fun y =>
            if E (csView (c :: csets) (canonData (c :: csets) α β v o) (x ++ y)) then 1 else 0)) :=
          vsum_congr _ (fun x hx => vsum_congr _ (fun y _ => by
            rw [show canonData (c :: csets) α β v o = cd :: canonData csets α β v o from rfl, split cd _ x y hx]))

section
variable (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
  (qs : List QGroup) (ks : List Nat) (cols : (Nat → Tup) → EF → EF → List (List (List F)))
  (csets : List CSet) (qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F))

/-- **The masked PCS with its quotients and their chunks**: every group's
    column openings and quotient values, as `pcsQuot`, and every quotient
    column's chunks at its query points and at `ζ`, the honest chunks `qd`
    computed from the trace, the challenges and the column masks; the
    randomness the column masks, then the chunks' random polynomials. -/
def pcsChunk (t : Nat → Tup) (α β : EF) (r : Nat) :
    List (List (List F × List EF) × List (List EF)) × List (List (List F × List EF)) :=
  let ds := digitsF (mtotal (qs.map QGroup.ext) ks + ctot csets) r
  let ms := ds.take (mtotal (qs.map QGroup.ext) ks)
  (quotPost qs α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms),
    csView csets (qd t α β ms) (ds.drop (mtotal (qs.map QGroup.ext) ks)))
end

section
variable (qs : List QGroup) (ks : List Nat) (csets : List CSet)

/-- **Its simulator**: zero columns under the same masks, the quotient
    values from their openings, and the canonical chunks from the
    recombinations those openings give. -/
def psimChunk (α β : EF) (v : List EF) (r : Nat) :
    List (List (List F × List EF) × List (List EF)) × List (List (List F × List EF)) :=
  let ds := digitsF (mtotal (qs.map QGroup.ext) ks + ctot csets) r
  let ms := ds.take (mtotal (qs.map QGroup.ext) ks)
  let o := openMulti (qs.map QGroup.ext) (((qs.map QGroup.ext).zip ks).map
    (fun p => List.replicate p.2 (List.replicate p.1.n 0))) ms
  (quotPost qs α β v o, csView csets (canonData csets α β v o) (ds.drop (mtotal (qs.map QGroup.ext) ks)))
end

/-- **The masked PCS hides its quotients' chunks exactly**: with the
    quotient groups' masks covering their points (`QGroup.OK`), every
    quotient column's chunks meeting `CSet.OK`, and the honest chunks
    recombining, at their query points and at `ζ`, to the targets the
    column openings give (`RecOK`), the view of the column openings, the
    quotient values and every chunk's opened values has the simulator's
    distribution: `PCSCloseN` with `ε = 0`. -/
theorem pcsCloseN_chunks {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    {csets : List CSet} {qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F)}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (hcs : ∀ c ∈ csets, c.OK) (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    (hrec : ∀ t α β ms, RecOK csets (qd t α β ms)
      (fun c => c.JS α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))) :
    PCSCloseN off (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) tv
      (pcsChunk off tv qs ks cols csets qd) (psimChunk qs ks csets) 0 := by
  intro t α β Ev
  let gs := qs.map QGroup.ext
  let M := mtotal gs ks
  let C := ctot csets
  let v := tv (prefixOf α (off β)) β t
  let zs := (gs.zip ks).map (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F)))
  have hgs : ∀ g ∈ gs, g.OK := fun g hg => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
    exact QGroup.ext_OK (hok q hq)
  obtain ⟨hsh, hl⟩ := hcols t α β
  obtain ⟨hz, hzl⟩ := shaped_zero gs ks (by rw [hks, List.length_map])
  let G : List (List (List F × List EF)) → List F → Nat := fun o cr =>
    indB (Ev (quotPost qs α β v o, csView csets (canonData csets α β v o) cr))
  have key : sumTo (P ^ (M + C)) (fun r => indB (Ev (pcsChunk off tv qs ks cols csets qd t α β r))) =
      sumTo (P ^ (M + C)) (fun r => indB (Ev (psimChunk qs ks csets α β v r))) := by
    unfold pcsChunk psimChunk
    rw [sumTo_digitsF (M + C) (fun ds => indB (Ev (quotPost qs α β v (openMulti gs (cols t α β) (ds.take M)),
        csView csets (qd t α β (ds.take M)) (ds.drop M)))),
      sumTo_digitsF (M + C) (fun ds => indB (Ev (quotPost qs α β v (openMulti gs zs (ds.take M)),
        csView csets (canonData csets α β v (openMulti gs zs (ds.take M))) (ds.drop M))))]
    rw [vsum_append C, vsum_append C]
    calc vsum M (fun x => vsum C (fun y => indB (Ev (quotPost qs α β v (openMulti gs (cols t α β) ((x ++ y).take M)),
          csView csets (qd t α β ((x ++ y).take M)) ((x ++ y).drop M)))))
        = vsum M (fun x => vsum C (fun y => G (openMulti gs (cols t α β) x) y)) :=
          vsum_congr _ (fun x hx => by
            rw [show (fun y => indB (Ev (quotPost qs α β v (openMulti gs (cols t α β) ((x ++ y).take M)),
                csView csets (qd t α β ((x ++ y).take M)) ((x ++ y).drop M)))) =
                fun y => indB (Ev (quotPost qs α β v (openMulti gs (cols t α β) x), csView csets (qd t α β x) y)) from
              funext fun y => by rw [List.take_left' hx, List.drop_left' hx]]
            exact csets_sim csets (qd t α β x) α β v (openMulti gs (cols t α β) x) hcs (hrec t α β x)
              (fun L => Ev (quotPost qs α β v (openMulti gs (cols t α β) x), L)))
      _ = vsum C (fun y => vsum M (fun x => G (openMulti gs (cols t α β) x) y)) := vsum_comm _ _ _
      _ = vsum C (fun y => vsum M (fun x => G (openMulti gs zs x) y)) := by
          refine vsum_congr _ (fun y _ => ?_)
          have h := masks_hide_multi gs (cols t α β) zs hgs hsh hz (by rw [hl, hzl])
            (fun o => Ev (quotPost qs α β v o, csView csets (canonData csets α β v o) y))
          rw [hl] at h
          exact h
      _ = vsum M (fun x => vsum C (fun y => G (openMulti gs zs x) y)) := (vsum_comm _ _ _).symm
      _ = vsum M (fun x => vsum C (fun y => indB (Ev (quotPost qs α β v (openMulti gs zs ((x ++ y).take M)),
            csView csets (canonData csets α β v (openMulti gs zs ((x ++ y).take M))) ((x ++ y).drop M))))) :=
          vsum_congr _ (fun x hx => vsum_congr _ (fun y _ => by rw [List.take_left' hx, List.drop_left' hx]))
  rw [key]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- **The transcript over the masked PCS with its quotients and their chunks**:
    `transcript_zkG` with the column openings and the quotient values of
    every height as the PCS's view, which `pcsCloseN_chunks` simulates
    exactly; no PCS term remains. -/
theorem transcript_zkG_chunks {PB : Type} {off : EF → String → EF} {M m : Nat}
    {bus : Nat → String} {sg : Nat → Bool} {par : Nat → Nat} (hpar : ∀ k, par (k + 1) ≤ k)
    {tabs : (Nat → Tup) → List (AirD × Table)}
    {tv : (String → EF) → EF → (Nat → Tup) → List EF} {tp : (String → EF) → EF → EF}
    {pb : (String → EF) → EF → PB} {xu : (String → EF) → EF → Nat → EF}
    (hchain : ∀ pre β t, tv pre β t = viewT β (fun k => pre (bus k)) sg par (m + 1) (xu pre β) t)
    (hsum : ∀ pre β, sumL (xu pre β) (List.range (m + 1)) = EF.zero.sub (tp pre β))
    (hM : ∀ t, (allEntries (tabs t)).length ≤ M)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {csets : List CSet} {qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F)}
    (hcs : ∀ c ∈ csets, c.OK)
    (hrec : ∀ t α β ms, RecOK csets (qd t α β ms)
      (fun c => c.JS α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms)))
    (E : TViewN (List (List (List F × List EF) × List (List EF)) × List (List (List F × List EF))) PB → Bool) :
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) m (fun α β r t =>
        indB (genB β && E (realVN off tabs tv pb (pcsChunk off tv qs ks cols csets qd) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) m (fun α β r t =>
        indB (genB β && E (simVN off pb bus sg par (m + 1) tp (psimChunk qs ks csets) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * 0)) ∧
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) m (fun α β r t =>
        indB (genB β && E (simVN off pb bus sg par (m + 1) tp (psimChunk qs ks csets) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) m (fun α β r t =>
        indB (genB β && E (realVN off tabs tv pb (pcsChunk off tv qs ks cols csets qd) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * 0)) :=
  transcript_zkG hpar hchain hsum hM (pcsCloseN_chunks hok hks hcols hcs off tv hrec) E

/-- `comp_transcriptG` over the masked PCS with its quotients and their chunks (`pcsCloseN_chunks`): no PCS term. -/
theorem comp_transcriptG_chunks (off : EF → String → EF)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat} {C Mm Wt : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt (segsPub roots)))
    (h : Unblinded WT_BLIND C Mm Wt)
    {csets : List CSet} {qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F)}
    (hcs : ∀ c ∈ csets, c.OK)
    (hrec : ∀ t α β ms, RecOK csets (qd t α β ms)
      (fun c => c.JS α β ((fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β ((fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms)))
    (E : TViewN (List (List (List F × List EF) × List (List EF)) × List (List (List F × List EF))) (EF × EF) → Bool) :
    let tabs := fun t : Nat → Tup => compTables hd0 stk0 ctr0 n nilA heap N W roots
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableC heap N W)
      (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
    let tv := fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t
    let pb := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W),
      terminal pre β (segsAir roots) (segsPub roots))
    let tp := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))
    let M := (allEntries (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm (progTableC heap N W) Wt
      (segsPub roots))).length
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsChunk off (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) qs ks cols csets qd) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 tp (psimChunk qs ks csets) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 tp (psimChunk qs ks csets) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsChunk off (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) qs ks cols csets qd) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) :=
  comp_transcriptG off (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 0 (pcsChunk off (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) qs ks cols csets qd) (psimChunk qs ks csets) hb h
    (pcsCloseN_chunks hok hks hcols hcs off (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t) hrec) E

/-- `sud_transcriptG` over the masked PCS with its quotients and their chunks (`pcsCloseN_chunks`): no PCS term. -/
theorem sud_transcriptG_chunks (off : EF → String → EF)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Wt : Table}
    (hb : Balanced (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)) (h : Unblinded 1 C Mm Wt)
    {csets : List CSet} {qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F)}
    (hcs : ∀ c ∈ csets, c.OK)
    (hrec : ∀ t α β ms, RecOK csets (qd t α β ms)
      (fun c => c.JS α β ((fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β ((fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms)))
    (E : TViewN (List (List (List F × List EF) × List (List EF)) × List (List (List F × List EF))) EF → Bool) :
    let tabs := fun t : Nat → Tup => sudTables hd0 stk0 ctr0 heap ((C.setBlind BLA (t 1)).setBlind BLB (t 0))
      (Mm.setBlind 5 (t 0)) (progTableS heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS heap) (progTableS heap)
    let M := (allEntries (sudTables hd0 stk0 ctr0 heap C Mm (progTableS heap) Wt)).length
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsChunk off (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) qs ks cols csets qd) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimChunk qs ks csets) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimChunk qs ks csets) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsChunk off (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) qs ks cols csets qd) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) :=
  sud_transcriptG off (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 0 (pcsChunk off (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) qs ks cols csets qd) (psimChunk qs ks csets) hb h
    (pcsCloseN_chunks hok hks hcols hcs off (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t) hrec) E

/-- `wit_transcriptG` over the masked PCS with its quotients and their chunks (`pcsCloseN_chunks`): no PCS term. -/
theorem wit_transcriptG_chunks (off : EF → String → EF)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat} {C Mm Wt : Table}
    (hb : Balanced (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)) (h : Unblinded WT_BLIND C Mm Wt)
    {csets : List CSet} {qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F)}
    (hcs : ∀ c ∈ csets, c.OK)
    (hrec : ∀ t α β ms, RecOK csets (qd t α β ms)
      (fun c => c.JS α β ((fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β ((fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms)))
    (E : TViewN (List (List (List F × List EF) × List (List EF)) × List (List (List F × List EF))) EF → Bool) :
    let tabs := fun t : Nat → Tup => witTables hd0 stk0 ctr0 heap W ((C.setBlind BLA (t 1)).setBlind BLB (t 0))
      (Mm.setBlind 5 (t 0)) (progTableW heap W) (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirW heap W) (progTableW heap W)
    let M := (allEntries (witTables hd0 stk0 ctr0 heap W C Mm (progTableW heap W) Wt)).length
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsChunk off (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) qs ks cols csets qd) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimChunk qs ks csets) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimChunk qs ks csets) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp (pcsChunk off (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) qs ks cols csets qd) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) :=
  wit_transcriptG off (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 0 (pcsChunk off (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) qs ks cols csets qd) (psimChunk qs ks csets) hb h
    (pcsCloseN_chunks hok hks hcols hcs off (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) hrec) E

/-- `compJ_transcriptG` over the masked PCS with its quotients and their chunks (`pcsCloseN_chunks`): no PCS term. -/
theorem compJ_transcriptG_chunks (off : EF → String → EF)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {segRoots : List Nat}
    {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Wt Rt Hd Tm Po Iw : Table}
    (hb : Balanced (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm (progTableC heap N W) Wt
      (segsPub segRoots) Rt Hd Tm Po Iw))
    (h : UnblindedCJ roots jets C Mm Wt Rt Hd Tm Po Iw)
    {csets : List CSet} {qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F)}
    (hcs : ∀ c ∈ csets, c.OK)
    (hrec : ∀ t α β ms, RecOK csets (qd t α β ms)
      (fun c => c.JS α β ((fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β ((fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms)))
    (E : TViewN (List (List (List F × List EF) × List (List EF)) × List (List (List F × List EF))) (EF × EF) → Bool) :
    let tabs := fun t : Nat → Tup => compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets
      (((C.setBlind BLAJ (t 1)).setBlind BLBJ (t 0)).setBlind BLCJ (t 2)) (Mm.setBlind 5 (t 0))
      (progTableC heap N W) (Wt.setBlind WT_BLIND (t 1)) (segsPub segRoots) (Rt.setBlind 1 (t 6))
      ((Hd.setBlind 1 (t 5)).setBlind 6 (t 6)) ((Tm.setBlind 1 (t 4)).setBlind 6 (t 5))
      ((Po.setBlind popAir.width (t 2)).setBlind (popAir.width + 5) (t 3))
      ((Iw.setBlind instwAir.width (t 3)).setBlind (instwAir.width + 5) (t 4))
    let tv := fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t
    let pb := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W),
      terminal pre β (segsAir segRoots) (segsPub segRoots))
    let tp := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W)).add
      (terminal pre β (segsAir segRoots) (segsPub segRoots))
    let M := (allEntries (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm (progTableC heap N W)
      Wt (segsPub segRoots) Rt Hd Tm Po Iw)).length
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 7 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsChunk off (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t) qs ks cols csets qd) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 7 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 8 tp (psimChunk qs ks csets) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * 0)) ∧
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 7 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 8 tp (psimChunk qs ks csets) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 7 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsChunk off (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t) qs ks cols csets qd) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * 0)) :=
  compJ_transcriptG off (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 0 (pcsChunk off (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t) qs ks cols csets qd) (psimChunk qs ks csets) hb h
    (pcsCloseN_chunks hok hks hcols hcs off (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t) hrec) E

/-- `compP_transcriptG` over the masked PCS with its quotients and their chunks (`pcsCloseN_chunks`): no PCS term. -/
theorem compP_transcriptG_chunks (off : EF → String → EF) (calls : Nat)
    {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
    {C Mm Wt Pi Po Pp : Table}
    (hb : Balanced (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm (progTableC heap N W) Wt
      (segsPub roots) Pi Po Pp (idxPub calls)))
    (h : UnblindedCP C Mm Wt Pi Po Pp)
    {csets : List CSet} {qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F)}
    (hcs : ∀ c ∈ csets, c.OK)
    (hrec : ∀ t α β ms, RecOK csets (qd t α β ms)
      (fun c => c.JS α β ((fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β ((fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t) (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms)))
    (E : TViewN (List (List (List F × List EF) × List (List EF)) × List (List (List F × List EF))) ((EF × EF) × EF) → Bool) :
    let tabs := fun t : Nat → Tup => compPTables hd0 stk0 ctr0 n nilA J root heap N W roots
      (((C.setBlind BLA (t 1)).setBlind BLB (t 0)).setBlind (P2SEL + 1) (t 2)) (Mm.setBlind 5 (t 0))
      (progTableC heap N W) (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
      ((Pi.setBlind p2inAir.width (t 2)).setBlind (p2inAir.width + 5) (t 3))
      ((Po.setBlind p2outAir.width (t 3)).setBlind (p2outAir.width + 5) (t 4))
      (Pp.setBlind P2Air.p2Air.width (t 4)) (idxPub calls)
    let tv := fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t
    let pb := fun pre β => ((terminal pre β (progAirC heap N W) (progTableC heap N W),
      terminal pre β (segsAir roots) (segsPub roots)), terminal pre β p2idxAir (idxPub calls))
    let tp := fun pre β => ((terminal pre β (progAirC heap N W) (progTableC heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))).add (terminal pre β p2idxAir (idxPub calls))
    let M := (allEntries (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm (progTableC heap N W)
      Wt (segsPub roots) Pi Po Pp (idxPub calls))).length
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 5 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsChunk off (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t) qs ks cols csets qd) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 5 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 6 tp (psimChunk qs ks csets) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * 0)) ∧
    tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 5 (fun α β r t => indB (genB β && E (simVN off pb jetBus jetSg jetPar 6 tp (psimChunk qs ks csets) α β r t))) ≤
      tsumN (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 5 (fun α β r t => indB (genB β && E (realVN off tabs tv pb (pcsChunk off (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t) qs ks cols csets qd) α β r t))) +
        Q4 * (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * (Q4 ^ 5 * M)) + Q4 * (Q4 * (Q4 ^ 5 * 0)) :=
  compP_transcriptG off (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets)) 0 calls (pcsChunk off (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t) qs ks cols csets qd) (psimChunk qs ks csets) hb h
    (pcsCloseN_chunks hok hks hcols hcs off (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t) hrec) E

end Circuit
