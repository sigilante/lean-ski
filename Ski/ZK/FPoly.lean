import Ski.ZK.Poly

/-!
# Polynomials over the base field: interpolation and uniqueness

A polynomial over `F` as its coefficient list, lowest first (`fval`).
Through distinct points with any values there is a polynomial of at most
as many coefficients (`finterp`, Newton's form: each point adds a multiple
of the product of `x - x_j` over the points before it), and two
polynomials of at most `N` coefficients agreeing at `N` distinct points
agree everywhere (`fagree`, by the root bound `froots_lt`).
-/

namespace Circuit

open ZKF

/-- A polynomial's value at `x`, its coefficients lowest first. -/
def fval (x : F) : List F → F
  | [] => 0
  | c :: cs => c + x * fval x cs

/-- Every coefficient is zero. -/
def FZero (cs : List F) : Prop := ∀ c ∈ cs, c = 0

instance (cs : List F) : Decidable (FZero cs) := inferInstanceAs (Decidable (∀ c ∈ cs, c = 0))

theorem fval_fzero (x : F) : ∀ cs : List F, FZero cs → fval x cs = 0
  | [], _ => rfl
  | c :: cs, h => by
    show c + x * fval x cs = 0
    rw [h c List.mem_cons_self, fval_fzero x cs (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')), mul_zero',
      zero_add']

/-- The quotient of synthetic division by `x - a`. -/
def fdivq (a : F) : List F → List F
  | [] => []
  | [_] => []
  | _ :: d :: cs => fval a (d :: cs) :: fdivq a (d :: cs)

theorem fdivq_length (a : F) : ∀ cs : List F, (fdivq a cs).length = cs.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: d :: cs => by
    show (fdivq a (d :: cs)).length + 1 = (d :: cs).length + 1 - 1
    rw [fdivq_length a (d :: cs)]
    simp only [List.length_cons]
    omega

/-- **Synthetic division**: `p(x) = (x - a) q(x) + p(a)`. -/
theorem fval_fdivq (x a : F) : ∀ cs : List F, fval x cs = (x - a) * fval x (fdivq a cs) + fval a cs
  | [] => by show (0 : F) = (x - a) * 0 + 0; rw [mul_zero', add_zero']
  | [c] => by
    show c + x * 0 = (x - a) * 0 + (c + a * 0)
    exact fid (e := v 0 + v 1 * k 0) (e' := (v 1 - v 2) * k 0 + (v 0 + v 2 * k 0)) (by decide) [c, x, a]
  | c :: d :: cs => by
    show c + x * fval x (d :: cs) = (x - a) * (fval a (d :: cs) + x * fval x (fdivq a (d :: cs))) +
      (c + a * fval a (d :: cs))
    rw [fval_fdivq x a (d :: cs)]
    exact fid (e := v 2 + v 0 * ((v 0 - v 1) * v 4 + v 3)) (e' := (v 0 - v 1) * (v 3 + v 0 * v 4) + (v 2 + v 1 * v 3))
      (by decide) [x, a, c, fval a (d :: cs), fval x (fdivq a (d :: cs))]

theorem fzero_of_fdivq (a : F) : ∀ cs : List F, fval a cs = 0 → FZero (fdivq a cs) → FZero cs
  | [], _, _ => fun _ h => nomatch h
  | [c], h, _ => by
    have : c + a * 0 = 0 := h
    rw [mul_zero', add_zero'] at this
    intro c' hc'
    rw [List.mem_singleton.1 hc', this]
  | c :: d :: cs, h, hq => by
    have hq0 : fval a (d :: cs) = 0 := hq _ List.mem_cons_self
    have hrest : FZero (d :: cs) := fzero_of_fdivq a (d :: cs) hq0 (fun c' hc' => hq c' (List.mem_cons_of_mem _ hc'))
    have hc : c + a * fval a (d :: cs) = 0 := h
    rw [hq0, mul_zero', add_zero'] at hc
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hc
    · exact hrest c' hc'

theorem fsub_ne_zero {x y : F} (h : x ≠ y) : x - y ≠ 0 := fun e => h (sub_eq_zero e)

/-- **The root bound** over `F`. -/
theorem froots_lt : ∀ (n : Nat) (cs : List F), cs.length ≤ n → ¬ FZero cs →
    ∀ pts : List F, pts.Nodup → (∀ x ∈ pts, fval x cs = 0) → pts.length < cs.length
  | n, cs, _, hz, [], _, _ => by
    rcases cs with _ | ⟨c, cs⟩
    · exact absurd (fun _ h => nomatch h) hz
    · exact Nat.succ_pos _
  | 0, cs, hl, hz, _ :: _, _, _ => by
    rcases cs with _ | ⟨c, cs⟩
    · exact absurd (fun _ h => nomatch h) hz
    · simp only [List.length_cons] at hl; omega
  | n + 1, cs, hl, hz, a :: rest, hnd, hr => by
    have ha : fval a cs = 0 := hr a List.mem_cons_self
    have hqz : ¬ FZero (fdivq a cs) := fun h => hz (fzero_of_fdivq a cs ha h)
    have hql : (fdivq a cs).length = cs.length - 1 := fdivq_length a cs
    have hrest : ∀ x ∈ rest, fval x (fdivq a cs) = 0 := by
      intro x hx
      have hxa : x ≠ a := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hx)
      have e := fval_fdivq x a cs
      rw [hr x (List.mem_cons_of_mem _ hx), ha, add_zero'] at e
      exact (mul_eq_zero e.symm).resolve_left (fsub_ne_zero hxa)
    have ih := froots_lt n (fdivq a cs) (by omega) hqz rest (List.nodup_cons.1 hnd).2 hrest
    have hpos : 0 < cs.length := by
      rcases cs with _ | ⟨c, cs⟩
      · exact absurd (fun _ h => nomatch h) hz
      · exact Nat.succ_pos _
    simp only [List.length_cons]
    omega

-- ---------------------------------------------------------------------------
-- Building polynomials
-- ---------------------------------------------------------------------------

def fcadd : List F → List F → List F
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: fcadd p q

theorem fval_fcadd (x : F) : ∀ p q : List F, fval x (fcadd p q) = fval x p + fval x q
  | [], q => by show fval x q = 0 + fval x q; rw [zero_add']
  | a :: p, [] => by show fval x (a :: p) = fval x (a :: p) + 0; rw [add_zero']
  | a :: p, b :: q => by
    show (a + b) + x * fval x (fcadd p q) = (a + x * fval x p) + (b + x * fval x q)
    rw [fval_fcadd x p q]
    exact fid (e := (v 0 + v 1) + v 2 * (v 3 + v 4)) (e' := (v 0 + v 2 * v 3) + (v 1 + v 2 * v 4))
      (by decide) [a, b, x, fval x p, fval x q]

theorem fcadd_length : ∀ p q : List F, (fcadd p q).length ≤ max p.length q.length
  | [], q => by simp [fcadd]
  | a :: p, [] => by simp [fcadd]
  | a :: p, b :: q => by
    show (fcadd p q).length + 1 ≤ max (p.length + 1) (q.length + 1)
    have := fcadd_length p q
    omega

def fcscale (c : F) (p : List F) : List F := p.map (c * ·)

theorem fval_fcscale (x c : F) : ∀ p : List F, fval x (fcscale c p) = c * fval x p
  | [] => by show (0 : F) = c * 0; rw [mul_zero']
  | a :: p => by
    show c * a + x * fval x (fcscale c p) = c * (a + x * fval x p)
    rw [fval_fcscale x c p]
    exact fid (e := v 0 * v 1 + v 2 * (v 0 * v 3)) (e' := v 0 * (v 1 + v 2 * v 3)) (by decide) [c, a, x, fval x p]

theorem fcscale_length (c : F) (p : List F) : (fcscale c p).length = p.length := List.length_map _

/-- The product with `x - a`. -/
def fclin (a : F) (p : List F) : List F := fcadd (0 :: p) (fcscale (-a) p)

theorem fval_fclin (x a : F) (p : List F) : fval x (fclin a p) = (x - a) * fval x p := by
  unfold fclin
  rw [fval_fcadd, fval_fcscale]
  show (0 + x * fval x p) + -a * fval x p = (x - a) * fval x p
  exact fid (e := (k 0 + v 0 * v 2) + (-(v 1)) * v 2) (e' := (v 0 - v 1) * v 2) (by decide) [x, a, fval x p]

theorem fclin_length (a : F) (p : List F) : (fclin a p).length ≤ p.length + 1 := by
  unfold fclin
  have := fcadd_length (0 :: p) (fcscale (-a) p)
  rw [fcscale_length] at this
  simp only [List.length_cons] at this
  omega

/-- `∏ (x - x_j)`. -/
def fvan : List F → List F
  | [] => [1]
  | x :: r => fclin x (fvan r)

theorem fvan_length : ∀ xs : List F, (fvan xs).length ≤ xs.length + 1
  | [] => Nat.le_refl 1
  | x :: r => by
    have := fclin_length x (fvan r)
    have := fvan_length r
    show (fclin x (fvan r)).length ≤ r.length + 1 + 1
    omega

theorem fval_one (x : F) : fval x [1] = 1 := by show 1 + x * 0 = 1; rw [mul_zero', add_zero']

theorem fvan_root (y : F) : ∀ xs : List F, y ∈ xs → fval y (fvan xs) = 0
  | [], h => nomatch h
  | x :: r, h => by
    show fval y (fclin x (fvan r)) = 0
    rw [fval_fclin]
    rcases List.mem_cons.1 h with rfl | h
    · rw [show y - y = 0 from sub_self' y, zero_mul']
    · rw [fvan_root y r h, mul_zero']

theorem fvan_ne (y : F) : ∀ xs : List F, y ∉ xs → fval y (fvan xs) ≠ 0
  | [], _ => by rw [show fvan [] = [1] from rfl, fval_one]; decide
  | x :: r, h => by
    show fval y (fclin x (fvan r)) ≠ 0
    rw [fval_fclin]
    intro e
    rcases mul_eq_zero e with e | e
    · exact h (List.mem_cons.2 (.inl (sub_eq_zero e)))
    · exact fvan_ne y r (fun h' => h (List.mem_cons_of_mem _ h')) e

-- ---------------------------------------------------------------------------
-- Interpolation
-- ---------------------------------------------------------------------------

/-- **Newton's interpolation**: through each point, its value. -/
def finterp : List (F × F) → List F
  | [] => []
  | (x, y) :: r =>
    fcadd (finterp r) (fcscale ((y - fval x (finterp r)) * finv (fval x (fvan (r.map Prod.fst))))
      (fvan (r.map Prod.fst)))

theorem finterp_length : ∀ pts : List (F × F), (finterp pts).length ≤ pts.length
  | [] => Nat.le_refl 0
  | (x, y) :: r => by
    have h1 := fcadd_length (finterp r) (fcscale ((y - fval x (finterp r)) * finv (fval x (fvan (r.map Prod.fst))))
      (fvan (r.map Prod.fst)))
    rw [fcscale_length] at h1
    have h2 := finterp_length r
    have h3 := fvan_length (r.map Prod.fst)
    rw [List.length_map] at h3
    show (fcadd _ _).length ≤ r.length + 1
    omega

/-- **The interpolant takes each value**, the points distinct. -/
theorem finterp_eval : ∀ pts : List (F × F), (pts.map Prod.fst).Nodup → ∀ p ∈ pts, fval p.1 (finterp pts) = p.2
  | [], _, _, h => nomatch h
  | (x, y) :: r, hnd, p, hp => by
    rw [List.map_cons, List.nodup_cons] at hnd
    show fval p.1 (fcadd (finterp r) (fcscale ((y - fval x (finterp r)) * finv (fval x (fvan (r.map Prod.fst))))
      (fvan (r.map Prod.fst)))) = p.2
    rw [fval_fcadd, fval_fcscale]
    rcases List.mem_cons.1 hp with rfl | hr
    · have hz := fvan_ne x (r.map Prod.fst) hnd.1
      show fval x (finterp r) + (y - fval x (finterp r)) * finv (fval x (fvan (r.map Prod.fst))) *
        fval x (fvan (r.map Prod.fst)) = y
      rw [mul_assoc', finv_mul hz, mul_one']
      exact fid (e := v 0 + (v 1 - v 0)) (e' := v 1) (by decide) [fval x (finterp r), y]
    · rw [finterp_eval r hnd.2 p hr, fvan_root p.1 _ (List.mem_map.2 ⟨p, hr, rfl⟩), mul_zero', add_zero']

/-- `p - q` as coefficients. -/
def fcdiff (p q : List F) : List F := fcadd p (fcscale (-1) q)

theorem fval_fcdiff (x : F) (p q : List F) : fval x (fcdiff p q) = fval x p - fval x q := by
  unfold fcdiff
  rw [fval_fcadd, fval_fcscale]
  exact fid (e := v 0 + (-(k 1)) * v 1) (e' := v 0 - v 1) (by decide) [fval x p, fval x q]

/-- **Uniqueness, coefficientwise**: two polynomials of at most `N`
    coefficients agreeing at `N` distinct points differ by zero
    coefficients. -/
theorem fagree_zero {N : Nat} {p q : List F} (hp : p.length ≤ N) (hq : q.length ≤ N) (pts : List F)
    (hnd : pts.Nodup) (hl : pts.length = N) (h : ∀ x ∈ pts, fval x p = fval x q) : FZero (fcdiff p q) := by
  have hd : (fcdiff p q).length ≤ N := by
    unfold fcdiff
    have := fcadd_length p (fcscale (-1) q)
    rw [fcscale_length] at this
    omega
  rcases (inferInstance : Decidable (FZero (fcdiff p q))) with hz | hz
  · have := froots_lt N _ hd hz pts hnd (fun x hx => by rw [fval_fcdiff, h x hx, sub_self'])
    omega
  · exact hz

/-- **Uniqueness**: two polynomials of at most `N` coefficients agreeing at
    `N` distinct points agree everywhere. -/
theorem fagree {N : Nat} {p q : List F} (hp : p.length ≤ N) (hq : q.length ≤ N) (pts : List F) (hnd : pts.Nodup)
    (hl : pts.length = N) (h : ∀ x ∈ pts, fval x p = fval x q) (y : F) : fval y p = fval y q := by
  have := fval_fzero y _ (fagree_zero hp hq pts hnd hl h)
  rw [fval_fcdiff] at this
  exact sub_eq_zero this

end Circuit
