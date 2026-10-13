import Ski.ZK.MaskCis

/-!
# The honest quotient polynomial

`MaskRec` and `MaskCoset` reduce `RecOK` to two facts about the honest
quotient `Qp`: its degree, and its values at the opened points.  This
file builds `Qp` by polynomial division, proves its values, and bounds
its size (`|Qp| = |C| - |H|`, `|C| ≤ D m + 1`).  Plonky3 instead
interpolates `C / Z_H` on the quotient domain, which gives the same
polynomial when `|Qp|` fits that domain; `QuotOK`'s bound
`|Qp| ≤ (|cs| + 1) n` still needs `D m + 1 - |H| ≤ (|cs| + 1) n`.

An AIR constraint is an expression `e : E` over columns at row offsets
and selectors.  Over column polynomials it is a polynomial `e.fpoly ρ`:
a column at offset `o` is `p(gᵒ X)` (`fshift`), and a selector is the
polynomial Plonky3 evaluates.  Its value at any point is the expression
evaluated on the columns' values there (`fval_epoly`, `fvalE_epoly`).
So at a point `x` it reads the columns at `gᵒ x`: with offsets 0 and 1,
as Plonky3's two-row window has, at `x` and `g x`.  The verifier opens
the trace at `ζ` and `g ζ`; at a query point it opens only `x`, and
`g x` is in the hiding view (`MaskQuot`).

The folded constraint polynomial `C` vanishes on the trace domain `H`
for an honest trace.  Dividing by `∏_{a ∈ H} (X - a)` root by root
(`fdivH`) gives `Qp` with `Qp · Z_H = C` (`fdivH_rel`), with `|C| - |H|`
coefficients (`fdivH_length`).  With constraints of degree at most `D`
over columns of at most `m + 1` coefficients, `|C| ≤ D m + 1`
(`cpoly_length`).

`air_quot` gathers these facts.  The quotient's targets are `airTg` and
`airTgE`, which read the leaves' values at each point, the public
domain data, and `|qs|` (through `allL`).
With the standard leaves (`stdRho`), those values are the openings at
`gᵒ x` (`fval_stdRho`).  `shows_air` is the endpoint: honest chunks of
an AIR's quotient show the AIR's targets.

Scope.
- **Folding.** The fold is per base-field coordinate `k`.  A base
  constraint's weight is coordinate `k` of its power of `α`; the base
  coordinate `c_m` of an extension constraint takes coordinate `k` of
  `αʲ Xᵐ`.  `Ski/ZK/QuotFold.lean` folds the coordinates back
  (`airTgE_back`).
- **Leaves.** `E` has no periodic columns and no extension-valued
  leaves; an extension column enters as its four base columns, and an
  extension constraint as its coordinates (`Ski/ZK/QuotFold.lean`).
  Public values and challenges enter only as constants.
- **Selectors.** They are given polynomials.  Plonky3 evaluates them
  through `Z_H(x) = xⁿ - 1`; `Ski/ZK/VanishPow.lean` proves that formula
  equals `∏_{a ∈ H} (x - a)` and gives the first- and last-row
  selectors as products.
- **Vanishing.** `hvan`, every constraint vanishing on `H` under
  Plonky3's selectors, is a hypothesis here; `Ski/ZK/QuotSat.lean`
  derives it from the circuit's `Sat` (`hvan_of_sat`).
- **Targets.** No circuit's `CSet` targets `JS`, `Jζ` are yet tied to
  `airTg`, `airTgE`.
-/

namespace Circuit

open ZKF

-- ---------------------------------------------------------------------------
-- A column at a row offset: `p(c X)`
-- ---------------------------------------------------------------------------

/-- `p(c X)`: coefficient `i` scaled by `cⁱ`. -/
def fshift (c : F) : List F → List F
  | [] => []
  | a :: p => a :: fcscale c (fshift c p)

theorem fval_fshift (x c : F) : ∀ p : List F, fval x (fshift c p) = fval (c * x) p
  | [] => rfl
  | a :: p => by
    show a + x * fval x (fcscale c (fshift c p)) = a + c * x * fval (c * x) p
    rw [fval_fcscale, fval_fshift x c p, ← mul_assoc', mul_comm' x c]

theorem fvalE_fshift (z : EF) (c : F) : ∀ p : List F, fvalE z (fshift c p) = fvalE ((EF.ofF c).mul z) p
  | [] => rfl
  | a :: p => by
    show fvalE z (a :: fcscale c (fshift c p)) = _
    rw [fvalE_cons, fvalE_cons, fvalE_fcscale, fvalE_fshift z c p, ← EF.mul_assoc, EF.mul_comm z]

theorem fshift_length (c : F) : ∀ p : List F, (fshift c p).length = p.length
  | [] => rfl
  | _ :: p => by
    show (fcscale c (fshift c p)).length + 1 = p.length + 1
    rw [fcscale_length, fshift_length c p]

-- ---------------------------------------------------------------------------
-- An expression over polynomials
-- ---------------------------------------------------------------------------

/-- **An expression as a polynomial**, its leaves the polynomials `ρ`. -/
def E.fpoly (ρ : Atom → List F) : E → List F
  | .atom a => ρ a
  | .const c => [c]
  | .add a b => fcadd (a.fpoly ρ) (b.fpoly ρ)
  | .sub a b => fcdiff (a.fpoly ρ) (b.fpoly ρ)
  | .mul a b => fmul (a.fpoly ρ) (b.fpoly ρ)
  | .neg a => fcscale (-1) (a.fpoly ρ)

/-- An expression's meaning over the extension. -/
def E.evalE (ρ : Atom → EF) : E → EF
  | .atom a => ρ a
  | .const c => EF.ofF c
  | .add a b => (a.evalE ρ).add (b.evalE ρ)
  | .sub a b => (a.evalE ρ).sub (b.evalE ρ)
  | .mul a b => (a.evalE ρ).mul (b.evalE ρ)
  | .neg a => (EF.ofF (-1)).mul (a.evalE ρ)

theorem fval_single (x c : F) : fval x [c] = c := by show c + x * 0 = c; rw [mul_zero', add_zero']

theorem fvalE_single (z : EF) (c : F) : fvalE z [c] = EF.ofF c := by
  show (EF.ofF c).add (z.mul EF.zero) = _; rw [EF.mul_zero, EF.add_zero]

/-- **The polynomial's value is the expression's** on the leaves' values. -/
theorem fval_epoly (x : F) (ρ : Atom → List F) : ∀ e : E, fval x (e.fpoly ρ) = e.eval (fun a => fval x (ρ a))
  | .atom _ => rfl
  | .const c => fval_single x c
  | .add a b => by
    show fval x (fcadd _ _) = _ + _; rw [fval_fcadd, fval_epoly x ρ a, fval_epoly x ρ b]
  | .sub a b => by
    show fval x (fcdiff _ _) = _ - _; rw [fval_fcdiff, fval_epoly x ρ a, fval_epoly x ρ b]
  | .mul a b => by
    show fval x (fmul _ _) = _ * _; rw [fval_fmul, fval_epoly x ρ a, fval_epoly x ρ b]
  | .neg a => by
    show fval x (fcscale _ _) = -_; rw [fval_fcscale, fval_epoly x ρ a, ← neg_eq_neg_one_mul]

theorem fvalE_epoly (z : EF) (ρ : Atom → List F) : ∀ e : E, fvalE z (e.fpoly ρ) = e.evalE (fun a => fvalE z (ρ a))
  | .atom _ => rfl
  | .const c => fvalE_single z c
  | .add a b => by
    show fvalE z (fcadd _ _) = EF.add _ _; rw [fvalE_fcadd, fvalE_epoly z ρ a, fvalE_epoly z ρ b]
  | .sub a b => by
    show fvalE z (fcdiff _ _) = EF.sub _ _; rw [fvalE_fcdiff, fvalE_epoly z ρ a, fvalE_epoly z ρ b]
  | .mul a b => by
    show fvalE z (fmul _ _) = EF.mul _ _; rw [fvalE_fmul, fvalE_epoly z ρ a, fvalE_epoly z ρ b]
  | .neg a => by
    show fvalE z (fcscale _ _) = EF.mul _ _; rw [fvalE_fcscale, fvalE_epoly z ρ a]

/-- An expression's degree, its leaves of degree one. -/
def E.deg : E → Nat
  | .atom _ => 1
  | .const _ => 0
  | .add a b => max a.deg b.deg
  | .sub a b => max a.deg b.deg
  | .mul a b => a.deg + b.deg
  | .neg a => a.deg

theorem fmul_len_le : ∀ p q : List F, (fmul p q).length ≤ p.length + q.length
  | [], _ => Nat.zero_le _
  | a :: p, q => by
    have h1 := fcadd_length (fcscale a q) (0 :: fmul p q)
    have h2 := fmul_len_le p q
    rw [fcscale_length] at h1
    show (fcadd _ _).length ≤ p.length + 1 + q.length
    simp only [List.length_cons] at h1
    omega

/-- **The polynomial's size**: at most `deg · m + 1` coefficients when every
    leaf has at most `m + 1`. -/
theorem epoly_length (ρ : Atom → List F) (m : Nat) (hρ : ∀ a, (ρ a).length ≤ m + 1) :
    ∀ e : E, (e.fpoly ρ).length ≤ e.deg * m + 1
  | .atom a => by show (ρ a).length ≤ 1 * m + 1; rw [Nat.one_mul]; exact hρ a
  | .const _ => by show 1 ≤ 0 * m + 1; omega
  | .add a b => by
    have := fcadd_length (a.fpoly ρ) (b.fpoly ρ)
    have ha := epoly_length ρ m hρ a; have hb := epoly_length ρ m hρ b
    show (fcadd _ _).length ≤ max a.deg b.deg * m + 1
    rw [Nat.max_def] at ⊢; rw [Nat.max_def] at this
    split <;> split at this <;> first
      | omega
      | (have := Nat.mul_le_mul_right m (Nat.le_of_lt (Nat.lt_of_not_le ‹_›)); omega)
      | (have := Nat.mul_le_mul_right m ‹a.deg ≤ b.deg›; omega)
  | .sub a b => by
    have := fcadd_length (a.fpoly ρ) (fcscale (-1) (b.fpoly ρ))
    rw [fcscale_length] at this
    have ha := epoly_length ρ m hρ a; have hb := epoly_length ρ m hρ b
    show (fcadd _ _).length ≤ max a.deg b.deg * m + 1
    rw [Nat.max_def] at ⊢; rw [Nat.max_def] at this
    split <;> split at this <;> first
      | omega
      | (have := Nat.mul_le_mul_right m (Nat.le_of_lt (Nat.lt_of_not_le ‹_›)); omega)
      | (have := Nat.mul_le_mul_right m ‹a.deg ≤ b.deg›; omega)
  | .mul a b => by
    have ha := epoly_length ρ m hρ a; have hb := epoly_length ρ m hρ b
    show (fmul _ _).length ≤ (a.deg + b.deg) * m + 1
    rw [Nat.add_mul]
    by_cases hq : b.fpoly ρ = []
    · have := fmul_len_le (a.fpoly ρ) (b.fpoly ρ)
      rw [hq, List.length_nil] at this; rw [hq]
      omega
    · have := fmul_length (a.fpoly ρ) (b.fpoly ρ) hq
      omega
  | .neg a => by
    show (fcscale _ _).length ≤ a.deg * m + 1; rw [fcscale_length]; exact epoly_length ρ m hρ a

-- ---------------------------------------------------------------------------
-- Division by the vanishing polynomial
-- ---------------------------------------------------------------------------

/-- **Division by `∏_{a ∈ H} (X - a)`**, one root at a time. -/
def fdivH : List F → List F → List F
  | [], C => C
  | a :: H, C => fdivH H (fdivq a C)

theorem fdivH_length : ∀ (H C : List F), (fdivH H C).length = C.length - H.length
  | [], C => (Nat.sub_zero _).symm
  | a :: H, C => by
    show (fdivH H (fdivq a C)).length = C.length - (H.length + 1)
    rw [fdivH_length H, fdivq_length]; omega

theorem fdivq_root {a b : F} {C : List F} (hab : b ≠ a) (hC : fval a C = 0) (hb : fval b C = 0) :
    fval b (fdivq a C) = 0 := by
  have := fval_fdivq b a C
  rw [hb, hC, add_zero'] at this
  rcases mul_eq_zero this.symm with e | e
  · exact absurd (sub_eq_zero e) hab
  · exact e

/-- **The quotient times the vanishing polynomial is `C`** at every point,
    when `C` vanishes on `H`, which has no repeats. -/
theorem fval_fdivH (x : F) : ∀ (H C : List F), H.Nodup → (∀ a ∈ H, fval a C = 0) →
    fval x C = fval x (fvan H) * fval x (fdivH H C)
  | [], C, _, _ => by rw [show fvan [] = [1] from rfl, fval_one, one_mul']; rfl
  | a :: H, C, hnd, hC => by
    have ha : fval a C = 0 := hC a List.mem_cons_self
    have hnd' := List.nodup_cons.1 hnd
    have ih := fval_fdivH x H (fdivq a C) hnd'.2 (fun b hb =>
      fdivq_root (fun e => hnd'.1 (e ▸ hb)) ha (hC b (List.mem_cons_of_mem _ hb)))
    show fval x C = fval x (fclin a (fvan H)) * fval x (fdivH H (fdivq a C))
    rw [fval_fdivq x a C, ha, add_zero', ih, fval_fclin, mul_assoc']

/-- `ofN 0, …, ofN (N - 1)`. -/
def ptsN : Nat → List F
  | 0 => []
  | n + 1 => ofN n :: ptsN n

theorem ptsN_length : ∀ n, (ptsN n).length = n
  | 0 => rfl
  | n + 1 => by show (ptsN n).length + 1 = n + 1; rw [ptsN_length]

theorem mem_ptsN {y : F} : ∀ {n}, y ∈ ptsN n → ∃ m, m < n ∧ y = ofN m
  | 0, h => nomatch h
  | n + 1, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨n, Nat.lt_succ_self n, rfl⟩
    · obtain ⟨m, hm, e⟩ := mem_ptsN h
      exact ⟨m, Nat.lt_succ_of_lt hm, e⟩

theorem ptsN_nodup : ∀ n, n ≤ P → (ptsN n).Nodup
  | 0, _ => List.nodup_nil
  | n + 1, hn => List.nodup_cons.2 ⟨fun h => by
      obtain ⟨m, hm, e⟩ := mem_ptsN h
      have := congrArg Fin.val e
      change n % P = m % P at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega, ptsN_nodup n (by omega)⟩

/-- **The quotient's defining identity**, as polynomials: `Qp · Z_H - C`
    has zero coefficients, when `C` vanishes on `H` and has at most `P`
    coefficients. -/
theorem fdivH_rel (H C : List F) (hnd : H.Nodup) (hC : ∀ a ∈ H, fval a C = 0) (hP : C.length ≤ P) :
    FZero (fcdiff (fmul (fdivH H C) (fvan H)) C) := by
  by_cases hH : C.length ≤ H.length
  · -- the quotient is empty, and `C` vanishes on more points than it has coefficients
    have hq : fdivH H C = [] := List.eq_nil_of_length_eq_zero (by rw [fdivH_length]; omega)
    have hz : FZero (fcdiff [] C) := fagree_zero (N := H.length) (Nat.zero_le _) hH H hnd rfl
      (fun x hx => by rw [hC x hx]; rfl)
    rw [hq]; exact hz
  · have hl : (fmul (fdivH H C) (fvan H)).length ≤ C.length := by
      have := fmul_length (fdivH H C) (fvan H) (fvan_ne_nil H)
      have := fvan_length H
      rw [fdivH_length] at *
      omega
    exact fagree_zero hl (Nat.le_refl _) (ptsN C.length) (ptsN_nodup _ hP) (ptsN_length _)
      (fun x _ => by rw [fval_fmul, mul_comm', ← fval_fdivH x H C hnd hC])

-- ---------------------------------------------------------------------------
-- The folded constraints
-- ---------------------------------------------------------------------------

/-- `Σ_i w_i p_i`. -/
def foldP : List F → List (List F) → List F
  | w :: ws, p :: ps => fcadd (fcscale w p) (foldP ws ps)
  | _, _ => []

/-- `Σ_i w_i v_i`, over `F` and over the extension. -/
def foldV : List F → List F → F
  | w :: ws, v :: vs => w * v + foldV ws vs
  | _, _ => 0

def foldVE : List F → List EF → EF
  | w :: ws, v :: vs => ((EF.ofF w).mul v).add (foldVE ws vs)
  | _, _ => EF.zero

theorem fval_foldP (x : F) : ∀ (ws : List F) (ps : List (List F)), fval x (foldP ws ps) = foldV ws (ps.map (fval x))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | w :: ws, p :: ps => by
    show fval x (fcadd _ _) = w * fval x p + foldV ws (ps.map (fval x))
    rw [fval_fcadd, fval_fcscale, fval_foldP x ws ps]

theorem fvalE_foldP (z : EF) : ∀ (ws : List F) (ps : List (List F)), fvalE z (foldP ws ps) = foldVE ws (ps.map (fvalE z))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | w :: ws, p :: ps => by
    show fvalE z (fcadd _ _) = ((EF.ofF w).mul (fvalE z p)).add (foldVE ws (ps.map (fvalE z)))
    rw [fvalE_fcadd, fvalE_fcscale, fvalE_foldP z ws ps]

theorem foldV_zero : ∀ (ws vs : List F), (∀ v ∈ vs, v = 0) → foldV ws vs = 0
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | w :: ws, v :: vs, h => by
    show w * v + foldV ws vs = 0
    rw [h v List.mem_cons_self, mul_zero', zero_add', foldV_zero ws vs (fun u hu => h u (List.mem_cons_of_mem _ hu))]

theorem foldP_length (N : Nat) : ∀ (ws : List F) (ps : List (List F)), (∀ p ∈ ps, p.length ≤ N) → (foldP ws ps).length ≤ N
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], _ => Nat.zero_le _
  | w :: ws, p :: ps, h => by
    have h1 := fcadd_length (fcscale w p) (foldP ws ps)
    have h2 := foldP_length N ws ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h3 := h p List.mem_cons_self
    rw [fcscale_length] at h1
    show (fcadd _ _).length ≤ N
    exact Nat.le_trans h1 (Nat.max_le.2 ⟨h3, h2⟩)

/-- **The folded constraint polynomial**: `Σ_i w_i e_i(ρ)`, the weights one
    coordinate of the folding challenge's powers. -/
def cpoly (ρ : Atom → List F) (ws : List F) (es : List E) : List F := foldP ws (es.map (·.fpoly ρ))

theorem fval_cpoly (x : F) (ρ : Atom → List F) (ws : List F) (es : List E) :
    fval x (cpoly ρ ws es) = foldV ws (es.map (·.eval (fun a => fval x (ρ a)))) := by
  unfold cpoly; rw [fval_foldP, List.map_map]
  exact congrArg _ (List.map_congr_left (fun e _ => fval_epoly x ρ e))

theorem fvalE_cpoly (z : EF) (ρ : Atom → List F) (ws : List F) (es : List E) :
    fvalE z (cpoly ρ ws es) = foldVE ws (es.map (·.evalE (fun a => fvalE z (ρ a)))) := by
  unfold cpoly; rw [fvalE_foldP, List.map_map]
  exact congrArg _ (List.map_congr_left (fun e _ => fvalE_epoly z ρ e))

theorem cpoly_length (ρ : Atom → List F) (m D : Nat) (hρ : ∀ a, (ρ a).length ≤ m + 1) (ws : List F) (es : List E)
    (hD : ∀ e ∈ es, e.deg ≤ D) : (cpoly ρ ws es).length ≤ D * m + 1 :=
  foldP_length _ ws _ (fun p hp => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
    exact Nat.le_trans (epoly_length ρ m hρ e) (Nat.succ_le_succ (Nat.mul_le_mul_right m (hD e he))))

-- ---------------------------------------------------------------------------
-- The targets from the openings
-- ---------------------------------------------------------------------------

/-- **The targets an AIR's quotient asks**, from the leaves' values `ρv x`
    at each point: the folded constraints over `Z_H`, and off every chunk
    domain over `Z_H κ ∏_j v_j` too.  They depend on the chunks only
    through the public domain data and `|qs|`. -/
def airTg (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F) (H ws : List F)
    (es : List E) (ρv : F → Atom → F) (x : F) : F :=
  if x ∈ Hl ∨ inSome x cs = true then foldV ws (es.map (·.eval (ρv x))) * finv (fval x (fvan H))
  else foldV ws (es.map (·.eval (ρv x))) * finv (fval x (fvan H) * (κ * fval x (rpoly.ppoly (allL cs Hl cl qs ql))))

def airTgE (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F) (H ws : List F)
    (es : List E) (ρE : Atom → EF) : EF :=
  (foldVE ws (es.map (·.evalE ρE))).mul
    ((fvalE ζ (fvan H)).mul ((EF.ofF κ).mul (fvalE ζ (rpoly.ppoly (allL cs Hl cl qs ql))))).inv

/-- **The honest quotient of an AIR**: when every constraint vanishes on
    the trace domain `H` over the column polynomials `ρ`, the quotient
    `Qp = fdivH H C` of the folded constraints `C` meets `Qp · Z_H = C`,
    has `|C| - |H|` coefficients, and its targets are `airTg` and
    `airTgE`: functions of the leaves' values at each point (with
    `stdRho`, the columns at `gᵒ x`), the domain data and `|qs|`. -/
theorem air_quot (ρ : Atom → List F) (ws : List F) (es : List E) (H : List F) (hnd : H.Nodup)
    (hvan : ∀ e ∈ es, ∀ x ∈ H, e.eval (fun a => fval x (ρ a)) = 0) (hP : (cpoly ρ ws es).length ≤ P) :
    FZero (fcdiff (fmul (fdivH H (cpoly ρ ws es)) (fvan H)) (cpoly ρ ws es)) ∧
    (fdivH H (cpoly ρ ws es)).length = (cpoly ρ ws es).length - H.length ∧
    (∀ (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ x : F), fval x (fvan H) ≠ 0 →
      qtg cs Hl cl qs ql κ (fdivH H (cpoly ρ ws es)) x = airTg cs Hl cl qs ql κ H ws es (fun x a => fval x (ρ a)) x) ∧
    (∀ (ζ : EF) (cs : List Chunk) (Hl : List F) (cl : F) (qs : List (List F)) (ql : List F) (κ : F),
      fvalE ζ (fvan H) ≠ EF.zero →
      qtgE ζ cs Hl cl qs ql κ (fdivH H (cpoly ρ ws es)) = airTgE ζ cs Hl cl qs ql κ H ws es (fun a => fvalE ζ (ρ a))) := by
  have hC : ∀ a ∈ H, fval a (cpoly ρ ws es) = 0 := fun a ha => by
    rw [fval_cpoly]
    refine foldV_zero ws _ (fun v hv => ?_)
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
    exact hvan e he a ha
  have hrel := fdivH_rel H _ hnd hC hP
  refine ⟨hrel, fdivH_length H _, fun cs Hl cl qs ql κ x hz => ?_, fun ζ cs Hl cl qs ql κ hz => ?_⟩
  · rw [qtg_ctg hrel x hz]
    unfold ctg airTg
    rw [fval_cpoly]
  · rw [qtgE_ctgE hrel hz]
    unfold ctgE airTgE
    rw [fvalE_cpoly]

-- ---------------------------------------------------------------------------
-- The leaves: columns at row offsets, and the selectors
-- ---------------------------------------------------------------------------

/-- **The leaves' polynomials**: main and preprocessed column `i` at row
    offset `o` is its polynomial at `gᵒ X`; the selectors are given. -/
def stdRho (g : F) (main pre : Nat → List F) (sf sl st : List F) : Atom → List F
  | .main o i => fshift (fpow g o) (main i)
  | .pre o i => fshift (fpow g o) (pre i)
  | .first => sf
  | .last => sl
  | .trans => st

/-- **A leaf's value is an opening**: column `i` at offset `o`, at `x`,
    is the column's value at `gᵒ x`. -/
theorem fval_stdRho (x g : F) (main pre : Nat → List F) (sf sl st : List F) (o i : Nat) :
    fval x (stdRho g main pre sf sl st (.main o i)) = fval (fpow g o * x) (main i) ∧
    fval x (stdRho g main pre sf sl st (.pre o i)) = fval (fpow g o * x) (pre i) :=
  ⟨fval_fshift x _ _, fval_fshift x _ _⟩

theorem fvalE_stdRho (z : EF) (g : F) (main pre : Nat → List F) (sf sl st : List F) (o i : Nat) :
    fvalE z (stdRho g main pre sf sl st (.main o i)) = fvalE ((EF.ofF (fpow g o)).mul z) (main i) ∧
    fvalE z (stdRho g main pre sf sl st (.pre o i)) = fvalE ((EF.ofF (fpow g o)).mul z) (pre i) :=
  ⟨fvalE_fshift z _ _, fvalE_fshift z _ _⟩

theorem stdRho_length (g : F) (main pre : Nat → List F) (sf sl st : List F) (m : Nat)
    (hm : ∀ i, (main i).length ≤ m + 1) (hp : ∀ i, (pre i).length ≤ m + 1)
    (hs : sf.length ≤ m + 1 ∧ sl.length ≤ m + 1 ∧ st.length ≤ m + 1) :
    ∀ a, (stdRho g main pre sf sl st a).length ≤ m + 1
  | .main o i => by show (fshift _ _).length ≤ _; rw [fshift_length]; exact hm i
  | .pre o i => by show (fshift _ _).length ≤ _; rw [fshift_length]; exact hp i
  | .first => hs.1
  | .last => hs.2.1
  | .trans => hs.2.2

-- ---------------------------------------------------------------------------
-- The endpoint: honest chunks of an AIR's quotient show its targets
-- ---------------------------------------------------------------------------

/-- **Honest chunks of an AIR's quotient show the AIR's targets**: with
    `Qp` the honest quotient (`air_quot`) and `QuotOK` for its chunks, the
    chunks show `airTg` on the query points and `airTgE` at `ζ`, both
    computed from the leaves' values there, when `Z_H` vanishes at none of
    them. -/
theorem shows_air {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) {cs : List Chunk} {Hl : List F} {cl : F}
    {qs : List (List F)} {ql : List F} {κ : F} (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0)
    (ρ : Atom → List F) (ws : List F) (es : List E) (H : List F) (hnd : H.Nodup)
    (hvan : ∀ e ∈ es, ∀ x ∈ H, e.eval (fun a => fval x (ρ a)) = 0) (hP : (cpoly ρ ws es).length ≤ P)
    (hS : ∀ x ∈ S, fval x (fvan H) ≠ 0) (hZ : fvalE ζ (fvan H) ≠ EF.zero)
    (hq : QuotOK cs Hl cl qs ql κ (fdivH H (cpoly ρ ws es))) :
    Shows S ζ cs Hl cl qs ql (airTg cs Hl cl qs ql κ H ws es (fun x a => fval x (ρ a)))
      (airTgE ζ cs Hl cl qs ql κ H ws es (fun a => fvalE ζ (ρ a))) := by
  obtain ⟨_, _, h3, h4⟩ := air_quot ρ ws es H hnd hvan hP
  exact shows_congr (shows_of_honest hζ hc hcl hq) (fun x hx => h3 cs Hl cl qs ql κ x (hS x hx))
    (h4 ζ cs Hl cl qs ql κ hZ)

end Circuit
