import Ski.ZK.VanishPow
import Ski.Circuit.Selectors

/-!
# The constraints vanish on the trace domain

`air_quot` asks that every constraint vanish on the trace domain `H`
under Plonky3's selector polynomials (`hvan`).  The circuit's own
semantics (`Sat`, `Ski/Circuit/Air.lean`) evaluates the constraints row
by row with 0/1 selectors.  This file derives the first from the second.

`Ski/Circuit/Selectors.lean` already reads the constraints with any
selectors of Plonky3's zero pattern (`Sels`, `SatP`).  For guarded
constraints, where a selector is only a factor of the whole constraint,
`SatP` is `Sat` (`guarded_iff`), and the Rust AIRs are guarded.  This
file builds the `Sels` of Plonky3's selector polynomials at the points
`gʳ` (`p3Sels`).  The first- and last-row selectors are the products of
`VanishPow`, and the transition selector is `X - gᵐ` with `m = h - 1`, so `gᵐ = g⁻¹`.  With column
polynomials that interpolate the table on `⟨g⟩`, the leaves' values at
`gʳ` are `envP` at row `r`, so `Sat` gives `hvan` (`hvan_of_sat`).
`shows_sat` puts the pieces together: for a table that meets `Sat`, its honest
quotient chunks, over Plonky3's selector polynomials, show the AIR's
targets.  `quot_length_le` bounds the quotient by the constraints'
degree.  `quot_fits` shows the quotient fits Plonky3's ZK chunk count,
`2^(lq+1)` chunks of `N` points with `D ≤ 2^lq`, in Plonky3's own degree
`E.pdeg`: the transition selector `X - g⁻¹` counts `0`, and each such
factor adds one coefficient (`E.sdeg`).
-/

namespace Circuit

open ZKF

/-- Powers of `g` repeat with period `h` when `gʰ = 1`. -/
theorem fpow_mod {g : F} {h : Nat} (hg : fpow g h = 1) (a : Nat) : fpow g a = fpow g (a % h) := by
  conv => lhs; rw [← Nat.div_add_mod a h]
  rw [fpow_add', fpow_mul', hg, fpow_one', one_mul']

/-- **Plonky3's selector polynomials** on `⟨g⟩` of size `m + 1`:
    `Z_H / (X - 1)`, `Z_H / (X - gᵐ)` and `X - gᵐ`, as products. -/
def selF (g : F) (m : Nat) : List F := fvan (cosetL (1 * g) g m)
def selL (g : F) (m : Nat) : List F := fvan (cosetL 1 g m)
def selT (g : F) (m : Nat) : List F := [-fpow g m, 1]

theorem fval_selT (g x : F) (m : Nat) : fval x (selT g m) = x - fpow g m := by
  show -fpow g m + x * (1 + x * 0) = x - fpow g m
  rw [mul_zero', add_zero', mul_one']
  exact fid (e := -v 0 + v 1) (e' := v 1 - v 0) (by decide) [fpow g m, x]

theorem mem_cosetL_one {g : F} {m r : Nat} (hr : r < m) : fpow g r ∈ cosetL 1 g m :=
  mem_coset_iff.2 ⟨r, hr, by rw [one_mul']⟩

theorem mem_cosetL_g {g : F} {m r : Nat} (hr0 : r ≠ 0) (hr : r < m + 1) : fpow g r ∈ cosetL (1 * g) g m :=
  mem_coset_iff.2 ⟨r - 1, by omega, by rw [one_mul', fpow_succ', show r - 1 + 1 = r by omega]⟩

theorem not_mem_cosetL {g : F} {n a : Nat} (hinj : ∀ a b, a < n → b < n → fpow g a = fpow g b → a = b) (ha : a < n)
    {s : F} (hs : s = 1 ∨ s = 1 * g) {k : Nat} (hk : (s = 1 ∧ k = 0) ∨ (s = 1 * g ∧ k = 1))
    {len : Nat} (hlen : k + len ≤ n) (hout : a < k ∨ k + len ≤ a) : fpow g a ∉ cosetL s g len := fun hm => by
  obtain ⟨t, ht, e⟩ := mem_coset hm
  have e' : fpow g a = fpow g (k + t) := by
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e, one_mul', Nat.zero_add]
    · rw [e, one_mul', fpow_succ', Nat.add_comm]
  have := hinj a (k + t) ha (by omega) e'
  omega

/-- **Plonky3's selectors as `Sels`**: for `r < m + 1` their values at
    `gʳ`, past the table constants with the same pattern; the zero pattern `Sels` asks when the powers of `g` below `m + 1`
    are distinct. -/
def p3Sels (g : F) (m : Nat) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b) : Sels (m + 1) where
  first r := if r < m + 1 then fval (fpow g r) (selF g m) else 0
  last r := if r < m + 1 then fval (fpow g r) (selL g m) else 0
  trans r := if r < m + 1 then fval (fpow g r) (selT g m) else 1
  first_zero r := by
    by_cases hr : r < m + 1
    · rw [if_pos hr]
      constructor
      · intro h e; subst e
        exact fvan_ne _ _ (not_mem_cosetL hinj hr (.inr rfl) (.inr ⟨rfl, rfl⟩) (by omega) (.inl (by omega))) h
      · intro h; exact fvan_root _ _ (mem_cosetL_g h hr)
    · rw [if_neg hr]; exact ⟨fun _ => by omega, fun _ => rfl⟩
  last_zero r := by
    by_cases hr : r < m + 1
    · rw [if_pos hr]
      constructor
      · intro h e
        have hrm : r = m := by omega
        subst hrm
        exact fvan_ne _ _ (not_mem_cosetL hinj hr (.inl rfl) (.inl ⟨rfl, rfl⟩) (by omega) (.inr (by omega))) h
      · intro h; exact fvan_root _ _ (mem_cosetL_one (by omega))
    · rw [if_neg hr]; exact ⟨fun _ => by omega, fun _ => rfl⟩
  trans_zero r := by
    by_cases hr : r < m + 1
    · rw [if_pos hr, fval_selT]
      constructor
      · intro h
        have := hinj r m hr (Nat.lt_succ_self m) (sub_eq_zero h)
        omega
      · intro h
        have hrm : r = m := by omega
        rw [hrm, sub_self']
    · rw [if_neg hr]; exact ⟨fun h => absurd h (by decide), fun h => by omega⟩

/-- **The constraints vanish on the trace domain**: when the table meets
    `Sat`, every constraint is guarded, `T.h = m + 1`, the powers of `g`
    below `m + 1` are distinct with `g^{m+1} = 1`, and the column
    polynomials interpolate the table's columns at the points `gʳ`, every
    constraint vanishes at every point of `⟨g⟩` over the column
    polynomials and Plonky3's selectors. -/
theorem hvan_of_sat {A : AirD} {T : Table} {g : F} {m : Nat} (hsat : Sat A T) (hh : T.h = m + 1)
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hgd : ∀ c ∈ A.cons, c.guarded = true) (main pre : Nat → List F)
    (hmain : ∀ r i, r < m + 1 → fval (fpow g r) (main i) = T.main r i)
    (hpre : ∀ r i, r < m + 1 → fval (fpow g r) (pre i) = T.pre r i) :
    ∀ c ∈ A.cons, ∀ x ∈ cosetL 1 g (m + 1),
      c.eval (fun a => fval x (stdRho g main pre (selF g m) (selL g m) (selT g m) a)) = 0 := by
  obtain ⟨h, tm, tp⟩ := T
  change h = m + 1 at hh
  subst hh
  intro c hc x hx
  obtain ⟨r, hr, rfl⟩ := mem_coset hx
  rw [one_mul']
  have hcol : ∀ o, fpow g o * fpow g r = fpow g ((r + o) % (m + 1)) := fun o => by
    rw [← fpow_add', Nat.add_comm, ← fpow_mod hg]
  have hmod : ∀ o, (r + o) % (m + 1) < m + 1 := fun o => Nat.mod_lt _ (Nat.succ_pos m)
  have hagree : (fun a => fval (fpow g r) (stdRho g main pre (selF g m) (selL g m) (selT g m) a)) =
      Table.envP ⟨m + 1, tm, tp⟩ (p3Sels g m hinj) r := by
    funext a
    cases a with
    | main o i => rw [(fval_stdRho _ g main pre _ _ _ o i).1, hcol, hmain _ i (hmod o)]; rfl
    | pre o i => rw [(fval_stdRho _ g main pre _ _ _ o i).2, hcol, hpre _ i (hmod o)]; rfl
    | first => exact (if_pos hr).symm
    | last => exact (if_pos hr).symm
    | trans => exact (if_pos hr).symm
  rw [hagree]
  exact (guarded_iff ⟨m + 1, tm, tp⟩ (p3Sels g m hinj) r c (hgd c hc)).2 (hsat.2 c hc r hr)

theorem cosetL_one_nodup {g : F} {n : Nat} (hinj : ∀ a b, a < n → b < n → fpow g a = fpow g b → a = b) :
    (cosetL 1 g n).Nodup :=
  coset_nodup g n 1 (fun t t' ht ht' e => by rw [one_mul', one_mul'] at e; exact hinj t t' ht ht' e)

/-- **The quotient's size from the constraints' degree**: at most
    `D m + 1 - |H|` coefficients, constraints of degree at most `D` over
    leaves of at most `m + 1`. -/
theorem quot_length_le (ρ : Atom → List F) (m D : Nat) (hρ : ∀ a, (ρ a).length ≤ m + 1) (ws : List F) (es : List E)
    (hD : ∀ e ∈ es, e.deg ≤ D) (H : List F) : (fdivH H (cpoly ρ ws es)).length ≤ D * m + 1 - H.length := by
  rw [fdivH_length]; have := cpoly_length ρ m D hρ ws es hD; omega

/-- **For a table that meets `Sat`, its honest quotient chunks show the AIR's targets**:
    `shows_air` with the vanishing from `Sat` (`hvan_of_sat`), the trace
    domain `⟨g⟩` and Plonky3's selector polynomials. -/
theorem shows_sat {A : AirD} {T : Table} {g : F} {m : Nat} (hsat : Sat A T) (hh : T.h = m + 1)
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hgd : ∀ c ∈ A.cons, c.guarded = true) (main pre : Nat → List F)
    (hmain : ∀ r i, r < m + 1 → fval (fpow g r) (main i) = T.main r i)
    (hpre : ∀ r i, r < m + 1 → fval (fpow g r) (pre i) = T.pre r i)
    {S : List F} {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) {cs : List Chunk} {Hl : List F} {cl : F}
    {qs : List (List F)} {ql : List F} {κ : F} (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (ws : List F)
    (hP : (cpoly (stdRho g main pre (selF g m) (selL g m) (selT g m)) ws A.cons).length ≤ P)
    (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0) (hZ : fvalE ζ (fvan (cosetL 1 g (m + 1))) ≠ EF.zero)
    (hq : QuotOK cs Hl cl qs ql κ
      (fdivH (cosetL 1 g (m + 1)) (cpoly (stdRho g main pre (selF g m) (selL g m) (selT g m)) ws A.cons))) :
    Shows S ζ cs Hl cl qs ql
      (airTg cs Hl cl qs ql κ (cosetL 1 g (m + 1)) ws A.cons
        (fun x a => fval x (stdRho g main pre (selF g m) (selL g m) (selT g m) a)))
      (airTgE ζ cs Hl cl qs ql κ (cosetL 1 g (m + 1)) ws A.cons
        (fun a => fvalE ζ (stdRho g main pre (selF g m) (selL g m) (selT g m) a))) :=
  shows_air hζ hc hcl _ ws A.cons _ (cosetL_one_nodup hinj)
    (hvan_of_sat hsat hh hg hinj hgd main pre hmain hpre) hP hS hZ hq

/-- **Plonky3's degree** of an expression, in units of the trace's
    degree: columns and the first- and last-row selectors count `1`, the
    transition selector `X - g⁻¹` counts `0` (`SymbolicExpression`'s
    `degree_multiple`). -/
def E.pdeg : E → Nat
  | .atom .trans => 0
  | .atom _ => 1
  | .const _ => 0
  | .add a b | .sub a b => max a.pdeg b.pdeg
  | .mul a b => a.pdeg + b.pdeg
  | .neg a => a.pdeg

/-- The extra coefficients transition factors add: one each. -/
def E.sdeg : E → Nat
  | .atom .trans => 1
  | .atom _ => 0
  | .const _ => 0
  | .add a b | .sub a b => max a.sdeg b.sdeg
  | .mul a b => a.sdeg + b.sdeg
  | .neg a => a.sdeg

theorem len_max {la lb da db sa sb m : Nat} (ha : la ≤ da * m + sa + 1) (hb : lb ≤ db * m + sb + 1) :
    max la lb ≤ max da db * m + max sa sb + 1 := by
  have h1 : da * m ≤ max da db * m := Nat.mul_le_mul_right m (Nat.le_max_left da db)
  have h2 : db * m ≤ max da db * m := Nat.mul_le_mul_right m (Nat.le_max_right da db)
  have h3 := Nat.le_max_left sa sb
  have h4 := Nat.le_max_right sa sb
  exact Nat.max_le.2 ⟨by omega, by omega⟩

/-- **The polynomial's size in Plonky3's degree**: at most
    `pdeg · m + sdeg + 1` coefficients, leaves of at most `m + 1` and the
    transition selector of at most `2`. -/
theorem epoly_plen (ρ : Atom → List F) (m : Nat) (hρ : ∀ a, a ≠ .trans → (ρ a).length ≤ m + 1)
    (ht : (ρ .trans).length ≤ 2) : ∀ e : E, (e.fpoly ρ).length ≤ e.pdeg * m + e.sdeg + 1
  | .atom .trans => by show (ρ .trans).length ≤ 0 * m + 1 + 1; omega
  | .atom .first => by show (ρ .first).length ≤ 1 * m + 0 + 1; have := hρ .first (by decide); omega
  | .atom .last => by show (ρ .last).length ≤ 1 * m + 0 + 1; have := hρ .last (by decide); omega
  | .atom (.main o i) => by show (ρ _).length ≤ 1 * m + 0 + 1; have := hρ (.main o i) Atom.noConfusion; omega
  | .atom (.pre o i) => by show (ρ _).length ≤ 1 * m + 0 + 1; have := hρ (.pre o i) Atom.noConfusion; omega
  | .const _ => by show 1 ≤ 0 * m + 0 + 1; omega
  | .add a b => by
    show (fcadd _ _).length ≤ max a.pdeg b.pdeg * m + max a.sdeg b.sdeg + 1
    exact Nat.le_trans (fcadd_length _ _) (len_max (epoly_plen ρ m hρ ht a) (epoly_plen ρ m hρ ht b))
  | .sub a b => by
    show (fcadd _ (fcscale _ _)).length ≤ max a.pdeg b.pdeg * m + max a.sdeg b.sdeg + 1
    have := fcadd_length (a.fpoly ρ) (fcscale (-1) (b.fpoly ρ))
    rw [fcscale_length] at this
    exact Nat.le_trans this (len_max (epoly_plen ρ m hρ ht a) (epoly_plen ρ m hρ ht b))
  | .mul a b => by
    have ha := epoly_plen ρ m hρ ht a; have hb := epoly_plen ρ m hρ ht b
    show (fmul _ _).length ≤ (a.pdeg + b.pdeg) * m + (a.sdeg + b.sdeg) + 1
    rw [Nat.add_mul]
    by_cases hq : b.fpoly ρ = []
    · have := fmul_len_le (a.fpoly ρ) (b.fpoly ρ)
      rw [hq, List.length_nil] at this; rw [hq]
      omega
    · have := fmul_length (a.fpoly ρ) (b.fpoly ρ) hq
      omega
  | .neg a => by
    show (fcscale _ _).length ≤ a.pdeg * m + a.sdeg + 1; rw [fcscale_length]; exact epoly_plen ρ m hρ ht a

theorem cpoly_plen (ρ : Atom → List F) (m D s : Nat) (hρ : ∀ a, a ≠ .trans → (ρ a).length ≤ m + 1)
    (ht : (ρ .trans).length ≤ 2) (ws : List F) (es : List E) (hD : ∀ e ∈ es, e.pdeg ≤ D) (hs : ∀ e ∈ es, e.sdeg ≤ s) :
    (cpoly ρ ws es).length ≤ D * m + s + 1 :=
  foldP_length _ ws _ (fun p hp => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
    have := epoly_plen ρ m hρ ht e
    have := Nat.mul_le_mul_right m (hD e he)
    have := hs e he
    omega)

/-- **Plonky3's chunk count fits the quotient** under ZK: a trace of `N`
    rows has polynomials of `2N` coefficients, and there are `2^(lq+1)`
    chunks of `N` points each, with `D ≤ 2^lq` for Plonky3's degree `D`
    (`get_log_num_quotient_chunks`, `num_quotient_chunks = 1 << (lq +
    is_zk)`).  Then `D (2N - 1) + s + 1 - N ≤ 2^(lq+1) N` when `s < N`. -/
theorem p3_deg (D N lq s : Nat) (hs : s < N) (hD : D ≤ 2 ^ lq) : D * (2 * N - 1) + s + 1 - N ≤ 2 ^ (lq + 1) * N := by
  rcases N with _ | N
  · exact absurd hs (Nat.not_lt_zero s)
  · have h1 : D * (2 * (N + 1) - 1) ≤ D * (2 * (N + 1)) := Nat.mul_le_mul_left D (by omega)
    have h2 : D * (2 * (N + 1)) ≤ 2 ^ lq * (2 * (N + 1)) := Nat.mul_le_mul_right _ hD
    have h3 : 2 ^ lq * (2 * (N + 1)) = 2 ^ (lq + 1) * (N + 1) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    omega

/-- **The honest quotient fits Plonky3's chunks**: constraints of Plonky3
    degree at most `D ≤ 2^lq`, with at most `s < N` transition factors,
    over leaves of at most `2N` coefficients and the transition selector
    of `2`, divided by a trace domain of `N` points, leave at most
    `2^(lq+1) N` coefficients, the bound `QuotOK` asks of `2^(lq+1)`
    chunks of `N` points. -/
theorem quot_fits (ρ : Atom → List F) (N D lq s : Nat) (hρ : ∀ a, a ≠ .trans → (ρ a).length ≤ 2 * N)
    (ht : (ρ .trans).length ≤ 2) (ws : List F) (es : List E) (hD : ∀ e ∈ es, e.pdeg ≤ D)
    (hsd : ∀ e ∈ es, e.sdeg ≤ s) (hs : s < N) (hlq : D ≤ 2 ^ lq) (H : List F) (hH : H.length = N) :
    (fdivH H (cpoly ρ ws es)).length ≤ 2 ^ (lq + 1) * N := by
  have := cpoly_plen ρ (2 * N - 1) D s (fun a ha => by have := hρ a ha; omega) ht ws es hD hsd
  rw [fdivH_length, hH]
  exact Nat.le_trans (Nat.sub_le_sub_right this N) (p3_deg D N lq s hs hlq)

end Circuit
