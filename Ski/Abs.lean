import Ski.Open
open Term

/-!
# Bracket abstraction

`skijack` compiles a definition by expanding its globals to closed terms
and abstracting its formals with Curry's four rules and eta
(`aviary_kernel/abstraction.py`, `bracket_abstract`):

    [x] x      = I
    [x] E      = K E              if x is not free in E
    [x] (E x)  = E                if x is not free in E   (eta)
    [x] (E F)  = S ([x] E) ([x] F)   otherwise

`abs` is that function on open terms (`Ski/Open.lean`), whose variables
are the formals, checked in the same order: an atom is the variable or
not; an application is first tested for the variable, then for eta.
`absN` abstracts a list of formals, innermost last, as `skijack` folds
over `reversed(formals)`.  The generated `*_abs` theorems of
`Ski/Scott.lean` and `Ski/Table.lean` check, by `rfl`, that `absN` of each
Scott constructor's source equals the term `skijack` emitted.

**β.**  `abs_beta`: `abs x M ⬝ N` weakly reduces to `M[N/x]`.  Weakly, not
by head reduction alone: in the last rule, `S ([x] E) ([x] F) ⬝ N` reaches
`[x] E ⬝ N ⬝ ([x] F ⬝ N)`, and the argument `[x] F ⬝ N` is reduced only
when it comes to the head.  G1's split turns this into head steps followed
by internal parallel steps (`abs_beta_head`).  `absN_beta` is β for all the
formals at once, for closed arguments, through `absN_subst`: abstraction
commutes with substituting a closed term for another variable.
-/

-- ---------------------------------------------------------------------------
-- Occurrence, computably
-- ---------------------------------------------------------------------------

/-- The variable `x` occurs in `t`. -/
def OTerm.mem (x : Nat) : OTerm → Bool
  | .var y => y == x
  | .app f a => f.mem x || a.mem x
  | _ => false

theorem mem_var {x y : Nat} : (OTerm.var y).mem x = true ↔ y = x := by
  simp [OTerm.mem]

theorem mem_app {x : Nat} {f a : OTerm} :
    (OTerm.app f a).mem x = (f.mem x || a.mem x) := rfl

theorem OTerm.mem_of_occ {x : Nat} {t : OTerm} (h : Occ x t) : t.mem x = true := by
  induction h with
  | var => exact mem_var.mpr rfl
  | left _ _ ih => rw [mem_app, ih]; rfl
  | right _ _ ih => rw [mem_app, ih, Bool.or_true]

theorem OTerm.not_occ {x : Nat} {t : OTerm} (h : t.mem x = false) : ¬ Occ x t :=
  fun ho => by rw [OTerm.mem_of_occ ho] at h; cases h

theorem mem_toO (x : Nat) : ∀ t : Term, t.toO.mem x = false
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app f a => by
    show (f.toO.mem x || a.toO.mem x) = false
    rw [mem_toO x f, mem_toO x a]
    rfl

-- ---------------------------------------------------------------------------
-- Single substitution
-- ---------------------------------------------------------------------------

/-- `N` for the variable `x`, every other variable kept. -/
def single (x : Nat) (N : OTerm) : Nat → OTerm := fun y => if y = x then N else .var y

theorem single_self (x : Nat) (N : OTerm) : single x N x = N := if_pos rfl

theorem single_ne {x y : Nat} (N : OTerm) (h : y ≠ x) : single x N y = .var y := if_neg h

theorem subst_var : ∀ t : OTerm, t.subst OTerm.var = t
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var _ => rfl
  | .app f a => by
    show OTerm.app (f.subst OTerm.var) (a.subst OTerm.var) = _
    rw [subst_var f, subst_var a]

/-- Substituting for a variable that does not occur changes nothing. -/
theorem subst_single_of_not_mem {x : Nat} {N t : OTerm} (h : t.mem x = false) :
    t.subst (single x N) = t := by
  have e : t.subst (single x N) = t.subst OTerm.var :=
    subst_agree fun i hi => single_ne N (fun e => OTerm.not_occ h (e ▸ hi))
  rw [e, subst_var]

-- ---------------------------------------------------------------------------
-- The abstraction
-- ---------------------------------------------------------------------------

/-- `[x] t`, exactly as `skijack`'s `bracket_abstract`. -/
def abs (x : Nat) : OTerm → OTerm
  | .var y => if y = x then .I else .K ⬝ₒ .var y
  | .app e f =>
    if (OTerm.app e f).mem x = false then .K ⬝ₒ .app e f
    else if f = .var x ∧ e.mem x = false then e
    else .S ⬝ₒ abs x e ⬝ₒ abs x f
  | t => .K ⬝ₒ t

theorem abs_var (x y : Nat) : abs x (.var y) = if y = x then .I else .K ⬝ₒ .var y := rfl

theorem abs_app (x : Nat) (e f : OTerm) :
    abs x (.app e f) = if (OTerm.app e f).mem x = false then .K ⬝ₒ .app e f
      else if f = .var x ∧ e.mem x = false then e
      else .S ⬝ₒ abs x e ⬝ₒ abs x f := rfl

/-- `[x1] … [xn] t`, the formals in order. -/
def absN (xs : List Nat) (t : OTerm) : OTerm := xs.foldr abs t

/-- `abs x t` and `t.mem x` in one pass.  `abs` checks occurrence afresh
    at every node, so the kernel evaluates it in time quadratic in the
    term, cubic for a Scott constructor of `m` alternatives; this is linear.
    `absO_eq` proves it the same, so kernel checks of large programs use it. -/
def absO (x : Nat) : OTerm → OTerm × Bool
  | .var y => if y = x then (.I, true) else (.K ⬝ₒ .var y, false)
  | .app e f =>
    match absO x e, absO x f with
    | (e', be), (f', bf) =>
      if (be || bf) = false then (.K ⬝ₒ .app e f, false)
      else if f = .var x ∧ be = false then (e, true)
      else (.S ⬝ₒ e' ⬝ₒ f', true)
  | t => (.K ⬝ₒ t, false)

theorem absO_eq (x : Nat) : ∀ t, absO x t = (abs x t, t.mem x)
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var y => by
    show (if y = x then (OTerm.I, true) else (.K ⬝ₒ .var y, false)) = (abs x (.var y), y == x)
    by_cases h : y = x
    · subst h; rw [if_pos rfl, abs_var, if_pos rfl, show (y == y) = true from beq_iff_eq.mpr rfl]
    · rw [if_neg h, abs_var, if_neg h, beq_false_of_ne h]
  | .app e f => by
    rw [absO, absO_eq x e, absO_eq x f, abs_app]
    show (if (e.mem x || f.mem x) = false then (OTerm.K ⬝ₒ .app e f, false)
        else if f = .var x ∧ e.mem x = false then (e, true)
        else (OTerm.S ⬝ₒ abs x e ⬝ₒ abs x f, true)) =
      (if (e.mem x || f.mem x) = false then OTerm.K ⬝ₒ .app e f
        else if f = .var x ∧ e.mem x = false then e
        else OTerm.S ⬝ₒ abs x e ⬝ₒ abs x f, (e.mem x || f.mem x))
    by_cases hm : (e.mem x || f.mem x) = false
    · rw [if_pos hm, if_pos hm, hm]
    · have ht : (e.mem x || f.mem x) = true := by
        cases hb : (e.mem x || f.mem x)
        · exact absurd hb hm
        · rfl
      rw [if_neg hm, if_neg hm, ht]
      by_cases h2 : f = .var x ∧ e.mem x = false
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]


/-- A term without the variable abstracts to a constant. -/
theorem abs_of_not_mem {x : Nat} : ∀ {t : OTerm}, t.mem x = false → abs x t = .K ⬝ₒ t
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var y, h => by
    have hne : y ≠ x := fun e => by rw [mem_var.mpr e] at h; cases h
    rw [abs_var, if_neg hne]
  | .app e f, h => by rw [abs_app, if_pos h]

/-- Abstraction removes its variable and keeps the rest. -/
theorem mem_abs (x y : Nat) : ∀ t : OTerm, (abs x t).mem y = (t.mem y && y != x)
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var z => by
    by_cases h : z = x
    · subst h
      rw [abs_var, if_pos rfl]
      show false = ((z == y) && (y != z))
      by_cases hy : y = z
      · subst hy; rw [bne_self_eq_false, Bool.and_false]
      · rw [beq_false_of_ne (Ne.symm hy)]; rfl
    · rw [abs_var, if_neg h]
      show (false || (z == y)) = ((z == y) && (y != x))
      by_cases hy : y = x
      · subst hy; rw [beq_false_of_ne h, bne_self_eq_false]; rfl
      · rw [bne_iff_ne.mpr hy, Bool.and_true, Bool.false_or]
  | .app e f => by
    rw [abs_app]
    by_cases hm : (OTerm.app e f).mem x = false
    · rw [if_pos hm]
      show (false || (OTerm.app e f).mem y) = ((OTerm.app e f).mem y && (y != x))
      by_cases hy : y = x
      · subst hy; rw [hm, bne_self_eq_false]; rfl
      · rw [bne_iff_ne.mpr hy, Bool.and_true, Bool.false_or]
    · rw [if_neg hm]
      by_cases h2 : f = .var x ∧ e.mem x = false
      · rw [if_pos h2]
        cases h2 with
        | intro hf he =>
          subst hf
          show e.mem y = ((e.mem y || (x == y)) && (y != x))
          by_cases hy : y = x
          · subst hy; rw [he, bne_self_eq_false, Bool.and_false]
          · rw [beq_false_of_ne (Ne.symm hy), Bool.or_false, bne_iff_ne.mpr hy, Bool.and_true]
      · rw [if_neg h2]
        show ((false || (abs x e).mem y) || (abs x f).mem y) = ((e.mem y || f.mem y) && (y != x))
        rw [mem_abs x y e, mem_abs x y f]
        cases e.mem y <;> cases f.mem y <;> cases (y != x) <;> rfl

/-- The variables of a term, possibly repeated. -/
def OTerm.vars : OTerm → List Nat
  | .var y => [y]
  | .app e f => e.vars ++ f.vars
  | _ => []

theorem OTerm.mem_vars (y : Nat) : ∀ t : OTerm, t.mem y = true ↔ y ∈ t.vars
  | .S => by simp [OTerm.mem, OTerm.vars]
  | .K => by simp [OTerm.mem, OTerm.vars]
  | .I => by simp [OTerm.mem, OTerm.vars]
  | .var z => by
    show (z == y) = true ↔ y ∈ [z]
    rw [beq_iff_eq, List.mem_singleton]
    exact ⟨Eq.symm, Eq.symm⟩
  | .app e f => by
    show (e.mem y || f.mem y) = true ↔ y ∈ e.vars ++ f.vars
    rw [Bool.or_eq_true, List.mem_append, OTerm.mem_vars y e, OTerm.mem_vars y f]

/-- `absN`, innermost formal first, carrying the variables `vs` of the
    term so far: a formal not among them costs one `K`, not a pass over the
    term.  A Scott constructor of `m` alternatives abstracts in time linear
    in `m`, where `absN` takes cubic time in the kernel. -/
def absNV : List Nat → OTerm → List Nat → OTerm × List Nat
  | [], t, vs => (t, vs)
  | x :: xs, t, vs =>
    match absNV xs t vs with
    | (u, us) =>
      if us.contains x then ((absO x u).1, us.filter (· != x)) else (.K ⬝ₒ u, us)

theorem absNV_eq : ∀ (xs : List Nat) (t : OTerm) (vs : List Nat),
    (∀ y, t.mem y = true ↔ y ∈ vs) →
    (absNV xs t vs).1 = absN xs t ∧ ∀ y, (absN xs t).mem y = true ↔ y ∈ (absNV xs t vs).2
  | [], _, _, h => ⟨rfl, h⟩
  | x :: xs, t, vs, h => by
    have ih := absNV_eq xs t vs h
    cases hr : absNV xs t vs with
    | mk u us =>
      rw [hr] at ih
      cases ih with
      | intro hu hus =>
        simp only at hu hus
        subst hu
        show (absNV (x :: xs) t vs).1 = abs x (absN xs t) ∧
          ∀ y, (abs x (absN xs t)).mem y = true ↔ y ∈ (absNV (x :: xs) t vs).2
        simp only [absNV, hr]
        by_cases hx : us.contains x = true
        · rw [if_pos hx, absO_eq]
          refine ⟨rfl, fun y => ?_⟩
          rw [mem_abs, List.mem_filter, Bool.and_eq_true, hus]
        · rw [if_neg hx]
          have hn : (absN xs t).mem x = false := by
            cases hm : (absN xs t).mem x
            · rfl
            · exact absurd (List.contains_iff_mem.mpr ((hus x).mp hm)) hx
          rw [abs_of_not_mem hn]
          exact ⟨rfl, fun y => by simp only [OTerm.mem, Bool.false_or]; exact hus y⟩

/-- `absN` by `absNV`. -/
def absNF (xs : List Nat) (t : OTerm) : OTerm := (absNV xs t t.vars).1

theorem absNF_eq (xs : List Nat) (t : OTerm) : absNF xs t = absN xs t :=
  (absNV_eq xs t t.vars (OTerm.mem_vars · t)).1

-- ---------------------------------------------------------------------------
-- β
-- ---------------------------------------------------------------------------

/-- **β for bracket abstraction.**  `[x] M ⬝ N` weakly reduces to `M[N/x]`. -/
theorem abs_beta (x : Nat) (N : OTerm) : ∀ M : OTerm,
    OWSteps (abs x M ⬝ₒ N) (M.subst (single x N))
  | .S => (OSteps.single (.K _ _)).weak
  | .K => (OSteps.single (.K _ _)).weak
  | .I => (OSteps.single (.K _ _)).weak
  | .var y => by
    by_cases hy : y = x
    · subst hy
      rw [abs_var, if_pos rfl]
      show OWSteps (.I ⬝ₒ N) (single y N y)
      rw [single_self]
      exact (OSteps.single (.I _)).weak
    · rw [abs_var, if_neg hy]
      show OWSteps (.K ⬝ₒ .var y ⬝ₒ N) (single x N y)
      rw [single_ne N hy]
      exact (OSteps.single (.K _ _)).weak
  | .app e f => by
    by_cases hm : (OTerm.app e f).mem x = false
    · rw [abs_app, if_pos hm, subst_single_of_not_mem hm]
      exact (OSteps.single (.K _ _)).weak
    · by_cases he : f = .var x ∧ e.mem x = false
      · rw [abs_app, if_neg hm, if_pos he]
        cases he with
        | intro hf he =>
          subst hf
          show OWSteps (e ⬝ₒ N) (OTerm.app (e.subst (single x N)) (single x N x))
          rw [subst_single_of_not_mem he, single_self]
          exact .refl _
      · rw [abs_app, if_neg hm, if_neg he]
        exact .step (.S _ _ _) (OWSteps.app (abs_beta x N e) (abs_beta x N f))

/-- β as head reduction: head steps, then internal parallel steps (G1). -/
theorem abs_beta_head (x : Nat) (N M : OTerm) :
    ∃ w, OSteps (abs x M ⬝ₒ N) w ∧ OParIs w (M.subst (single x N)) :=
  owsteps_split (abs_beta x N M)

-- ---------------------------------------------------------------------------
-- Abstraction commutes with substituting a closed term for another variable
-- ---------------------------------------------------------------------------

theorem mem_subst_single {x y : Nat} {N : OTerm} (hxy : x ≠ y) (hN : N.mem x = false) :
    ∀ t : OTerm, (t.subst (single y N)).mem x = t.mem x
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var z => by
    by_cases hz : z = y
    · subst hz
      show (single z N z).mem x = (OTerm.var z).mem x
      rw [single_self, hN]
      cases h : (OTerm.var z).mem x with
      | false => rfl
      | true => exact absurd (mem_var.mp h).symm hxy
    · show (single y N z).mem x = (OTerm.var z).mem x
      rw [single_ne N hz]
  | .app f a => by
    show ((f.subst (single y N)).mem x || (a.subst (single y N)).mem x) = (f.mem x || a.mem x)
    rw [mem_subst_single hxy hN f, mem_subst_single hxy hN a]

theorem subst_eq_var_iff {x y : Nat} {N : OTerm} (hxy : x ≠ y) (hN : N.mem x = false) :
    ∀ f : OTerm, f.subst (single y N) = .var x ↔ f = .var x
  | .S => by simp [OTerm.subst]
  | .K => by simp [OTerm.subst]
  | .I => by simp [OTerm.subst]
  | .var z => by
    by_cases hz : z = y
    · subst hz
      show single z N z = .var x ↔ OTerm.var z = .var x
      rw [single_self]
      constructor
      · intro e
        rw [e, mem_var.mpr rfl] at hN
        cases hN
      · intro e
        cases e
        exact absurd rfl hxy
    · show single y N z = .var x ↔ OTerm.var z = .var x
      rw [single_ne N hz]
  | .app f a => by
    constructor
    · intro e; cases e
    · intro e; cases e

/-- Abstraction commutes with substituting, for another variable, a term in
    which the abstracted variable does not occur. -/
theorem abs_subst {x y : Nat} {N : OTerm} (hxy : x ≠ y) (hN : N.mem x = false) :
    ∀ M : OTerm, (abs x M).subst (single y N) = abs x (M.subst (single y N))
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var z => by
    by_cases hzx : z = x
    · subst hzx
      have hzy : z ≠ y := hxy
      rw [abs_var, if_pos rfl]
      show OTerm.I = abs z (single y N z)
      rw [single_ne N hzy, abs_var, if_pos rfl]
    · rw [abs_var, if_neg hzx]
      show OTerm.K ⬝ₒ single y N z = abs x (single y N z)
      by_cases hzy : z = y
      · subst hzy
        rw [single_self]
        exact (abs_of_not_mem hN).symm
      · rw [single_ne N hzy, abs_var, if_neg hzx]
  | .app e f => by
    have hm := mem_subst_single hxy hN (.app e f)
    by_cases hmx : (OTerm.app e f).mem x = false
    · rw [abs_app, if_pos hmx, abs_of_not_mem (hm ▸ hmx)]
      rfl
    · have hmx' : ¬ (OTerm.app (e.subst (single y N)) (f.subst (single y N))).mem x = false :=
        fun h => hmx (hm ▸ (h : ((OTerm.app e f).subst (single y N)).mem x = false))
      have hiff := subst_eq_var_iff hxy hN f
      have he' := mem_subst_single hxy hN e
      by_cases heta : f = .var x ∧ e.mem x = false
      · rw [abs_app, if_neg hmx, if_pos heta]
        have heta' : f.subst (single y N) = .var x ∧ (e.subst (single y N)).mem x = false :=
          ⟨hiff.mpr heta.1, he' ▸ heta.2⟩
        show e.subst (single y N) = abs x (OTerm.app (e.subst (single y N)) (f.subst (single y N)))
        rw [abs_app, if_neg hmx', if_pos heta']
      · rw [abs_app, if_neg hmx, if_neg heta]
        have heta' : ¬ (f.subst (single y N) = .var x ∧ (e.subst (single y N)).mem x = false) :=
          fun h => heta ⟨hiff.mp h.1, he' ▸ h.2⟩
        show OTerm.S ⬝ₒ (abs x e).subst (single y N) ⬝ₒ (abs x f).subst (single y N) =
          abs x (OTerm.app (e.subst (single y N)) (f.subst (single y N)))
        rw [abs_subst hxy hN e, abs_subst hxy hN f, abs_app, if_neg hmx', if_neg heta']

/-- The formals are distinct. -/
def Distinct : List Nat → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ Distinct xs

theorem absN_subst {y : Nat} {N : OTerm} (hN : ∀ x, N.mem x = false) :
    ∀ {xs : List Nat}, y ∉ xs → ∀ M : OTerm,
      (absN xs M).subst (single y N) = absN xs (M.subst (single y N))
  | [], _, _ => rfl
  | x :: xs, hy, M => by
    have hxy : x ≠ y := fun e => hy (e ▸ .head xs)
    have hy' : y ∉ xs := fun h => hy (.tail x h)
    show (abs x (absN xs M)).subst (single y N) = abs x (absN xs (M.subst (single y N)))
    rw [abs_subst hxy (hN x), absN_subst hN hy' M]

/-- `t` applied to a list of arguments. -/
def appL : OTerm → List OTerm → OTerm
  | t, [] => t
  | t, a :: as => appL (t ⬝ₒ a) as

theorem OWSteps.appL {t u : OTerm} (h : OWSteps t u) : ∀ as, OWSteps (appL t as) (appL u as)
  | [] => h
  | a :: as => OWSteps.appL (OWSteps.left a h) as

/-- Substitute closed arguments for the formals, first to last. -/
def substL : List Nat → List Term → OTerm → OTerm
  | x :: xs, N :: Ns, M => substL xs Ns (M.subst (single x N.toO))
  | _, _, M => M

/-- **β for all the formals at once**, for closed arguments: `[x1] … [xn] M`
    applied to `N1 … Nn` weakly reduces to `M` with each `Ni` for `xi`. -/
theorem absN_beta : ∀ (xs : List Nat) (Ns : List Term) (M : OTerm),
    Distinct xs → xs.length = Ns.length →
      OWSteps (appL (absN xs M) (Ns.map Term.toO)) (substL xs Ns M)
  | [], [], _, _, _ => .refl _
  | x :: xs, N :: Ns, M, hd, hl => by
    show OWSteps (appL (abs x (absN xs M) ⬝ₒ N.toO) (Ns.map Term.toO))
      (substL xs Ns (M.subst (single x N.toO)))
    have h1 := abs_beta x N.toO (absN xs M)
    rw [absN_subst (fun z => mem_toO z N) hd.1 M] at h1
    exact (OWSteps.appL h1 _).trans
      (absN_beta xs Ns _ hd.2 (Nat.succ.inj hl))
  | [], _ :: _, _, _, hl => by cases hl
  | _ :: _, [], _, _, hl => by cases hl

-- ---------------------------------------------------------------------------
-- β under any substitution, for any arguments
-- ---------------------------------------------------------------------------

theorem OWStep.subst (τ : Nat → OTerm) {t u : OTerm} (h : OWStep t u) :
    OWStep (t.subst τ) (u.subst τ) := by
  induction h with
  | S f g x => exact .S _ _ _
  | K x y => exact .K _ _
  | I x => exact .I _
  | left x _ ih => exact .left _ ih
  | right f _ ih => exact .right _ ih

theorem OWSteps.subst (τ : Nat → OTerm) {t u : OTerm} (h : OWSteps t u) :
    OWSteps (t.subst τ) (u.subst τ) := by
  induction h with
  | refl t => exact .refl _
  | step h _ ih => exact .step (h.subst τ) ih

theorem OWStep.close (σ : Nat → Term) {t u : OTerm} (h : OWStep t u) :
    WStep (t.close σ) (u.close σ) := by
  induction h with
  | S f g x => exact .S _ _ _
  | K x y => exact .K _ _
  | I x => exact .I _
  | left x _ ih => exact .left _ ih
  | right f _ ih => exact .right _ ih

theorem OWSteps.close (σ : Nat → Term) {t u : OTerm} (h : OWSteps t u) :
    WSteps (t.close σ) (u.close σ) := by
  induction h with
  | refl t => exact .refl _
  | step h _ ih => exact .step (h.close σ) ih

theorem close_agree {σ₁ σ₂ : Nat → Term} :
    ∀ {t : OTerm}, (∀ i, Occ i t → σ₁ i = σ₂ i) → t.close σ₁ = t.close σ₂
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var i, h => h i (.var i)
  | .app f x, h => by
    show Term.app (f.close σ₁) (x.close σ₁) = Term.app (f.close σ₂) (x.close σ₂)
    rw [close_agree (fun i hi => h i (.left x hi)), close_agree (fun i hi => h i (.right f hi))]

/-- `[x] t` has no variable `t` lacks, and not `x`. -/
theorem occ_abs {x y : Nat} : ∀ {t : OTerm}, Occ y (abs x t) → Occ y t ∧ y ≠ x
  | .S, h => by
    have h' : Occ y (.K ⬝ₒ .S) := h
    cases h' with
    | left _ h1 => cases h1
    | right _ h1 => cases h1
  | .K, h => by
    have h' : Occ y (.K ⬝ₒ .K) := h
    cases h' with
    | left _ h1 => cases h1
    | right _ h1 => cases h1
  | .I, h => by
    have h' : Occ y (.K ⬝ₒ .I) := h
    cases h' with
    | left _ h1 => cases h1
    | right _ h1 => cases h1
  | .var z, h => by
    rw [abs_var] at h
    by_cases hz : z = x
    · rw [if_pos hz] at h
      cases h
    · rw [if_neg hz] at h
      cases h with
      | left _ h1 => cases h1
      | right _ h1 =>
        cases h1
        exact ⟨.var y, hz⟩
  | .app e f, h => by
    rw [abs_app] at h
    by_cases hm : (OTerm.app e f).mem x = false
    · rw [if_pos hm] at h
      cases h with
      | left _ h1 => cases h1
      | right _ h1 =>
        exact ⟨h1, fun e' => by subst e'; rw [OTerm.mem_of_occ h1] at hm; cases hm⟩
    · rw [if_neg hm] at h
      by_cases he : f = .var x ∧ e.mem x = false
      · rw [if_pos he] at h
        exact ⟨.left f h, fun e' => by subst e'; rw [OTerm.mem_of_occ h] at he; cases he.2⟩
      · rw [if_neg he] at h
        cases h with
        | left _ h1 =>
          cases h1 with
          | left _ h2 => cases h2
          | right _ h2 =>
            have r := occ_abs h2
            exact ⟨.left f r.1, r.2⟩
        | right _ h1 =>
          have r := occ_abs h1
          exact ⟨.right e r.1, r.2⟩

/-- `ρ` with `N` for `x`. -/
def upd (ρ : Nat → OTerm) (x : Nat) (N : OTerm) : Nat → OTerm :=
  fun y => if y = x then N else ρ y

/-- `ρ` with the arguments for the formals, first to last; a later formal
    of the same name wins, as it does under abstraction. -/
def override : (Nat → OTerm) → List Nat → List OTerm → Nat → OTerm
  | ρ, x :: xs, N :: Ns => override (upd ρ x N) xs Ns
  | ρ, _, _ => ρ

theorem single_var (x : Nat) : single x (.var x) = OTerm.var :=
  funext fun y => by
    by_cases h : y = x
    · rw [single, if_pos h, h]
    · rw [single, if_neg h]

/-- β for one formal under a substitution: nothing is captured, because
    `[x] A` has no variables but `A`'s other than `x`. -/
theorem abs_beta_subst (x : Nat) (A : OTerm) (ρ : Nat → OTerm) (N : OTerm) :
    OWSteps ((abs x A).subst ρ ⬝ₒ N) (A.subst (upd ρ x N)) := by
  have h0 := (abs_beta x (.var x) A).subst (upd ρ x N)
  rw [single_var, subst_var] at h0
  have e1 : (abs x A).subst (upd ρ x N) = (abs x A).subst ρ :=
    subst_agree fun i hi => if_neg (occ_abs hi).2
  have e2 : (OTerm.var x).subst (upd ρ x N) = N := if_pos rfl
  have h1 : OWSteps ((abs x A).subst (upd ρ x N) ⬝ₒ (OTerm.var x).subst (upd ρ x N))
      (A.subst (upd ρ x N)) := h0
  rw [e1, e2] at h1
  exact h1

/-- **β for all the formals, under any substitution, for any arguments.**
    `([x1] … [xn] M)[ρ]` applied to `N1 … Nn` weakly reduces to `M` with
    `Ni` for `xi` and `ρ` for the rest. -/
theorem absN_beta_subst : ∀ (xs : List Nat) (M : OTerm) (ρ : Nat → OTerm) (Ns : List OTerm),
    Ns.length = xs.length → OWSteps (appL ((absN xs M).subst ρ) Ns) (M.subst (override ρ xs Ns))
  | [], _, _, [], _ => .refl _
  | x :: xs, M, ρ, N :: Ns, hl =>
    (OWSteps.appL (abs_beta_subst x (absN xs M) ρ N) Ns).trans
      (absN_beta_subst xs M (upd ρ x N) Ns (Nat.succ.inj hl))
  | [], _, _, _ :: _, hl => by cases hl
  | _ :: _, _, _, [], hl => by cases hl

-- ---------------------------------------------------------------------------
-- The same for closed terms
-- ---------------------------------------------------------------------------

/-- `t` applied to a list of closed arguments. -/
def appT : Term → List Term → Term
  | t, [] => t
  | t, a :: as => appT (t ⬝ a) as

theorem WSteps.appT {t u : Term} (h : WSteps t u) : ∀ as, WSteps (appT t as) (appT u as)
  | [] => h
  | a :: as => WSteps.appT (WSteps.left a h) as

theorem appT_append (t : Term) : ∀ as bs, appT t (as ++ bs) = appT (appT t as) bs
  | [], _ => rfl
  | a :: as, bs => appT_append (t ⬝ a) as bs

theorem close_appL (σ : Nat → Term) : ∀ (t : OTerm) (as : List OTerm),
    (appL t as).close σ = appT (t.close σ) (as.map (OTerm.close σ))
  | _, [] => rfl
  | t, a :: as => close_appL σ (t ⬝ₒ a) as

/-- `γ` with `N` for `x`. -/
def updC (γ : Nat → Term) (x : Nat) (N : Term) : Nat → Term :=
  fun y => if y = x then N else γ y

/-- `γ` with the arguments for the formals, first to last. -/
def overrideC : (Nat → Term) → List Nat → List Term → Nat → Term
  | γ, x :: xs, N :: Ns => overrideC (updC γ x N) xs Ns
  | γ, _, _ => γ

theorem abs_beta_close (x : Nat) (A : OTerm) (γ : Nat → Term) (N : Term) :
    WSteps ((abs x A).close γ ⬝ N) (A.close (updC γ x N)) := by
  have h0 := (abs_beta x (.var x) A).close (updC γ x N)
  rw [single_var, subst_var] at h0
  have e1 : (abs x A).close (updC γ x N) = (abs x A).close γ :=
    close_agree fun i hi => if_neg (occ_abs hi).2
  have e2 : (OTerm.var x).close (updC γ x N) = N := if_pos rfl
  have h1 : WSteps ((abs x A).close (updC γ x N) ⬝ (OTerm.var x).close (updC γ x N))
      (A.close (updC γ x N)) := h0
  rw [e1, e2] at h1
  exact h1

/-- **β for all the formals, closed.** -/
theorem absN_beta_close : ∀ (xs : List Nat) (M : OTerm) (γ : Nat → Term) (Ns : List Term),
    Ns.length = xs.length → WSteps (appT ((absN xs M).close γ) Ns) (M.close (overrideC γ xs Ns))
  | [], _, _, [], _ => .refl _
  | x :: xs, M, γ, N :: Ns, hl =>
    (WSteps.appT (abs_beta_close x (absN xs M) γ N) Ns).trans
      (absN_beta_close xs M (updC γ x N) Ns (Nat.succ.inj hl))
  | [], _, _, _ :: _, hl => by cases hl
  | _ :: _, _, _, [], hl => by cases hl

theorem updC_self (γ : Nat → Term) (x : Nat) : updC γ x (γ x) = γ :=
  funext fun y => by
    by_cases h : y = x
    · rw [updC, if_pos h, h]
    · rw [updC, if_neg h]

/-- Overriding formals with their own values changes nothing. -/
theorem overrideC_self : ∀ (γ : Nat → Term) (xs : List Nat), overrideC γ xs (xs.map γ) = γ
  | _, [] => rfl
  | γ, x :: xs => by
    show overrideC (updC γ x (γ x)) xs (xs.map γ) = γ
    rw [updC_self]
    exact overrideC_self γ xs

theorem overrideC_append : ∀ (γ : Nat → Term) (xs ys : List Nat) (as bs : List Term),
    as.length = xs.length → overrideC γ (xs ++ ys) (as ++ bs) = overrideC (overrideC γ xs as) ys bs
  | _, [], _, [], _, _ => rfl
  | γ, x :: xs, ys, a :: as, bs, hl => overrideC_append (updC γ x a) xs ys as bs (Nat.succ.inj hl)
  | _, [], _, _ :: _, _, hl => by cases hl
  | _, _ :: _, _, [], _, hl => by cases hl
