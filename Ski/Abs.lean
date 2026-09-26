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

/-- A term without the variable abstracts to a constant. -/
theorem abs_of_not_mem {x : Nat} : ∀ {t : OTerm}, t.mem x = false → abs x t = .K ⬝ₒ t
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var y, h => by
    have hne : y ≠ x := fun e => by rw [mem_var.mpr e] at h; cases h
    rw [abs_var, if_neg hne]
  | .app e f, h => by rw [abs_app, if_pos h]

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
