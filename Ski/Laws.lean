import Ski.Apply
import Ski.Kernel
open Term

set_option linter.unusedSectionVars false

/-!
# The laws, for every table

G4 of `PLAN.md` §3.  `KitElim`, `KitWords` and `KitApply` hold for the
kit compiled from every table whose static quotations' bodies are valid
over it (`Table.kit_elim`, `Table.kit_words`, `Table.kit_apply`).  One
proof covers every table `skijack` emits; `Ski/Table.lean` checks only
that each generated table's terms are `Table.kit`'s (`table_*`) and that
the table is valid (`table_valid`).

## β for compiled source

Every law is β-reduction of compiled source.  `absN_beta_close`
(`Ski/Abs.lean`) reduces a bracket abstraction applied to all its formals
to its body, under any closing substitution.  `Src.ev` reads a closed
compiled term down to its λs: a global is itself, a variable is its
value, an application is an application, and a λ is its compiled term;
`close_comp_ev` says compiling then closing is `Src.ev`.  `lam1_beta` and
`lam2_beta` are β for a compiled λ of one or two parameters: the lifted
combinator, applied to its captured binders and then to its parameters,
reduces to its body with the parameters bound and the captures as they
were.  No scoping condition is needed.  The substitution overrides the
formals and keeps every other variable, which is what λ-lifting followed
by bracket abstraction computes.

## The laws

- `KitElim`: `ctor_beta` reduces the constructor at position `j` of `m`,
  applied to its fields and `m` continuations under any substitution, to
  continuation `j` applied to the fields, on open terms, as the decode
  relation's probes need.
- `KitWords`: `unit`, `cons` and `cat`, stage by stage
  (`Table.wUnit_stages` and its siblings).
- `KitApply`: `applyU` unrolls through `Y` by head reduction
  (`kit_applyU_unfold`); its body reduces to the scrutinee applied to the
  static arms `b_k self s` and three compiled λs (`applySrc_ev`,
  `armCons_beta` and its siblings); each static quotation's term reduces
  to `N` of its words (`kit_body_compiles`).

Every run here is a weak reduction.  Head reduction alone does not reach
the substituted body: `S A B x` leaves `B x` in argument position,
unreduced.  The consumers accept weak runs: decoding and `Contract` are
closed under backward weak reduction (G1b), and the converse's measure
does not grow under it (`StepsN.wtail`, `Ski/Converse.lean`).
-/

-- ---------------------------------------------------------------------------
-- Compiled source, closed
-- ---------------------------------------------------------------------------

def Src.isLam : Src → Bool
  | .lam _ _ => true
  | _ => false

/-- A compiled source term closed by `γ`, read down to its λs: globals are
    themselves, variables are `γ`'s, and a λ is its compiled term. -/
def Src.ev (sc : List Nat) (γ : Nat → Term) : Src → Term
  | .glob t => t
  | .var x => γ x
  | .app f a => Src.ev sc γ f ⬝ Src.ev sc γ a
  | .lam x b => (comp sc (.lam x b)).close γ

theorem close_comp_ev (sc : List Nat) (γ : Nat → Term) :
    ∀ e : Src, (comp sc e).close γ = e.ev sc γ
  | .glob t => close_toO γ t
  | .var _ => rfl
  | .app f a => by
    show Term.app ((comp sc f).close γ) ((comp sc a).close γ) = _
    rw [close_comp_ev sc γ f, close_comp_ev sc γ a]
    rfl
  | .lam _ _ => rfl

theorem compLam_body {caps ps : List Nat} : ∀ {e : Src}, e.isLam = false →
    compLam caps ps e = wrapLift caps ps (comp (caps ++ ps) e)
  | .glob _, _ => rfl
  | .var _, _ => rfl
  | .app _ _, _ => rfl
  | .lam _ _, h => by cases h

/-- A lifted combinator, applied to its parameters, weakly reduces to its
    body with the captured binders as they were and the parameters bound. -/
theorem wrapLift_beta (caps ps : List Nat) (B : OTerm) (γ : Nat → Term) (Ns : List Term)
    (hl : Ns.length = ps.length) :
    WSteps (appT ((wrapLift caps ps B).close γ) Ns) (B.close (overrideC γ ps Ns)) := by
  have e1 : (wrapLift caps ps B).close γ = appT ((absN (caps ++ ps) B).close γ) (caps.map γ) := by
    unfold wrapLift
    rw [close_appL, List.map_map]
    rfl
  have h := absN_beta_close (caps ++ ps) B γ (caps.map γ ++ Ns)
    (by rw [List.length_append, List.length_append, List.length_map, hl])
  rw [overrideC_append γ caps ps (caps.map γ) Ns (List.length_map _), overrideC_self] at h
  rw [e1, ← appT_append]
  exact h

/-- **β for a compiled λ of one parameter.** -/
theorem lam1_beta {sc : List Nat} {x : Nat} {b : Src} (hb : b.isLam = false)
    (γ : Nat → Term) (N : Term) :
    ∃ sc', WSteps ((comp sc (.lam x b)).close γ ⬝ N) (b.ev sc' (updC γ x N)) := by
  have h := wrapLift_beta (sc.filter fun s => (Src.lam x b).occurs s) [x]
    (comp ((sc.filter fun s => (Src.lam x b).occurs s) ++ [x]) b) γ [N] rfl
  rw [← compLam_body hb, close_comp_ev] at h
  exact ⟨_, h⟩

/-- **β for a compiled λ of two parameters.** -/
theorem lam2_beta {sc : List Nat} {x y : Nat} {b : Src} (hb : b.isLam = false)
    (γ : Nat → Term) (N1 N2 : Term) :
    ∃ sc', WSteps ((comp sc (.lam x (.lam y b))).close γ ⬝ N1 ⬝ N2)
      (b.ev sc' (updC (updC γ x N1) y N2)) := by
  have h := wrapLift_beta (sc.filter fun s => (Src.lam x (.lam y b)).occurs s) [x, y]
    (comp ((sc.filter fun s => (Src.lam x (.lam y b)).occurs s) ++ [x, y]) b) γ [N1, N2] rfl
  rw [← compLam_body hb, close_comp_ev] at h
  exact ⟨_, h⟩

/-- β for a definition of one formal. -/
theorem compDef1_beta (x : Nat) (body : Src) (s : Term) :
    WSteps (toTerm (compDef [x] body) ⬝ s) (body.ev [x] (updC (fun _ => K) x s)) := by
  have h := absN_beta_close [x] (comp [x] body) (fun _ => K) [s] rfl
  rw [close_comp_ev] at h
  exact h

-- ---------------------------------------------------------------------------
-- Scott constructors, open
-- ---------------------------------------------------------------------------

theorem appL_append (t : OTerm) : ∀ as bs, appL t (as ++ bs) = appL (appL t as) bs
  | [], _ => rfl
  | a :: as, bs => appL_append (t ⬝ₒ a) as bs

theorem subst_appL (σ : Nat → OTerm) : ∀ (t : OTerm) (as : List OTerm),
    (appL t as).subst σ = appL (t.subst σ) (as.map (OTerm.subst σ))
  | _, [] => rfl
  | t, a :: as => subst_appL σ (t ⬝ₒ a) as

theorem appO_eq (t : OTerm) (ks : Nat → OTerm) : ∀ m, appO t ks m = appL t ((List.range m).map ks)
  | 0 => rfl
  | m + 1 => by
    have e : List.range (m + 1) = List.range m ++ [m] := List.range_succ
    rw [e, List.map_append, appL_append, ← appO_eq t ks m]
    rfl

theorem override_append : ∀ (ρ : Nat → OTerm) (xs ys : List Nat) (as bs : List OTerm),
    as.length = xs.length → override ρ (xs ++ ys) (as ++ bs) = override (override ρ xs as) ys bs
  | _, [], _, [], _, _ => rfl
  | ρ, x :: xs, ys, a :: as, bs, hl => override_append (upd ρ x a) xs ys as bs (Nat.succ.inj hl)
  | _, [], _, _ :: _, _, hl => by cases hl
  | _, _ :: _, _, [], _, hl => by cases hl

theorem override_range (ρ F : Nat → OTerm) : ∀ L,
    override ρ (List.range L) ((List.range L).map F) = fun y => if y < L then F y else ρ y
  | 0 => funext fun y => (if_neg (Nat.not_lt_zero y)).symm
  | L + 1 => by
    have e : List.range (L + 1) = List.range L ++ [L] := List.range_succ
    rw [e, List.map_append, override_append ρ _ _ _ _ (List.length_map _), override_range ρ F L]
    funext y
    show (if y = L then F L else if y < L then F y else ρ y) = if y < L + 1 then F y else ρ y
    by_cases h1 : y = L
    · rw [if_pos h1, if_pos (by omega), h1]
    · by_cases h2 : y < L
      · rw [if_neg h1, if_pos h2, if_pos (by omega)]
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]

/-- **A Scott constructor eliminates**: the constructor at position `j` of
    `m`, with `a` fields, under any substitution, applied to its fields and
    `m` continuations, weakly reduces to continuation `j` applied to the
    fields. -/
theorem ctor_beta (a j m : Nat) (hj : j < m) (ρ F : Nat → OTerm) :
    OWSteps (appL ((ctorO a j m).subst ρ) ((List.range (a + m)).map F))
      (appL (F (a + j)) ((List.range a).map F)) := by
  have h := absN_beta_subst (List.range (a + m)) (appL (.var (a + j)) ((List.range a).map .var)) ρ
    ((List.range (a + m)).map F) (List.length_map _)
  rw [override_range, subst_appL, List.map_map] at h
  have e1 : (OTerm.var (a + j)).subst (fun y => if y < a + m then F y else ρ y) = F (a + j) :=
    if_pos (by omega)
  have e2 : (List.range a).map (OTerm.subst (fun y => if y < a + m then F y else ρ y) ∘ OTerm.var) =
      (List.range a).map F :=
    List.map_congr_left fun i hi => if_pos (by have := List.mem_range.mp hi; omega)
  rw [e1, e2] at h
  exact h

namespace Table

variable (tb : Table)

theorem wUnit_stages (s : Term) : ∃ c1,
    WSteps (tb.wUnit ⬝ s) (s ⬝ Scott.RErr ⬝ c1) ∧
    ∀ f g, WSteps (c1 ⬝ f ⬝ g) (Scott.RVal ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ (tb.QUnit ⬝ f)) ⬝ g)) :=
  ⟨_, compDef1_beta 0 (KernelSrc.wUnit tb.QUnit) s, fun f g =>
    match lam2_beta rfl _ f g with
    | ⟨_, h⟩ => h⟩

theorem wQcons_stages (s : Term) : ∃ c1,
    WSteps (tb.wQcons ⬝ s) (s ⬝ Scott.RErr ⬝ c1) ∧
    ∀ f g, ∃ e0 e1, WSteps (c1 ⬝ f ⬝ g) (f ⬝ e0 ⬝ e1) ∧ (∀ n, WSteps (e0 ⬝ n) Scott.RErr) ∧
      ∀ x, ∃ d1, WSteps (e1 ⬝ x) (g ⬝ Scott.RErr ⬝ d1) ∧
        ∀ f2 g2, WSteps (d1 ⬝ f2 ⬝ g2)
          (Scott.RVal ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ (tb.QCons ⬝ f2 ⬝ x)) ⬝ g2)) :=
  ⟨_, compDef1_beta 0 (KernelSrc.wQcons tb.QCons) s, fun f g =>
    match lam2_beta rfl _ f g with
    | ⟨_, h⟩ => ⟨_, _, h,
      fun n => match lam1_beta rfl _ n with | ⟨_, h1⟩ => h1,
      fun x => match lam1_beta rfl _ x with
        | ⟨_, h1⟩ => ⟨_, h1, fun f2 g2 => match lam2_beta rfl _ f2 g2 with | ⟨_, h2⟩ => h2⟩⟩⟩

theorem wCat_stages (s : Term) : ∃ c1,
    WSteps (tb.wCat ⬝ s) (s ⬝ Scott.RErr ⬝ c1) ∧
    ∀ f g, ∃ e0 e1, WSteps (c1 ⬝ f ⬝ g) (f ⬝ e0 ⬝ e1) ∧ (∀ n, WSteps (e0 ⬝ n) Scott.RErr) ∧
      ∀ x, ∃ d1, WSteps (e1 ⬝ x) (g ⬝ Scott.RErr ⬝ d1) ∧
        ∀ f2 g2, ∃ e0' e1', WSteps (d1 ⬝ f2 ⬝ g2) (f2 ⬝ e0' ⬝ e1') ∧
          (∀ n, WSteps (e0' ⬝ n) Scott.RErr) ∧
          ∀ y, WSteps (e1' ⬝ y) (Scott.RVal ⬝ (Scott.Push ⬝
            (Scott.Quot ⬝ (tb.QCons ⬝ (Scott.Quot ⬝ y) ⬝ (tb.QThen ⬝ x))) ⬝ g2)) :=
  ⟨_, compDef1_beta 0 (KernelSrc.wCat tb.QCons tb.QThen) s, fun f g =>
    match lam2_beta rfl _ f g with
    | ⟨_, h⟩ => ⟨_, _, h,
      fun n => match lam1_beta rfl _ n with | ⟨_, h1⟩ => h1,
      fun x => match lam1_beta rfl _ x with
        | ⟨_, h1⟩ => ⟨_, h1, fun f2 g2 => match lam2_beta rfl _ f2 g2 with
          | ⟨_, h2⟩ => ⟨_, _, h2,
            fun n => match lam1_beta rfl _ n with | ⟨_, h3⟩ => h3,
            fun y => match lam1_beta rfl _ y with | ⟨_, h3⟩ => h3⟩⟩⟩⟩

-- ---------------------------------------------------------------------------
-- The table's constructors
-- ---------------------------------------------------------------------------

/-- **`KitElim` for every table.** -/
theorem kit_elim : @KitElim tb.kit :=
  @KitElim.mk tb.kit
  (fun k hk ks => by
    have hk' : k < tb.n := hk
    show OWSteps (appO (toTerm (ctorO 0 k (tb.n + 3))).toO ks (tb.n + 3)) (ks k)
    have h := ctor_beta 0 k (tb.n + 3) (by omega) (fun _ => (K : Term).toO) ks
    rw [Nat.zero_add, Nat.zero_add] at h
    rw [toTerm, toO_close, appO_eq]
    exact h)
  (fun x r ks => by
    show OWSteps (appO ((toTerm (ctorO 2 tb.n (tb.n + 3))).toO ⬝ₒ x ⬝ₒ r) ks (tb.n + 3))
      (ks tb.n ⬝ₒ x ⬝ₒ r)
    let F : Nat → OTerm := fun y => match y with
      | 0 => x
      | 1 => r
      | y + 2 => ks y
    have hF : ∀ i, F (2 + i) = ks i := fun i => by rw [Nat.add_comm]
    have e : (List.range (2 + (tb.n + 3))).map F = [x, r] ++ (List.range (tb.n + 3)).map ks := by
      rw [List.range_add, List.map_append, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => hF i
    have h := ctor_beta 2 tb.n (tb.n + 3) (by omega) (fun _ => (K : Term).toO) F
    rw [e, hF tb.n] at h
    rw [toTerm, toO_close, appO_eq]
    exact h)
  (fun x ks => by
    show OWSteps (appO ((toTerm (ctorO 1 (tb.n + 1) (tb.n + 3))).toO ⬝ₒ x) ks (tb.n + 3))
      (ks (tb.n + 1) ⬝ₒ x)
    let F : Nat → OTerm := fun y => match y with
      | 0 => x
      | y + 1 => ks y
    have hF : ∀ i, F (1 + i) = ks i := fun i => by rw [Nat.add_comm]
    have e : (List.range (1 + (tb.n + 3))).map F = [x] ++ (List.range (tb.n + 3)).map ks := by
      rw [List.range_add, List.map_append, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => hF i
    have h := ctor_beta 1 (tb.n + 1) (tb.n + 3) (by omega) (fun _ => (K : Term).toO) F
    rw [e, hF (tb.n + 1)] at h
    rw [toTerm, toO_close, appO_eq]
    exact h)
  (fun x ks => by
    show OWSteps (appO ((toTerm (ctorO 1 (tb.n + 2) (tb.n + 3))).toO ⬝ₒ x) ks (tb.n + 3))
      (ks (tb.n + 2) ⬝ₒ x)
    let F : Nat → OTerm := fun y => match y with
      | 0 => x
      | y + 1 => ks y
    have hF : ∀ i, F (1 + i) = ks i := fun i => by rw [Nat.add_comm]
    have e : (List.range (1 + (tb.n + 3))).map F = [x] ++ (List.range (tb.n + 3)).map ks := by
      rw [List.range_add, List.map_append, List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => hF i
    have h := ctor_beta 1 (tb.n + 2) (tb.n + 3) (by omega) (fun _ => (K : Term).toO) F
    rw [e, hF (tb.n + 2)] at h
    rw [toTerm, toO_close, appO_eq]
    exact h)

/-- **`KitWords` for every table.** -/
theorem kit_words : @KitWords tb.kit :=
  @KitWords.mk tb.kit tb.wUnit_stages tb.wQcons_stages tb.wCat_stages

-- ---------------------------------------------------------------------------
-- The table's `apply`
-- ---------------------------------------------------------------------------

/-- Continuations `0 … n + 2` of `applyU`'s case: the static arms, then three. -/
def armsK (n : Nat) (arms : Nat → Term) (c3 c5 c6 : Term) : Nat → Term :=
  fun k => if k < n then arms k else if k = n then c3 else if k = n + 1 then c5 else c6

theorem appF_agree (t : Term) {ks ks' : Nat → Term} :
    ∀ n, (∀ k, k < n → ks k = ks' k) → appF t ks n = appF t ks' n
  | 0, _ => rfl
  | n + 1, h => by
    show appF t ks n ⬝ ks n = appF t ks' n ⬝ ks' n
    rw [appF_agree t n (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

theorem armsK_lt {n k : Nat} {arms : Nat → Term} {c3 c5 c6 : Term} (hk : k < n) :
    armsK n arms c3 c5 c6 k = arms k := if_pos hk

theorem armsK_n (n : Nat) (arms : Nat → Term) (c3 c5 c6 : Term) :
    armsK n arms c3 c5 c6 n = c3 := by
  show (if n < n then arms n else if n = n then c3 else if n = n + 1 then c5 else c6) = c3
  rw [if_neg (Nat.lt_irrefl n), if_pos rfl]

theorem armsK_n1 (n : Nat) (arms : Nat → Term) (c3 c5 c6 : Term) :
    armsK n arms c3 c5 c6 (n + 1) = c5 := by
  show (if n + 1 < n then arms (n + 1) else if n + 1 = n then c3
    else if n + 1 = n + 1 then c5 else c6) = c5
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem armsK_n2 (n : Nat) (arms : Nat → Term) (c3 c5 c6 : Term) :
    armsK n arms c3 c5 c6 (n + 2) = c6 := by
  show (if n + 2 < n then arms (n + 2) else if n + 2 = n then c3
    else if n + 2 = n + 1 then c5 else c6) = c6
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem appF_armsK (t : Term) (n : Nat) (arms : Nat → Term) (c3 c5 c6 : Term) :
    appF t (armsK n arms c3 c5 c6) (n + 3) = appF t arms n ⬝ c3 ⬝ c5 ⬝ c6 := by
  show appF t (armsK n arms c3 c5 c6) n ⬝ armsK n arms c3 c5 c6 n ⬝
    armsK n arms c3 c5 c6 (n + 1) ⬝ armsK n arms c3 c5 c6 (n + 2) = _
  rw [appF_agree t n (fun k hk => armsK_lt hk), armsK_n, armsK_n1, armsK_n2]

/-- The static arms of `applySrc`, folded, read as `appF`. -/
theorem ev_arms (sc : List Nat) (γ : Nat → Term) : ∀ n,
    Src.ev sc γ ((List.range n).foldl
      (fun acc k => acc ⬝ₛ (.glob (tb.bodyT k) ⬝ₛ .var 0 ⬝ₛ .var 2)) (.var 1)) =
    appF (γ 1) (fun k => tb.bodyT k ⬝ γ 0 ⬝ γ 2) n
  | 0 => rfl
  | n + 1 => by
    have e : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [e, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Src.ev]
    rw [ev_arms sc γ n]
    rfl

/-- `applySrc`, closed: the scrutinee applied to the static arms and the
    three compiled λs. -/
theorem applySrc_ev (sc : List Nat) (γ : Nat → Term) :
    tb.applySrc.ev sc γ = appF (γ 1) (fun k => tb.bodyT k ⬝ γ 0 ⬝ γ 2) tb.n ⬝
      KernelSrc.armCons.ev sc γ ⬝ KernelSrc.armUnit.ev sc γ ⬝ KernelSrc.armThen.ev sc γ := by
  unfold Table.applySrc
  simp only [Src.ev]
  rw [ev_arms]

theorem armCons_beta (sc : List Nat) (γ : Nat → Term) (x r : Term) :
    WSteps (KernelSrc.armCons.ev sc γ ⬝ x ⬝ r) (γ 0 ⬝ r ⬝ (Scott.Push ⬝ x ⬝ γ 2)) :=
  match lam2_beta rfl γ x r with
  | ⟨_, h⟩ => h

theorem armUnit_beta (sc : List Nat) (γ : Nat → Term) (x : Term) :
    WSteps (KernelSrc.armUnit.ev sc γ ⬝ x) (Scott.RVal ⬝ (Scott.Push ⬝ x ⬝ γ 2)) :=
  match lam1_beta rfl γ x with
  | ⟨_, h⟩ => h

theorem armThen_beta (sc : List Nat) (γ : Nat → Term) (b : Term) :
    WSteps (KernelSrc.armThen.ev sc γ ⬝ b) (Scott.seq ⬝ (Scott.wDo ⬝ γ 0) ⬝ (γ 0 ⬝ b) ⬝ γ 2) :=
  match lam1_beta rfl γ b with
  | ⟨_, h⟩ => h

theorem kit_applyU_unfold (fq fs : Term) :
    Steps (tb.applyU ⬝ fq ⬝ fs) (fixSelf (@applyF tb.kit) (fixB (@applyF tb.kit)) ⬝ fq ⬝ fs) :=
  Steps.left fs (@fix_unfold tb.kit tb.kit_elim tb.kit_words _ fq)

theorem kit_applyF_stages (R q s : Term) : ∃ ks : Nat → Term,
    WSteps (@applyF tb.kit ⬝ R ⬝ q ⬝ s) (appF q ks (tb.n + 3)) ∧
    (∀ k, k < tb.n → WSteps (ks k) (tb.bodyT k ⬝ R ⬝ s)) ∧
    (∀ x r, WSteps (ks tb.n ⬝ x ⬝ r) (R ⬝ r ⬝ (Scott.Push ⬝ x ⬝ s))) ∧
    (∀ x, WSteps (ks (tb.n + 1) ⬝ x) (Scott.RVal ⬝ (Scott.Push ⬝ x ⬝ s))) ∧
    (∀ b, WSteps (ks (tb.n + 2) ⬝ b) (Scott.seq ⬝ (Scott.wDo ⬝ R) ⬝ (R ⬝ b) ⬝ s)) := by
  have h0 := absN_beta_close [0, 1, 2] (comp [0, 1, 2] tb.applySrc) (fun _ => K) [R, q, s] rfl
  rw [close_comp_ev] at h0
  rw [applySrc_ev] at h0
  let γ := overrideC (fun _ => K) [0, 1, 2] [R, q, s]
  refine ⟨armsK tb.n (fun k => tb.bodyT k ⬝ R ⬝ s) (KernelSrc.armCons.ev [0, 1, 2] γ)
    (KernelSrc.armUnit.ev [0, 1, 2] γ) (KernelSrc.armThen.ev [0, 1, 2] γ), ?_, ?_, ?_, ?_, ?_⟩
  · rw [appF_armsK]
    exact h0
  · intro k hk
    rw [armsK_lt hk]
    exact .refl _
  · intro x r
    rw [armsK_n]
    exact armCons_beta [0, 1, 2] γ x r
  · intro x
    rw [armsK_n1]
    exact armUnit_beta [0, 1, 2] γ x
  · intro b
    rw [armsK_n2]
    exact armThen_beta [0, 1, 2] γ b

mutual
  theorem encItem_eq : ∀ x : Item, tb.encItem x = @_root_.encItem tb.kit x
    | .num _ => rfl
    | .quot q => by
      show Scott.Quot ⬝ tb.encQuot q = Scott.Quot ⬝ @_root_.encQuot tb.kit q
      rw [encQuot_eq q]
  theorem encQuot_eq : ∀ q : Quotation, tb.encQuot q = @_root_.encQuot tb.kit q
    | .stat _ => rfl
    | .cons x r => by
      show tb.QCons ⬝ tb.encItem x ⬝ tb.encQuot r = tb.QCons ⬝ @_root_.encItem tb.kit x ⬝ @_root_.encQuot tb.kit r
      rw [encItem_eq x, encQuot_eq r]
    | .unit x => by
      show tb.QUnit ⬝ tb.encItem x = tb.QUnit ⬝ @_root_.encItem tb.kit x
      rw [encItem_eq x]
    | .then r => by
      show tb.QThen ⬝ tb.encQuot r = tb.QThen ⬝ @_root_.encQuot tb.kit r
      rw [encQuot_eq r]
end

-- The table's words are compared as constants here; unfolding them is costly
-- and never needed.
attribute [local irreducible] Table.wQcons Table.wCat Table.wUnit in
theorem ev_wordSrc (sc : List Nat) (γ : Nat → Term) : ∀ w : Word,
    (tb.wordSrc w).ev sc γ = @wordTerm tb.kit (γ 0) w
  | .dup => rfl
  | .swap => rfl
  | .pop => rfl
  | .cons => rfl
  | .cat => rfl
  | .unit => rfl
  | .dip => rfl
  | .i => rfl
  | .ifz => rfl
  | .lit _ => rfl
  | .quote q => by
    show Scott.wQuote ⬝ tb.encQuot q = Scott.wQuote ⬝ @_root_.encQuot tb.kit q
    rw [encQuot_eq]
  | .add => rfl

theorem ev_bodySrc (sc : List Nat) (γ : Nat → Term) : ∀ p : List Word,
    (tb.bodySrc p).ev sc γ = @N tb.kit (γ 0) p
  | [] => rfl
  | [w] => tb.ev_wordSrc sc γ w
  | w :: w' :: p => by
    show Scott.seq ⬝ (tb.wordSrc w).ev sc γ ⬝ (tb.bodySrc (w' :: p)).ev sc γ =
      Scott.seq ⬝ @wordTerm tb.kit (γ 0) w ⬝ @N tb.kit (γ 0) (w' :: p)
    rw [tb.ev_wordSrc sc γ w, ev_bodySrc sc γ (w' :: p)]

/-- Each static quotation's compiled term runs to its body's compiled form. -/
theorem kit_body_compiles (k : Nat) (R : Term) :
    WSteps (tb.bodyT k ⬝ R) (@N tb.kit R (tb.body k)) := by
  have h := compDef1_beta 0 (tb.bodySrc (tb.body k)) R
  rw [ev_bodySrc] at h
  exact h

/-- A table is valid when every static quotation's body is valid over it. -/
def Valid : Prop := ∀ k, k < tb.n → (tb.body k).all (Word.ok tb.n) = true

/-- **`KitApply` for every valid table.** -/
theorem kit_apply (h : tb.Valid) : @KitApply tb.kit tb.kit_elim tb.kit_words :=
  @KitApply.mk tb.kit tb.kit_elim tb.kit_words tb.kit_applyU_unfold tb.kit_applyF_stages
    (fun k _ R => tb.kit_body_compiles k R) h

end Table
