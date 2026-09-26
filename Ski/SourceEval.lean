import Ski.Simulation
open Term Front

set_option linter.unusedSectionVars false

/-!
# Source runs, by normal order

`sstep?` takes one step of the source semantics (`SStep`,
`Ski/Simulation.lean`) at the head of the spine, if the head is a
closure, equation or constructor with all its arguments, and
`sstep?_sound` proves every step it takes is an `SStep`.  `seval` iterates
it, stopping at a term with no head step, and `seval_sound` proves the
iteration a run (`SSteps`).  The semantics stays the relation: these are
proof search, the source-level counterpart of `iter` and `iter_sound`
(`Ski/Fuel.lean`), and a proof by `seval_sound (k := N) rfl` is checked
by re-running the steps on symbolic terms.

`SSteps.mono` carries a run to any program that defines the same globals
the same way, so a run proved for a small literal program holds for every
source file whose program contains it.
-/

namespace Cl

/-- The head of a term and its arguments. -/
def spine : Cl → Cl × List Cl
  | .app f a => ((spine f).1, (spine f).2 ++ [a])
  | c => (c, [])

theorem apps_append (f : Cl) : ∀ xs ys : List Cl, f.apps (xs ++ ys) = (f.apps xs).apps ys
  | [], _ => rfl
  | x :: xs, ys => apps_append (.app f x) xs ys

theorem spine_apps : ∀ c : Cl, c.spine.1.apps c.spine.2 = c
  | .app f a => by
    show (spine f).1.apps ((spine f).2 ++ [a]) = .app f a
    rw [apps_append, spine_apps f]
    rfl
  | .const _ => rfl
  | .gref _ => rfl
  | .clo _ _ _ _ => rfl

end Cl

section
variable {P : Nm → Option GDef}

theorem SStep.apps_left {f f' : Cl} (h : SStep P f f') : ∀ xs, SStep P (f.apps xs) (f'.apps xs)
  | [] => h
  | a :: as => SStep.apps_left (.left a h) as

theorem SSteps.single {c c' : Cl} (h : SStep P c c') : SSteps P c c' := .step h (.refl _)

theorem SSteps.trans {c c' c'' : Cl} (h : SSteps P c c') (h' : SSteps P c' c'') : SSteps P c c'' := by
  induction h with
  | refl _ => exact h'
  | step s _ ih => exact .step s (ih h')

theorem SSteps.left {f f' : Cl} (a : Cl) (h : SSteps P f f') : SSteps P (.app f a) (.app f' a) := by
  induction h with
  | refl _ => exact .refl _
  | step s _ ih => exact .step (.left a s) ih

theorem SSteps.right (f : Cl) {a a' : Cl} (h : SSteps P a a') : SSteps P (.app f a) (.app f a') := by
  induction h with
  | refl _ => exact .refl _
  | step s _ ih => exact .step (.right f s) ih

/-- A run carries to any program that defines what this one defines. -/
theorem SStep.mono {P' : Nm → Option GDef} (hP : ∀ n d, P n = some d → P' n = some d)
    {c c' : Cl} (h : SStep P c c') : SStep P' c c' := by
  induction h with
  | beta hl => exact .beta hl
  | delta hn hl => exact .delta (hP _ _ hn) hl
  | fix hn hl => exact .fix (hP _ _ hn) hl
  | ctor hn hj hf hk => exact .ctor (hP _ _ hn) hj hf hk
  | left a _ ih => exact .left a ih
  | right f _ ih => exact .right f ih

theorem SSteps.mono {P' : Nm → Option GDef} (hP : ∀ n d, P n = some d → P' n = some d)
    {c c' : Cl} (h : SSteps P c c') : SSteps P' c c' := by
  induction h with
  | refl _ => exact .refl _
  | step s _ ih => exact .step (s.mono hP) ih

end

/-- One step at the head of the spine, of a head applied to arguments. -/
def headStep (P : Nm → Option GDef) : Cl → List Cl → Option Cl
  | .clo caps ps b ρ, args =>
    if ps.length ≤ args.length then
      some ((inst (caps ++ ps) (overrideCl ρ ps (args.take ps.length)) b).apps
        (args.drop ps.length))
    else none
  | .gref n, args =>
    match P n with
    | some (.eqn ⟨ps, none, b⟩) =>
      if ps.length ≤ args.length then
        some ((inst ps (overrideCl junk ps (args.take ps.length)) b).apps (args.drop ps.length))
      else none
    | some (.eqn ⟨ps, some s, b⟩) =>
      if ps.length ≤ args.length then
        some ((inst (s :: ps) (overrideCl junk (s :: ps) (.gref n :: args.take ps.length)) b).apps
          (args.drop ps.length))
      else none
    | some (.ctor a j m) =>
      if j < m ∧ a + m ≤ args.length then
        some ((((args.drop a).take m).getD j (.const K)).apps (args.take a) |>.apps
          (args.drop (a + m)))
      else none
    | none => none
  | _, _ => none

theorem headStep_sound {P : Nm → Option GDef} :
    ∀ {hd : Cl} {args : List Cl} {c' : Cl}, headStep P hd args = some c' → SStep P (hd.apps args) c'
  | .clo caps ps b ρ, args, c', h => by
    by_cases hl : ps.length ≤ args.length
    · simp only [headStep, if_pos hl, Option.some.injEq] at h
      subst h
      have s := SStep.apps_left (SStep.beta (P := P) (caps := caps) (b := b) (ρ := ρ)
        (args := args.take ps.length) (List.length_take_of_le hl)) (args.drop ps.length)
      rw [← Cl.apps_append, List.take_append_drop] at s
      exact s
    · simp only [headStep, if_neg hl] at h
      cases h
  | .gref n, args, c', h => by
    cases hn : P n with
    | none => simp only [headStep, hn] at h; cases h
    | some d =>
      cases d with
      | eqn e =>
        cases e with
        | mk ps self b =>
          cases self with
          | none =>
            by_cases hl : ps.length ≤ args.length
            · simp only [headStep, hn, if_pos hl, Option.some.injEq] at h
              subst h
              have s := SStep.apps_left (SStep.delta (P := P) (args := args.take ps.length) hn
                (List.length_take_of_le hl)) (args.drop ps.length)
              rw [← Cl.apps_append, List.take_append_drop] at s
              exact s
            · simp only [headStep, hn, if_neg hl] at h
              cases h
          | some sf =>
            by_cases hl : ps.length ≤ args.length
            · simp only [headStep, hn, if_pos hl, Option.some.injEq] at h
              subst h
              have s := SStep.apps_left (SStep.fix (P := P) (args := args.take ps.length) hn
                (List.length_take_of_le hl)) (args.drop ps.length)
              rw [← Cl.apps_append, List.take_append_drop] at s
              exact s
            · simp only [headStep, hn, if_neg hl] at h
              cases h
      | ctor a j m =>
        by_cases hl : j < m ∧ a + m ≤ args.length
        · simp only [headStep, hn, if_pos hl, Option.some.injEq] at h
          subst h
          have ha : a ≤ args.length := Nat.le_trans (Nat.le_add_right a m) hl.2
          have hm : m ≤ (args.drop a).length := by rw [List.length_drop]; omega
          have st := SStep.apps_left (SStep.ctor (P := P) (fs := args.take a)
            (ks := (args.drop a).take m) hn hl.1 (List.length_take_of_le ha)
            (List.length_take_of_le hm)) ((args.drop a).drop m)
          rw [← Cl.apps_append, List.append_assoc, List.take_append_drop, List.take_append_drop,
            List.drop_drop] at st
          exact st
        · simp only [headStep, hn, if_neg hl] at h
          cases h
  | .const _, _, _, h => by cases h
  | .app _ _, _, _, h => by cases h

/-- **One source step**, at the head, by normal order. -/
def sstep? (P : Nm → Option GDef) (c : Cl) : Option Cl := headStep P c.spine.1 c.spine.2

theorem sstep?_sound {P : Nm → Option GDef} {c c' : Cl} (h : sstep? P c = some c') : SStep P c c' := by
  have s := headStep_sound h
  rw [Cl.spine_apps] at s
  exact s

/-- At most `k` source steps by normal order, stopping where none applies. -/
def seval (P : Nm → Option GDef) : Nat → Cl → Option Cl
  | 0, c => some c
  | k + 1, c =>
    match sstep? P c with
    | some c' => seval P k c'
    | none => some c

theorem seval_sound {P : Nm → Option GDef} : ∀ {k : Nat} {c c' : Cl},
    seval P k c = some c' → SSteps P c c'
  | 0, _, _, h => by cases h; exact .refl _
  | k + 1, c, c', h => by
    unfold seval at h
    split at h
    · rename_i c1 hc
      exact .step (sstep?_sound hc) (seval_sound h)
    · cases h
      exact .refl _

-- ---------------------------------------------------------------------------
-- Filling placeholders
-- ---------------------------------------------------------------------------

/-- Replace constants by `σ`'s values.  No source step creates a constant
    but `K` (`junk`) or looks inside one, so a run on terms with constant
    placeholders is a run on whatever fills them. -/
def Cl.substC (σ : Term → Option Cl) : Cl → Cl
  | .const t => (σ t).getD (.const t)
  | .gref n => .gref n
  | .clo caps ps b ρ => .clo caps ps b (fun i => (ρ i).substC σ)
  | .app f a => .app (f.substC σ) (a.substC σ)

section
variable {σ : Term → Option Cl}

theorem Cl.substC_apps : ∀ (f : Cl) (xs : List Cl),
    (f.apps xs).substC σ = (f.substC σ).apps (xs.map (Cl.substC σ))
  | _, [] => rfl
  | f, x :: xs => Cl.substC_apps (.app f x) xs

theorem inst_substC (sc : List Nat) (ρ : Nat → Cl) :
    ∀ b : CSrc, (inst sc ρ b).substC σ = inst sc (fun i => (ρ i).substC σ) b
  | .glob _ => rfl
  | .var _ => rfl
  | .app f a => by
    show Cl.app ((inst sc ρ f).substC σ) ((inst sc ρ a).substC σ) = _
    rw [inst_substC sc ρ f, inst_substC sc ρ a]
    rfl
  | .lam _ _ => rfl

theorem overrideCl_substC (ρ : Nat → Cl) :
    ∀ (xs : List Nat) (vs : List Cl) (i : Nat),
      (overrideCl ρ xs vs i).substC σ =
        overrideCl (fun j => (ρ j).substC σ) xs (vs.map (Cl.substC σ)) i
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, v :: vs, i => by
    show (overrideCl (updCl ρ x v) xs vs i).substC σ =
      overrideCl (updCl (fun j => (ρ j).substC σ) x (v.substC σ)) xs (vs.map (Cl.substC σ)) i
    rw [overrideCl_substC (updCl ρ x v) xs vs i]
    have e : (fun j => (updCl ρ x v j).substC σ) = updCl (fun j => (ρ j).substC σ) x (v.substC σ) :=
      funext fun j => by
        unfold updCl
        by_cases h : j = x
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
    rw [e]

theorem getD_map_substC (hK : σ K = none) :
    ∀ (ks : List Cl) (j : Nat),
      (ks.getD j (.const K)).substC σ = (ks.map (Cl.substC σ)).getD j (.const K)
  | [], _ => by
    show ((σ K).getD (.const K)) = .const K
    rw [hK]
    rfl
  | _ :: _, 0 => rfl
  | _ :: ks, j + 1 => getD_map_substC hK ks j

theorem junk_substC (hK : σ K = none) : (fun j => (junk j).substC σ) = junk :=
  funext fun _ => by
    show ((σ K).getD (.const K)) = .const K
    rw [hK]
    rfl

/-- **Runs survive filling placeholders.** -/
theorem SStep.substC {P : Nm → Option GDef} (hK : σ K = none) {c c' : Cl} (h : SStep P c c') :
    SStep P (c.substC σ) (c'.substC σ) := by
  induction h with
  | @beta caps ps b ρ args hl =>
    rw [Cl.substC_apps, inst_substC,
      show (fun i => (overrideCl ρ ps args i).substC σ) =
        overrideCl (fun j => (ρ j).substC σ) ps (args.map (Cl.substC σ)) from
        funext fun i => overrideCl_substC ρ ps args i]
    exact .beta (by rw [List.length_map]; exact hl)
  | @delta n ps b args hn hl =>
    rw [Cl.substC_apps, inst_substC,
      show (fun i => (overrideCl junk ps args i).substC σ) =
        overrideCl (fun j => (junk j).substC σ) ps (args.map (Cl.substC σ)) from
        funext fun i => overrideCl_substC junk ps args i, junk_substC hK]
    exact .delta hn (by rw [List.length_map]; exact hl)
  | @fix n s ps b args hn hl =>
    rw [Cl.substC_apps, inst_substC,
      show (fun i => (overrideCl junk (s :: ps) (.gref n :: args) i).substC σ) =
        overrideCl (fun j => (junk j).substC σ) (s :: ps) ((Cl.gref n :: args).map (Cl.substC σ)) from
        funext fun i => overrideCl_substC junk (s :: ps) (.gref n :: args) i, junk_substC hK]
    exact .fix hn (by rw [List.length_map]; exact hl)
  | @ctor n a j m fs ks hn hj hf hk =>
    rw [Cl.substC_apps, Cl.substC_apps, getD_map_substC hK, List.map_append]
    exact .ctor hn hj (by rw [List.length_map]; exact hf) (by rw [List.length_map]; exact hk)
  | left a _ ih => exact .left _ ih
  | right f _ ih => exact .right _ ih

theorem SSteps.substC {P : Nm → Option GDef} {c c' : Cl} (h : SSteps P c c') (hK : σ K = none) :
    SSteps P (c.substC σ) (c'.substC σ) := by
  induction h with
  | refl _ => exact .refl _
  | step s _ ih => exact .step (s.substC hK) ih

end

/-- The `i`-th placeholder: a closed constant other than `K`. -/
def holeT : Nat → Term
  | 0 => I ⬝ I
  | i + 1 => I ⬝ holeT i

def hole (i : Nat) : Cl := .const (holeT i)

/-- The placeholders filled with `vs`, in order. -/
def fill (vs : List Cl) : Term → Option Cl := fun t =>
  ((List.range vs.length).find? (fun i => holeT i == t)).map (fun i => vs.getD i (.const K))

theorem holeT_ne_K : ∀ i, (holeT i == K) = false
  | 0 => rfl
  | _ + 1 => rfl

theorem fill_K (vs : List Cl) : fill vs K = none := by
  unfold fill
  rw [List.find?_eq_none.mpr (fun i _ => by rw [holeT_ne_K]; exact Bool.false_ne_true)]
  rfl
