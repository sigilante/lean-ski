import Ski.Decode
import Ski.SmallLemma

open Term

/-!
# Values as probe trees

A value is read by probing (`Ski/Decode.lean`): apply the term to one
fresh variable per constructor of its type, see which variable the head
reduction reaches, then read that variable's arguments the same way.  This
module states that reading once, for any finite type of Scott data: a
**probe tree** `V.node c k ch` says the term's type has `k` constructors,
the term is the `c`-th, and its fields read as `ch`.

**The theorems.**
- `owsteps_spine`: a weak reduction ending in a variable applied to fields
  is head reduction to that variable applied to fields that weakly reduce
  to them, for any number of fields.  (`owsteps_var0` through
  `owsteps_var2` are its first cases.)
- `DecV.subst`, `DecV.of_owsteps`: reading moves along substitutions and is
  closed under backward weak reduction.
- `DecV.of_probe`: **one** probe at **one** fresh base, with fields that
  read, is a reading at every fresh base.  So a single run that probes at
  one block of markers suffices.
- `decodes_of_decV`: the probe tree of a number-valued outcome, read, is
  `Decodes` (`toV`).
-/

set_option linter.unusedSectionVars false

namespace Probe

variable [Kit]

-- ---------------------------------------------------------------------------
-- Weak reduction to a variable-headed spine, of any length
-- ---------------------------------------------------------------------------

/-- Pairwise weak reduction of two lists of terms. -/
inductive AllW : List OTerm → List OTerm → Prop
  | nil : AllW [] []
  | cons {a b : OTerm} {as bs : List OTerm} : OWSteps a b → AllW as bs → AllW (a :: as) (b :: bs)

theorem AllW.refl : ∀ (as : List OTerm), AllW as as
  | [] => .nil
  | a :: as => .cons (.refl a) (AllW.refl as)

theorem AllW.trans : ∀ {as bs cs : List OTerm}, AllW as bs → AllW bs cs → AllW as cs
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2 => .cons (h1.trans h2) (AllW.trans t1 t2)

theorem AllW.snoc : ∀ {as bs : List OTerm} {a b : OTerm}, AllW as bs → OWSteps a b →
    AllW (as ++ [a]) (bs ++ [b])
  | [], [], _, _, .nil, h => .cons h .nil
  | _ :: _, _ :: _, _, _, .cons h1 t1, h => .cons h1 (AllW.snoc t1 h)

theorem AllW.length : ∀ {as bs : List OTerm}, AllW as bs → as.length = bs.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ t => by simp [AllW.length t]

/-- An internal parallel step cannot change a variable-headed spine's head
    or length. -/
theorem _root_.OParI.spineN {c : Nat} (n : Nat) : ∀ (fs : List OTerm) {w : OTerm}, fs.length = n →
    OParI w (appL (.var c) fs) → ∃ fs', w = appL (.var c) fs' ∧ AllW fs' fs := by
  induction n with
  | zero =>
    intro fs w hl h
    rw [List.length_eq_zero_iff] at hl
    subst hl
    cases h
    exact ⟨[], rfl, .nil⟩
  | succ n ih =>
    intro fs w hl h
    have hne : fs ≠ [] := by intro e; subst e; cases hl
    rw [← List.dropLast_concat_getLast hne, appL_snoc] at h
    cases h with
    | app h1 hx =>
      obtain ⟨fs', e, hall⟩ := ih fs.dropLast (by rw [List.length_dropLast, hl]; rfl) h1
      subst e
      refine ⟨fs' ++ [_], by rw [appL_snoc], ?_⟩
      have := hall.snoc hx.wsteps
      rw [List.dropLast_concat_getLast hne] at this
      exact this

theorem _root_.OParI.spine {c : Nat} (fs : List OTerm) {w : OTerm} (h : OParI w (appL (.var c) fs)) :
    ∃ fs', w = appL (.var c) fs' ∧ AllW fs' fs :=
  _root_.OParI.spineN fs.length fs rfl h

theorem _root_.OParIs.spine {c : Nat} {w v : OTerm} (h : OParIs w v) :
    ∀ {fs : List OTerm}, v = appL (.var c) fs → ∃ fs', w = appL (.var c) fs' ∧ AllW fs' fs := by
  induction h with
  | refl _ => exact fun e => ⟨_, e, AllW.refl _⟩
  | step h _ ih =>
    intro fs e
    obtain ⟨fs1, e1, h1⟩ := ih e
    subst e1
    obtain ⟨fs0, e0, h0⟩ := h.spine fs1
    exact ⟨fs0, e0, h0.trans h1⟩

/-- **A weak reduction to a variable-headed spine** is head reduction to a
    spine with the same variable and as many fields, which weakly reduce to
    the given ones. -/
theorem owsteps_spine {t : OTerm} {c : Nat} {fs : List OTerm} (h : OWSteps t (appL (.var c) fs)) :
    ∃ fs', OSteps t (appL (.var c) fs') ∧ AllW fs' fs := by
  obtain ⟨t', h1, h2⟩ := owsteps_split h
  obtain ⟨fs', e, hall⟩ := h2.spine rfl
  exact ⟨fs', e ▸ h1, hall⟩

-- ---------------------------------------------------------------------------
-- Probe trees and their reading
-- ---------------------------------------------------------------------------

/-- **A probe tree**: the `c`-th of `k` constructors, with its fields' trees. -/
inductive V where
  | node (c k : Nat) (ch : List V)
  deriving Repr

mutual
  /-- **Reading a term as a probe tree**, at every fresh base. -/
  def DecV : OTerm → V → Prop
    | t, .node c k ch => ∀ b, Fresh b t → ∃ fs,
        OSteps (appO t (vars b) k) (appL (.var (c + b)) fs) ∧ DecVs fs ch
  def DecVs : List OTerm → List V → Prop
    | [], [] => True
    | f :: fs, v :: vs => DecV f v ∧ DecVs fs vs
    | _, _ => False
end

theorem subst_appL (τ : Nat → OTerm) : ∀ (t : OTerm) (fs : List OTerm),
    (appL t fs).subst τ = appL (t.subst τ) (fs.map (·.subst τ))
  | _, [] => rfl
  | t, f :: fs => subst_appL τ (t ⬝ₒ f) fs

mutual
  theorem DecV.subst : ∀ {v : V} {t : OTerm} (τ : Nat → OTerm), DecV t v → DecV (t.subst τ) v
    | .node c k ch, t, τ, h => by
      intro b _
      obtain ⟨b0, hb0⟩ := fresh_exists t
      obtain ⟨fs, hs, hd⟩ := h b0 hb0
      have e := probe_subst τ b hb0 hs
      rw [subst_appL, show (OTerm.var (c + b0)).subst (shiftAt τ b0 b) = .var (c + b)
        from shiftAt_at τ b0 b c] at e
      exact ⟨_, e, DecVs.subst _ hd⟩
  theorem DecVs.subst : ∀ {vs : List V} {fs : List OTerm} (τ : Nat → OTerm), DecVs fs vs →
      DecVs (fs.map (·.subst τ)) vs
    | [], [], _, _ => trivial
    | _ :: _, _ :: _, τ, ⟨h1, h2⟩ => ⟨DecV.subst τ h1, DecVs.subst τ h2⟩
    | [], _ :: _, _, h => h.elim
    | _ :: _, [], _, h => h.elim
end

mutual
  theorem DecV.of_owsteps : ∀ {v : V} {t u : OTerm}, OWSteps t u → DecV u v → DecV t v
    | .node c k ch, t, u, h, hu => by
      intro b hb
      obtain ⟨fs, hs, hd⟩ := hu b (hb.of_owsteps h)
      obtain ⟨fs', hs', hall⟩ := owsteps_spine ((_root_.OWSteps.appO _ h k).trans hs.weak)
      exact ⟨fs', hs', DecVs.of_allw hall hd⟩
  theorem DecVs.of_allw : ∀ {vs : List V} {fs' fs : List OTerm}, AllW fs' fs → DecVs fs vs →
      DecVs fs' vs
    | [], [], [], .nil, _ => trivial
    | _ :: _, _ :: _, _ :: _, .cons h1 t1, ⟨d1, d2⟩ => ⟨DecV.of_owsteps h1 d1, DecVs.of_allw t1 d2⟩
    | [], _ :: _, _ :: _, .cons _ _, h => h.elim
    | _ :: _, [], [], .nil, h => h.elim
end

/-- **One probe suffices**: a probe at one fresh base `b0` whose fields read
    is a reading at every fresh base. -/
theorem DecV.of_probe {t : OTerm} {c k b0 : Nat} {fs : List OTerm} {ch : List V}
    (hb0 : Fresh b0 t) (hs : OSteps (appO t (vars b0) k) (appL (.var (c + b0)) fs))
    (hd : DecVs fs ch) : DecV t (.node c k ch) := by
  intro b _
  have e := probe_subst OTerm.var b hb0 hs
  rw [subst_var, subst_appL, show (OTerm.var (c + b0)).subst (shiftAt OTerm.var b0 b) = .var (c + b)
    from shiftAt_at _ b0 b c] at e
  exact ⟨_, e, DecVs.subst _ hd⟩

-- ---------------------------------------------------------------------------
-- The trees of number-valued outcomes, and `Decodes`
-- ---------------------------------------------------------------------------

/-- `nat === Zero | Suc nat` -/
def natV : Nat → V
  | 0 => .node 0 2 []
  | n + 1 => .node 1 2 [natV n]

/-- A stack of numbers: `stack === Empty | Push item stack`, each item
    `Num n` (`item === Num nat | Quot quot`). -/
def stackV : List Nat → V
  | [] => .node 0 2 []
  | n :: s => .node 1 2 [.node 0 2 [natV n], stackV s]

/-- An item's number, if it is one. -/
def itemNum : Item → Option Nat
  | .num n => some n
  | .quot _ => none

/-- **The probe tree of an outcome** whose stack holds numbers:
    `result === RVal stack | RErr | RTime`. -/
def toV : Outcome → Option V
  | .err => some (.node 1 3 [])
  | .val s => (s.mapM itemNum).map fun ns => .node 0 3 [stackV ns]

theorem decNat_of_decV : ∀ {n : Nat} {t : OTerm}, DecV t (natV n) → DecNatO t n
  | 0, _, h => fun b hb => by
    obtain ⟨fs, hs, hd⟩ := h b hb
    cases fs with
    | nil => exact hs
    | cons _ _ => exact hd.elim
  | n + 1, _, h => fun b hb => by
    obtain ⟨fs, hs, hd⟩ := h b hb
    match fs, hd with
    | [f], ⟨hf, _⟩ => exact ⟨f, hs, decNat_of_decV hf⟩

theorem decStack_of_decV : ∀ {ns : List Nat} {t : OTerm}, DecV t (stackV ns) →
    DecStackO t (ns.map Item.num)
  | [], _, h => fun b hb => by
    obtain ⟨fs, hs, hd⟩ := h b hb
    cases fs with
    | nil => exact hs
    | cons _ _ => exact hd.elim
  | n :: ns, _, h => fun b hb => by
    obtain ⟨fs, hs, hd⟩ := h b hb
    match fs, hd with
    | [f, g], ⟨hf, hg, _⟩ =>
      refine ⟨f, g, hs, fun b' hb' => ?_, decStack_of_decV hg⟩
      obtain ⟨fs', hs', hd'⟩ := hf b' hb'
      match fs', hd' with
      | [f'], ⟨hf', _⟩ => exact ⟨f', hs', decNat_of_decV hf'⟩

theorem mapM_num : ∀ {s : List Item} {ns : List Nat},
    s.mapM itemNum = some ns → s = ns.map Item.num
  | [], ns, h => by simp at h; subst h; rfl
  | .num n :: s, ns, h => by
    cases hm : s.mapM itemNum with
    | none => simp [List.mapM_cons, hm, itemNum] at h
    | some ns' =>
      simp [List.mapM_cons, hm, itemNum] at h
      subst h
      rw [mapM_num hm]
      rfl
  | .quot _ :: _, _, h => by simp [List.mapM_cons, itemNum] at h

/-- **A probe tree of an outcome, read, is `Decodes`.** -/
theorem decodes_of_decV {o : Outcome} {v : V} (hv : toV o = some v) {t : Term}
    (h : DecV t.toO v) : Decodes t o := by
  cases o with
  | err =>
    cases hv
    intro b hb
    obtain ⟨fs, hs, hd⟩ := h b hb
    cases fs with
    | nil => exact hs
    | cons _ _ => exact hd.elim
  | val s =>
    simp only [toV] at hv
    cases hm : s.mapM itemNum with
    | none => rw [hm] at hv; cases hv
    | some ns =>
      rw [hm] at hv
      cases hv
      rw [mapM_num hm]
      intro b hb
      obtain ⟨fs, hs, hd⟩ := h b hb
      match fs, hd with
      | [f], ⟨hf, _⟩ => exact ⟨f, hs, decStack_of_decV hf⟩

end Probe
