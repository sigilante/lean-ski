import Ski.HnfCertBase
open Term

/-!
# Semantics of claim terms and run terms

* `Inst c u`: the closed pure-S term `u` is an instance of the claim term `c` (each variable of
  state `s` is replaced by some pure term of code `s`).
* `InstR sz t u`: `u` is an instance of the run term `t`; every leaf's instance has size at most
  its form evaluated at the root sizes `sz`, and every cached state is the code of the instance.
-/

namespace HnfCert
open HnfS HnfSound HnfProd HnfCertLaws HnfB0 HnfQ5

def Inst : CT → Term → Prop
  | .S, u => u = S
  | .V s, u => PureS u ∧ pst u = s
  | .A l r, u => ∃ a b, u = a ⬝ b ∧ Inst l a ∧ Inst r b

theorem Inst.pure : ∀ {c : CT} {u : Term}, Inst c u → PureS u
  | .S, _, h => h ▸ .S
  | .V _, _, h => h.1
  | .A _ _, _, ⟨_, _, rfl, ha, hb⟩ => .app ha.pure hb.pure

theorem Inst.st : ∀ {c : CT} {u : Term}, Inst c u → c.st = pst u
  | .S, _, h => by subst h; rfl
  | .V _, _, h => h.2.symm
  | .A _ _, _, ⟨_, _, rfl, ha, hb⟩ => by
    simp only [CT.st]; rw [ha.st, hb.st, pst_app ha.pure hb.pure]

theorem mkV_zero : mkV 0 = .S := rfl
theorem mkV_ne {s : Nat} (h : (s == 0) = false) : mkV s = .V s := by unfold mkV; rw [h]; rfl
theorem mkVR_zero (f : Option Form) : mkVR 0 f = .S := rfl
theorem mkVR_ne {s : Nat} (f : Option Form) (h : (s == 0) = false) : mkVR s f = .V s f := by
  unfold mkVR; rw [h]; rfl

theorem inst_mkV {u : Term} (hu : PureS u) : Inst (mkV (pst u)) u :=
  if h : pst u = 0 then by
    rw [h, mkV_zero]; exact eq_S_of_pst hu h
  else by
    have : (pst u == 0) = false := by simp [h]
    rw [mkV_ne this]; exact ⟨hu, rfl⟩

/-! ## Run terms -/

def InstR (sz : Sz) : RT → Term → Prop
  | .S, u => u = S
  | .V s f, u => PureS u ∧ pst u = s ∧ ∀ g, f = some g → (tsz u : Int) ≤ g.eval sz
  | .A l r s, u => ∃ a b, u = a ⬝ b ∧ InstR sz l a ∧ InstR sz r b ∧ s = pst u

theorem InstR.pure {sz : Sz} : ∀ {t : RT} {u : Term}, InstR sz t u → PureS u
  | .S, _, h => h ▸ .S
  | .V _ _, _, h => h.1
  | .A _ _ _, _, ⟨_, _, rfl, ha, hb, _⟩ => .app ha.pure hb.pure

theorem InstR.st {sz : Sz} : ∀ {t : RT} {u : Term}, InstR sz t u → t.st = pst u
  | .S, _, h => by subst h; rfl
  | .V _ _, _, h => h.2.1.symm
  | .A _ _ _, _, ⟨_, _, _, _, _, h⟩ => h

theorem mkA_inst {sz : Sz} {l r : RT} {a b : Term} (ha : InstR sz l a) (hb : InstR sz r b) :
    InstR sz (mkA l r) (a ⬝ b) := by
  refine ⟨a, b, rfl, ha, hb, ?_⟩
  rw [ha.st, hb.st, pst_app ha.pure hb.pure]

theorem mkVR_inst {sz : Sz} {s : Nat} {f : Option Form} {u : Term} (hu : PureS u) (hs : pst u = s)
    (hf : ∀ g, f = some g → (tsz u : Int) ≤ g.eval sz) : InstR sz (mkVR s f) u :=
  if h : s = 0 then by
    subst h; rw [mkVR_zero]; exact eq_S_of_pst hu hs
  else by
    have : (s == 0) = false := by simp [h]
    rw [mkVR_ne f this]; exact ⟨hu, hs, hf⟩

theorem eval_const (c : Int) (sz : Sz) : (Form.const c).eval sz = c := by
  simp [Form.const, Form.eval]

theorem eval_add (a b : Form) (sz : Sz) : (a.add b).eval sz = a.eval sz + b.eval sz := by
  simp only [Form.add, Form.eval, Int.add_mul]; omega

theorem eval_shift (a : Form) (k : Int) (sz : Sz) : (a.shift k).eval sz = a.eval sz + k := by
  simp only [Form.shift, Form.eval]; omega

/-- Size forms bound the sizes of instances. -/
theorem sz_bound {sz : Sz} : ∀ {t : RT} {u : Term} {g : Form}, InstR sz t u → t.sz = some g →
    (tsz u : Int) ≤ g.eval sz
  | .S, _, g, h, hg => by
    subst h; simp only [RT.sz, Option.some.injEq] at hg; subst hg; rw [eval_const]; simp [tsz]
  | .V _ _, _, g, h, hg => h.2.2 g hg
  | .A l r _, _, g, ⟨a, b, rfl, ha, hb, _⟩, hg => by
    simp only [RT.sz] at hg
    cases hl : l.sz <;> cases hr : r.sz <;> simp only [hl, hr, oadd, reduceCtorEq] at hg
    rename_i gl gr
    simp only [Option.some.injEq] at hg; subst hg
    rw [eval_add]
    have h1 := sz_bound ha hl; have h2 := sz_bound hb hr
    simp only [tsz]; omega

/-! ## Spines and builds -/

/-- Pointwise relation between two lists. -/
inductive F2 (R : RT → Term → Prop) : List RT → List Term → Prop
  | nil : F2 R [] []
  | cons {a : RT} {v : Term} {as : List RT} {vs : List Term} : R a v → F2 R as vs → F2 R (a :: as) (v :: vs)

theorem F2.append {R : RT → Term → Prop} : ∀ {as bs : List RT} {vs ws : List Term},
    F2 R as vs → F2 R bs ws → F2 R (as ++ bs) (vs ++ ws)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h1 h2, h => .cons h1 (F2.append h2 h)

theorem F2.length {R : RT → Term → Prop} : ∀ {as : List RT} {vs : List Term}, F2 R as vs → as.length = vs.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [F2.length h]

theorem F2.get {R : RT → Term → Prop} : ∀ {as : List RT} {vs : List Term} {i : Nat} {a : RT},
    F2 R as vs → as[i]? = some a → ∃ v, vs[i]? = some v ∧ R a v ∧ v ∈ vs
  | _ :: _, v :: _, 0, _, .cons h _, hi => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨v, rfl, h, by simp⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ hr, hi => by
    simp only [List.getElem?_cons_succ] at hi
    obtain ⟨v, hv, hR, hm⟩ := F2.get hr hi
    exact ⟨v, by simpa using hv, hR, by simp [hm]⟩

theorem build_inst {sz : Sz} : ∀ (args : List RT) (vs : List Term) {h : RT} {hu : Term},
    InstR sz h hu → F2 (InstR sz) args vs → InstR sz (build h args) (vs.foldl Term.app hu)
  | [], [], _, _, hh, _ => hh
  | a :: as, v :: vs, _, _, hh, .cons ha hrest => build_inst as vs (mkA_inst hh ha) hrest

theorem spine_inst {sz : Sz} : ∀ {t : RT} {u : Term}, InstR sz t u →
    ∃ hu vs, u = vs.foldl Term.app hu ∧ InstR sz t.spine.1 hu ∧ F2 (InstR sz) t.spine.2 vs
  | .S, u, h => ⟨u, [], rfl, h, .nil⟩
  | .V _ _, u, h => ⟨u, [], rfl, h, .nil⟩
  | .A l r _, _, ⟨a, b, rfl, ha, hb, _⟩ => by
    obtain ⟨hu, vs, rfl, hh, hvs⟩ := spine_inst ha
    refine ⟨hu, vs ++ [b], ?_, hh, ?_⟩
    · simp [List.foldl_append]
    · simp only [RT.spine]; exact F2.append hvs (.cons hb .nil)

end HnfCert
