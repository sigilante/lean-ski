import Ski.Phi
import Ski.GCertSound
import Ski.TopTermMain
open Term

/-!
# Finite index of the full observable (S6, Theorem 6)

Mechanization of Theorem 6 of the S6 paper (`s6-prefix-regularity/main.tex`, Section 4; the
combined invariant R7 of `notes/S4-bounded-exposure.md`).  Setting: closed terms over `S`.

* `PeriodicF 𝔐 N p`: the constants of S6: `N ≥ 10`, `p ≥ 1`, and `σ^j = σ^j'`, `φ^j = φ^j'` for
  `j, j' ≥ N − 2` congruent mod `p`, where `σ a = s·a` (`SModel.sIter`) and `φ (a, b) = (b, a·b)`
  (`SModel.fibM`).  Finiteness of `M` is not assumed for part (a).
* `Psi 𝔐 t a b`: the head run of `t` reaches a stable frame `f w` (`f` without hnf) with
  `a = M f`, `b = M w`.  `ObsF 𝔐 t o`: the full observable `O`, as a relation: `o = .hnf l` if
  the head run reaches an hnf with item values `l`; `o = .bot a b` if `Psi 𝔐 t a b`.  It is a
  total function on closed S-terms (`obsF_total`, `obsF_unique`).  S6 reads `Ψ` at the *first*
  stable frame; every stable frame on the head run gives the same pair (`psi_unique`), and
  `first_stable` gives the first one.
* `coreK`, `coreV`: the core form `t = S^k v`, `v = S` or `v` of at least two items.
* `Base0` (S6's `≈₋₁`), `Apx n` (`≈_{n−1}`), `SimL n` (`≃_{n−1}`), `SimF g = SimL (g + 1)` (`≃_g`).
* **(a)** `theorem_six`: `t ≃₇₇ t'` implies `O(C[t]) = O(C[t'])` for every context `C`.
* **(b)** `sig`: a computable signature into the explicitly finite type `SigT m (N + p) n`
  (built from `Fin`, `×`, `Option`), with `sig_sound`: equal signatures at level `n` imply
  `SimL n`; `sigCode`, `sigCode_inj`: an injection of `SigT m c n` into `Fin (sigBound m c n)`,
  `sigBound m c 0 = c·m·(m² + 1)`, `sigBound m c (n+1) = c·m·(m² + 1)·(sigBound m c n ² + 1)`.
  `sig_congruence`: equal signatures at level 78 imply equal observables in every context.
-/

namespace Full
open HnfS HnfSound BExp Phi

/-! ## Constants, the observable, the relations -/

/-- The constants of S6, Section 4: `N ≥ 10`, `p ≥ 1`; for `j, j' ≥ N − 2` congruent mod `p`,
`σ^j = σ^j'` and `φ^j = φ^j'` on all of `M`, `M²`. -/
structure PeriodicF (𝔐 : SModel) (N p : Nat) : Prop where
  hN : 10 ≤ N
  hp : 1 ≤ p
  sit : ∀ j j' : Nat, N - 2 ≤ j → N - 2 ≤ j' → j % p = j' % p → ∀ m, 𝔐.sIter j m = 𝔐.sIter j' m
  fib : ∀ j j' : Nat, N - 2 ≤ j → N - 2 ≤ j' → j % p = j' % p → ∀ q, 𝔐.fibM j q = 𝔐.fibM j' q

/-- `Ψ` as a relation: the head run of `t` reaches a stable frame `f w` (`f` has no hnf) with
values `a = M f`, `b = M w`.  Only hnf-less terms have one, and the pair is unique
(`psi_unique`). -/
def Psi (𝔐 : SModel) (t : Term) (a b : 𝔐.M) : Prop :=
  ∃ f w, Steps t (f ⬝ w) ∧ ¬ HasHnf f ∧ a = 𝔐.val f ∧ b = 𝔐.val w

/-- Values of the full observable: the item values of the hnf (the list carries the arity), or
`(⊥, M f, M w)`. -/
inductive Out (α : Type) : Type
  | hnf (items : List α) : Out α
  | bot (f w : α) : Out α

/-- **The full observable `O`** of S6, Definition 2, as a relation. -/
def ObsF (𝔐 : SModel) (t : Term) : Out 𝔐.M → Prop
  | .hnf l => ∃ v, Steps t v ∧ IsHnf v ∧ l = (spine v).map 𝔐.val
  | .bot a b => Psi 𝔐 t a b

/-- The exponent `k` of the core form `t = S^k v`. -/
def coreK : Term → Nat
  | .app .S x => coreK x + 1
  | _ => 0

/-- The core `v` of the core form `t = S^k v`: `S`, or a term of at least two items. -/
def coreV : Term → Term
  | .app .S x => coreV x
  | t => t

/-- S6's `≈₋₁`: equal values and, if `v` has no hnf, equal `Ψ`. -/
def Base0 (𝔐 : SModel) (v v' : Term) : Prop :=
  𝔐.val v = 𝔐.val v' ∧ (¬ HasHnf v → ∀ a b, Psi 𝔐 v a b ↔ Psi 𝔐 v' a b)

/-- S6's `≈_{n−1}` on cores: `Apx 0 = ≈₋₁`; `Apx (n+1) v v'` iff `v ≈₋₁ v'` and, for the two-item
hnfs `S a b`, `S a' b'` of `v`, `v'`: `a ≃_{n−1} a'` and `b ≃_{n−1} b'` (`≃` unfolded into the
core forms, see `SimL`). -/
def Apx (𝔐 : SModel) (N p : Nat) : Nat → Term → Term → Prop
  | 0 => Base0 𝔐
  | n + 1 => fun v v' => Base0 𝔐 v v' ∧
      ∀ a b a' b' : Term, Steps v (S ⬝ a ⬝ b) → Steps v' (S ⬝ a' ⬝ b') →
        (TowRel N p (coreK a) (coreK a') ∧ Apx 𝔐 N p n (coreV a) (coreV a')) ∧
        (TowRel N p (coreK b) (coreK b') ∧ Apx 𝔐 N p n (coreV b) (coreV b'))

/-- S6's `≃_{n−1}`: the core forms `(k, v)`, `(k', v')` satisfy `k ∼ k'` (`TowRel`) and
`v ≈_{n−1} v'`. -/
def SimL (𝔐 : SModel) (N p n : Nat) (u u' : Term) : Prop :=
  TowRel N p (coreK u) (coreK u') ∧ Apx 𝔐 N p n (coreV u) (coreV u')

/-- **S6's `≃_g`**, `g ≥ 0`. -/
def SimF (𝔐 : SModel) (N p g : Nat) : Term → Term → Prop := SimL 𝔐 N p (g + 1)

/-! ## (a) Theorem 6 -/

/-- Stable frames on one head run have the same value pair. -/
theorem psi_unique (𝔐 : SModel) {t : Term} (ht : PureS t) {a b a' b' : 𝔐.M}
    (h : Psi 𝔐 t a b) (h' : Psi 𝔐 t a' b') : a = a' ∧ b = b' := sorry

/-- The observable is defined on every closed S-term. -/
theorem obsF_total (𝔐 : SModel) {t : Term} (ht : PureS t) : ∃ o, ObsF 𝔐 t o := sorry

/-- The observable is a function. -/
theorem obsF_unique (𝔐 : SModel) {t : Term} (ht : PureS t) {o o' : Out 𝔐.M}
    (h : ObsF 𝔐 t o) (h' : ObsF 𝔐 t o') : o = o' := sorry

/-- The head run of an hnf-less term reaches a first stable frame: a run (`GCert.Run`) all of
whose frames before the last are not stable.  Its value pair is `Ψ`. -/
theorem first_stable (𝔐 : SModel) {t : Term} (ht : PureS t) (hn : ¬ HasHnf t) :
    ∃ k n f w, GCert.Run k n t (f ⬝ w) ∧ ¬ HasHnf f ∧ ObsF 𝔐 t (.bot (𝔐.val f) (𝔐.val w)) :=
  sorry

/-- **Theorem 6 of S6.**  If `t ≃₇₇ t'` then `O(C[t]) = O(C[t'])` for every context `C`. -/
theorem theorem_six (𝔐 : SModel) {N p : Nat} (hper : PeriodicF 𝔐 N p) {t t' : Term}
    (ht : PureS t) (ht' : PureS t') (h : SimF 𝔐 N p 77 t t') (C : Ctx) (o : Out 𝔐.M) :
    ObsF 𝔐 (C.plug t) o ↔ ObsF 𝔐 (C.plug t') o := sorry

/-! ## (b) The signature -/

/-- Closed S-terms. -/
abbrev PT : Type := {t : Term // PureS t}

/-- The target of the head step of a frame of at least three items. -/
def nextOf (t : Term) : Option Term :=
  match spine t with
  | u₁ :: u₂ :: u₃ :: rest => some (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃)))
  | _ => none

/-- The frame `f w` is stable, decided on blocks. -/
def stableB : Term → Bool
  | .app f _ => fold f == 36
  | _ => false

theorem nextOf_step {t t' : Term} (ht : PureS t) (h : nextOf t = some t') : Step t t' := sorry

/-- One head step from a frame that is not stable. -/
def Nxt (y x : PT) : Prop := stableB x.1 = false ∧ Step x.1 y.1

/-- Head runs through non-stable frames end (`TopTerm.reach_all`). -/
theorem nxt_wf : WellFounded Nxt := sorry

instance : WellFoundedRelation PT := ⟨Nxt, nxt_wf⟩

/-- The end of the head run: the hnf, or the first stable frame. -/
def headEnd (x : PT) : PT :=
  if hs : stableB x.1 = false then
    match hn : nextOf x.1 with
    | none => x
    | some y => headEnd ⟨y, (wstep_pure (nextOf_step x.2 hn).weak x.2).1⟩
  else x
termination_by x
decreasing_by exact ⟨hs, nextOf_step x.2 hn⟩

/-- Signatures at level `n` (for `≃_{n−1}`): the class of `k`, the value of the core, `Ψ` of the
core if it has no hnf, and from level 1 on the signatures of the two items of its hnf. -/
def SigT (m c : Nat) : Nat → Type
  | 0 => Fin c × Fin m × Option (Fin m × Fin m)
  | n + 1 => (Fin c × Fin m × Option (Fin m × Fin m)) × Option (SigT m c n × SigT m c n)

/-- The class of `k` under `∼`: `k` itself below `N`, else `N + (k − N) mod p`. -/
def kcls (N p k : Nat) : Nat := if k < N then k else N + (k - N) % p

theorem kcls_lt {N p : Nat} (hp : 0 < p) (k : Nat) : kcls N p k < N + p := sorry

/-- `Ψ` read off the end of the head run. -/
def psiOf (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m) : Term → Option (Fin m × Fin m)
  | .app f w => if fold f = 36 then some (code (𝔐.val f), code (𝔐.val w)) else none
  | _ => none

/-- The two items of an hnf `S a b`. -/
def itemsOf : (e : Term) → PureS e → Option (PT × PT)
  | .app (.app .S a) b, he => some (⟨a, he.app_inv.1.app_inv.2⟩, ⟨b, he.app_inv.2⟩)
  | _, _ => none

theorem coreV_pure {t : Term} (ht : PureS t) : PureS (coreV t) := sorry

/-- The level-0 signature. -/
def sig0 (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m) (N p : Nat) (hp : 0 < p) (t : PT) :
    Fin (N + p) × Fin m × Option (Fin m × Fin m) :=
  (⟨kcls N p (coreK t.1), kcls_lt hp _⟩, code (𝔐.val (coreV t.1)),
    psiOf 𝔐 code (headEnd ⟨coreV t.1, coreV_pure t.2⟩).1)

/-- **The signature map.**  `sig n` is computable and takes values in `SigT m (N + p) n`. -/
def sig (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m) (N p : Nat) (hp : 0 < p) :
    (n : Nat) → PT → SigT m (N + p) n
  | 0, t => sig0 𝔐 code N p hp t
  | n + 1, t => (sig0 𝔐 code N p hp t,
      (itemsOf (headEnd ⟨coreV t.1, coreV_pure t.2⟩).1 (headEnd ⟨coreV t.1, coreV_pure t.2⟩).2).map
        fun q => (sig 𝔐 code N p hp n q.1, sig 𝔐 code N p hp n q.2))

/-- **Finite index of `≃_{n−1}`, constructively.**  For a model with an injective coding of its
values in `Fin m`, equal signatures at level `n` imply `SimL n`. -/
theorem sig_sound (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m)
    (inj : ∀ a b, code a = code b → a = b) (N p : Nat) (hp : 0 < p) :
    ∀ (n : Nat) (t t' : PT), sig 𝔐 code N p hp n t = sig 𝔐 code N p hp n t' →
      SimL 𝔐 N p n t.1 t'.1 := sorry

/-- The number of signatures at level `n`, for `|M| = m` and `c = N + p` classes of `k`. -/
def sigBound (m c : Nat) : Nat → Nat
  | 0 => c * (m * (m * m + 1))
  | n + 1 => (c * (m * (m * m + 1))) * (sigBound m c n * sigBound m c n + 1)

def pairF {a b : Nat} (i : Fin a) (j : Fin b) : Fin (a * b) :=
  ⟨i.1 * b + j.1, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.2 _)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right b i.2)⟩

def optF {a : Nat} : Option (Fin a) → Fin (a + 1)
  | none => ⟨a, Nat.lt_succ_self a⟩
  | some i => ⟨i.1, Nat.lt_succ_of_lt i.2⟩

def baseCode {m c : Nat} (x : Fin c × Fin m × Option (Fin m × Fin m)) :
    Fin (c * (m * (m * m + 1))) :=
  pairF x.1 (pairF x.2.1 (optF (x.2.2.map fun q => pairF q.1 q.2)))

/-- Signatures at level `n`, numbered below `sigBound m c n`. -/
def sigCode {m c : Nat} : (n : Nat) → SigT m c n → Fin (sigBound m c n)
  | 0, x => baseCode x
  | n + 1, x => pairF (baseCode x.1)
      (optF (x.2.map fun q => pairF (sigCode n q.1) (sigCode n q.2)))

/-- **The bound.**  `sigCode` is injective, so there are at most `sigBound m (N + p) n`
signatures at level `n`. -/
theorem sigCode_inj {m c : Nat} : ∀ (n : Nat) (x y : SigT m c n),
    sigCode n x = sigCode n y → x = y := sorry

/-- Terms with equal signatures at level 78 (for `≃₇₇`) have equal observables in every
context: the syntactic congruence of `O` has at most `sigBound m (N + p) 78` classes. -/
theorem sig_congruence (𝔐 : SModel) {m : Nat} (code : 𝔐.M → Fin m)
    (inj : ∀ a b, code a = code b → a = b) {N p : Nat} (hper : PeriodicF 𝔐 N p) (t t' : PT)
    (h : sig 𝔐 code N p hper.hp 78 t = sig 𝔐 code N p hper.hp 78 t') (C : Ctx) (o : Out 𝔐.M) :
    ObsF 𝔐 (C.plug t.1) o ↔ ObsF 𝔐 (C.plug t'.1) o := sorry

end Full
