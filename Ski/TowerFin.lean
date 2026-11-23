/-!
# Finite combinatorics for the tower of models (S6, Lemma 7)

Constructive tools used by `Ski/Tower.lean`; nothing here mentions terms.  No `Fintype`, no
`Finset`, no choice.

* `php`: the pigeonhole principle for `g : Nat → Nat` with `g i < n` for `i ≤ n`.
* `iter_period`, `iter_mod`: a self-map of a set that injects into `Fin n` satisfies
  `f^(L + L!) = f^L` for every `L ≥ n`; hence `f^j = f^j'` for `j, j' ≥ L` congruent mod `L!`.
* `cnt_dich`: a pointwise smaller decidable predicate has the same extension on a list or a
  strictly smaller count.
* `posP`, `dedup`, `qidx`, `qelt`: the quotient of `Fin n` by a decidable equivalence, renumbered
  as `Fin (qn e)`.
* `EP`, `stab_final`, `EP_max`: Moore refinement on a finite binary algebra with an output; it is
  stable after `n²` rounds (`pairs n` has that length), and the stable relation is the largest
  congruence inside the kernel of the output.
* `closure`: the closure of `{s₀}` under a binary operation modulo a code `sg x < B`, as an
  explicit finite algebra on representatives (`Alg`).
-/

namespace TowerFin

/-! ## Pigeonhole -/

/-- Bounded search for a value of `g`. -/
theorem find_lt (g : Nat → Nat) (c : Nat) :
    ∀ k : Nat, (∃ i, i < k ∧ g i = c) ∨ (∀ i, i < k → g i ≠ c)
  | 0 => .inr (fun i h => absurd h (Nat.not_lt_zero i))
  | k + 1 => by
    rcases find_lt g c k with ⟨i, hi, e⟩ | h
    · exact .inl ⟨i, Nat.lt_succ_of_lt hi, e⟩
    · cases Nat.decEq (g k) c with
      | isTrue e => exact .inl ⟨k, Nat.lt_succ_self k, e⟩
      | isFalse ne =>
        refine .inr (fun i hi => ?_)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact h i h'
        · rw [h']; exact ne

/-- **Pigeonhole.**  `n + 1` values below `n` contain a repetition. -/
theorem php : ∀ (n : Nat) (g : Nat → Nat), (∀ i, i ≤ n → g i < n) →
    ∃ i j, i < j ∧ j ≤ n ∧ g i = g j
  | 0, g, h => absurd (h 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | n + 1, g, h => by
    rcases find_lt g (g (n + 1)) (n + 1) with ⟨i, hi, e⟩ | hne
    · exact ⟨i, n + 1, hi, Nat.le_refl _, e⟩
    · have key : ∀ i, i ≤ n → (if g i < g (n + 1) then g i else g i - 1) < n := by
        intro i hi
        have h1 := h i (Nat.le_succ_of_le hi)
        have h2 := h (n + 1) (Nat.le_refl _)
        have h3 := hne i (Nat.lt_succ_of_le hi)
        cases Nat.decLt (g i) (g (n + 1)) with
        | isTrue hlt => rw [if_pos hlt]; omega
        | isFalse hge => rw [if_neg hge]; omega
      obtain ⟨i, j, hij, hj, e⟩ := php n (fun i => if g i < g (n + 1) then g i else g i - 1) key
      refine ⟨i, j, hij, Nat.le_succ_of_le hj, ?_⟩
      have hi3 := hne i (by omega)
      have hj3 := hne j (by omega)
      have e' : (if g i < g (n + 1) then g i else g i - 1) =
          (if g j < g (n + 1) then g j else g j - 1) := e
      cases Nat.decLt (g i) (g (n + 1)) with
      | isTrue hi' =>
        rw [if_pos hi'] at e'
        cases Nat.decLt (g j) (g (n + 1)) with
        | isTrue hj' => rw [if_pos hj'] at e'; exact e'
        | isFalse hj' => rw [if_neg hj'] at e'; omega
      | isFalse hi' =>
        rw [if_neg hi'] at e'
        cases Nat.decLt (g j) (g (n + 1)) with
        | isTrue hj' => rw [if_pos hj'] at e'; omega
        | isFalse hj' => rw [if_neg hj'] at e'; omega

/-! ## Iteration and eventual periods -/

/-- `f^k`. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => f (iter f k x)

theorem iter_add {α : Type} (f : α → α) : ∀ (a b : Nat) (x : α),
    iter f (a + b) x = iter f a (iter f b x)
  | 0, b, x => by rw [Nat.zero_add]; rfl
  | a + 1, b, x => by rw [Nat.succ_add]; exact congrArg f (iter_add f a b x)

/-- `f^(k+1) = f^k ∘ f`. -/
theorem iter_succ' {α : Type} (f : α → α) (k : Nat) (x : α) :
    iter f (k + 1) x = iter f k (f x) := iter_add f k 1 x

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n : Nat, 0 < fact n
  | 0 => Nat.one_pos
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

theorem dvd_fact : ∀ (n c : Nat), 1 ≤ c → c ≤ n → ∃ q, fact n = c * q
  | 0, c, h1, h2 => absurd (Nat.le_trans h1 h2) (by decide)
  | n + 1, c, h1, h2 => by
    rcases Nat.lt_or_eq_of_le h2 with h | h
    · obtain ⟨q, e⟩ := dvd_fact n c h1 (Nat.le_of_lt_succ h)
      refine ⟨(n + 1) * q, ?_⟩
      show (n + 1) * fact n = c * ((n + 1) * q)
      rw [e, Nat.mul_left_comm]
    · exact ⟨fact n, by rw [h]; rfl⟩

theorem iter_step {α : Type} (f : α → α) {i c : Nat} {x : α}
    (h : iter f (i + c) x = iter f i x) (a : Nat) (ha : i ≤ a) :
    iter f (a + c) x = iter f a x :=
  calc iter f (a + c) x = iter f ((a - i) + (i + c)) x := by
        rw [show a + c = (a - i) + (i + c) by omega]
    _ = iter f (a - i) (iter f (i + c) x) := iter_add f _ _ x
    _ = iter f (a - i) (iter f i x) := by rw [h]
    _ = iter f ((a - i) + i) x := (iter_add f _ _ x).symm
    _ = iter f a x := by rw [show a - i + i = a by omega]

/-- A cycle `f^(i+c) x = f^i x` repeats from every `a ≥ i`. -/
theorem iter_cycle {α : Type} (f : α → α) {i c : Nat} {x : α}
    (h : iter f (i + c) x = iter f i x) : ∀ (q a : Nat), i ≤ a →
    iter f (a + c * q) x = iter f a x
  | 0, a, _ => by rw [Nat.mul_zero]; rfl
  | q + 1, a, ha => by
    rw [Nat.mul_succ, ← Nat.add_assoc, iter_step f h (a + c * q) (Nat.le_trans ha (Nat.le_add_right _ _))]
    exact iter_cycle f h q a ha

/-- **Eventual period.**  If `α` injects into `Fin n` (through `code`), then
`f^(L + L!) = f^L` for every `L ≥ n`. -/
theorem iter_period {α : Type} (f : α → α) (code : α → Nat) (n : Nat) (hc : ∀ x, code x < n)
    (inj : ∀ x y, code x = code y → x = y) (L : Nat) (hL : n ≤ L) (x : α) :
    iter f (L + fact L) x = iter f L x := by
  obtain ⟨i, j, hij, hj, e⟩ := php n (fun k => code (iter f k x)) (fun k _ => hc _)
  have e' : iter f i x = iter f j x := inj _ _ e
  have hcyc : iter f (i + (j - i)) x = iter f i x := by
    rw [show i + (j - i) = j by omega]; exact e'.symm
  obtain ⟨q, hq⟩ := dvd_fact L (j - i) (by omega) (by omega)
  rw [hq]
  exact iter_cycle f hcyc q L (by omega)

theorem iter_mod_le {α : Type} (f : α → α) {L p : Nat}
    (h : ∀ x, iter f (L + p) x = iter f L x) {j j' : Nat} (hj : L ≤ j) (hjj : j ≤ j')
    (hm : j % p = j' % p) (x : α) : iter f j x = iter f j' x := by
  have h0 : (j' - j) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq hm.symm
  have h1 := Nat.div_add_mod (j' - j) p
  rw [h0, Nat.add_zero] at h1
  have e : j' = j + p * ((j' - j) / p) := by omega
  rw [e]
  exact (iter_cycle f (h x) _ j hj).symm

/-- From the period on: `f^j = f^j'` for `j, j' ≥ L` congruent mod `p`. -/
theorem iter_mod {α : Type} (f : α → α) {L p : Nat}
    (h : ∀ x, iter f (L + p) x = iter f L x) {j j' : Nat} (hj : L ≤ j) (hj' : L ≤ j')
    (hm : j % p = j' % p) (x : α) : iter f j x = iter f j' x := by
  rcases Nat.le_total j j' with hle | hle
  · exact iter_mod_le f h hj hle hm x
  · exact (iter_mod_le f h hj' hle hm.symm x).symm

/-! ## Counting -/

/-- The number of elements of a list that satisfy `p`. -/
def cnt {α : Type} (p : α → Prop) [DecidablePred p] : List α → Nat
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + cnt p xs

theorem cnt_le_len {α : Type} (p : α → Prop) [DecidablePred p] : ∀ l : List α, cnt p l ≤ l.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    have ih := cnt_le_len p xs
    show (if p x then 1 else 0) + cnt p xs ≤ xs.length + 1
    cases (inferInstance : Decidable (p x)) with
    | isTrue h => rw [if_pos h]; omega
    | isFalse h => rw [if_neg h]; omega

/-- If `q` implies `p`, then on a list either `p` implies `q`, or `q` has strictly fewer
instances. -/
theorem cnt_dich {α : Type} (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hqp : ∀ x, q x → p x) : ∀ l : List α,
    cnt q l ≤ cnt p l ∧ ((∀ x, x ∈ l → p x → q x) ∨ cnt q l < cnt p l)
  | [] => ⟨Nat.le_refl 0, .inl (fun x hx => nomatch hx)⟩
  | x :: xs => by
    obtain ⟨ih1, ih2⟩ := cnt_dich p q hqp xs
    show (if q x then 1 else 0) + cnt q xs ≤ (if p x then 1 else 0) + cnt p xs ∧
      ((∀ y, y ∈ x :: xs → p y → q y) ∨
        (if q x then 1 else 0) + cnt q xs < (if p x then 1 else 0) + cnt p xs)
    cases (inferInstance : Decidable (q x)) with
    | isTrue hq =>
      rw [if_pos hq, if_pos (hqp x hq)]
      refine ⟨by omega, ?_⟩
      rcases ih2 with h | h
      · refine .inl (fun y hy hp => ?_)
        rcases List.mem_cons.mp hy with e | hy'
        · rw [e]; exact hq
        · exact h y hy' hp
      · exact .inr (by omega)
    | isFalse hq =>
      rw [if_neg hq]
      cases (inferInstance : Decidable (p x)) with
      | isTrue hp => rw [if_pos hp]; exact ⟨by omega, .inr (by omega)⟩
      | isFalse hp =>
        rw [if_neg hp]
        refine ⟨by omega, ?_⟩
        rcases ih2 with h | h
        · refine .inl (fun y hy hpy => ?_)
          rcases List.mem_cons.mp hy with e | hy'
          · rw [e] at hpy; exact absurd hpy hp
          · exact h y hy' hpy
        · exact .inr (by omega)

/-! ## First positions and renumbered quotients -/

/-- The position of the first element satisfying `p` (the length if there is none). -/
def posP {α : Type} (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => if p x = true then 0 else posP p xs + 1

theorem posP_lt {α : Type} {p : α → Bool} : ∀ {l : List α}, (∃ y, y ∈ l ∧ p y = true) →
    posP p l < l.length
  | [], ⟨_, hy, _⟩ => nomatch hy
  | x :: xs, ⟨y, hy, hp⟩ => by
    show (if p x = true then 0 else posP p xs + 1) < xs.length + 1
    cases hx : p x with
    | true => rw [if_pos rfl]; exact Nat.succ_pos _
    | false =>
      rw [if_neg (by decide)]
      rcases List.mem_cons.mp hy with e | hy'
      · rw [e, hx] at hp; exact absurd hp (by decide)
      · exact Nat.succ_lt_succ (posP_lt ⟨y, hy', hp⟩)

theorem posP_sat {α : Type} {p : α → Bool} : ∀ {l : List α} (h : posP p l < l.length),
    p (l[posP p l]'h) = true
  | [], h => absurd h (Nat.not_lt_zero _)
  | x :: xs, h => by
    cases hx : p x with
    | true =>
      have e : posP p (x :: xs) = 0 := by show (if p x = true then 0 else _) = 0; rw [hx]; rfl
      have : (x :: xs)[posP p (x :: xs)]'h = x := by simp only [e]; rfl
      rw [this]; exact hx
    | false =>
      have e : posP p (x :: xs) = posP p xs + 1 := by
        show (if p x = true then 0 else _) = _; rw [hx]; rfl
      have h' : posP p xs < xs.length := by rw [e] at h; exact Nat.lt_of_succ_lt_succ h
      have : (x :: xs)[posP p (x :: xs)]'h = xs[posP p xs]'h' := by simp only [e]; rfl
      rw [this]; exact posP_sat h'

theorem posP_min {α : Type} {p : α → Bool} : ∀ {l : List α} {i : Nat} (hi : i < l.length),
    i < posP p l → p (l[i]'hi) = false
  | [], _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | x :: xs, i, hi, h => by
    cases hx : p x with
    | true =>
      have e : posP p (x :: xs) = 0 := by show (if p x = true then 0 else _) = 0; rw [hx]; rfl
      rw [e] at h; exact absurd h (Nat.not_lt_zero _)
    | false =>
      have e : posP p (x :: xs) = posP p xs + 1 := by
        show (if p x = true then 0 else _) = _; rw [hx]; rfl
      rw [e] at h
      cases i with
      | zero => exact hx
      | succ i => exact posP_min (l := xs) (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ h)

theorem posP_congr {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ y, y ∈ l → p y = q y) →
    posP p l = posP q l
  | [], _ => rfl
  | x :: xs, h => by
    show (if p x = true then 0 else posP p xs + 1) = (if q x = true then 0 else posP q xs + 1)
    rw [h x (List.mem_cons_self), posP_congr (l := xs) (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- One representative of each class of `e`, scanning from the right. -/
def dedup {α : Type} (e : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => if (dedup e xs).any (e x) = true then dedup e xs else x :: dedup e xs

theorem dedup_pw {α : Type} (e : α → α → Bool) : ∀ l : List α,
    List.Pairwise (fun a b => e a b = false) (dedup e l)
  | [] => List.Pairwise.nil
  | x :: xs => by
    show List.Pairwise _ (if (dedup e xs).any (e x) = true then dedup e xs else x :: dedup e xs)
    cases hx : (dedup e xs).any (e x) with
    | true => rw [if_pos rfl]; exact dedup_pw e xs
    | false =>
      rw [if_neg (by decide)]
      refine List.Pairwise.cons (fun y hy => ?_) (dedup_pw e xs)
      cases hxy : e x y with
      | false => rfl
      | true =>
        have : (dedup e xs).any (e x) = true := List.any_eq_true.mpr ⟨y, hy, hxy⟩
        rw [hx] at this; exact absurd this (by decide)

theorem dedup_cover {α : Type} (e : α → α → Bool) (refl : ∀ x, e x x = true) :
    ∀ (l : List α) (x : α), x ∈ l → ∃ y, y ∈ dedup e l ∧ e x y = true
  | [], _, hx => nomatch hx
  | z :: zs, x, hx => by
    show ∃ y, y ∈ (if (dedup e zs).any (e z) = true then dedup e zs else z :: dedup e zs) ∧
      e x y = true
    cases hz : (dedup e zs).any (e z) with
    | true =>
      rw [if_pos rfl]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact List.any_eq_true.mp hz
      · exact dedup_cover e refl zs x hx'
    | false =>
      rw [if_neg (by decide)]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨x, List.mem_cons_self, refl x⟩
      · obtain ⟨y, hy, h⟩ := dedup_cover e refl zs x hx'
        exact ⟨y, List.mem_cons_of_mem z hy, h⟩

theorem pw_get {α : Type} {R : α → α → Prop} : ∀ {l : List α}, List.Pairwise R l →
    ∀ {i j : Nat} (hi : i < l.length) (hj : j < l.length), i < j → R (l[i]'hi) (l[j]'hj)
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: xs, h, i, j, hi, hj, hij => by
    have hc := List.pairwise_cons.mp h
    cases j with
    | zero => exact absurd hij (Nat.not_lt_zero _)
    | succ j =>
      cases i with
      | zero => exact hc.1 _ (List.getElem_mem (Nat.lt_of_succ_lt_succ hj))
      | succ i =>
        exact pw_get (l := xs) hc.2 (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
          (Nat.lt_of_succ_lt_succ hij)

section Quot
variable {n : Nat}

/-- The representatives of the classes of `e` on `Fin n`. -/
def reps (e : Fin n → Fin n → Bool) : List (Fin n) := dedup e (List.finRange n)

/-- The number of classes. -/
def qn (e : Fin n → Fin n → Bool) : Nat := (reps e).length

theorem qcover (e : Fin n → Fin n → Bool) (hr : ∀ a, e a a = true) (a : Fin n) :
    ∃ y, y ∈ reps e ∧ e a y = true :=
  dedup_cover e hr _ a (List.mem_finRange a)

/-- The class of `a`, as a number below `qn e`. -/
def qidx (e : Fin n → Fin n → Bool) (hr : ∀ a, e a a = true) (a : Fin n) : Fin (qn e) :=
  ⟨posP (e a) (reps e), posP_lt (qcover e hr a)⟩

/-- The representative of a class. -/
def qelt (e : Fin n → Fin n → Bool) (q : Fin (qn e)) : Fin n := (reps e)[q.1]'q.2

theorem qelt_idx (e : Fin n → Fin n → Bool) (hr : ∀ a, e a a = true) (a : Fin n) :
    e a (qelt e (qidx e hr a)) = true :=
  posP_sat (p := e a) (posP_lt (qcover e hr a))

theorem qidx_eq (e : Fin n → Fin n → Bool) (hr : ∀ a, e a a = true)
    (hs : ∀ a b, e a b = true → e b a = true)
    (ht : ∀ a b c, e a b = true → e b c = true → e a c = true)
    {a a' : Fin n} (h : e a a' = true) : qidx e hr a = qidx e hr a' := by
  apply Fin.eq_of_val_eq
  show posP (e a) (reps e) = posP (e a') (reps e)
  apply posP_congr
  intro y _
  cases h1 : e a y with
  | true => exact (ht a' a y (hs a a' h) h1).symm
  | false =>
    cases h2 : e a' y with
    | false => rfl
    | true => rw [ht a a' y h h2] at h1; exact absurd h1 (by decide)

theorem qidx_inj (e : Fin n → Fin n → Bool) (hr : ∀ a, e a a = true)
    (hs : ∀ a b, e a b = true → e b a = true)
    (ht : ∀ a b c, e a b = true → e b c = true → e a c = true)
    {a a' : Fin n} (h : qidx e hr a = qidx e hr a') : e a a' = true := by
  have h1 := qelt_idx e hr a
  have h2 := qelt_idx e hr a'
  rw [h] at h1
  exact ht _ _ _ h1 (hs _ _ h2)

theorem qidx_elt (e : Fin n → Fin n → Bool) (hr : ∀ a, e a a = true)
    (hs : ∀ a b, e a b = true → e b a = true) (q : Fin (qn e)) : qidx e hr (qelt e q) = q := by
  apply Fin.eq_of_val_eq
  show posP (e (qelt e q)) (reps e) = q.1
  have hlt : posP (e (qelt e q)) (reps e) < (reps e).length := posP_lt (qcover e hr (qelt e q))
  have hsat := posP_sat (p := e (qelt e q)) hlt
  rcases Nat.lt_trichotomy (posP (e (qelt e q)) (reps e)) q.1 with h | h | h
  · have hpw := pw_get (dedup_pw e (List.finRange n)) hlt q.2 h
    have := hs _ _ hsat
    have hpw' : e ((reps e)[posP (e (qelt e q)) (reps e)]'hlt) (qelt e q) = false := hpw
    rw [hpw'] at this; exact absurd this (by decide)
  · exact h
  · have := posP_min (p := e (qelt e q)) q.2 h
    have h' : e (qelt e q) (qelt e q) = false := this
    rw [hr] at h'; exact absurd h' (by decide)

end Quot

/-! ## Moore refinement -/

section Moore
variable {n : Nat} {β : Type} (mul : Fin n → Fin n → Fin n) (o : Fin n → β)

/-- `EP 0` is the kernel of the output; `EP (i+1) a a'` iff `EP i a a'` and `EP i` holds after one
multiplication, on either side, by any element. -/
def EP : Nat → Fin n → Fin n → Prop
  | 0, a, a' => o a = o a'
  | i + 1, a, a' => EP i a a' ∧
      ∀ b, b ∈ List.finRange n → EP i (mul a b) (mul a' b) ∧ EP i (mul b a) (mul b a')

instance decEP [DecidableEq β] : ∀ (i : Nat) (a a' : Fin n), Decidable (EP mul o i a a')
  | 0, a, a' => inferInstanceAs (Decidable (o a = o a'))
  | i + 1, a, a' =>
    have : ∀ x y, Decidable (EP mul o i x y) := decEP i
    inferInstanceAs (Decidable (EP mul o i a a' ∧
      ∀ b, b ∈ List.finRange n → EP mul o i (mul a b) (mul a' b) ∧ EP mul o i (mul b a) (mul b a')))

theorem EP_refl : ∀ (i : Nat) (a : Fin n), EP mul o i a a
  | 0, _ => rfl
  | i + 1, a => ⟨EP_refl i a, fun _ _ => ⟨EP_refl i _, EP_refl i _⟩⟩

theorem EP_symm : ∀ (i : Nat) {a a' : Fin n}, EP mul o i a a' → EP mul o i a' a
  | 0, _, _, h => Eq.symm h
  | i + 1, _, _, h => ⟨EP_symm i h.1, fun b hb => ⟨EP_symm i (h.2 b hb).1, EP_symm i (h.2 b hb).2⟩⟩

theorem EP_trans : ∀ (i : Nat) {a b c : Fin n}, EP mul o i a b → EP mul o i b c → EP mul o i a c
  | 0, _, _, _, h, h' => Eq.trans h h'
  | i + 1, _, _, _, h, h' => ⟨EP_trans i h.1 h'.1, fun x hx =>
      ⟨EP_trans i (h.2 x hx).1 (h'.2 x hx).1, EP_trans i (h.2 x hx).2 (h'.2 x hx).2⟩⟩

theorem EP_out : ∀ (i : Nat) {a a' : Fin n}, EP mul o i a a' → o a = o a'
  | 0, _, _, h => h
  | i + 1, _, _, h => EP_out i h.1

/-- Round `i` is stable. -/
def Stab (i : Nat) : Prop := ∀ a a' : Fin n, EP mul o i a a' → EP mul o (i + 1) a a'

theorem stab_succ {i : Nat} (h : Stab mul o i) : Stab mul o (i + 1) :=
  fun _ _ h1 => ⟨h1, fun b hb => ⟨h _ _ (h1.2 b hb).1, h _ _ (h1.2 b hb).2⟩⟩

theorem stab_le {i : Nat} (h : Stab mul o i) : ∀ j : Nat, i ≤ j → Stab mul o j := by
  intro j hj
  induction j with
  | zero => rw [Nat.le_zero.mp hj] at h; exact h
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hj with h' | h'
    · exact stab_succ mul o (ih (Nat.le_of_lt_succ h'))
    · rw [h'] at h; exact h

/-- All pairs. -/
def pairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a => (List.finRange n).map fun a' => (a, a')

theorem mem_pairs (a a' : Fin n) : (a, a') ∈ pairs n :=
  List.mem_flatMap.mpr ⟨a, List.mem_finRange a, List.mem_map.mpr ⟨a', List.mem_finRange a', rfl⟩⟩

theorem stab_search [DecidableEq β] : ∀ k : Nat, (∃ i, i < k ∧ Stab mul o i) ∨
    cnt (fun q : Fin n × Fin n => EP mul o k q.1 q.2) (pairs n) + k ≤
      cnt (fun q : Fin n × Fin n => EP mul o 0 q.1 q.2) (pairs n)
  | 0 => .inr (Nat.le_refl _)
  | k + 1 => by
    rcases stab_search k with ⟨i, hi, h⟩ | h
    · exact .inl ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · obtain ⟨_, h2⟩ := cnt_dich (fun q : Fin n × Fin n => EP mul o k q.1 q.2)
        (fun q : Fin n × Fin n => EP mul o (k + 1) q.1 q.2) (fun _ hq => hq.1) (pairs n)
      rcases h2 with h2 | h2
      · exact .inl ⟨k, Nat.lt_succ_self k, fun a a' => h2 (a, a') (mem_pairs a a')⟩
      · exact .inr (by omega)

/-- **Refinement stops.**  Round `(pairs n).length` (that is, `n²`) is stable. -/
theorem stab_final [DecidableEq β] : Stab mul o (pairs n).length := by
  rcases stab_search mul o ((pairs n).length + 1) with ⟨i, hi, h⟩ | h
  · exact stab_le mul o h _ (Nat.le_of_lt_succ hi)
  · have h0 := cnt_le_len (fun q : Fin n × Fin n => EP mul o 0 q.1 q.2) (pairs n)
    exact absurd (Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _) h) h0) (Nat.not_succ_le_self _)

/-- The stable relation is a congruence. -/
theorem EP_cong [DecidableEq β] {a a' : Fin n} (h : EP mul o (pairs n).length a a') (b : Fin n) :
    EP mul o (pairs n).length (mul a b) (mul a' b) ∧
      EP mul o (pairs n).length (mul b a) (mul b a') :=
  (stab_final mul o a a' h).2 b (List.mem_finRange b)

/-- Every congruence inside the kernel of the output is inside every `EP i`. -/
theorem EP_max (Rel : Fin n → Fin n → Prop) (hout : ∀ a a', Rel a a' → o a = o a')
    (hmul : ∀ a a' b, Rel a a' → Rel (mul a b) (mul a' b) ∧ Rel (mul b a) (mul b a')) :
    ∀ (i : Nat) (a a' : Fin n), Rel a a' → EP mul o i a a'
  | 0, a, a', h => hout a a' h
  | i + 1, a, a', h => ⟨EP_max Rel hout hmul i a a' h, fun b _ =>
      ⟨EP_max Rel hout hmul i _ _ (hmul a a' b h).1, EP_max Rel hout hmul i _ _ (hmul a a' b h).2⟩⟩

end Moore

/-! ## Closure under a binary operation, modulo a code -/

section Closure
variable {T : Type} (app : T → T → T) (sg : T → Nat)

/-- A product of two listed elements whose code is not listed, if there is one. -/
def findNew (R : List T) : Option T :=
  (R.flatMap fun t => R.map fun u => app t u).find? fun x => !(R.any fun r => Nat.beq (sg r) (sg x))

theorem findNew_none {R : List T} (h : findNew app sg R = none) {t u : T} (ht : t ∈ R)
    (hu : u ∈ R) : ∃ r, r ∈ R ∧ sg r = sg (app t u) := by
  have h1 := List.find?_eq_none.mp h (app t u)
    (List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨u, hu, rfl⟩⟩)
  cases h2 : R.any (fun r => Nat.beq (sg r) (sg (app t u))) with
  | true =>
    obtain ⟨r, hr, e⟩ := List.any_eq_true.mp h2
    exact ⟨r, hr, Nat.eq_of_beq_eq_true e⟩
  | false => rw [h2] at h1; exact absurd rfl h1

theorem findNew_some {R : List T} {x : T} (h : findNew app sg R = some x) {r : T} (hr : r ∈ R) :
    sg r ≠ sg x := by
  have h1 := List.find?_some h
  intro e
  have h2 : R.any (fun r => Nat.beq (sg r) (sg x)) = true :=
    List.any_eq_true.mpr ⟨r, hr, by rw [e]; exact Nat.beq_refl _⟩
  rw [h2] at h1; exact absurd h1 (by decide)

/-- Add new products, at most `fuel` of them. -/
def close : Nat → List T → List T
  | 0, R => R
  | f + 1, R =>
    match findNew app sg R with
    | none => R
    | some x => close f (x :: R)

/-- The codes of the list are pairwise different. -/
def Dist (R : List T) : Prop := List.Pairwise (fun a b => sg a ≠ sg b) R

theorem close_mem : ∀ (f : Nat) (R : List T) (x : T), x ∈ R → x ∈ close app sg f R
  | 0, _, _, h => h
  | f + 1, R, x, h => by
    show x ∈ (match findNew app sg R with | none => R | some y => close app sg f (y :: R))
    cases findNew app sg R with
    | none => exact h
    | some y => exact close_mem f (y :: R) x (List.mem_cons_of_mem y h)

theorem close_spec : ∀ (f : Nat) (R : List T), Dist sg R →
    Dist sg (close app sg f R) ∧
      (findNew app sg (close app sg f R) = none ∨ R.length + f ≤ (close app sg f R).length)
  | 0, R, h => ⟨h, .inr (Nat.le_refl _)⟩
  | f + 1, R, h => by
    show Dist sg (match findNew app sg R with | none => R | some y => close app sg f (y :: R)) ∧
      (findNew app sg (match findNew app sg R with | none => R | some y => close app sg f (y :: R))
          = none ∨
        R.length + (f + 1) ≤
          (match findNew app sg R with | none => R | some y => close app sg f (y :: R)).length)
    cases hn : findNew app sg R with
    | none => exact ⟨h, .inl hn⟩
    | some y =>
      have hd : Dist sg (y :: R) :=
        List.Pairwise.cons (fun r hr => (findNew_some app sg hn hr).symm) h
      obtain ⟨h1, h2⟩ := close_spec f (y :: R) hd
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact .inl h2
      · refine .inr ?_
        have : (y :: R).length = R.length + 1 := rfl
        show R.length + (f + 1) ≤ (close app sg f (y :: R)).length
        omega

/-- Pairwise different codes below `B`: at most `B` elements. -/
theorem dist_len {B : Nat} (hB : ∀ x, sg x < B) {R : List T} (h : Dist sg R) : R.length ≤ B := by
  rcases Nat.lt_or_ge B R.length with hlt | hge
  · exfalso
    obtain ⟨i, j, hij, hj, e⟩ := php B (fun i => if hi : i < R.length then sg (R[i]'hi) else 0)
      (fun i hi => by
        show (if hi : i < R.length then sg (R[i]'hi) else 0) < B
        rw [dif_pos (Nat.lt_of_le_of_lt hi hlt)]; exact hB _)
    have hi' : i < R.length := by omega
    have hj' : j < R.length := by omega
    have e' : (if hi : i < R.length then sg (R[i]'hi) else 0) =
        (if hj : j < R.length then sg (R[j]'hj) else 0) := e
    rw [dif_pos hi', dif_pos hj'] at e'
    exact pw_get h hi' hj' hij e'
  · exact hge

variable (s₀ : T) (B : Nat)

/-- The closure of `{s₀}`: representatives of all codes of terms built from `s₀`, as far as the
operation on representatives shows. -/
def closed : List T := close app sg (B + 1) [s₀]

theorem closed_s : s₀ ∈ closed app sg s₀ B := close_mem app sg _ _ _ List.mem_cons_self

theorem closed_closed (hB : ∀ x, sg x < B) : findNew app sg (closed app sg s₀ B) = none := by
  obtain ⟨h1, h2⟩ := close_spec app sg (B + 1) [s₀] (List.Pairwise.cons (fun _ h => nomatch h) .nil)
  rcases h2 with h2 | h2
  · exact h2
  · have h3 := dist_len sg hB h1
    have : ([s₀] : List T).length = 1 := rfl
    have h4 : ([s₀] : List T).length + (B + 1) ≤ (closed app sg s₀ B).length := h2
    omega

/-- A finite algebra of representatives: `rep (mul a b)` has the code of `app (rep a) (rep b)`,
and `rep s` the code of `s₀`. -/
structure Alg where
  n : Nat
  rep : Fin n → T
  mul : Fin n → Fin n → Fin n
  s : Fin n
  mul_sg : ∀ a b, sg (rep (mul a b)) = sg (app (rep a) (rep b))
  s_sg : sg (rep s) = sg s₀

theorem look_ex {R : List T} {x : T} (h : ∃ r, r ∈ R ∧ sg r = sg x) :
    ∃ y, y ∈ R ∧ Nat.beq (sg y) (sg x) = true := by
  obtain ⟨r, hr, e⟩ := h
  exact ⟨r, hr, by rw [e]; exact Nat.beq_refl _⟩

/-- **The closure as an algebra.** -/
def closure (hB : ∀ x, sg x < B) : Alg app sg s₀ where
  n := (closed app sg s₀ B).length
  rep a := (closed app sg s₀ B)[a.1]'a.2
  mul a b := ⟨posP (fun r => Nat.beq (sg r) (sg (app ((closed app sg s₀ B)[a.1]'a.2)
      ((closed app sg s₀ B)[b.1]'b.2)))) (closed app sg s₀ B),
    posP_lt (look_ex sg (findNew_none app sg (closed_closed app sg s₀ B hB)
      (List.getElem_mem a.2) (List.getElem_mem b.2)))⟩
  s := ⟨posP (fun r => Nat.beq (sg r) (sg s₀)) (closed app sg s₀ B),
    posP_lt (look_ex sg ⟨s₀, closed_s app sg s₀ B, rfl⟩)⟩
  mul_sg a b := Nat.eq_of_beq_eq_true (posP_sat (p := fun r => Nat.beq (sg r) (sg (app
    ((closed app sg s₀ B)[a.1]'a.2) ((closed app sg s₀ B)[b.1]'b.2)))) _)
  s_sg := Nat.eq_of_beq_eq_true (posP_sat (p := fun r => Nat.beq (sg r) (sg s₀)) _)

end Closure

end TowerFin
