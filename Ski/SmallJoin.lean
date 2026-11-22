import Ski.WordProblem
import Ski.HeadRec
open Term

/-!
# The word problem for S: Small Join (S3, route 1)

Size is the leaf count `HeadRec.sz`.

**(a) Small Join ⟹ decidability.**  A weak step never shrinks a pure term (`sz_wstep`), so the
reducts of `t` of size `≤ s` are among the finitely many pure terms of size `≤ s`.
`reductsUpTo s t` lists them: `mem_reductsUpTo : w ∈ reductsUpTo s t ↔ WSteps t w ∧ sz w ≤ s`
for pure `t`.  The list is `reachN` cut off at the number of terms in an enumeration `gen s` of
the pure terms of size `≤ s + 1`; the cut-off is justified by `HeadRec.no_ground_loop` (a
reduction path repeats no term, so a path that stays below size `s` is no longer than the
enumeration).  `SmallJoin g` says that convertible pure terms `t`, `u` have a common reduct of
size `≤ g |t| |u|`.  Then `convB g t u : Bool` decides conversion: `smallJoin_decides`.  No
Markov principle and no `Lock1`.  `g` is an arbitrary Lean function `Nat → Nat → Nat`; `convB g`
is computable relative to `g` (it calls `g` once), so conversion is decidable in the usual sense
if `g` is computable, or bounded by a computable function (`SmallJoin` is monotone in `g`).
`SmallJoin g` is a hypothesis, not a theorem.  Classically some `g` always works (take, for each
pair of sizes, the largest least join over the finitely many convertible pairs), so all the
content is in `g` being computable.

**(b) A family with unbounded join excess.**  `P = S S S`, `Q = S (S S)`, `R = S S`;
`fk 0 = S P`, `fk (k+1) = S S (fk k)`, likewise `gk` from `S Q`; `tk k = fk k P R`,
`uk k = gk k Q Q`.  `|tk k| = 2k + 9`, `|uk k| = 2k + 10`.
* `tk_join`, `uk_join`, `sz_wk`: both reduce to `wk k`, of size `6k + 12`; `conv_family`.
* `family_lower`: **every common reduct of `tk k` and `uk k` has size `≥ 3k + 10`**, that is,
  at least `max (|tk k|, |uk k|) + k`.  (The exact least size, `6k + 12`, is known by
  computation for `k ≤ 5` only and is not proved here.)
* `smallJoin_lower`, `not_smallJoin_max_add`: so no function `max a b + c` is a Small Join bound.

The proof of `family_lower`: call a pure term `A`-clean (`ArgS A`) if every application `a ⬝ S`
in it has `A a`.  If `A` allows only `S` and `S S`, cleanness is preserved by reduction and every
step from a clean term adds at least one leaf (`argS_wstep`): the argument of a redex is never
`S`.  `uk k` is clean for `A = {S}`, so no reduct of it contains `P`.  `tk k` is clean for
`A = {S, S S}`, and it contains the chain `fk k = S S (S S (… (S P)))`.  `rk` is the length of the
longest such chain in a term; a step lowers it by at most one (`rk_step`), because a chain is
normal, so it is either untouched, or is the `S S c` of a redex `S S c z` (then `c` survives), or
is the `S f` of a redex `S f g x` (then the chain `f` inside it survives).
So `sz + rk` never decreases from `tk k`, and it starts at `(2k + 9) + (k + 1)`.
-/

namespace WordProblem
open HnfS HeadRec

/-! ## Size never decreases -/

theorem sz_app_ge (f x : Term) : 2 ≤ sz (f ⬝ x) := by
  have h1 := sz_pos f
  have h2 := sz_pos x
  show 2 ≤ sz f + sz x
  omega

/-- **A weak step never shrinks a pure term**: `S x y z → x z (y z)` adds `|z| − 1` leaves. -/
theorem sz_wstep {t t' : Term} (ht : PureS t) (h : WStep t t') : sz t ≤ sz t' := by
  induction h with
  | S f g x =>
    have := sz_pos x
    show 1 + sz f + sz g + sz x ≤ sz f + sz x + (sz g + sz x)
    omega
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | @left f f' x _ ih =>
    have := ih ht.app_inv.1
    show sz f + sz x ≤ sz f' + sz x
    omega
  | @right f x x' _ ih =>
    have := ih ht.app_inv.2
    show sz f + sz x ≤ sz f + sz x'
    omega

theorem sz_wsteps {t u : Term} (ht : PureS t) (h : WSteps t u) : sz t ≤ sz u := by
  induction h with
  | refl => exact Nat.le_refl _
  | step s _ ih => exact Nat.le_trans (sz_wstep ht s) (ih (wstep_pure s ht).1)

/-! ## The pure terms of bounded size -/

/-- A list containing every pure term of size `≤ n + 1` (`mem_gen`). -/
def gen : Nat → List Term
  | 0 => [S]
  | n + 1 => S :: (gen n).flatMap fun a => (gen n).map fun b => a ⬝ b

theorem mem_gen : ∀ (n : Nat) {a : Term}, PureS a → sz a ≤ n + 1 → a ∈ gen n := by
  intro n
  induction n with
  | zero =>
    intro a ha h
    cases ha with
    | S => exact List.mem_singleton.mpr rfl
    | @app f x _ _ =>
      have := sz_app_ge f x
      omega
  | succ n ih =>
    intro a ha h
    cases ha with
    | S => exact List.mem_cons_self
    | @app f x hf hx =>
      have h1 := sz_pos f
      have h2 := sz_pos x
      have h3 : sz f + sz x ≤ n + 1 + 1 := h
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨f, ih hf (by omega), List.mem_map.mpr ⟨x, ih hx (by omega), rfl⟩⟩)

/-- Remove the first occurrence of `a`.  (Core's `List.erase` lemmas carry `Classical.choice`.) -/
def rm (a : Term) : List Term → List Term
  | [] => []
  | b :: m => if b = a then m else b :: rm a m

theorem length_rm {a : Term} : ∀ {m : List Term}, a ∈ m → (rm a m).length + 1 = m.length
  | [], h => absurd h List.not_mem_nil
  | b :: m, h => by
    rcases Decidable.em (b = a) with e | e
    · show (if b = a then m else b :: rm a m).length + 1 = m.length + 1
      rw [if_pos e]
    · show (if b = a then m else b :: rm a m).length + 1 = m.length + 1
      rw [if_neg e]
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd h'.symm e
      · exact congrArg (· + 1) (length_rm h')

theorem mem_rm {a c : Term} (hne : c ≠ a) : ∀ {m : List Term}, c ∈ m → c ∈ rm a m
  | [], h => absurd h List.not_mem_nil
  | b :: m, h => by
    rcases Decidable.em (b = a) with e | e
    · show c ∈ (if b = a then m else b :: rm a m)
      rw [if_pos e]
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd (h'.trans e) hne
      · exact h'
    · show c ∈ (if b = a then m else b :: rm a m)
      rw [if_neg e]
      rcases List.mem_cons.mp h with h' | h'
      · rw [h']; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_rm hne h')

/-- Pigeonhole: a list without repetitions inside `m` is no longer than `m`. -/
theorem length_le_of_nodup_subset : ∀ (l m : List Term), l.Nodup → (∀ a, a ∈ l → a ∈ m) →
    l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intro m _ _; exact Nat.zero_le _
  | cons a l ih =>
    intro m hn hs
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hn
    have h1 := ih (rm a m) hl fun b hb =>
      mem_rm (fun (e : b = a) => ha (e ▸ hb)) (hs b (List.mem_cons_of_mem _ hb))
    have h2 := length_rm (hs a List.mem_cons_self)
    exact h2 ▸ Nat.succ_le_succ h1

/-- **A reduction path of a pure term repeats no term** (from `HeadRec.no_ground_loop`).  The
list `l` holds the terms passed before `w`. -/
theorem path_nodup {t w : Term} (ht : PureS t) (h : WSteps t w) :
    ∃ l : List Term, l.Nodup ∧ (∀ a, a ∈ l → WSteps t a ∧ WSteps a w) ∧
      w ∈ reachN l.length t := by
  induction h with
  | refl t => exact ⟨[], List.nodup_nil, fun _ h => absurd h List.not_mem_nil, reachN_self _ _⟩
  | @step t t' w s hs ih =>
    obtain ⟨l, hn, hl, hw⟩ := ih (wstep_pure s ht).1
    refine ⟨t :: l,
      List.nodup_cons.mpr ⟨fun hm => no_ground_loop ht s (hl t hm).1 .refl, hn⟩, ?_, ?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with e | ha
      · rw [e]; exact ⟨.refl _, .step s hs⟩
      · exact ⟨.step s (hl a ha).1, (hl a ha).2⟩
    · show w ∈ reachN (l.length + 1) t
      rw [reachN, List.mem_cons, List.mem_flatMap]
      exact .inr ⟨t', mem_reducts.mpr s, hw⟩

/-! ## (a) The reducts of bounded size, and the decision procedure -/

/-- **The reducts of `t` of size `≤ s`** (for pure `t`: `mem_reductsUpTo`). -/
def reductsUpTo (s : Nat) (t : Term) : List Term :=
  (reachN (gen s).length t).filter fun a => decide (sz a ≤ s)

/-- Soundness needs no purity. -/
theorem reductsUpTo_sound {s : Nat} {t w : Term} (h : w ∈ reductsUpTo s t) :
    WSteps t w ∧ sz w ≤ s := by
  obtain ⟨h1, h2⟩ := List.mem_filter.mp h
  exact ⟨reachN_sound h1, of_decide_eq_true h2⟩

/-- **`reductsUpTo s t` is exactly the set of reducts of `t` of size `≤ s`.** -/
theorem mem_reductsUpTo {s : Nat} {t w : Term} (ht : PureS t) :
    w ∈ reductsUpTo s t ↔ WSteps t w ∧ sz w ≤ s := by
  refine ⟨reductsUpTo_sound, ?_⟩
  rintro ⟨h, hs⟩
  obtain ⟨l, hn, hl, hw⟩ := path_nodup ht h
  have hlen : l.length ≤ (gen s).length := length_le_of_nodup_subset l (gen s) hn fun a ha => by
    have hp := (fold_wsteps (hl a ha).1 ht).1
    have := sz_wsteps hp (hl a ha).2
    exact mem_gen s hp (by omega)
  exact List.mem_filter.mpr ⟨reachN_le hw hlen, decide_eq_true hs⟩

/-- Do `t` and `u` have a common reduct of size `≤ s`? -/
def convWithin (s : Nat) (t u : Term) : Bool :=
  (reductsUpTo s t).any fun a => decide (a ∈ reductsUpTo s u)

theorem convWithin_iff {s : Nat} {t u : Term} (ht : PureS t) (hu : PureS u) :
    convWithin s t u = true ↔ ∃ w, WSteps t w ∧ WSteps u w ∧ sz w ≤ s := by
  unfold convWithin
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, h1, h2⟩
    exact ⟨a, (reductsUpTo_sound h1).1, (reductsUpTo_sound (of_decide_eq_true h2)).1,
      (reductsUpTo_sound h1).2⟩
  · rintro ⟨w, h1, h2, hs⟩
    exact ⟨w, (mem_reductsUpTo ht).mpr ⟨h1, hs⟩, decide_eq_true ((mem_reductsUpTo hu).mpr ⟨h2, hs⟩)⟩

/-- A positive answer is always right: no purity, no hypothesis. -/
theorem conv_of_convWithin {s : Nat} {t u : Term} (h : convWithin s t u = true) : Conv t u := by
  unfold convWithin at h
  rw [List.any_eq_true] at h
  obtain ⟨a, h1, h2⟩ := h
  exact conv_iff_join.mpr ⟨a, (reductsUpTo_sound h1).1, (reductsUpTo_sound (of_decide_eq_true h2)).1⟩

/-- **Small Join** with bound `g`: convertible pure terms have a common reduct of size at most
`g |t| |u|`.  A hypothesis.  Classically some (noncomputable) `g` exists trivially; the open
question is whether a computable `g` works. -/
def SmallJoin (g : Nat → Nat → Nat) : Prop :=
  ∀ t u, PureS t → PureS u → Conv t u → ∃ w, WSteps t w ∧ WSteps u w ∧ sz w ≤ g (sz t) (sz u)

/-- The decision procedure given a bound `g`: search for a common reduct of size
`≤ g |t| |u|`. -/
def convB (g : Nat → Nat → Nat) (t u : Term) : Bool := convWithin (g (sz t) (sz u)) t u

/-- **Small Join ⟹ the word problem for S is decided by `convB g`.** -/
theorem smallJoin_decides {g : Nat → Nat → Nat} (h : SmallJoin g) {t u : Term} (ht : PureS t)
    (hu : PureS u) : Conv t u ↔ convB g t u = true :=
  ⟨fun hc => (convWithin_iff ht hu).mpr (h t u ht hu hc), conv_of_convWithin⟩

theorem smallJoin_em {g : Nat → Nat → Nat} (h : SmallJoin g) {t u : Term} (ht : PureS t)
    (hu : PureS u) : Conv t u ∨ ¬ Conv t u := by
  cases hb : convB g t u with
  | true => exact .inl ((smallJoin_decides h ht hu).mpr hb)
  | false => exact .inr fun hc => by rw [(smallJoin_decides h ht hu).mp hc] at hb; cases hb

/-- The `Decidable` instance that Small Join gives (data: it runs `convB g`). -/
def smallJoinDecidable {g : Nat → Nat → Nat} (h : SmallJoin g) {t u : Term} (ht : PureS t)
    (hu : PureS u) : Decidable (Conv t u) :=
  decidable_of_iff _ (smallJoin_decides h ht hu).symm

/-! ## Clean terms: the argument of a redex is never `S` -/

/-- `ArgS A t`: `t` is a pure S-term in which every application `a ⬝ S` has `A a`. -/
def ArgS (A : Term → Prop) : Term → Prop
  | .app a b => ArgS A a ∧ ArgS A b ∧ (b = S → A a)
  | .S => True
  | .K => False
  | .I => False

theorem argS_pure {A : Term → Prop} : ∀ {t : Term}, ArgS A t → PureS t
  | .S, _ => .S
  | .K, h => h.elim
  | .I, h => h.elim
  | .app _ _, h => .app (argS_pure h.1) (argS_pure h.2.1)

theorem no_step_S {t : Term} : ¬ WStep S t := fun h => nomatch h

theorem no_step_SS {t : Term} : ¬ WStep (S ⬝ S) t := by
  intro h
  cases h with
  | left _ h => cases h
  | right _ h => cases h

theorem no_step_SSS {t : Term} : ¬ WStep (S ⬝ S ⬝ S) t := by
  intro h
  cases h with
  | left _ h => exact no_step_SS h
  | right _ h => cases h

/-- **If `A` allows only `S` and `S S`, then `A`-cleanness is preserved by a step, and the step
adds at least one leaf.** -/
theorem argS_wstep {A : Term → Prop} (hA : ∀ a, A a → a = S ∨ a = S ⬝ S) {t t' : Term}
    (h : ArgS A t) (s : WStep t t') : ArgS A t' ∧ sz t + 1 ≤ sz t' := by
  induction s with
  | S f g x =>
    obtain ⟨⟨⟨-, hf, -⟩, hg, -⟩, hx, hxS⟩ := h
    have hne : x ≠ S := fun e => by
      rcases hA _ (hxS e) with e' | e' <;> cases e'
    clear hxS
    have h2 : 2 ≤ sz x := by
      cases x with
      | S => exact absurd rfl hne
      | K => exact hx.elim
      | I => exact hx.elim
      | app a b => exact sz_app_ge a b
    refine ⟨⟨⟨hf, hx, fun e => absurd e hne⟩, ⟨hg, hx, fun e => absurd e hne⟩,
      fun e => nomatch e⟩, ?_⟩
    clear hne hf hg hx hA
    show 1 + sz f + sz g + sz x + 1 ≤ sz f + sz x + (sz g + sz x)
    omega
  | K x y => exact h.1.1.elim
  | I x => exact h.1.elim
  | @left f f' x s ih =>
    obtain ⟨hf, hx, hxS⟩ := h
    obtain ⟨hf', hsz⟩ := ih hf
    refine ⟨⟨hf', hx, fun e => ?_⟩, ?_⟩
    · rcases hA _ (hxS e) with e' | e'
      · rw [e'] at s; exact absurd s no_step_S
      · rw [e'] at s; exact absurd s no_step_SS
    · clear hxS hA ih
      show sz f + sz x + 1 ≤ sz f' + sz x
      omega
  | @right f x x' s ih =>
    obtain ⟨hf, hx, hxS⟩ := h
    obtain ⟨hx', hsz⟩ := ih hx
    refine ⟨⟨hf, hx', fun e => ?_⟩, ?_⟩
    · rw [e] at hsz
      have h1 := sz_pos x
      have h2 : sz x + 1 ≤ 1 := hsz
      exact absurd (Nat.le_of_succ_le_succ h2) (Nat.not_le_of_gt h1)
    · clear hxS hA ih
      show sz f + sz x + 1 ≤ sz f + sz x'
      omega

/-! ## The chain rank -/

/-- The length of the chain `S S (S S (… (S (S S S))))` that `t` is, or `0` if `t` is not one:
`cr (S P) = 1`, `cr (S S c) = cr c + 1` for a chain `c`. -/
def cr : Term → Nat
  | .app a b =>
    if a = S then (if b = S ⬝ S ⬝ S then 1 else 0)
    else if a = S ⬝ S then (if cr b = 0 then 0 else cr b + 1)
    else 0
  | _ => 0

theorem cr_app (a b : Term) : cr (a ⬝ b) =
    if a = S then (if b = S ⬝ S ⬝ S then 1 else 0)
    else if a = S ⬝ S then (if cr b = 0 then 0 else cr b + 1)
    else 0 := rfl

theorem cr_app_pos {a b : Term} (h : 0 < cr (a ⬝ b)) :
    (a = S ∧ b = S ⬝ S ⬝ S) ∨ (a = S ⬝ S ∧ 0 < cr b) := by
  rw [cr_app] at h
  rcases Decidable.em (a = S) with h1 | h1
  · rw [if_pos h1] at h
    rcases Decidable.em (b = S ⬝ S ⬝ S) with h2 | h2
    · exact .inl ⟨h1, h2⟩
    · rw [if_neg h2] at h; exact absurd h (Nat.lt_irrefl 0)
  · rw [if_neg h1] at h
    rcases Decidable.em (a = S ⬝ S) with h2 | h2
    · rw [if_pos h2] at h
      rcases Decidable.em (cr b = 0) with h3 | h3
      · rw [if_pos h3] at h; exact absurd h (Nat.lt_irrefl 0)
      · exact .inr ⟨h2, Nat.pos_of_ne_zero h3⟩
    · rw [if_neg h2] at h; exact absurd h (Nat.lt_irrefl 0)

/-- A chain is normal. -/
theorem cr_pos_normal : ∀ (t : Term), 0 < cr t → ∀ t', ¬ WStep t t' := by
  intro t
  induction t with
  | S => intro h; exact absurd h (Nat.lt_irrefl 0)
  | K => intro h; exact absurd h (Nat.lt_irrefl 0)
  | I => intro h; exact absurd h (Nat.lt_irrefl 0)
  | app a b _ ihb =>
    intro h t' s
    rcases cr_app_pos h with ⟨e1, e2⟩ | ⟨e1, hb⟩
    · rw [e1, e2] at s
      cases s with
      | left _ h => cases h
      | right _ h => exact no_step_SSS h
    · rw [e1] at s
      cases s with
      | left _ h => exact no_step_SS h
      | right _ h => exact ihb hb _ h

/-- The length of the longest chain occurring in `t`. -/
def rk : Term → Nat
  | .app a b => max (cr (a ⬝ b)) (max (rk a) (rk b))
  | _ => 0

theorem rk_app (a b : Term) : rk (a ⬝ b) = max (cr (a ⬝ b)) (max (rk a) (rk b)) := rfl

theorem cr_le_rk : ∀ t : Term, cr t ≤ rk t
  | .S => Nat.le_refl _
  | .K => Nat.le_refl _
  | .I => Nat.le_refl _
  | .app _ _ => Nat.le_max_left _ _

theorem cr_app_le (a b : Term) : cr (a ⬝ b) ≤ rk b + 1 := by
  have := cr_le_rk b
  rw [cr_app]
  split
  · split <;> omega
  · split
    · split <;> omega
    · omega

/-- **A step lowers the chain rank by at most one.** -/
theorem rk_step {t t' : Term} (ht : PureS t) (s : WStep t t') : rk t ≤ rk t' + 1 := by
  induction s with
  | S f g x =>
    have c0 : cr (S ⬝ f ⬝ g ⬝ x) = 0 := by
      rcases Nat.eq_zero_or_pos (cr (S ⬝ f ⬝ g ⬝ x)) with h | h
      · exact h
      · rcases cr_app_pos h with ⟨e, _⟩ | ⟨e, _⟩ <;> cases e
    have c1 := cr_app_le (S ⬝ f) g
    have c2 := cr_app_le S f
    have e1 : rk (S ⬝ f ⬝ g ⬝ x) = max (cr (S ⬝ f ⬝ g ⬝ x)) (max (max (cr (S ⬝ f ⬝ g))
        (max (max (cr (S ⬝ f)) (max 0 (rk f))) (rk g))) (rk x)) := rfl
    have e2 : rk (f ⬝ x ⬝ (g ⬝ x)) = max (cr (f ⬝ x ⬝ (g ⬝ x)))
        (max (max (cr (f ⬝ x)) (max (rk f) (rk x))) (max (cr (g ⬝ x)) (max (rk g) (rk x)))) := rfl
    rw [e1, e2, c0]
    omega
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | @left f f' x s ih =>
    have c0 : cr (f ⬝ x) = 0 := by
      rcases Nat.eq_zero_or_pos (cr (f ⬝ x)) with h | h
      · exact h
      · rcases cr_app_pos h with ⟨e, _⟩ | ⟨e, _⟩
        · rw [e] at s; exact absurd s no_step_S
        · rw [e] at s; exact absurd s no_step_SS
    have := ih ht.app_inv.1
    rw [rk_app f x, rk_app f' x, c0]
    omega
  | @right f x x' s ih =>
    have c0 : cr (f ⬝ x) = 0 := by
      rcases Nat.eq_zero_or_pos (cr (f ⬝ x)) with h | h
      · exact h
      · rcases cr_app_pos h with ⟨_, e⟩ | ⟨_, hx⟩
        · rw [e] at s; exact absurd s no_step_SSS
        · exact absurd s (cr_pos_normal x hx _)
    have := ih ht.app_inv.2
    rw [rk_app f x, rk_app f x', c0]
    omega

/-- A term in which `S` is an argument of `S` only contains no chain (no `S S S`). -/
theorem argS_rk : ∀ {t : Term}, ArgS (fun a => a = S) t → rk t = 0 := by
  intro t
  induction t with
  | S => intro _; rfl
  | K => intro _; rfl
  | I => intro _; rfl
  | app a b iha ihb =>
    intro h
    obtain ⟨ha, hb, _⟩ := h
    have c0 : cr (a ⬝ b) = 0 := by
      rcases Nat.eq_zero_or_pos (cr (a ⬝ b)) with h | h
      · exact h
      · rcases cr_app_pos h with ⟨_, e⟩ | ⟨_, hpos⟩
        · rw [e] at hb
          have := hb.2.2 rfl
          cases this
        · have := cr_le_rk b
          have := ihb hb
          omega
    rw [rk_app, c0, iha ha, ihb hb]
    rfl

/-- **`sz + rk` never decreases along a reduction of an `{S, S S}`-clean term.** -/
theorem pot_wsteps {A : Term → Prop} (hA : ∀ a, A a → a = S ∨ a = S ⬝ S) {t w : Term}
    (h : ArgS A t) (r : WSteps t w) : ArgS A w ∧ sz t + rk t ≤ sz w + rk w := by
  induction r with
  | refl => exact ⟨h, Nat.le_refl _⟩
  | step s _ ih =>
    obtain ⟨h', hsz⟩ := argS_wstep hA h s
    obtain ⟨hw, hpot⟩ := ih h'
    have := rk_step (argS_pure h) s
    exact ⟨hw, by omega⟩

/-! ## (b) The family -/

namespace Family

def P : Term := S ⬝ S ⬝ S
def Q : Term := S ⬝ (S ⬝ S)
def R : Term := S ⬝ S

def fk : Nat → Term
  | 0 => S ⬝ P
  | k + 1 => S ⬝ S ⬝ fk k

def gk : Nat → Term
  | 0 => S ⬝ Q
  | k + 1 => S ⬝ S ⬝ gk k

/-- `t_k = f_k P R`. -/
def tk (k : Nat) : Term := fk k ⬝ P ⬝ R

/-- `u_k = g_k Q Q`. -/
def uk (k : Nat) : Term := gk k ⬝ Q ⬝ Q

/-- The common reduct `Q Q (Q Q (… (Q Q (Q Q))))`, with `k + 2` copies of `Q Q`. -/
def wk : Nat → Term
  | 0 => Q ⬝ Q ⬝ (Q ⬝ Q)
  | k + 1 => Q ⬝ Q ⬝ wk k

theorem sz_fk : ∀ k, sz (fk k) = 2 * k + 4
  | 0 => rfl
  | k + 1 => by
    show 1 + 1 + sz (fk k) = 2 * (k + 1) + 4
    rw [sz_fk k]; omega

theorem sz_gk : ∀ k, sz (gk k) = 2 * k + 4
  | 0 => rfl
  | k + 1 => by
    show 1 + 1 + sz (gk k) = 2 * (k + 1) + 4
    rw [sz_gk k]; omega

theorem sz_tk (k : Nat) : sz (tk k) = 2 * k + 9 := by
  show sz (fk k) + 3 + 2 = 2 * k + 9
  rw [sz_fk k]

theorem sz_uk (k : Nat) : sz (uk k) = 2 * k + 10 := by
  show sz (gk k) + 3 + 3 = 2 * k + 10
  rw [sz_gk k]

theorem sz_wk : ∀ k, sz (wk k) = 6 * k + 12
  | 0 => rfl
  | k + 1 => by
    show 6 + sz (wk k) = 6 * (k + 1) + 12
    rw [sz_wk k]; omega

/-- `P R → S R (S R) = Q Q`. -/
theorem PR_step : WStep (P ⬝ R) (Q ⬝ Q) := WStep.S S S R

/-- `t_k ↠ Q Q (… (Q Q))`. -/
theorem tk_join : ∀ k, WSteps (tk k) (wk k)
  | 0 => .step (WStep.S P P R) (.app (.single PR_step) (.single PR_step))
  | k + 1 =>
    .step (.left R (WStep.S S (fk k) P))
      (.step (WStep.S P (fk k ⬝ P) R) (.app (.single PR_step) (tk_join k)))

/-- `u_k ↠ Q Q (… (Q Q))`. -/
theorem uk_join : ∀ k, WSteps (uk k) (wk k)
  | 0 => .single (WStep.S Q Q Q)
  | k + 1 =>
    .step (.left Q (WStep.S S (gk k) Q))
      (.step (WStep.S Q (gk k ⬝ Q) Q) (.right (Q ⬝ Q) (uk_join k)))

/-- **`t_k` and `u_k` are convertible.** -/
theorem conv_family (k : Nat) : Conv (tk k) (uk k) :=
  conv_iff_join.mpr ⟨wk k, tk_join k, uk_join k⟩

theorem fk_ne (k : Nat) : fk k ≠ S := by
  cases k <;> exact fun e => nomatch e

theorem gk_ne (k : Nat) : gk k ≠ S := by
  cases k <;> exact fun e => nomatch e

theorem argS_fk : ∀ k, ArgS (fun a => a = S ∨ a = S ⬝ S) (fk k)
  | 0 => ⟨trivial, ⟨⟨trivial, trivial, fun _ => .inl rfl⟩, trivial, fun _ => .inr rfl⟩,
      fun e => nomatch e⟩
  | k + 1 => ⟨⟨trivial, trivial, fun _ => .inl rfl⟩, argS_fk k, fun e => absurd e (fk_ne k)⟩

theorem argS_tk (k : Nat) : ArgS (fun a => a = S ∨ a = S ⬝ S) (tk k) :=
  ⟨⟨argS_fk k, ⟨⟨trivial, trivial, fun _ => .inl rfl⟩, trivial, fun _ => .inr rfl⟩,
      fun e => nomatch e⟩,
    ⟨trivial, trivial, fun _ => .inl rfl⟩, fun e => nomatch e⟩

theorem argS_Q : ArgS (fun a => a = S) Q :=
  ⟨trivial, ⟨trivial, trivial, fun _ => rfl⟩, fun e => nomatch e⟩

theorem argS_gk : ∀ k, ArgS (fun a => a = S) (gk k)
  | 0 => ⟨trivial, argS_Q, fun e => nomatch e⟩
  | k + 1 => ⟨⟨trivial, trivial, fun _ => rfl⟩, argS_gk k, fun e => absurd e (gk_ne k)⟩

theorem argS_uk (k : Nat) : ArgS (fun a => a = S) (uk k) :=
  ⟨⟨argS_gk k, argS_Q, fun e => nomatch e⟩, argS_Q, fun e => nomatch e⟩

theorem pure_tk (k : Nat) : PureS (tk k) := argS_pure (argS_tk k)

theorem pure_uk (k : Nat) : PureS (uk k) := argS_pure (argS_uk k)

theorem cr_fk : ∀ k, cr (fk k) = k + 1
  | 0 => rfl
  | k + 1 => by
    show cr (S ⬝ S ⬝ fk k) = k + 1 + 1
    rw [cr_app, if_neg (fun e => nomatch e), if_pos rfl, cr_fk k, if_neg (Nat.succ_ne_zero k)]

theorem rk_tk (k : Nat) : k + 1 ≤ rk (tk k) := by
  have h1 := cr_le_rk (fk k)
  have h2 := cr_fk k
  show k + 1 ≤ rk (fk k ⬝ P ⬝ R)
  rw [rk_app, rk_app (fk k) P]
  omega

/-- No reduct of `t_k` that is `{S}`-clean (contains no `a ⬝ S` with `a ≠ S`) is smaller than
`3k + 10`. -/
theorem tk_clean_lower {k : Nat} {w : Term} (h : WSteps (tk k) w)
    (hw : ArgS (fun a => a = S) w) : 3 * k + 10 ≤ sz w := by
  have h1 := (pot_wsteps (fun _ h => h) (argS_tk k) h).2
  have h2 := argS_rk hw
  have h3 := rk_tk k
  have h4 := sz_tk k
  omega

/-- **The family bound.**  Every common reduct of `t_k` and `u_k` has size at least
`3k + 10 = max (|t_k|, |u_k|) + k`. -/
theorem family_lower {k : Nat} {w : Term} (h1 : WSteps (tk k) w) (h2 : WSteps (uk k) w) :
    3 * k + 10 ≤ sz w :=
  tk_clean_lower h1 (pot_wsteps (fun _ h => .inl h) (argS_uk k) h2).1

/-- A Small Join bound is at least `3k + 10` at `(2k + 9, 2k + 10)`. -/
theorem smallJoin_lower {g : Nat → Nat → Nat} (h : SmallJoin g) (k : Nat) :
    3 * k + 10 ≤ g (2 * k + 9) (2 * k + 10) := by
  obtain ⟨w, h1, h2, hs⟩ := h (tk k) (uk k) (pure_tk k) (pure_uk k) (conv_family k)
  rw [sz_tk, sz_uk] at hs
  exact Nat.le_trans (family_lower h1 h2) hs

/-- **No bound of the form `max |t| |u| + c` is a Small Join bound.** -/
theorem not_smallJoin_max_add (c : Nat) : ¬ SmallJoin fun a b => max a b + c := by
  intro h
  have := smallJoin_lower h (c + 1)
  omega

end Family

end WordProblem
