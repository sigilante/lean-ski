import Ski.Converse

open Term

/-!
# Graph reduction with update in place, correct against L1

L2's heap is write-once (`Ski/Heap.lean`): it shares structure but not
work, so its contraction count is L1's.  Graph reduction proper overwrites
a contracted redex in place, so every pointer to it sees the contractum.
This file builds that machine and proves it correct against L1's
normal-order reduction, up to weak reduction of the value's arguments.

**The machine** (`gstep`).  A heap of cells (`S`, `K`, `I`, `app f x`, and
an indirection `ind p`), a fixed root, a head pointer and a spine of the
application cells above the head.
- An application at the head unwinds onto the spine; an indirection is
  followed.
- `I x`: the cell holding `I x` becomes `ind x`.
- `K x y`: the cell holding `K x y` becomes `ind x`.
- `S x y z`: two fresh cells `x z` and `y z`, and the cell holding
  `S x y z` becomes their application.  `z` is shared, not copied.

**Decoding** (`Dec h a t n`) reads address `a` as a term `t`, by a
derivation of `n` nodes; it is relational, so a cyclic heap has no decoding
and no acyclicity needs stating.

**One update is a parallel step** (`dec_update`).  Overwriting a redex's
cell contracts every occurrence of it in every decoding at once, which is
a parallel reduction (`Par`).  At the head the machine contracts the head
redex, so the root's decoding takes a head step and then a parallel step
(`gstep_inv`): `D → D₁ ⇉ D'`.

**Correctness against L1.**
- `graph_sound`: if the machine halts from a loaded term `t` after `c`
  contractions, the root decodes to a weak head normal form `v`, `t`
  evaluates under L1 to some `u` with `u ↠ v`, and `c` is at most L1's
  contraction count.  So `v` has `u`'s head and arity (`graph_spine`), its
  arguments possibly further reduced by the shared updates; it is `u`
  exactly when `u` is a combinator (`graph_leaf`).
- `graph_complete`: if `t` evaluates under L1 in `n` contractions, the
  machine halts, after at most `n` contractions, on such a `v`.

The count bound is `StepsN.wtail_lt`: a head step followed by any weak
reduction leaves strictly fewer contractions to normal form.  So sharing
never costs contractions; `bench/GraphCost.lean` measures what it saves.
-/

namespace Graph

inductive GCell where
  | S | K | I
  | app (f x : Nat)
  | ind (p : Nat)
  deriving DecidableEq, Repr

abbrev Heap := List GCell

/-- `Dec h a t n`: address `a` decodes to `t`, by a derivation of `n` nodes. -/
inductive Dec (h : Heap) : Nat → Term → Nat → Prop
  | S {a : Nat} : h[a]? = some .S → Dec h a .S 1
  | K {a : Nat} : h[a]? = some .K → Dec h a .K 1
  | I {a : Nat} : h[a]? = some .I → Dec h a .I 1
  | app {a f x : Nat} {tf tx : Term} {nf nx : Nat} : h[a]? = some (.app f x) →
      Dec h f tf nf → Dec h x tx nx → Dec h a (tf ⬝ tx) (nf + nx + 1)
  | ind {a p : Nat} {t : Term} {n : Nat} : h[a]? = some (.ind p) →
      Dec h p t n → Dec h a t (n + 1)

theorem Dec.det {h : Heap} {a : Nat} {t t' : Term} {n n' : Nat} (d : Dec h a t n) (d' : Dec h a t' n') :
    t = t' ∧ n = n' := by
  induction d generalizing t' n' with
  | S e => cases d' <;> simp_all
  | K e => cases d' <;> simp_all
  | I e => cases d' <;> simp_all
  | app e _ _ ihf ihx =>
    cases d' with
    | app e' df dx =>
      rw [e] at e'
      cases e'
      obtain ⟨r1, r2⟩ := ihf df
      obtain ⟨r3, r4⟩ := ihx dx
      subst r1; subst r2; subst r3; subst r4
      exact ⟨rfl, rfl⟩
    | S e' => rw [e] at e'; cases e'
    | K e' => rw [e] at e'; cases e'
    | I e' => rw [e] at e'; cases e'
    | ind e' _ => rw [e] at e'; cases e'
  | ind e _ ih =>
    cases d' with
    | ind e' dp =>
      rw [e] at e'
      cases e'
      obtain ⟨r1, r2⟩ := ih dp
      subst r1; subst r2
      exact ⟨rfl, rfl⟩
    | S e' => rw [e] at e'; cases e'
    | K e' => rw [e] at e'; cases e'
    | I e' => rw [e] at e'; cases e'
    | app e' _ _ => rw [e] at e'; cases e'

theorem Dec.app_inv {h : Heap} {a f x : Nat} {t : Term} {n : Nat} (d : Dec h a t n)
    (e : h[a]? = some (.app f x)) :
    ∃ tf tx nf nx, t = tf ⬝ tx ∧ n = nf + nx + 1 ∧ Dec h f tf nf ∧ Dec h x tx nx := by
  cases d with
  | app e' df dx =>
    rw [e] at e'
    cases e'
    exact ⟨_, _, _, _, rfl, rfl, df, dx⟩
  | S e' => rw [e] at e'; cases e'
  | K e' => rw [e] at e'; cases e'
  | I e' => rw [e] at e'; cases e'
  | ind e' _ => rw [e] at e'; cases e'

theorem Dec.ind_inv {h : Heap} {a p : Nat} {t : Term} {n : Nat} (d : Dec h a t n)
    (e : h[a]? = some (.ind p)) : ∃ m, n = m + 1 ∧ Dec h p t m := by
  cases d with
  | ind e' dp =>
    rw [e] at e'
    cases e'
    exact ⟨_, rfl, dp⟩
  | S e' => rw [e] at e'; cases e'
  | K e' => rw [e] at e'; cases e'
  | I e' => rw [e] at e'; cases e'
  | app e' _ _ => rw [e] at e'; cases e'

theorem Dec.S_inv {h : Heap} {a : Nat} {t : Term} {n : Nat} (d : Dec h a t n)
    (e : h[a]? = some .S) : t = .S := by
  cases d <;> simp_all

theorem Dec.K_inv {h : Heap} {a : Nat} {t : Term} {n : Nat} (d : Dec h a t n)
    (e : h[a]? = some .K) : t = .K := by
  cases d <;> simp_all

theorem Dec.I_inv {h : Heap} {a : Nat} {t : Term} {n : Nat} (d : Dec h a t n)
    (e : h[a]? = some .I) : t = .I := by
  cases d <;> simp_all

theorem Dec.cell {h : Heap} {a : Nat} {t : Term} {n : Nat} (d : Dec h a t n) : ∃ c, h[a]? = some c := by
  cases d with
  | S e => exact ⟨_, e⟩
  | K e => exact ⟨_, e⟩
  | I e => exact ⟨_, e⟩
  | app e _ _ => exact ⟨_, e⟩
  | ind e _ => exact ⟨_, e⟩

-- ---------------------------------------------------------------------------
-- Indirection chains and the spine
-- ---------------------------------------------------------------------------

/-- `Path h b c`: a chain of indirections from `b` to `c`. -/
inductive Path (h : Heap) : Nat → Nat → Prop
  | refl (b : Nat) : Path h b b
  | ind {b p c : Nat} : h[b]? = some (.ind p) → Path h p c → Path h b c

theorem Path.dec {h : Heap} {b c : Nat} (hp : Path h b c) :
    ∀ {t : Term} {n : Nat}, Dec h b t n → ∃ n', n' ≤ n ∧ Dec h c t n' := by
  induction hp with
  | refl b => exact fun d => ⟨_, Nat.le_refl _, d⟩
  | ind e _ ih =>
    intro t n d
    obtain ⟨m, hm, dp⟩ := d.ind_inv e
    obtain ⟨n', h1, h2⟩ := ih dp
    exact ⟨n', by rw [hm]; exact Nat.le_succ_of_le h1, h2⟩

theorem Path.dec_back {h : Heap} {b c : Nat} (hp : Path h b c) :
    ∀ {t : Term} {n : Nat}, Dec h c t n → ∃ n', Dec h b t n' := by
  induction hp with
  | refl b => exact fun d => ⟨_, d⟩
  | ind e _ ih =>
    intro t n d
    obtain ⟨n', d'⟩ := ih d
    exact ⟨_, .ind e d'⟩

theorem Path.snoc {h : Heap} {b c p : Nat} (hp : Path h b c) (e : h[c]? = some (.ind p)) :
    Path h b p := by
  induction hp with
  | refl b => exact .ind e (.refl p)
  | ind e' _ ih => exact .ind e' (ih e)

/-- The spine from the head `c` up to the root: each spine cell is an
    application whose function reaches the cell below by indirections. -/
def SpineOK (h : Heap) : Nat → List Nat → Nat → Prop
  | c, [], root => Path h root c
  | c, s :: sp, root => ∃ f x, h[s]? = some (.app f x) ∧ Path h f c ∧ SpineOK h s sp root

/-- The spine's arguments, decoded. -/
inductive Args (h : Heap) : List Nat → List Term → Prop
  | nil : Args h [] []
  | cons {s f x : Nat} {t : Term} {m : Nat} {sp : List Nat} {as : List Term} :
      h[s]? = some (.app f x) → Dec h x t m → Args h sp as → Args h (s :: sp) (t :: as)

/-- The root decodes to the head's term applied to the spine's arguments. -/
theorem dec_spine {h : Heap} {root : Nat} {D : Term} {n : Nat} (dr : Dec h root D n) :
    ∀ (sp : List Nat) (c : Nat), SpineOK h c sp root →
      ∃ H nH as, Dec h c H nH ∧ D = appT H as ∧ Args h sp as
  | [], c, hp => by
    obtain ⟨n', _, d⟩ := Path.dec hp dr
    exact ⟨D, n', [], d, rfl, .nil⟩
  | s :: sp, c, ⟨f, x, hs, hp, hrest⟩ => by
    obtain ⟨Hs, nHs, as, ds, eD, ha⟩ := dec_spine dr sp s hrest
    obtain ⟨tf, tx, nf, nx, eH, _, df, dx⟩ := ds.app_inv hs
    obtain ⟨n', _, dc⟩ := Path.dec hp df
    refine ⟨tf, n', tx :: as, dc, ?_, .cons hs dx ha⟩
    rw [eD, eH]
    rfl

/-- Conversely, the head's term and the arguments decode the root. -/
theorem spine_dec {h : Heap} {root : Nat} :
    ∀ (sp : List Nat) (c : Nat) (H : Term) (nH : Nat) (as : List Term),
      SpineOK h c sp root → Dec h c H nH → Args h sp as → ∃ n, Dec h root (appT H as) n
  | [], c, H, nH, [], hp, d, _ => Path.dec_back hp d
  | s :: sp, c, H, nH, t :: as, ⟨f, x, hs, hp, hrest⟩, d, .cons hs' dx ha => by
    rw [hs] at hs'
    cases hs'
    obtain ⟨n', df⟩ := Path.dec_back hp d
    exact spine_dec sp s (H ⬝ t) _ as hrest (.app hs df dx) ha
  | [], _, _, _, _ :: _, _, _, h => by cases h
  | _ :: _, _, _, _, [], _, _, h => by cases h

def size : Term → Nat
  | .app f x => size f + size x + 1
  | _ => 1

/-- Every spine cell decodes to a strictly larger term than the head. -/
theorem spine_size {h : Heap} {root : Nat} {D : Term} {n : Nat} (dr : Dec h root D n) :
    ∀ (sp : List Nat) (c : Nat) (H : Term) (nH : Nat), SpineOK h c sp root → Dec h c H nH →
      ∀ s ∈ sp, ∀ T m, Dec h s T m → size H < size T
  | [], _, _, _, _, _, _, hs, _, _, _ => by cases hs
  | s :: sp, c, H, nH, ⟨f, x, hs, hp, hrest⟩, dc, s', hs', T, m, dT => by
    obtain ⟨Hs, nHs, _, ds, _, _⟩ := dec_spine dr sp s hrest
    obtain ⟨tf, tx, nf, nx, eH, _, df, _⟩ := ds.app_inv hs
    obtain ⟨n', _, dc'⟩ := Path.dec hp df
    have eHc : H = tf := (dc.det dc').1
    have lt : size H < size Hs := by
      rw [eH, eHc]
      show size tf < size tf + size tx + 1
      exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
    cases hs' with
    | head => rw [← (ds.det dT).1]; exact lt
    | tail _ hm => exact Nat.lt_trans lt (spine_size dr sp s Hs nHs hrest ds s' hm T m dT)

/-- No spine cell is the head. -/
theorem spine_ne {h : Heap} {root c : Nat} {D : Term} {n : Nat} {sp : List Nat}
    (dr : Dec h root D n) (hs : SpineOK h c sp root) : ∀ s ∈ sp, s ≠ c := by
  intro s hm e
  obtain ⟨H, nH, _, dc, _, _⟩ := dec_spine dr sp c hs
  have := spine_size dr sp c H nH hs dc s hm H nH (e ▸ dc)
  exact Nat.lt_irrefl _ this

theorem SpineOK.follow {h : Heap} {c p root : Nat} (e : h[c]? = some (.ind p)) :
    ∀ {sp : List Nat}, SpineOK h c sp root → SpineOK h p sp root
  | [], hp => Path.snoc hp e
  | _ :: _, ⟨f, x, hs, hp, hrest⟩ => ⟨f, x, hs, Path.snoc hp e, hrest⟩

-- ---------------------------------------------------------------------------
-- An update is a parallel step
-- ---------------------------------------------------------------------------

/-- `h'` agrees with `h` at every written address but `a`. -/
def Agree (h h' : Heap) (a : Nat) : Prop := ∀ d c, d ≠ a → h[d]? = some c → h'[d]? = some c

theorem Path.agree {h h' : Heap} {a f x : Nat} (hag : Agree h h' a) (ea : h[a]? = some (.app f x))
    {b c : Nat} (hp : Path h b c) : Path h' b c := by
  induction hp with
  | refl b => exact .refl b
  | ind e _ ih =>
    refine .ind (hag _ _ ?_ e) ih
    intro hb
    rw [hb, ea] at e
    cases e

theorem SpineOK.agree {h h' : Heap} {a f x root : Nat} (hag : Agree h h' a)
    (ea : h[a]? = some (.app f x)) :
    ∀ {sp : List Nat} {c : Nat}, (∀ s ∈ sp, s ≠ a) → SpineOK h c sp root → SpineOK h' c sp root
  | [], _, _, hp => Path.agree hag ea hp
  | s :: _, _, hn, ⟨f', x', hs, hp, hrest⟩ =>
    ⟨f', x', hag _ _ (hn s (.head _)) hs, Path.agree hag ea hp,
      SpineOK.agree hag ea (fun s' hm => hn s' (.tail _ hm)) hrest⟩

/-- **Overwriting one cell with a parallel reduct of its term is a parallel
    step of every decoding.**  `hA` is the overwritten cell's case, given
    the result for every smaller derivation. -/
theorem dec_update {h h' : Heap} {a : Nat} (hag : Agree h h' a)
    (hA : ∀ r n, Dec h a r n →
      (∀ b t m, m < n → Dec h b t m → ∃ t' m', Dec h' b t' m' ∧ Par t t') →
      ∃ r' m', Dec h' a r' m' ∧ Par r r') :
    ∀ N b t n, n ≤ N → Dec h b t n → ∃ t' m', Dec h' b t' m' ∧ Par t t' := by
  intro N
  induction N with
  | zero =>
    intro b t n hn d
    cases d <;> simp_all
  | succ N ih =>
    intro b t n hn d
    have small : ∀ b t m, m < n → Dec h b t m → ∃ t' m', Dec h' b t' m' ∧ Par t t' :=
      fun b t m hm d => ih b t m (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hm hn)) d
    by_cases hb : b = a
    · subst hb
      exact hA t n d small
    · cases d with
      | S e => exact ⟨_, _, .S (hag _ _ hb e), .S⟩
      | K e => exact ⟨_, _, .K (hag _ _ hb e), .K⟩
      | I e => exact ⟨_, _, .I (hag _ _ hb e), .I⟩
      | app e df dx =>
        obtain ⟨tf', mf, df', pf⟩ := small _ _ _ (by omega) df
        obtain ⟨tx', mx, dx', px⟩ := small _ _ _ (by omega) dx
        exact ⟨_, _, .app (hag _ _ hb e) df' dx', .app pf px⟩
      | ind e dp =>
        obtain ⟨t', m', dp', pp⟩ := small _ _ _ (Nat.lt_succ_self _) dp
        exact ⟨_, _, .ind (hag _ _ hb e) dp', pp⟩

theorem dec_update' {h h' : Heap} {a : Nat} (hag : Agree h h' a)
    (hA : ∀ r n, Dec h a r n →
      (∀ b t m, m < n → Dec h b t m → ∃ t' m', Dec h' b t' m' ∧ Par t t') →
      ∃ r' m', Dec h' a r' m' ∧ Par r r')
    {b : Nat} {t : Term} {n : Nat} (d : Dec h b t n) : ∃ t' m', Dec h' b t' m' ∧ Par t t' :=
  dec_update hag hA n b t n (Nat.le_refl n) d

/-- Pointwise parallel reduction of argument lists. -/
inductive ParL : List Term → List Term → Prop
  | nil : ParL [] []
  | cons {t t' : Term} {as as' : List Term} : Par t t' → ParL as as' → ParL (t :: as) (t' :: as')

theorem par_appT : ∀ {t t' : Term} {as as' : List Term}, Par t t' → ParL as as' →
    Par (appT t as) (appT t' as')
  | _, _, [], [], hp, .nil => hp
  | t, t', a :: as, a' :: as', hp, .cons ha hl =>
    par_appT (t := t ⬝ a) (t' := t' ⬝ a') (as := as) (as' := as') (.app hp ha) hl

theorem step_appT : ∀ {t t' : Term}, Step t t' → ∀ as : List Term, Step (appT t as) (appT t' as)
  | _, _, s, [] => s
  | _, _, s, a :: as => step_appT (.left a s) as

/-- The spine's arguments under an update off the spine. -/
theorem Args.update {h h' : Heap} {a : Nat} (hag : Agree h h' a)
    (hd : ∀ {b : Nat} {t : Term} {n : Nat}, Dec h b t n → ∃ t' m', Dec h' b t' m' ∧ Par t t') :
    ∀ {sp : List Nat} {as : List Term}, (∀ s ∈ sp, s ≠ a) → Args h sp as →
      ∃ as', Args h' sp as' ∧ ParL as as'
  | [], [], _, .nil => ⟨[], .nil, .nil⟩
  | s :: _, _ :: _, hn, .cons hs dx ha => by
    obtain ⟨t', m', dx', px⟩ := hd dx
    obtain ⟨as', ha', pl⟩ := Args.update hag hd (fun s' hm => hn s' (.tail _ hm)) ha
    exact ⟨t' :: as', .cons (hag _ _ (hn s (.head _)) hs) dx' ha', .cons px pl⟩

-- ---------------------------------------------------------------------------
-- The machine
-- ---------------------------------------------------------------------------

/-- A machine state: the heap, the root, the head and the spine above it. -/
structure GM where
  heap : Heap
  root : Nat
  hd : Nat
  spine : List Nat
  deriving Repr

/-- One transition, and whether it contracts. -/
def gstep (m : GM) : Option (GM × Bool) :=
  match m.heap[m.hd]? with
  | some (.app f _) => some (⟨m.heap, m.root, f, m.hd :: m.spine⟩, false)
  | some (.ind p) => some (⟨m.heap, m.root, p, m.spine⟩, false)
  | some .I =>
    match m.spine with
    | s1 :: rest =>
      match m.heap[s1]? with
      | some (.app _ x) => some (⟨m.heap.set s1 (.ind x), m.root, s1, rest⟩, true)
      | _ => none
    | [] => none
  | some .K =>
    match m.spine with
    | s1 :: s2 :: rest =>
      match m.heap[s1]?, m.heap[s2]? with
      | some (.app _ x), some (.app _ _) => some (⟨m.heap.set s2 (.ind x), m.root, s2, rest⟩, true)
      | _, _ => none
    | _ => none
  | some .S =>
    match m.spine with
    | s1 :: s2 :: s3 :: rest =>
      match m.heap[s1]?, m.heap[s2]?, m.heap[s3]? with
      | some (.app _ x), some (.app _ y), some (.app _ z) =>
        some (⟨(m.heap ++ [GCell.app x z, GCell.app y z]).set s3 (.app m.heap.length (m.heap.length + 1)),
          m.root, s3, rest⟩, true)
      | _, _, _ => none
    | _ => none
  | none => none

/-- The transitions, as a relation. -/
inductive GStep : GM → GM → Bool → Prop
  | unwind {h : Heap} {r c f x : Nat} {sp : List Nat} : h[c]? = some (.app f x) →
      GStep ⟨h, r, c, sp⟩ ⟨h, r, f, c :: sp⟩ false
  | follow {h : Heap} {r c p : Nat} {sp : List Nat} : h[c]? = some (.ind p) →
      GStep ⟨h, r, c, sp⟩ ⟨h, r, p, sp⟩ false
  | I {h : Heap} {r c s1 f1 x : Nat} {rest : List Nat} : h[c]? = some .I →
      h[s1]? = some (.app f1 x) →
      GStep ⟨h, r, c, s1 :: rest⟩ ⟨h.set s1 (.ind x), r, s1, rest⟩ true
  | K {h : Heap} {r c s1 s2 f1 x f2 y : Nat} {rest : List Nat} : h[c]? = some .K →
      h[s1]? = some (.app f1 x) → h[s2]? = some (.app f2 y) →
      GStep ⟨h, r, c, s1 :: s2 :: rest⟩ ⟨h.set s2 (.ind x), r, s2, rest⟩ true
  | S {h : Heap} {r c s1 s2 s3 f1 x f2 y f3 z : Nat} {rest : List Nat} : h[c]? = some .S →
      h[s1]? = some (.app f1 x) → h[s2]? = some (.app f2 y) → h[s3]? = some (.app f3 z) →
      GStep ⟨h, r, c, s1 :: s2 :: s3 :: rest⟩
        ⟨(h ++ [GCell.app x z, GCell.app y z]).set s3 (.app h.length (h.length + 1)), r, s3, rest⟩ true

theorem gstep_sound {m m' : GM} {b : Bool} (hs : gstep m = some (m', b)) : GStep m m' b := by
  obtain ⟨h, r, c, sp⟩ := m
  unfold gstep at hs
  simp only at hs
  split at hs
  · rename_i f x e; cases hs; exact .unwind e
  · rename_i p e; cases hs; exact .follow e
  · rename_i e
    split at hs
    · rename_i s1 rest
      split at hs
      · rename_i f1 x e1; cases hs; exact .I e e1
      · cases hs
    · cases hs
  · rename_i e
    split at hs
    · rename_i s1 s2 rest
      split at hs
      · rename_i f1 x f2 y e1 e2; cases hs; exact .K e e1 e2
      · cases hs
    · cases hs
  · rename_i e
    split at hs
    · rename_i s1 s2 s3 rest
      split at hs
      · rename_i f1 x f2 y f3 z e1 e2 e3; cases hs; exact .S e e1 e2 e3
      · cases hs
    · cases hs
  · cases hs

/-- The machine invariant: the root decodes to `D`, and the spine is sound. -/
def Inv (m : GM) (D : Term) : Prop :=
  (∃ n, Dec m.heap m.root D n) ∧ SpineOK m.heap m.hd m.spine m.root

theorem Inv.head {m : GM} {D : Term} (hi : Inv m D) : ∃ H nH, Dec m.heap m.hd H nH := by
  obtain ⟨⟨n, dr⟩, hs⟩ := hi
  obtain ⟨H, nH, _, d, _, _⟩ := dec_spine dr _ _ hs
  exact ⟨H, nH, d⟩

theorem lt_of_get {h : Heap} {a : Nat} {c : GCell} (e : h[a]? = some c) : a < h.length := by
  by_cases hl : a < h.length
  · exact hl
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt hl)] at e
    cases e

theorem agree_set {h : Heap} {a : Nat} (c : GCell) : Agree h (h.set a c) a :=
  fun d _ hd e => by rw [List.getElem?_set_ne (Ne.symm hd)]; exact e

theorem agree_S {h : Heap} {a : Nat} (c1 c2 c : GCell) :
    Agree h ((h ++ [c1, c2]).set a c) a :=
  fun d _ hd e => by
    rw [List.getElem?_set_ne (Ne.symm hd), List.getElem?_append_left (lt_of_get e)]
    exact e

/-- The redex the `S` rule contracts, read off the spine. -/
theorem s_redex {h : Heap} {c s1 s2 s3 f1 x f2 y f3 z : Nat}
    (ec : h[c]? = some .S) (e1 : h[s1]? = some (.app f1 x)) (e2 : h[s2]? = some (.app f2 y))
    (e3 : h[s3]? = some (.app f3 z)) (p1 : Path h f1 c) (p2 : Path h f2 s1) (p3 : Path h f3 s2)
    {r : Term} {n : Nat} (d : Dec h s3 r n) :
    ∃ tx ty tz mx my mz, r = .S ⬝ tx ⬝ ty ⬝ tz ∧ Dec h x tx mx ∧ Dec h y ty my ∧ Dec h z tz mz ∧
      mx < n ∧ my < n ∧ mz < n := by
  obtain ⟨t3, tz, n3, mz, er, en, d3, dz⟩ := d.app_inv e3
  obtain ⟨n3', l3, d3'⟩ := Path.dec p3 d3
  obtain ⟨t2, ty, n2, my, e2', en2, d2, dy⟩ := d3'.app_inv e2
  obtain ⟨n2', l2, d2'⟩ := Path.dec p2 d2
  obtain ⟨t1, tx, n1, mx, e1', en1, d1, dx⟩ := d2'.app_inv e1
  obtain ⟨n1', _, d1'⟩ := Path.dec p1 d1
  have eS : t1 = .S := d1'.S_inv ec
  refine ⟨tx, ty, tz, mx, my, mz, ?_, dx, dy, dz, by omega, by omega, by omega⟩
  rw [er, e2', e1', eS]

theorem k_redex {h : Heap} {c s1 s2 f1 x f2 y : Nat}
    (ec : h[c]? = some .K) (e1 : h[s1]? = some (.app f1 x)) (e2 : h[s2]? = some (.app f2 y))
    (p1 : Path h f1 c) (p2 : Path h f2 s1) {r : Term} {n : Nat} (d : Dec h s2 r n) :
    ∃ tx ty mx, r = .K ⬝ tx ⬝ ty ∧ Dec h x tx mx ∧ mx < n := by
  obtain ⟨t2, ty, n2, my, e2', en2, d2, _⟩ := d.app_inv e2
  obtain ⟨n2', l2, d2'⟩ := Path.dec p2 d2
  obtain ⟨t1, tx, n1, mx, e1', en1, d1, dx⟩ := d2'.app_inv e1
  obtain ⟨n1', _, d1'⟩ := Path.dec p1 d1
  have eK : t1 = .K := d1'.K_inv ec
  refine ⟨tx, ty, mx, ?_, dx, by omega⟩
  rw [e2', e1', eK]

theorem i_redex {h : Heap} {c s1 f1 x : Nat}
    (ec : h[c]? = some .I) (e1 : h[s1]? = some (.app f1 x))
    (p1 : Path h f1 c) {r : Term} {n : Nat} (d : Dec h s1 r n) :
    ∃ tx mx, r = .I ⬝ tx ∧ Dec h x tx mx ∧ mx < n := by
  obtain ⟨t1, tx, n1, mx, e1', en1, d1, dx⟩ := d.app_inv e1
  obtain ⟨n1', _, d1'⟩ := Path.dec p1 d1
  have eI : t1 = .I := d1'.I_inv ec
  refine ⟨tx, mx, ?_, dx, by omega⟩
  rw [e1', eI]

/-- A contraction at the spine cell `a`: the root's decoding takes a head
    step, then a parallel step. -/
theorem contract {h h' : Heap} {root a : Nat} {rest : List Nat} {D : Term} {n : Nat}
    {fa xa : Nat} (ea : h[a]? = some (.app fa xa)) (hag : Agree h h' a)
    (dr : Dec h root D n) (hs : SpineOK h a rest root)
    (hA : ∀ r n, Dec h a r n →
      (∀ b t m, m < n → Dec h b t m → ∃ t' m', Dec h' b t' m' ∧ Par t t') →
      ∃ r' m', Dec h' a r' m' ∧ Par r r')
    (hred : ∀ r n, Dec h a r n → ∃ r1, Step r r1 ∧ ∃ r' m', Dec h' a r' m' ∧ Par r1 r') :
    ∃ D', Inv ⟨h', root, a, rest⟩ D' ∧ ∃ D1, Step D D1 ∧ Par D1 D' := by
  obtain ⟨R, nR, as, dR, eD, ha⟩ := dec_spine dr rest a hs
  have hn : ∀ s ∈ rest, s ≠ a := spine_ne dr hs
  obtain ⟨as', ha', pl⟩ := Args.update hag (fun d => dec_update' hag hA d) hn ha
  obtain ⟨r1, s1, r', m', dr', p1⟩ := hred R nR dR
  have hs' : SpineOK h' a rest root := SpineOK.agree hag ea hn hs
  obtain ⟨n', dD'⟩ := spine_dec rest a r' m' as' hs' dr' ha'
  refine ⟨appT r' as', ⟨⟨n', dD'⟩, hs'⟩, appT r1 as, ?_, par_appT p1 pl⟩
  rw [eD]
  exact step_appT s1 as

/-- **One transition preserves the invariant**: an unwind or an
    indirection keeps the decoding and shrinks the head's derivation; a
    contraction takes the root's decoding a head step and a parallel step. -/
theorem gstep_inv {m m' : GM} {b : Bool} {D : Term} (hs : GStep m m' b) (hi : Inv m D) :
    ∃ D', Inv m' D' ∧ m'.root = m.root ∧
      (b = false → D' = D ∧ m'.heap = m.heap ∧
        ∀ H nH, Dec m.heap m.hd H nH → ∃ H' nH', Dec m.heap m'.hd H' nH' ∧ nH' < nH) ∧
      (b = true → ∃ D1, Step D D1 ∧ Par D1 D') := by
  obtain ⟨⟨n, dr⟩, hsp⟩ := hi
  cases hs with
  | unwind e =>
    refine ⟨D, ⟨⟨n, dr⟩, ⟨_, _, e, .refl _, hsp⟩⟩, rfl, fun _ => ⟨rfl, rfl, ?_⟩, fun h => by cases h⟩
    intro H nH d
    obtain ⟨tf, tx, nf, nx, _, en, df, _⟩ := d.app_inv e
    exact ⟨tf, nf, df, by omega⟩
  | follow e =>
    refine ⟨D, ⟨⟨n, dr⟩, SpineOK.follow e hsp⟩, rfl, fun _ => ⟨rfl, rfl, ?_⟩, fun h => by cases h⟩
    intro H nH d
    obtain ⟨m, en, dp⟩ := d.ind_inv e
    exact ⟨H, m, dp, by omega⟩
  | @I h r c s1 f1 x rest ec e1 =>
    obtain ⟨f1', x', e1', p1, hrest⟩ := hsp
    rw [e1] at e1'
    cases e1'
    have hag := agree_set (h := h) (a := s1) (.ind x)
    have hl := lt_of_get e1
    have hA : ∀ r n, Dec h s1 r n →
        (∀ b t m, m < n → Dec h b t m → ∃ t' m', Dec (h.set s1 (.ind x)) b t' m' ∧ Par t t') →
        ∃ r' m', Dec (h.set s1 (.ind x)) s1 r' m' ∧ Par r r' := by
      intro r n d ih
      obtain ⟨tx, mx, er, dx, lt⟩ := i_redex ec e1 p1 d
      obtain ⟨tx', mx', dx', px⟩ := ih _ _ _ lt dx
      exact ⟨tx', _, .ind (List.getElem?_set_self hl) dx', er ▸ .I1 px⟩
    obtain ⟨D', hi', D1, st, pp⟩ := contract e1 hag dr hrest hA (by
      intro r n d
      obtain ⟨tx, mx, er, dx, _⟩ := i_redex ec e1 p1 d
      obtain ⟨tx', mx', dx', px⟩ := dec_update' hag hA dx
      exact ⟨tx, er ▸ .I tx, tx', _, .ind (List.getElem?_set_self hl) dx', px⟩)
    exact ⟨D', hi', rfl, (fun e => by cases e), fun _ => ⟨D1, st, pp⟩⟩
  | @K h r c s1 s2 f1 x f2 y rest ec e1 e2 =>
    obtain ⟨f1', x', e1', p1, f2', y', e2', p2, hrest⟩ := hsp
    rw [e1] at e1'
    cases e1'
    rw [e2] at e2'
    cases e2'
    have hag := agree_set (h := h) (a := s2) (.ind x)
    have hl := lt_of_get e2
    have hA : ∀ r n, Dec h s2 r n →
        (∀ b t m, m < n → Dec h b t m → ∃ t' m', Dec (h.set s2 (.ind x)) b t' m' ∧ Par t t') →
        ∃ r' m', Dec (h.set s2 (.ind x)) s2 r' m' ∧ Par r r' := by
      intro r n d ih
      obtain ⟨tx, ty, mx, er, dx, lt⟩ := k_redex ec e1 e2 p1 p2 d
      obtain ⟨tx', mx', dx', px⟩ := ih _ _ _ lt dx
      exact ⟨tx', _, .ind (List.getElem?_set_self hl) dx', er ▸ .K2 ty px⟩
    obtain ⟨D', hi', D1, st, pp⟩ := contract e2 hag dr hrest hA (by
      intro r n d
      obtain ⟨tx, ty, mx, er, dx, _⟩ := k_redex ec e1 e2 p1 p2 d
      obtain ⟨tx', mx', dx', px⟩ := dec_update' hag hA dx
      exact ⟨tx, er ▸ .K tx ty, tx', _, .ind (List.getElem?_set_self hl) dx', px⟩)
    exact ⟨D', hi', rfl, (fun e => by cases e), fun _ => ⟨D1, st, pp⟩⟩
  | @S h r c s1 s2 s3 f1 x f2 y f3 z rest ec e1 e2 e3 =>
    obtain ⟨f1', x', e1', p1, f2', y', e2', p2, f3', z', e3', p3, hrest⟩ := hsp
    rw [e1] at e1'
    cases e1'
    rw [e2] at e2'
    cases e2'
    rw [e3] at e3'
    cases e3'
    have hag := agree_S (h := h) (a := s3) (.app x z) (.app y z) (.app h.length (h.length + 1))
    have hl := lt_of_get e3
    -- the new heap's cells: the two fresh applications and the overwritten redex
    have gP : ((h ++ [GCell.app x z, GCell.app y z]).set s3 (.app h.length (h.length + 1)))[h.length]? =
        some (.app x z) := by
      rw [List.getElem?_set_ne (Nat.ne_of_lt hl), List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self]
      rfl
    have gQ : ((h ++ [GCell.app x z, GCell.app y z]).set s3 (.app h.length (h.length + 1)))[h.length + 1]? =
        some (.app y z) := by
      rw [List.getElem?_set_ne (Nat.ne_of_lt (Nat.lt_succ_of_lt hl)),
        List.getElem?_append_right (Nat.le_succ _), Nat.succ_sub (Nat.le_refl _), Nat.sub_self]
      rfl
    have g3 : ((h ++ [GCell.app x z, GCell.app y z]).set s3 (.app h.length (h.length + 1)))[s3]? =
        some (.app h.length (h.length + 1)) := by
      apply List.getElem?_set_self
      rw [List.length_append]
      exact Nat.lt_of_lt_of_le hl (Nat.le_add_right _ _)
    have hA : ∀ r n, Dec h s3 r n →
        (∀ b t m, m < n → Dec h b t m →
          ∃ t' m', Dec ((h ++ [GCell.app x z, GCell.app y z]).set s3 (.app h.length (h.length + 1))) b t' m' ∧
            Par t t') →
        ∃ r' m', Dec ((h ++ [GCell.app x z, GCell.app y z]).set s3 (.app h.length (h.length + 1))) s3 r' m' ∧
          Par r r' := by
      intro r n d ih
      obtain ⟨tx, ty, tz, mx, my, mz, er, dx, dy, dz, lx, ly, lz⟩ :=
        s_redex ec e1 e2 e3 p1 p2 p3 d
      obtain ⟨tx', _, dx', px⟩ := ih _ _ _ lx dx
      obtain ⟨ty', _, dy', py⟩ := ih _ _ _ ly dy
      obtain ⟨tz', _, dz', pz⟩ := ih _ _ _ lz dz
      exact ⟨_, _, .app g3 (.app gP dx' dz') (.app gQ dy' dz'), er ▸ .S3 px py pz⟩
    obtain ⟨D', hi', D1, st, pp⟩ := contract e3 hag dr hrest hA (by
      intro r n d
      obtain ⟨tx, ty, tz, mx, my, mz, er, dx, dy, dz, _, _, _⟩ :=
        s_redex ec e1 e2 e3 p1 p2 p3 d
      obtain ⟨tx', _, dx', px⟩ := dec_update' hag hA dx
      obtain ⟨ty', _, dy', py⟩ := dec_update' hag hA dy
      obtain ⟨tz', _, dz', pz⟩ := dec_update' hag hA dz
      exact ⟨_, er ▸ .S tx ty tz, _, _, .app g3 (.app gP dx' dz') (.app gQ dy' dz'),
        .app (.app px pz) (.app py pz)⟩)
    exact ⟨D', hi', rfl, (fun e => by cases e), fun _ => ⟨D1, st, pp⟩⟩

theorem Dec.pos {h : Heap} {a : Nat} {t : Term} {n : Nat} (d : Dec h a t n) : 0 < n := by
  cases d with
  | S _ => exact Nat.zero_lt_one
  | K _ => exact Nat.zero_lt_one
  | I _ => exact Nat.zero_lt_one
  | app _ _ _ => exact Nat.zero_lt_succ _
  | ind _ _ => exact Nat.zero_lt_succ _

/-- **The machine stops only at a weak head normal form.** -/
theorem gstep_none {m : GM} {D : Term} (hn : gstep m = none) (hi : Inv m D) : Whnf D := by
  obtain ⟨h, r, c, sp⟩ := m
  obtain ⟨⟨n, dr⟩, hsp⟩ := hi
  obtain ⟨H, nH, as, dH, eD, ha⟩ := dec_spine dr sp c hsp
  obtain ⟨cell, hc⟩ := dH.cell
  subst eD
  cases cell with
  | app f x => simp only [gstep, hc] at hn; cases hn
  | ind p => simp only [gstep, hc] at hn; cases hn
  | I =>
    rw [dH.I_inv hc]
    cases ha with
    | nil => exact .I
    | cons e1 _ _ => simp only [gstep, hc, e1] at hn; cases hn
  | K =>
    rw [dH.K_inv hc]
    cases ha with
    | nil => exact .K
    | cons e1 _ ha =>
      cases ha with
      | nil => exact .K1 _
      | cons e2 _ _ => simp only [gstep, hc, e1, e2] at hn; cases hn
  | S =>
    rw [dH.S_inv hc]
    cases ha with
    | nil => exact .S
    | cons e1 _ ha =>
      cases ha with
      | nil => exact .S1 _
      | cons e2 _ ha =>
        cases ha with
        | nil => exact .S2 _ _
        | cons e3 _ _ => simp only [gstep, hc, e1, e2, e3] at hn; cases hn

-- ---------------------------------------------------------------------------
-- Runs
-- ---------------------------------------------------------------------------

/-- Run with fuel `k`: the halted state and the number of contractions. -/
def grun : Nat → GM → Option (GM × Nat)
  | 0, _ => none
  | k + 1, m =>
    match gstep m with
    | none => some (m, 0)
    | some (m1, b) =>
      match grun k m1 with
      | none => none
      | some (m', c) => some (m', if b then c + 1 else c)

theorem grun_halt {m : GM} (k : Nat) (hs : gstep m = none) : grun (k + 1) m = some (m, 0) := by
  simp only [grun, hs]

theorem grun_step {m m1 m' : GM} {b : Bool} {k c : Nat} (hs : gstep m = some (m1, b))
    (hr : grun k m1 = some (m', c)) : grun (k + 1) m = some (m', if b then c + 1 else c) := by
  simp only [grun, hs, hr]

/-- **A halted run is sound**: the root decodes to a weak head normal form
    that the start's decoding weakly reduces to, and the run's contractions
    are at most the head reduction's from the start. -/
theorem grun_sound : ∀ (k : Nat) {m m' : GM} {D : Term} {c : Nat}, grun k m = some (m', c) → Inv m D →
    ∃ D', Inv m' D' ∧ m'.root = m.root ∧ WSteps D D' ∧ Whnf D' ∧
      ∀ n w, StepsN n D w → Whnf w → c ≤ n
  | 0, _, _, _, _, hr, _ => by cases hr
  | k + 1, m, m', D, c, hr, hi => by
    cases hs : gstep m with
    | none =>
      rw [grun_halt k hs] at hr
      cases hr
      exact ⟨D, hi, rfl, .refl _, gstep_none hs hi, fun _ _ _ _ => Nat.zero_le _⟩
    | some p =>
      obtain ⟨m1, b⟩ := p
      cases hr1 : grun k m1 with
      | none => simp only [grun, hs, hr1] at hr; cases hr
      | some q =>
        obtain ⟨m'', c'⟩ := q
        rw [grun_step hs hr1] at hr
        cases hr
        obtain ⟨D1, hi1, er, fb, tb⟩ := gstep_inv (gstep_sound hs) hi
        obtain ⟨D', hi', er', w1, wf, bd⟩ := grun_sound k hr1 hi1
        cases b with
        | false =>
          obtain ⟨e, _, _⟩ := fb rfl
          subst e
          exact ⟨D', hi', er'.trans er, w1, wf, bd⟩
        | true =>
          obtain ⟨E, st, pp⟩ := tb rfl
          refine ⟨D', hi', er'.trans er, (WSteps.single st.weak).trans (pp.wsteps.trans w1), wf, ?_⟩
          intro n w hw ww
          obtain ⟨m0, w0, lt, h0, ww0⟩ := StepsN.wtail_lt st pp.wsteps hw ww
          exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (bd m0 w0 h0 ww0) lt)

/-- **A run from a normalizing decoding halts.**  The measure: the head
    reduction's remaining contractions, which a contraction lowers
    (`StepsN.wtail_lt`), then the head's derivation, which an unwind or an
    indirection lowers. -/
theorem grun_halts : ∀ (B n : Nat), n ≤ B → ∀ (N : Nat) {m : GM} {D w H : Term} {nH : Nat},
    Inv m D → StepsN n D w → Whnf w → Dec m.heap m.hd H nH → nH ≤ N →
      ∃ k m' c, grun k m = some (m', c) := by
  intro B
  induction B with
  | zero =>
    intro n hn N
    induction N with
    | zero => intro m D w H nH _ _ _ dH hN; exact absurd (Nat.lt_of_lt_of_le dH.pos hN) (Nat.lt_irrefl 0)
    | succ N ihN =>
      intro m D w H nH hi hw ww dH hN
      cases hs : gstep m with
      | none => exact ⟨1, m, 0, grun_halt 0 hs⟩
      | some p =>
        obtain ⟨m1, b⟩ := p
        obtain ⟨D1, hi1, _, fb, tb⟩ := gstep_inv (gstep_sound hs) hi
        cases b with
        | false =>
          obtain ⟨e, eh, dec⟩ := fb rfl
          subst e
          obtain ⟨H', nH', dH', lt⟩ := dec H nH dH
          rw [← eh] at dH'
          obtain ⟨k, m', c, hr⟩ := ihN hi1 hw ww dH' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le lt hN))
          exact ⟨k + 1, m', _, grun_step hs hr⟩
        | true =>
          obtain ⟨E, st, pp⟩ := tb rfl
          obtain ⟨m0, w0, lt, _, _⟩ := StepsN.wtail_lt st pp.wsteps hw ww
          exact absurd (Nat.lt_of_lt_of_le lt hn) (Nat.not_lt_zero _)
  | succ B ihB =>
    intro n hn N
    induction N with
    | zero => intro m D w H nH _ _ _ dH hN; exact absurd (Nat.lt_of_lt_of_le dH.pos hN) (Nat.lt_irrefl 0)
    | succ N ihN =>
      intro m D w H nH hi hw ww dH hN
      cases hs : gstep m with
      | none => exact ⟨1, m, 0, grun_halt 0 hs⟩
      | some p =>
        obtain ⟨m1, b⟩ := p
        obtain ⟨D1, hi1, _, fb, tb⟩ := gstep_inv (gstep_sound hs) hi
        cases b with
        | false =>
          obtain ⟨e, eh, dec⟩ := fb rfl
          subst e
          obtain ⟨H', nH', dH', lt⟩ := dec H nH dH
          rw [← eh] at dH'
          obtain ⟨k, m', c, hr⟩ := ihN hi1 hw ww dH' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le lt hN))
          exact ⟨k + 1, m', _, grun_step hs hr⟩
        | true =>
          obtain ⟨E, st, pp⟩ := tb rfl
          obtain ⟨m0, w0, lt, h0, ww0⟩ := StepsN.wtail_lt st pp.wsteps hw ww
          obtain ⟨H1, nH1, dH1⟩ := hi1.head
          obtain ⟨k, m', c, hr⟩ := ihB m0 (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le lt hn)) nH1 hi1 h0 ww0 dH1
            (Nat.le_refl _)
          exact ⟨k + 1, m', _, grun_step hs hr⟩

/-- **Fuel is monotone.**  A run that halts within fuel `k` halts within
    every larger fuel, in the same state after the same contractions.  A
    budget-exact trace in this semantics is not stated here. -/
theorem grun_mono : ∀ {k : Nat} {m m' : GM} {c : Nat}, grun k m = some (m', c) → grun (k + 1) m = some (m', c)
  | 0, _, _, _, h => by cases h
  | k + 1, m, m', c, h => by
    cases hs : gstep m with
    | none => rw [grun_halt k hs] at h; rw [grun_halt (k + 1) hs, h]
    | some p =>
      obtain ⟨m1, b⟩ := p
      cases hr : grun k m1 with
      | none => simp only [grun, hs, hr] at h; cases h
      | some q =>
        obtain ⟨m'', c'⟩ := q
        rw [grun_step hs hr] at h
        rw [grun_step hs (grun_mono hr), h]

theorem grun_le {k k' : Nat} {m m' : GM} {c : Nat} (h : grun k m = some (m', c)) (hk : k ≤ k') :
    grun k' m = some (m', c) := by
  induction hk with
  | refl => exact h
  | step _ ih => exact grun_mono ih

-- ---------------------------------------------------------------------------
-- Loading a term
-- ---------------------------------------------------------------------------

/-- Append a term's cells, children first; the address of its root. -/
def loadT : Term → Heap → Heap × Nat
  | .S, h => (h ++ [.S], h.length)
  | .K, h => (h ++ [.K], h.length)
  | .I, h => (h ++ [.I], h.length)
  | .app f x, h =>
    let r1 := loadT f h
    let r2 := loadT x r1.1
    (r2.1 ++ [.app r1.2 r2.2], r2.1.length)

theorem Dec.mono {h : Heap} {a : Nat} {t : Term} {n : Nat} (d : Dec h a t n) (e : Heap) :
    Dec (h ++ e) a t n := by
  induction d with
  | S g => exact .S (by rw [List.getElem?_append_left (lt_of_get g)]; exact g)
  | K g => exact .K (by rw [List.getElem?_append_left (lt_of_get g)]; exact g)
  | I g => exact .I (by rw [List.getElem?_append_left (lt_of_get g)]; exact g)
  | app g _ _ ihf ihx => exact .app (by rw [List.getElem?_append_left (lt_of_get g)]; exact g) ihf ihx
  | ind g _ ih => exact .ind (by rw [List.getElem?_append_left (lt_of_get g)]; exact g) ih

theorem get_last (h : Heap) (c : GCell) : (h ++ [c])[h.length]? = some c := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem loadT_spec : ∀ (t : Term) (h : Heap), ∃ e n, (loadT t h).1 = h ++ e ∧ Dec (loadT t h).1 (loadT t h).2 t n
  | .S, h => ⟨[.S], 1, rfl, .S (get_last h _)⟩
  | .K, h => ⟨[.K], 1, rfl, .K (get_last h _)⟩
  | .I, h => ⟨[.I], 1, rfl, .I (get_last h _)⟩
  | .app f x, h => by
    obtain ⟨e1, n1, h1, d1⟩ := loadT_spec f h
    obtain ⟨e2, n2, h2, d2⟩ := loadT_spec x (loadT f h).1
    refine ⟨e1 ++ e2 ++ [.app (loadT f h).2 (loadT x (loadT f h).1).2], n1 + n2 + 1, ?_, ?_⟩
    · show (loadT x (loadT f h).1).1 ++ _ = _
      rw [h2, h1, List.append_assoc, List.append_assoc, List.append_assoc]
    · show Dec ((loadT x (loadT f h).1).1 ++ _) (loadT x (loadT f h).1).1.length (f ⬝ x) _
      refine .app (get_last _ _) ?_ (d2.mono _)
      rw [h2, List.append_assoc]
      exact d1.mono _

/-- A term loaded alone: the root and the head at its root cell. -/
def gload (t : Term) : GM := ⟨(loadT t []).1, (loadT t []).2, (loadT t []).2, []⟩

theorem inv_load (t : Term) : Inv (gload t) t := by
  obtain ⟨_, n, _, d⟩ := loadT_spec t []
  exact ⟨⟨n, d⟩, .refl _⟩

-- ---------------------------------------------------------------------------
-- Correctness against L1
-- ---------------------------------------------------------------------------

/-- **Soundness.**  A halted run from `t` after `c` contractions leaves the
    root decoding to a weak head normal form `v`; `t` evaluates under L1 to
    some `u` with `u ↠ v`, and `c` is at most L1's contraction count. -/
theorem graph_sound {t : Term} {k c : Nat} {m' : GM} (hr : grun k (gload t) = some (m', c)) :
    ∃ v n u, Dec m'.heap m'.root v n ∧ Whnf v ∧ Eval t u ∧ WSteps u v ∧
      ∀ s, StepsN s t u → c ≤ s := by
  obtain ⟨v, ⟨⟨n, dv⟩, _⟩, _, wv, hv, bd⟩ := grun_sound k hr (inv_load t)
  obtain ⟨u, eu, wu⟩ := eval_back wv ⟨.refl v, hv⟩
  exact ⟨v, n, u, dv, hv, eu, wu, fun s hs => bd s u hs eu.2⟩

/-- **Completeness.**  If `t` evaluates under L1 in `n` contractions, the
    machine halts after at most `n`, on a weak head normal form that L1's
    value reduces to. -/
theorem graph_complete {t u : Term} {n : Nat} (hs : StepsN n t u) (hw : Whnf u) :
    ∃ k m' c v n', grun k (gload t) = some (m', c) ∧ c ≤ n ∧ Dec m'.heap m'.root v n' ∧ Whnf v ∧
      WSteps u v := by
  obtain ⟨_, nH, _, dH⟩ := loadT_spec t []
  obtain ⟨k, m', c, hr⟩ := grun_halts n n (Nat.le_refl n) nH (inv_load t) hs hw dH (Nat.le_refl _)
  obtain ⟨v, n', u', dv, wv, eu, wu, bd⟩ := graph_sound hr
  have e : u' = u := steps_whnf_det eu.1 eu.2 hs.steps hw
  subst e
  exact ⟨k, m', c, v, n', hr, bd n hs, dv, wv, wu⟩

/-- A combinator does not reduce. -/
theorem wsteps_leaf {a v : Term} (ha : a = .S ∨ a = .K ∨ a = .I) (h : WSteps a v) : v = a := by
  cases h with
  | refl => rfl
  | step s _ => rcases ha with e | e | e <;> (subst e; cases s)

/-- **When L1's value is a combinator, the machine's is the same one.** -/
theorem graph_leaf {t u : Term} {k c : Nat} {m' : GM} (hr : grun k (gload t) = some (m', c))
    (hu : Eval t u) (ha : u = .S ∨ u = .K ∨ u = .I) : ∃ n, Dec m'.heap m'.root u n := by
  obtain ⟨v, n, u', dv, _, eu, wu, _⟩ := graph_sound hr
  have e : u' = u := steps_whnf_det eu.1 eu.2 hu.1 hu.2
  subst e
  rw [wsteps_leaf ha wu] at dv
  exact ⟨n, dv⟩

/-- A term's head and its number of arguments. -/
def spineOf : Term → Term × Nat
  | .app f _ => ((spineOf f).1, (spineOf f).2 + 1)
  | t => (t, 0)

/-- A weak step from a weak head normal form reduces an argument only. -/
theorem wstep_whnf {t u : Term} (hw : Whnf t) (h : WStep t u) : Whnf u ∧ spineOf u = spineOf t := by
  cases hw with
  | S => cases h
  | K => cases h
  | I => cases h
  | S1 x =>
    cases h with
    | left _ h => cases h
    | right _ _ => exact ⟨.S1 _, rfl⟩
  | K1 x =>
    cases h with
    | left _ h => cases h
    | right _ _ => exact ⟨.K1 _, rfl⟩
  | S2 x y =>
    cases h with
    | left _ h =>
      cases h with
      | left _ h => cases h
      | right _ _ => exact ⟨.S2 _ _, rfl⟩
    | right _ _ => exact ⟨.S2 _ _, rfl⟩

theorem wsteps_whnf {t u : Term} (h : WSteps t u) (hw : Whnf t) : spineOf u = spineOf t := by
  induction h with
  | refl => rfl
  | step s _ ih =>
    obtain ⟨w', e⟩ := wstep_whnf hw s
    exact (ih w').trans e

/-- **The machine's value has L1's head and arity.** -/
theorem graph_spine {t : Term} {k c : Nat} {m' : GM} (hr : grun k (gload t) = some (m', c)) :
    ∃ v n u, Dec m'.heap m'.root v n ∧ Eval t u ∧ spineOf v = spineOf u := by
  obtain ⟨v, n, u, dv, _, eu, wu, _⟩ := graph_sound hr
  exact ⟨v, n, u, dv, eu, wsteps_whnf wu eu.2⟩

end Graph
