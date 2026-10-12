import Ski.ZK.LogUpAir
import Ski.ZK.QuotBase

/-!
# The shape of LogUp's constraints

`tabsHonest_gen` asks of an AIR family's constraints, uniformly in the
challenges and terminal, that they be guarded, in the window, of
Plonky3 degree at most `D` and with at most `s` transition factors.
This file proves it for `withLup`.  The bounds pass through the
extension's arithmetic coordinate by coordinate (`QP_add`, `QP_mul`),
and the challenges and terminal are constants of degree 0.  So when
each lookup's elements have degree at most 1, its multiplicity at most
2, and both lie in the AIR's columns, LogUp's constraints have degree at
most 2 and at most one transition factor (`lup_shape`).  For the corpus
the kernel checks the elements and multiplicities (`corpus_lup_ok`).

Scope.  An `Inter` is one p3 `Lookup`: no flags, one tuple (same-bus
packing cannot merge two tuples at degree 2), the fields as elements
and the signed count as the multiplicity.  The bus enters only through
the lookup's prefix, its `α_c`, a constant.
-/

namespace Circuit

open B

/-- A selector-free expression in the window `W`, of Plonky3 degree at most `d`. -/
def Plain (W d : Nat) (e : E) : Prop := e.selFree = true ∧ e.win W = true ∧ e.pdeg ≤ d

/-- An extension expression whose coordinates are `Plain`. -/
def QP (W d : Nat) (q : Q) : Prop := Plain W d q.q0 ∧ Plain W d q.q1 ∧ Plain W d q.q2 ∧ Plain W d q.q3

theorem plain_add {W a b : Nat} {x y : E} (hx : Plain W a x) (hy : Plain W b y) : Plain W (max a b) (.add x y) := by
  refine ⟨?_, ?_, ?_⟩
  · show (x.selFree && y.selFree) = true; rw [hx.1, hy.1]; rfl
  · show (x.win W && y.win W) = true; rw [hx.2.1, hy.2.1]; rfl
  · show max x.pdeg y.pdeg ≤ _; have := hx.2.2; have := hy.2.2; omega

theorem plain_sub {W a b : Nat} {x y : E} (hx : Plain W a x) (hy : Plain W b y) : Plain W (max a b) (.sub x y) := by
  refine ⟨?_, ?_, ?_⟩
  · show (x.selFree && y.selFree) = true; rw [hx.1, hy.1]; rfl
  · show (x.win W && y.win W) = true; rw [hx.2.1, hy.2.1]; rfl
  · show max x.pdeg y.pdeg ≤ _; have := hx.2.2; have := hy.2.2; omega

theorem plain_mul {W a b : Nat} {x y : E} (hx : Plain W a x) (hy : Plain W b y) : Plain W (a + b) (.mul x y) := by
  refine ⟨?_, ?_, ?_⟩
  · show (x.selFree && y.selFree) = true; rw [hx.1, hy.1]; rfl
  · show (x.win W && y.win W) = true; rw [hx.2.1, hy.2.1]; rfl
  · show x.pdeg + y.pdeg ≤ _; have := hx.2.2; have := hy.2.2; omega

theorem plain_const (W : Nat) (c : F) : Plain W 0 (.const c) := ⟨rfl, rfl, Nat.le_refl 0⟩

theorem plain_mono {W a b : Nat} {x : E} (h : Plain W a x) (hab : a ≤ b) : Plain W b x :=
  ⟨h.1, h.2.1, Nat.le_trans h.2.2 hab⟩

theorem QP_mono {W a b : Nat} {q : Q} (h : QP W a q) (hab : a ≤ b) : QP W b q :=
  ⟨plain_mono h.1 hab, plain_mono h.2.1 hab, plain_mono h.2.2.1 hab, plain_mono h.2.2.2 hab⟩

theorem QP_add {W a b : Nat} {p q : Q} (hp : QP W a p) (hq : QP W b q) : QP W (max a b) (p.add q) :=
  ⟨plain_add hp.1 hq.1, plain_add hp.2.1 hq.2.1, plain_add hp.2.2.1 hq.2.2.1, plain_add hp.2.2.2 hq.2.2.2⟩

theorem QP_sub {W a b : Nat} {p q : Q} (hp : QP W a p) (hq : QP W b q) : QP W (max a b) (p.sub q) :=
  ⟨plain_sub hp.1 hq.1, plain_sub hp.2.1 hq.2.1, plain_sub hp.2.2.1 hq.2.2.1, plain_sub hp.2.2.2 hq.2.2.2⟩

theorem QP_mul {W a b : Nat} {p q : Q} (hp : QP W a p) (hq : QP W b q) : QP W (a + b) (p.mul q) := by
  obtain ⟨p0, p1, p2, p3⟩ := hp
  obtain ⟨q0, q1, q2, q3⟩ := hq
  have m := fun {x y : E} (hx : Plain W a x) (hy : Plain W b y) => plain_mul hx hy
  have w := plain_const W W11
  have e : ∀ {d : Nat} {x : E}, Plain W d x → Plain W (a + b) x → Plain W (a + b) x := fun _ h => h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine plain_mono (plain_add (m p0 q0) (plain_mul w (plain_add (plain_add (m p1 q3) (m p2 q2)) (m p3 q1)))) ?_
    omega
  · refine plain_mono (plain_add (plain_add (m p0 q1) (m p1 q0)) (plain_mul w (plain_add (m p2 q3) (m p3 q2)))) ?_
    omega
  · refine plain_mono (plain_add (plain_add (plain_add (m p0 q2) (m p1 q1)) (m p2 q0)) (plain_mul w (m p3 q3))) ?_
    omega
  · refine plain_mono (plain_add (plain_add (plain_add (m p0 q3) (m p1 q2)) (m p2 q1)) (m p3 q0)) ?_
    omega

theorem QP_QC (W : Nat) (c : EF) : QP W 0 (QC c) :=
  ⟨plain_const W _, plain_const W _, plain_const W _, plain_const W _⟩

theorem plain_atom {W o i : Nat} (ho : o ≤ 1) (hi : i < W) : Plain W 1 (.atom (.main o i)) :=
  ⟨rfl, by show (decide (o ≤ 1) && decide (i < W)) = true; simp [ho, hi], Nat.le_refl 1⟩

theorem QP_QV {W i o : Nat} (ho : o ≤ 1) (hi : i + 3 < W) : QP W 1 (QV i o) :=
  ⟨plain_atom ho (by omega), plain_atom ho (by omega), plain_atom ho (by omega), plain_atom ho hi⟩

theorem QP_QE {W d : Nat} {e : E} (h : Plain W d e) : QP W d (QE e) :=
  ⟨h, plain_mono (plain_const W 0) (Nat.zero_le _), plain_mono (plain_const W 0) (Nat.zero_le _),
    plain_mono (plain_const W 0) (Nat.zero_le _)⟩

theorem QP_comb {W d : Nat} (β : EF) : ∀ (es : List E) (q : Q), QP W d q → (∀ e ∈ es, Plain W d e) →
    QP W d (es.foldl (fun acc e => (QE e).add (acc.mul (QC β))) q)
  | [], _, hq, _ => hq
  | e :: es, q, hq, he => by
    rw [List.foldl_cons]
    refine QP_comb β es _ ?_ (fun e' h' => he e' (List.mem_cons_of_mem _ h'))
    refine QP_mono (QP_add (QP_QE (he e List.mem_cons_self)) (QP_mul hq (QP_QC W β))) ?_
    omega

theorem QP_sumQ {W : Nat} (o : Nat) (ho : o ≤ 1) : ∀ (is : List Nat), (∀ i ∈ is, i + 3 < W) → QP W 1 (sumQ o is)
  | [], _ => QP_mono (QP_QC W _) (Nat.zero_le _)
  | i :: is, h => QP_mono (QP_add (QP_QV ho (h i List.mem_cons_self))
      (QP_sumQ o ho is (fun j hj => h j (List.mem_cons_of_mem _ hj)))) (by omega)

-- ---------------------------------------------------------------------------
-- Selector-free expressions, guarded and without transition factors
-- ---------------------------------------------------------------------------

theorem guarded_of_selFree : ∀ (e : E), e.selFree = true → e.guarded = true
  | .atom (.main _ _), _ => rfl
  | .atom (.pre _ _), _ => rfl
  | .atom .first, h => nomatch h
  | .atom .last, h => nomatch h
  | .atom .trans, h => nomatch h
  | .const _, _ => rfl
  | .add _ _, h => h
  | .sub _ _, h => h
  | .neg _, h => h
  | .mul (.atom (.main _ _)) _, h => by
    simp only [E.selFree, Bool.and_eq_true] at h
    simp [E.guarded, Atom.isSel, h.2]
  | .mul (.atom (.pre _ _)) _, h => by
    simp only [E.selFree, Bool.and_eq_true] at h
    simp [E.guarded, Atom.isSel, h.2]
  | .mul (.atom .first) _, h => by simp [E.selFree, Atom.isSel] at h
  | .mul (.atom .last) _, h => by simp [E.selFree, Atom.isSel] at h
  | .mul (.atom .trans) _, h => by simp [E.selFree, Atom.isSel] at h
  | .mul (.const _) _, h => h
  | .mul (.add _ _) _, h => h
  | .mul (.sub _ _) _, h => h
  | .mul (.mul _ _) _, h => h
  | .mul (.neg _) _, h => h

theorem sdeg_of_selFree : ∀ (e : E), e.selFree = true → e.sdeg = 0
  | .atom (.main _ _), _ => rfl
  | .atom (.pre _ _), _ => rfl
  | .atom .first, h => nomatch h
  | .atom .last, h => nomatch h
  | .atom .trans, h => nomatch h
  | .const _, _ => rfl
  | .add a b, h | .sub a b, h | .mul a b, h => by
    simp only [E.selFree, Bool.and_eq_true] at h
    simp [E.sdeg, sdeg_of_selFree a h.1, sdeg_of_selFree b h.2]
  | .neg a, h => sdeg_of_selFree a h

/-- **What `tabsHonest_gen` asks of a constraint.** -/
def CShape (W D s : Nat) (e : E) : Prop := e.guarded = true ∧ e.win W = true ∧ e.pdeg ≤ D ∧ e.sdeg ≤ s

theorem shape_plain {W d D s : Nat} {e : E} (h : Plain W d e) (hd : d ≤ D) : CShape W D s e :=
  ⟨guarded_of_selFree e h.1, h.2.1, Nat.le_trans h.2.2 hd, by rw [sdeg_of_selFree e h.1]; exact Nat.zero_le _⟩

theorem shape_sel {W d : Nat} {e : E} (h : Plain W d e) :
    CShape W (1 + d) 0 (.mul (.atom .first) e) ∧ CShape W (1 + d) 0 (.mul (.atom .last) e) ∧
      CShape W (0 + d) 1 (.mul (.atom .trans) e) := by
  have hs := sdeg_of_selFree e h.1
  have hsf := h.1
  have hg : ∀ s : Atom, s.isSel = true → (E.mul (.atom s) e).guarded = true := fun s hs' => by
    cases s <;> simp_all [E.guarded, Atom.isSel]
  have hwe := h.2.1
  have hw : ∀ s : Atom, s.isSel = true → (E.mul (.atom s) e).win W = true := fun s hs' => by
    cases s
    all_goals first | (show (true && e.win W) = true; rw [hwe]; rfl) | (simp [Atom.isSel] at hs')
  have hp := h.2.2
  refine ⟨⟨hg _ rfl, hw _ rfl, ?_, ?_⟩, ⟨hg _ rfl, hw _ rfl, ?_, ?_⟩, ⟨hg _ rfl, hw _ rfl, ?_, ?_⟩⟩
  · show 1 + e.pdeg ≤ 1 + d; omega
  · show 0 + e.sdeg ≤ 0; omega
  · show 1 + e.pdeg ≤ 1 + d; omega
  · show 0 + e.sdeg ≤ 0; omega
  · show 0 + e.pdeg ≤ 0 + d; omega
  · show 1 + e.sdeg ≤ 1; omega

theorem shape_mono {W D D' s s' : Nat} {e : E} (h : CShape W D s e) (hD : D ≤ D') (hs : s ≤ s') : CShape W D' s' e :=
  ⟨h.1, h.2.1, Nat.le_trans h.2.2.1 hD, Nat.le_trans h.2.2.2 hs⟩

/-- **LogUp's constraints have degree at most 2 and at most one transition
    factor**, at any challenges and terminal, when each lookup's elements
    are selector-free of degree at most 1 and its multiplicity of degree
    at most 2, all in the AIR's `w` columns, and the window `W` holds the
    permutation columns. -/
theorem lup_shape {W w : Nat} (αs : Nat → EF) (β T : EF) (Ls : List (List E × E))
    (hL : ∀ L ∈ Ls, (∀ e ∈ L.1, Plain W 1 e) ∧ Plain W 2 L.2) (hW : w + 4 * (Ls.length + 1) ≤ W) :
    ∀ e ∈ eq4 (lupCons αs β T w Ls), CShape W 2 1 e := by
  intro e he
  obtain ⟨q, hq, hcoord⟩ := mem_eq4 he
  have hfis : ∀ i ∈ (List.range Ls.length).map (fun c => w + 4 * (c + 1)), i + 3 < W := fun i hi => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
    have := List.mem_range.1 hc; omega
  have hsum := QP_sumQ (W := W) 0 (Nat.zero_le 1) _ hfis
  have hacc0 : QP W 1 (QV w 0) := QP_QV (i := w) (o := 0) (Nat.zero_le 1) (by omega)
  have hacc1 : QP W 1 (QV w 1) := QP_QV (i := w) (o := 1) (Nat.le_refl 1) (by omega)
  -- each coordinate of a `QP` expression has the shape, and so does each of a selector times one
  have cplain : ∀ {d : Nat} {q : Q}, QP W d q → d ≤ 2 → (e = q.q0 ∨ e = q.q1 ∨ e = q.q2 ∨ e = q.q3) → CShape W 2 1 e :=
    fun hq hd hc => by
      rcases hc with rfl | rfl | rfl | rfl
      · exact shape_plain hq.1 hd
      · exact shape_plain hq.2.1 hd
      · exact shape_plain hq.2.2.1 hd
      · exact shape_plain hq.2.2.2 hd
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    rw [List.length_zipWith, List.length_range, Nat.min_self] at hi
    rw [List.getElem_zipWith, List.getElem_range] at hcoord
    obtain ⟨hes, hm⟩ := hL _ (List.getElem_mem hi)
    have hc : QP W 1 (comb β Ls[i].1) := QP_comb β _ _ (QP_mono (QP_QC W _) (Nat.zero_le 1)) hes
    have hf : QP W 1 (QV (w + 4 * (i + 1)) 0) := QP_QV (i := w + 4 * (i + 1)) (o := 0) (Nat.zero_le 1) (by omega)
    refine cplain (QP_sub (QP_mul (QP_sub (QP_QC W (αs i)) hc) hf) (QP_QE hm)) (by omega) hcoord
  · have selc : ∀ {s : Atom} {q : Q}, (s = .first ∨ s = .last ∨ s = .trans) → QP W 1 q →
        (e = (Q.sel s q).q0 ∨ e = (Q.sel s q).q1 ∨ e = (Q.sel s q).q2 ∨ e = (Q.sel s q).q3) → CShape W 2 1 e :=
      fun {s} {q} hs hq hc => by
        have one : ∀ x, Plain W 1 x → (e = .mul (.atom s) x) → CShape W 2 1 e := fun x hx hex => by
          subst hex
          obtain ⟨h1, h2, h3⟩ := shape_sel hx
          rcases hs with rfl | rfl | rfl
          · exact shape_mono h1 (by omega) (by omega)
          · exact shape_mono h2 (by omega) (by omega)
          · exact shape_mono h3 (by omega) (Nat.le_refl 1)
        rcases hc with h | h | h | h
        · exact one _ hq.1 h
        · exact one _ hq.2.1 h
        · exact one _ hq.2.2.1 h
        · exact one _ hq.2.2.2 h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact selc (.inl rfl) hacc0 hcoord
    rcases List.mem_cons.1 hq with rfl | hq
    · exact selc (.inr (.inr rfl)) (QP_mono (QP_sub (QP_sub hacc1 hacc0) hsum) (by omega)) hcoord
    rcases List.mem_cons.1 hq with rfl | hq
    · exact selc (.inr (.inl rfl)) (QP_mono (QP_sub (QP_sub (QP_mono (QP_QC W T) (Nat.zero_le 1)) hacc0) hsum)
        (by omega)) hcoord
    · nomatch hq

-- ---------------------------------------------------------------------------
-- The corpus
-- ---------------------------------------------------------------------------

/-- The interactions as single-tuple lookups. -/
def corpusLs (A : AirD) : List (List E × E) := A.inters.map fun I => (I.fields, I.count)

/-- The elements' and multiplicity's check, as one `Bool`. -/
def lupOkB (w : Nat) (L : List E × E) : Bool :=
  L.1.all (fun e => e.selFree && e.win w && decide (e.pdeg ≤ 1)) && L.2.selFree && L.2.win w && decide (L.2.pdeg ≤ 2)

set_option maxRecDepth 100000 in
/-- **The corpus interactions' elements and multiplicities**, for every
    term: selector-free, in the AIR's columns, of degree at most 1 and 2. -/
theorem corpus_lup_ok (t : Term) : ∀ A ∈ baseAirs t, (corpusLs A).all (lupOkB A.width) = true := by
  intro A hA
  simp only [baseAirs, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl <;> rfl

theorem win_mono {w W : Nat} (hW : w ≤ W) : ∀ e : E, e.win w = true → e.win W = true
  | .atom (.main o i), h => by
    simp only [E.win, Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact ⟨h.1, by omega⟩
  | .atom (.pre _ _), _ => rfl
  | .atom .first, _ => rfl
  | .atom .last, _ => rfl
  | .atom .trans, _ => rfl
  | .const _, _ => rfl
  | .add a b, h | .sub a b, h | .mul a b, h => by
    simp only [E.win, Bool.and_eq_true] at h ⊢; exact ⟨win_mono hW a h.1, win_mono hW b h.2⟩
  | .neg a, h => win_mono hW a h

/-- **The corpus LogUp constraints' shape**, for every term, challenge pair
    and terminal. -/
theorem base_lup_shape (t : Term) {A : AirD} (hA : A ∈ baseAirs t) (αs : Nat → EF) (β T : EF) :
    ∀ e ∈ eq4 (lupCons αs β T A.width (corpusLs A)),
      CShape (A.width + 4 * ((corpusLs A).length + 1)) 2 1 e := by
  refine lup_shape αs β T _ (fun L hL => ?_) (Nat.le_refl _)
  have h := List.all_eq_true.1 (corpus_lup_ok t A hA) L hL
  simp only [lupOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hes, hs⟩, hw⟩, hd⟩ := h
  refine ⟨fun e he => ?_, hs, win_mono (by omega) _ hw, hd⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hes e he
  exact ⟨h1, win_mono (by omega) _ h2, h3⟩

/-- **A corpus AIR with its LogUp constraints meets `tabsHonest_gen`'s
    uniform hypotheses**: at every challenge pair and terminal, every
    constraint is guarded, in the window of the AIR's and the
    permutation trace's columns, of Plonky3 degree at most 2 and with at
    most one transition factor. -/
theorem corpus_withLup_shape (t : Term) {A : AirD} (hA : A ∈ baseAirs t) (αs : Nat → EF) (β T : EF) :
    ∀ c ∈ (withLup A αs β T A.width (corpusLs A)).cons,
      CShape (A.width + 4 * ((corpusLs A).length + 1)) 2 1 c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨hgd, hwin, hD, hsd⟩ := base_facts t hA
    exact ⟨hgd c hc, win_mono (by omega) c (hwin c hc), hD c hc, hsd c hc⟩
  · exact base_lup_shape t hA αs β T c hc

end Circuit
