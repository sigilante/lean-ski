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

With each lookup's `α` its bus prefix, the honest accumulator's total is
the transcript's `terminal pre β A Tb` (`accV_terminal`), so LogUp's
completeness holds at the transcript's terminal of any table meeting
`Sat`, when no message of nonzero count has a vanishing denominator
(`lup_sat_terminal`).

The committed groups: the main group's columns and the permutation
group's flattened columns, concatenated, are the table with its
permutation columns (`cols_withPerm`, in `LogUpAir`).  So a builder
whose main group holds a `Sat` table, whose permutation group holds the
honest columns and whose transcript publishes the terminal meets
`tabsHonest_gen`'s per-trace hypothesis (`hsatT_lup`), and a corpus AIR's
table with its LogUp constraints is honest (`tabsHonest_corpus`).

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

-- ---------------------------------------------------------------------------
-- The terminal is the transcript's
-- ---------------------------------------------------------------------------

theorem combV_horner (β : EF) (vs : List F) : combV β vs = hornerL β vs := by
  unfold combV hornerL
  have : (fun (acc : EF) (v : F) => (EF.ofF v).add (acc.mul β)) = fun acc v => (acc.mul β).add (EF.ofF v) := by
    funext acc v; exact EF.add_comm _ _
  rw [this]

theorem fsum_sumL (Tb : Table) (αs : Nat → EF) (β : EF) (Ls : List (List E × E)) (r : Nat) :
    ∀ cs : List Nat, fsum Tb αs β Ls r cs = sumL (fun c => fV Tb αs β Ls c r) cs
  | [] => rfl
  | c :: cs => by rw [sumL_cons, ← fsum_sumL Tb αs β Ls r cs]; rfl

theorem sumL_range {α : Type} (g : α → EF) : ∀ (l : List α) (f : Nat → EF) (d : α),
    (∀ c, c < l.length → f c = g (l.getD c d)) → sumL f (List.range l.length) = sumL g l
  | [], _, _, _ => rfl
  | a :: l, f, d, h => by
    rw [List.length_cons, List.range_succ_eq_map, sumL_cons, sumL_map, sumL_cons]
    rw [h 0 (Nat.succ_pos _), sumL_range g l (fun c => f (c + 1)) d (fun c hc => h (c + 1) (Nat.succ_lt_succ hc))]
    rfl

theorem accV_sumL (Tb : Table) (αs : Nat → EF) (β : EF) (Ls : List (List E × E)) : ∀ n,
    accV Tb αs β Ls n = sumL (fun r => fsum Tb αs β Ls r (List.range Ls.length)) (List.range n)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, sumL_append, sumL_cons, sumL_nil, EF.add_zero, ← accV_sumL Tb αs β Ls n]; rfl

/-- A placeholder interaction. -/
def interD : Inter := ⟨"", 0, .const 0, []⟩

/-- Each lookup's `α`: its interaction's bus prefix. -/
def busAlphas (pre : String → EF) (A : AirD) (c : Nat) : EF := pre (A.inters.getD c interD).bus

/-- **The honest total is the transcript's terminal**: with each lookup's
    `α` its bus's prefix, the honest accumulator's total over the table is
    `terminal pre β A Tb`, the value the transcript publishes for it. -/
theorem accV_terminal (pre : String → EF) (β : EF) (A : AirD) (Tb : Table) :
    accV Tb (busAlphas pre A) β (corpusLs A) Tb.h = terminal pre β A Tb := by
  rw [accV_sumL]
  unfold terminal
  congr 1
  funext r
  rw [fsum_sumL]
  unfold rowTerm
  have hlen : (corpusLs A).length = A.inters.length := by unfold corpusLs; rw [List.length_map]
  rw [hlen]
  refine sumL_range _ A.inters _ interD (fun c hc => ?_)
  have e1 : (corpusLs A).getD c ([], .const 0) = ((A.inters.getD c interD).fields, (A.inters.getD c interD).count) := by
    unfold corpusLs
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hc]
    rfl
  unfold fV msgTerm den busAlphas
  rw [e1, combV_horner]

/-- **LogUp's completeness at the transcript's terminal**: a table that
    meets `Sat` for an AIR whose constraints and interactions lie in its
    columns, with the honest permutation columns appended, meets `Sat` for
    the AIR with LogUp's constraints at the terminal the transcript
    publishes, when no message of nonzero count has a vanishing
    denominator. -/
theorem lup_sat_terminal {A : AirD} {Tb : Table} (h : Sat A Tb) (pre : String → EF) (β : EF)
    (hA : ∀ c ∈ A.cons, c.win A.width = true)
    (hI : ∀ I ∈ A.inters, (∀ e ∈ I.fields, e.win A.width = true) ∧ I.count.win A.width = true)
    (hden : ∀ I ∈ A.inters, ∀ r, r < Tb.h → I.count.eval (Tb.env r) ≠ 0 →
      den pre β I.bus (I.fields.map (·.eval (Tb.env r))) ≠ EF.zero) :
    Sat (withLup A (busAlphas pre A) β (terminal pre β A Tb) A.width (corpusLs A))
      (withPerm Tb (busAlphas pre A) β (corpusLs A) A.width) := by
  rw [← accV_terminal]
  refine lup_sat h _ β _ _ hA (fun L hL => ?_) (fun c hc r hr => ?_)
  · obtain ⟨I, hI', rfl⟩ := List.mem_map.1 hL
    exact hI I hI'
  · intro hm0
    have hlen : (corpusLs A).length = A.inters.length := by unfold corpusLs; rw [List.length_map]
    rw [hlen] at hc
    have e1 : (corpusLs A).getD c ([], .const 0) = ((A.inters.getD c interD).fields, (A.inters.getD c interD).count) := by
      unfold corpusLs
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
      rfl
    have hmem : A.inters.getD c interD ∈ A.inters := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]; exact List.getElem_mem hc
    rw [e1] at hm0 ⊢
    rw [combV_horner]
    exact hden _ hmem r hr hm0

theorem plain_wmono {w W d : Nat} {e : E} (h : Plain w d e) (hW : w ≤ W) : Plain W d e :=
  ⟨h.1, win_mono hW e h.2.1, h.2.2⟩

/-- **`hsatT` for an AIR with its LogUp constraints**, from the builder:
    at each trace and challenge pair, group `gm` holds a table `Tb` that
    meets `Sat` and group `gp` the honest permutation columns, the
    transcript's value at index `k` is the table's terminal, and no
    message of nonzero count has a vanishing denominator.  Then the two groups, concatenated,
    are a table meeting `Sat` for the AIR with LogUp's constraints at the
    transcript's values, as `tabsHonest_gen` asks. -/
theorem hsatT_lup {A : AirD} {m gm gp k : Nat} (pre : EF → EF → String → EF)
    (cols : (Nat → Tup) → EF → EF → List (List (List F))) (vt : (Nat → Tup) → EF → EF → List EF)
    (preP : Nat → List F) (g : F) (good : (Nat → Tup) → EF → EF → Prop)
    (hA : ∀ c ∈ A.cons, c.win A.width = true)
    (hI : ∀ I ∈ A.inters, (∀ e ∈ I.fields, Plain A.width 1 e) ∧ Plain A.width 2 I.count)
    (hb : ∀ t α β, good t α β → ∃ Tb : Table, Sat A Tb ∧ Tb.h = m + 1 ∧
      (cols t α β).getD gm [] = mainCols Tb A.width ∧
      (cols t α β).getD gp [] = permCols Tb (busAlphas (pre α β) A) β (corpusLs A) ∧
      (vt t α β).getD k EF.zero = terminal (pre α β) β A Tb ∧
      (∀ I ∈ A.inters, ∀ r, r < Tb.h → I.count.eval (Tb.env r) ≠ 0 →
        den (pre α β) β I.bus (I.fields.map (·.eval (Tb.env r))) ≠ EF.zero) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = Tb.pre r i)) :
    ∀ t α β, good t α β → ∃ Tb : Table,
      Sat ((fun α β v => withLup A (busAlphas (pre α β) A) β (v.getD k EF.zero) A.width (corpusLs A)) α β (vt t α β)) Tb ∧
      Tb.h = m + 1 ∧
      (∀ c ∈ ((fun α β v => withLup A (busAlphas (pre α β) A) β (v.getD k EF.zero) A.width (corpusLs A))
        α β (vt t α β)).cons, c.win (catAt (cols t α β) [gm, gp]).length = true) ∧
      (∀ col ∈ catAt (cols t α β) [gm, gp], col.length = m + 1) ∧
      (∀ i (hi : i < (catAt (cols t α β) [gm, gp]).length) r (hr : r < ((catAt (cols t α β) [gm, gp])[i]).length),
        ((catAt (cols t α β) [gm, gp])[i])[r] = Tb.main r i) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = Tb.pre r i) := by
  intro t α β hgood
  obtain ⟨Tb, hsat, hh, hm, hp, hv, hden, hpre⟩ := hb t α β hgood
  have hcat : catAt (cols t α β) [gm, gp] = mainCols Tb A.width ++ permCols Tb (busAlphas (pre α β) A) β (corpusLs A) := by
    show (cols t α β).getD gm [] ++ ((cols t α β).getD gp [] ++ []) = _
    rw [hm, hp, List.append_nil]
  obtain ⟨hlen, hcl, hval⟩ := cols_withPerm Tb (busAlphas (pre α β) A) β (corpusLs A) A.width
  refine ⟨withPerm Tb (busAlphas (pre α β) A) β (corpusLs A) A.width, ?_, hh, fun c hc => ?_, ?_, ?_, hpre⟩
  · show Sat (withLup A (busAlphas (pre α β) A) β ((vt t α β).getD k EF.zero) A.width (corpusLs A)) _
    rw [hv]
    exact lup_sat_terminal hsat (pre α β) β hA
      (fun I hI' => ⟨fun e he => ((hI I hI').1 e he).2.1, (hI I hI').2.2.1⟩) hden
  · rw [hcat, hlen]
    rcases List.mem_append.1 hc with hc | hc
    · exact win_mono (by omega) c (hA c hc)
    · obtain ⟨q, hq, e⟩ := mem_eq4 hc
      have := lup_shape (W := A.width + 4 * ((corpusLs A).length + 1)) (w := A.width) (busAlphas (pre α β) A) β
        ((vt t α β).getD k EF.zero) (corpusLs A) (fun L hL => ?_) (Nat.le_refl _) c hc
      · exact this.2.1
      · obtain ⟨I, hI', rfl⟩ := List.mem_map.1 hL
        have hw : A.width ≤ A.width + 4 * ((corpusLs A).length + 1) := by omega
        exact ⟨fun e he => plain_wmono ((hI I hI').1 e he) hw, plain_wmono (hI I hI').2 hw⟩
  · rw [hcat]; intro col hcol; rw [hcl col hcol, hh]
  · intro i hi r hr
    have hi' : i < (mainCols Tb A.width ++ permCols Tb (busAlphas (pre α β) A) β (corpusLs A)).length := by
      rw [← hcat]; exact hi
    have := hval i hi' r (by simp only [hcat] at hr; exact hr)
    simp only [hcat]
    exact this

theorem corpus_plain (t : Term) {A : AirD} (hA : A ∈ baseAirs t) :
    ∀ I ∈ A.inters, (∀ e ∈ I.fields, Plain A.width 1 e) ∧ Plain A.width 2 I.count := fun I hI => by
  have h := List.all_eq_true.1 (corpus_lup_ok t A hA) (I.fields, I.count) (List.mem_map.2 ⟨I, hI, rfl⟩)
  simp only [lupOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hes, hs⟩, hw⟩, hd⟩ := h
  exact ⟨fun e he => ⟨(hes e he).1.1, (hes e he).1.2, (hes e he).2⟩, hs, hw, hd⟩

/-- **No message of nonzero count has a vanishing denominator** at the
    builder's table: where Plonky3's prover does not abort. -/
def goodLup (A : AirD) (pre : EF → EF → String → EF) (tab : (Nat → Tup) → EF → EF → Table)
    (t : Nat → Tup) (α β : EF) : Prop :=
  ∀ I ∈ A.inters, ∀ r, r < (tab t α β).h → I.count.eval ((tab t α β).env r) ≠ 0 →
    den (pre α β) β I.bus (I.fields.map (·.eval ((tab t α β).env r))) ≠ EF.zero

/-- **A corpus AIR's quotient table with its LogUp constraints is honest**
    (for an AIR with at least one lookup, as p3 commits no permutation
    trace for one without):
    `tabsHonest_gen` over its main group `gm` and permutation group `gp`,
    the constraints the AIR's and LogUp's at each lookup's bus prefix and
    the transcript's terminal, at the challenges where `good` holds (no
    message of nonzero count has a vanishing denominator; elsewhere the
    prover aborts, and `pcsCloseN_fri_gen` sends the canonical chunks),
    from the builder's facts (`hb`) and the static facts of the groups,
    the domains and the weights. -/
theorem tabsHonest_corpus (term : Term) {A : AirD} (hA : A ∈ baseAirs term) {g : F} {m gm gp k : Nat}
    {preP : Nat → List F} {κ : F} {cs : List Chunk} {Hl : List F} {cl : F} {S : List F} {ζ : EF}
    {ws : List (EF → EF → List F)} {qs : List QGroup} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (pre : EF → EF → String → EF) (vt : (Nat → Tup) → EF → EF → List EF) (tab : (Nat → Tup) → EF → EF → Table)
    (good : (Nat → Tup) → EF → EF → Prop) (hgl : ∀ t α β, good t α β → goodLup A pre tab t α β)
    (hgrp : ∀ j ∈ [gm, gp], ∃ hj : j < qs.length, (qs[j]'hj).base.T = cosetL 1 g (m + 1) ∧ (qs[j]'hj).base.S = S ∧
      (qs[j]'hj).base.Z = [ζ, (EF.ofF g).mul ζ] ∧ (qs[j]'hj).nxt = (g * ·) ∧
      (cosetL 1 g (m + 1) ++ (qs[j]'hj).base.R).Nodup ∧ (qs[j]'hj).base.R.length ≤ m + 1)
    (hcl' : ∀ t α β, ∀ j ∈ [gm, gp], j < (cols t α β).length)
    (hb : ∀ t α β, Sat A (tab t α β) ∧ (tab t α β).h = m + 1 ∧
      (cols t α β).getD gm [] = mainCols (tab t α β) A.width ∧
      (cols t α β).getD gp [] = permCols (tab t α β) (busAlphas (pre α β) A) β (corpusLs A) ∧
      (vt t α β).getD k EF.zero = terminal (pre α β) β A (tab t α β) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = (tab t α β).pre r i))
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {kk lq : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ kk) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (kk + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hDlq : 2 ≤ 2 ^ lq) (hs : 1 < m + 1)
    (hPsz : 2 * (2 * (m + 1) - 1) + 1 + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (hok : ∀ c ∈ (airQTabG (fun α β v => withLup A (busAlphas (pre α β) A) β (v.getD k EF.zero) A.width (corpusLs A))
      g m preP [gm, gp] κ cs Hl cl S ζ ws).sets, c.OK)
    (hHn : ∀ ch ∈ cs, ch.H.Nodup) (hHln : Hl.Nodup) :
    ∀ t α β ms, good t α β → TabsHonest
      (fun c => c.JS α β (vt t α β) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (vt t α β) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      [airQTabG (fun α β v => withLup A (busAlphas (pre α β) A) β (v.getD k EF.zero) A.width (corpusLs A))
        g m preP [gm, gp] κ cs Hl cl S ζ ws]
      [airData (withLup A (busAlphas (pre α β) A) β ((vt t α β).getD k EF.zero) A.width (corpusLs A)) g m preP cs Hl
        ws α β (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) [gm, gp])] := by
  obtain ⟨hgd, hwin, _, _⟩ := base_facts term hA
  have shape := fun α β (v : List EF) => corpus_withLup_shape term hA (busAlphas (pre α β) A) β (v.getD k EF.zero)
  exact tabsHonest_gen (AF := fun α β v => withLup A (busAlphas (pre α β) A) β (v.getD k EF.zero) A.width (corpusLs A))
    vt good hgrp hcl' (hsatT_lup pre cols vt preP g good hwin (corpus_plain term hA)
      (fun t α β hgood => by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb t α β
        exact ⟨tab t α β, h1, h2, h3, h4, h5, hgl t α β hgood, h6⟩)) hg hinj
    (fun α β v c hc => (shape α β v c hc).1) hpreL hζ hS hc hcl hκ hshift hhalf hN hdom hL
    (fun α β v c hc => (shape α β v c hc).2.2.1) hDlq (fun α β v c hc => (shape α β v c hc).2.2.2) hs hPsz hw hok
    hHn hHln

-- ---------------------------------------------------------------------------
-- The abort: no abort, no vanishing denominator
-- ---------------------------------------------------------------------------

/-- **Where the proof does not abort, `goodLup` holds**: `Aborts` flags
    any message, of any count, with a vanishing denominator, so on the
    challenges where the transcript is shown (`realVN` is `none` on an
    abort, and the transcript theorems charge those challenges by
    `abort_count`) no message of nonzero count has one. -/
theorem goodLup_of_noAbort {A : AirD} {off : EF → String → EF} {tab : (Nat → Tup) → EF → EF → Table}
    {ts : (Nat → Tup) → EF → EF → List (AirD × Table)} {t : Nat → Tup} {α β : EF}
    (hmem : (A, tab t α β) ∈ ts t α β) (h : Aborts (prefixOf α (off β)) β (ts t α β) = false) :
    goodLup A (fun α β => prefixOf α (off β)) tab t α β := by
  intro I hI r hr _ e
  have hent : ((I.bus, I.fields.map (·.eval ((tab t α β).env r))), I.count.eval ((tab t α β).env r)) ∈
      allEntries (ts t α β) := by
    unfold allEntries
    refine List.mem_flatMap.2 ⟨(A, tab t α β), hmem, ?_⟩
    unfold entries
    exact List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, List.mem_map.2 ⟨I, hI, rfl⟩⟩
  unfold Aborts at h
  have := List.any_eq_false.1 h _ hent
  exact this (decide_eq_true e)

/-- **The composed hiding PCS for a corpus AIR with its LogUp constraints**:
    `pcsCloseN_fri` at the table over the AIR's main group `gm` and its
    permutation group `gp`, the constraints the AIR's and LogUp's at each
    lookup's bus prefix `prefixOf α (off β)` and the transcript's
    terminal.  Where the proof does not abort (`Aborts`, the transcript
    theorems' event) the data are the honest chunks, and elsewhere, where
    the transcript shows nothing, the canonical chunks.  The builder's
    main table `tab t` is committed before the challenges and is among
    the transcript's tables `tabs t`. -/
theorem pcsCloseN_fri_corpus {V : Type} {ks : List Nat} {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    (term : Term) {A : AirD} (hA : A ∈ baseAirs term) {g : F} {m gm gp k : Nat}
    {preP : Nat → List F} {κ : F} {cs : List Chunk} {Hl : List F} {cl : F} {S : List F} {ζ : EF}
    {ws : List (EF → EF → List F)} {qs : List QGroup} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    (tab : (Nat → Tup) → Table) (tabs : (Nat → Tup) → List (AirD × Table)) (hmem : ∀ t, (A, tab t) ∈ tabs t)
    (hokq : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (hdet : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (hgrp : ∀ j ∈ [gm, gp], ∃ hj : j < qs.length, (qs[j]'hj).base.T = cosetL 1 g (m + 1) ∧ (qs[j]'hj).base.S = S ∧
      (qs[j]'hj).base.Z = [ζ, (EF.ofF g).mul ζ] ∧ (qs[j]'hj).nxt = (g * ·) ∧
      (cosetL 1 g (m + 1) ++ (qs[j]'hj).base.R).Nodup ∧ (qs[j]'hj).base.R.length ≤ m + 1)
    (hcl' : ∀ t α β, ∀ j ∈ [gm, gp], j < (cols t α β).length)
    (hb : ∀ t α β, Sat A (tab t) ∧ (tab t).h = m + 1 ∧
      (cols t α β).getD gm [] = mainCols (tab t) A.width ∧
      (cols t α β).getD gp [] = permCols (tab t) (busAlphas (prefixOf α (off β)) A) β (corpusLs A) ∧
      (tv (prefixOf α (off β)) β t).getD k EF.zero = terminal (prefixOf α (off β)) β A (tab t) ∧
      (∀ r i, r < m + 1 → fval (fpow g r) (preP i) = (tab t).pre r i))
    (hg : fpow g (m + 1) = 1) (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b)
    (hpreL : ∀ i, (preP i).length ≤ 2 * (m + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hS : ∀ x ∈ S, fval x (fvan (cosetL 1 g (m + 1))) ≠ 0)
    (hc : ∀ ch ∈ cs, ch.c ≠ 0) (hcl : cl ≠ 0) (hκ : κ ≠ 0)
    {shift ω : F} {kk lq : Nat} (hshift : shift ≠ 0) (hhalf : fpow ω (2 ^ kk) = -1)
    (hN : (cs.length + 1) * (m + 1) = 2 ^ (kk + 1))
    (hdom : cs.map (·.H) ++ [Hl] = splitD shift ω (cs.length + 1) (m + 1))
    (hL : cs.length + 1 = 2 ^ (lq + 1)) (hDlq : 2 ≤ 2 ^ lq) (hs : 1 < m + 1)
    (hPsz : 2 * (2 * (m + 1) - 1) + 1 + 1 ≤ P)
    (hw : ∀ (qs : List (List F)) (ql : List F), qs.length = cs.length → ∀ j (hj : j < (allL cs Hl cl qs ql).length) s',
      ((allL cs Hl cl qs ql)[j]'hj).1 = cosetL s' (fpow ω (cs.length + 1)) (m + 1) →
      ((allL cs Hl cl qs ql)[j]'hj).2.2.1 = finv (opv s' (allL cs Hl cl qs ql) j) * finv κ)
    (hok : ∀ c ∈ (airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (v.getD k EF.zero) A.width
      (corpusLs A)) g m preP [gm, gp] κ cs Hl cl S ζ ws).sets, c.OK)
    (hHn : ∀ ch ∈ cs, ch.H.Nodup) (hHln : Hl.Nodup) :
    PCSCloseN off (P ^ (friN1 qs ks [airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β
        (v.getD k EF.zero) A.width (corpusLs A)) g m preP [gm, gp] κ cs Hl cl S ζ ws] +
      friN2 qs [airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (v.getD k EF.zero) A.width
        (corpusLs A)) g m preP [gm, gp] κ cs Hl cl S ζ ws] ncw)) tv
      (pcsFri off tv qs ks cols [airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β
          (v.getD k EF.zero) A.width (corpusLs A)) g m preP [gm, gp] κ cs Hl cl S ζ ws]
        (fun t α β ms => [if Aborts (prefixOf α (off β)) β (tabs t) = false then
          airData (withLup A (busAlphas (prefixOf α (off β)) A) β ((tv (prefixOf α (off β)) β t).getD k EF.zero)
            A.width (corpusLs A)) g m preP cs Hl ws α β (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) [gm, gp])
          else canonData (airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (v.getD k EF.zero)
            A.width (corpusLs A)) g m preP [gm, gp] κ cs Hl cl S ζ ws).sets α β (tv (prefixOf α (off β)) β t)
            (openMulti (qs.map QGroup.ext) (cols t α β) ms)])
        ncw αb fri)
      (psimFri qs ks [airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (v.getD k EF.zero) A.width
        (corpusLs A)) g m preP [gm, gp] κ cs Hl cl S ζ ws] ncw αb fri) 0 := by
  refine pcsCloseN_fri hokq hks hcols hdet haw hncw off tv (fun t α β ms => ?_)
  by_cases hab : Aborts (prefixOf α (off β)) β (tabs t) = false
  · rw [if_pos hab]
    exact tabsHonest_corpus term hA (fun α β => prefixOf α (off β)) (fun t α β => tv (prefixOf α (off β)) β t)
      (fun t _ _ => tab t) (fun t α β => Aborts (prefixOf α (off β)) β (tabs t) = false)
      (fun t α β h => goodLup_of_noAbort (ts := fun t _ _ => tabs t) (hmem t) h)
      hgrp hcl' hb hg hinj hpreL hζ hS hc hcl hκ hshift hhalf hN hdom hL hDlq hs hPsz hw hok hHn hHln t α β ms hab
  · rw [if_neg hab]
    have hdl : ∀ H ∈ cs.map (·.H) ++ [Hl], H.length = m + 1 := fun H hH => by
      rw [hdom] at hH; exact split_length hH
    exact tabsHonest_canon α β _ _ hok
      (fun ch hch => ⟨hdl _ (List.mem_append_left _ (List.mem_map_of_mem hch)), hHn ch hch⟩)
      (hdl _ (List.mem_append_right _ List.mem_cons_self)) hHln

end Circuit
