import Ski.SourceRun
import Ski.Programs
open Term Front

set_option linter.unusedSectionVars false

/-!
# Adequacy: the compiled program, the source program and `Run` agree

Three semantics of a Joy program over a table: `Run` (`Ski/Apply.lean`),
the source semantics of its SKIjack source (`Ski/Simulation.lean`), and
weak head reduction of its compiled term.  For every valid table whose
source program has the table's structure (`JoyProg`) and whose compiled
globals are the table's terms (`GenvTable`, with `Fixed` for the
simulation), and for every valid program and stack:

- `exact_iff`: the compiled program normalizes to a term that decodes to
  a valid outcome `o` ⟺ the source program reaches the encoding of `o`
  ⟺ `Run` derives `o`;
- `diverges_iff_source`: the compiled program diverges ⟺ the source
  program reaches no outcome.

This is the converse of the simulation for programs: every convergent
compiled run comes from a source run with the same outcome.  The
directions come from three theorems: `run_source` (a derivation is a
source run), `simulation_steps` (a source run is matched by the compiled
term), and `Table.program_exact` (a compiled run that normalizes has a
derivation, `Ski/Converse.lean` underneath).  The four source texts meet
the hypotheses (`Ski/Table.lean`'s tables: `NoQuot.adequate` and its
siblings).
-/

/-- `genv` gives a table's compiled globals. -/
structure GenvTable (genv : Nm → Term) (tb : Table) : Prop where
  zero : genv (nm! "Zero") = Scott.Zero
  suc : genv (nm! "Suc") = Scott.Suc
  num : genv (nm! "Num") = Scott.Num
  quot : genv (nm! "Quot") = Scott.Quot
  empty : genv (nm! "Empty") = Scott.Empty
  push : genv (nm! "Push") = Scott.Push
  rval : genv (nm! "RVal") = Scott.RVal
  rerr : genv (nm! "RErr") = Scott.RErr
  qs : ∀ k, k < tb.n → genv (qname k) = tb.Qs k
  qcons : genv (nm! "QCons") = tb.QCons
  qunit : genv (nm! "QUnit") = tb.QUnit
  qthen : genv (nm! "QThen") = tb.QThen
  wDup : genv (nm! "wDup") = Scott.wDup
  wSwap : genv (nm! "wSwap") = Scott.wSwap
  wPop : genv (nm! "wPop") = Scott.wPop
  wQcons : genv (nm! "wQcons") = tb.wQcons
  wCat : genv (nm! "wCat") = tb.wCat
  wUnit : genv (nm! "wUnit") = tb.wUnit
  wDip : genv (nm! "wDip") = Scott.wDip
  wDo : genv (nm! "wDo") = Scott.wDo
  wIfz : genv (nm! "wIfz") = Scott.wIfz
  wLit : genv (nm! "wLit") = Scott.wLit
  wQuote : genv (nm! "wQuote") = Scott.wQuote
  wAdd : genv (nm! "wAdd") = Scott.wAdd
  seq : genv (nm! "seq") = Scott.seq
  idW : genv (nm! "idW") = Scott.idW
  applyU : genv (nm! "applyU") = tb.applyU

/-- A valid outcome: its stack's quotations are the table's. -/
def Outcome.ok (n : Nat) : Outcome → Bool
  | .val s => s.all (Item.ok n)
  | .err => true

/-- The source program run on a stack. -/
def srcRun (p : List Word) (st : Stack) : Cl := .app (progS (.gref (nm! "applyU")) p) (stackS st)

section
variable {P : Nm → Option GDef} {genv : Nm → Term} {tb : Table}

-- ---------------------------------------------------------------------------
-- Encodings translate to encodings
-- ---------------------------------------------------------------------------

theorem tr_gref_eq (hG : genv n = t) : Tr genv P (.gref n) t := hG ▸ .gref n

theorem tr_natS (hG : GenvTable genv tb) : ∀ n, Tr genv P (natS n) (encNat n)
  | 0 => tr_gref_eq hG.zero
  | n + 1 => .app (tr_gref_eq hG.suc) (tr_natS hG n)

mutual
  theorem tr_itemS (hG : GenvTable genv tb) :
      ∀ x : Item, x.ok tb.n = true → Tr genv P (itemS x) (@encItem tb.kit x)
    | .num n, _ => .app (tr_gref_eq hG.num) (tr_natS hG n)
    | .quot q, h => .app (tr_gref_eq hG.quot) (tr_quotS hG q h)
  theorem tr_quotS (hG : GenvTable genv tb) :
      ∀ q : Quotation, q.ok tb.n = true → Tr genv P (quotS q) (@encQuot tb.kit q)
    | .stat k, h => tr_gref_eq (hG.qs k (of_decide_eq_true h))
    | .cons x r, h => by
      simp only [Quotation.ok, Bool.and_eq_true] at h
      exact .app (.app (tr_gref_eq hG.qcons) (tr_itemS hG x h.1)) (tr_quotS hG r h.2)
    | .unit x, h => .app (tr_gref_eq hG.qunit) (tr_itemS hG x h)
    | .then r, h => .app (tr_gref_eq hG.qthen) (tr_quotS hG r h)
end

theorem tr_stackS (hG : GenvTable genv tb) :
    ∀ st : Stack, st.all (Item.ok tb.n) = true → Tr genv P (stackS st) (@encStack tb.kit st)
  | [], _ => tr_gref_eq hG.empty
  | a :: st, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact .app (.app (tr_gref_eq hG.push) (tr_itemS hG a h.1)) (tr_stackS hG st h.2)

attribute [local irreducible] Table.wQcons Table.wCat Table.wUnit Table.applyU in
theorem tr_wordS (hG : GenvTable genv tb) :
    ∀ w : Word, w.ok tb.n = true →
      Tr genv P (wordS (.gref (nm! "applyU")) w) (@wordTerm tb.kit tb.applyU w)
  | .dup, _ => tr_gref_eq hG.wDup
  | .swap, _ => tr_gref_eq hG.wSwap
  | .pop, _ => tr_gref_eq hG.wPop
  | .cons, _ => tr_gref_eq hG.wQcons
  | .cat, _ => tr_gref_eq hG.wCat
  | .unit, _ => tr_gref_eq hG.wUnit
  | .dip, _ => .app (tr_gref_eq hG.wDip) (tr_gref_eq hG.applyU)
  | .i, _ => .app (tr_gref_eq hG.wDo) (tr_gref_eq hG.applyU)
  | .ifz, _ => .app (tr_gref_eq hG.wIfz) (tr_gref_eq hG.applyU)
  | .lit n, _ => .app (tr_gref_eq hG.wLit) (tr_natS hG n)
  | .quote q, h => .app (tr_gref_eq hG.wQuote) (tr_quotS hG q h)
  | .add, _ => tr_gref_eq hG.wAdd

attribute [local irreducible] Table.wQcons Table.wCat Table.wUnit Table.applyU in
theorem tr_progS (hG : GenvTable genv tb) :
    ∀ p : List Word, p.all (Word.ok tb.n) = true →
      Tr genv P (progS (.gref (nm! "applyU")) p) (@N tb.kit tb.applyU p)
  | [], _ => tr_gref_eq hG.idW
  | [w], h => by
    simp only [List.all_cons, List.all_nil, Bool.and_true] at h
    exact tr_wordS hG w h
  | w :: w' :: ws, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact .app (.app (tr_gref_eq hG.seq) (tr_wordS hG w h.1))
      (tr_progS hG (w' :: ws) (by simp only [List.all_cons, Bool.and_eq_true]; exact h.2))

-- ---------------------------------------------------------------------------
-- Encodings translate only to terms that decode to them
-- ---------------------------------------------------------------------------

/-- A constructor's translation is its compiled term. -/
theorem tr_ctor_inv (hP : P n = some (.ctor a j m)) {t : Term} (h : Tr genv P (.gref n) t) :
    t = genv n := by
  cases h with
  | gref _ => rfl
  | self hP' _ =>
    rw [hP] at hP'
    cases hP'

theorem dec_of_tr_natS (hJ : JoyProg P tb) (hG : GenvTable genv tb) :
    ∀ n {t : Term}, Tr genv P (natS n) t → DecNat t n
  | 0, t, h => by
    letI : Kit := tb.kit
    haveI : KitElim := tb.kit_elim
    rw [tr_ctor_inv (hJ.kernel _ _ rfl) h, hG.zero]
    exact dec_zero
  | n + 1, t, h => by
    letI : Kit := tb.kit
    haveI : KitElim := tb.kit_elim
    cases h with
    | app hf ha =>
      rw [tr_ctor_inv (hJ.kernel _ _ rfl) hf, hG.suc]
      exact dec_suc (dec_of_tr_natS hJ hG n ha)

mutual
  theorem dec_of_tr_itemS (hJ : JoyProg P tb) (hG : GenvTable genv tb) :
      ∀ x : Item, x.ok tb.n = true → ∀ {t : Term}, Tr genv P (itemS x) t → @DecItem tb.kit t x
    | .num n, _, t, h => by
      letI : Kit := tb.kit
      haveI : KitElim := tb.kit_elim
      cases h with
      | app hf ha =>
        rw [tr_ctor_inv (hJ.kernel _ _ rfl) hf, hG.num]
        exact dec_num (dec_of_tr_natS hJ hG n ha)
    | .quot q, hq, t, h => by
      letI : Kit := tb.kit
      haveI : KitElim := tb.kit_elim
      cases h with
      | app hf ha =>
        rw [tr_ctor_inv (hJ.kernel _ _ rfl) hf, hG.quot]
        exact dec_quot (dec_of_tr_quotS hJ hG q hq ha)
  theorem dec_of_tr_quotS (hJ : JoyProg P tb) (hG : GenvTable genv tb) :
      ∀ q : Quotation, q.ok tb.n = true → ∀ {t : Term}, Tr genv P (quotS q) t → @DecQuot tb.kit t q
    | .stat k, hq, t, h => by
      letI : Kit := tb.kit
      haveI : KitElim := tb.kit_elim
      have hk : k < tb.n := of_decide_eq_true hq
      rw [tr_ctor_inv (hJ.qs k hk) h, hG.qs k hk]
      exact dec_stat hk
    | .cons x r, hq, t, h => by
      letI : Kit := tb.kit
      haveI : KitElim := tb.kit_elim
      simp only [Quotation.ok, Bool.and_eq_true] at hq
      cases h with
      | app hf ha =>
        cases hf with
        | app hc hx =>
          rw [tr_ctor_inv hJ.qcons hc, hG.qcons]
          exact dec_qcons (dec_of_tr_itemS hJ hG x hq.1 hx)
            (dec_of_tr_quotS hJ hG r hq.2 ha)
    | .unit x, hq, t, h => by
      letI : Kit := tb.kit
      haveI : KitElim := tb.kit_elim
      cases h with
      | app hf ha =>
        rw [tr_ctor_inv hJ.qunit hf, hG.qunit]
        exact dec_qunit (dec_of_tr_itemS hJ hG x hq ha)
    | .then r, hq, t, h => by
      letI : Kit := tb.kit
      haveI : KitElim := tb.kit_elim
      cases h with
      | app hf ha =>
        rw [tr_ctor_inv hJ.qthen hf, hG.qthen]
        exact dec_qthen (dec_of_tr_quotS hJ hG r hq ha)
end

theorem dec_of_tr_stackS (hJ : JoyProg P tb) (hG : GenvTable genv tb) :
    ∀ st : Stack, st.all (Item.ok tb.n) = true → ∀ {t : Term}, Tr genv P (stackS st) t →
      @DecStack tb.kit t st
  | [], _, t, h => by
    letI : Kit := tb.kit
    haveI : KitElim := tb.kit_elim
    rw [tr_ctor_inv (hJ.kernel _ _ rfl) h, hG.empty]
    exact dec_empty
  | a :: st, hs, t, h => by
    letI : Kit := tb.kit
    haveI : KitElim := tb.kit_elim
    simp only [List.all_cons, Bool.and_eq_true] at hs
    cases h with
    | app hf ha =>
      cases hf with
      | app hc hx =>
        rw [tr_ctor_inv (hJ.kernel _ _ rfl) hc, hG.push]
        exact dec_push (dec_of_tr_itemS hJ hG a hs.1 hx)
          (dec_of_tr_stackS hJ hG st hs.2 ha)

/-- A translated outcome meets its contract. -/
theorem contract_of_tr_outS (hJ : JoyProg P tb) (hG : GenvTable genv tb) {o : Outcome}
    (ho : o.ok tb.n = true) {t : Term} (h : Tr genv P (outS o) t) : @Contract tb.kit t o := by
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  cases o with
  | val st =>
    cases h with
    | app hf ha =>
      rw [tr_ctor_inv (hJ.kernel _ _ rfl) hf, hG.rval]
      exact contract_val (.refl _) (dec_of_tr_stackS hJ hG st ho ha)
  | err =>
    rw [tr_ctor_inv (hJ.kernel _ _ rfl) h, hG.rerr]
    exact contract_err (.refl _)

/-- A translated outcome, valid or not, normalizes. -/
theorem converges_of_tr_outS (hJ : JoyProg P tb) (hG : GenvTable genv tb) {o : Outcome} {t : Term}
    (h : Tr genv P (outS o) t) : Converges t := by
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  cases o with
  | val st =>
    cases h with
    | app hf _ =>
      rw [tr_ctor_inv (hJ.kernel _ _ rfl) hf, hG.rval]
      exact ⟨_, eval_rval _⟩
  | err =>
    rw [tr_ctor_inv (hJ.kernel _ _ rfl) h, hG.rerr]
    exact ⟨_, .refl _, .K1 K⟩

-- ---------------------------------------------------------------------------
-- The three semantics agree
-- ---------------------------------------------------------------------------

/-- The source program run, translated: the compiled program, as `N`. -/
theorem tr_srcRun (hG : GenvTable genv tb) {p : List Word} {st : Stack}
    (hp : p.all (Word.ok tb.n) = true) (hs : st.all (Item.ok tb.n) = true) :
    Tr genv P (srcRun p st) (@N tb.kit tb.applyU p ⬝ @encStack tb.kit st) :=
  .app (tr_progS hG p hp) (tr_stackS hG st hs)

/-- **A source run is a derivation.** -/
theorem run_of_source (hv : tb.Valid) (hJ : JoyProg P tb) (hF : Fixed P genv) (hG : GenvTable genv tb)
    {p : List Word} {st : Stack} {o : Outcome} (hp : p.all (Word.ok tb.n) = true)
    (hs : st.all (Item.ok tb.n) = true) (ho : o.ok tb.n = true)
    (h : SSteps P (srcRun p st) (outS o)) : @Run tb.kit (.prog p) st o := by
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  cases simulation_steps hF h (tr_srcRun hG hp hs) with
  | intro t' ht =>
    have hc := Contract.of_wsteps ((tb.progT_wsteps p tb.applyU _).trans ht.1)
      (contract_of_tr_outS hJ hG ho ht.2)
    cases hc with
    | intro u hu =>
      exact Table.program_exact hv hp (encStack_dec st hs) hu.1 hu.2

/-- **Exactness.**  For a valid outcome, the compiled program normalizes
    to a term that decodes to it exactly when the source program reaches
    its encoding, exactly when `Run` derives it. -/
theorem exact_iff (hv : tb.Valid) (hJ : JoyProg P tb) (hF : Fixed P genv) (hG : GenvTable genv tb)
    {p : List Word} {st : Stack} {o : Outcome} (hp : p.all (Word.ok tb.n) = true)
    (hs : st.all (Item.ok tb.n) = true) (ho : o.ok tb.n = true) :
    ((∃ u, Eval (tb.progT p ⬝ tb.applyU ⬝ @encStack tb.kit st) u ∧ @Decodes tb.kit u o) ↔
      SSteps P (srcRun p st) (outS o)) ∧
    (SSteps P (srcRun p st) (outS o) ↔ @Run tb.kit (.prog p) st o) := by
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  have h1 : (∃ u, Eval (tb.progT p ⬝ tb.applyU ⬝ @encStack tb.kit st) u ∧ @Decodes tb.kit u o) →
      @Run tb.kit (.prog p) st o := fun ⟨u, he, hd⟩ =>
    Table.program_exact hv hp (encStack_dec st hs) he hd
  have h2 : @Run tb.kit (.prog p) st o →
      (∃ u, Eval (tb.progT p ⬝ tb.applyU ⬝ @encStack tb.kit st) u ∧ @Decodes tb.kit u o) :=
    fun h => Table.program_apply hv h hp (encStack_dec st hs)
  exact ⟨⟨fun h => run_source hJ (h1 h), fun h => h2 (run_of_source hv hJ hF hG hp hs ho h)⟩,
    ⟨run_of_source hv hJ hF hG hp hs ho, run_source hJ⟩⟩

/-- **Divergence.**  The compiled program diverges exactly when the source
    program reaches no outcome. -/
theorem diverges_iff_source (hv : tb.Valid) (hJ : JoyProg P tb) (hF : Fixed P genv)
    (hG : GenvTable genv tb) {p : List Word} {st : Stack} (hp : p.all (Word.ok tb.n) = true)
    (hs : st.all (Item.ok tb.n) = true) :
    Diverges (tb.progT p ⬝ tb.applyU ⬝ @encStack tb.kit st) ↔
      ∀ o, ¬ SSteps P (srcRun p st) (outS o) := by
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  letI : Kit := tb.kit
  haveI : KitElim := tb.kit_elim
  constructor
  · intro hd o h
    cases simulation_steps hF h (tr_srcRun hG hp hs) with
    | intro t' ht =>
      have hn : ¬ Diverges (@N tb.kit tb.applyU p ⬝ @encStack tb.kit st) := by
        letI : Kit := tb.kit
        haveI : KitElim := tb.kit_elim
        intro hdn
        cases converges_of_tr_outS hJ hG ht.2 with
        | intro w hw =>
          cases eval_back ht.1 hw with
          | intro v hv' => exact hdn v hv'.1
      exact hn ((diverges_iff_of_wsteps (tb.progT_wsteps p tb.applyU _)).mp hd)
  · intro hno
    refine (Table.program_diverges hv hp (encStack_dec st hs)).mpr ?_
    intro o h
    exact hno o (run_source hJ h)

end

-- ---------------------------------------------------------------------------
-- Checking a source file against a table, in one pass
-- ---------------------------------------------------------------------------

/-- The fixed globals `GenvTable` names, with the table's terms. -/
def genvPairs (genv : Nm → Term) (tb : Table) : List (Term × Term) :=
  [(genv (nm! "Zero"), Scott.Zero), (genv (nm! "Suc"), Scott.Suc), (genv (nm! "Num"), Scott.Num),
   (genv (nm! "Quot"), Scott.Quot), (genv (nm! "Empty"), Scott.Empty),
   (genv (nm! "Push"), Scott.Push), (genv (nm! "RVal"), Scott.RVal),
   (genv (nm! "RErr"), Scott.RErr), (genv (nm! "QCons"), tb.QCons),
   (genv (nm! "QUnit"), tb.QUnit), (genv (nm! "QThen"), tb.QThen),
   (genv (nm! "wDup"), Scott.wDup), (genv (nm! "wSwap"), Scott.wSwap),
   (genv (nm! "wPop"), Scott.wPop), (genv (nm! "wQcons"), tb.wQcons),
   (genv (nm! "wCat"), tb.wCat), (genv (nm! "wUnit"), tb.wUnit),
   (genv (nm! "wDip"), Scott.wDip), (genv (nm! "wDo"), Scott.wDo),
   (genv (nm! "wIfz"), Scott.wIfz), (genv (nm! "wLit"), Scott.wLit),
   (genv (nm! "wQuote"), Scott.wQuote), (genv (nm! "wAdd"), Scott.wAdd),
   (genv (nm! "seq"), Scott.seq), (genv (nm! "idW"), Scott.idW),
   (genv (nm! "applyU"), tb.applyU)]

/-- Everything `GenvTable` and `JoyProg` ask of a source file beyond the
    kernel, as one check. -/
def tableCheck (P : Nm → Option GDef) (genv : Nm → Term) (tb : Table) : Bool :=
  (genvPairs genv tb).all (fun p => p.1 == p.2) &&
  (List.range tb.n).all (fun k => genv (qname k) == tb.Qs k) &&
  (List.range tb.n).all (fun k => P (qname k) == some (.ctor 0 k (tb.n + 3))) &&
  (P (nm! "QCons") == some (.ctor 2 tb.n (tb.n + 3))) &&
  (P (nm! "QUnit") == some (.ctor 1 (tb.n + 1) (tb.n + 3))) &&
  (P (nm! "QThen") == some (.ctor 1 (tb.n + 2) (tb.n + 3))) &&
  (List.range tb.n).all (fun k => P (bname k) == some (.eqn ⟨[0], none, bodyC (tb.body k)⟩)) &&
  (P (nm! "applyU") == some (.eqn ⟨[1, 2], some 0, applyC tb.n⟩))

theorem of_tableCheck {P : Nm → Option GDef} {genv : Nm → Term} {tb : Table}
    (hK : HasKernel P) (h : tableCheck P genv tb = true) : JoyProg P tb ∧ GenvTable genv tb := by
  simp only [tableCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  have g : ∀ a b, (a, b) ∈ genvPairs genv tb → a = b := fun a b hm => h.1.1.1.1.1.1.1 (a, b) hm
  refine ⟨⟨hK, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩, ?_⟩
  exact ⟨g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]),
    g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]),
    g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]), h.1.1.1.1.1.1.2,
    g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]),
    g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]),
    g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]),
    g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]),
    g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]),
    g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs]), g _ _ (by simp [genvPairs])⟩
