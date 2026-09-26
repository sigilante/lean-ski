import Ski.SourceJoy
import Ski.Apply
open Term Front

set_option linter.unusedSectionVars false

/-!
# Every derivation of `Run`, realized by the source

`Run` (`Ski/Apply.lean`) is the big-step semantics of Joy programs over a
table.  This file proves that the source program realizes it: for a
source program `P` with a table's structure (`JoyProg`: the kernel, the
table's constructors, each static quotation's body and `applyU`, as
`skilark.joy.compiled` writes them), every derivation of `Run` is a run of
the source semantics from the encoding of its input to the encoding of
its outcome (`run_source`).  It is `run_sound` at the source, and simpler:
the source has no thunks, so the encodings are exact.
-/

/-- `b(k+1)`, the `k`-th static quotation's body. -/
def bname (k : Nat) : Nm := 98 :: (Nat.toDigits 10 (k + 1)).map Char.toNat

-- ---------------------------------------------------------------------------
-- The table's source, as `skilark.joy.compiled` writes it
-- ---------------------------------------------------------------------------

def natC : Nat → CSrc
  | 0 => .glob (nm! "Zero")
  | n + 1 => .app (.glob (nm! "Suc")) (natC n)

mutual
  def itemCS : Item → CSrc
    | .num n => .app (.glob (nm! "Num")) (natC n)
    | .quot q => .app (.glob (nm! "Quot")) (quoteCS q)
  def quoteCS : Quotation → CSrc
    | .stat k => .glob (qname k)
    | .cons x r => .app (.app (.glob (nm! "QCons")) (itemCS x)) (quoteCS r)
    | .unit x => .app (.glob (nm! "QUnit")) (itemCS x)
    | .then r => .app (.glob (nm! "QThen")) (quoteCS r)
end

/-- A word in a body, the eliminator `ap` being `v 0`. -/
def wordC : Word → CSrc
  | .dup => .glob (nm! "wDup")
  | .swap => .glob (nm! "wSwap")
  | .pop => .glob (nm! "wPop")
  | .cons => .glob (nm! "wQcons")
  | .cat => .glob (nm! "wCat")
  | .unit => .glob (nm! "wUnit")
  | .dip => .app (.glob (nm! "wDip")) (.var 0)
  | .i => .app (.glob (nm! "wDo")) (.var 0)
  | .ifz => .app (.glob (nm! "wIfz")) (.var 0)
  | .lit n => .app (.glob (nm! "wLit")) (natC n)
  | .quote q => .app (.glob (nm! "wQuote")) (quoteCS q)
  | .add => .glob (nm! "wAdd")

/-- `b ap = seq w1 (seq w2 … wm)`, or `idW`. -/
def bodyC : List Word → CSrc
  | [] => .glob (nm! "idW")
  | [w] => wordC w
  | w :: w' :: ws => .app (.app (.glob (nm! "seq")) (wordC w)) (bodyC (w' :: ws))

/-- `QCons x r (applyU r (Push x s))`, lowered: `self0 q1 s2 x3 r4`. -/
def armConsC : CSrc :=
  .lam 3 (.lam 4 (.app (.app (.var 0) (.var 4))
    (.app (.app (.glob (nm! "Push")) (.var 3)) (.var 2))))

/-- `QUnit x (RVal (Push x s))`: `x5`. -/
def armUnitC : CSrc :=
  .lam 5 (.app (.glob (nm! "RVal")) (.app (.app (.glob (nm! "Push")) (.var 5)) (.var 2)))

/-- `QThen b (seq (wDo applyU) (applyU b) s)`: `b6`. -/
def armThenC : CSrc :=
  .lam 6 (.app (.app (.app (.glob (nm! "seq")) (.app (.glob (nm! "wDo")) (.var 0)))
    (.app (.var 0) (.var 6))) (.var 2))

/-- `applyU q s = q |> { Q1 (b1 applyU s); …; QCons …; QUnit …; QThen … }`,
    lowered. -/
def applyC (n : Nat) : CSrc :=
  .app (.app (.app ((List.range n).foldl (fun acc k =>
      .app acc (.app (.app (.glob (bname k)) (.var 0)) (.var 2))) (.var 1))
    armConsC) armUnitC) armThenC

/-- **A source program with a table's structure.** -/
structure JoyProg (P : Nm → Option GDef) (tb : Table) : Prop where
  kernel : HasKernel P
  qs : ∀ k, k < tb.n → P (qname k) = some (.ctor 0 k (tb.n + 3))
  qcons : P (nm! "QCons") = some (.ctor 2 tb.n (tb.n + 3))
  qunit : P (nm! "QUnit") = some (.ctor 1 (tb.n + 1) (tb.n + 3))
  qthen : P (nm! "QThen") = some (.ctor 1 (tb.n + 2) (tb.n + 3))
  bodies : ∀ k, k < tb.n → P (bname k) = some (.eqn ⟨[0], none, bodyC (tb.body k)⟩)
  applyU : P (nm! "applyU") = some (.eqn ⟨[1, 2], some 0, applyC tb.n⟩)

-- ---------------------------------------------------------------------------
-- A program's source term
-- ---------------------------------------------------------------------------

/-- A word list's source term, given the eliminator. -/
def progS (ap : Cl) : List Word → Cl
  | [] => .gref (nm! "idW")
  | [w] => wordS ap w
  | w :: w' :: ws => (Cl.gref (nm! "seq")).apps [wordS ap w, progS ap (w' :: ws)]

theorem inst_natC (sc : List Nat) (ρ : Nat → Cl) : ∀ n, inst sc ρ (natC n) = natS n
  | 0 => rfl
  | n + 1 => by
    show Cl.app (.gref (nm! "Suc")) (inst sc ρ (natC n)) = _
    rw [inst_natC sc ρ n]
    rfl

mutual
  theorem inst_itemCS (sc : List Nat) (ρ : Nat → Cl) : ∀ x, inst sc ρ (itemCS x) = itemS x
    | .num n => by
      show Cl.app (.gref (nm! "Num")) (inst sc ρ (natC n)) = _
      rw [inst_natC]
      rfl
    | .quot q => by
      show Cl.app (.gref (nm! "Quot")) (inst sc ρ (quoteCS q)) = _
      rw [inst_quoteCS sc ρ q]
      rfl
  theorem inst_quoteCS (sc : List Nat) (ρ : Nat → Cl) : ∀ q, inst sc ρ (quoteCS q) = quotS q
    | .stat _ => rfl
    | .cons x r => by
      show Cl.app (.app (.gref (nm! "QCons")) (inst sc ρ (itemCS x))) (inst sc ρ (quoteCS r)) = _
      rw [inst_itemCS sc ρ x, inst_quoteCS sc ρ r]
      rfl
    | .unit x => by
      show Cl.app (.gref (nm! "QUnit")) (inst sc ρ (itemCS x)) = _
      rw [inst_itemCS sc ρ x]
      rfl
    | .then r => by
      show Cl.app (.gref (nm! "QThen")) (inst sc ρ (quoteCS r)) = _
      rw [inst_quoteCS sc ρ r]
      rfl
end

theorem inst_wordC (sc : List Nat) (ρ : Nat → Cl) : ∀ w, inst sc ρ (wordC w) = wordS (ρ 0) w
  | .dup => rfl
  | .swap => rfl
  | .pop => rfl
  | .cons => rfl
  | .cat => rfl
  | .unit => rfl
  | .dip => rfl
  | .i => rfl
  | .ifz => rfl
  | .lit n => by
    show Cl.app (.gref (nm! "wLit")) (inst sc ρ (natC n)) = _
    rw [inst_natC]
    rfl
  | .quote q => by
    show Cl.app (.gref (nm! "wQuote")) (inst sc ρ (quoteCS q)) = _
    rw [inst_quoteCS]
    rfl
  | .add => rfl

theorem inst_bodyC (sc : List Nat) (ρ : Nat → Cl) : ∀ p, inst sc ρ (bodyC p) = progS (ρ 0) p
  | [] => rfl
  | [w] => inst_wordC sc ρ w
  | w :: w' :: ws => by
    show Cl.app (.app (.gref (nm! "seq")) (inst sc ρ (wordC w))) (inst sc ρ (bodyC (w' :: ws))) = _
    rw [inst_wordC, inst_bodyC sc ρ (w' :: ws)]
    rfl

-- ---------------------------------------------------------------------------
-- `seq`, at the source
-- ---------------------------------------------------------------------------

theorem seq_source_stages : ∃ k0,
    SSteps KP ((Cl.gref (nm! "seq")).apps [hole 0, hole 1, hole 2])
      ((Cl.app (hole 0) (hole 2)).apps [k0, errH, rtimeH]) ∧
    SSteps KP (.app k0 (hole 3)) (.app (hole 1) (hole 3)) :=
  ⟨_, seval_sound (k := 1) rfl, seval_sound (k := 1) rfl⟩

/-- **`seq f g` follows `f`'s outcome**, strictly, at the source. -/
theorem seq_source {P : Nm → Option GDef} (hK : HasKernel P) {f g s : Cl} {o : Outcome}
    {k : Stack → Outcome} (hf : SSteps P (.app f s) (outS o))
    (hg : ∀ S', o = .val S' → SSteps P (.app g (stackS S')) (outS (k S'))) :
    SSteps P ((Cl.gref (nm! "seq")).apps [f, g, s]) (outS (bindO o k)) := by
  cases seq_source_stages with
  | intro k0 hk =>
    cases o with
    | val S' =>
      have h1 := (hk.1.substC (σ := fill [f, g, s, stackS S']) (fill_K _)).mono hK
      have h2 := (hk.2.substC (σ := fill [f, g, s, stackS S']) (fill_K _)).mono hK
      exact h1.trans ((SSteps.apps_left hf _).trans ((outS_val_cases hK S' _ _ _).trans
        (h2.trans (hg S' rfl))))
    | err =>
      have h1 := (hk.1.substC (σ := fill [f, g, s]) (fill_K _)).mono hK
      exact h1.trans ((SSteps.apps_left hf _).trans (outS_err_cases hK _ _ _))

-- ---------------------------------------------------------------------------
-- `applyU`, at the source: the case over the table's constructors
-- ---------------------------------------------------------------------------

/-- The environment of `applyU q s`'s body. -/
def applyEnv (q s : Cl) : Nat → Cl := overrideCl junk [0, 1, 2] [.gref (nm! "applyU"), q, s]

/-- The `k`-th static arm: `b(k+1) applyU s`. -/
def armStatic (s : Cl) (k : Nat) : Cl := (Cl.gref (bname k)).apps [.gref (nm! "applyU"), s]

/-- The continuations `applyU q s` applies `q` to. -/
def armsOf (n : Nat) (q s : Cl) : List Cl :=
  (List.range n).map (armStatic s) ++
    [inst [0, 1, 2] (applyEnv q s) armConsC, inst [0, 1, 2] (applyEnv q s) armUnitC,
     inst [0, 1, 2] (applyEnv q s) armThenC]

theorem armsOf_length (n : Nat) (q s : Cl) : (armsOf n q s).length = n + 3 := by
  unfold armsOf
  rw [List.length_append, List.length_map, List.length_range]
  rfl

theorem inst_arms (q s : Cl) : ∀ n,
    inst [0, 1, 2] (applyEnv q s) ((List.range n).foldl (fun acc k =>
      .app acc (.app (.app (.glob (bname k)) (.var 0)) (.var 2))) (.var 1)) =
    q.apps ((List.range n).map (armStatic s))
  | 0 => rfl
  | n + 1 => by
    have e : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [e, List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append, Cl.apps_append]
    show Cl.app (inst [0, 1, 2] (applyEnv q s) _) _ = _
    rw [inst_arms q s n]
    rfl

/-- `applyU q s` unrolls to `q` applied to its continuations. -/
theorem applyU_dispatch {P : Nm → Option GDef} {tb : Table} (hJ : JoyProg P tb) (q s : Cl) :
    SSteps P ((Cl.gref (nm! "applyU")).apps [q, s]) (q.apps (armsOf tb.n q s)) := by
  have h := SStep.fix (args := [q, s]) hJ.applyU rfl
  have e : inst (0 :: [1, 2]) (overrideCl junk (0 :: [1, 2]) (.gref (nm! "applyU") :: [q, s]))
      (applyC tb.n) = q.apps (armsOf tb.n q s) := by
    show Cl.app (.app (.app (inst [0, 1, 2] (applyEnv q s) _) _) _) _ = _
    rw [inst_arms]
    unfold armsOf
    rw [Cl.apps_append]
    rfl
  rw [e] at h
  exact SSteps.single h

theorem getD_map_range {α : Type} (f : Nat → α) (d : α) :
    ∀ n k, k < n → ((List.range n).map f).getD k d = f k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    have e : List.range (n + 1) = List.range n ++ [n] := List.range_succ
    rw [e, List.map_append]
    by_cases hk : k < n
    · rw [getD_app_left _ _ _ _ (by rw [List.length_map, List.length_range]; exact hk)]
      exact getD_map_range f d n k hk
    · have hkn : k = n := by omega
      subst hkn
      have := getD_app_right d ((List.range k).map f) [f k] 0
      rw [List.length_map, List.length_range, Nat.add_zero] at this
      exact this

theorem getD_armsOf_static {n k : Nat} (hk : k < n) (q s : Cl) :
    (armsOf n q s).getD k (.const K) = armStatic s k := by
  unfold armsOf
  rw [getD_app_left _ _ _ _ (by rw [List.length_map, List.length_range]; exact hk)]
  exact getD_map_range _ _ n k hk

theorem getD_armsOf_last (n : Nat) (q s : Cl) (i : Nat) :
    (armsOf n q s).getD (n + i) (.const K) =
      [inst [0, 1, 2] (applyEnv q s) armConsC, inst [0, 1, 2] (applyEnv q s) armUnitC,
       inst [0, 1, 2] (applyEnv q s) armThenC].getD i (.const K) := by
  unfold armsOf
  have := getD_app_right (Cl.const K) ((List.range n).map (armStatic s))
    [inst [0, 1, 2] (applyEnv q s) armConsC, inst [0, 1, 2] (applyEnv q s) armUnitC,
     inst [0, 1, 2] (applyEnv q s) armThenC] i
  rw [List.length_map, List.length_range] at this
  exact this

/-- An arm, filled: the placeholder environment becomes `applyEnv q s`. -/
theorem arm_fill3 (c : CSrc) (q s x : Cl) :
    (inst [0, 1, 2] (applyEnv (hole 0) (hole 1)) c).substC (fill [q, s, x]) =
      inst [0, 1, 2] (applyEnv q s) c := by
  rw [inst_substC]
  congr 1
  funext i
  unfold applyEnv
  rw [overrideCl_substC, junk_substC (fill_K _)]
  rfl

theorem arm_fill4 (c : CSrc) (q s x y : Cl) :
    (inst [0, 1, 2] (applyEnv (hole 0) (hole 1)) c).substC (fill [q, s, x, y]) =
      inst [0, 1, 2] (applyEnv q s) c := by
  rw [inst_substC]
  congr 1
  funext i
  unfold applyEnv
  rw [overrideCl_substC, junk_substC (fill_K _)]
  rfl

theorem armCons_source : SSteps KP ((inst [0, 1, 2] (applyEnv (hole 0) (hole 1)) armConsC).apps
    [hole 2, hole 3]) ((Cl.gref (nm! "applyU")).apps [hole 3, pushH (hole 2) (hole 1)]) :=
  seval_sound (k := 1) rfl

theorem armUnit_source : SSteps KP ((inst [0, 1, 2] (applyEnv (hole 0) (hole 1)) armUnitC).apps
    [hole 2]) (rvalH (pushH (hole 2) (hole 1))) :=
  seval_sound (k := 1) rfl

theorem armThen_source : SSteps KP ((inst [0, 1, 2] (applyEnv (hole 0) (hole 1)) armThenC).apps
    [hole 2]) ((Cl.gref (nm! "seq")).apps
      [.app (.gref (nm! "wDo")) (.gref (nm! "applyU")), .app (.gref (nm! "applyU")) (hole 2), hole 1]) :=
  seval_sound (k := 1) rfl

-- ---------------------------------------------------------------------------
-- Every derivation, at the source
-- ---------------------------------------------------------------------------

/-- What a derivation promises at the source. -/
def SoundS (P : Nm → Option GDef) : Job → Stack → Outcome → Prop
  | .quot q, st, o => SSteps P ((Cl.gref (nm! "applyU")).apps [quotS q, stackS st]) (outS o)
  | .prog p, st, o => SSteps P (.app (progS (.gref (nm! "applyU")) p) (stackS st)) (outS o)
  | .word w, st, o => SSteps P (.app (wordS (.gref (nm! "applyU")) w) (stackS st)) (outS o)

theorem idW_source {P : Nm → Option GDef} (hK : HasKernel P) (st : Stack) :
    SSteps P (.app (.gref (nm! "idW")) (stackS st)) (outS (.val st)) :=
  ((seval_sound (k := 1) rfl : SSteps KP (.app (.gref (nm! "idW")) (hole 0)) (rvalH (hole 0))).substC
    (σ := fill [stackS st]) (fill_K _)).mono hK

/-- **Every derivation of `Run` is a run of the source.** -/
theorem run_source {P : Nm → Option GDef} {tb : Table} (hJ : JoyProg P tb) {t : Job} {st : Stack}
    {o : Outcome} (h : @Run tb.kit t st o) : SoundS P t st o := by
  have hK := hJ.kernel
  induction h with
  | @stat k st o hk _ ih =>
    show SSteps P ((Cl.gref (nm! "applyU")).apps [quotS (.stat k), stackS st]) (outS o)
    have hk' : k < tb.n := hk
    refine (applyU_dispatch hJ _ _).trans ?_
    have hc := SStep.ctor (P := P) (fs := []) (ks := armsOf tb.n (quotS (.stat k)) (stackS st))
      (hJ.qs k hk') (by omega) rfl (armsOf_length _ _ _)
    rw [getD_armsOf_static hk'] at hc
    refine (SSteps.single hc).trans ?_
    have hd := SStep.delta (P := P) (args := [.gref (nm! "applyU")]) (hJ.bodies k hk') rfl
    rw [inst_bodyC] at hd
    exact (SSteps.single (SStep.apps_left hd [stackS st])).trans ih
  | @cons x r st o _ ih =>
    show SSteps P ((Cl.gref (nm! "applyU")).apps [quotS (.cons x r), stackS st]) (outS o)
    refine (applyU_dispatch hJ _ _).trans ?_
    have hc := SStep.ctor (P := P) (fs := [itemS x, quotS r])
      (ks := armsOf tb.n (quotS (.cons x r)) (stackS st)) hJ.qcons (by omega) rfl (armsOf_length _ _ _)
    have e := getD_armsOf_last tb.n (quotS (.cons x r)) (stackS st) 0
    rw [Nat.add_zero] at e
    rw [e] at hc
    refine (SSteps.single hc).trans ?_
    have h2 := (armCons_source.substC (σ := fill [quotS (.cons x r), stackS st, itemS x, quotS r])
      (fill_K _)).mono hK
    rw [Cl.substC_apps, arm_fill4] at h2
    exact h2.trans ih
  | @unit x st =>
    show SSteps P ((Cl.gref (nm! "applyU")).apps [quotS (.unit x), stackS st]) (outS (.val (x :: st)))
    refine (applyU_dispatch hJ _ _).trans ?_
    have hc := SStep.ctor (P := P) (fs := [itemS x])
      (ks := armsOf tb.n (quotS (.unit x)) (stackS st)) hJ.qunit (by omega) rfl (armsOf_length _ _ _)
    rw [getD_armsOf_last tb.n (quotS (.unit x)) (stackS st) 1] at hc
    refine (SSteps.single hc).trans ?_
    have h2 := (armUnit_source.substC (σ := fill [quotS (.unit x), stackS st, itemS x])
      (fill_K _)).mono hK
    rw [Cl.substC_apps, arm_fill3] at h2
    exact h2
  | @then_val b r t st' o _ _ ih1 ih2 =>
    show SSteps P ((Cl.gref (nm! "applyU")).apps [quotS (.then b), stackS (.quot r :: t)]) (outS o)
    refine (applyU_dispatch hJ _ _).trans ?_
    have hc := SStep.ctor (P := P) (fs := [quotS b])
      (ks := armsOf tb.n (quotS (.then b)) (stackS (.quot r :: t))) hJ.qthen (by omega) rfl
      (armsOf_length _ _ _)
    rw [getD_armsOf_last tb.n (quotS (.then b)) (stackS (.quot r :: t)) 2] at hc
    refine (SSteps.single hc).trans ?_
    have h2 := (armThen_source.substC (σ := fill [quotS (.then b), stackS (.quot r :: t), quotS b])
      (fill_K _)).mono hK
    rw [Cl.substC_apps, arm_fill3] at h2
    refine h2.trans ?_
    exact seq_source (k := fun _ => o) hK ((i_run_source hK _ r t).trans ih1)
      (fun _ e => by cases e; exact ih2)
  | @then_err b r t _ ih1 =>
    show SSteps P ((Cl.gref (nm! "applyU")).apps [quotS (.then b), stackS (.quot r :: t)])
      (outS .err)
    refine (applyU_dispatch hJ _ _).trans ?_
    have hc := SStep.ctor (P := P) (fs := [quotS b])
      (ks := armsOf tb.n (quotS (.then b)) (stackS (.quot r :: t))) hJ.qthen (by omega) rfl
      (armsOf_length _ _ _)
    rw [getD_armsOf_last tb.n (quotS (.then b)) (stackS (.quot r :: t)) 2] at hc
    refine (SSteps.single hc).trans ?_
    have h2 := (armThen_source.substC (σ := fill [quotS (.then b), stackS (.quot r :: t), quotS b])
      (fill_K _)).mono hK
    rw [Cl.substC_apps, arm_fill3] at h2
    refine h2.trans ?_
    exact seq_source (k := fun _ => Outcome.err) hK ((i_run_source hK _ r t).trans ih1)
      (fun _ e => by cases e)
  | @then_bad b st hb =>
    show SSteps P ((Cl.gref (nm! "applyU")).apps [quotS (.then b), stackS st]) (outS .err)
    refine (applyU_dispatch hJ _ _).trans ?_
    have hc := SStep.ctor (P := P) (fs := [quotS b])
      (ks := armsOf tb.n (quotS (.then b)) (stackS st)) hJ.qthen (by omega) rfl
      (armsOf_length _ _ _)
    rw [getD_armsOf_last tb.n (quotS (.then b)) (stackS st) 2] at hc
    refine (SSteps.single hc).trans ?_
    have h2 := (armThen_source.substC (σ := fill [quotS (.then b), stackS st, quotS b])
      (fill_K _)).mono hK
    rw [Cl.substC_apps, arm_fill3] at h2
    refine h2.trans ?_
    exact seq_source (k := fun _ => Outcome.err) hK (i_bad_source hK _ st hb) (fun _ e => by cases e)
  | nil st => exact idW_source hK st
  | @seq_val w p st st' o _ hp ihw ihp =>
    cases p with
    | nil =>
      cases hp
      exact ihw
    | cons w' p' =>
      exact seq_source (k := fun _ => o) hK ihw (fun _ e => by cases e; exact ihp)
  | @seq_err w p st _ ihw =>
    cases p with
    | nil => exact ihw
    | cons w' p' => exact seq_source (k := fun _ => Outcome.err) hK ihw (fun _ e => by cases e)
  | @plain w st hw => exact (plain_source _ w hw st).mono hK
  | @i_run r t o _ ih => exact (i_run_source hK _ r t).trans ih
  | i_bad hb => exact i_bad_source hK _ _ hb
  | @dip_run r b u o _ ih => exact dip_run_source hK _ r b u o ih
  | dip_bad hb => exact dip_bad_source hK _ _ hb
  | @ifz_zero sc z v o _ ih => exact (ifz_zero_source hK _ sc z v).trans ih
  | @ifz_succ sc z m v o _ ih => exact (ifz_succ_source hK _ sc z m v).trans ih
  | ifz_bad hb => exact ifz_bad_source hK _ _ hb
