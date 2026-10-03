import Ski.ZK.Fermat
import Ski.ZK.Poseidon2SKI

set_option linter.unusedSimpArgs false

/-!
# The Poseidon2 table, as data

One row per permutation.  The 650 columns are the sixteen inputs, then
for each round the values it commits; a last column holds the row's
multiplicity on the bus.
- The initial linear layer: the sixteen entries of the new state.
- A full round: sixteen cubes `x = a^3`, one for each entry's `a = s + c`;
  then the sixteen S-box outputs `y = x² a`; then the sixteen entries of
  the new state.
- A partial round: the first entry's cube and S-box output, then the
  sixteen entries of the new state.

Every constraint reads one row and has degree at most 3: `x - a^3`,
`y - x x a`, and for each entry of a new state, the entry minus a linear
form of the previous state's columns.  The linear forms are the
expressions of `Ski/ZK/Poseidon2SKI.lean`'s sublayers (`Ex`), read in the
field (`toE`), so the bridges proved there give the field values.  The
last state's columns are the outputs.  The table provides `(inputs,
outputs)` on the bus `p2`.

**`p2_sound`**: an assignment on which every constraint vanishes has, as
its outputs, `Poseidon2.permute` of its inputs; **`p2_sound_row`**: so
does every row of a table that satisfies the AIR.
-/

namespace P2Air

open Circuit Circuit.B Poseidon2SKI

-- ---------------------------------------------------------------------------
-- Expressions in the field
-- ---------------------------------------------------------------------------

/-- An expression's value in the field: `md` is the identity there, the
    S-box the seventh power. -/
def evalF (ρ : Nat → F) : Ex → F
  | .var i => ρ i
  | .lit n => ofN n
  | .add a b => evalF ρ a + evalF ρ b
  | .mul a b => evalF ρ a * evalF ρ b
  | .md a => evalF ρ a
  | .sbox a => fpow (evalF ρ a) 7

theorem p_eq : Poseidon2.p = Circuit.P := rfl

/-- **The field value is the value modulo `p`.** -/
theorem evalF_ofN (ρ : Nat → Nat) : ∀ e : Ex, evalF (fun i => ofN (ρ i)) e = ofN (e.eval ρ)
  | .var _ => rfl
  | .lit _ => rfl
  | .add a b => by
    show evalF _ a + evalF _ b = ofN (a.eval ρ + b.eval ρ)
    rw [evalF_ofN ρ a, evalF_ofN ρ b, ofN_add]
  | .mul a b => by
    show evalF _ a * evalF _ b = ofN (a.eval ρ * b.eval ρ)
    rw [evalF_ofN ρ a, evalF_ofN ρ b, ofN_mul]
  | .md a => by
    show evalF _ a = ofN (a.eval ρ % Poseidon2.p)
    rw [evalF_ofN ρ a, p_eq, ofN_mod]
  | .sbox a => by
    show fpow (evalF _ a) 7 = ofN (a.eval ρ ^ 7 % Poseidon2.p)
    rw [evalF_ofN ρ a, p_eq, ofN_mod, fpow_ofN]

/-- `a^n` as a product. -/
def epow (a : E) : Nat → E
  | 0 => .const 1
  | n + 1 => .mul (epow a n) a

theorem epow_eval (ρ : Atom → F) (a : E) : ∀ n, (epow a n).eval ρ = fpow (a.eval ρ) n
  | 0 => rfl
  | n + 1 => by
    show (epow a n).eval ρ * a.eval ρ = fpow (a.eval ρ) n * a.eval ρ
    rw [epow_eval ρ a n]

/-- An expression as a constraint expression, input `i` read as `env i`. -/
def toE (env : Nat → E) : Ex → E
  | .var i => env i
  | .lit n => .const (ofN n)
  | .add a b => .add (toE env a) (toE env b)
  | .mul a b => .mul (toE env a) (toE env b)
  | .md a => toE env a
  | .sbox a => epow (toE env a) 7

theorem toE_eval (ρ : Atom → F) (env : Nat → E) :
    ∀ e : Ex, (toE env e).eval ρ = evalF (fun i => (env i).eval ρ) e
  | .var _ => rfl
  | .lit _ => rfl
  | .add a b => by
    show (toE env a).eval ρ + (toE env b).eval ρ = _
    rw [toE_eval ρ env a, toE_eval ρ env b]; rfl
  | .mul a b => by
    show (toE env a).eval ρ * (toE env b).eval ρ = _
    rw [toE_eval ρ env a, toE_eval ρ env b]; rfl
  | .md a => toE_eval ρ env a
  | .sbox a => by
    show (epow (toE env a) 7).eval ρ = _
    rw [epow_eval, toE_eval ρ env a]; rfl

-- ---------------------------------------------------------------------------
-- The full round's linear layer as one list of expressions
-- ---------------------------------------------------------------------------

/-- Substitution: input `i` replaced by `es`'s `i`-th expression. -/
def exSubst (es : List Ex) : Ex → Ex
  | .var i => es.getD i (.lit 0)
  | .lit n => .lit n
  | .add a b => .add (exSubst es a) (exSubst es b)
  | .mul a b => .mul (exSubst es a) (exSubst es b)
  | .md a => .md (exSubst es a)
  | .sbox a => .sbox (exSubst es a)

theorem eval_subst (ρ : Nat → Nat) (es : List Ex) :
    ∀ e : Ex, (exSubst es e).eval ρ = e.eval (fun i => (es.getD i (.lit 0)).eval ρ)
  | .var _ => rfl
  | .lit _ => rfl
  | .add a b => by
    show (exSubst es a).eval ρ + (exSubst es b).eval ρ = _
    rw [eval_subst ρ es a, eval_subst ρ es b]; rfl
  | .mul a b => by
    show (exSubst es a).eval ρ * (exSubst es b).eval ρ = _
    rw [eval_subst ρ es a, eval_subst ρ es b]; rfl
  | .md a => by
    show (exSubst es a).eval ρ % Poseidon2.p = _
    rw [eval_subst ρ es a]; rfl
  | .sbox a => by
    show (exSubst es a).eval ρ ^ 7 % Poseidon2.p = _
    rw [eval_subst ρ es a]; rfl

/-- The external linear layer: `M₄` on each block, then the mixing. -/
def extLE : List Ex := mixLE.map (exSubst mat4LE)

theorem getD_map {α β : Type} (f : α → β) (d : α) : ∀ (l : List α) (i : Nat),
    (l.map f).getD i (f d) = f (l.getD i d)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_map f d l i

theorem bridge_ext (vs : List Nat) (hv : vs.length = 16) : extLE.map (Ex.eval (at16 vs)) = Poseidon2.extLinear vs := by
  have hm := bridge_mat4 vs hv
  have hl : (mat4L vs).length = 16 := by rw [← hm, List.length_map]; rfl
  have e : (fun i => (mat4LE.getD i (.lit 0)).eval (at16 vs)) = at16 (mat4L vs) := by
    funext i
    rw [← hm]
    exact (getD_map (Ex.eval (at16 vs)) (.lit 0) mat4LE i).symm
  show (mixLE.map (exSubst mat4LE)).map (Ex.eval (at16 vs)) = _
  rw [List.map_map]
  have e2 : (fun e : Ex => (exSubst mat4LE e).eval (at16 vs)) = Ex.eval (at16 (mat4L vs)) := by
    funext x
    rw [eval_subst, e]
  rw [show Ex.eval (at16 vs) ∘ exSubst mat4LE = Ex.eval (at16 (mat4L vs)) from e2, bridge_mix _ hl,
    extLinear_split]

-- ---------------------------------------------------------------------------
-- The table's constraints
-- ---------------------------------------------------------------------------

/-- A state's entry `i`, `0` past its end. -/
def stE (st : List E) : Nat → E := fun i => st.getD i (.const 0)

/-- Sixteen columns from `k`. -/
def colsFrom (k : Nat) : List E := (List.range 16).map fun i => col (k + i)

/-- A linear layer at column `k`: entry `i` of the new state minus its
    expression over the previous state. -/
def linCons (st : List E) (es : List Ex) (k : Nat) : List E :=
  (List.range 16).map fun i => .sub (col (k + i)) (toE (stE st) (es.getD i (.lit 0)))

/-- The S-box's input in a full round. -/
def sboxA (st : List E) (rc : List Nat) (i : Nat) : E := .add (stE st i) (.const (ofN (rc.getD i 0)))

/-- A full round's S-boxes at column `k`: cubes at `k`, outputs at `k + 16`. -/
def fullCons (st : List E) (rc : List Nat) (k : Nat) : List E :=
  (List.range 16).flatMap fun i =>
    [.sub (col (k + i)) (epow (sboxA st rc i) 3),
     .sub (col (k + 16 + i)) (.mul (.mul (col (k + i)) (col (k + i))) (sboxA st rc i))]

/-- A partial round's S-box at column `k`: the cube, then the output. -/
def partCons (st : List E) (c : Nat) (k : Nat) : List E :=
  [.sub (col k) (epow (.add (stE st 0) (.const (ofN c))) 3),
   .sub (col (k + 1)) (.mul (.mul (col k) (col k)) (.add (stE st 0) (.const (ofN c))))]

/-- The rounds, as the specification's. -/
inductive Round
  | l0
  | full (rc : List Nat)
  | part (c : Nat)

def Round.spec : Round → List Nat → List Nat
  | .l0 => Poseidon2.extLinear
  | .full rc => fun s => Poseidon2.extRound s rc
  | .part c => fun s => Poseidon2.intRound s c

/-- A round's constraints, its new state, and its next free column. -/
def Round.gen : Round → Nat → List E → List E × List E × Nat
  | .l0, k, st => (linCons st extLE k, colsFrom k, k + 16)
  | .full rc, k, st => (fullCons st rc k ++ linCons (colsFrom (k + 16)) extLE (k + 32), colsFrom (k + 32), k + 48)
  | .part c, k, st => (partCons st c k ++ linCons (col (k + 1) :: st.tail) intLinLE (k + 2), colsFrom (k + 2), k + 18)

def gen : List Round → Nat → List E → List E × List E
  | [], _, st => ([], st)
  | r :: rs, k, st =>
    let g := r.gen k st
    let rest := gen rs g.2.2 g.2.1
    (g.1 ++ rest.1, rest.2)

def rounds : List Round :=
  .l0 :: (Poseidon2.rcInitial.map .full ++ Poseidon2.rcInternal.map .part ++ Poseidon2.rcTerminal.map .full)

def p2Cons : List E := (gen rounds 16 (colsFrom 0)).1
def p2Out : List E := (gen rounds 16 (colsFrom 0)).2

/-- The committed columns: sixteen inputs, then the rounds' (`16 + 16 + 8·48 + 13·18`). -/
def COLS : Nat := 650
/-- The multiplicity of the row's message on `p2`. -/
def MULT : Nat := 650

/-- **The Poseidon2 table**: each row provides `(inputs, outputs)` on `p2`. -/
def p2Air : AirD := ⟨"p2", COLS + 1, 0, p2Cons, [⟨"p2", 0, .neg (col MULT), colsFrom 0 ++ p2Out⟩], []⟩

-- ---------------------------------------------------------------------------
-- Soundness
-- ---------------------------------------------------------------------------

/-- Every expression of the list vanishes. -/
def allZ (ρ : Atom → F) : List E → Prop
  | [] => True
  | e :: es => e.eval ρ = 0 ∧ allZ ρ es

theorem allZ_append (ρ : Atom → F) : ∀ (a b : List E), allZ ρ (a ++ b) → allZ ρ a ∧ allZ ρ b
  | [], _, h => ⟨trivial, h⟩
  | _ :: a, b, ⟨h, hs⟩ => let ⟨ha, hb⟩ := allZ_append ρ a b hs; ⟨⟨h, ha⟩, hb⟩

/-- The state's columns hold the values `vs`. -/
def Ev (ρ : Atom → F) (st : List E) (vs : List Nat) : Prop := st.map (E.eval ρ) = vs.map ofN

theorem Ev.get {ρ : Atom → F} : ∀ {st : List E} {vs : List Nat}, Ev ρ st vs →
    ∀ i, (stE st i).eval ρ = ofN (vs.getD i 0)
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, h, 0 => (List.cons.inj h).1
  | _ :: st, _ :: vs, h, i + 1 => Ev.get (st := st) (vs := vs) (List.cons.inj h).2 i
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h

theorem Ev.tail {ρ : Atom → F} {e : E} {st : List E} {v : Nat} {vs : List Nat} (h : Ev ρ (e :: st) (v :: vs)) :
    Ev ρ st vs := (List.cons.inj h).2

theorem lin_ev (ρ : Atom → F) (st : List E) (vs : List Nat) (es : List Ex) (k : Nat) (hst : Ev ρ st vs) :
    ∀ l : List Nat, allZ ρ (l.map fun i => .sub (col (k + i)) (toE (stE st) (es.getD i (.lit 0)))) →
      Ev ρ (l.map fun i => col (k + i)) (l.map fun i => (es.getD i (.lit 0)).eval (at16 vs))
  | [], _ => rfl
  | i :: l, ⟨h, hs⟩ => by
    have e : (col (k + i)).eval ρ = ofN ((es.getD i (.lit 0)).eval (at16 vs)) := by
      have h' := sub_eq_zero h
      rw [h', toE_eval]
      have : (fun j => (stE st j).eval ρ) = fun j => ofN (at16 vs j) := funext hst.get
      rw [this, evalF_ofN]
    show _ :: _ = _ :: _
    rw [e]
    exact congrArg _ (lin_ev ρ st vs es k hst l hs)

/-- A linear layer of sixteen expressions maps the values to the
    expressions' values. -/
theorem lin_ok (ρ : Atom → F) (st : List E) (vs : List Nat) (es : List Ex) (k : Nat) (hst : Ev ρ st vs)
    (hes : es.length = 16) (h : allZ ρ (linCons st es k)) : Ev ρ (colsFrom k) (es.map (Ex.eval (at16 vs))) := by
  have := lin_ev ρ st vs es k hst (List.range 16) h
  rw [← range16_map (.lit 0) es hes, List.map_map]
  exact this

theorem pow7 (n : Nat) : n ^ 3 * n ^ 3 * n = n ^ 7 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]

theorem sbox_ofN (n : Nat) (x : F) (hx : x = fpow (ofN n) 3) :
    x * x * ofN n = ofN (Poseidon2.sbox n) := by
  rw [hx, fpow_ofN, ← ofN_mul, ← ofN_mul, pow7]
  show ofN (n ^ 7) = ofN (n ^ 7 % Poseidon2.p)
  rw [p_eq, ofN_mod]

theorem full_ev (ρ : Atom → F) (st : List E) (vs rc : List Nat) (k : Nat) (hst : Ev ρ st vs) :
    ∀ l : List Nat, allZ ρ (l.flatMap fun i =>
        [.sub (col (k + i)) (epow (sboxA st rc i) 3),
         .sub (col (k + 16 + i)) (.mul (.mul (col (k + i)) (col (k + i))) (sboxA st rc i))]) →
      Ev ρ (l.map fun i => col (k + 16 + i)) (l.map fun i => Poseidon2.sbox (vs.getD i 0 + rc.getD i 0))
  | [], _ => rfl
  | i :: l, ⟨h1, h2, hs⟩ => by
    have ha : (sboxA st rc i).eval ρ = ofN (vs.getD i 0 + rc.getD i 0) := by
      show (stE st i).eval ρ + ofN (rc.getD i 0) = _
      rw [hst.get i, ofN_add]
    have hx : (col (k + i)).eval ρ = fpow (ofN (vs.getD i 0 + rc.getD i 0)) 3 := by
      rw [sub_eq_zero h1, epow_eval, ha]
    have hy : (col (k + 16 + i)).eval ρ = ofN (Poseidon2.sbox (vs.getD i 0 + rc.getD i 0)) := by
      rw [sub_eq_zero h2]
      show (col (k + i)).eval ρ * (col (k + i)).eval ρ * (sboxA st rc i).eval ρ = _
      rw [ha]
      exact sbox_ofN _ _ hx
    show _ :: _ = _ :: _
    rw [hy]
    exact congrArg _ (full_ev ρ st vs rc k hst l hs)

theorem sboxL_range (vs rc : List Nat) (hv : vs.length = 16) (hc : rc.length = 16) :
    (List.range 16).map (fun i => Poseidon2.sbox (vs.getD i 0 + rc.getD i 0)) = sboxL rc vs :=
  len16 (P := fun rc => (List.range 16).map (fun i => Poseidon2.sbox (vs.getD i 0 + rc.getD i 0)) = sboxL rc vs)
    (fun c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 =>
      len16 (P := fun vs => (List.range 16).map (fun i => Poseidon2.sbox (vs.getD i 0 + [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15].getD i 0)) =
          sboxL [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] vs)
        (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) vs hv) rc hc

/-- **A round computes its specification**: from a state of sixteen
    values, the new state holds the round's values. -/
theorem round_ok (ρ : Atom → F) (r : Round) (hr : ∀ rc, r = .full rc → rc.length = 16)
    (k : Nat) (st : List E) (vs : List Nat) (hst : Ev ρ st vs) (hv : vs.length = 16)
    (h : allZ ρ (r.gen k st).1) : Ev ρ (r.gen k st).2.1 (r.spec vs) ∧ (r.spec vs).length = 16 := by
  cases r with
  | l0 =>
    have e := bridge_ext vs hv
    have := lin_ok ρ st vs extLE k hst rfl h
    rw [e] at this
    refine ⟨this, ?_⟩
    show (Poseidon2.extLinear vs).length = 16
    rw [← e, List.length_map]; rfl
  | full rc =>
    have hc := hr rc rfl
    obtain ⟨h1, h2⟩ := allZ_append ρ _ _ h
    have hs := full_ev ρ st vs rc k hst (List.range 16) h1
    rw [sboxL_range vs rc hv hc] at hs
    have hsl : (sboxL rc vs).length = 16 := by rw [← sboxL_range vs rc hv hc, List.length_map, List.length_range]
    have e := bridge_ext (sboxL rc vs) hsl
    have hcols : Ev ρ (colsFrom (k + 16)) (sboxL rc vs) := hs
    have := lin_ok ρ _ _ extLE (k + 32) hcols rfl h2
    rw [e] at this
    refine ⟨this, ?_⟩
    show (Poseidon2.extRound vs rc).length = 16
    rw [extRound_split, ← extLinear_split, ← e, List.length_map]; rfl
  | part c =>
    obtain ⟨h1, h2⟩ := allZ_append ρ _ _ h
    match st, vs, hst, hv with
    | e0 :: st', v0 :: vs', hst, hv =>
      obtain ⟨hx, hy, _⟩ := h1
      have ha : (E.add (stE (e0 :: st') 0) (.const (ofN c))).eval ρ = ofN (v0 + c) := by
        show (stE (e0 :: st') 0).eval ρ + ofN c = _
        rw [hst.get 0, ofN_add]; rfl
      have hx' : (col k).eval ρ = fpow (ofN (v0 + c)) 3 := by rw [sub_eq_zero hx, epow_eval, ha]
      have hy' : (col (k + 1)).eval ρ = ofN (Poseidon2.sbox (v0 + c)) := by
        rw [sub_eq_zero hy]
        show (col k).eval ρ * (col k).eval ρ * _ = _
        rw [ha]; exact sbox_ofN _ _ hx'
      have hnew : Ev ρ (col (k + 1) :: st') (sbox0L c (v0 :: vs')) := by
        show _ :: _ = _ :: _
        rw [hy']
        exact congrArg _ hst.tail
      have hl : (sbox0L c (v0 :: vs')).length = 16 := hv
      have e := bridge_intLin _ hl
      have := lin_ok ρ _ _ intLinLE (k + 2) hnew rfl h2
      rw [e] at this
      refine ⟨?_, ?_⟩
      · show Ev ρ (colsFrom (k + 2)) (Poseidon2.intRound (v0 :: vs') c)
        rw [intRound_split]; exact this
      · show (Poseidon2.intRound (v0 :: vs') c).length = 16
        rw [intRound_split, ← e, List.length_map]; rfl
    | [], _ :: _, hst, _ => nomatch hst
    | _, [], _, hv => nomatch hv

/-- Every full round's constants number sixteen. -/
def RcOK : List Round → Prop
  | [] => True
  | r :: rs => (∀ rc, r = .full rc → rc.length = 16) ∧ RcOK rs

theorem gen_ok (ρ : Atom → F) : ∀ (rs : List Round), RcOK rs → ∀ (k : Nat) (st : List E) (vs : List Nat),
    Ev ρ st vs → vs.length = 16 → allZ ρ (gen rs k st).1 →
      Ev ρ (gen rs k st).2 (rs.foldl (fun v r => r.spec v) vs)
  | [], _, _, _, _, hst, _, _ => hst
  | r :: rs, ⟨hr, hrs⟩, k, st, vs, hst, hv, h => by
    obtain ⟨h1, h2⟩ := allZ_append ρ _ _ h
    obtain ⟨hst', hv'⟩ := round_ok ρ r hr k st vs hst hv h1
    exact gen_ok ρ rs hrs _ _ _ hst' hv' h2

theorem rcOK_full : ∀ l : List (List Nat), l.all (fun rc => decide (rc.length = 16)) = true → RcOK (l.map .full)
  | [], _ => trivial
  | rc :: l, h => by
    show RcOK (Round.full rc :: l.map .full)
    exact And.intro (fun _ e => by cases e; exact of_decide_eq_true (band_l h)) (rcOK_full l (band_r h))

theorem rcOK_part : ∀ l : List Nat, RcOK (l.map .part)
  | [] => trivial
  | c :: l => by
    show RcOK (Round.part c :: l.map .part)
    exact And.intro (fun _ e => nomatch e) (rcOK_part l)

theorem rcOK_append : ∀ (a b : List Round), RcOK a → RcOK b → RcOK (a ++ b)
  | [], _, _, hb => hb
  | _ :: a, b, ⟨h, ha⟩, hb => ⟨h, rcOK_append a b ha hb⟩

theorem rounds_rcOK : RcOK rounds := by
  show RcOK (Round.l0 :: (Poseidon2.rcInitial.map .full ++ Poseidon2.rcInternal.map .part ++
    Poseidon2.rcTerminal.map .full))
  exact And.intro (fun _ e => nomatch e) (rcOK_append _ _ (rcOK_append _ _ (rcOK_full Poseidon2.rcInitial (by decide))
    (rcOK_part _)) (rcOK_full Poseidon2.rcTerminal (by decide)))

theorem rounds_spec (s : List Nat) : rounds.foldl (fun v r => r.spec v) s = Poseidon2.permute s := by
  simp only [rounds, List.foldl_cons, List.foldl_append, List.foldl_map]
  rfl

/-- The row's inputs. -/
def ins (ρ : Atom → F) : List F := (List.range 16).map fun i => ρ (.main 0 i)

/-- **A row computes Poseidon2**: when every constraint vanishes, the
    output columns hold the permutation of the input columns. -/
theorem p2_sound (ρ : Atom → F) (h : allZ ρ p2Cons) :
    p2Out.map (E.eval ρ) = (Poseidon2.permute ((ins ρ).map Fin.val)).map ofN := by
  have hst : Ev ρ (colsFrom 0) ((ins ρ).map Fin.val) := by
    show ((List.range 16).map fun i => col (0 + i)).map (E.eval ρ) = _
    rw [List.map_map, ins, List.map_map, List.map_map]
    exact List.map_congr_left fun i _ => by
      show ρ (.main 0 (0 + i)) = ofN (ρ (.main 0 i)).val
      rw [Nat.zero_add, ofN_val]
  have := gen_ok ρ rounds rounds_rcOK 16 (colsFrom 0) _ hst (by rw [ins, List.length_map, List.length_map, List.length_range]) h
  rw [rounds_spec] at this
  exact this

theorem allZ_of_mem (ρ : Atom → F) : ∀ l : List E, (∀ e ∈ l, e.eval ρ = 0) → allZ ρ l
  | [], _ => trivial
  | e :: l, h => ⟨h e (List.mem_cons_self ..), allZ_of_mem ρ l fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

/-- **Every row of a table that satisfies the AIR computes Poseidon2.** -/
theorem p2_sound_row (T : Table) (hT : Sat p2Air T) (r : Nat) (hr : r < T.h) :
    p2Out.map (E.eval (T.env r)) = (Poseidon2.permute ((ins (T.env r)).map Fin.val)).map ofN :=
  p2_sound (T.env r) (allZ_of_mem _ _ fun e he => hT.2 e he r hr)

-- ---------------------------------------------------------------------------
-- Residues
-- ---------------------------------------------------------------------------

theorem ofN_eq_mod {a b : Nat} (h : ofN a = ofN b) : a % Poseidon2.p = b % Poseidon2.p := by
  have := congrArg Fin.val h
  exact this

/-- An expression reduced at its root depends only on its inputs' residues. -/
theorem eval_md_mod (ρ ρ' : Nat → Nat) (hρ : ∀ i, ofN (ρ i) = ofN (ρ' i)) (e : Ex) :
    (Ex.md e).eval ρ = (Ex.md e).eval ρ' := by
  show e.eval ρ % Poseidon2.p = e.eval ρ' % Poseidon2.p
  apply ofN_eq_mod
  rw [← evalF_ofN, ← evalF_ofN]
  exact congrArg (evalF · e) (funext hρ)

theorem extLE_md : ∀ e ∈ extLE, ∃ e', e = .md e' := by
  intro e he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hm
  exact ⟨_, rfl⟩

/-- **The permutation depends only on its inputs' residues.** -/
theorem permute_mod (s : List Nat) (hs : s.length = 16) :
    Poseidon2.permute s = Poseidon2.permute (s.map (· % Poseidon2.p)) := by
  have hs' : (s.map (· % Poseidon2.p)).length = 16 := by rw [List.length_map, hs]
  have e : Poseidon2.extLinear s = Poseidon2.extLinear (s.map (· % Poseidon2.p)) := by
    rw [← bridge_ext s hs, ← bridge_ext _ hs']
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨e', rfl⟩ := extLE_md x hx
    refine eval_md_mod _ _ (fun i => ?_) e'
    show ofN (s.getD i 0) = ofN ((s.map (· % Poseidon2.p)).getD i 0)
    have := getD_map (· % Poseidon2.p) 0 s i
    rw [show (0 : Nat) % Poseidon2.p = 0 from rfl] at this
    rw [this]
    show ofN (s.getD i 0) = ofN (s.getD i 0 % Circuit.P)
    rw [ofN_mod]
  show (Poseidon2.rcTerminal.foldl Poseidon2.extRound
    (Poseidon2.rcInternal.foldl Poseidon2.intRound
      (Poseidon2.rcInitial.foldl Poseidon2.extRound (Poseidon2.extLinear s)))) =
    (Poseidon2.rcTerminal.foldl Poseidon2.extRound
    (Poseidon2.rcInternal.foldl Poseidon2.intRound
      (Poseidon2.rcInitial.foldl Poseidon2.extRound (Poseidon2.extLinear (s.map (· % Poseidon2.p))))))
  rw [e]

theorem foldl_ext_last : ∀ (rcs : List (List Nat)), rcs ≠ [] →
    rcs.all (fun rc => decide (rc.length = 16)) = true → ∀ X : List Nat, X.length = 16 →
      ∃ Y, Y.length = 16 ∧ rcs.foldl Poseidon2.extRound X = Poseidon2.extLinear Y
  | [], h, _, _, _ => absurd rfl h
  | [rc], _, hc, X, hX => by
    refine ⟨sboxL rc X, sboxL_len rc X hX (of_decide_eq_true (band_l hc)), ?_⟩
    rw [List.foldl_cons, List.foldl_nil, extRound_split, extLinear_split]
  | rc :: rc' :: rest, _, hc, X, hX => by
    have hX' : (Poseidon2.extRound X rc).length = 16 := by
      rw [extRound_split]
      exact mixL_len _ (mat4L_len _ (sboxL_len rc X hX (of_decide_eq_true (band_l hc))))
    rw [List.foldl_cons]
    exact foldl_ext_last (rc' :: rest) (List.cons_ne_nil _ _) (band_r hc) _ hX'

/-- **The permutation's outputs are reduced.** -/
theorem permute_lt (s : List Nat) (hs : s.length = 16) : ∀ y ∈ Poseidon2.permute s, y < Poseidon2.p := by
  have hin : (Poseidon2.rcInternal.foldl Poseidon2.intRound
      (Poseidon2.rcInitial.foldl Poseidon2.extRound (Poseidon2.extLinear s))).length = 16 :=
    foldl_int_len _ _ (foldl_ext_len _ (by decide) _ (by rw [extLinear_split]; exact mixL_len _ (mat4L_len _ hs)))
  obtain ⟨Y, hY, e⟩ := foldl_ext_last Poseidon2.rcTerminal (by decide) (by decide) _ hin
  intro y hy
  have hy' : y ∈ Poseidon2.extLinear Y := by
    have : Poseidon2.permute s = Poseidon2.rcTerminal.foldl Poseidon2.extRound
        (Poseidon2.rcInternal.foldl Poseidon2.intRound
          (Poseidon2.rcInitial.foldl Poseidon2.extRound (Poseidon2.extLinear s))) := rfl
    rw [this, e] at hy; exact hy
  rw [← bridge_ext Y hY] at hy'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy'
  obtain ⟨e', rfl⟩ := extLE_md x hx
  exact Nat.mod_lt _ (by decide)

end P2Air
