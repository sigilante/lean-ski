import Ski.AirCheck
import Ski.AirOpen
import Ski.Inst
import Ski.SmallLemma

open Term

/-!
# The AIR with instantiation rows

The circuit of `bench/plonky3/DESIGN.md` §2, as constraints: besides the
machine's transitions, a row may **instantiate** a supercombinator at a
listed root, popping its arguments and writing its body's cells, as
`Mach.instStepG` does.

**The public data.**
- *Jets*: each a template `absN xs body` with the public address of each
  global, a variable of the body outside the formals (`Jet`).  A global is
  how a body names a closed subterm without writing it, so a nested
  template's root stays a root.
- *Roots*: pairs `(a, g)`, an address in the loaded heap and a jet.
  `RootsOK` asks that the term at `a` be jet `g`'s compiled form, with each
  global read at its address; `rootsOKB` checks it (`rootsOKB_sound`).

**The row.**  `instRow` reads the head's argument cells below the counter
(`popR`, which is `popN` over reads), computes the body's cells from the
counter on (`icells`, which is what `ibuild` writes), and checks the writes
(`wrs`).  An instantiation row that passes is a jetted step
(`instRow_jstep`), given `RootsOK` on the memory table's loaded prefix.

**The theorems.**
- `air_sound_jet`: a table the AIR with instantiation rows accepts, from a
  loaded term whose roots are licensed, ends on a value that the term
  evaluates to in normal order, up to weak reduction of the value, with the
  same head combinator and arity (`jet_run_eval`, `jet_run_shape`).
- `checkJA_sound`: `checkJA` decides these constraints' soundness side on
  a concrete table, over an array: what `lake exe jets check` runs on the
  Plonky3 prover's jetted tables.

Instantiation is not tied to a halt: at a root the prover may unwind as
usual or instantiate, and both are sound.
-/

namespace Air

open Mach

/-- **A jet**: formals, a body, and the public address of each global, a
    body variable outside the formals. -/
structure Jet where
  xs : List Nat
  body : OTerm
  glob : List (Nat × Nat)
  deriving Repr

/-- Where a global points; `0` for a variable with no entry, which
    `RootsOK` rules out for every variable the body uses. -/
def Jet.genv (J : Jet) (x : Nat) : Nat := (J.glob.lookup x).getD 0

-- ---------------------------------------------------------------------------
-- The row, over a reader
-- ---------------------------------------------------------------------------

/-- `popN` through reads below the counter `c`. -/
def popR (g : Nat → Option Cell) (c : Nat) : Nat → Nat → Option (List Nat × Nat)
  | 0, s => some ([], s)
  | k + 1, s =>
    match rdG g c s with
    | some (.cons x r) => (popR g c k r).map fun p => (x :: p.1, p.2)
    | _ => none

/-- The cells `ibuild` writes from address `c`, and the root. -/
def icells (env : Nat → Nat) (c : Nat) : OTerm → List Cell × Nat
  | .S => ([.S], c)
  | .K => ([.K], c)
  | .I => ([.I], c)
  | .var x => ([], env x)
  | .app f a =>
    let (cf, pf) := icells env c f
    let (ca, pa) := icells env (c + cf.length) a
    (cf ++ ca ++ [.app pf pa], c + cf.length + ca.length)

/-- **The instantiation constraint** of one row, for jet `J`: the head's
    arguments popped by reads, the body's cells written at the counter.
    The next row is the body's root, the rest of the stack, and the counter
    past the writes. -/
def instRowG (g : Nat → Option Cell) (J : Jet) (r : Row) : Option Row :=
  match popR g r.ctr J.xs.length r.stk with
  | some (ps, rest) =>
    let (cs, root) := icells (overrideN J.genv J.xs ps) r.ctr J.body
    if wrsG g r.ctr cs then some ⟨root, rest, r.ctr + cs.length⟩ else none
  | none => none

/-- The same, over the memory table. -/
def instRow (M : List Cell) (J : Jet) (r : Row) : Option Row := instRowG (fun a => M[a]?) J r

-- ---------------------------------------------------------------------------
-- Licensed roots
-- ---------------------------------------------------------------------------

/-- **Licensed roots** over a loaded heap `h0`: each listed root holds its
    jet's compiled form, with each global the body uses read at its
    address. -/
def RootsOK (h0 : List Cell) (roots : List (Nat × Nat)) (jets : List Jet) : Prop :=
  ∀ a g, (a, g) ∈ roots → ∃ J, jets[g]? = some J ∧ ∃ γ : Nat → Term,
    termAt h0 (h0.length + 1) a = some ((absN J.xs J.body).close γ) ∧
    ∀ x, Occ x J.body → x ∉ J.xs → termAt h0 (h0.length + 1) (J.genv x) = some (γ x)

/-- `termAt` over a reader. -/
def termAtG (g : Nat → Option Cell) : Nat → Nat → Option Term
  | 0, _ => none
  | f + 1, a =>
    match g a with
    | some .S => some .S
    | some .K => some .K
    | some .I => some .I
    | some (.app u x) =>
      match termAtG g f u, termAtG g f x with
      | some tu, some tx => some (tu ⬝ tx)
      | _, _ => none
    | _ => none

theorem termAt_G (heap : List Cell) : ∀ f a, termAt heap f a = termAtG (fun a => heap[a]?) f a
  | 0, _ => rfl
  | f + 1, a => by
    unfold termAt termAtG
    cases heap[a]? with
    | none => rfl
    | some c =>
      cases c with
      | app u x =>
        dsimp only
        rw [termAt_G heap f u, termAt_G heap f x]
        cases termAtG (fun a => heap[a]?) f u <;> cases termAtG (fun a => heap[a]?) f x <;> rfl
      | _ => rfl

/-- The meanings of a jet's globals, read through `g` with fuel `F`. -/
def globMeaning (g : Nat → Option Cell) (F : Nat) (J : Jet) (x : Nat) : Term :=
  (termAtG g F (J.genv x)).getD K

/-- One root, checked, through a reader with fuel `F`. -/
def rootOKB (g : Nat → Option Cell) (F : Nat) (jets : List Jet) (a j : Nat) : Bool :=
  match jets[j]? with
  | some J =>
    (J.body.vars.all fun x => J.xs.contains x || (termAtG g F (J.genv x)).isSome) &&
      termAtG g F a == some ((absNF J.xs J.body).close (globMeaning g F J))
  | none => false

/-- **Licensed roots, decided**, over an array copy of the loaded heap. -/
def rootsOKB (h0 : List Cell) (roots : List (Nat × Nat)) (jets : List Jet) : Bool :=
  let A := h0.toArray
  roots.all fun (a, j) => rootOKB (fun i => A[i]?) (h0.length + 1) jets a j

theorem rootsOKB_sound {h0 : List Cell} {roots : List (Nat × Nat)} {jets : List Jet}
    (h : rootsOKB h0 roots jets = true) : RootsOK h0 roots jets := by
  intro a g hm
  have hA : (fun (i : Nat) => h0.toArray[i]?) = (fun (i : Nat) => h0[i]?) := by
    funext i; simp
  have h1 : rootOKB (fun i => h0.toArray[i]?) (h0.length + 1) jets a g = true :=
    List.all_eq_true.1 h (a, g) hm
  rw [hA] at h1
  unfold rootOKB at h1
  cases hj : jets[g]? with
  | none => rw [hj] at h1; cases h1
  | some J =>
    rw [hj] at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨hv, ht⟩ := h1
    refine ⟨J, rfl, globMeaning (fun i => h0[i]?) (h0.length + 1) J,
      by rw [termAt_G, ht, absNF_eq], fun x hx hn => ?_⟩
    have hx' : x ∈ J.body.vars := (OTerm.mem_vars x J.body).1 (OTerm.mem_of_occ hx)
    have := List.all_eq_true.1 hv x hx'
    rw [Bool.or_eq_true] at this
    rcases this with hc | hs
    · exact absurd (List.contains_iff_mem.1 hc) hn
    · rw [termAt_G]
      unfold globMeaning
      cases hq : termAtG (fun i => h0[i]?) (h0.length + 1) (J.genv x) with
      | none => rw [hq] at hs; cases hs
      | some u => rfl

-- ---------------------------------------------------------------------------
-- An instantiation row is a jetted step
-- ---------------------------------------------------------------------------

theorem popR_popN {M : List Cell} {c : Nat} : ∀ (k s : Nat),
    popR (fun a => M[a]?) c k s = popN (M.take c) k s
  | 0, _ => rfl
  | k + 1, s => by
    unfold popR popN
    rw [← rd_G, rd_eq]
    cases (M.take c)[s]? with
    | none => rfl
    | some x =>
      cases x with
      | cons x r => dsimp only; rw [popR_popN k r]
      | _ => rfl

theorem ibuild_icells (env : Nat → Nat) : ∀ (t : OTerm) (h : List Cell),
    ibuild env h t = (h ++ (icells env h.length t).1, (icells env h.length t).2)
  | .S, h => by simp [ibuild, icells, alloc]
  | .K, h => by simp [ibuild, icells, alloc]
  | .I, h => by simp [ibuild, icells, alloc]
  | .var x, h => by simp [ibuild, icells]
  | .app f a, h => by
    have ef := ibuild_icells env f h
    have ea := ibuild_icells env a (h ++ (icells env h.length f).1)
    show (let (h1, pf) := ibuild env h f
      let (h2, pa) := ibuild env h1 a
      alloc h2 (.app pf pa)) = _
    rw [ef]
    dsimp only
    rw [ea]
    simp [icells, alloc, List.append_assoc, Nat.add_assoc]

/-- The loaded prefix grows: a term read from `M.take c0` reads the same
    from `M.take c` for `c0 ≤ c ≤ |M|`. -/
theorem termAt_take {M : List Cell} {c0 c : Nat} {a : Nat} {u : Term} (hc0 : c0 ≤ c)
    (hc : c ≤ M.length) (h : termAt (M.take c0) ((M.take c0).length + 1) a = some u) :
    termAt (M.take c) ((M.take c).length + 1) a = some u := by
  have e : M.take c = M.take c0 ++ (M.take c).drop c0 := by
    have ht : (M.take c).take c0 = M.take c0 := by rw [List.take_take, Nat.min_eq_left hc0]
    calc M.take c = (M.take c).take c0 ++ (M.take c).drop c0 := (List.take_append_drop _ _).symm
      _ = _ := by rw [ht]
  rw [e]
  refine termAt_grow h ?_
  rw [← e, take_length hc, take_length (Nat.le_trans hc0 hc)]
  omega

/-- **An instantiation row that passes is a jetted step**, given licensed
    roots over the memory table's prefix below `c0`. -/
theorem instRow_jstep {M : List Cell} {roots : List (Nat × Nat)} {jets : List Jet} {c0 : Nat}
    (hroots : RootsOK (M.take c0) roots jets) {r r' : Row} {g : Nat} {J : Jet}
    (hc0 : c0 ≤ r.ctr) (hc : r.ctr ≤ M.length) (hm : (r.hd, g) ∈ roots) (hJ : jets[g]? = some J)
    (h : instRow M J r = some r') : JStep (st M r) (st M r') ∧ r'.ctr ≤ M.length := by
  obtain ⟨J', hJ', γ, hhd, hglob⟩ := hroots r.hd g hm
  rw [hJ] at hJ'
  cases hJ'
  unfold instRow instRowG at h
  cases hp : popR (fun a => M[a]?) r.ctr J.xs.length r.stk with
  | none => rw [hp] at h; cases h
  | some q =>
    obtain ⟨ps, rest⟩ := q
    rw [hp] at h
    dsimp only at h
    cases hw : wrsG (fun a => M[a]?) r.ctr (icells (overrideN J.genv J.xs ps) r.ctr J.body).1 with
    | false => rw [hw] at h; cases h
    | true =>
      rw [hw, if_pos rfl] at h
      cases h
      rw [← wrs_G] at hw
      have ht := take_of_wrs hw
      have hlen := congrArg List.length ht
      rw [List.length_take, List.length_append, take_length hc] at hlen
      refine ⟨?_, by show r.ctr + _ ≤ M.length; omega⟩
      refine JStep.inst J.xs J.body J.genv γ (fun x hx hn => termAt_take hc0 hc (hglob x hx hn))
        (termAt_take hc0 hc hhd) ?_
      unfold instStepG
      rw [show (st M r).heap = M.take r.ctr from rfl, show (st M r).stk = r.stk from rfl,
        ← popR_popN, hp]
      dsimp only
      rw [ibuild_icells, take_length hc, ← ht]
      rfl

-- ---------------------------------------------------------------------------
-- The AIR with instantiation rows
-- ---------------------------------------------------------------------------

/-- **The AIR with instantiation rows accepts** a table of `k` rows over
    `M`, from the machine state `m0`, with the public roots and jets: each
    row steps, instantiates a jet at a listed root, or has halted and
    repeats. -/
structure AcceptsJ (M : List Cell) (m0 : Mach) (roots : List (Nat × Nat)) (jets : List Jet)
    (k : Nat) (row : Nat → Row) : Prop where
  pos : 0 < k
  heap0 : M.take (row 0).ctr = m0.heap
  hd0 : (row 0).hd = m0.hd
  stk0 : (row 0).stk = m0.stk
  ctr0 : (row 0).ctr = m0.heap.length
  trans : ∀ i, i + 1 < k →
    stepRow M (row i) = some (row (i + 1)) ∨
    (∃ g J, ((row i).hd, g) ∈ roots ∧ jets[g]? = some J ∧ instRow M J (row i) = some (row (i + 1))) ∨
    (haltRow M (row i) = true ∧ row (i + 1) = row i)
  final : haltRow M (row (k - 1)) = true

theorem _root_.Mach.JSteps.snoc {m m1 m2 : Mach} (h : JSteps m m1) (hs : JStep m1 m2) :
    JSteps m m2 := by
  induction h with
  | refl _ => exact .step hs (.refl _)
  | step h1 _ ih => exact .step h1 (ih hs)

/-- Every accepted row is reached by a jetted run, within the table. -/
theorem AcceptsJ.reach {M : List Cell} {m0 : Mach} {roots : List (Nat × Nat)} {jets : List Jet}
    {k : Nat} {row : Nat → Row} (h : AcceptsJ M m0 roots jets k row)
    (hroots : RootsOK m0.heap roots jets) :
    ∀ i, i < k → (row 0).ctr ≤ (row i).ctr ∧ (row i).ctr ≤ M.length ∧ JSteps m0 (st M (row i)) := by
  have hr0 : RootsOK (M.take (row 0).ctr) roots jets := by rw [h.heap0]; exact hroots
  intro i
  induction i with
  | zero =>
    intro _
    have hst : st M (row 0) = m0 := by unfold st; rw [h.heap0, h.hd0, h.stk0]
    refine ⟨Nat.le_refl _, ?_, by rw [hst]; exact .refl _⟩
    have := congrArg List.length h.heap0
    rw [List.length_take, ← h.ctr0] at this
    omega
  | succ i ih =>
    intro hi
    obtain ⟨hc0, hc, hr⟩ := ih (by omega)
    rcases h.trans i hi with hs | ⟨g, J, hm, hJ, hI⟩ | hh
    · obtain ⟨hm, hc'⟩ := stepRow_mstep hc hs
      have : (row i).ctr ≤ (row (i + 1)).ctr := by
        unfold stepRow at hs
        cases hg : stepG (rd M (row i).ctr) (row i).ctr (row i).hd (row i).stk with
        | none => rw [hg] at hs; cases hs
        | some p =>
          obtain ⟨_, _, ws⟩ := p
          rw [hg] at hs
          dsimp only at hs
          cases hw : wrs M (row i).ctr ws with
          | false => rw [hw] at hs; cases hs
          | true =>
            rw [hw, if_pos rfl] at hs
            rw [← Option.some.inj hs]
            show _ ≤ _ + _
            omega
      exact ⟨by omega, hc', hr.snoc (.mach hm)⟩
    · obtain ⟨hj, hc'⟩ := instRow_jstep hr0 hc0 hc hm hJ hI
      have : (row i).ctr ≤ (row (i + 1)).ctr := by
        unfold instRow instRowG at hI
        cases hp : popR (fun a => M[a]?) (row i).ctr J.xs.length (row i).stk with
        | none => rw [hp] at hI; cases hI
        | some q =>
          rw [hp] at hI
          dsimp only at hI
          split at hI
          · rw [← Option.some.inj hI]
            show _ ≤ _ + _
            omega
          · cases hI
      exact ⟨by omega, hc', hr.snoc hj⟩
    · rw [hh.2]
      exact ⟨hc0, hc, hr⟩

/-- **Soundness of the AIR with instantiation rows.**  A table it accepts
    from a loaded term whose roots are licensed ends on a value `v` such
    that the term evaluates in normal order to a value that weakly reduces
    to `v`, with `v`'s head combinator and arity. -/
theorem air_sound_jet {M : List Cell} {t : Term} {roots : List (Nat × Nat)} {jets : List Jet}
    {k : Nat} {row : Nat → Row} (h : AcceptsJ M (load t) roots jets k row)
    (hroots : RootsOK (load t).heap roots jets) :
    ∃ v, decode (st M (row (k - 1))) = some v ∧ Whnf v ∧
      (∃ v', Eval t v' ∧ WSteps v' v) ∧ (∃ v', Eval t v' ∧ chead v' = chead v) := by
  obtain ⟨_, _, hr⟩ := h.reach hroots (k - 1) (by have := h.pos; omega)
  obtain ⟨v, hv, _⟩ := jsteps_wsteps (decode_load t) hr
  have hw : Whnf v := whnf_iff_step?_none.2 (mstep_none hv (haltRow_mstep h.final))
  exact ⟨v, hv, hw, jet_run_eval hr hv hw, jet_run_shape hr hv hw⟩

-- ---------------------------------------------------------------------------
-- The checker, over an array
-- ---------------------------------------------------------------------------

/-- Each row steps, instantiates at a listed root, or has halted and
    repeats, over a reader. -/
def chainJ (g : Nat → Option Cell) (roots : List (Nat × Nat)) (jets : List Jet) : List Row → Bool
  | r :: r' :: rest =>
    (decide (stepRowG g r = some r') ||
      roots.any (fun (a, j) => a == r.hd &&
        match jets[j]? with
        | some J => decide (instRowG g J r = some r')
        | none => false) ||
      (haltRowG g r && decide (r' = r))) && chainJ g roots jets (r' :: rest)
  | _ => true

/-- **The AIR with instantiation rows, checked** on a table over an array,
    from the state `m0`, with its roots licensed over `m0`'s heap. -/
def checkJA (A : Array Cell) (m0 : Mach) (roots : List (Nat × Nat)) (jets : List Jet) :
    List Row → Bool
  | [] => false
  | r0 :: rest =>
    rootsOKB m0.heap roots jets &&
      decide (A.toList.take r0.ctr = m0.heap) && decide (r0.hd = m0.hd) &&
      decide (r0.stk = m0.stk) && decide (r0.ctr = m0.heap.length) &&
      chainJ (fun a => A[a]?) roots jets (r0 :: rest) &&
      haltRowG (fun a => A[a]?) ((r0 :: rest).getLast (List.cons_ne_nil _ _))

theorem chainJ_trans {M : List Cell} {roots : List (Nat × Nat)} {jets : List Jet} :
    ∀ {rows : List Row}, chainJ (fun a => M[a]?) roots jets rows = true →
    ∀ i, i + 1 < rows.length →
      stepRow M (rowFn rows i) = some (rowFn rows (i + 1)) ∨
      (∃ g J, ((rowFn rows i).hd, g) ∈ roots ∧ jets[g]? = some J ∧
        instRow M J (rowFn rows i) = some (rowFn rows (i + 1))) ∨
      (haltRow M (rowFn rows i) = true ∧ rowFn rows (i + 1) = rowFn rows i)
  | [], _, i, hi => absurd hi (by simp)
  | [_], _, i, hi => absurd hi (by simp)
  | r :: r' :: rest, h, i, hi => by
    unfold chainJ at h
    rw [Bool.and_eq_true] at h
    cases i with
    | zero =>
      show stepRow M r = some r' ∨ (∃ g J, (r.hd, g) ∈ roots ∧ jets[g]? = some J ∧
        instRow M J r = some r') ∨ (haltRow M r = true ∧ r' = r)
      rw [Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_iff] at h
      rcases h.1 with (hs | ha) | hh
      · left; rw [stepRow_G]; exact hs
      · right; left
        obtain ⟨⟨a, j⟩, hm, hj⟩ := List.any_eq_true.1 ha
        rw [Bool.and_eq_true, beq_iff_eq] at hj
        obtain ⟨ha', hJ⟩ := hj
        cases hjj : jets[j]? with
        | none => rw [hjj] at hJ; cases hJ
        | some J =>
          rw [hjj, decide_eq_true_iff] at hJ
          subst ha'
          exact ⟨j, J, hm, hjj, hJ⟩
      · right; right
        rw [Bool.and_eq_true, decide_eq_true_iff] at hh
        exact ⟨by rw [haltRow_G]; exact hh.1, hh.2⟩
    | succ i => exact chainJ_trans h.2 i (by simp at hi ⊢; omega)

/-- **`checkJA` is sound**: a table it accepts, the AIR with instantiation
    rows accepts, with licensed roots. -/
theorem checkJA_sound {A : Array Cell} {m0 : Mach} {roots : List (Nat × Nat)} {jets : List Jet}
    {rows : List Row} (h : checkJA A m0 roots jets rows = true) :
    RootsOK m0.heap roots jets ∧ AcceptsJ A.toList m0 roots jets rows.length (rowFn rows) := by
  cases rows with
  | nil => cases h
  | cons r0 rest =>
    unfold checkJA at h
    dsimp only at h
    rw [getElem?_fun, ← haltRow_G] at h
    simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨⟨⟨⟨⟨⟨hr, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨rootsOKB_sound hr, by simp, h0, h1, h2, h3, ?_, ?_⟩
    · exact chainJ_trans h4
    · rw [← getLast_eq_getD]
      exact h5

end Air
