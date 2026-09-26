import Ski.SourceEval
open Term Front

set_option linter.unusedSectionVars false

/-!
# The words' meaning, from their source

`cw` (`Ski/Words.lean`) is the C model of each word, transcribed from
`skilark.joy.COMPILED_KERNEL`.  This file derives it from the source
instead: each word's equation, as the front end reads it
(`kernelDefs`, checked against all four source texts), run in the source
semantics (`Ski/Simulation.lean`) on the source encoding of a stack,
reaches the source encoding of `cw`'s outcome (`plain_source` for the
words that run no quotation, `source_i` and its siblings for the rest).
No SKI term appears: the source semantics has β, δ and Scott case, and
the encodings are constructors applied to encodings, so the results are
exact, with no unreduced fields.
-/

section
local macro:max "g! " s:str : term => `(CSrc.glob (nm! $s))
local macro:max "v! " x:num : term => `(CSrc.var $x)
local infixl:70 " ⬝c " => CSrc.app

/-- The kernel's constructors of fixed types and its equations, as the
    front end lowers them (`kernelDefs_kernel` and siblings check them). -/
def kernelDefs : List (Nm × GDef) :=
  [(nm! "Zero", .ctor 0 0 2), (nm! "Suc", .ctor 1 1 2),
   (nm! "Num", .ctor 1 0 2), (nm! "Quot", .ctor 1 1 2),
   (nm! "Empty", .ctor 0 0 2), (nm! "Push", .ctor 2 1 2),
   (nm! "RVal", .ctor 1 0 3), (nm! "RErr", .ctor 0 1 3), (nm! "RTime", .ctor 0 2 3),
   (nm! "add", .eqn ⟨[1, 2], some 0,
      ((v! 2 ⬝c v! 1) ⬝c (.lam 3 (g! "Suc" ⬝c ((v! 0 ⬝c v! 1) ⬝c v! 3))))⟩),
   (nm! "seq", .eqn ⟨[0, 1, 2], none,
      ((((v! 0 ⬝c v! 2) ⬝c (.lam 3 (v! 1 ⬝c v! 3))) ⬝c g! "RErr") ⬝c g! "RTime")⟩),
   (nm! "idW", .eqn ⟨[0], none, (g! "RVal" ⬝c v! 0)⟩),
   (nm! "wPop", .eqn ⟨[0], none,
      ((v! 0 ⬝c g! "RErr") ⬝c (.lam 1 (.lam 2 (g! "RVal" ⬝c v! 2))))⟩),
   (nm! "wDup", .eqn ⟨[0], none,
      ((v! 0 ⬝c g! "RErr") ⬝c (.lam 1 (.lam 2 (g! "RVal" ⬝c ((g! "Push" ⬝c v! 1) ⬝c
        ((g! "Push" ⬝c v! 1) ⬝c v! 2))))))⟩),
   (nm! "wSwap", .eqn ⟨[0], none,
      ((v! 0 ⬝c g! "RErr") ⬝c (.lam 1 (.lam 2 ((v! 2 ⬝c g! "RErr") ⬝c (.lam 3 (.lam 4
        (g! "RVal" ⬝c ((g! "Push" ⬝c v! 3) ⬝c ((g! "Push" ⬝c v! 1) ⬝c v! 4)))))))))⟩),
   (nm! "wQcons", .eqn ⟨[0], none,
      ((v! 0 ⬝c g! "RErr") ⬝c (.lam 1 (.lam 2 ((v! 1 ⬝c (.lam 3 g! "RErr")) ⬝c (.lam 4
        ((v! 2 ⬝c g! "RErr") ⬝c (.lam 5 (.lam 6 (g! "RVal" ⬝c ((g! "Push" ⬝c
          (g! "Quot" ⬝c ((g! "QCons" ⬝c v! 5) ⬝c v! 4))) ⬝c v! 6))))))))))⟩),
   (nm! "wCat", .eqn ⟨[0], none,
      ((v! 0 ⬝c g! "RErr") ⬝c (.lam 1 (.lam 2 ((v! 1 ⬝c (.lam 3 g! "RErr")) ⬝c (.lam 4
        ((v! 2 ⬝c g! "RErr") ⬝c (.lam 5 (.lam 6 ((v! 5 ⬝c (.lam 7 g! "RErr")) ⬝c (.lam 8
          (g! "RVal" ⬝c ((g! "Push" ⬝c (g! "Quot" ⬝c ((g! "QCons" ⬝c (g! "Quot" ⬝c v! 8)) ⬝c
            (g! "QThen" ⬝c v! 4)))) ⬝c v! 6))))))))))))⟩),
   (nm! "wUnit", .eqn ⟨[0], none,
      ((v! 0 ⬝c g! "RErr") ⬝c (.lam 1 (.lam 2 (g! "RVal" ⬝c ((g! "Push" ⬝c
        (g! "Quot" ⬝c (g! "QUnit" ⬝c v! 1))) ⬝c v! 2)))))⟩),
   (nm! "wDip", .eqn ⟨[0, 1], none,
      ((v! 1 ⬝c g! "RErr") ⬝c (.lam 2 (.lam 3 ((v! 2 ⬝c (.lam 4 g! "RErr")) ⬝c (.lam 5
        ((v! 3 ⬝c g! "RErr") ⬝c (.lam 6 (.lam 7 (((((v! 0 ⬝c v! 5) ⬝c v! 7) ⬝c (.lam 8
          (g! "RVal" ⬝c ((g! "Push" ⬝c v! 6) ⬝c v! 8)))) ⬝c g! "RErr") ⬝c g! "RTime")))))))))⟩),
   (nm! "wDo", .eqn ⟨[0, 1], none,
      ((v! 1 ⬝c g! "RErr") ⬝c (.lam 2 (.lam 3 ((v! 2 ⬝c (.lam 4 g! "RErr")) ⬝c (.lam 5
        ((v! 0 ⬝c v! 5) ⬝c v! 3))))))⟩),
   (nm! "wIfz", .eqn ⟨[0, 1], none,
      ((v! 1 ⬝c g! "RErr") ⬝c (.lam 2 (.lam 3 ((v! 2 ⬝c (.lam 4 g! "RErr")) ⬝c (.lam 5
        ((v! 3 ⬝c g! "RErr") ⬝c (.lam 6 (.lam 7 ((v! 6 ⬝c (.lam 8 g! "RErr")) ⬝c (.lam 9
          ((v! 7 ⬝c g! "RErr") ⬝c (.lam 10 (.lam 11 ((v! 10 ⬝c (.lam 12 ((v! 12 ⬝c
            ((v! 0 ⬝c v! 9) ⬝c v! 11)) ⬝c (.lam 13 ((v! 0 ⬝c v! 5) ⬝c ((g! "Push" ⬝c
              (g! "Num" ⬝c v! 13)) ⬝c v! 11)))))) ⬝c (.lam 14 g! "RErr")))))))))))))))⟩),
   (nm! "wLit", .eqn ⟨[0, 1], none, (g! "RVal" ⬝c ((g! "Push" ⬝c (g! "Num" ⬝c v! 0)) ⬝c v! 1))⟩),
   (nm! "wQuote", .eqn ⟨[0, 1], none,
      (g! "RVal" ⬝c ((g! "Push" ⬝c (g! "Quot" ⬝c v! 0)) ⬝c v! 1))⟩),
   (nm! "wAdd", .eqn ⟨[0], none,
      ((v! 0 ⬝c g! "RErr") ⬝c (.lam 1 (.lam 2 ((v! 2 ⬝c g! "RErr") ⬝c (.lam 3 (.lam 4
        ((v! 1 ⬝c (.lam 5 ((v! 3 ⬝c (.lam 6 (g! "RVal" ⬝c ((g! "Push" ⬝c (g! "Num" ⬝c
          ((g! "add" ⬝c v! 5) ⬝c v! 6))) ⬝c v! 4)))) ⬝c (.lam 7 g! "RErr")))) ⬝c
            (.lam 8 g! "RErr"))))))))⟩)]
end

/-- The kernel's program. -/
def KP : Nm → Option GDef := fun n => kernelDefs.lookup n

/-- A source file's program defines each of the kernel's globals as
    `kernelDefs` does. -/
def containsKernel (src : List Nat) : Bool :=
  kernelDefs.all fun p => progOf src p.1 == KP p.1

theorem kernel_mono {src : List Nat} (h : containsKernel src = true) :
    ∀ n d, KP n = some d → progOf src n = some d := by
  intro n d hn
  unfold containsKernel at h
  rw [List.all_eq_true] at h
  match lookup_some_mem hn with
  | ⟨p, hp, hp1⟩ =>
    have hc := beq_iff_eq.mp (h p hp)
    rw [hp1, hn] at hc
    exact hc

/-- **The kernel's equations are the source's**, in all four source texts. -/
theorem kernelDefs_sources :
    containsKernel kernelText = true ∧ containsKernel corpusText = true ∧
      containsKernel loopText = true ∧ containsKernel sumText = true := by
  decide +kernel

-- ---------------------------------------------------------------------------
-- Source encodings of values
-- ---------------------------------------------------------------------------

/-- The name of the `k`-th static quotation's constructor, `Q(k+1)`. -/
def qname (k : Nat) : Nm := 81 :: (Nat.toDigits 10 (k + 1)).map Char.toNat

def natS : Nat → Cl
  | 0 => .gref (nm! "Zero")
  | n + 1 => .app (.gref (nm! "Suc")) (natS n)

mutual
  def itemS : Item → Cl
    | .num n => .app (.gref (nm! "Num")) (natS n)
    | .quot q => .app (.gref (nm! "Quot")) (quotS q)
  def quotS : Quotation → Cl
    | .stat k => .gref (qname k)
    | .cons x r => (Cl.gref (nm! "QCons")).apps [itemS x, quotS r]
    | .unit x => .app (.gref (nm! "QUnit")) (itemS x)
    | .then r => .app (.gref (nm! "QThen")) (quotS r)
end

def stackS : Stack → Cl
  | [] => .gref (nm! "Empty")
  | a :: s => (Cl.gref (nm! "Push")).apps [itemS a, stackS s]

def outS : Outcome → Cl
  | .val s => .app (.gref (nm! "RVal")) (stackS s)
  | .err => .gref (nm! "RErr")

/-- A word's source term, given the quotation eliminator `ap`. -/
def wordS (ap : Cl) : Word → Cl
  | .dup => .gref (nm! "wDup")
  | .swap => .gref (nm! "wSwap")
  | .pop => .gref (nm! "wPop")
  | .cons => .gref (nm! "wQcons")
  | .cat => .gref (nm! "wCat")
  | .unit => .gref (nm! "wUnit")
  | .dip => .app (.gref (nm! "wDip")) ap
  | .i => .app (.gref (nm! "wDo")) ap
  | .ifz => .app (.gref (nm! "wIfz")) ap
  | .lit n => .app (.gref (nm! "wLit")) (natS n)
  | .quote q => .app (.gref (nm! "wQuote")) (quotS q)
  | .add => .gref (nm! "wAdd")

-- ---------------------------------------------------------------------------
-- The words that run no quotation
-- ---------------------------------------------------------------------------

/-- The source `add m n` runs to the numeral `m + n`: `add` recurses on `n`. -/
theorem add_source (m : Nat) : ∀ n,
    SSteps KP ((Cl.gref (nm! "add")).apps [natS m, natS n]) (natS (m + n))
  | 0 => seval_sound (k := 2) rfl
  | n + 1 =>
    (seval_sound (k := 3) rfl : SSteps KP _
      (.app (.gref (nm! "Suc")) ((Cl.gref (nm! "add")).apps [natS m, natS n]))).trans
      (SSteps.right _ (add_source m n))

/-- A word's source run, on a stack's encoding, to the encoding of `cw`'s
    outcome. -/
def WordSource (ap : Cl) (w : Word) (S : Stack) : Prop :=
  SSteps KP (.app (wordS ap w) (stackS S)) (outS (cw (fun _ _ => .err) w S))

/-- Source values with placeholders (`Ski/SourceEval.lean`): runs are
    proved on closed terms, where the elaborator caches, then filled. -/
def pushH (x y : Cl) : Cl := (Cl.gref (nm! "Push")).apps [x, y]
def numH (x : Cl) : Cl := .app (.gref (nm! "Num")) x
def quotH (x : Cl) : Cl := .app (.gref (nm! "Quot")) x
def emptyH : Cl := .gref (nm! "Empty")
def errH : Cl := .gref (nm! "RErr")
def rvalH (x : Cl) : Cl := .app (.gref (nm! "RVal")) x
def qconsH (x y : Cl) : Cl := (Cl.gref (nm! "QCons")).apps [x, y]
def qthenH (x : Cl) : Cl := .app (.gref (nm! "QThen")) x
def addH (x y : Cl) : Cl := (Cl.gref (nm! "add")).apps [x, y]

theorem dup_source (ap : Cl) : ∀ S, WordSource ap .dup S
  | [] => seval_sound (k := 20) rfl
  | _ :: _ => seval_sound (k := 20) rfl

theorem swap_source (ap : Cl) : ∀ S, WordSource ap .swap S
  | [] => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wSwap")) emptyH) errH).substC (σ := fill []) (fill_K _)
  | [a] => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wSwap")) (pushH (hole 0) emptyH)) errH).substC
        (σ := fill [itemS a]) (fill_K _)
  | a :: b :: u => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wSwap")) (pushH (hole 0) (pushH (hole 1) (hole 2)))) (rvalH (pushH (hole 1) (pushH (hole 0) (hole 2))))).substC
        (σ := fill [itemS a, itemS b, stackS u]) (fill_K _)

theorem pop_source (ap : Cl) : ∀ S, WordSource ap .pop S
  | [] => seval_sound (k := 20) rfl
  | _ :: _ => seval_sound (k := 20) rfl

theorem cons_source (ap : Cl) : ∀ S, WordSource ap .cons S
  | [] => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wQcons")) emptyH) errH).substC (σ := fill []) (fill_K _)
  | .num n :: t => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wQcons")) (pushH (numH (hole 0)) (hole 1))) errH).substC
        (σ := fill [natS n, stackS t]) (fill_K _)
  | [.quot r] => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wQcons")) (pushH (quotH (hole 0)) emptyH)) errH).substC
        (σ := fill [quotS r]) (fill_K _)
  | .quot r :: b :: u => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wQcons")) (pushH (quotH (hole 0)) (pushH (hole 1) (hole 2)))) (rvalH (pushH (quotH (qconsH (hole 1) (hole 0))) (hole 2)))).substC
        (σ := fill [quotS r, itemS b, stackS u]) (fill_K _)

theorem cat_source (ap : Cl) : ∀ S, WordSource ap .cat S
  | [] => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wCat")) emptyH) errH).substC (σ := fill []) (fill_K _)
  | .num n :: t => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wCat")) (pushH (numH (hole 0)) (hole 1))) errH).substC
        (σ := fill [natS n, stackS t]) (fill_K _)
  | [.quot r] => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wCat")) (pushH (quotH (hole 0)) emptyH)) errH).substC
        (σ := fill [quotS r]) (fill_K _)
  | .quot r :: .num m :: u => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wCat"))
        (pushH (quotH (hole 0)) (pushH (numH (hole 1)) (hole 2)))) errH).substC
        (σ := fill [quotS r, natS m, stackS u]) (fill_K _)
  | .quot r :: .quot l :: u => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wCat"))
        (pushH (quotH (hole 0)) (pushH (quotH (hole 1)) (hole 2)))) (rvalH (pushH (quotH (qconsH (quotH (hole 1)) (qthenH (hole 0)))) (hole 2)))).substC
        (σ := fill [quotS r, quotS l, stackS u]) (fill_K _)

theorem unit_source (ap : Cl) : ∀ S, WordSource ap .unit S
  | [] => seval_sound (k := 20) rfl
  | _ :: _ => seval_sound (k := 20) rfl

theorem lit_source (ap : Cl) (n : Nat) (S : Stack) : WordSource ap (.lit n) S :=
  seval_sound (k := 20) rfl

theorem quote_source (ap : Cl) (q : Quotation) (S : Stack) : WordSource ap (.quote q) S :=
  seval_sound (k := 20) rfl

theorem add_word_source (ap : Cl) : ∀ S, WordSource ap .add S
  | [] => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wAdd")) emptyH) errH).substC (σ := fill []) (fill_K _)
  | [.num m] => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wAdd")) (pushH (numH (hole 0)) emptyH)) errH).substC
        (σ := fill [natS m]) (fill_K _)
  | [.quot q] => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wAdd")) (pushH (quotH (hole 0)) emptyH)) errH).substC
        (σ := fill [quotS q]) (fill_K _)
  | .quot r :: b :: u => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wAdd")) (pushH (quotH (hole 0)) (pushH (hole 1) (hole 2)))) errH).substC
        (σ := fill [quotS r, itemS b, stackS u]) (fill_K _)
  | .num m :: .quot r :: u => (seval_sound (k := 20) rfl :
      SSteps KP (.app (.gref (nm! "wAdd"))
        (pushH (numH (hole 0)) (pushH (quotH (hole 1)) (hole 2)))) errH).substC
        (σ := fill [natS m, quotS r, stackS u]) (fill_K _)
  | .num m :: .num n :: u =>
    ((seval_sound (k := 20) rfl : SSteps KP (.app (.gref (nm! "wAdd"))
        (pushH (numH (hole 0)) (pushH (numH (hole 1)) (hole 2)))) (rvalH (pushH (numH (addH (hole 0) (hole 1))) (hole 2)))).substC
        (σ := fill [natS m, natS n, stackS u]) (fill_K _) :
      SSteps KP _ (.app (.gref (nm! "RVal")) ((Cl.gref (nm! "Push")).apps
        [.app (.gref (nm! "Num")) ((Cl.gref (nm! "add")).apps [natS m, natS n]), stackS u]))).trans
      (SSteps.right _ (SSteps.left _ (SSteps.right _ (SSteps.right _ (add_source m n)))))

/-- **`cw` from the source**, for every word that runs no quotation: the
    word's equation, run in the source semantics on a stack's encoding,
    reaches the encoding of `cw`'s outcome. -/
theorem plain_source (ap : Cl) : ∀ (w : Word), w.ho = false → ∀ S : Stack, WordSource ap w S
  | .dup, _, st => dup_source ap st
  | .swap, _, st => swap_source ap st
  | .pop, _, st => pop_source ap st
  | .cons, _, st => cons_source ap st
  | .cat, _, st => cat_source ap st
  | .unit, _, st => unit_source ap st
  | .lit n, _, st => lit_source ap n st
  | .quote q, _, st => quote_source ap q st
  | .add, _, st => add_word_source ap st
  | .dip, h, _ => by cases h
  | .i, h, _ => by cases h
  | .ifz, h, _ => by cases h

-- ---------------------------------------------------------------------------
-- The words that run a quotation
-- ---------------------------------------------------------------------------

def rtimeH : Cl := .gref (nm! "RTime")

/-- The eliminator meets a relation at the source: applied to a
    quotation's and a stack's encodings, it runs to the encoding of every
    outcome the relation gives. -/
def ApSource (P : Nm → Option GDef) (ap : Cl) (R : Quotation → Stack → Outcome → Prop) : Prop :=
  ∀ r u o, R r u o → SSteps P (ap.apps [quotS r, stackS u]) (outS o)

/-- `P` defines the kernel's globals as `kernelDefs` does. -/
def HasKernel (P : Nm → Option GDef) : Prop := ∀ n d, KP n = some d → P n = some d

theorem i_run_source {P : Nm → Option GDef} (hK : HasKernel P) (ap : Cl) (r : Quotation)
    (t : Stack) :
    SSteps P (.app (wordS ap .i) (stackS (.quot r :: t))) (ap.apps [quotS r, stackS t]) :=
  ((seval_sound (k := 5) rfl : SSteps KP (.app (.app (.gref (nm! "wDo")) (hole 0))
      (pushH (quotH (hole 1)) (hole 2))) ((hole 0).apps [hole 1, hole 2])).substC
    (σ := fill [ap, quotS r, stackS t]) (fill_K _)).mono hK

theorem i_bad_source {P : Nm → Option GDef} (hK : HasKernel P) (ap : Cl) :
    ∀ S : Stack, (∀ r t, S ≠ .quot r :: t) → SSteps P (.app (wordS ap .i) (stackS S)) (outS .err)
  | [], _ => ((seval_sound (k := 20) rfl : SSteps KP (.app (.app (.gref (nm! "wDo")) (hole 0))
      emptyH) errH).substC (σ := fill [ap]) (fill_K _)).mono hK
  | .num n :: t, _ => ((seval_sound (k := 20) rfl : SSteps KP (.app (.app (.gref (nm! "wDo")) (hole 0))
      (pushH (numH (hole 1)) (hole 2))) errH).substC (σ := fill [ap, natS n, stackS t]) (fill_K _)).mono hK
  | .quot r :: t, h => absurd rfl (h r t)

/-- `dip`'s run to its eliminator call, with the continuation that pushes
    the saved item back. -/
theorem dip_stages : ∃ k0,
    SSteps KP (.app (.app (.gref (nm! "wDip")) (hole 0))
      (pushH (quotH (hole 1)) (pushH (hole 2) (hole 3))))
      ((hole 0).apps [hole 1, hole 3, k0, errH, rtimeH]) ∧
    SSteps KP (.app k0 (hole 4)) (rvalH (pushH (hole 2) (hole 4))) :=
  ⟨_, seval_sound (k := 20) rfl, seval_sound (k := 1) rfl⟩

/-- A result's encoding, applied to `RVal`'s, `RErr`'s and `RTime`'s
    continuations, takes its own. -/
theorem outS_val_cases {P : Nm → Option GDef} (hK : HasKernel P) (v : Stack) (k0 k1 k2 : Cl) :
    SSteps P ((outS (.val v)).apps [k0, k1, k2]) (.app k0 (stackS v)) :=
  SSteps.single (SStep.ctor (n := nm! "RVal") (a := 1) (j := 0) (m := 3) (fs := [stackS v])
    (ks := [k0, k1, k2]) (hK _ _ rfl) (by decide) rfl rfl)

theorem outS_err_cases {P : Nm → Option GDef} (hK : HasKernel P) (k0 k1 k2 : Cl) :
    SSteps P ((outS .err).apps [k0, k1, k2]) k1 :=
  SSteps.single (SStep.ctor (n := nm! "RErr") (a := 0) (j := 1) (m := 3) (fs := [])
    (ks := [k0, k1, k2]) (hK _ _ rfl) (by decide) rfl rfl)

theorem SSteps.apps_left {P : Nm → Option GDef} {f f' : Cl} (h : SSteps P f f') :
    ∀ xs, SSteps P (f.apps xs) (f'.apps xs)
  | [] => h
  | a :: as => SSteps.apps_left (h.left a) as

theorem dip_run_source {P : Nm → Option GDef} (hK : HasKernel P) (ap : Cl) (r : Quotation)
    (b : Item) (u : Stack) (o : Outcome) (h : SSteps P (ap.apps [quotS r, stackS u]) (outS o)) :
    SSteps P (.app (wordS ap .dip) (stackS (.quot r :: b :: u))) (outS (dipOut b o)) := by
  cases dip_stages with
  | intro k0 hk =>
    cases o with
    | val v =>
      have h1 := (hk.1.substC (σ := fill [ap, quotS r, itemS b, stackS u, stackS v]) (fill_K _)).mono hK
      have h3 := (hk.2.substC (σ := fill [ap, quotS r, itemS b, stackS u, stackS v]) (fill_K _)).mono hK
      exact h1.trans ((SSteps.apps_left h _).trans ((outS_val_cases hK v _ _ _).trans h3))
    | err =>
      have h1 := (hk.1.substC (σ := fill [ap, quotS r, itemS b, stackS u]) (fill_K _)).mono hK
      exact h1.trans ((SSteps.apps_left h _).trans (outS_err_cases hK _ _ _))

theorem dip_bad_source {P : Nm → Option GDef} (hK : HasKernel P) (ap : Cl) :
    ∀ S : Stack, (∀ r b u, S ≠ .quot r :: b :: u) →
      SSteps P (.app (wordS ap .dip) (stackS S)) (outS .err)
  | [], _ => ((seval_sound (k := 20) rfl : SSteps KP (.app (.app (.gref (nm! "wDip")) (hole 0))
      emptyH) errH).substC (σ := fill [ap]) (fill_K _)).mono hK
  | .num n :: t, _ => ((seval_sound (k := 20) rfl : SSteps KP (.app (.app (.gref (nm! "wDip")) (hole 0))
      (pushH (numH (hole 1)) (hole 2))) errH).substC (σ := fill [ap, natS n, stackS t]) (fill_K _)).mono hK
  | [.quot r], _ => ((seval_sound (k := 20) rfl : SSteps KP (.app (.app (.gref (nm! "wDip")) (hole 0))
      (pushH (quotH (hole 1)) emptyH)) errH).substC (σ := fill [ap, quotS r]) (fill_K _)).mono hK
  | .quot r :: b :: u, h => absurd rfl (h r b u)

theorem ifz_zero_source {P : Nm → Option GDef} (hK : HasKernel P) (ap : Cl) (sc z : Quotation)
    (v : Stack) :
    SSteps P (.app (wordS ap .ifz) (stackS (.quot sc :: .quot z :: .num 0 :: v)))
      (ap.apps [quotS z, stackS v]) :=
  ((seval_sound (k := 30) rfl : SSteps KP (.app (.app (.gref (nm! "wIfz")) (hole 0))
      (pushH (quotH (hole 1)) (pushH (quotH (hole 2)) (pushH (numH (.gref (nm! "Zero"))) (hole 3)))))
      ((hole 0).apps [hole 2, hole 3])).substC
    (σ := fill [ap, quotS sc, quotS z, stackS v]) (fill_K _)).mono hK

theorem ifz_succ_source {P : Nm → Option GDef} (hK : HasKernel P) (ap : Cl) (sc z : Quotation)
    (m : Nat) (v : Stack) :
    SSteps P (.app (wordS ap .ifz) (stackS (.quot sc :: .quot z :: .num (m + 1) :: v)))
      (ap.apps [quotS sc, stackS (.num m :: v)]) :=
  ((seval_sound (k := 30) rfl : SSteps KP (.app (.app (.gref (nm! "wIfz")) (hole 0))
      (pushH (quotH (hole 1)) (pushH (quotH (hole 2))
        (pushH (numH (.app (.gref (nm! "Suc")) (hole 3))) (hole 4)))))
      ((hole 0).apps [hole 1, pushH (numH (hole 3)) (hole 4)])).substC
    (σ := fill [ap, quotS sc, quotS z, natS m, stackS v]) (fill_K _)).mono hK

theorem ifz_bad_source {P : Nm → Option GDef} (hK : HasKernel P) (ap : Cl) :
    ∀ S : Stack, (∀ sc z n v, S ≠ .quot sc :: .quot z :: .num n :: v) →
      SSteps P (.app (wordS ap .ifz) (stackS S)) (outS .err)
  | [], _ => ((seval_sound (k := 30) rfl : SSteps KP (.app (.app (.gref (nm! "wIfz")) (hole 0))
      emptyH) errH).substC (σ := fill [ap]) (fill_K _)).mono hK
  | .num n :: t, _ => ((seval_sound (k := 30) rfl : SSteps KP (.app (.app (.gref (nm! "wIfz")) (hole 0))
      (pushH (numH (hole 1)) (hole 2))) errH).substC (σ := fill [ap, natS n, stackS t]) (fill_K _)).mono hK
  | [.quot r], _ => ((seval_sound (k := 30) rfl : SSteps KP (.app (.app (.gref (nm! "wIfz")) (hole 0))
      (pushH (quotH (hole 1)) emptyH)) errH).substC (σ := fill [ap, quotS r]) (fill_K _)).mono hK
  | .quot r :: .num n :: t, _ => ((seval_sound (k := 30) rfl : SSteps KP
      (.app (.app (.gref (nm! "wIfz")) (hole 0)) (pushH (quotH (hole 1)) (pushH (numH (hole 2)) (hole 3))))
      errH).substC (σ := fill [ap, quotS r, natS n, stackS t]) (fill_K _)).mono hK
  | [.quot r, .quot z], _ => ((seval_sound (k := 30) rfl : SSteps KP
      (.app (.app (.gref (nm! "wIfz")) (hole 0)) (pushH (quotH (hole 1)) (pushH (quotH (hole 2)) emptyH)))
      errH).substC (σ := fill [ap, quotS r, quotS z]) (fill_K _)).mono hK
  | .quot r :: .quot z :: .quot q :: t, _ => ((seval_sound (k := 30) rfl : SSteps KP
      (.app (.app (.gref (nm! "wIfz")) (hole 0)) (pushH (quotH (hole 1)) (pushH (quotH (hole 2))
        (pushH (quotH (hole 3)) (hole 4))))) errH).substC
      (σ := fill [ap, quotS r, quotS z, quotS q, stackS t]) (fill_K _)).mono hK
  | .quot sc :: .quot z :: .num n :: v, h => absurd rfl (h sc z n v)

/-- **`cw` from the source, for every word.**  If the eliminator `ap` meets
    a relation `R` at the source, every word's equation, run on a stack's
    encoding, reaches the encoding of each outcome `cw` gives with `R`
    (`CwR`, `Ski/Apply.lean`). -/
theorem cwR_source {P : Nm → Option GDef} (hK : HasKernel P) {ap : Cl}
    {R : Quotation → Stack → Outcome → Prop} (hR : ApSource P ap R) {w : Word} {S : Stack}
    {o : Outcome} (hc : CwR R w S o) : SSteps P (.app (wordS ap w) (stackS S)) (outS o) := by
  cases hc with
  | plain hw => exact (plain_source ap w hw S).mono hK
  | i_run hr => exact (i_run_source hK ap _ _).trans (hR _ _ _ hr)
  | i_bad hb => exact i_bad_source hK ap _ hb
  | dip_run hr => exact dip_run_source hK ap _ _ _ _ (hR _ _ _ hr)
  | dip_bad hb => exact dip_bad_source hK ap _ hb
  | ifz_zero hr => exact (ifz_zero_source hK ap _ _ _).trans (hR _ _ _ hr)
  | ifz_succ hr => exact (ifz_succ_source hK ap _ _ _ _).trans (hR _ _ _ hr)
  | ifz_bad hb => exact ifz_bad_source hK ap _ hb
