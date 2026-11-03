import Ski.InstOpen
import Ski.AirJet
import Ski.DataJet
import Ski.BitArith

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Term

/-!
# The `dec` data jet: Nock's decrement on a stack, as a contract and a row

**The contract** (`decContract`).  skinock's Λ word `dec` runs on a stack
noun: `decC (cell (atom (n + 1)) r) = val (cell (atom n) r)`, and a crash
(`exit`) on `cell (atom 0) _`, on `cell (cell _ _) _` and on an atom
(`Nock2Ski/JetSpec.lean`).  Its transported contract is `nounContract
decC`: the subject encoded by `encNoun` (an atom's canonical bits, least
significant first, as a Scott list under `Atom`; a cell's halves under
`Cell`), the outcome by `encOut` (`encNoun` of the value, `errT` on exit),
and the licensed implementation is `jetT decF`
(`Nock2Ski/JetTransport.lean`).

This module states the same contract over lean-ski's own copy of the
encoding (`Nn`, `encNn`: `atomT`, `cellT`, `errT` are skinock's
definitions, character for character), restricted to the subjects the
jet's rows read: well-formed nouns (`Nn.wf`, every atom canonical) whose
head atom, when the subject is `[a r]`, has at most `W = 32` bits
(`Dom`).  Beyond that the jet does not fire.  The specification is
`decC` clause for clause (`decSpec`), with the decrement `decB` on bits
(`decB_val`, `decB_canon`).  The contract respects its encoding
(`decContract_respects`: `encNn` is injective), and the tail `r` passes
through as the same term (the contract hands the jet `encNn r` and asks
`encNn r` back), so the row shares its cells.

**The row** (`decRow`).  At the atom `J` with one argument `p` on the
stack, the row reads the subject at `p` cell by cell (`readNn`: the
wrappers `atomT` and `cellT`, the bit list's `Cons` cells, each bit `K`
or `K I`), computes the outcome, and writes it at the counter: the
output's `Cell` and `Atom` wrappers, whose `S (K K)`, `S I` and `K t`
parts point at the input's verified cells; one `Cons` per rewritten bit,
the bits above the first set bit shared with the input; and on a crash
`errT`'s three cells.  The next head is the output's root over the rest of
the stack.  **`decRow_step`** reads a row back: the state is `J ⬝ encNn s
⬝ R` for a subject `s` in the domain, the next `encO (decSpec s) ⬝ R`;
**`decRow_cstep`**: one step of the contract's reduction
(`DataJet.JStep.jet`).
-/

namespace DecJet

open Compose BitArith Mach Air

/-- The head atom's bits beyond which the jet does not fire. -/
def W : Nat := 32

-- ---------------------------------------------------------------------------
-- The encoding: skinock's `Nock2Ski/Noun.lean`, over canonical bit lists
-- ---------------------------------------------------------------------------

/-- `Atom b = λ a c f e. a b`, as bracket abstraction gives it. -/
def atomT (b : Term) : Term :=
  S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ I ⬝ (K ⬝ b))))

/-- `Cell h t = λ a c f e. c h t`. -/
def cellT (h t : Term) : Term :=
  K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ pairT h t))

/-- `Err = λ a c f e. e`, the crash. -/
def errT : Term := K ⬝ (K ⬝ (K ⬝ I))

def atomO (b : OTerm) : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ b))))
def cellO (h t : OTerm) : OTerm :=
  .K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ pairO h t))
def errO : OTerm := .K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))

theorem atomT_toO (b : Term) : (atomT b).toO = atomO b.toO := rfl
theorem cellT_toO (h t : Term) : (cellT h t).toO = cellO h.toO t.toO := rfl
theorem errT_toO : errT.toO = errO := rfl

/-- A canonical bit list: empty, or ending in a set bit. -/
def canonB : List Bool → Bool
  | [] => true
  | [b] => b
  | _ :: b :: bs => canonB (b :: bs)

/-- A noun over bit lists. -/
inductive Nn
  | atom (b : List Bool)
  | cell (h t : Nn)
  deriving DecidableEq, Repr

/-- Every atom canonical. -/
def Nn.wf : Nn → Bool
  | .atom b => canonB b
  | .cell h t => h.wf && t.wf

/-- **The encoding**: skinock's `encNoun`, with `bits n` written out. -/
def encNn : Nn → Term
  | .atom b => atomT (bl b)
  | .cell h t => cellT (encNn h) (encNn t)

/-- An outcome's encoding: `encOut`. -/
def encO : Option Nn → Term
  | none => errT
  | some n => encNn n

-- ---------------------------------------------------------------------------
-- The decrement on bits
-- ---------------------------------------------------------------------------

/-- `b - 1` on canonical bits, least significant first: borrow through the
    low clear bits, clear the first set bit, and drop it when it was the
    top. -/
def decB : List Bool → List Bool
  | [] => []
  | false :: bs => true :: decB bs
  | true :: bs => if bs = [] then [] else false :: bs

theorem canonB_cons {b : Bool} {bs : List Bool} (h : canonB (b :: bs) = true) (hne : bs ≠ []) :
    canonB bs = true := by
  cases bs with
  | nil => exact absurd rfl hne
  | cons c cs => exact h

theorem canonB_tail {b : Bool} {bs : List Bool} (h : canonB (b :: bs) = true) : canonB bs = true := by
  cases bs with
  | nil => rfl
  | cons c cs => exact h

theorem val_pos_of_canon : ∀ {bs : List Bool}, canonB bs = true → bs ≠ [] → 0 < val bs
  | [], _, h => absurd rfl h
  | [b], h, _ => by cases b <;> simp [canonB] at h ⊢; simp [val]
  | b :: c :: cs, h, _ => by
    have := val_pos_of_canon (bs := c :: cs) h (List.cons_ne_nil _ _)
    show 0 < b.toNat + 2 * val (c :: cs); omega

/-- **The decrement's value**: `val (decB b) + 1 = val b` on nonempty
    canonical bits. -/
theorem decB_val : ∀ {bs : List Bool}, canonB bs = true → bs ≠ [] → val (decB bs) + 1 = val bs
  | [], _, h => absurd rfl h
  | false :: bs, h, _ => by
    have hne : bs ≠ [] := by cases bs with | nil => cases h | cons _ _ => exact List.cons_ne_nil _ _
    have ih := decB_val (canonB_cons h hne) hne
    simp only [decB, val, Bool.toNat_true, Bool.toNat_false]; omega
  | true :: bs, _, _ => by
    cases bs with
    | nil => rfl
    | cons c cs => simp only [decB, if_neg (List.cons_ne_nil c cs), val, Bool.toNat_true, Bool.toNat_false]; omega

/-- **The decrement is canonical.** -/
theorem decB_canon : ∀ {bs : List Bool}, canonB bs = true → canonB (decB bs) = true
  | [], _ => rfl
  | false :: bs, h => by
    have hne : bs ≠ [] := by cases bs with | nil => cases h | cons _ _ => exact List.cons_ne_nil _ _
    have ih := decB_canon (canonB_cons h hne)
    show canonB (true :: decB bs) = true
    cases hd : decB bs with
    | nil => rfl
    | cons c cs => rw [hd] at ih; exact ih
  | true :: bs, h => by
    cases bs with
    | nil => rfl
    | cons c cs => simp only [decB, if_neg (List.cons_ne_nil c cs)]; exact h

/-- Canonical bits with one value are one list. -/
theorem canon_val_inj : ∀ {a b : List Bool}, canonB a = true → canonB b = true → val a = val b → a = b
  | [], [], _, _, _ => rfl
  | [], c :: cs, _, hb, hv => by
    have := val_pos_of_canon hb (List.cons_ne_nil _ _)
    have h0 : val ([] : List Bool) = 0 := rfl
    omega
  | c :: cs, [], ha, _, hv => by
    have := val_pos_of_canon ha (List.cons_ne_nil _ _)
    have h0 : val ([] : List Bool) = 0 := rfl
    omega
  | a :: as, b :: bs, ha, hb, hv => by
    simp only [val] at hv
    have hab : a = b := by
      cases a <;> cases b <;> simp at hv ⊢ <;> omega
    subst hab
    have hv' : val as = val bs := by cases a <;> simp at hv <;> omega
    rw [canon_val_inj (canonB_tail ha) (canonB_tail hb) hv']

-- ---------------------------------------------------------------------------
-- The contract
-- ---------------------------------------------------------------------------

/-- **The specification**: skinock's `decC`, clause for clause. -/
def decSpec : Nn → Option Nn
  | .atom _ => none
  | .cell (.atom []) _ => none
  | .cell (.cell _ _) _ => none
  | .cell (.atom (b :: bs)) r => some (.cell (.atom (decB (b :: bs))) r)

/-- The head atom's bits fit `W`; any other subject does. -/
def headFits : Nn → Bool
  | .cell (.atom b) _ => decide (b.length ≤ W)
  | _ => true

/-- **The domain**: well-formed nouns whose head atom fits. -/
def Dom : Type := {s : Nn // s.wf = true ∧ headFits s = true}

/-- **The `dec` data jet**: `J ⬝ encNn s ⟶ encO (decSpec s)`. -/
def decContract : DataJet.Contract Dom (Option Nn) :=
  ⟨fun s => encNn s.1, encO, fun s => decSpec s.1⟩

theorem decContract_encI (s : Dom) : decContract.encI s = encNn s.1 := rfl
theorem decContract_encO : decContract.encO = encO := rfl
theorem decContract_spec (s : Dom) : decContract.spec s = decSpec s.1 := rfl

theorem bl_inj : ∀ {a b : List Bool}, bl a = bl b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: as, b :: bs, h => by
    have h' : K ⬝ pairT (boolT a) (bl as) = K ⬝ pairT (boolT b) (bl bs) := h
    simp only [Term.app.injEq, true_and] at h'
    obtain ⟨h1, h2⟩ := DataJet.pairT_inj h'
    rw [DataJet.boolT_inj h1, bl_inj h2]

theorem encNn_inj : ∀ {x y : Nn}, encNn x = encNn y → x = y
  | .atom a, .atom b, h => by
    have h' : atomT (bl a) = atomT (bl b) := h
    simp only [atomT, Term.app.injEq, true_and] at h'
    rw [bl_inj h']
  | .atom _, .cell _ _, h => nomatch h
  | .cell _ _, .atom _, h => nomatch h
  | .cell h1 t1, .cell h2 t2, h => by
    have h' : cellT (encNn h1) (encNn t1) = cellT (encNn h2) (encNn t2) := h
    simp only [cellT, Term.app.injEq, true_and, and_true] at h'
    obtain ⟨e1, e2⟩ := DataJet.pairT_inj h'
    rw [encNn_inj e1, encNn_inj e2]

/-- **The contract respects its encoding**: `encNn` is injective. -/
theorem decContract_respects : decContract.Respects :=
  DataJet.respects_of_inj fun _ _ h => Subtype.ext (encNn_inj h)

/-- The output's value: `decSpec` on `[a r]` with `a > 0` is `[a - 1 r]`. -/
theorem decSpec_val (b : List Bool) (r : Nn) (hb : canonB b = true) (hne : b ≠ []) :
    ∃ d, decSpec (.cell (.atom b) r) = some (.cell (.atom d) r) ∧ canonB d = true ∧ val d + 1 = val b := by
  cases b with
  | nil => exact absurd rfl hne
  | cons x xs => exact ⟨_, rfl, decB_canon hb, decB_val hb hne⟩

-- ---------------------------------------------------------------------------
-- Reading the subject's cells
-- ---------------------------------------------------------------------------

def isK (H : List Cell) (a : Nat) : Bool := H[a]? == some .K
def isS (H : List Cell) (a : Nat) : Bool := H[a]? == some .S
def isI (H : List Cell) (a : Nat) : Bool := H[a]? == some .I

/-- `S (K K)` at `a`. -/
def isSKK (H : List Cell) (a : Nat) : Bool :=
  match H[a]? with
  | some (.app s kk) =>
    isS H s && (match H[kk]? with
      | some (.app k1 k2) => isK H k1 && isK H k2
      | _ => false)
  | _ => false

/-- `S I` at `a`. -/
def isSI (H : List Cell) (a : Nat) : Bool :=
  match H[a]? with
  | some (.app s i) => isS H s && isI H i
  | _ => false

/-- A Scott Boolean at `a`: `K`, or `K` applied to `I` (`P2Jet.boolAt`). -/
def boolAt (H : List Cell) (a : Nat) : Option Bool :=
  match H[a]? with
  | some .K => some true
  | some (.app f x) => if isK H f && isI H x then some false else none
  | _ => none

/-- The cells of a `Cons` the output reuses: its `S` and `S I` cells, and
    its tail pointer. -/
structure ConsSk where
  s : Nat
  c5 : Nat
  t : Nat
  deriving Repr, DecidableEq

/-- A `Cons b t` cell at `p`: `K (S (S I (K b)) (K t))`. -/
def readCons (H : List Cell) (p : Nat) : Option (Bool × ConsSk) :=
  match H[p]? with
  | some (.app k c1) =>
    if isK H k then
      match H[c1]? with
      | some (.app c2 c3) =>
        match H[c2]?, H[c3]? with
        | some (.app s c4), some (.app k3 t) =>
          if isS H s && isK H k3 then
            match H[c4]? with
            | some (.app c5 c6) =>
              if isSI H c5 then
                match H[c6]? with
                | some (.app k2 h) =>
                  if isK H k2 then
                    match boolAt H h with
                    | some b => some (b, ⟨s, c5, t⟩)
                    | none => none
                  else none
                | _ => none
              else none
            | _ => none
          else none
        | _, _ => none
      | _ => none
    else none
  | _ => none

/-- A bit list at `p`: `Cons` cells to a `K`. -/
def readBits (H : List Cell) : Nat → Nat → Option (List Bool × List ConsSk)
  | 0, _ => none
  | n + 1, p =>
    if isK H p then some ([], [])
    else match readCons H p with
      | some (b, sk) =>
        match readBits H n sk.t with
        | some (bs, sks) => some (b :: bs, sk :: sks)
        | none => none
      | none => none

/-- The cells of an `Atom` wrapper the output reuses: its three `S (K K)`
    cells, its `S I` cell, and the bits' root. -/
structure AtomSk where
  a1 : Nat
  a2 : Nat
  a3 : Nat
  si : Nat
  b : Nat
  deriving Repr, DecidableEq

/-- `Atom b` at `p`: `S (K K) (S (K K) (S (K K) (S I (K b))))`. -/
def readAtom (H : List Cell) (p : Nat) : Option AtomSk :=
  match H[p]? with
  | some (.app a1 x1) =>
    match H[x1]? with
    | some (.app a2 x2) =>
      match H[x2]? with
      | some (.app a3 x3) =>
        match H[x3]? with
        | some (.app si kb) =>
          match H[kb]? with
          | some (.app k b) =>
            if isSKK H a1 && isSKK H a2 && isSKK H a3 && isSI H si && isK H k then some ⟨a1, a2, a3, si, b⟩
            else none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- The cells of a `Cell` wrapper the output reuses: its two `S (K K)`
    cells, its `S` and `S I` cells, its `K t` cell, and the halves. -/
structure CellSk where
  a1 : Nat
  a2 : Nat
  s3 : Nat
  si : Nat
  kt : Nat
  h : Nat
  t : Nat
  deriving Repr, DecidableEq

/-- `Cell h t` at `p`: `K (S (K K) (S (K K) (S (S I (K h)) (K t))))`. -/
def readCell (H : List Cell) (p : Nat) : Option CellSk :=
  match H[p]? with
  | some (.app k0 y1) =>
    match H[y1]? with
    | some (.app a1 y2) =>
      match H[y2]? with
      | some (.app a2 y3) =>
        match H[y3]? with
        | some (.app p1 kt) =>
          match H[p1]?, H[kt]? with
          | some (.app s3 p2), some (.app k6 t) =>
            match H[p2]? with
            | some (.app si kh) =>
              match H[kh]? with
              | some (.app k5 h) =>
                if isK H k0 && isSKK H a1 && isSKK H a2 && isS H s3 && isSI H si && isK H k5 && isK H k6 then
                  some ⟨a1, a2, s3, si, kt, h, t⟩
                else none
              | _ => none
            | _ => none
          | _, _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- A well-formed noun at `p`. -/
def readNn (H : List Cell) : Nat → Nat → Option Nn
  | 0, _ => none
  | n + 1, p =>
    match readAtom H p with
    | some sk =>
      match readBits H (n + 1) sk.b with
      | some (bs, _) => if canonB bs then some (.atom bs) else none
      | none => none
    | none =>
      match readCell H p with
      | some sk =>
        match readNn H n sk.h, readNn H n sk.t with
        | some h, some t => some (.cell h t)
        | _, _ => none
      | none => none

-- ---------------------------------------------------------------------------
-- The output's cells
-- ---------------------------------------------------------------------------

/-- The slots: `K`, `I`, `K I` at 0, 1, 2 (`P2Jet.slotsOK`). -/
def slotsOK (H : List Cell) : Bool :=
  H[0]? == some .K && H[1]? == some .I && H[2]? == some (.app 0 1)

/-- The output `Cell` wrapper at `c`, over the input's cells, its head at
    `c + 7`. -/
def cellCells (c : Nat) (sk : CellSk) : List Cell :=
  [.app 0 (c + 1), .app sk.a1 (c + 2), .app sk.a2 (c + 3), .app (c + 4) sk.kt, .app sk.s3 (c + 5),
   .app sk.si (c + 6), .app 0 (c + 7)]

/-- The output `Atom` wrapper at `c`, its bits' root `root`. -/
def atomCells (c : Nat) (sk : AtomSk) (root : Nat) : List Cell :=
  [.app sk.a1 (c + 1), .app sk.a2 (c + 2), .app sk.a3 (c + 3), .app sk.si (c + 4), .app 0 root]

/-- `errT`'s cells at `c`: `K (K (K I))` over the slots. -/
def errCells (c : Nat) : List Cell := [.app 0 (c + 1), .app 0 (c + 2), .app 0 1]

/-- Whether the next `Cons` of `bs` is dropped: the top bit, set, about to
    clear. -/
def dropped (bs : List Bool) : Bool := bs == [true]

/-- The output's bit cells from `c`, one `Cons` of six cells per rewritten
    bit: a clear bit under borrow becomes `K` (the slot `0`); the first set
    bit becomes `K I` (the slot `2`) over the input's tail, or is dropped
    when it is the top. -/
def bitCells : Nat → List Bool → List ConsSk → List Cell
  | _, [], _ => []
  | _, _, [] => []
  | c, false :: bs, sk :: sks =>
    [.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 0,
     .app 0 (if dropped bs then 0 else c + 6)] ++ bitCells (c + 6) bs sks
  | c, true :: bs, sk :: _ =>
    if bs = [] then []
    else [.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 2, .app 0 sk.t]

/-- The output bits' root: the slot `0` (nil) when the only bit is dropped,
    else the first `Cons` at `c`. -/
def bitsRoot (c : Nat) (bs : List Bool) : Nat := if dropped bs then 0 else c

/-- **The cells a row writes at `c`**, and the output's root. -/
def outCells (c : Nat) (s : Nn) (csk : Option CellSk) (ask : Option AtomSk) (sks : List ConsSk) :
    Option (List Cell × Nat) :=
  match s, csk, ask with
  | .atom _, _, _ => some (errCells c, c)
  | .cell (.atom []) _, some csk, some ask =>
    some (cellCells c csk ++ atomCells (c + 7) ask 0 ++ errCells (c + 12), c + 12)
  | .cell (.atom (b :: bs)) _, some csk, some ask =>
    some (cellCells c csk ++ atomCells (c + 7) ask (bitsRoot (c + 12) (b :: bs)) ++ bitCells (c + 12) (b :: bs) sks, c)
  | .cell (.cell _ _) _, some csk, _ =>
    some (cellCells c csk ++ List.replicate 5 (.app 0 0) ++ errCells (c + 12), c + 12)
  | _, _, _ => none

/-- **The subject at `p`**, read once: the noun, and the cells of its
    wrappers and head bits the output reuses.  An atom subject; a cell whose
    head is an atom (its bits canonical) over a noun; or a cell whose head
    is a cell, both halves nouns. -/
def readSubj (H : List Cell) (p : Nat) : Option (Nn × Option CellSk × Option AtomSk × List ConsSk) :=
  match readAtom H p with
  | some sk =>
    match readBits H H.length sk.b with
    | some (bs, sks) => if canonB bs then some (.atom bs, none, some sk, sks) else none
    | none => none
  | none =>
    match readCell H p with
    | some csk =>
      match readAtom H csk.h with
      | some ask =>
        match readBits H H.length ask.b with
        | some (bs, sks) =>
          if canonB bs then
            match readNn H H.length csk.t with
            | some r => some (.cell (.atom bs) r, some csk, some ask, sks)
            | none => none
          else none
        | none => none
      | none =>
        match readNn H H.length csk.h, readNn H H.length csk.t with
        | some hh, some tt => some (.cell hh tt, some csk, none, [])
        | _, _ => none
    | none => none

/-- **The jet's row**: at the atom `J` with the subject's pointer `p` on the
    stack, a well-formed subject whose head fits, the outcome written at
    the counter. -/
def decRow (M : List Cell) (J : Nat) (r : Row) : Option Row :=
  let H := M.take r.ctr
  match H[r.hd]? with
  | some (.atom j') =>
    if j' = J ∧ slotsOK H = true then
      match popN H 1 r.stk with
      | some ([p], rest) =>
        match readSubj H p with
        | some (s, csk, ask, sks) =>
          if headFits s then
            match outCells r.ctr s csk ask sks with
            | some (cells, root) =>
              if wrs M r.ctr cells then some ⟨root, rest, r.ctr + cells.length⟩ else none
            | none => none
          else none
        | none => none
      | _ => none
    else none
  | _ => none

-- ---------------------------------------------------------------------------
-- Reading back: peeling a read-back along the cells the row reads
-- ---------------------------------------------------------------------------

/-- An application cell's read-back is its parts', one fuel below. -/
theorem app_peel {H : List Cell} {p a b : Nat} {F : Nat} {u : OTerm} (hp : H[p]? = some (.app a b))
    (hu : otermAt H F p = some u) :
    ∃ f ta tb, F = f + 1 ∧ otermAt H f a = some ta ∧ otermAt H f b = some tb ∧ u = ta ⬝ₒ tb := by
  cases F with
  | zero => cases hu
  | succ f =>
    unfold otermAt at hu
    rw [hp] at hu
    dsimp only at hu
    cases ha : otermAt H f a with
    | none => rw [ha] at hu; cases hu
    | some ta =>
      cases hb : otermAt H f b with
      | none => rw [ha, hb] at hu; cases hu
      | some tb =>
        rw [ha, hb] at hu
        cases hu
        exact ⟨f, ta, tb, rfl, ha, hb, rfl⟩

theorem K_peel {H : List Cell} {p F : Nat} {u : OTerm} (hp : H[p]? = some .K) (hu : otermAt H F p = some u) :
    u = .K := by
  cases F with
  | zero => cases hu
  | succ f => unfold otermAt at hu; rw [hp] at hu; cases hu; rfl

theorem S_peel {H : List Cell} {p F : Nat} {u : OTerm} (hp : H[p]? = some .S) (hu : otermAt H F p = some u) :
    u = .S := by
  cases F with
  | zero => cases hu
  | succ f => unfold otermAt at hu; rw [hp] at hu; cases hu; rfl

theorem I_peel {H : List Cell} {p F : Nat} {u : OTerm} (hp : H[p]? = some .I) (hu : otermAt H F p = some u) :
    u = .I := by
  cases F with
  | zero => cases hu
  | succ f => unfold otermAt at hu; rw [hp] at hu; cases hu; rfl

/-- A read-back takes fuel. -/
theorem otermAt_pos {H : List Cell} {a F : Nat} {u : OTerm} (h : otermAt H F a = some u) : 1 ≤ F := by
  cases F with
  | zero => cases h
  | succ _ => omega

theorem isK_eq {H : List Cell} {a : Nat} (h : isK H a = true) : H[a]? = some .K := beq_iff_eq.1 h
theorem isS_eq {H : List Cell} {a : Nat} (h : isS H a = true) : H[a]? = some .S := beq_iff_eq.1 h
theorem isI_eq {H : List Cell} {a : Nat} (h : isI H a = true) : H[a]? = some .I := beq_iff_eq.1 h

/-- The cells read back at any fuel that reaches them. -/
theorem K_ot {H : List Cell} {a : Nat} (h : isK H a = true) {F : Nat} (hF : 1 ≤ F) : otermAt H F a = some .K := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
  unfold otermAt; rw [isK_eq h]

theorem S_ot {H : List Cell} {a : Nat} (h : isS H a = true) {F : Nat} (hF : 1 ≤ F) : otermAt H F a = some .S := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
  unfold otermAt; rw [isS_eq h]

theorem I_ot {H : List Cell} {a : Nat} (h : isI H a = true) {F : Nat} (hF : 1 ≤ F) : otermAt H F a = some .I := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
  unfold otermAt; rw [isI_eq h]

/-- Building a read-back from the parts'. -/
theorem app_ot {H : List Cell} {p a b : Nat} {f g F : Nat} {ta tb : OTerm} (hp : H[p]? = some (.app a b))
    (ha : otermAt H f a = some ta) (hb : otermAt H g b = some tb) (hf : f + 1 ≤ F) (hg : g + 1 ≤ F) :
    otermAt H F p = some (ta ⬝ₒ tb) := by
  obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by omega⟩
  unfold otermAt
  rw [hp]
  dsimp only
  rw [otermAt_mono ha (by omega), otermAt_mono hb (by omega)]

theorem isSKK_ot {H : List Cell} {a : Nat} (h : isSKK H a = true) {F : Nat} (hF : 3 ≤ F) :
    otermAt H F a = some (.S ⬝ₒ (.K ⬝ₒ .K)) := by
  unfold isSKK at h
  cases ha : H[a]? with
  | none => rw [ha] at h; cases h
  | some c =>
    rw [ha] at h
    cases c with
    | app s kk =>
      dsimp only at h
      cases hkk : H[kk]? with
      | none => rw [hkk] at h; simp at h
      | some c2 =>
        rw [hkk] at h
        cases c2 with
        | app k1 k2 =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨hs, hk1, hk2⟩ := h
          exact app_ot (F := F) ha (S_ot hs (F := 1) (by omega))
            (app_ot (F := 2) hkk (K_ot hk1 (F := 1) (by omega)) (K_ot hk2 (F := 1) (by omega)) (by omega) (by omega))
            (by omega) (by omega)
        | _ => simp at h
    | _ => cases h

theorem isSI_ot {H : List Cell} {a : Nat} (h : isSI H a = true) {F : Nat} (hF : 2 ≤ F) :
    otermAt H F a = some (.S ⬝ₒ .I) := by
  unfold isSI at h
  cases ha : H[a]? with
  | none => rw [ha] at h; cases h
  | some c =>
    rw [ha] at h
    cases c with
    | app s i =>
      simp only [Bool.and_eq_true] at h
      exact app_ot (F := F) ha (S_ot h.1 (F := 1) (by omega)) (I_ot h.2 (F := 1) (by omega)) (by omega) (by omega)
    | _ => cases h

theorem boolAt_ot {H : List Cell} {a : Nat} {b : Bool} (h : boolAt H a = some b) {F : Nat} (hF : 2 ≤ F) :
    otermAt H F a = some (boolT b).toO := by
  unfold boolAt at h
  cases ha : H[a]? with
  | none => rw [ha] at h; cases h
  | some c =>
    rw [ha] at h
    cases c with
    | K => cases h; exact K_ot (beq_iff_eq.2 ha) (by omega)
    | app f x =>
      dsimp only at h
      split at h
      · rename_i hk
        cases h
        simp only [Bool.and_eq_true] at hk
        exact app_ot (F := F) ha (K_ot hk.1 (F := 1) (by omega)) (I_ot hk.2 (F := 1) (by omega)) (by omega) (by omega)
      · cases h
    | _ => cases h

/-- A read-back is unique: two fuels that reach a cell read the same term. -/
theorem otermAt_det {H : List Cell} {a F G : Nat} {u v : OTerm} (hu : otermAt H F a = some u)
    (hv : otermAt H G a = some v) : u = v := by
  have hu' := otermAt_mono hu (Nat.le_max_left F G)
  have hv' := otermAt_mono hv (Nat.le_max_right F G)
  rw [hu'] at hv'
  cases hv'; rfl

/-- **A `Cons` cell peeled**: its read-back is the Boolean consed on its
    tail's, the tail three fuels below. -/
theorem readCons_peel {H : List Cell} {p : Nat} {b : Bool} {sk : ConsSk} (h : readCons H p = some (b, sk))
    {F : Nat} {u : OTerm} (hu : otermAt H F p = some u) :
    ∃ f tt, F = f + 4 ∧ 2 ≤ f ∧ u = consO (boolT b).toO tt ∧ otermAt H (f + 1) sk.t = some tt ∧
      isS H sk.s = true ∧ isSI H sk.c5 = true := by
  unfold readCons at h
  cases hp : H[p]? with
  | none => rw [hp] at h; cases h
  | some c =>
    rw [hp] at h
    cases c with
    | app k c1 =>
      dsimp only at h
      split at h
      · rename_i hk
        cases hc1 : H[c1]? with
        | none => rw [hc1] at h; cases h
        | some cc1 =>
          rw [hc1] at h
          cases cc1 with
          | app c2 c3 =>
            dsimp only at h
            cases hc2 : H[c2]? with
            | none => rw [hc2] at h; cases h
            | some cc2 =>
              cases hc3 : H[c3]? with
              | none => rw [hc2, hc3] at h; cases cc2 <;> cases h
              | some cc3 =>
                rw [hc2, hc3] at h
                cases cc2 with
                | app s c4 =>
                  cases cc3 with
                  | app k3 t =>
                    dsimp only at h
                    split at h
                    · rename_i hsk3
                      simp only [Bool.and_eq_true] at hsk3
                      cases hc4 : H[c4]? with
                      | none => rw [hc4] at h; cases h
                      | some cc4 =>
                        rw [hc4] at h
                        cases cc4 with
                        | app c5 c6 =>
                          dsimp only at h
                          split at h
                          · rename_i hc5
                            cases hc6 : H[c6]? with
                            | none => rw [hc6] at h; cases h
                            | some cc6 =>
                              rw [hc6] at h
                              cases cc6 with
                              | app k2 hb =>
                                dsimp only at h
                                split at h
                                · rename_i hk2
                                  cases hbb : boolAt H hb with
                                  | none => rw [hbb] at h; cases h
                                  | some b' =>
                                    rw [hbb] at h
                                    cases h
                                    -- peel the read-back along the same cells
                                    obtain ⟨f1, t1, t2, rfl, h1, h2, rfl⟩ := app_peel hp hu
                                    have e1 := K_peel (isK_eq hk) h1
                                    obtain ⟨f2, t3, t4, rfl, h3, h4, rfl⟩ := app_peel hc1 h2
                                    obtain ⟨f3, t5, t6, rfl, h5, h6, rfl⟩ := app_peel hc2 h3
                                    obtain ⟨f3', t7, t8, e3, h7, h8, rfl⟩ := app_peel hc3 h4
                                    have e3' : f3' = f3 := by omega
                                    subst e3'
                                    have e5 := S_peel (isS_eq hsk3.1) h5
                                    have e7 := K_peel (isK_eq hsk3.2) h7
                                    obtain ⟨f4, t9, t10, rfl, h9, h10, rfl⟩ := app_peel hc4 h6
                                    have e9 := otermAt_det h9 (isSI_ot hc5 (F := 2) (Nat.le_refl _))
                                    have hf4 : 2 ≤ f4 := by
                                      unfold isSI at hc5
                                      cases hc5' : H[c5]? with
                                      | none => rw [hc5'] at hc5; cases hc5
                                      | some cc5 =>
                                        rw [hc5'] at hc5
                                        cases cc5 with
                                        | app s5 i5 =>
                                          obtain ⟨f', _, _, rfl, h', _, _⟩ := app_peel hc5' h9
                                          have := otermAt_pos h'
                                          omega
                                        | _ => cases hc5
                                    obtain ⟨f5, t11, t12, rfl, h11, h12, rfl⟩ := app_peel hc6 h10
                                    have e11 := K_peel (isK_eq hk2) h11
                                    have e12 := otermAt_det h12 (boolAt_ot hbb (F := 2) (Nat.le_refl _))
                                    subst e1 e5 e7 e9 e11 e12
                                    exact ⟨f5 + 1, t8, by omega, by omega, rfl, h8, hsk3.1, hc5⟩
                                · cases h
                              | _ => cases h
                          · cases h
                        | _ => cases h
                    · cases h
                  | _ => cases h
                | _ => cases cc3 <;> cases h
          | _ => cases h
      · cases h
    | _ => cases h

/-- **A bit list read back**: `bl` of the bits. -/
theorem readBits_ot {H : List Cell} : ∀ {n p : Nat} {bs : List Bool} {sks : List ConsSk},
    readBits H n p = some (bs, sks) → ∀ {F : Nat} {u : OTerm}, otermAt H F p = some u → u = (bl bs).toO
  | 0, _, _, _, h, _, _, _ => nomatch h
  | n + 1, p, bs, sks, h, F, u, hu => by
    unfold readBits at h
    split at h
    · rename_i hk
      cases h
      exact K_peel (isK_eq hk) hu
    · cases hc : readCons H p with
      | none => rw [hc] at h; cases h
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hc] at h
        dsimp only at h
        cases hr : readBits H n sk.t with
        | none => rw [hr] at h; cases h
        | some q' =>
          obtain ⟨bs', sks'⟩ := q'
          rw [hr] at h
          cases h
          obtain ⟨f, tt, rfl, _, rfl, ht, _, _⟩ := readCons_peel hc hu
          rw [readBits_ot hr ht]
          rfl

theorem readBits_length {H : List Cell} : ∀ {n p : Nat} {bs : List Bool} {sks : List ConsSk},
    readBits H n p = some (bs, sks) → sks.length = bs.length
  | 0, _, _, _, h => by cases h
  | n + 1, p, bs, sks, h => by
    unfold readBits at h
    split at h
    · cases h; rfl
    · cases hc : readCons H p with
      | none => rw [hc] at h; cases h
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hc] at h
        dsimp only at h
        cases hr : readBits H n sk.t with
        | none => rw [hr] at h; cases h
        | some q' =>
          obtain ⟨bs', sks'⟩ := q'
          rw [hr] at h
          cases h
          exact congrArg (· + 1) (readBits_length hr)

/-- **An `Atom` wrapper peeled**: `atomO` of its bits' read-back, five fuels
    below. -/
theorem readAtom_peel {H : List Cell} {p : Nat} {sk : AtomSk} (h : readAtom H p = some sk) {F : Nat} {u : OTerm}
    (hu : otermAt H F p = some u) :
    ∃ f tb, F = f + 5 ∧ u = atomO tb ∧ otermAt H f sk.b = some tb ∧
      isSKK H sk.a1 = true ∧ isSKK H sk.a2 = true ∧ isSKK H sk.a3 = true ∧ isSI H sk.si = true := by
  unfold readAtom at h
  cases hp : H[p]? with
  | none => rw [hp] at h; cases h
  | some c =>
    rw [hp] at h
    cases c with
    | app a1 x1 =>
      dsimp only at h
      cases h1 : H[x1]? with
      | none => rw [h1] at h; cases h
      | some c1 =>
        rw [h1] at h
        cases c1 with
        | app a2 x2 =>
          dsimp only at h
          cases h2 : H[x2]? with
          | none => rw [h2] at h; cases h
          | some c2 =>
            rw [h2] at h
            cases c2 with
            | app a3 x3 =>
              dsimp only at h
              cases h3 : H[x3]? with
              | none => rw [h3] at h; cases h
              | some c3 =>
                rw [h3] at h
                cases c3 with
                | app si kb =>
                  dsimp only at h
                  cases h4 : H[kb]? with
                  | none => rw [h4] at h; cases h
                  | some c4 =>
                    rw [h4] at h
                    cases c4 with
                    | app k b =>
                      dsimp only at h
                      split at h
                      · rename_i hall
                        cases h
                        simp only [Bool.and_eq_true] at hall
                        obtain ⟨⟨⟨⟨ha1, ha2⟩, ha3⟩, hsi⟩, hk⟩ := hall
                        obtain ⟨f1, t1, t2, rfl, g1, g2, rfl⟩ := app_peel hp hu
                        obtain ⟨f2, t3, t4, rfl, g3, g4, rfl⟩ := app_peel h1 g2
                        obtain ⟨f3, t5, t6, rfl, g5, g6, rfl⟩ := app_peel h2 g4
                        obtain ⟨f4, t7, t8, rfl, g7, g8, rfl⟩ := app_peel h3 g6
                        obtain ⟨f5, t9, t10, rfl, g9, g10, rfl⟩ := app_peel h4 g8
                        have e1 := otermAt_det g1 (isSKK_ot ha1 (F := 3) (Nat.le_refl _))
                        have e3 := otermAt_det g3 (isSKK_ot ha2 (F := 3) (Nat.le_refl _))
                        have e5 := otermAt_det g5 (isSKK_ot ha3 (F := 3) (Nat.le_refl _))
                        have e7 := otermAt_det g7 (isSI_ot hsi (F := 2) (Nat.le_refl _))
                        have e9 := K_peel (isK_eq hk) g9
                        subst e1 e3 e5 e7 e9
                        exact ⟨f5, t10, by omega, rfl, g10, ha1, ha2, ha3, hsi⟩
                      · cases h
                    | _ => cases h
                | _ => cases h
            | _ => cases h
        | _ => cases h
    | _ => cases h

/-- **A `Cell` wrapper peeled**: `cellO` of its halves' read-backs, seven
    and five fuels below. -/
theorem readCell_peel {H : List Cell} {p : Nat} {sk : CellSk} (h : readCell H p = some sk) {F : Nat} {u : OTerm}
    (hu : otermAt H F p = some u) :
    ∃ f th tt, F = f + 7 ∧ u = cellO th tt ∧ otermAt H f sk.h = some th ∧ otermAt H (f + 2) sk.t = some tt ∧
      otermAt H (f + 3) sk.kt = some (.K ⬝ₒ tt) ∧
      isSKK H sk.a1 = true ∧ isSKK H sk.a2 = true ∧ isS H sk.s3 = true ∧ isSI H sk.si = true := by
  unfold readCell at h
  cases hp : H[p]? with
  | none => rw [hp] at h; cases h
  | some c =>
    rw [hp] at h
    cases c with
    | app k0 y1 =>
      dsimp only at h
      cases h1 : H[y1]? with
      | none => rw [h1] at h; cases h
      | some c1 =>
        rw [h1] at h
        cases c1 with
        | app a1 y2 =>
          dsimp only at h
          cases h2 : H[y2]? with
          | none => rw [h2] at h; cases h
          | some c2 =>
            rw [h2] at h
            cases c2 with
            | app a2 y3 =>
              dsimp only at h
              cases h3 : H[y3]? with
              | none => rw [h3] at h; cases h
              | some c3 =>
                rw [h3] at h
                cases c3 with
                | app p1 kt =>
                  dsimp only at h
                  cases h4 : H[p1]? with
                  | none => rw [h4] at h; cases h
                  | some c4 =>
                    cases h5 : H[kt]? with
                    | none => rw [h4, h5] at h; cases c4 <;> cases h
                    | some c5 =>
                      rw [h4, h5] at h
                      cases c4 with
                      | app s3 p2 =>
                        cases c5 with
                        | app k6 t =>
                          dsimp only at h
                          cases h6 : H[p2]? with
                          | none => rw [h6] at h; cases h
                          | some c6 =>
                            rw [h6] at h
                            cases c6 with
                            | app si kh =>
                              dsimp only at h
                              cases h7 : H[kh]? with
                              | none => rw [h7] at h; cases h
                              | some c7 =>
                                rw [h7] at h
                                cases c7 with
                                | app k5 hh =>
                                  dsimp only at h
                                  split at h
                                  · rename_i hall
                                    cases h
                                    simp only [Bool.and_eq_true] at hall
                                    obtain ⟨⟨⟨⟨⟨⟨hk0, ha1⟩, ha2⟩, hs3⟩, hsi⟩, hk5⟩, hk6⟩ := hall
                                    obtain ⟨f1, t1, t2, rfl, g1, g2, rfl⟩ := app_peel hp hu
                                    have e1 := K_peel (isK_eq hk0) g1
                                    obtain ⟨f2, t3, t4, rfl, g3, g4, rfl⟩ := app_peel h1 g2
                                    have e3 := otermAt_det g3 (isSKK_ot ha1 (F := 3) (Nat.le_refl _))
                                    obtain ⟨f3, t5, t6, rfl, g5, g6, rfl⟩ := app_peel h2 g4
                                    have e5 := otermAt_det g5 (isSKK_ot ha2 (F := 3) (Nat.le_refl _))
                                    obtain ⟨f4, t7, t8, rfl, g7, g8, rfl⟩ := app_peel h3 g6
                                    obtain ⟨f5, t9, t10, rfl, g9, g10, rfl⟩ := app_peel h4 g7
                                    obtain ⟨f5', t11, t12, e5', g11, g12, rfl⟩ := app_peel h5 g8
                                    have e5'' : f5' = f5 := by omega
                                    subst e5''
                                    have e9 := S_peel (isS_eq hs3) g9
                                    have e11 := K_peel (isK_eq hk6) g11
                                    obtain ⟨f6, t13, t14, rfl, g13, g14, rfl⟩ := app_peel h6 g10
                                    have e13 := otermAt_det g13 (isSI_ot hsi (F := 2) (Nat.le_refl _))
                                    obtain ⟨f7, t15, t16, rfl, g15, g16, rfl⟩ := app_peel h7 g14
                                    have e15 := K_peel (isK_eq hk5) g15
                                    subst e1 e3 e5 e9 e11 e13 e15
                                    exact ⟨f7, t16, t12, by omega, rfl, g16, g12, g8, ha1, ha2, hs3, hsi⟩
                                  · cases h
                                | _ => cases h
                            | _ => cases h
                        | _ => cases h
                      | _ => cases c5 <;> cases h
                | _ => cases h
            | _ => cases h
        | _ => cases h
    | _ => cases h

/-- **A noun read back**: its encoding. -/
theorem readNn_ot {H : List Cell} : ∀ {n p : Nat} {s : Nn}, readNn H n p = some s →
    ∀ {F : Nat} {u : OTerm}, otermAt H F p = some u → u = (encNn s).toO
  | 0, _, _, h, _, _, _ => nomatch h
  | n + 1, p, s, h, F, u, hu => by
    unfold readNn at h
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at h
      dsimp only at h
      cases hb : readBits H (n + 1) sk.b with
      | none => rw [hb] at h; cases h
      | some q =>
        obtain ⟨bs, sks⟩ := q
        rw [hb] at h
        dsimp only at h
        split at h
        · cases h
          obtain ⟨f, tb, rfl, rfl, htb, _⟩ := readAtom_peel ha hu
          rw [readBits_ot hb htb]
          rfl
        · cases h
    | none =>
      rw [ha] at h
      dsimp only at h
      cases hc : readCell H p with
      | none => rw [hc] at h; cases h
      | some sk =>
        rw [hc] at h
        dsimp only at h
        cases hh : readNn H n sk.h with
        | none => rw [hh] at h; cases h
        | some sh =>
          cases ht : readNn H n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some st =>
            rw [hh, ht] at h
            cases h
            obtain ⟨f, th, tt, rfl, rfl, hth, htt, _⟩ := readCell_peel hc hu
            rw [readNn_ot hh hth, readNn_ot ht htt]
            rfl

/-- A read noun is well formed. -/
theorem readNn_wf {H : List Cell} : ∀ {n p : Nat} {s : Nn}, readNn H n p = some s → s.wf = true
  | 0, _, _, h => by cases h
  | n + 1, p, s, h => by
    unfold readNn at h
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at h
      dsimp only at h
      cases hb : readBits H (n + 1) sk.b with
      | none => rw [hb] at h; cases h
      | some q =>
        obtain ⟨bs, sks⟩ := q
        rw [hb] at h
        dsimp only at h
        split at h
        · cases h; assumption
        · cases h
    | none =>
      rw [ha] at h
      dsimp only at h
      cases hc : readCell H p with
      | none => rw [hc] at h; cases h
      | some sk =>
        rw [hc] at h
        dsimp only at h
        cases hh : readNn H n sk.h with
        | none => rw [hh] at h; cases h
        | some sh =>
          cases ht : readNn H n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some st =>
            rw [hh, ht] at h
            cases h
            show (sh.wf && st.wf) = true
            rw [readNn_wf hh, readNn_wf ht]; rfl

-- ---------------------------------------------------------------------------
-- Reading back the output
-- ---------------------------------------------------------------------------

theorem readBits_mono {H : List Cell} : ∀ {n m p : Nat} {x : List Bool × List ConsSk},
    readBits H n p = some x → n ≤ m → readBits H m p = some x
  | 0, _, _, _, h, _ => nomatch h
  | n + 1, m, p, x, h, hnm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold readBits at h ⊢
    split at h
    · rename_i hk; rw [if_pos hk]; exact h
    · rename_i hk
      rw [if_neg hk]
      cases hc : readCons H p with
      | none => rw [hc] at h; cases h
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hc] at h
        dsimp only at h ⊢
        cases hr : readBits H n sk.t with
        | none => rw [hr] at h; cases h
        | some q' =>
          rw [hr] at h
          rw [readBits_mono hr (by omega)]
          exact h

theorem slots_K {H : List Cell} (hs : slotsOK H = true) : isK H 0 = true := by
  unfold slotsOK at hs; simp only [Bool.and_eq_true] at hs; exact beq_iff_eq.2 (beq_iff_eq.1 hs.1.1)
theorem slots_I {H : List Cell} (hs : slotsOK H = true) : isI H 1 = true := by
  unfold slotsOK at hs; simp only [Bool.and_eq_true] at hs; exact beq_iff_eq.2 (beq_iff_eq.1 hs.1.2)
theorem slots_KI {H : List Cell} (hs : slotsOK H = true) : H[2]? = some (.app 0 1) := by
  unfold slotsOK at hs; simp only [Bool.and_eq_true] at hs; exact beq_iff_eq.1 hs.2

theorem slots_len {H : List Cell} (hs : slotsOK H = true) : 3 ≤ H.length := by
  have := slots_KI hs
  rw [List.getElem?_eq_some_iff] at this
  obtain ⟨hl, _⟩ := this
  omega

theorem slotsOK_append {H cs : List Cell} (hs : slotsOK H = true) : slotsOK (H ++ cs) = true := by
  have hl := slots_len hs
  unfold slotsOK at hs ⊢
  rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
    List.getElem?_append_left (by omega)]
  exact hs

/-- The slot `2` reads back as `K I`. -/
theorem slot2_ot {H : List Cell} (hs : slotsOK H = true) {F : Nat} (hF : 2 ≤ F) :
    otermAt H F 2 = some (.K ⬝ₒ .I) :=
  app_ot (F := F) (slots_KI hs) (K_ot (slots_K hs) (F := 1) (Nat.le_refl _)) (I_ot (slots_I hs) (F := 1) (Nat.le_refl _))
    (by omega) (by omega)

/-- `errT`'s cells at `c` read back as `errO`. -/
theorem err_ot {H : List Cell} {c : Nat} (hs : slotsOK H = true) (h0 : H[c]? = some (.app 0 (c + 1)))
    (h1 : H[c + 1]? = some (.app 0 (c + 2))) (h2 : H[c + 2]? = some (.app 0 1)) {F : Nat} (hF : 4 ≤ F) :
    otermAt H F c = some errO :=
  app_ot (F := F) h0 (K_ot (slots_K hs) (F := 1) (Nat.le_refl _))
    (app_ot (F := F - 1) h1 (K_ot (slots_K hs) (F := 1) (Nat.le_refl _))
      (app_ot (F := F - 2) h2 (K_ot (slots_K hs) (F := 1) (Nat.le_refl _)) (I_ot (slots_I hs) (F := 1) (Nat.le_refl _))
        (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)

/-- The cells written at `c` are at `c + i` in the extended heap. -/
theorem at_written {H cs : List Cell} {c i : Nat} (hc : H.length = c) : (H ++ cs)[c + i]? = cs[i]? := by
  rw [List.getElem?_append_right (by omega), hc, Nat.add_sub_cancel_left]

theorem bitCells_cons_false (c : Nat) (bs : List Bool) (sk : ConsSk) (sks : List ConsSk) :
    bitCells c (false :: bs) (sk :: sks) =
      [.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 0,
       .app 0 (bitsRoot (c + 6) bs)] ++ bitCells (c + 6) bs sks := rfl

/-- **The output's bits read back** as `bl (decB bs)`: the rewritten
    `Cons` cells at `c`, over the input's `S` and `S I` cells and its
    shared tail. -/
theorem bits_ot {H cs : List Cell} (hs : slotsOK (H ++ cs) = true) :
    ∀ (bs : List Bool) (sks : List ConsSk) (c n p F : Nat) (u : OTerm), canonB bs = true → bs ≠ [] →
      readBits H n p = some (bs, sks) → otermAt H F p = some u →
      (∀ i, i < (bitCells c bs sks).length → (H ++ cs)[c + i]? = (bitCells c bs sks)[i]?) →
      ∀ G, F + 1 ≤ G → otermAt (H ++ cs) G (bitsRoot c bs) = some (bl (decB bs)).toO
  | [], _, _, _, _, _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | b :: bs, sks, c, n, p, F, u, hcan, _, hr, hu, hcells, G, hG => by
    cases n with
    | zero => cases hr
    | succ n =>
      unfold readBits at hr
      split at hr
      · cases hr
      · cases hc : readCons H p with
        | none => rw [hc] at hr; cases hr
        | some q =>
          obtain ⟨b', sk⟩ := q
          rw [hc] at hr
          dsimp only at hr
          cases hr' : readBits H n sk.t with
          | none => rw [hr'] at hr; cases hr
          | some q' =>
            obtain ⟨bs', sks'⟩ := q'
            rw [hr'] at hr
            have e := Option.some.inj hr
            have eb := List.cons.inj (congrArg Prod.fst e)
            have es : sk :: sks' = sks := congrArg Prod.snd e
            subst es
            obtain ⟨eb1, eb2⟩ := eb
            subst eb1 eb2
            obtain ⟨f, tt, rfl, hf2, rfl, htt, hss, hc5⟩ := readCons_peel hc hu
            have htt' : tt = (bl bs').toO := readBits_ot hr' htt
            subst htt'
            have hK := K_ot (slots_K hs) (F := 1) (Nat.le_refl _)
            have hS : otermAt (H ++ cs) 1 sk.s = some .S :=
              S_ot (H := H ++ cs) (by
                unfold isS
                rw [List.getElem?_append_left (by
                  have := isS_eq hss; rw [List.getElem?_eq_some_iff] at this; exact this.1)]
                exact hss) (F := 1) (Nat.le_refl _)
            have hSI := otermAt_append (cs := cs) (isSI_ot hc5 (F := 2) (Nat.le_refl _))
            cases b' with
            | false =>
              have hne : bs' ≠ [] := by cases bs' with | nil => cases hcan | cons _ _ => exact List.cons_ne_nil _ _
              rw [bitCells_cons_false] at hcells
              have cell : ∀ i, i < 6 → (H ++ cs)[c + i]? =
                  [Cell.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 0,
                   .app 0 (bitsRoot (c + 6) bs')][i]? := fun i hi => by
                rw [hcells i (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
                  List.getElem?_append_left (by simp only [List.length_cons, List.length_nil]; omega)]
              have ih := bits_ot hs bs' sks' (c + 6) n sk.t (f + 1) (bl bs').toO (canonB_cons hcan hne) hne hr' htt
                (fun i hi => by
                  have := hcells (6 + i) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                  rw [show c + (6 + i) = c + 6 + i by omega] at this
                  rw [this, show 6 + i = i + 6 by omega]
                  rfl) (G - 3) (by omega)
              show otermAt (H ++ cs) G (if dropped (false :: bs') then 0 else c) = _
              rw [show dropped (false :: bs') = false from rfl, if_neg (by decide)]
              show otermAt (H ++ cs) G c = some (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)) ⬝ₒ (.K ⬝ₒ (bl (decB bs')).toO)))
              refine app_ot (F := G) (g := G - 1) (cell 0 (by omega)) hK ?_ (by omega) (by omega)
              refine app_ot (F := G - 1) (f := G - 2) (g := G - 2) (cell 1 (by omega)) ?_ ?_ (by omega) (by omega)
              · refine app_ot (F := G - 2) (g := G - 3) (cell 2 (by omega)) hS ?_ (by omega) (by omega)
                refine app_ot (F := G - 3) (g := G - 4) (cell 3 (by omega)) hSI ?_ (by omega) (by omega)
                exact app_ot (F := G - 4) (cell 4 (by omega)) hK hK (by omega) (by omega)
              · exact app_ot (F := G - 2) (cell 5 (by omega)) hK ih (by omega) (by omega)
            | true =>
              cases bs' with
              | nil =>
                show otermAt (H ++ cs) G (if dropped [true] then 0 else c) = some (bl []).toO
                rw [show dropped [true] = true from rfl, if_pos rfl]
                exact K_ot (slots_K hs) (F := G) (by omega)
              | cons b2 bs2 =>
                have hcl : bitCells c (true :: b2 :: bs2) (sk :: sks') =
                    [.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 2,
                     .app 0 sk.t] := by
                  show (if b2 :: bs2 = [] then [] else _) = _
                  rw [if_neg (List.cons_ne_nil _ _)]
                rw [hcl] at hcells
                have cell : ∀ i, i < 6 → (H ++ cs)[c + i]? =
                    [Cell.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 2,
                     .app 0 sk.t][i]? := fun i hi => hcells i (by simp only [List.length_cons, List.length_nil]; omega)
                show otermAt (H ++ cs) G (if dropped (true :: b2 :: bs2) then 0 else c) = _
                rw [show dropped (true :: b2 :: bs2) = false from rfl, if_neg (by decide)]
                have htail := otermAt_append (cs := cs) htt
                have hd : decB (true :: b2 :: bs2) = false :: b2 :: bs2 := by
                  show (if b2 :: bs2 = [] then [] else _) = _
                  rw [if_neg (List.cons_ne_nil _ _)]
                rw [hd]
                show otermAt (H ++ cs) G c = some (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))) ⬝ₒ (.K ⬝ₒ (bl (b2 :: bs2)).toO)))
                refine app_ot (F := G) (g := G - 1) (cell 0 (by omega)) hK ?_ (by omega) (by omega)
                refine app_ot (F := G - 1) (f := G - 2) (g := G - 2) (cell 1 (by omega)) ?_ ?_ (by omega) (by omega)
                · refine app_ot (F := G - 2) (g := G - 3) (cell 2 (by omega)) hS ?_ (by omega) (by omega)
                  refine app_ot (F := G - 3) (g := G - 4) (cell 3 (by omega)) hSI ?_ (by omega) (by omega)
                  exact app_ot (F := G - 4) (cell 4 (by omega)) hK (slot2_ot hs (F := 2) (Nat.le_refl _)) (by omega) (by omega)
                · exact app_ot (F := G - 2) (cell 5 (by omega)) hK htail (by omega) (by omega)

/-- **The subject read back**: its encoding. -/
theorem readSubj_ot {H : List Cell} {p : Nat} {s : Nn} {csk : Option CellSk} {ask : Option AtomSk}
    {sks : List ConsSk} (h : readSubj H p = some (s, csk, ask, sks)) {F : Nat} {u : OTerm}
    (hu : otermAt H F p = some u) : u = (encNn s).toO := by
  unfold readSubj at h
  cases ha : readAtom H p with
  | some sk =>
    rw [ha] at h
    dsimp only at h
    cases hb : readBits H H.length sk.b with
    | none => rw [hb] at h; cases h
    | some q =>
      obtain ⟨bs, sks'⟩ := q
      rw [hb] at h
      dsimp only at h
      split at h
      · cases h
        obtain ⟨f, tb, rfl, rfl, htb, _⟩ := readAtom_peel ha hu
        rw [readBits_ot hb htb]; rfl
      · cases h
  | none =>
    rw [ha] at h
    dsimp only at h
    cases hc : readCell H p with
    | none => rw [hc] at h; cases h
    | some csk' =>
      rw [hc] at h
      dsimp only at h
      obtain ⟨f, th, tt, rfl, rfl, hth, htt, _⟩ := readCell_peel hc hu
      cases ha2 : readAtom H csk'.h with
      | some ask' =>
        rw [ha2] at h
        dsimp only at h
        cases hb : readBits H H.length ask'.b with
        | none => rw [hb] at h; cases h
        | some q =>
          obtain ⟨bs, sks'⟩ := q
          rw [hb] at h
          dsimp only at h
          split at h
          · cases ht : readNn H H.length csk'.t with
            | none => rw [ht] at h; cases h
            | some r =>
              rw [ht] at h
              cases h
              obtain ⟨f', tb, rfl, rfl, htb, _⟩ := readAtom_peel ha2 hth
              rw [readBits_ot hb htb, readNn_ot ht htt]; rfl
          · cases h
      | none =>
        rw [ha2] at h
        dsimp only at h
        cases hh : readNn H H.length csk'.h with
        | none => rw [hh] at h; cases h
        | some hh' =>
          cases ht : readNn H H.length csk'.t with
          | none => rw [hh, ht] at h; cases h
          | some tt' =>
            rw [hh, ht] at h
            cases h
            rw [readNn_ot hh hth, readNn_ot ht htt]; rfl

/-- A read subject is well formed. -/
theorem readSubj_wf {H : List Cell} {p : Nat} {s : Nn} {csk : Option CellSk} {ask : Option AtomSk}
    {sks : List ConsSk} (h : readSubj H p = some (s, csk, ask, sks)) : s.wf = true := by
  unfold readSubj at h
  cases ha : readAtom H p with
  | some sk =>
    rw [ha] at h
    dsimp only at h
    cases hb : readBits H H.length sk.b with
    | none => rw [hb] at h; cases h
    | some q =>
      obtain ⟨bs, sks'⟩ := q
      rw [hb] at h
      dsimp only at h
      split at h
      · cases h; assumption
      · cases h
  | none =>
    rw [ha] at h
    dsimp only at h
    cases hc : readCell H p with
    | none => rw [hc] at h; cases h
    | some csk' =>
      rw [hc] at h
      dsimp only at h
      cases ha2 : readAtom H csk'.h with
      | some ask' =>
        rw [ha2] at h
        dsimp only at h
        cases hb : readBits H H.length ask'.b with
        | none => rw [hb] at h; cases h
        | some q =>
          obtain ⟨bs, sks'⟩ := q
          rw [hb] at h
          dsimp only at h
          split at h
          · rename_i hcan
            cases ht : readNn H H.length csk'.t with
            | none => rw [ht] at h; cases h
            | some r =>
              rw [ht] at h
              cases h
              show (canonB bs && r.wf) = true
              rw [hcan, readNn_wf ht]; rfl
          · cases h
      | none =>
        rw [ha2] at h
        dsimp only at h
        cases hh : readNn H H.length csk'.h with
        | none => rw [hh] at h; cases h
        | some hh' =>
          cases ht : readNn H H.length csk'.t with
          | none => rw [hh, ht] at h; cases h
          | some tt' =>
            rw [hh, ht] at h
            cases h
            show (hh'.wf && tt'.wf) = true
            rw [readNn_wf hh, readNn_wf ht]; rfl

/-- The input's `S (K K)`, `S` and `S I` cells read back in the extended heap. -/
theorem isSKK_ot' {H cs : List Cell} {a : Nat} (h : isSKK H a = true) {F : Nat} (hF : 3 ≤ F) :
    otermAt (H ++ cs) F a = some (.S ⬝ₒ (.K ⬝ₒ .K)) := otermAt_append (isSKK_ot h hF)
theorem isSI_ot' {H cs : List Cell} {a : Nat} (h : isSI H a = true) {F : Nat} (hF : 2 ≤ F) :
    otermAt (H ++ cs) F a = some (.S ⬝ₒ .I) := otermAt_append (isSI_ot h hF)
theorem isS_ot' {H cs : List Cell} {a : Nat} (h : isS H a = true) {F : Nat} (hF : 1 ≤ F) :
    otermAt (H ++ cs) F a = some .S := otermAt_append (S_ot h hF)

/-- **The output `Cell` wrapper reads back** as `cellO` of its head's
    read-back and the input's tail. -/
theorem cell_ot {H cs : List Cell} (hs : slotsOK (H ++ cs) = true) (csk : CellSk) (c : Nat)
    (hcell : ∀ i, i < 7 → (H ++ cs)[c + i]? = (cellCells c csk)[i]?)
    (ha1 : isSKK H csk.a1 = true) (ha2 : isSKK H csk.a2 = true) (hs3 : isS H csk.s3 = true)
    (hsi : isSI H csk.si = true) {fk : Nat} {tt : OTerm} (hkt : otermAt H fk csk.kt = some (.K ⬝ₒ tt))
    {fh : Nat} {th : OTerm} (hh : otermAt (H ++ cs) fh (c + 7) = some th) {G : Nat}
    (hG1 : fk + 4 ≤ G) (hG2 : fh + 7 ≤ G) (hG3 : 8 ≤ G) : otermAt (H ++ cs) G c = some (cellO th tt) := by
  have hK := K_ot (slots_K hs) (F := 1) (Nat.le_refl _)
  have hkt' := otermAt_append (cs := cs) hkt
  show otermAt (H ++ cs) G c = some (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ
    (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ th)) ⬝ₒ (.K ⬝ₒ tt)))))
  refine app_ot (F := G) (g := G - 1) (hcell 0 (by omega)) hK ?_ (by omega) (by omega)
  refine app_ot (F := G - 1) (g := G - 2) (hcell 1 (by omega)) (isSKK_ot' ha1 (F := 3) (Nat.le_refl _)) ?_ (by omega) (by omega)
  refine app_ot (F := G - 2) (g := G - 3) (hcell 2 (by omega)) (isSKK_ot' ha2 (F := 3) (Nat.le_refl _)) ?_ (by omega) (by omega)
  refine app_ot (F := G - 3) (f := G - 4) (hcell 3 (by omega)) ?_ hkt' (by omega) (by omega)
  refine app_ot (F := G - 4) (g := G - 5) (hcell 4 (by omega)) (isS_ot' hs3 (F := 1) (Nat.le_refl _)) ?_ (by omega) (by omega)
  refine app_ot (F := G - 5) (g := G - 6) (hcell 5 (by omega)) (isSI_ot' hsi (F := 2) (Nat.le_refl _)) ?_ (by omega) (by omega)
  exact app_ot (F := G - 6) (hcell 6 (by omega)) hK hh (by omega) (by omega)

/-- **The output `Atom` wrapper reads back** as `atomO` of its bits'. -/
theorem atom_ot {H cs : List Cell} (hs : slotsOK (H ++ cs) = true) (ask : AtomSk) (c root : Nat)
    (hcell : ∀ i, i < 5 → (H ++ cs)[c + i]? = (atomCells c ask root)[i]?)
    (ha1 : isSKK H ask.a1 = true) (ha2 : isSKK H ask.a2 = true) (ha3 : isSKK H ask.a3 = true)
    (hsi : isSI H ask.si = true) {fb : Nat} {tb : OTerm} (hb : otermAt (H ++ cs) fb root = some tb) {G : Nat}
    (hG1 : fb + 5 ≤ G) (hG2 : 6 ≤ G) : otermAt (H ++ cs) G c = some (atomO tb) := by
  have hK := K_ot (slots_K hs) (F := 1) (Nat.le_refl _)
  show otermAt (H ++ cs) G c = some (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ
    (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ tb)))))
  refine app_ot (F := G) (g := G - 1) (hcell 0 (by omega)) (isSKK_ot' ha1 (F := 3) (Nat.le_refl _)) ?_ (by omega) (by omega)
  refine app_ot (F := G - 1) (g := G - 2) (hcell 1 (by omega)) (isSKK_ot' ha2 (F := 3) (Nat.le_refl _)) ?_ (by omega) (by omega)
  refine app_ot (F := G - 2) (g := G - 3) (hcell 2 (by omega)) (isSKK_ot' ha3 (F := 3) (Nat.le_refl _)) ?_ (by omega) (by omega)
  refine app_ot (F := G - 3) (g := G - 4) (hcell 3 (by omega)) (isSI_ot' hsi (F := 2) (Nat.le_refl _)) ?_ (by omega) (by omega)
  exact app_ot (F := G - 4) (hcell 4 (by omega)) hK hb (by omega) (by omega)

theorem getElem?_after12 {l1 l2 : List Cell} (h : l1.length = 12) (i : Nat) : (l1 ++ l2)[12 + i]? = l2[i]? := by
  rw [List.getElem?_append_right (by omega), h, Nat.add_sub_cancel_left]

theorem cellCells_length (c : Nat) (sk : CellSk) : (cellCells c sk).length = 7 := rfl
theorem atomCells_length (c : Nat) (sk : AtomSk) (r : Nat) : (atomCells c sk r).length = 5 := rfl
theorem errCells_length (c : Nat) : (errCells c).length = 3 := rfl

-- ---------------------------------------------------------------------------
-- A row, read back
-- ---------------------------------------------------------------------------

theorem JStep.appL {α β : Type} {cc : DataJet.Contract α β} {j : Nat} :
    ∀ (as : List OTerm) {t u : OTerm}, DataJet.JStep cc j t u → DataJet.JStep cc j (_root_.appL t as) (_root_.appL u as)
  | [], _, _, h => h
  | a :: as, _, _, h => JStep.appL as (.left a h)

/-- The output read back, case by case, from the subject's cells. -/
theorem out_ot {H cs : List Cell} (hs : slotsOK H = true) {p : Nat} {s : Nn} {csk : Option CellSk} {ask : Option AtomSk}
    {sks : List ConsSk} (hr : readSubj H p = some (s, csk, ask, sks)) {root : Nat}
    (hout : outCells H.length s csk ask sks = some (cs, root)) {N : OTerm}
    (hN : otermAt H (H.length + 1) p = some N) :
    otermAt (H ++ cs) ((H ++ cs).length + 1) root = some (encO (decSpec s)).toO := by
  have hs' := slotsOK_append (cs := cs) hs
  have hcell : ∀ i, i < cs.length → (H ++ cs)[H.length + i]? = cs[i]? := fun i _ => at_written rfl
  have hlen : (H ++ cs).length = H.length + cs.length := List.length_append ..
  unfold readSubj at hr
  cases ha : readAtom H p with
  | some sk =>
    rw [ha] at hr
    dsimp only at hr
    cases hb : readBits H H.length sk.b with
    | none => rw [hb] at hr; cases hr
    | some q =>
      obtain ⟨bs, sks'⟩ := q
      rw [hb] at hr
      dsimp only at hr
      split at hr
      · cases hr
        -- an atom subject: `errT`
        unfold outCells at hout
        cases hout
        rw [hlen, errCells_length]
        exact err_ot hs' (hcell 0 (by rw [errCells_length]; omega)) (hcell 1 (by rw [errCells_length]; omega))
          (hcell 2 (by rw [errCells_length]; omega)) (by omega)
      · cases hr
  | none =>
    rw [ha] at hr
    dsimp only at hr
    cases hc : readCell H p with
    | none => rw [hc] at hr; cases hr
    | some csk' =>
      rw [hc] at hr
      dsimp only at hr
      obtain ⟨f, th, tt, hF, rfl, hth, htt, hkt, ha1, ha2, hs3, hsi⟩ := readCell_peel hc hN
      cases ha2' : readAtom H csk'.h with
      | some ask' =>
        rw [ha2'] at hr
        dsimp only at hr
        cases hb : readBits H H.length ask'.b with
        | none => rw [hb] at hr; cases hr
        | some q =>
          obtain ⟨bs, sks'⟩ := q
          rw [hb] at hr
          dsimp only at hr
          split at hr
          · rename_i hcan
            cases ht : readNn H H.length csk'.t with
            | none => rw [ht] at hr; cases hr
            | some r0 =>
              rw [ht] at hr
              cases hr
              obtain ⟨f', tb, rfl, rfl, htb, hb1, hb2, hb3, hbsi⟩ := readAtom_peel ha2' hth
              have htb' := readBits_ot hb htb
              subst htb'
              have htt' := readNn_ot ht htt
              subst htt'
              have hf' := otermAt_pos htb
              cases bs with
              | nil =>
                -- `[0 r]`: `errT` at `c + 12`
                unfold outCells at hout
                cases hout
                have hl15 : (cellCells H.length csk' ++ atomCells (H.length + 7) ask' 0 ++ errCells (H.length + 12)).length = 15 := by
                  simp only [List.length_append, cellCells_length, atomCells_length, errCells_length]
                rw [hlen, hl15]
                exact err_ot hs' (hcell 12 (by rw [hl15]; omega)) (hcell 13 (by rw [hl15]; omega))
                  (hcell 14 (by rw [hl15]; omega)) (by omega)
              | cons b bs =>
                unfold outCells at hout
                cases hout
                rw [hlen]
                -- the bits, then the wrappers over them
                generalize hL : (cellCells H.length csk' ++ atomCells (H.length + 7) ask' (bitsRoot (H.length + 12) (b :: bs)) ++
                    bitCells (H.length + 12) (b :: bs) sks).length = L at hcell hlen
                have hL12 : 12 + (bitCells (H.length + 12) (b :: bs) sks).length = L := by
                  rw [← hL]; simp only [List.length_append, cellCells_length, atomCells_length]
                have hbits := bits_ot (G := H.length + L + 1 - 12) hs' (b :: bs) sks (H.length + 12) H.length ask'.b f'
                  (bl (b :: bs)).toO hcan (List.cons_ne_nil _ _) hb htb
                  (fun i hi => by
                    rw [show H.length + 12 + i = H.length + (12 + i) by omega, hcell (12 + i) (by omega),
                      getElem?_after12 (by simp only [List.length_append, cellCells_length, atomCells_length])])
                  (by omega)
                have hatom := atom_ot (G := H.length + L + 1 - 7) hs' ask' (H.length + 7) (bitsRoot (H.length + 12) (b :: bs))
                  (fun i hi => by
                    rw [show H.length + 7 + i = H.length + (7 + i) by omega, hcell (7 + i) (by omega),
                      List.getElem?_append_left (by simp only [List.length_append, cellCells_length, atomCells_length]; omega),
                      List.getElem?_append_right (by rw [cellCells_length]; omega),
                      cellCells_length, show 7 + i - 7 = i by omega])
                  hb1 hb2 hb3 hbsi hbits (by omega) (by omega)
                have hcellT := cell_ot (G := H.length + L + 1) hs' csk' H.length
                  (fun i hi => by
                    rw [hcell i (by omega),
                      List.getElem?_append_left (by simp only [List.length_append, cellCells_length, atomCells_length]; omega),
                      List.getElem?_append_left (by rw [cellCells_length]; omega)])
                  ha1 ha2 hs3 hsi hkt hatom (by omega) (by omega) (by omega)
                exact hcellT
          · cases hr
      | none =>
        rw [ha2'] at hr
        dsimp only at hr
        cases hh : readNn H H.length csk'.h with
        | none => rw [hh] at hr; cases hr
        | some hh' =>
          cases ht : readNn H H.length csk'.t with
          | none => rw [hh, ht] at hr; cases hr
          | some tt' =>
            rw [hh, ht] at hr
            cases hr
            -- a cell head: `errT` at `c + 12`
            cases hh' with
            | atom b =>
              -- the head read back as an atom, but `readAtom` failed: impossible
              exfalso
              cases hn : H.length with
              | zero => rw [hn] at hh; cases hh
              | succ n =>
                rw [hn] at hh
                unfold readNn at hh
                rw [ha2'] at hh
                dsimp only at hh
                cases hc2 : readCell H csk'.h with
                | none => rw [hc2] at hh; cases hh
                | some _ =>
                  rw [hc2] at hh
                  dsimp only at hh
                  split at hh <;> cases hh
            | cell h1 t1 =>
              unfold outCells at hout
              cases hout
              have hl15 : (cellCells H.length csk' ++ List.replicate 5 (Cell.app 0 0) ++ errCells (H.length + 12)).length = 15 := by
                simp only [List.length_append, cellCells_length, List.length_replicate, errCells_length]
              rw [hlen, hl15]
              exact err_ot hs' (hcell 12 (by rw [hl15]; omega)) (hcell 13 (by rw [hl15]; omega))
                (hcell 14 (by rw [hl15]; omega)) (by omega)

theorem decRow_unfold {M : List Cell} {J : Nat} {r r' : Row} (h : decRow M J r = some r') :
    let H := M.take r.ctr
    ∃ p rest s csk ask sks cells root, H[r.hd]? = some (.atom J) ∧ slotsOK H = true ∧
      popN H 1 r.stk = some ([p], rest) ∧ readSubj H p = some (s, csk, ask, sks) ∧ headFits s = true ∧
      outCells r.ctr s csk ask sks = some (cells, root) ∧ wrs M r.ctr cells = true ∧
      r' = ⟨root, rest, r.ctr + cells.length⟩ := by
  unfold decRow at h
  dsimp only at h ⊢
  generalize M.take r.ctr = H at h ⊢
  cases hhd : H[r.hd]? with
  | none => rw [hhd] at h; cases h
  | some cell =>
    rw [hhd] at h
    cases cell with
    | atom j' =>
      dsimp only at h
      by_cases hcond : j' = J ∧ slotsOK H = true
      · rw [if_pos hcond] at h
        obtain ⟨rfl, hs⟩ := hcond
        cases hpop : popN H 1 r.stk with
        | none => rw [hpop] at h; cases h
        | some q =>
          obtain ⟨qs, rest⟩ := q
          rw [hpop] at h
          match qs, h with
          | [p], h =>
            dsimp only at h
            cases hrd : readSubj H p with
            | none => rw [hrd] at h; cases h
            | some q4 =>
              obtain ⟨s, csk, ask, sks⟩ := q4
              rw [hrd] at h
              dsimp only at h
              by_cases hfit : headFits s = true
              · rw [if_pos hfit] at h
                cases hout : outCells r.ctr s csk ask sks with
                | none => rw [hout] at h; cases h
                | some q2 =>
                  obtain ⟨cells, root⟩ := q2
                  rw [hout] at h
                  dsimp only at h
                  cases hw : wrs M r.ctr cells with
                  | false => rw [hw] at h; cases h
                  | true =>
                    rw [hw] at h
                    cases h
                    exact ⟨p, rest, s, csk, ask, sks, cells, root, rfl, hs, rfl, hrd, hfit, hout, hw, rfl⟩
              · rw [if_neg hfit] at h; cases h
          | [], h => cases h
          | _ :: _ :: _, h => cases h
      · rw [if_neg hcond] at h; cases h
    | _ => cases h

/-- **A jet row, read back**: the state is `J ⬝ encNn s ⬝ R` for a subject
    `s` in the domain, and the next state `encO (decSpec s) ⬝ R`. -/
theorem decRow_step {M : List Cell} {J : Nat} {r r' : Row} (h : decRow M J r = some r') (hc : r.ctr ≤ M.length)
    {t : OTerm} (hdec : odecode (st M r) = some t) :
    r'.ctr ≤ M.length ∧ ∃ (s : Dom) (R : List OTerm), t = _root_.appL (.var J) ((encNn s.1).toO :: R) ∧
      odecode (st M r') = some (_root_.appL (encO (decSpec s.1)).toO R) := by
  obtain ⟨p, rest, s, csk, ask, sks, cells, root, hhd, hs, hpop, hrd, hfit, hout, hw, rfl⟩ := decRow_unfold h
  generalize hH : M.take r.ctr = H at hhd hs hpop hrd hout
  have hHl : H.length = r.ctr := by rw [← hH, List.length_take]; omega
  have htake := take_of_wrs hw
  rw [hH] at htake
  have hlen' : (M.take (r.ctr + cells.length)).length = r.ctr + cells.length := by
    rw [htake, List.length_append, hHl]
  refine ⟨?_, ?_⟩
  · show r.ctr + cells.length ≤ M.length
    rw [List.length_take] at hlen'
    omega
  · obtain ⟨hdt, args, h1, h2, rfl⟩ := odecode_eq hdec
    replace h1 : otermAt H (H.length + 1) r.hd = some hdt := by rw [← hH]; exact h1
    replace h2 : ostackAt H (H.length + 1) r.stk = some args := by rw [← hH]; exact h2
    have hj : hdt = .var J := by
      unfold otermAt at h1; rw [hhd] at h1; cases h1; rfl
    obtain ⟨Ns, R, G, hG, hargs, hNl, hpl, hok, hR⟩ := popN_ospec 1 hpop h2
    match Ns, hNl, hok with
    | [N], _, ⟨hN, _⟩ =>
      have hNe := readSubj_ot hrd hN
      subst hNe
      rw [← hHl] at hout
      have hroot := out_ot hs hrd hout hN
      refine ⟨⟨s, readSubj_wf hrd, hfit⟩, R, by rw [hargs, hj]; rfl, ?_⟩
      show odecode ⟨M.take (r.ctr + cells.length), root, rest⟩ = _
      rw [htake]
      apply odecode_of hroot
      exact ostackAt_grow hR (by rw [List.length_append]; omega)

/-- **A jet row reads back as one step of the contract's reduction.** -/
theorem decRow_cstep {M : List Cell} {J : Nat} {r r' : Row} (h : decRow M J r = some r') (hc : r.ctr ≤ M.length)
    {t : OTerm} (hdec : odecode (st M r) = some t) :
    r'.ctr ≤ M.length ∧ ∃ t', odecode (st M r') = some t' ∧ DataJet.JStep decContract J t t' := by
  obtain ⟨h1, s, R, rfl, hd⟩ := decRow_step h hc hdec
  refine ⟨h1, _, hd, ?_⟩
  have hjet := DataJet.JStep.jet (c := decContract) (j := J) s
  rw [show _root_.appL (OTerm.var J) ((encNn s.1).toO :: R) = _root_.appL (.var J ⬝ₒ (encNn s.1).toO) R from rfl]
  exact JStep.appL R hjet

/-- A jet row moves the counter forward and stays within the memory. -/
theorem decRow_ctr_len {M : List Cell} {J : Nat} {r r' : Row} (h : decRow M J r = some r')
    (hc : r.ctr ≤ M.length) : r.ctr ≤ r'.ctr ∧ r'.ctr ≤ M.length := by
  obtain ⟨_, _, _, _, _, _, cells, _, _, _, _, _, _, _, hw, rfl⟩ := decRow_unfold h
  have ht := take_of_wrs hw
  have hl := congrArg List.length ht
  rw [List.length_take, List.length_append, List.length_take] at hl
  exact ⟨Nat.le_add_right _ _, by show r.ctr + cells.length ≤ M.length; omega⟩

-- ---------------------------------------------------------------------------
-- Elimination: a value selects its continuation (skinock's `Noun.lean`)
-- ---------------------------------------------------------------------------

theorem atomT_abs (b : Term) :
    atomT b = (absN [1, 2, 3, 4] (.var 1 ⬝ₒ .var 0)).close (fun _ => b) := rfl

theorem cellT_abs (h t : Term) :
    cellT h t = (absN [2, 3, 4, 5] (.var 3 ⬝ₒ .var 0 ⬝ₒ .var 1)).close
      (fun i => if i = 0 then h else t) := rfl

theorem errT_abs : errT = (absN [0, 1, 2, 3] (.var 3)).close (fun _ => K) := rfl

theorem atomT_elim (b a c f e : Term) : WSteps (atomT b ⬝ a ⬝ c ⬝ f ⬝ e) (a ⬝ b) := by
  rw [atomT_abs]
  exact absN_beta_close [1, 2, 3, 4] _ (fun _ => b) [a, c, f, e] rfl

theorem cellT_elim (h t a c f e : Term) : WSteps (cellT h t ⬝ a ⬝ c ⬝ f ⬝ e) (c ⬝ h ⬝ t) := by
  rw [cellT_abs]
  exact absN_beta_close [2, 3, 4, 5] _ (fun i => if i = 0 then h else t) [a, c, f, e] rfl

theorem errT_elim (a c f e : Term) : WSteps (errT ⬝ a ⬝ c ⬝ f ⬝ e) e := by
  rw [errT_abs]
  exact absN_beta_close [0, 1, 2, 3] _ (fun _ => K) [a, c, f, e] rfl

end DecJet
