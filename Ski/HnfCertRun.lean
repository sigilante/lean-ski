import Ski.HnfCertData

/-!
# The checker for hypothesis (A): computable definitions

A transcription of `notes/checks/s15/cert/kcheck.py` (replay mode).  All recursion is structural
(on `fuel` for runs), so the kernel can evaluate it.  A product state is coded
`class * 64 + block`; tables are big `Nat` literals read by shifts.  Size forms are linear in the
sizes of at most five root variable occurrences.
-/

namespace HnfCert

def γN (a b : Nat) : Nat := (CTN >>> (6 * (a * 39 + b))) % 64
def βN (a b : Nat) : Nat := (BTN >>> (6 * (a * 38 + b))) % 64
/-- Product of two state codes. -/
def dxN (s t : Nat) : Nat := γN (s / 64) (t / 64) * 64 + βN (s % 64) (t % 64)
def accN (s : Nat) : Bool := s / 64 != 37

def mkV (s : Nat) : CT := if s == 0 then .S else .V s

def CT.st : CT → Nat
  | .S => 0
  | .V s => s
  | .A l r => dxN l.st r.st

def npair (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

def CT.code : CT → Nat
  | .S => 1
  | .V s => 2 + 4 * s
  | .A l r => 3 + 4 * npair l.code r.code

def CBST.find : CBST → Nat → List Claim
  | .leaf, _ => []
  | .node k items l r, key => if key == k then items else if key < k then l.find key else r.find key

/-- The claims whose term is `t`. -/
def lookup (t : CT) : List Claim := (CBST_.find t.code).filter (fun c => c.term == t)

def exactB (b : Nat) : Option Nat := (EXACTT.find? (fun p => p.1 == b)).map (·.2)
def minsz (s : Nat) : Nat := match MINSZT.find? (fun p => p.1 == s) with | some p => p.2 | none => 1
def unf (s : Nat) : List Shape := match UNFT.find? (fun p => p.1 == s) with | some p => p.2 | none => []
/-- Accepted pairs `(p, q)` with `dxN p q = s`. -/
def splits (s : Nat) : List (Nat × Nat) := match SPLT.find? (fun p => p.1 == s) with | some p => p.2 | none => []

/-! ## Size forms over five root variables -/

structure Form where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  c : Int

def Form.const (c : Int) : Form := ⟨0, 0, 0, 0, 0, c⟩
def Form.unit : Nat → Form
  | 0 => ⟨1, 0, 0, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0, 0, 0⟩
  | 3 => ⟨0, 0, 0, 1, 0, 0⟩
  | 4 => ⟨0, 0, 0, 0, 1, 0⟩
  | _ => ⟨0, 0, 0, 0, 0, 0⟩
def Form.add (a b : Form) : Form :=
  ⟨a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2, a.a3 + b.a3, a.a4 + b.a4, a.c + b.c⟩
def Form.shift (a : Form) (k : Int) : Form := ⟨a.a0, a.a1, a.a2, a.a3, a.a4, a.c + k⟩

def oadd : Option Form → Option Form → Option Form
  | some a, some b => some (a.add b)
  | _, _ => none

/-- Five root sizes (or their lower bounds). -/
structure Sz where
  s0 : Int
  s1 : Int
  s2 : Int
  s3 : Int
  s4 : Int

def Form.eval (f : Form) (s : Sz) : Int :=
  f.a0 * s.s0 + f.a1 * s.s1 + f.a2 * s.s2 + f.a3 * s.s3 + f.a4 * s.s4 + f.c

/-- 2: at most root − 1 for all sizes ≥ mins; 1: at most root; 0: unknown. -/
def grade (f : Option Form) (root : Form) (mins : Sz) : Nat :=
  match f with
  | none => 0
  | some f =>
    if root.a0 - f.a0 < 0 || root.a1 - f.a1 < 0 || root.a2 - f.a2 < 0 || root.a3 - f.a3 < 0 ||
        root.a4 - f.a4 < 0 then 0
    else
      let mn := (root.a0 - f.a0) * mins.s0 + (root.a1 - f.a1) * mins.s1 + (root.a2 - f.a2) * mins.s2 +
        (root.a3 - f.a3) * mins.s3 + (root.a4 - f.a4) * mins.s4 + root.c - f.c
      if mn ≥ 1 then 2 else if mn ≥ 0 then 1 else 0

/-! ## Run terms: leaves carry size forms, applications cache their state -/

inductive RT
  | S
  | V (s : Nat) (f : Option Form)
  | A (l r : RT) (s : Nat)

def RT.st : RT → Nat
  | .S => 0
  | .V s _ => s
  | .A _ _ s => s

def mkA (l r : RT) : RT := .A l r (dxN l.st r.st)
def mkVR (s : Nat) (f : Option Form) : RT := if s == 0 then .S else .V s f

def RT.sz : RT → Option Form
  | .S => some (Form.const 1)
  | .V _ f => f
  | .A l r _ => oadd l.sz r.sz

def RT.hasBot : RT → Bool
  | .S => false
  | .V s _ => s % 64 == 36
  | .A l r s => s % 64 == 36 || l.hasBot || r.hasBot

def RT.gen : RT → CT
  | .S => .S
  | .V s _ => mkV s
  | .A l r s => if accN s then mkV s else .A l.gen r.gen

def RT.spine : RT → RT × List RT
  | .A l r _ => let p := l.spine; (p.1, p.2 ++ [r])
  | t => (t, [])

def build (h : RT) (args : List RT) : RT := args.foldl mkA h

structure Ctx where
  stratum : Nat
  rank : Nat
  root : Form
  mins : Sz

def claimOK (cx : Ctx) (g : Nat) (t : CT) : Bool :=
  (lookup t).any fun d =>
    d.stratum < cx.stratum || (d.stratum == cx.stratum && (g == 2 || (g == 1 && d.rank < cx.rank)))

/-- A minimal rejected node whose pair claim is lower, or equal-stratum and strictly smaller. -/
def pairClose (cx : Ctx) : RT → Bool
  | .S => false
  | .V _ _ => false
  | .A l r s =>
    if accN s then false
    else if accN l.st && accN r.st then
      (lookup (.A (mkV l.st) (mkV r.st))).any fun d =>
        d.stratum < cx.stratum || (d.stratum == cx.stratum && grade (oadd l.sz r.sz) cx.root cx.mins == 2)
    else pairClose cx l || pairClose cx r

/-- The hnf shape that replaces a head variable whose instance has size form `f`. -/
def shapeTerm (f : Option Form) : Shape → RT
  | .s0 => .S
  | .s1 a =>
    let z1 := match exactB (a % 64) with
      | some v => some (Form.const v)
      | none => f.map (·.shift (-1))
    mkA .S (mkVR a z1)
  | .s2 a b =>
    let z1 := (exactB (a % 64)).map (fun (v : Nat) => Form.const (v : Int))
    let z2 := match exactB (b % 64) with
      | some v => some (Form.const v)
      | none => if a % 64 == 0 || a % 64 == 1 then f.map (·.shift (-2)) else none
    mkA (mkA .S (mkVR a z1)) (mkVR b z2)

/-- One hnf descent: consume a hint, then close the chosen rejected argument by a claim (`2 i`) or
descend into it with `rec` (`2 i + 1`). -/
def hnfStep (cx : Ctx) (rec : Nat → RT → List Nat → Option (List Nat)) (dl : Nat) (args : List RT) :
    List Nat → Option (List Nat)
  | [] => none
  | h :: hs' =>
    match args[h / 2]? with
    | none => none
    | some a =>
      if accN a.st then none
      else if h % 2 == 0 then
        (if claimOK cx (grade a.sz cx.root cx.mins) a.gen then some hs' else none)
      else if dl > 0 then rec (dl - 1) a hs'
      else none

/-- Replay a run, consuming hints at hnf descents; `some rest` on success. -/
def run (cx : Ctx) : Nat → Nat → RT → List Nat → Option (List Nat)
  | 0, _, _, _ => none
  | fuel + 1, dl, t, hs =>
    if t.hasBot then some hs
    else if pairClose cx t then some hs
    else
      match t.spine with
      | (.S, x :: y :: z :: rest) => run cx fuel dl (build x (z :: mkA y z :: rest)) hs
      | (.S, args) => hnfStep cx (fun dl' a hs => run cx fuel dl' a hs) dl args hs
      | (.V _ _, []) => none
      | (.V s f, args) =>
        if accN s then
          (unf s).foldl (fun acc sh => acc.bind fun hs => run cx fuel dl (build (shapeTerm f sh) args) hs)
            (some hs)
        else none
      | (.A _ _ _, _) => none

/-! ## Claims -/

def CT.vars : CT → List Nat
  | .S => []
  | .V s => [s]
  | .A l r => l.vars ++ r.vars

/-- The run term of a claim term: occurrence `i` gets the unit form `e_i` (or its exact size). -/
def toRT : CT → Nat → RT × Nat
  | .S, i => (.S, i)
  | .V s, i =>
    let f := match exactB (s % 64) with
      | some v => Form.const v
      | none => Form.unit i
    (.V s (some f), i + 1)
  | .A l r, i =>
    let p := toRT l i
    let q := toRT r p.2
    (mkA p.1 q.1, q.2)

/-- Minimum size of occurrence `j` (0 past the last occurrence). -/
def minAt (vs : List Nat) (j : Nat) : Int := if j < vs.length then minsz (vs.getD j 0) else 0

def minsOf (vs : List Nat) : Sz := ⟨minAt vs 0, minAt vs 1, minAt vs 2, minAt vs 3, minAt vs 4⟩

/-- Replace the variable occurrence with preorder index `i` (counter `some i`; `none` once done). -/
def replaceK (new : CT) : CT → Option Nat → CT × Option Nat
  | .S, i => (.S, i)
  | .V _, some 0 => (new, none)
  | .V s, some (i + 1) => (.V s, some i)
  | .V s, none => (.V s, none)
  | .A l r, i =>
    let p := replaceK new l i
    let q := replaceK new r p.2
    (.A p.1 q.1, q.2)

def FUEL : Nat := 3000
def MAXDEPTH : Nat := 10

def checkClaim (c : Claim) : Bool :=
  match c.split with
  | some k =>
    let σ := c.term.vars.getD k 0
    σ != 0 && accN σ && decide (k < c.term.vars.length) &&
    (splits σ).all fun (p, q) =>
      (lookup (replaceK (.A (mkV p) (mkV q)) c.term (some k)).1).any fun d =>
        d.stratum < c.stratum || (d.stratum == c.stratum && d.rank < c.rank)
  | none =>
    decide (c.term.vars.length ≤ 5) &&
    match (toRT c.term 0).1.sz with
    | none => false
    | some root =>
      match run ⟨c.stratum, c.rank, root, minsOf c.term.vars⟩ FUEL MAXDEPTH (toRT c.term 0).1 c.hints with
      | some [] => true
      | _ => false

/-- Every minimal rejected pair with a head normal form has a claim. -/
def rootsCovered : Bool :=
  ACCS.all fun a => ACCS.all fun b =>
    let s := dxN a b
    accN s || s % 64 == 36 || !(lookup (.A (mkV a) (mkV b))).isEmpty

end HnfCert
