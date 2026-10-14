import Ski.ZK.SpongeRestate

/-!
# The chains absorbing the trace openings at `ζ`

Plonky3's challenger absorbs the opened values at the out-of-domain point
`ζ` before it draws FRI's challenge.  In the Sudoku composites the fourth
challenge `c4` picks the query sets (`S16 c4`, `S10 c4`, `SP c4`), and the
composite's index absorbs the opened values computed at `c4 = 0`.
`SpongeRestate`'s `sud_squeezeN` therefore let the chains absorb the
commitments alone.  The trace's openings at `ζ` and `ζ g` read the
columns, the masks and the out-of-domain points, never the query sets, so
the view at the real challenge shows the ones the index absorbs.

- **One group.** `openAll`'s out-of-domain values do not read `S`
  (`openAll_oz`), and a group's view keeps them (`view_fst_snd`).
- **Every group.** Groups with equal domains, masks, out-of-domain points
  and heights give equal out-of-domain values (`openMulti_snd`) and the
  same mask count (`mtotal_sh`); `quotPost` keeps them in order
  (`quotPost_oz`).
- **The PCS.** The masks are the first `mtotal` digits whatever the later
  counts (`digitsF_take`), so the composed PCS's trace openings at `ζ`
  agree under any query sets of the groups' shape (`pcsFri_oz`), and the
  Sudoku PCS's under any `S16`, `S10`, `SP`, table weights and FRI
  (`sudPcs_oz`).  A proof's real transcript (`sudRvFS`, `sudFS4T`'s) shows
  the same trace openings at `ζ` at every fourth challenge (`sudRvFS_oz`).
- **The composite.** With the chains absorbing the third message and the
  trace openings at `ζ` (`encW`, reading the opened values only through
  them, `loadψG_w`), the view still reads `H4` only at the squeeze
  positions (`sud_rv_localζ`), the distinguisher recomputes each run from
  the third message and the openings its view shows (`sud_hprζ`), and
  `sud_squeezeNζ` is `sud_squeezeN` with this encoding.

Limits.  The quotient chunks' and the codewords' openings at `ζ` are not
absorbed: the model draws their randomness after digits whose count reads
the query sets, and no invariance is shown for them.  Plonky3 also absorbs,
before the query indices, FRI's layer roots and final polynomial and the
proof-of-work witness; here the fourth challenge drives FRI's challenges
and the query sets together, so those depend on it and cannot be absorbed
before it (see `fs_pow` and the FRI-folding entry in `WORKLIST`).  The
other limits are `sud_squeezeN`'s.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

theorem digitsF_take : ∀ (k j r : Nat), j ≤ k → (digitsF k r).take j = digitsF j r
  | _, 0, _, _ => List.take_zero
  | 0, _ + 1, _, h => absurd h (Nat.not_succ_le_zero _)
  | k + 1, j + 1, r, h => by
    show (ofN (r % P) :: digitsF k (r / P)).take (j + 1) = ofN (r % P) :: digitsF j (r / P)
    rw [List.take_succ_cons, digitsF_take k j (r / P) (Nat.le_of_succ_le_succ h)]

/-- **A group's out-of-domain values do not read its query points.** -/
theorem openAll_oz (T R S S' : List F) (Z : List EF) (n : Nat) :
    ∀ (ts : List (List F)) (rs : List F),
      (openAll T R S Z n ts rs).map Prod.snd = (openAll T R S' Z n ts rs).map Prod.snd
  | [], _ => rfl
  | t :: ts, rs => by
    show _ :: (openAll T R S Z n ts (rs.drop n)).map Prod.snd = _ :: (openAll T R S' Z n ts (rs.drop n)).map Prod.snd
    rw [openAll_oz T R S S' Z n ts (rs.drop n)]

/-- A group's shape apart from its query points. -/
def gShape (g : MGroup) : List F × List F × List EF × Nat := (g.T, g.R, g.Z, g.n)

theorem mtotal_sh : ∀ (gs gs' : List MGroup) (ks : List Nat), gs.map gShape = gs'.map gShape →
    mtotal gs ks = mtotal gs' ks
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], _, h => absurd h (by simp)
  | g :: gs, g' :: gs', [], _ => rfl
  | g :: gs, g' :: gs', k :: ks, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    have hn : g.n = g'.n := congrArg (fun s => s.2.2.2) h.1
    show k * g.n + mtotal gs ks = k * g'.n + mtotal gs' ks
    rw [hn, mtotal_sh gs gs' ks h.2]

/-- **Groups of one shape give one list of out-of-domain values.** -/
theorem openMulti_snd : ∀ (gs gs' : List MGroup) (tss : List (List (List F))) (rs : List F),
    gs.map gShape = gs'.map gShape →
      (openMulti gs tss rs).map (List.map Prod.snd) = (openMulti gs' tss rs).map (List.map Prod.snd)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)
  | _ :: _, _ :: _, [], _, _ => rfl
  | g :: gs, g' :: gs', ts :: tss, rs, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    have e : (g.T, g.R, g.Z, g.n) = (g'.T, g'.R, g'.Z, g'.n) := h.1
    simp only [Prod.mk.injEq] at e
    obtain ⟨eT, eR, eZ, en⟩ := e
    show (openAll g.T g.R g.S g.Z g.n ts (rs.take (ts.length * g.n))).map Prod.snd ::
        (openMulti gs tss (rs.drop (ts.length * g.n))).map (List.map Prod.snd) =
      (openAll g'.T g'.R g'.S g'.Z g'.n ts (rs.take (ts.length * g'.n))).map Prod.snd ::
        (openMulti gs' tss (rs.drop (ts.length * g'.n))).map (List.map Prod.snd)
    rw [eT, eR, eZ, en, openAll_oz g'.T g'.R g.S g'.S g'.Z g'.n ts, openMulti_snd gs gs' tss _ h.2]

theorem view_fst_snd (q : QGroup) (α β : EF) (v : List EF) (os : List (List F × List EF)) :
    (q.view α β v os).1.map Prod.snd = os.map Prod.snd := by
  show (os.map (fun o => (o.1.take q.base.S.length, o.2))).map Prod.snd = _
  rw [List.map_map]; rfl

/-- **`quotPost` keeps the out-of-domain values, group by group.** -/
theorem quotPost_oz : ∀ (qs : List QGroup) (α β : EF) (v : List EF) (oss : List (List (List F × List EF))),
    (quotPost qs α β v oss).map (fun g => g.1.map Prod.snd) = (qs.zip oss).map (fun p => p.2.map Prod.snd)
  | qs, α, β, v, oss => by
    unfold quotPost
    rw [List.map_map]
    exact List.map_congr_left (fun p _ => view_fst_snd p.1 α β v p.2)

theorem zip_map_snd_take {A B C : Type} (f : B → C) : ∀ (as : List A) (bs : List B),
    (as.zip bs).map (fun p => f p.2) = (bs.map f).take as.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, b :: bs => by
    rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.length_cons, List.take_succ_cons,
      zip_map_snd_take f as bs]

/-- **The composed PCS's trace openings at the out-of-domain points do not
    read the query points**: under groups of one shape and number, any
    quotient tables, table data, batching challenge and FRI. -/
theorem pcsFri_oz {V V' : Type} (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    (qs qs' : List QGroup) (ks : List Nat) (cols : (Nat → Tup) → EF → EF → List (List (List F))) (tabs tabs' : List QTab)
    (qdT qdT' : (Nat → Tup) → EF → EF → List F → List (List (List (List F) × List F))) (ncw : Nat) (αb αb' : EF)
    (fri : EF → EF → List (EF → EF) → V) (fri' : EF → EF → List (EF → EF) → V') (t : Nat → Tup) (α β : EF) (r : Nat)
    (hsh : (qs.map QGroup.ext).map gShape = (qs'.map QGroup.ext).map gShape) (hl : qs.length = qs'.length) :
    (pcsFri off tv qs ks cols tabs qdT ncw αb fri t α β r).1.1.map (fun g => g.1.map Prod.snd) =
      (pcsFri off tv qs' ks cols tabs' qdT' ncw αb' fri' t α β r).1.1.map (fun g => g.1.map Prod.snd) := by
  have hM : mtotal (qs.map QGroup.ext) ks = mtotal (qs'.map QGroup.ext) ks := mtotal_sh _ _ ks hsh
  have ms1 : ((digitsF (friN1 qs ks tabs + friN2 qs tabs ncw) r).take (friN1 qs ks tabs)).take
      (mtotal (qs.map QGroup.ext) ks) = digitsF (mtotal (qs.map QGroup.ext) ks) r := by
    rw [List.take_take, digitsF_take _ _ _ (Nat.le_trans (Nat.min_le_left _ _) (by unfold friN1; omega))]
    congr 1; unfold friN1; omega
  have ms2 : ((digitsF (friN1 qs' ks tabs' + friN2 qs' tabs' ncw) r).take (friN1 qs' ks tabs')).take
      (mtotal (qs'.map QGroup.ext) ks) = digitsF (mtotal (qs'.map QGroup.ext) ks) r := by
    rw [List.take_take, digitsF_take _ _ _ (Nat.le_trans (Nat.min_le_left _ _) (by unfold friN1; omega))]
    congr 1; unfold friN1; omega
  show (quotPost qs α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β)
        (((digitsF (friN1 qs ks tabs + friN2 qs tabs ncw) r).take (friN1 qs ks tabs)).take
          (mtotal (qs.map QGroup.ext) ks)))).map (fun g => g.1.map Prod.snd) =
    (quotPost qs' α β (tv (prefixOf α (off β)) β t) (openMulti (qs'.map QGroup.ext) (cols t α β)
        (((digitsF (friN1 qs' ks tabs' + friN2 qs' tabs' ncw) r).take (friN1 qs' ks tabs')).take
          (mtotal (qs'.map QGroup.ext) ks)))).map (fun g => g.1.map Prod.snd)
  rw [ms1, ms2, ← hM, quotPost_oz, quotPost_oz, zip_map_snd_take, zip_map_snd_take, hl,
    openMulti_snd _ _ _ _ hsh]

/-- **The Sudoku PCS's trace openings at `ζ` do not read the query sets**:
    any `S16`, `S10`, `SP`, any table weights, batching challenge and FRI. -/
theorem sudPcs_oz {V V' : Type} (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table)
    (tp : Nat) (S16 S10 SP S16' S10' SP' : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wm' wc' ww' wp' : List (EF → EF → List F)) (ncw : Nat) (αb αb' : EF)
    (fri : EF → EF → List (EF → EF) → V) (fri' : EF → EF → List (EF → EF) → V') (t : Nat → Tup) (α β : EF) (r : Nat) :
    (sudPcs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp ncw αb fri t α β r).1.1.map
        (fun g => g.1.map Prod.snd) =
      (sudPcs off hd0 stk0 ctr0 heap C Mm Wt tp S16' S10' SP' ζ qv wm' wc' ww' wp' ncw αb' fri' t α β r).1.1.map
        (fun g => g.1.map Prod.snd) :=
  pcsFri_oz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl

/-- A view's trace openings at the out-of-domain points. -/
def ozζV {V PB : Type} (v : TViewN (SudPV V) PB) : Option (List (List (List EF))) :=
  v.map (fun p => p.1.1.1.map (fun g => g.1.map Prod.snd))

/-- **Real transcripts over PCSs with equal trace openings at `ζ` show
    equal trace openings at `ζ`.** -/
theorem realVN_oz {V PB : Type} (off : EF → String → EF) (tabs : (Nat → Tup) → List (AirD × Table))
    (tv : (String → EF) → EF → (Nat → Tup) → List EF) (pb : (String → EF) → EF → PB)
    (pcs pcs' : (Nat → Tup) → EF → EF → Nat → SudPV V)
    (h : ∀ t α β r, (pcs t α β r).1.1.map (fun g => g.1.map Prod.snd) = (pcs' t α β r).1.1.map (fun g => g.1.map Prod.snd))
    (α β : EF) (r : Nat) (t : Nat → Tup) :
    ozζV (realVN off tabs tv pb pcs α β r t) = ozζV (realVN off tabs tv pb pcs' α β r t) := by
  unfold realVN
  split
  · rfl
  · exact congrArg some (h t α β r)

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

/-- **One Sudoku proof's real transcript** as `sudFS4T` builds it, at the
    fourth challenge `c4`, the second `c2` and the third `c3`. -/
def sudRvFS {V Wv : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row)
    (tP : Nat) (S16 S10 SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V)
    (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) : TViewN (SudPV (V × Wv)) EF :=
  let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
  let C := cpuTableW A row k (2 ^ 16)
  let Pg := progTableS blank.heap
  let Wt := witTableS A
  let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
  let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv
    (wm 0) (wc 0) (ww 0) (wp 0) ncw
  let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP
    (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4) (friX (fri c4) (Rb c4) (Ro c4) (r / NR0))
    t α β (r % NR0)
  let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
    ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
  let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
  let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
  realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t

/-- **A Sudoku proof's trace openings at `ζ` do not read the fourth
    challenge.** -/
theorem sudRvFS_oz {V Wv : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat)
    (row : Nat → Air.Row) (tP : Nat) (S16 S10 SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V)
    (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    (c4 c4' c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) :
    ozζV (sudRvFS off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri Rb Ro c4 c2 c3 α β r t) =
      ozζV (sudRvFS off puzzle A k row tP S16 S10 SP qv wm wc ww wp ncw αd fri Rb Ro c4' c2 c3 α β r t) := by
  unfold sudRvFS
  exact realVN_oz _ _ _ _ _ _ (fun t α β r => sudPcs_oz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    t α β (r % _)) _ _ _ _

/-- The opened values the composite's index absorbs (`sudFS4T`'s `ozF`). -/
def ozFS {V Wv : Type} (v : TViewN (SudPV (V × Wv)) EF) : WSud :=
  match v with
  | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
      pv.2.1.map (List.map Prod.snd))
  | none => none

theorem ozFS_fst {V Wv : Type} (v : TViewN (SudPV (V × Wv)) EF) : (ozFS v).map Prod.fst = ozζV v := by
  rcases v with _ | ⟨pv, _⟩ <;> rfl

end


/-! ### The chains absorbing the trace openings at `ζ` -/

/-- With the encoding reading only the trace openings, the index reads the
    opened values only through them. -/
theorem loadψG_w {K : Nat} (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat) (G n1 L : Nat)
    (encW : Nat → Option (List (List (List EF))) → List Nat) (P ix m : Nat) {w w' : WSud}
    (h : w.map Prod.fst = w'.map Prod.fst) :
    loadψG K inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P ix m w =
      loadψG K inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P ix m w' := by
  show inner (chain1 K inner (ivP K inner z (pre0 ++ [blk (m % n1 % G)]) P)
      (bf (m % n1 / G) :: encW (m / n1) (w.map Prod.fst)) P L) ((bf (m % n1 / G) :: encW (m / n1) (w.map Prod.fst)).getD L 0) =
    inner (chain1 K inner (ivP K inner z (pre0 ++ [blk (m % n1 % G)]) P)
      (bf (m % n1 / G) :: encW (m / n1) (w'.map Prod.fst)) P L) ((bf (m % n1 / G) :: encW (m / n1) (w'.map Prod.fst)).getD L 0)
  rw [h]

/-- The fourth indexes a distinguisher computes from `n` proofs' views, the
    index of proof `i` from its whole view `idx i y`. -/
def posVζ {O : Type} (idx : Nat → (Nat × Nat × Nat × O) → Nat) :
    (n : Nat) → PowD (fun _ => Option (Nat × Nat × Nat × O) × List Nat) n → List Nat
  | 0, _ => []
  | n + 1, v => (match v.1.1 with | some y => idx n y | none => 0) :: posVζ idx n v.2

theorem posVζ_rvPowD {T Xt O : Type} (d : Xt) (idx : Nat → (Nat × Nat × Nat × O) → Nat)
    (rv : (i : Nat) → T → Xt → Option (Nat × Nat × Nat × O) × List Nat) (H : T) :
    ∀ n (x : PowD (fun _ => Xt) n),
      posVζ idx n (rvPowD (X := fun _ => Xt) rv n H x) =
        listN (fun i => match (rv i H (xAt d n x i)).1 with | some y => idx i y | none => 0) n
  | 0, _ => rfl
  | n + 1, x => by
    show (match (rv n H x.1).1 with | some y => idx n y | none => 0) ::
        posVζ idx n (rvPowD (X := fun _ => Xt) rv n H x.2) = _ :: _
    rw [posVζ_rvPowD d idx rv H n x.2]
    congr 1
    · show _ = (match (rv n H (xAt d (n + 1) x n)).1 with | some y => idx n y | none => 0)
      rw [show xAt d (n + 1) x n = x.1 from if_pos rfl]
    · exact listN_congr n (fun i hi => by rw [show xAt d (n + 1) x i = xAt d n x.2 i from if_neg (Nat.ne_of_lt hi)])

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

variable {V Wv P1 P2 P3 W1 W2 W3 : Type} (off : EF → String → EF) (puzzle : Nat → List Nat) (A : Nat → List Cell)
  (k : Nat → Nat) (row : Nat → Nat → Air.Row) (tP : Nat → Nat) (S16 S10 SP : Nat → Nat → List F)
  (qv : Nat → EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : Nat → Nat → List (EF → EF → List F))
  (K2 Kp : Nat) (ncw : Nat → Nat) (αd : Nat → Nat → EF) (B4 : Nat → Nat) (fri : Nat → Nat → EF → EF → List (EF → EF) → V)
  (NR2 : Nat → Nat) (Rb : Nat → Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → Nat → EF → EF → Nat → Wv)
  (NS1 NS2 NS3 : Nat → Nat) (n1 n2 n3 : Nat) (Com1 : Nat → List (List (List F)) → Nat → Nat)
  (Com2 : Nat → List (List (List F)) → Nat → Nat) (Com3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → Nat)
  (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1)
  (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat)
  (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2)
  (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3)
  (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
  (inner : Nat → Nat → Nat) (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat) (G L : Nat) (encW : Nat → Option (List (List (List EF))) → List Nat)

/-- Proof `i`'s opened values as the composite's index absorbs them: its
    real transcript at the fourth challenge `0`. -/
def sudW0At (n : Nat) (H : Nat × Nat × Nat) (x : PowD (fun _ => XSud) n) (i : Nat) : WSud :=
  ozFS (sudRvFS off (puzzle i) (A i) (k i) (row i) (tP i) (S16 i) (S10 i) (SP i) (qv i) (wm i) (wc i) (ww i) (wp i) (ncw i) (αd i) (fri i) (Rb i) (Ro i) 0
    (rget K2 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
      n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m2 (rget (Q4 * Q4) ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
      n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m1 (xAt xSud0 n x i)) H.1) (xAt xSud0 n x i)) H.2.1)
    (rget Q4 (sudM3At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
      Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i) H.2.2)
    (efOf (rget (Q4 * Q4) ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
      n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m1 (xAt xSud0 n x i)) H.1 / Q4))
    (efOf (rget (Q4 * Q4) ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
      n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m1 (xAt xSud0 n x i)) H.1 % Q4))
    (xAt xSud0 n x i).2.2.1 (xAt xSud0 n x i).2.2.2)

/-- Proof `i`'s sponge run: the prefix, then its third message and its trace
    openings at `ζ`. -/
def sudNxtIζ (n : Nat) (H : Nat × Nat × Nat) (x : PowD (fun _ => XSud) n) (i : Nat) : List Nat → Nat :=
  nxtBl inner z (blocksG pre0 blk bf G n1 (fun r (w : WSud) => encW r (w.map Prod.fst))
    (sudM3At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
      Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i)
    (sudW0At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
      Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i))

/-- **The restated view, the chains absorbing the trace openings at `ζ`**: the composite's view with each proof's fourth
    index its run's squeeze position and the fourth table answering `g`. -/
def sudRvSζ (n : Nat) (c : List (List (Nat × Nat))) (H : Nat × Nat × Nat) (x : PowD (fun _ => XSud) n) (g : Nat → Nat) :=
  rvPowD (X := fun _ => XSud) (mixRv (Q4 * Q4) K2 Q4 Kp 0 (fun _ => false) (fun _ _ => (0, 0, ()))
    (fun i => read4T (Q4 * Q4) K2 Q4 Kp
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
        (fun ix _ _ => posOf (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1
          NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x) c ix)
        Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m1
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
        n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m2
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
        n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).m3
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
        (fun ix _ _ => posOf (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1
          NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x) c ix)
        Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).q
      (sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (fun _ _ _ => 0) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
        n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i).out))
    n (H.1, H.2.1, H.2.2, tab Kp g Kp) x

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The composite's view reads the permutation only through the runs and
    `H4` only at their squeeze positions**: with no query phases, no
    table-reading openings, the fourth table a full state and an encoding
    of the third message and the trace openings at `ζ`, the view at
    `(P, H, H4)` is `sudRvSζ` at the
    runs and the lookup of `H4` at the distinct squeeze positions. -/
theorem sud_rv_localζ (hKp : 0 < Kp) (hin : ∀ s x, inner s x < Kp) (n P : Nat) (H : Nat × Nat × Nat) (H4 : Nat)
    (x : PowD (fun _ => XSud) n) :
    rvPowD (X := fun _ => XSud) (mixRv (Q4 * Q4) K2 Q4 Kp 0 (fun _ => false) (fun _ _ => (0, 0, ()))
      (fun i => read4T (Q4 * Q4) K2 Q4 Kp
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m1
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m2
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).m3
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).q
        ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp
          (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).out))
      n (H.1, H.2.1, H.2.2, H4) x =
    sudRvSζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3
      φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n
      (runsN Kp (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3
        Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x) (pre0.length + 1 + L) P n) H x
      (getAt (dedupL (sqOf (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x)
          (runsN Kp (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2
            n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x) (pre0.length + 1 + L) P n)))
        ((dedupL (sqOf (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
          n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x)
          (runsN Kp (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2
            n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x) (pre0.length + 1 + L) P n))).map
          (fun v => rget Kp v H4))) := by
  let nx := sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3
    Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x
  let kk := pre0.length + 1 + L
  let ps := dedupL (sqOf nx (runsN Kp nx kk P n))
  let g := getAt ps (ps.map (fun v => rget Kp v H4))
  refine rvPowD_congr xSud0 _ _ _ _ n x (fun i hi => ?_)
  refine congrArg (fun y => (some y, ([] : List Nat))) ?_
  refine read4T_congr _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl ?_
  -- the index is proof `i`'s squeeze position
  have hq : loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P i
      (sudM3At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
        Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i)
      (sudW0At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
        Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i) = posT Kp (nx i) P kk :=
    loadψG_posT Kp inner z pre0 blk bf G n1 L _ P i _ _
  have hpos : posOf nx (runsN Kp nx kk P n) i = posT Kp (nx i) P kk := posOf_runsN Kp nx kk P n i hi
  have hmem : posT Kp (nx i) P kk ∈ ps := (mem_dedupL _).2 (posT_mem_sqOf Kp nx kk P n i hi)
  have hlt : posT Kp (nx i) P kk < Kp := hin _ _
  have hg : ∀ m, m < Kp → g m < Kp := fun m _ => getAt_lt hKp ps _ (fun a ha => by
    obtain ⟨v, _, e⟩ := List.mem_map.1 ha; rw [← e]; exact rget_lt hKp _ _) m
  show rget Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P i
      (sudM3At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
        Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i)
      (sudW0At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2
        Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i)) H4 =
    rget Kp (posOf nx (runsN Kp nx kk P n) i) (tab Kp g Kp)
  rw [hq, hpos, rget_tab hKp Kp g hg _ hlt]
  exact (getAt_map (fun v => rget Kp v H4) ps hmem).symm




set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The distinguisher finds the squeeze positions from the restated
    view**: each proof's third message and its trace openings at `ζ` are in
    its view, the latter at the real fourth challenge, where they are the
    openings at the challenge `0` the run absorbs (`sudRvFS_oz`). -/
theorem sud_hprζ (n P : Nat) (H : Nat × Nat × Nat) (x : PowD (fun _ => XSud) n) (c : List (List (Nat × Nat)))
    (g : Nat → Nat) :
    dedupL (posVζ (fun i y => loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P i y.2.2.1 (ozFS y.2.2.2.2.2)) n
      (sudRvSζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n c H x g)) =
    dedupL (sqOf (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x)
      (runsN Kp (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x) (pre0.length + 1 + L) P n)) := by
  congr 1
  unfold sudRvSζ
  rw [posVζ_rvPowD xSud0, sqOf_runsN]
  refine listN_congr n (fun i _ => ?_)
  let φc := fun ix (_ : Nat) (_ : WSud) => posOf (sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x) c ix
  let D := sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp φc Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3
    n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 i
  let xi := xAt xSud0 n x i
  let Hq : Nat × Nat × Nat × Nat := (H.1, H.2.1, H.2.2, tab Kp g Kp)
  let c1 := rget (Q4 * Q4) (D.m1 xi) Hq.1
  let c2 := rget K2 (D.m2 c1 xi) Hq.2.1
  let c3 := rget Q4 (D.m3 c1 c2 xi) Hq.2.2.1
  let c4 := rget Kp (D.q c1 c2 c3 xi) Hq.2.2.2
  have hout : (D.out Hq c4 c1 c2 c3 xi).2.2 =
      sudRvFS off (puzzle i) (A i) (k i) (row i) (tP i) (S16 i) (S10 i) (SP i) (qv i) (wm i) (wc i) (ww i) (wp i) (ncw i) (αd i) (fri i) (Rb i) (Ro i) c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) xi.2.2.1 xi.2.2.2 := rfl
  have hw : (ozFS (D.out Hq c4 c1 c2 c3 xi).2.2).map Prod.fst =
      (sudW0At off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 n H x i).map Prod.fst := by
    rw [hout, ozFS_fst]
    show _ = (ozFS (sudRvFS off (puzzle i) (A i) (k i) (row i) (tP i) (S16 i) (S10 i) (SP i) (qv i) (wm i) (wc i) (ww i) (wp i) (ncw i) (αd i) (fri i) (Rb i) (Ro i) 0 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) xi.2.2.1 xi.2.2.2)).map Prod.fst
    rw [ozFS_fst]
    exact sudRvFS_oz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c4 0 c2 c3 _ _ _ _
  exact Eq.trans (loadψG_w (K := Kp) inner z pre0 blk bf G n1 L encW P i (D.m3 c1 c2 xi) hw)
    (loadψG_posT Kp inner z pre0 blk bf G n1 L _ P i _ _)

end

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- **`sud_squeezeN` with the chains absorbing the trace openings at `ζ`**:
    the index absorbs the third message and the trace's openings at the
    out-of-domain points (`encW`), which the view shows at the real fourth
    challenge and which do not read it (`sudRvFS_oz`); the rest as in
    `sud_squeezeN`. -/
theorem sud_squeezeNζ {V Wv P1 P2 P3 W1 W2 W3 : Type} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → W3 → Nat) (nx3 : Nat → Nat → Nat → List Nat → Nat × Nat × W3) (G3 : Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3)
     (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 Kp : Nat} (hK2 : 0 < K2) (hKp : 0 < Kp) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo Kp (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRdM (Q4 * Q4) K2 Q4 Kp n1 0 (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRdM (Q4 * Q4) K2 Q4 Kp n1 0 (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRdM (Q4 * Q4) K2 Q4 Kp n1 0 (φ3 ix) (nx3 ix) (G3 ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)))
    (inner : Nat → Nat → Nat) (hin : ∀ s x, inner s x < Kp) (κ : Nat → Nat) {Kc : Nat}
    (hκ : ∀ u, κ u < Kc) (hpk2 : ∀ s s' x x', inner s x = inner s' x' → κ s = κ s') (z : Nat) (pre0 : List Nat) (blk bf : Nat → Nat)
    {G N0 N : Nat} (hG : 0 < G) (hN : 0 < N) (hn : n1 = G * N0) (hbf : ∀ h, h < N0 → bf h < N)
    (hinj : ∀ h h', h < N0 → h' < N0 → bf h = bf h' → h = h')
    (hd : ∀ iv a b, a < N → b < N → a ≠ b → inner iv a ≠ inner iv b)
    (hdxC : ∀ iv s s' x c c', c < N → c' < N → inner s x = inner iv c → inner s' x = inner iv c' → c = c')
    {X : Nat} (hX : 0 < X) (L : Nat) (encW : Nat → Option (List (List (List EF))) → List Nat) (henc : ∀ r o i, i < L → (encW r o).getD i 0 < X)
    (δ0 : Nat → Nat)
    (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δ0 ix) {t : Nat} (ht : 0 < t) {s0 : Nat} (hs0 : 2 ≤ s0)
    {Fκ : Nat} (hF : ∀ v, sumTo Kp (fun u => indB (decide (κ u = v))) ≤ Fκ)
    (hκin : ∀ s x, κ (inner s x) = κ s) (n : Nat) 
    (E : Nat → Nat × Nat × Nat →
      PowD (fun _ => Option (Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF)) × List Nat) n →
      Bool) :
    let sD := fun (Pφ : Nat → Nat → WSud → Nat) => sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp Pφ Kp ncw αd B4
      fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3
    let ψ := fun P => loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P
    let kk := pre0.length + 1 + L
    let K4w := KPowD (fun _ => Kp * (Q4 * Q4 * (K2 * Q4))) n
    let ST := fun (f : Nat × Nat × Nat → Nat) => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
      sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3))))
    let sm := smPowD (X := fun _ => XSud) (fun i => (sD (ψ 0) i).sm 2) n
    let SC := scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) =>
      sumTo Kp (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n
    let nxtI := fun H x => sudNxtIζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n H x
    let rv := fun c H x g => sudRvSζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G encW n c H x g
    let pgF := fun (P : Nat) (H : Nat × Nat × Nat) (H4 : Nat) (c : PowD (fun _ => Nat × Nat × Nat × Nat) n)
        (x : PowD (fun _ => XSud) n) =>
      pgPowD (X := fun _ => XSud) (C := fun _ => Nat × Nat × Nat × Nat)
        (pgRd (Q4 * Q4) K2 Q4 Kp (fun i => !(fun _ => false) i) (fun i => (sD (ψ P) i).pts) (fun _ c => c)) n
        (H.1, H.2.1, H.2.2, H4) c x
    let pgJ := fun P H H4 c x => (((pgF P H H4 c x).1, (pgF P H H4 c x).2.1, (pgF P H H4 c x).2.2.1), (pgF P H H4 c x).2.2.2)
    let sv := fun (P : Nat) (H : Nat × Nat × Nat) (H4 : Nat) (c : PowD (fun _ => Nat × Nat × Nat × Nat) n)
        (x : PowD (fun _ => XSud) n) =>
      svPowDT (X := fun _ => XSud) (C := fun _ => Nat × Nat × Nat × Nat)
        (pgRd (Q4 * Q4) K2 Q4 Kp (fun i => !(fun _ => false) i) (fun i => (sD (ψ P) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 Kp 0 (fun _ => false) (fun _ _ => (0, 0, ())) (fun i => (sD (ψ P) i).sv)) n
        (H.1, H.2.1, H.2.2, H4) c x
    let pos := fun P (_ : Nat × Nat × Nat) v => dedupL (posVζ (fun i y => ψ P i y.2.2.1 (ozFS y.2.2.2.2.2)) n v)
    let ε := (sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) * (errPowD (fun _ => (Kp * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo Kp (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond ((fun _ => false) i) 0 ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo Kp (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (Kp ^ Kp) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) i).sm 2) n
          (fun _ => rSum (fun i => cond ((fun _ => false) i) 0 (4 + 3 * 0)) n *
            cond ((fun _ => false) n) 0 (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NS * (((sudD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp (loadψG Kp inner z pre0 blk bf G n1 L (fun r (w : WSud) => encW r (w.map Prod.fst)) P) Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 0 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3) n).NR * (Q4 ^ 2 * δsG Kp inner z pre0 blk G N X L t s0 δ0 P n))))))) n)))
    (Kp - n * kk) * (K4w * (Kp ^ Kp * ST (fun H => sm (fun x => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P &&
        E P H (rv (runsN Kp (nxtI H x) kk P n) H x
          (getAt (dedupL (sqOf (nxtI H x) (runsN Kp (nxtI H x) kk P n)))
            ((dedupL (sqOf (nxtI H x) (runsN Kp (nxtI H x) kk P n))).map (fun v => rget Kp v P)))))))))) ≤
      (Kp - n * kk) * (ST (fun H => SC (fun c => sm (fun x => sumTo (Kp ^ Kp) (fun P => indB (permB Kp P) *
        sumTo (Kp ^ Kp) (fun H4 => indB (E (progL Kp (pos P (pgJ P H H4 c x).1 (sv P H H4 c x)) (pgJ P H H4 c x).2 P)
          (pgJ P H H4 c x).1 (sv P H H4 c x))))))) + ε) +
      K4w * (Kp ^ (Kp - 1) * (ST (fun _ => sm (fun _ => 1)) *
        (((Kp - n * kk) * (n * (n * kk + n)) + Kp * n * ((sumTo (n * kk) (fun j => j) + n * kk * n) * Fκ)) *
          sumTo (Kp ^ Kp) (fun P => indB (permB Kp P))))) := by
  intro sD ψ kk K4w ST sm SC nxtI rv pgF pgJ sv pos ε
  have hcomp := sud_interleaveLGψ (kr := 0) (kq := 0) (K4 := Kp) φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 off hc hA hacc hlen hk htp
    S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hKp hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro
    Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 hKp inner hin κ hκ hpk2 z pre0 blk bf hG hN hn hbf hinj
    hd hdxC hX L (fun r w => encW r (w.map Prod.fst)) (fun r w i hi => henc r _ i hi) δ0 hsp1 ht hs0 (fun _ => false) (fun _ _ => (0, 0, ())) n
  have hST : Lin ST := lin_sum3 _ _ _
  have hsm : Lin sm := lin_smPowD (fun i => lin_sm _ _ _ _) n
  have hSC : Lin SC := lin_scPowD (fun _ => lin_sum4c _ _ _ _) n
  have hkk : 0 < kk := Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _)
  exact zk_squeezeN (K := Kp) (k := kk) (n := n) (K4w := K4w) (ε := ε) hKp hkk κ hF ST hST sm hsm SC nxtI
    (fun _ _ _ _ => hin _ _) (fun _ _ _ a l => hκin a _) rv pgJ sv pos
    (fun P H x g => sud_hprζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G L encW n P H x _ g)
    (fun D => hypN_of_zkbT ST hST sm hsm SC hSC (fun H H4 => (H.1, H.2.1, H.2.2, H4))
      (fun TT => ((TT.1, TT.2.1, TT.2.2.1), TT.2.2.2)) (fun _ _ => rfl) _ _ _ hcomp
      (fun P H x H4 => rv (runsN Kp (nxtI H x) kk P n) H x
        (getAt (dedupL (sqOf (nxtI H x) (runsN Kp (nxtI H x) kk P n)))
          ((dedupL (sqOf (nxtI H x) (runsN Kp (nxtI H x) kk P n))).map (fun v => rget Kp v H4))))
      pgJ sv
      (fun P H H4 x => sud_rv_localζ off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 Kp ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 φ1 nx1 G1 φ2 nx2 G2 φ3 nx3 G3 inner z pre0 blk bf G L encW hKp hin n P H H4 x)
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) D) E


end

end Circuit
