import Ski.ZK.Terminal
import Ski.Circuit.SudSound
import Ski.Circuit.WitSound
import Ski.Circuit.CompStep

/-!
# The zero-knowledge circuits hide their witnesses' terminals

What a Sudoku, hidden-term or composed proof publishes in the clear is its
statement's data (the AIRs, the preprocessed tables, the fixed heights) and
one LogUp terminal per table.  The program table's terminal (and the
composed circuit's segment table's) reads only public columns.  The
witness table's, the CPU's and the memory's carry the witness, blinded
along a chain (`chain_terminals`): so for every generic challenge, two
witnesses of one statement publish identically distributed terminals over
the blinding (`sud_zk`, `wit_zk`, `comp_zk`), and on the honest prover's
successful runs within `2 P^4` of the `P^8` blinding pairs
(`sud_zk_valid`, …).

Assumed, not proved here: Plonky3's hiding PCS (`HidingFriPcs`), that the
committed traces and their openings reveal nothing beyond these terminals.
-/

namespace Circuit

open ZKF B

theorem ofF_one_mul (u : EF) : (EF.ofF (sgn false)).mul u = u := EF.one_mul u

theorem ofF_neg_mul (x u : EF) : x.add ((EF.ofF (sgn true)).mul u) = x.sub u :=
  Q.eq_of_norm (p := (Q.var 0).add (Q.mul ⟨k (-1), k 0, k 0, k 0⟩ (Q.var 1))) (q := (Q.var 0).sub (Q.var 1))
    (by decide) (env3 x u EF.zero)

theorem setBlind_other {T : Table} {c d : Nat} (a : Tup) (hcd : c + 5 ≤ d) (r : Nat) :
    (T.setBlind c a).main r (d + 4) = T.main r (d + 4) := by
  dsimp only [Table.setBlind]
  split
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rfl

/-- **The chain's terminals**: blinding the witness table with `a`, the
    CPU with `a` and `b`, and the memory with `b` publishes `chainView` of
    the unblinded terminals. -/
theorem chain_terminals (pre : String → EF) (β : EF) {Aw Ac Am : AirD} {Lw1 Lw2 Lc Lm : List Inter}
    {cw ca cb cm : Nat} (hW : Aw.inters = Lw1 ++ blindInter "blind_a" cw false :: Lw2)
    (hC : Ac.inters = Lc ++ blindInter "blind_a" ca true :: [blindInter "blind_b" cb false])
    (hM : Am.inters = Lm ++ [blindInter "blind_b" cm true])
    (hw1 : ∀ I ∈ Lw1, I.avoids cw = true) (hw2 : ∀ I ∈ Lw2, I.avoids cw = true)
    (hca : ∀ I ∈ Lc, I.avoids ca = true) (hcb : ∀ I ∈ Lc, I.avoids cb = true)
    (hab : (blindInter "blind_b" cb false).avoids ca = true) (hba : (blindInter "blind_a" ca true).avoids cb = true)
    (hm : ∀ I ∈ Lm, I.avoids cm = true) (hsep : ca + 5 ≤ cb)
    {Wt C Mm : Table} (hWh : 0 < Wt.h) (hCh : 0 < C.h) (hMh : 0 < Mm.h)
    (zw : ∀ r, r < Wt.h → Wt.main r (cw + 4) = 0) (za : ∀ r, r < C.h → C.main r (ca + 4) = 0)
    (zb : ∀ r, r < C.h → C.main r (cb + 4) = 0) (zm : ∀ r, r < Mm.h → Mm.main r (cm + 4) = 0) (a b : Tup) :
    (⟨terminal pre β Aw (Wt.setBlind cw a), terminal pre β Ac ((C.setBlind ca a).setBlind cb b),
      terminal pre β Am (Mm.setBlind cm b)⟩ : View3) =
      chainView β (pre "blind_a") (pre "blind_b") ⟨terminal pre β Aw Wt, terminal pre β Ac C, terminal pre β Am Mm⟩
        a b := by
  have eW := terminal_setBlind pre β hW hw1 hw2 Wt hWh zw a
  have eC1 := terminal_setBlind pre β hC hca (fun I hI => by
    simp only [List.mem_singleton] at hI; rw [hI]; exact hab) C hCh za a
  have hC' : Ac.inters = (Lc ++ [blindInter "blind_a" ca true]) ++ blindInter "blind_b" cb false :: [] := by
    rw [hC, List.append_assoc]; rfl
  have eC2 := terminal_setBlind pre β hC' (fun I hI => by
    rcases List.mem_append.1 hI with hI | hI
    · exact hcb I hI
    · simp only [List.mem_singleton] at hI; rw [hI]; exact hba) (fun I hI => absurd hI List.not_mem_nil)
    (C.setBlind ca a) hCh (fun r hr => by rw [setBlind_other a hsep]; exact zb r hr) b
  have eM := terminal_setBlind pre β hM hm (fun I hI => absurd hI List.not_mem_nil) Mm hMh zm b
  rw [eW, eC2, eC1, eM]
  unfold chainView
  rw [ofF_one_mul, ofF_one_mul, ofF_neg_mul, ofF_neg_mul]

/-- The chain's unblinded terminals sum to minus the public ones'. -/
theorem view_sum_of (x : View3) (tp : EF) (h : x.tc.add (x.tm.add (tp.add (x.tw.add EF.zero))) = EF.zero) :
    x.sum = EF.zero.sub tp := by
  have e : x.sum = (x.tc.add (x.tm.add (tp.add (x.tw.add EF.zero)))).sub tp :=
    Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).add (Q.var 2))
      (q := ((Q.var 1).add ((Q.var 2).add ((Q.var 3).add ((Q.var 0).add ⟨k 0, k 0, k 0, k 0⟩)))).sub (Q.var 3))
      (by decide) (env4 x.tw x.tc x.tm tp)
  rw [e, h]

/-- The same with two public terminals, `tp` and `ts`. -/
theorem view_sum_of5 (x : View3) (tp ts : EF)
    (h : x.tc.add (x.tm.add (tp.add (x.tw.add (ts.add EF.zero)))) = EF.zero) :
    x.sum = EF.zero.sub (tp.add ts) := by
  have e : x.sum = (x.tc.add (x.tm.add (tp.add (x.tw.add (ts.add EF.zero))))).sub (tp.add ts) :=
    Q.eq_of_norm (p := ((Q.var 0).add (Q.var 1)).add (Q.var 2))
      (q := ((Q.var 1).add ((Q.var 2).add ((Q.var 3).add ((Q.var 0).add
        ((Q.var 4).add ⟨k 0, k 0, k 0, k 0⟩))))).sub ((Q.var 3).add (Q.var 4)))
      (by decide) (env8 x.tw x.tc x.tm tp ts EF.zero EF.zero EF.zero)
  rw [e, h]

theorem all_mem {α : Type} {p : α → Bool} {l : List α} (h : l.all p = true) : ∀ a ∈ l, p a = true :=
  fun a ha => List.all_eq_true.1 h a ha

-- ---------------------------------------------------------------------------
-- Sudoku
-- ---------------------------------------------------------------------------

/-- A chain's tables before blinding: each has a row, and its blinding
    flags (the witness table's at `cw + 4`) are clear. -/
structure Unblinded (cw : Nat) (C Mm Wt : Table) : Prop where
  hw : 0 < Wt.h
  hc : 0 < C.h
  hm : 0 < Mm.h
  zw : ∀ r, r < Wt.h → Wt.main r (cw + 4) = 0
  za : ∀ r, r < C.h → C.main r (BLA + 4) = 0
  zb : ∀ r, r < C.h → C.main r (BLB + 4) = 0
  zm : ∀ r, r < Mm.h → Mm.main r (5 + 4) = 0

/-- **What a Sudoku proof publishes of its witness**: the witness table's,
    the CPU's and the memory's terminals, blinded by `a` and `b`. -/
def sudView (pre : String → EF) (β : EF) (hd0 stk0 ctr0 : Nat) (C Mm Wt : Table) (a b : Tup) : View3 :=
  ⟨terminal pre β witAirS (Wt.setBlind 1 a), terminal pre β (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) ((C.setBlind BLA a).setBlind BLB b),
    terminal pre β memAirC (Mm.setBlind 5 b)⟩

theorem sud_chain (pre : String → EF) (β : EF) (hd0 stk0 ctr0 : Nat) {C Mm Wt : Table} (h : Unblinded 1 C Mm Wt)
    (a b : Tup) :
    sudView pre β hd0 stk0 ctr0 C Mm Wt a b = chainView β (pre "blind_a") (pre "blind_b")
      ⟨terminal pre β witAirS Wt, terminal pre β (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) C, terminal pre β memAirC Mm⟩ a b :=
  chain_terminals pre β (Lw1 := []) (Lw2 := [⟨"mem", 1, prec 1, [prec 0, .sub (c 3) (.mul (col 0) (c 2)), zero,
      .sub one (col 0)]⟩]) (Lc := cpuInters) (Lm := [⟨"mem", 0, .neg (col 4), [col 0, col 1, col 2, col 3]⟩])
    (cw := 1) (ca := BLA) (cb := BLB) (cm := 5) rfl rfl rfl
    (fun _ h => absurd h List.not_mem_nil) (all_mem (l := [_]) (by decide))
    (all_mem (by decide)) (all_mem (by decide)) (by decide) (by decide) (all_mem (l := [_]) (by decide)) (by decide)
    h.hw h.hc h.hm h.zw h.za h.zb h.zm a b

/-- A balanced Sudoku table set's chain terminals sum to minus the program table's. -/
theorem sud_sum (pre : String → EF) (β : EF) {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Pg Wt : Table}
    (hb : Balanced (sudTables hd0 stk0 ctr0 heap C Mm Pg Wt)) :
    (⟨terminal pre β witAirS Wt, terminal pre β (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) C,
      terminal pre β memAirC Mm⟩ : View3).sum = EF.zero.sub (terminal pre β (progAirS heap) Pg) :=
  view_sum_of ⟨terminal pre β witAirS Wt, terminal pre β (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) C,
    terminal pre β memAirC Mm⟩ _ (logup_sum pre β _ hb)

/-- **The Sudoku proof's published terminals hide the solution**: for a
    generic combiner challenge and any bus prefixes, two balanced,
    unblinded table sets for one puzzle (one program table) publish
    identically distributed terminals, over the prover's blinding. -/
theorem sud_zk (pre : String → EF) {β : EF} (hg : Generic β) {hd0 stk0 ctr0 : Nat} {heap : List Cell}
    {C Mm Pg Wt C' Mm' Wt' : Table} (hb : Balanced (sudTables hd0 stk0 ctr0 heap C Mm Pg Wt))
    (hb' : Balanced (sudTables hd0 stk0 ctr0 heap C' Mm' Pg Wt')) (h : Unblinded 1 C Mm Wt) (h' : Unblinded 1 C' Mm' Wt')
    (E : View3 → Bool) :
    count2 (fun a b => E (sudView pre β hd0 stk0 ctr0 C Mm Wt a b)) =
      count2 (fun a b => E (sudView pre β hd0 stk0 ctr0 C' Mm' Wt' a b)) := by
  simp only [sud_chain pre β hd0 stk0 ctr0 h, sud_chain pre β hd0 stk0 ctr0 h']
  refine chain_hides hg _ _ _ _ ?_ E
  rw [sud_sum pre β hb, sud_sum pre β hb']

/-- **On the honest prover's successful runs**: the two distributions differ
    by at most `2 P^4` of the `P^8` blinding pairs. -/
theorem sud_zk_valid (pre : String → EF) {β : EF} (hg : Generic β) {hd0 stk0 ctr0 : Nat} {heap : List Cell}
    {C Mm Pg Wt C' Mm' Wt' : Table} (hb : Balanced (sudTables hd0 stk0 ctr0 heap C Mm Pg Wt))
    (hb' : Balanced (sudTables hd0 stk0 ctr0 heap C' Mm' Pg Wt')) (h : Unblinded 1 C Mm Wt) (h' : Unblinded 1 C' Mm' Wt')
    (E : View3 → Bool) :
    count2 (fun a b => !Pole β (pre "blind_a") (pre "blind_b") a b && E (sudView pre β hd0 stk0 ctr0 C Mm Wt a b)) ≤
      count2 (fun a b => !Pole β (pre "blind_a") (pre "blind_b") a b && E (sudView pre β hd0 stk0 ctr0 C' Mm' Wt' a b)) +
        2 * Q4 := by
  simp only [sud_chain pre β hd0 stk0 ctr0 h, sud_chain pre β hd0 stk0 ctr0 h']
  refine chain_hides_valid hg _ _ _ _ ?_ E
  rw [sud_sum pre β hb, sud_sum pre β hb']

-- ---------------------------------------------------------------------------
-- The hidden term
-- ---------------------------------------------------------------------------

/-- **What a hidden-term proof publishes of its witness.** -/
def witView (pre : String → EF) (β : EF) (hd0 stk0 ctr0 W : Nat) (C Mm Wt : Table) (a b : Tup) : View3 :=
  ⟨terminal pre β (witAirW W) (Wt.setBlind WT_BLIND a), terminal pre β (cpuAirW hd0 stk0 ctr0) ((C.setBlind BLA a).setBlind BLB b),
    terminal pre β memAirC (Mm.setBlind 5 b)⟩

theorem wit_chain (pre : String → EF) (β : EF) (hd0 stk0 ctr0 W : Nat) {C Mm Wt : Table}
    (h : Unblinded WT_BLIND C Mm Wt) (a b : Tup) :
    witView pre β hd0 stk0 ctr0 W C Mm Wt a b = chainView β (pre "blind_a") (pre "blind_b")
      ⟨terminal pre β (witAirW W) Wt, terminal pre β (cpuAirW hd0 stk0 ctr0) C, terminal pre β memAirC Mm⟩ a b :=
  chain_terminals pre β (Lw1 := [witInters.head (by decide)]) (Lw2 := []) (Lc := cpuInters)
    (Lm := [⟨"mem", 0, .neg (col 4), [col 0, col 1, col 2, col 3]⟩])
    (cw := WT_BLIND) (ca := BLA) (cb := BLB) (cm := 5) rfl rfl rfl
    (all_mem (l := [_]) (by decide)) (fun _ h => absurd h List.not_mem_nil)
    (all_mem (by decide)) (all_mem (by decide)) (by decide) (by decide) (all_mem (l := [_]) (by decide)) (by decide)
    h.hw h.hc h.hm h.zw h.za h.zb h.zm a b

theorem wit_sum (pre : String → EF) (β : EF) {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat} {C Mm Pg Wt : Table}
    (hb : Balanced (witTables hd0 stk0 ctr0 heap W C Mm Pg Wt)) :
    (⟨terminal pre β (witAirW W) Wt, terminal pre β (cpuAirW hd0 stk0 ctr0) C,
      terminal pre β memAirC Mm⟩ : View3).sum = EF.zero.sub (terminal pre β (progAirW heap W) Pg) :=
  view_sum_of ⟨terminal pre β (witAirW W) Wt, terminal pre β (cpuAirW hd0 stk0 ctr0) C,
    terminal pre β memAirC Mm⟩ _ (logup_sum pre β _ hb)

/-- **The hidden-term proof's published terminals hide the term**: for a
    generic combiner challenge, two balanced, unblinded table sets for one
    statement (one program table) publish identically distributed
    terminals, over the prover's blinding. -/
theorem wit_zk (pre : String → EF) {β : EF} (hg : Generic β) {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat}
    {C Mm Pg Wt C' Mm' Wt' : Table} (hb : Balanced (witTables hd0 stk0 ctr0 heap W C Mm Pg Wt))
    (hb' : Balanced (witTables hd0 stk0 ctr0 heap W C' Mm' Pg Wt')) (h : Unblinded WT_BLIND C Mm Wt)
    (h' : Unblinded WT_BLIND C' Mm' Wt') (E : View3 → Bool) :
    count2 (fun a b => E (witView pre β hd0 stk0 ctr0 W C Mm Wt a b)) =
      count2 (fun a b => E (witView pre β hd0 stk0 ctr0 W C' Mm' Wt' a b)) := by
  simp only [wit_chain pre β hd0 stk0 ctr0 W h, wit_chain pre β hd0 stk0 ctr0 W h']
  refine chain_hides hg _ _ _ _ ?_ E
  rw [wit_sum pre β hb, wit_sum pre β hb']

/-- **On the honest prover's successful runs.** -/
theorem wit_zk_valid (pre : String → EF) {β : EF} (hg : Generic β) {hd0 stk0 ctr0 : Nat} {heap : List Cell}
    {W : Nat} {C Mm Pg Wt C' Mm' Wt' : Table} (hb : Balanced (witTables hd0 stk0 ctr0 heap W C Mm Pg Wt))
    (hb' : Balanced (witTables hd0 stk0 ctr0 heap W C' Mm' Pg Wt')) (h : Unblinded WT_BLIND C Mm Wt)
    (h' : Unblinded WT_BLIND C' Mm' Wt') (E : View3 → Bool) :
    count2 (fun a b => !Pole β (pre "blind_a") (pre "blind_b") a b && E (witView pre β hd0 stk0 ctr0 W C Mm Wt a b)) ≤
      count2 (fun a b => !Pole β (pre "blind_a") (pre "blind_b") a b &&
        E (witView pre β hd0 stk0 ctr0 W C' Mm' Wt' a b)) + 2 * Q4 := by
  simp only [wit_chain pre β hd0 stk0 ctr0 W h, wit_chain pre β hd0 stk0 ctr0 W h']
  refine chain_hides_valid hg _ _ _ _ ?_ E
  rw [wit_sum pre β hb, wit_sum pre β hb']

-- ---------------------------------------------------------------------------
-- The composed circuit
-- ---------------------------------------------------------------------------

/-- **What a composed proof publishes of its witness.** -/
def compView (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA N W : Nat) (C Mm Wt : Table) (a b : Tup) : View3 :=
  ⟨terminal pre β (witAir N W) (Wt.setBlind WT_BLIND a),
    terminal pre β (cpuAirC hd0 stk0 ctr0 n nilA) ((C.setBlind BLA a).setBlind BLB b),
    terminal pre β memAirC (Mm.setBlind 5 b)⟩

theorem comp_chain (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA N W : Nat) {C Mm Wt : Table}
    (h : Unblinded WT_BLIND C Mm Wt) (a b : Tup) :
    compView pre β hd0 stk0 ctr0 n nilA N W C Mm Wt a b = chainView β (pre "blind_a") (pre "blind_b")
      ⟨terminal pre β (witAir N W) Wt, terminal pre β (cpuAirC hd0 stk0 ctr0 n nilA) C,
        terminal pre β memAirC Mm⟩ a b :=
  chain_terminals pre β (Lw1 := [witInters.head (by decide)]) (Lw2 := []) (Lc := cpuIntersC.take 9)
    (Lm := [⟨"mem", 0, .neg (col 4), [col 0, col 1, col 2, col 3]⟩])
    (cw := WT_BLIND) (ca := BLA) (cb := BLB) (cm := 5) rfl rfl rfl
    (all_mem (l := [_]) (by decide)) (fun _ h => absurd h List.not_mem_nil)
    (all_mem (by decide)) (all_mem (by decide)) (by decide) (by decide) (all_mem (l := [_]) (by decide)) (by decide)
    h.hw h.hc h.hm h.zw h.za h.zb h.zm a b

theorem comp_sum (pre : String → EF) (β : EF) {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat}
    {roots : List Nat} {C Mm Pg Wt Sg : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg)) :
    (⟨terminal pre β (witAir N W) Wt, terminal pre β (cpuAirC hd0 stk0 ctr0 n nilA) C,
      terminal pre β memAirC Mm⟩ : View3).sum =
      EF.zero.sub ((terminal pre β (progAirC heap N W) Pg).add (terminal pre β (segsAir roots) Sg)) :=
  view_sum_of5 ⟨terminal pre β (witAir N W) Wt, terminal pre β (cpuAirC hd0 stk0 ctr0 n nilA) C,
    terminal pre β memAirC Mm⟩ _ _ (logup_sum pre β _ hb)

/-- **The composed proof's published terminals hide the witness**: for a
    generic combiner challenge, two balanced, unblinded table sets for one
    statement (one program table, one segment table) publish identically
    distributed terminals, over the prover's blinding. -/
theorem comp_zk (pre : String → EF) {β : EF} (hg : Generic β) {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell}
    {N W : Nat} {roots : List Nat} {C Mm Pg Wt Sg C' Mm' Wt' : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg))
    (hb' : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C' Mm' Pg Wt' Sg))
    (h : Unblinded WT_BLIND C Mm Wt) (h' : Unblinded WT_BLIND C' Mm' Wt') (E : View3 → Bool) :
    count2 (fun a b => E (compView pre β hd0 stk0 ctr0 n nilA N W C Mm Wt a b)) =
      count2 (fun a b => E (compView pre β hd0 stk0 ctr0 n nilA N W C' Mm' Wt' a b)) := by
  simp only [comp_chain pre β hd0 stk0 ctr0 n nilA N W h, comp_chain pre β hd0 stk0 ctr0 n nilA N W h']
  refine chain_hides hg _ _ _ _ ?_ E
  rw [comp_sum pre β hb, comp_sum pre β hb']

/-- **On the honest prover's successful runs.** -/
theorem comp_zk_valid (pre : String → EF) {β : EF} (hg : Generic β) {hd0 stk0 ctr0 n nilA : Nat}
    {heap : List Cell} {N W : Nat} {roots : List Nat} {C Mm Pg Wt Sg C' Mm' Wt' : Table}
    (hb : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg))
    (hb' : Balanced (compTables hd0 stk0 ctr0 n nilA heap N W roots C' Mm' Pg Wt' Sg))
    (h : Unblinded WT_BLIND C Mm Wt) (h' : Unblinded WT_BLIND C' Mm' Wt') (E : View3 → Bool) :
    count2 (fun a b => !Pole β (pre "blind_a") (pre "blind_b") a b &&
        E (compView pre β hd0 stk0 ctr0 n nilA N W C Mm Wt a b)) ≤
      count2 (fun a b => !Pole β (pre "blind_a") (pre "blind_b") a b &&
        E (compView pre β hd0 stk0 ctr0 n nilA N W C' Mm' Wt' a b)) + 2 * Q4 := by
  simp only [comp_chain pre β hd0 stk0 ctr0 n nilA N W h, comp_chain pre β hd0 stk0 ctr0 n nilA N W h']
  refine chain_hides_valid hg _ _ _ _ ?_ E
  rw [comp_sum pre β hb, comp_sum pre β hb']

end Circuit
