import Ski.Circuit.CompDFinal
import Ski.Circuit.CompJComplete
import Ski.Circuit.CompWitT

/-!
# Completeness of the circuit with the `dec` jet: the assembly

What is left of completeness once the two private tables a run determines,
the CPU and DEC, are in hand.  **`compD_accepted_of`**: tables the circuit
with the `dec` jet accepts, from

- a CPU table that satisfies `cpuAirDec`, whose `mem` messages are memory
  cells' tuples and whose `segs` messages are the segments' rows;
- a DEC table that satisfies `decAir`, clear past its columns (so its
  blinding block is quiet), whose `mem` messages are memory cells' tuples;
- the two balancing each other on every bus but `mem` and `segs` (the
  jet's buses `decn`, `decb`, `decd`, `decx`, and the blinding buses,
  where both are quiet);

with the public program and segment tables, the honest witness table and
a memory table counting every sender's lookups (`memTableL`).  The memory
bus is stated for any list of senders (`bal_memL`): a memory table that
counts the messages of senders whose messages are memory cells' tuples
balances them.

**`compDG_complete_of`** is the run's: from a run `AcceptsCD` accepts, from
the composed machine of literal bits and a well-formed region, the public
tables are the verifier's and the witness and memory tables are honest, so
an honest CPU and DEC table as above give tables that AIRs with the normal
forms of `compDAirsG Vs W` accept, with Plonky3's selectors, at the
heights a statement names, decoding back to the memory.  What remains
(`Ski/DecCompleteTodo.lean`) is that every run has such a CPU and DEC
table.
-/

namespace Circuit

open B Air Compose CompM Mach Stmt Wit ComposedDText

-- ---------------------------------------------------------------------------
-- The memory table, for any senders
-- ---------------------------------------------------------------------------

/-- What a list of tables sends on `bus` with tuple `v`. -/
def sendsL (ss : List (AirD × Table)) (bus : String) (v : List F) : F :=
  ss.foldr (fun p acc => tableSends p.1 p.2 bus v + acc) 0

/-- **The honest memory table** for senders `ss`: one row per cell, its
    multiplicity the count of messages the senders send with its tuple,
    the blinding flag clear. -/
def memTableL (A : List Cell) (ss : List (AirD × Table)) : Table :=
  ⟨A.length, fun m col =>
    if col = 0 then ofN m
    else if col = 1 then ofN (cellTag (A.getD m .nil))
    else if col = 2 then ofN (cellFields (A.getD m .nil)).1
    else if col = 3 then ofN (cellFields (A.getD m .nil)).2
    else if col = 4 then sendsL ss "mem" (tupleOf A m)
    else 0,
   fun _ _ => 0⟩

theorem memL_sat (A : List Cell) (ss : List (AirD × Table)) (hA : 0 < A.length) :
    Sat memAirC (memTableL A ss) := by
  refine ⟨hA, fun c hc m hm' => ?_⟩
  have hm : m < (memTableL A ss).h := hm'
  simp only [memAirC, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · simp only [B.whenFirst, B.col, E.eval, env_first, env_main0 hm]
    split
    · next h0 => subst h0; exact mul_zero' _
    · exact zero_mul' _
  · simp only [B.whenTrans, B.eq, B.nxt, B.col, B.one, B.c, E.eval, env_trans, env_main1, env_main0 hm]
    split
    · exact zero_mul' _
    · next hne =>
      have hne' : ¬ (m + 1 = A.length) := hne
      have hm1 : m + 1 < A.length := by have : m < A.length := hm; omega
      show 1 * ((memTableL A ss).main ((m + 1) % A.length) 0 - (ofN m + ofN 1)) = 0
      rw [Nat.mod_eq_of_lt hm1, one_mul', ofN_one, ofN_succ]
      exact sub_self' _
  · simp only [B.bool, B.col, B.one, B.c, E.eval, env_main0 hm]
    show (0 : F) * (0 - ofN 1) = 0
    exact zero_mul' _

theorem sendsL_zero {ss : List (AirD × Table)} {bus : String} {v : List F}
    (h : ∀ p ∈ ss, tableSends p.1 p.2 bus v = 0) : sendsL ss bus v = 0 :=
  fold_zero _ ss h

/-- `a + (-a + 0) = 0`. -/
theorem add_neg_zero (a : F) : a + (-a + 0) = 0 := by
  rw [add_zero', add_comm']; exact neg_add_cancel' a

/-- **`mem` balances for any senders**: the memory table counting the
    messages of senders whose messages are memory cells' tuples receives
    each tuple as often as they send it. -/
theorem bal_memL {A : List Cell} {ss : List (AirD × Table)} (hML : A.length < P)
    (hh : ∀ p ∈ ss, HonestMem A p.1 p.2) (v : List F) :
    sendsL ss "mem" v + tableSends memAirC (memTableL A ss) "mem" v = 0 := by
  let Mm := memTableL A ss
  have hrow : ∀ m, m < A.length → rowSends memAirC Mm "mem" v m =
      if tupleOf A m = v then -(sendsL ss "mem" (tupleOf A m)) else 0 := by
    intro m hm
    have hm' : m < Mm.h := hm
    simp only [rowSends, memAirC, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, B.col, E.eval,
      env_main0 hm']
    have hb : ¬ ("blind_b" = "mem") := by decide
    simp only [hb, false_and, true_and, ↓reduceIte, add_zero']
    rfl
  cases hany : (List.range A.length).any (fun m => decide (tupleOf A m = v)) with
  | true =>
    obtain ⟨m0, hm0, e0⟩ := List.any_eq_true.1 hany
    have hm0 := List.mem_range.1 hm0
    have e0 := of_decide_eq_true e0
    have hmem : tableSends memAirC Mm "mem" v = -(sendsL ss "mem" v) := by
      show List.foldr (fun r acc => rowSends memAirC Mm "mem" v r + acc) 0 (List.range A.length) = _
      rw [fold_range_single _ A.length m0 hm0, hrow m0 hm0, if_pos e0, e0]
      intro b hb hne
      rw [hrow b hb, if_neg]
      intro e
      rw [← e0] at e
      have := congrArg List.head? e
      simp only [tupleOf, List.head?_cons, Option.some.injEq] at this
      exact hne (ofN_inj (Nat.lt_trans hb hML) (Nat.lt_trans hm0 hML) this)
    rw [hmem, ← add_zero' (sendsL ss "mem" v + _), add_assoc']
    exact add_neg_zero _
  | false =>
    have hno : ¬ ∃ m, m < A.length ∧ v = tupleOf A m := by
      rintro ⟨m, hm, e⟩
      have := List.any_eq_false.1 hany m (List.mem_range.2 hm)
      exact this (decide_eq_true e.symm)
    have h1 : sendsL ss "mem" v = 0 := sendsL_zero fun p hp =>
      sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
        (fun r hr I hI hb hc => by obtain ⟨m, hm, e⟩ := hh p hp r hr I hI hb hc; exact ⟨m, hm, e⟩) hno
    have h4 : tableSends memAirC Mm "mem" v = 0 := by
      show List.foldr (fun r acc => rowSends memAirC Mm "mem" v r + acc) 0 (List.range A.length) = 0
      apply fold_zero
      intro m hm
      rw [hrow m (List.mem_range.1 hm), if_neg (fun e => hno ⟨m, List.mem_range.1 hm, e.symm⟩)]
    rw [h1, h4]; decide

-- ---------------------------------------------------------------------------
-- Every bus of the circuit with the `dec` jet
-- ---------------------------------------------------------------------------

/-- The honest memory table of the circuit with the `dec` jet: the CPU's,
    the program's, the witness table's and DEC's lookups. -/
def memTableD (A : List Cell) (cpu prog wit : AirD) (C Pg Wt D : Table) : Table :=
  memTableL A [(cpu, C), (prog, Pg), (wit, Wt), (decAirB, D)]

def at4' (a b c d : F) : Atom → F
  | .main 0 0 => a | .main 0 1 => b | .main 0 2 => c | .main 0 3 => d | _ => 0

/-- The memory bus's sum, rearranged, by normal forms. -/
theorem bal_memD_identity (a b c d : F) :
    a + (-(a + (b + (c + (d + 0)))) + (b + (c + (0 + (d + 0))))) = 0 :=
  E.eval_eq_of_norm
    (e := .add (.atom (.main 0 0)) (.add (.neg (.add (.atom (.main 0 0)) (.add (.atom (.main 0 1))
      (.add (.atom (.main 0 2)) (.add (.atom (.main 0 3)) (.const 0))))))
      (.add (.atom (.main 0 1)) (.add (.atom (.main 0 2)) (.add (.const 0) (.add (.atom (.main 0 3)) (.const 0)))))))
    (e' := .const 0) (by decide) (at4' a b c d)

/-- **The circuit with the `dec` jet balances**: on `mem` by the memory
    table (`bal_memL`), on `segs` by the segment table (`bal_segsC`), on
    every other bus the CPU and DEC against each other. -/
theorem balancedD {A : List Cell} {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat}
    {roots : List Nat} {C Pg Wt D : Table} (hML : A.length < P) (hR : roots.length < P) (hR0 : 0 < roots.length)
    (hcM : HonestMem A (cpuAirDec hd0 stk0 ctr0 n nilA J) C)
    (hcS : ∀ r, r < C.h → ∀ I ∈ (cpuAirDec hd0 stk0 ctr0 n nilA J).inters, I.bus = "segs" →
      I.count.eval (C.env r) ≠ 0 →
      ∃ q, q < roots.length ∧ I.fields.map (fun c => c.eval (C.env r)) = [ofN q, ofN (roots.getD q 0)])
    (hpM : ∀ r, r < Pg.h → ∀ I ∈ (progAirC heap N W).inters, I.count.eval (Pg.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (Pg.env r)) = tupleOf A m)
    (hwM : HonestMem A (witAir N W) Wt)
    (hwZ : ∀ r, r < Wt.h → ∀ I ∈ (witAir N W).inters, I.bus ≠ "mem" → I.count.eval (Wt.env r) = 0)
    (hdW : Wide Dec.decAir D) (hdM : HonestMem A Dec.decAir D)
    (hjet : ∀ B, B ≠ "mem" → B ≠ "segs" → ∀ v,
      tableSends (cpuAirDec hd0 stk0 ctr0 n nilA J) C B v + tableSends Dec.decAir D B v = 0) :
    Balanced (compDTables hd0 stk0 ctr0 n nilA J heap N W roots C
      (memTableD A (cpuAirDec hd0 stk0 ctr0 n nilA J) (progAirC heap N W) (witAir N W) C Pg Wt D) Pg Wt
      (segsTableC roots (cpuAirDec hd0 stk0 ctr0 n nilA J) C) D) := by
  intro B v
  unfold compDTables
  simp only [List.foldr_cons, List.foldr_nil]
  let cpu := cpuAirDec hd0 stk0 ctr0 n nilA J
  let Mm := memTableD A cpu (progAirC heap N W) (witAir N W) C Pg Wt D
  let Sg := segsTableC roots cpu C
  have hdq : ∀ B v, tableSends decAirB D B v = tableSends Dec.decAir D B v :=
    fun B v => sends_withBlocks_quiet hdW B v
  rw [hdq]
  by_cases hBm : B = "mem"
  · subst hBm
    have hseg : tableSends (segsAir roots) Sg "mem" v = 0 :=
      sends_nobus (fun I hI => by simp only [segsAir, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; decide)
    rw [hseg]
    have hpM' : HonestMem A (progAirC heap N W) Pg := fun r hr I hI _ hc => hpM r hr I hI hc
    have hdM' : HonestMem A decAirB D := honest_withBlocks (fun b hb => by
      simp only [List.mem_singleton] at hb; subst hb; decide) hdM
    have hb := bal_memL (ss := [(cpu, C), (progAirC heap N W, Pg), (witAir N W, Wt), (decAirB, D)]) hML
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact hcM
        · exact hpM'
        · exact hwM
        · exact hdM') v
    have hm : tableSends memAirC Mm "mem" v = -(sendsL [(cpu, C), (progAirC heap N W, Pg), (witAir N W, Wt),
        (decAirB, D)] "mem" v) := by
      have := congrArg (fun x => -(sendsL [(cpu, C), (progAirC heap N W, Pg), (witAir N W, Wt), (decAirB, D)]
        "mem" v) + x) hb
      rw [← add_assoc', neg_add_cancel', zero_add', add_zero'] at this
      exact this
    rw [hm]
    simp only [sendsL, List.foldr_cons, List.foldr_nil]
    rw [hdq]
    exact bal_memD_identity _ _ _ _
  · have z_mem : tableSends memAirC Mm B v = 0 := by
      apply sends_zero_of (Q := fun _ => False) _ id
      intro r hr I hI hb hc
      simp only [memAirC, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl
      · exact hBm hb.symm
      · apply hc
        show -((col 9).eval (Mm.env r)) = 0
        rw [B.col, E.eval, env_main0 hr]
        show -(0 : F) = 0
        decide
    have z_prog : tableSends (progAirC heap N W) Pg B v = 0 :=
      sends_nobus (fun I hI => by
        simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; exact fun h => hBm h.symm)
    have z_wit : tableSends (witAir N W) Wt B v = 0 :=
      sends_zero_of (Q := fun _ => False) (fun r hr I hI hb hc => hc (hwZ r hr I hI (by rw [hb]; exact hBm))) id
    rw [z_mem, z_prog, z_wit]
    by_cases hBs : B = "segs"
    · subst hBs
      have z_dec : tableSends Dec.decAir D "segs" v = 0 :=
        sends_nobus (fun I hI h => by
          have : I.bus ∈ ["mem", "decn", "decb", "decd", "decx"] := by
            revert I; decide
          rw [h] at this; revert this; decide)
      rw [z_dec, zero_add', zero_add', zero_add']
      have := bal_segsC (cpu := cpu) (C := C) hR hR0 hcS v
      rw [add_zero', add_zero']
      exact this
    · have z_seg : tableSends (segsAir roots) Sg B v = 0 :=
        sends_nobus (fun I hI => by
          simp only [segsAir, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI
          exact fun h => hBs h.symm)
      rw [z_seg, zero_add', zero_add', zero_add', zero_add', add_zero']
      exact hjet B hBm hBs v

-- ---------------------------------------------------------------------------
-- The run's tables
-- ---------------------------------------------------------------------------

/-- **What the CPU and DEC tables must give**: the CPU satisfies its AIR,
    its `mem` messages are memory cells' tuples and its `segs` messages the
    segments' rows; DEC satisfies its AIR, is clear past its columns, its
    `mem` messages are memory cells' tuples; and the two balance each other
    on every other bus. -/
structure DecHonest (A : List Cell) (cpu : AirD) (roots : List Nat) (C D : Table) : Prop where
  cpuSat : Sat cpu C
  cpuM : HonestMem A cpu C
  cpuS : ∀ r, r < C.h → ∀ I ∈ cpu.inters, I.bus = "segs" → I.count.eval (C.env r) ≠ 0 →
    ∃ q, q < roots.length ∧ I.fields.map (fun c => c.eval (C.env r)) = [ofN q, ofN (roots.getD q 0)]
  decSat : Sat Dec.decAir D
  wide : Wide Dec.decAir D
  decM : HonestMem A Dec.decAir D
  jet : ∀ B, B ≠ "mem" → B ≠ "segs" → ∀ v, tableSends cpu C B v + tableSends Dec.decAir D B v = 0

/-- The CPU AIR of `compDAirsG Vs W`. -/
def cpuDG (Vs : List OTerm) (W : Nat) : AirD :=
  cpuAirDec (blankMO shpD W Vs).hd (blankMO shpD W Vs).stk (blankMO shpD W Vs).heap.length
    (blankRootsO shpD W Vs).length (blankMO shpD W Vs).stk JD

set_option maxRecDepth 100000 in
/-- **Completeness of the circuit with the `dec` jet, given the CPU and DEC
    tables**: a run `AcceptsCD` accepts from the composed machine of literal
    bits and a well-formed region of `W` cells, over a memory of `2^Lm`
    cells whose cells point into it, with a CPU table of `2^R` rows and a
    DEC table of `2^LD` rows meeting `DecHonest`, gives tables that AIRs
    with the normal forms of `compDAirsG Vs W` accept, with Plonky3's
    selectors: the public program and segment tables, the honest witness
    table, and the memory table counting every lookup, which decodes back
    to the memory. -/
theorem compDG_complete_of {R Lm LD : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLD : LD ≤ 20)
    {Vs : List OTerm} {W : Nat} {Rs : List AirD} (hs : sameAirsB Rs (compDAirsG Vs W) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpD + 3 + i) c = true)
    (hNW : BT.nleaves shpD + W ≤ 2 ^ 8)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCD A (cMachineO ρ shpD region Vs) JD (cHeapO ρ shpD region Vs).2
      (cHeapO ρ shpD region Vs).1.length Vs.length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e (Vs.length - 1) < 2 ^ R)
    {C D : Table} (hC : C.h = 2 ^ R) (hD : D.h = 2 ^ LD)
    (hH : DecHonest A (cpuDG Vs W) (blankRootsO shpD W Vs) C D) :
    AcceptedP Rs [C, memTableD A (cpuDG Vs W) (progAirC (blankMO shpD W Vs).heap (BT.nleaves shpD) W)
        (witAir (BT.nleaves shpD) W) C (progTableC (blankMO shpD W Vs).heap (BT.nleaves shpD) W)
        (witTable A (BT.nleaves shpD) W) D,
      progTableC (blankMO shpD W Vs).heap (BT.nleaves shpD) W, witTable A (BT.nleaves shpD) W,
      segsTableC (blankRootsO shpD W Vs) (cpuDG Vs W) C, D] ∧
    memOf (memTableD A (cpuDG Vs W) (progAirC (blankMO shpD W Vs).heap (BT.nleaves shpD) W)
        (witAir (BT.nleaves shpD) W) C (progTableC (blankMO shpD W Vs).heap (BT.nleaves shpD) W)
        (witTable A (BT.nleaves shpD) W) D) = A ∧
    (witTable A (BT.nleaves shpD) W).h = 2 ^ 9 := by
  have hRb : 2 ^ R ≤ 1048576 := Nat.pow_le_pow_right (by decide) hR
  have hLb : 2 ^ Lm ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLm
  have hDb : 2 ^ LD ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLD
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, _, _, hlenm, htake, hpub⟩ :=
    cMachineO_public ρ (fun _ => false) shpD region (List.replicate W .S) Vs hl
  obtain ⟨m0, hm0⟩ : ∃ m, cMachineO ρ shpD region Vs = m := ⟨_, rfl⟩
  rw [hm0] at hA htake hpub hlenm
  have hn : 0 < Vs.length := hA.npos
  have hnR : (blankRootsO shpD W Vs).length = Vs.length := blankRootsO_length _ _ _
  -- the memory holds the machine
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hpre : BT.nleaves shpD + 3 + W ≤ m0.heap.length := by
    have := congrArg List.length htake
    simp only [List.length_take, List.length_append, slotHeap_length, hrl] at this
    omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hslot : ∀ k, k < BT.nleaves shpD + 3 + W →
      A.getD k .nil = (slotHeap ρ (BT.nleaves shpD) ++ region).getD k .nil := by
    intro k hk
    rw [hAm k (by omega)]
    have := congrArg (fun l => l[k]?) htake
    simp only [List.getElem?_take, if_pos (show k < BT.nleaves shpD + 3 + region.length by omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hbits : ∀ i, i < BT.nleaves shpD → A.getD (3 + i) .nil = .K ∨ A.getD (3 + i) .nil = .app 0 1 := by
    intro i hi
    rw [hslot (3 + i) (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [slotHeap_length]; omega)]
    unfold slotHeap
    rw [List.getElem?_append_right (by simp),
      show 3 + i - ([Cell.K, Cell.I, Cell.app 0 1] : List Cell).length = i by simp, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    cases ρ i
    · exact .inr rfl
    · exact .inl rfl
  have hreg : ∀ i, i < W → cellOK (3 + BT.nleaves shpD + i) (A.getD (3 + BT.nleaves shpD + i) .nil) = true := by
    intro i hi
    rw [hslot _ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [slotHeap_length]; omega), slotHeap_length,
      show 3 + BT.nleaves shpD + i - (BT.nleaves shpD + 3) = i by omega]
    have hri : i < region.length := by omega
    rw [List.getElem?_eq_getElem hri, Option.getD_some]
    have := hr i region[i] (List.getElem?_eq_getElem hri)
    rwa [show BT.nleaves shpD + 3 + i = 3 + BT.nleaves shpD + i by omega] at this
  -- the numbers
  have hPP : P = 2013265921 := rfl
  have hAl : A.length < P := by rw [hlen, hPP]; omega
  have hsmall : 3 + BT.nleaves shpD + W ≤ 2 ^ 24 := by omega
  have hlenW : 3 + BT.nleaves shpD + W ≤ A.length := by omega
  have hbl : (blankMO shpD W Vs).heap.length = m0.heap.length := hlenm.symm
  have hnK : Vs.length ≤ 2 ^ 24 := by
    have := emono_ge hA.emono (Vs.length - 1) (by omega); omega
  -- the tables
  let cpu := cpuDG Vs W
  let heap := (blankMO shpD W Vs).heap
  let N := BT.nleaves shpD
  let Pg := progTableC heap N W
  let Wt := witTable A N W
  let Mm := memTableD A cpu (progAirC heap N W) (witAir N W) C Pg Wt D
  let Sg := segsTableC (blankRootsO shpD W Vs) cpu C
  have hpubA : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + N + W) →
      i < A.length ∧ A.getD i .nil = heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by
      have : heap.length = m0.heap.length := hbl
      omega
    refine ⟨by omega, ?_⟩
    have hor : i < 3 ∨ BT.nleaves shpD + 3 + region.length ≤ i := by
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact .inl h3
      · refine .inr ?_
        have := Nat.le_of_not_lt (fun hlt => hp ⟨h3, hlt⟩)
        omega
    rw [hAm i hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hpub i hor]
    rfl
  have hWt : Wt.h = 2 ^ 9 := witRows_len hNW
  have hPg : Pg.h ≤ 2 ^ 24 := progRowsC_le (by have : heap.length = m0.heap.length := hbl; omega)
  have hSg : Sg.h ≤ 2 ^ 24 := segRows_le (by rw [hnR]; exact hnK)
  have hacc : Accepted (compDAirsG Vs W) [C, Mm, Pg, Wt, Sg, D] := by
    have z : (compDAirsG Vs W).zip [C, Mm, Pg, Wt, Sg, D] =
        compDTables (blankMO shpD W Vs).hd (blankMO shpD W Vs).stk
          (blankMO shpD W Vs).heap.length (blankRootsO shpD W Vs).length
          (blankMO shpD W Vs).stk JD heap N W (blankRootsO shpD W Vs) C Mm Pg Wt Sg D := rfl
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [z]
      intro p hp
      simp only [compDTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hH.cpuSat, .inl rfl⟩
      · exact ⟨memL_sat A _ (by omega), .inl rfl⟩
      · exact ⟨(progC_sat _ _ _).1, .inr (progC_sat _ _ _).2⟩
      · exact ⟨wit_sat (a0 := 3) (fun _ => by decide) hbits hreg hsmall, .inr ⟨rfl, fun _ _ _ _ => rfl⟩⟩
      · exact ⟨⟨segRows_pos _, fun c hc => nomatch hc⟩, .inr ⟨rfl, fun _ _ _ _ => rfl⟩⟩
      · exact ⟨sat_withBlocks hH.decSat hH.wide, .inl rfl⟩
    · rw [z]
      exact balancedD hAl (by rw [hnR, hPP]; omega) (by rw [hnR]; exact hn) hH.cpuM hH.cpuS
        (progC_honest hpubA) (witT_honest (a0 := 3) (fun _ => by decide) hbits hreg hlenW) witT_blindZero
        hH.wide hH.decM hH.jet
    · rw [z]
      unfold HeightsOK compDTables
      simp only [List.foldr_cons, List.foldr_nil]
      have hMm : Mm.h = 2 ^ Lm := hlen
      show 17 * C.h + (1 * Mm.h + (1 * Pg.h + (2 * Wt.h + (0 * Sg.h + (69 * D.h + 0))))) < P
      omega
    · rw [z]
      intro p hp
      simp only [compDTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · show C.h ≤ 2 ^ 27; rw [hC]; exact Nat.pow_le_pow_right (by decide) (by omega)
      · show A.length ≤ 2 ^ 27; omega
      · show Pg.h ≤ 2 ^ 27; omega
      · show Wt.h ≤ 2 ^ 27; rw [hWt]; decide
      · show Sg.h ≤ 2 ^ 27; omega
      · show D.h ≤ 2 ^ 27; rw [hD]; exact Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨(acceptedP_iff_of (compDG_guarded Vs W) hs _).2 (accepted_transfer (sameAirsB_symm hs) hacc), ?_, hWt⟩
  -- the memory decodes back
  apply List.ext_getElem?
  intro m
  unfold memOf
  rw [List.getElem?_map]
  rcases Nat.lt_or_ge m Mm.h with hm | hm
  · rw [List.getElem?_range hm, Option.map_some]
    have hm' : m < A.length := hm
    have hg : A.getD m .nil = A[m] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm']; rfl
    have hf := hfit _ (List.getElem_mem hm')
    show some (cellOf (ofN (cellTag (A.getD m .nil))) (ofN (cellFields (A.getD m .nil)).1)
      (ofN (cellFields (A.getD m .nil)).2)) = _
    rw [hg, cellOf_enc _ (by omega) (by omega), List.getElem?_eq_getElem hm']
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact hm), List.getElem?_eq_none hm]; rfl

end Circuit
