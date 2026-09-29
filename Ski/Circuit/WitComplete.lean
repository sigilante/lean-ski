import Ski.Circuit.WitSound
import Ski.Circuit.CompComplete

/-!
# Completeness of the hidden-term circuit

A run the Lean AIR accepts from the witness machine of a well-formed
region, ending at `K` over the empty stack, over a memory of `2^10` cells
in at most `2^10` rows, with a region of at most `2^8` cells (the witness
verifier's heights), gives honest tables the witness circuit accepts,
decoding back to the memory and the run (`wit_complete`).
-/

namespace Circuit

open B Air Wit Mach

/-- The run, padded by repeating its last row. -/
def rowQ (row : Nat → Row) (k i : Nat) : Row := if i < k then row i else row (k - 1)

/-- **The honest witness-circuit CPU row**: the corpus row, the blinding
    flags clear. -/
def cpuColW (A : List Cell) (row : Nat → Row) (k i col : Nat) : F :=
  if col < CPU_WIDTH then cpuCol A (rowQ row k i) col else 0

def cpuTableW (A : List Cell) (row : Nat → Row) (k K : Nat) : Table :=
  ⟨K, fun i col => cpuColW A row k i col, fun _ _ => 0⟩

/-- The corpus CPU's atoms: its columns, now and next, and the selectors. -/
def cpuAtom : Atom → Bool
  | .main 0 c | .main 1 c => decide (c < CPU_WIDTH)
  | .first | .last | .trans => true
  | _ => false

set_option maxRecDepth 100000 in
theorem cpuCons_atoms (hd0 stk0 ctr0 : Nat) : (cpuCons hd0 stk0 ctr0).all (·.onlyAtoms cpuAtom) = true := rfl

theorem cpuInters_atoms : cpuInters.all (fun I => I.count.onlyAtoms cpuAtom && I.fields.all (·.onlyAtoms cpuAtom)) =
    true := by decide

theorem cpuW_env {A : List Cell} {row : Nat → Row} {k K i : Nat} (hi : i < K) :
    ∀ a, cpuAtom a = true → (cpuTableW A row k K).env i a = (cpuTable A (rowQ row k) K).env i a := by
  intro a ha
  cases a with
  | main o c =>
    rcases o with _ | _ | o
    · simp only [cpuAtom, decide_eq_true_eq] at ha
      show cpuColW A row k ((i + 0) % K) c = cpuCol A (rowQ row k ((i + 0) % K)) c
      unfold cpuColW; rw [if_pos ha]
    · simp only [cpuAtom, decide_eq_true_eq] at ha
      show cpuColW A row k ((i + 1) % K) c = cpuCol A (rowQ row k ((i + 1) % K)) c
      unfold cpuColW; rw [if_pos ha]
    · simp [cpuAtom] at ha
  | pre _ _ => simp [cpuAtom] at ha
  | first => rfl
  | last => rfl
  | trans => rfl

section

variable {A : List Cell} {m0 : Mach} {k : Nat} {row : Nat → Row} (hA : AcceptsFrom A m0 k row)
  {K : Nat} (hkK : k ≤ K) (hK : K ≤ 2 ^ 24) (hlen : A.length ≤ 2 ^ 24)
include hA hkK

theorem rowQ_valid : ∀ i, i < K → Valid A (rowQ row k i) := by
  intro i _
  have hk := hA.pos
  unfold rowQ
  split
  · next hi =>
    rcases Nat.lt_or_ge (i + 1) k with h | h
    · rcases hA.trans i h with h' | h'
      · exact .inl (by rw [h']; rfl)
      · exact .inr h'.1
    · rw [show i = k - 1 by omega]; exact .inr hA.final
  · exact .inr hA.final

theorem rowQ_trans : ∀ i, i + 1 < K → stepRow A (rowQ row k i) = some (rowQ row k (i + 1)) ∨
    (haltRow A (rowQ row k i) = true ∧ rowQ row k (i + 1) = rowQ row k i) := by
  intro i _
  have hk := hA.pos
  unfold rowQ
  by_cases h : i + 1 < k
  · rw [if_pos (by omega), if_pos h]; exact hA.trans i h
  · rw [if_neg h]
    by_cases h' : i < k
    · rw [if_pos h', show i = k - 1 by omega]; exact .inr ⟨hA.final, rfl⟩
    · rw [if_neg h']; exact .inr ⟨hA.final, rfl⟩

omit hkK in
theorem AcceptsFrom.ctr_le' (h0 : m0.heap.length ≤ A.length) :
    ∀ i, i < k → (row i).ctr ≤ A.length := fun i hi => (hA.reach i hi).1

include hK hlen in
/-- **The honest witness-circuit CPU satisfies its AIR.** -/
theorem cpuW_sat (hK0 : 0 < K) (hfin5 : kindOf A (row (k - 1)) = 5) :
    Sat (cpuAirW (rowQ row k 0).hd (rowQ row k 0).stk (rowQ row k 0).ctr) (cpuTableW A row k K) := by
  have hk := hA.pos
  have hb : ∀ i, i < K → (rowQ row k i).ctr ≤ 2 ^ 24 := by
    intro i _
    unfold rowQ; split
    · exact Nat.le_trans ((hA.reach i (by assumption)).1) hlen
    · exact Nat.le_trans ((hA.reach (k - 1) (by omega)).1) hlen
  have hfinQ : haltRow A (rowQ row k (K - 1)) = true := by
    unfold rowQ; split
    · next h => rw [show K - 1 = k - 1 by omega]; exact hA.final
    · exact hA.final
  have base := cpu_sat (M := A) (row := rowQ row k) (k := K) (rowQ_valid hA hkK) (rowQ_trans hA hkK) hfinQ hb hK0
  refine ⟨hK0, fun c hc i (hi : i < K) => ?_⟩
  have cong := E.eval_congr (cpuW_env (A := A) (row := row) (k := k) hi)
  rcases List.mem_append.1 hc with hc | hc
  · rw [cong c (List.all_eq_true.1 (cpuCons_atoms _ _ _) c hc)]
    exact base.2 c hc i hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    have cv : ∀ cc, (col cc).eval ((cpuTableW A row k K).env i) = cpuColW A row k i cc := fun cc => by
      show cpuColW A row k ((i + 0) % K) cc = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
    rcases hc with rfl | rfl | rfl
    · simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
      show (if BLA + 4 < CPU_WIDTH then _ else 0) * ((if BLA + 4 < CPU_WIDTH then _ else 0) - 1) = 0
      rw [if_neg (by decide), zero_mul']
    · simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
      show (if BLB + 4 < CPU_WIDTH then _ else 0) * ((if BLB + 4 < CPU_WIDTH then _ else 0) - 1) = 0
      rw [if_neg (by decide), zero_mul']
    · simp only [B.whenLast, B.eq, E.eval, env_last, sHK1, B.one, B.c, ofN_one]
      split
      · next hl =>
        have hl' : i + 1 = K := hl
        rw [cv]
        show 1 * ((if SEL + 5 < CPU_WIDTH then cpuCol A (rowQ row k i) (SEL + 5) else 0) - 1) = 0
        rw [if_pos (by decide), cpuCol_sel _ _ (by decide)]
        have e : rowQ row k i = row (k - 1) := by
          unfold rowQ; split
          · next h => rw [show i = k - 1 by omega]
          · rfl
        rw [e, hfin5, if_pos rfl, sub_self', mul_zero']
      · exact zero_mul' _

end

section

variable {A : List Cell} {m0 : Mach} {k : Nat} {row : Nat → Row} (hA : AcceptsFrom A m0 k row)
  {K : Nat} (hkK : k ≤ K)
include hA hkK

/-- **The witness-circuit CPU's `mem` messages are honest.** -/
theorem cpuW_honest : ∀ r, r < (cpuTableW A row k K).h → ∀ I ∈ cpuIntersW, I.bus = "mem" →
    I.count.eval ((cpuTableW A row k K).env r) ≠ 0 →
    ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval ((cpuTableW A row k K).env r)) = tupleOf A m := by
  intro r (hr : r < K) I hI hbus hc
  have cong := E.eval_congr (cpuW_env (A := A) (row := row) (k := k) hr)
  rcases List.mem_append.1 hI with hI | hI
  · have ha := List.all_eq_true.1 cpuInters_atoms I hI
    simp only [Bool.and_eq_true, List.all_eq_true] at ha
    rw [cong _ ha.1] at hc
    obtain ⟨m, hm, e⟩ := cpu_honest (M := A) (row := rowQ row k) (k := K) (rowQ_valid hA hkK) r hr I hI hc
    refine ⟨m, hm, ?_⟩
    rw [← e]
    apply List.map_congr_left
    intro c hc'
    exact cong c (ha.2 c hc')
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl <;> exact absurd hbus (by decide)

omit hA hkK in
theorem cpuW_blindZero : ∀ r, r < (cpuTableW A row k K).h → ∀ I ∈ cpuIntersW, I.bus ≠ "mem" →
    I.count.eval ((cpuTableW A row k K).env r) = 0 := by
  intro r (hr : r < K) I hI hb
  have cv : ∀ cc, (col cc).eval ((cpuTableW A row k K).env r) = cpuColW A row k r cc := fun cc => by
    show cpuColW A row k ((r + 0) % K) cc = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hr]
  rcases List.mem_append.1 hI with hI | hI
  · simp only [cpuInters, writeInters, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;> exact absurd rfl hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · show -((col (BLA + 4)).eval _) = 0
      rw [cv]; show -(if BLA + 4 < CPU_WIDTH then _ else 0) = 0; rw [if_neg (by decide)]; decide
    · show (col (BLB + 4)).eval _ = 0
      rw [cv]; show (if BLB + 4 < CPU_WIDTH then _ else 0) = 0; rw [if_neg (by decide)]

end

def progTableW (heap : List Cell) (W : Nat) : Table :=
  ⟨(progRowsW heap W).length, fun _ _ => 0, fun q j => ((progRowsW heap W).getD q []).getD j 0⟩

theorem progRowsW_pos (heap : List Cell) (W : Nat) : 0 < (progRowsW heap W).length := by
  have := pow2From_ge 64 (2 ^ 8) ((heap.zipIdx.filter fun x => !(x.2 < W)).length)
  unfold progRowsW pow2Min
  simp only [List.length_append, List.length_map, List.length_replicate]
  have : (0 : Nat) < 2 ^ 8 := by decide
  omega

theorem progRowsW_le {heap : List Cell} {W : Nat} (h : heap.length ≤ 2 ^ 24) :
    (progRowsW heap W).length ≤ 2 ^ 24 := by
  have hf := List.length_filter_le (fun x : Cell × Nat => !(x.2 < W)) heap.zipIdx
  rw [List.length_zipIdx] at hf
  have hp := pow2From_le (n := (heap.zipIdx.filter fun x => !(x.2 < W)).length) (by omega) 64 8 (by decide)
  unfold progRowsW pow2Min
  simp only [List.length_append, List.length_map, List.length_replicate]
  omega

theorem progW_sat (heap : List Cell) (W : Nat) :
    Sat (progAirW heap W) (progTableW heap W) ∧ PreIs (progAirW heap W) (progTableW heap W) := by
  refine ⟨⟨progRowsW_pos heap W, fun c hc i hi => ?_⟩, ⟨rfl, fun _ _ _ _ => rfl⟩⟩
  simp only [progAirW, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  show (progTableW heap W).main ((i + 0) % _) 0 = 0
  rfl

/-- **The program table's messages are honest**, given the public cells in memory. -/
theorem progW_honest {A heap : List Cell} {W : Nat}
    (hpub : ∀ i, i < heap.length → W ≤ i → i < A.length ∧ A.getD i .nil = heap.getD i .nil) :
    ∀ r, r < (progTableW heap W).h → ∀ I ∈ (progAirW heap W).inters,
      I.count.eval ((progTableW heap W).env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun e => e.eval ((progTableW heap W).env r)) = tupleOf A m := by
  intro q hq I hI hc
  simp only [progAirW, List.mem_cons, List.not_mem_nil, or_false] at hI
  subst hI
  have pv : ∀ j, (prec j).eval ((progTableW heap W).env q) = ((progRowsW heap W).getD q []).getD j 0 := by
    intro j; show (progTableW heap W).pre ((q + 0) % _) j = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
  let pub := heap.zipIdx.filter fun x => !(x.2 < W)
  let rows := pub.map fun (x : Cell × Nat) =>
    [ofN x.2, ofN (cellTag x.1), ofN (cellFields x.1).1, ofN (cellFields x.1).2, ofN 1]
  have hrows : progRowsW heap W = rows ++ List.replicate (pow2Min 8 rows.length - rows.length)
      [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0] := rfl
  rcases Nat.lt_or_ge q rows.length with hl | hl
  · have hg : (progRowsW heap W).getD q [] = rows[q] := by
      rw [hrows, List.getD_eq_getElem?_getD, List.getElem?_append_left hl, List.getElem?_eq_getElem hl]; rfl
    have hm : rows[q] ∈ rows := List.getElem_mem hl
    obtain ⟨⟨c, i⟩, hmp, he⟩ := List.mem_map.1 hm
    obtain ⟨hz, hp⟩ := List.mem_filter.1 hmp
    obtain ⟨_, hi, hc'⟩ := List.mem_zipIdx hz
    simp only [Nat.zero_add, Nat.sub_zero] at hi hc'
    have hp' : W ≤ i := by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hp; omega
    obtain ⟨hiA, hA⟩ := hpub i hi hp'
    have hcell : heap.getD i .nil = c := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hc']; rfl
    refine ⟨i, hiA, ?_⟩
    simp only [List.map_cons, List.map_nil, pv, hg, ← he]
    unfold tupleOf
    rw [hA, hcell]
    rfl
  · exfalso; apply hc
    show (prec 4).eval _ = 0
    rw [pv, hrows, List.getD_eq_getElem?_getD (a := ([] : List F))]
    rcases Nat.lt_or_ge q (rows ++ List.replicate (pow2Min 8 rows.length - rows.length)
        [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0]).length with h' | h'
    · rw [List.getElem?_append_right hl, List.getElem?_replicate]
      simp only [List.length_append, List.length_replicate] at h'
      rw [if_pos (by omega)]; rfl
    · rw [List.getElem?_eq_none h']; rfl

/-- **The witness circuit's buses balance** on the honest tables. -/
theorem balancedW {A : List Cell} {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat} {C Pg Wt : Table}
    (hML : A.length < P)
    (hcM : ∀ r, r < C.h → ∀ I ∈ cpuIntersW, I.bus = "mem" → I.count.eval (C.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (C.env r)) = tupleOf A m)
    (hcZ : ∀ r, r < C.h → ∀ I ∈ cpuIntersW, I.bus ≠ "mem" → I.count.eval (C.env r) = 0)
    (hpM : ∀ r, r < Pg.h → ∀ I ∈ (progAirW heap W).inters, I.count.eval (Pg.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (Pg.env r)) = tupleOf A m)
    (hwM : ∀ r, r < Wt.h → ∀ I ∈ (witAirW W).inters, I.bus = "mem" → I.count.eval (Wt.env r) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (Wt.env r)) = tupleOf A m)
    (hwZ : ∀ r, r < Wt.h → ∀ I ∈ (witAirW W).inters, I.bus ≠ "mem" → I.count.eval (Wt.env r) = 0) :
    Balanced (witTables hd0 stk0 ctr0 heap W C
      (memTableC A (cpuAirW hd0 stk0 ctr0) (progAirW heap W) (witAirW W) C Pg Wt) Pg Wt) := by
  intro B v
  unfold witTables
  simp only [List.foldr_cons, List.foldr_nil]
  let cpu := cpuAirW hd0 stk0 ctr0
  let Mm := memTableC A cpu (progAirW heap W) (witAirW W) C Pg Wt
  have z_prog' : ∀ B', B' ≠ "mem" → tableSends (progAirW heap W) Pg B' v = 0 := fun B' hB =>
    sends_nobus (fun I hI => by
      simp only [progAirW, List.mem_cons, List.not_mem_nil, or_false] at hI; subst hI; exact fun h => hB h.symm)
  by_cases hBm : B = "mem"
  · subst hBm
    have hrow : ∀ m, m < A.length → rowSends memAirC Mm "mem" v m =
        if tupleOf A m = v then -(tableSends cpu C "mem" (tupleOf A m) + (tableSends (progAirW heap W) Pg "mem"
          (tupleOf A m) + tableSends (witAirW W) Wt "mem" (tupleOf A m))) else 0 := by
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
      have hmem : tableSends memAirC Mm "mem" v = -(tableSends cpu C "mem" v +
          (tableSends (progAirW heap W) Pg "mem" v + tableSends (witAirW W) Wt "mem" v)) := by
        show List.foldr (fun r acc => rowSends memAirC Mm "mem" v r + acc) 0 (List.range A.length) = _
        rw [fold_range_single _ A.length m0 hm0, hrow m0 hm0, if_pos e0, e0]
        intro b hb hne
        rw [hrow b hb, if_neg]
        intro e
        rw [← e0] at e
        have := congrArg List.head? e
        simp only [tupleOf, List.head?_cons, Option.some.injEq] at this
        exact hne (ofN_inj (Nat.lt_trans hb hML) (Nat.lt_trans hm0 hML) this)
      rw [hmem]
      show _ + (_ + (_ + (_ + 0))) = 0
      have := bal3_identity (tableSends cpu C "mem" v) (tableSends (progAirW heap W) Pg "mem" v)
        (tableSends (witAirW W) Wt "mem" v)
      rw [zero_add', add_zero'] at this
      rw [add_zero']; exact this
    | false =>
      have hno : ¬ ∃ m, m < A.length ∧ v = tupleOf A m := by
        rintro ⟨m, hm, e⟩
        have := List.any_eq_false.1 hany m (List.mem_range.2 hm)
        exact this (decide_eq_true e.symm)
      have h1 : tableSends cpu C "mem" v = 0 := sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
        (fun r hr I hI hb hc => by obtain ⟨m, hm, e⟩ := hcM r hr I hI hb hc; exact ⟨m, hm, e⟩) hno
      have h2 : tableSends (progAirW heap W) Pg "mem" v = 0 :=
        sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
          (fun r hr I hI _ hc => by obtain ⟨m, hm, e⟩ := hpM r hr I hI hc; exact ⟨m, hm, e⟩) hno
      have h3 : tableSends (witAirW W) Wt "mem" v = 0 :=
        sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
          (fun r hr I hI hb hc => by obtain ⟨m, hm, e⟩ := hwM r hr I hI hb hc; exact ⟨m, hm, e⟩) hno
      have h4 : tableSends memAirC Mm "mem" v = 0 := by
        show List.foldr (fun r acc => rowSends memAirC Mm "mem" v r + acc) 0 (List.range A.length) = 0
        apply fold_zero
        intro m hm
        rw [hrow m (List.mem_range.1 hm), if_neg (fun e => hno ⟨m, List.mem_range.1 hm, e.symm⟩)]
      rw [h1, h2, h3, h4]; decide
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
    have z_cpu : tableSends cpu C B v = 0 := by
      apply sends_zero_of (Q := fun _ => False) _ id
      intro r hr I hI hb hc
      exact hc (hcZ r hr I hI (fun h => hBm (hb ▸ h)))
    have z_wit : tableSends (witAirW W) Wt B v = 0 := by
      apply sends_zero_of (Q := fun _ => False) _ id
      intro r hr I hI hb hc
      exact hc (hwZ r hr I hI (fun h => hBm (hb ▸ h)))
    rw [z_cpu, z_mem, z_prog' B hBm, z_wit]; decide

/-- **Every stack pointer of a run is in memory.** -/
theorem AcceptsFrom.stk_le' {A : List Cell} {m0 : Mach} {k : Nat} {row : Nat → Row}
    (hA : AcceptsFrom A m0 k row) (hfit : Fits A) (h0 : m0.stk ≤ A.length) :
    ∀ i, i < k → (row i).stk ≤ A.length := by
  intro i
  induction i with
  | zero => intro _; rw [hA.stk0]; exact h0
  | succ i ih =>
    intro hi
    rcases hA.trans i hi with h | h
    · exact step_stk hfit h (hA.reach i (by omega)).1 (hA.reach (i + 1) hi).1
    · rw [h.2]; exact ih (by omega)

/-- **Completeness of the hidden-term circuit**: a run the Lean AIR
    accepts from the witness machine of a well-formed region of `W` cells,
    ending at `K` over the empty stack, over a memory of `2^10` cells whose
    cells point into it, in at most `2^10` rows, with `W ≤ 2^8` (the witness
    verifier's heights), gives tables that AIRs with the witness circuit's
    normal forms accept, with Plonky3's selectors; they decode back to the
    memory and the run. -/
theorem wit_complete {V x : Term} {W : Nat} {Rs : List AirD} (hs : sameAirsB Rs (witAirs V x W) = true)
    {ws : List Cell} (hwf : WF ws) (hwl : ws.length = W) (hW : 0 < W) (hW8 : W ≤ 2 ^ 8)
    {A : List Cell} {k : Nat} {row : Nat → Row} (hA : AcceptsFrom A (wMachine ws (V ⬝ x)) k row)
    (hK : rd A (row (k - 1)).ctr (row (k - 1)).hd = some .K ∧ rd A (row (k - 1)).ctr (row (k - 1)).stk = some .nil)
    (hfit : Fits A) (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10) :
    ∃ C Mm Pg Wt, AcceptedP Rs [C, Mm, Pg, Wt] ∧ C.h = 2 ^ 10 ∧ Mm.h = 2 ^ 10 ∧ Wt.h = 2 ^ 8 ∧
      memOf Mm = A ∧ ∀ i, i < k → rowOf C i = row i := by
  have hl : ws.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hwl]
  obtain ⟨hhd, hstk, hlenm, htake, hpub⟩ := wMachine_public ws (List.replicate W .S) (V ⬝ x) hl
  obtain ⟨m0, hm0⟩ : ∃ m, wMachine ws (V ⬝ x) = m := ⟨_, rfl⟩
  rw [hm0] at hA hhd hstk hlenm htake hpub
  have hk0 := hA.pos
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hWl : W ≤ m0.heap.length := by
    have := congrArg List.length htake; rw [List.length_take, hwl] at this; omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hfits0 := wMachine_fits (V ⬝ x) hwf (by omega)
  rw [hm0] at hfits0
  have hfin5 : kindOf A (row (k - 1)) = 5 := by simp only [kindOf, hK.1, hK.2]
  -- the region is in memory
  have hreg : ∀ i, i < W → cellOK (0 + 0 + i) (A.getD (0 + 0 + i) .nil) = true := by
    intro i hi
    simp only [Nat.zero_add]
    rw [hAm i (by omega)]
    have := congrArg (fun l => l[i]?) htake
    simp only [List.getElem?_take, if_pos (show i < ws.length by omega)] at this
    rw [List.getD_eq_getElem?_getD, this, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hwf i _ (List.getElem?_eq_getElem (by omega))
  -- the tables
  let C := cpuTableW A row k (2 ^ 10)
  let blank := wMachine (List.replicate W .S) (V ⬝ x)
  let cpu := cpuAirW blank.hd blank.stk blank.heap.length
  let Pg := progTableW blank.heap W
  let Wt := witTableG 0 A 0 W
  let Mm := memTableC A cpu (progAirW blank.heap W) (witAirW W) C Pg Wt
  have hPP : P = 2013265921 := rfl
  have hcpu : Sat cpu C := by
    have := cpuW_sat hA hk (by omega) (by omega) (by decide) hfin5
    have e0 : rowQ row k 0 = row 0 := by unfold rowQ; rw [if_pos hk0]
    rw [e0, hA.hd0, hA.stk0, hA.ctr0, hhd, hstk, hlenm] at this
    exact this
  have hpubA : ∀ i, i < blank.heap.length → W ≤ i → i < A.length ∧ A.getD i .nil = blank.heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by rw [hlenm]; exact hi
    refine ⟨by omega, ?_⟩
    rw [hAm i hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hpub i (by omega)]
  have hacc : Accepted (witAirs V x W) [C, Mm, Pg, Wt] := by
    have z : (witAirs V x W).zip [C, Mm, Pg, Wt] =
        witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm Pg Wt := rfl
    have hPg : Pg.h ≤ 2 ^ 24 := progRowsW_le (by rw [← hlenm]; omega)
    have hWt : Wt.h = 2 ^ 8 := witRowsG_len (by omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [z]
      intro p hp
      simp only [witTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨hcpu, .inl rfl⟩
      · exact ⟨memC_sat A _ _ _ _ _ _ (by omega), .inl rfl⟩
      · exact ⟨(progW_sat _ _).1, .inr (progW_sat _ _).2⟩
      · exact ⟨wit_sat (a0 := 0) (N := 0) (fun h => absurd h (Nat.lt_irrefl 0)) (fun i hi => absurd hi (Nat.not_lt_zero _))
          hreg (by omega), .inr ⟨rfl, fun _ _ _ _ => rfl⟩⟩
    · rw [z]
      exact balancedW (by omega) (cpuW_honest hA hk) cpuW_blindZero (progW_honest hpubA)
        (witT_honest (a0 := 0) (N := 0) (fun h => absurd h (Nat.lt_irrefl 0)) (fun i hi => absurd hi (Nat.not_lt_zero _))
          hreg (by omega)) witT_blindZero
    · rw [z]
      unfold HeightsOK witTables
      simp only [List.foldr_cons, List.foldr_nil]
      have hC : C.h = 2 ^ 10 := rfl
      have hMm : Mm.h = 2 ^ 10 := hlen
      show 10 * C.h + (1 * Mm.h + (1 * Pg.h + (2 * Wt.h + 0))) < P
      omega
    · rw [z]
      intro p hp
      simp only [witTables, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · show 2 ^ 10 ≤ 2 ^ 27; decide
      · show A.length ≤ 2 ^ 27; omega
      · show Pg.h ≤ 2 ^ 27; omega
      · show Wt.h ≤ 2 ^ 27; omega
  have hRs : AcceptedP Rs [C, Mm, Pg, Wt] :=
    (acceptedP_iff_of (wit_guarded V x W) hs _).2 (accepted_transfer (sameAirsB_symm hs) hacc)
  refine ⟨C, Mm, Pg, Wt, hRs, rfl, hlen, witRowsG_len (by omega), ?_, ?_⟩
  · -- the memory decodes back
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
  · -- the rows decode back
    intro i hi
    have e1 : rowQ row k i = row i := by unfold rowQ; rw [if_pos hi]
    have hc := (hA.reach i hi).1
    have hs' := AcceptsFrom.stk_le' hA hfit (by have := hfits0.2.2; omega) i hi
    have hS := shape (rowQ_valid hA hk i (by omega))
    obtain ⟨cell, hrd, _⟩ := hS.reads 0 (by decide) rfl
    have hh := (rd_get hrd).1
    rw [e1] at hh
    show (⟨(cpuColW A row k i HD).val, (cpuColW A row k i STK).val, (cpuColW A row k i CTR).val⟩ : Row) = row i
    show (⟨(cpuCol A (rowQ row k i) HD).val, (cpuCol A (rowQ row k i) STK).val,
      (cpuCol A (rowQ row k i) CTR).val⟩ : Row) = row i
    rw [e1]
    show (⟨(ofN (row i).hd).val, (ofN (row i).stk).val, (ofN (row i).ctr).val⟩ : Row) = row i
    rw [val_ofN (by show (row i).hd < P; have : (row i).hd < (row i).ctr := hh; omega),
      val_ofN (by omega), val_ofN (by omega)]

end Circuit
