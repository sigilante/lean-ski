import Ski.Circuit.CompPJet

/-!
# The circuit with the Poseidon2 jet: a jet row is `P2Jet.p2Row`

`CompPOK.jetRow`: at a CPU row of kind `12`, the memory holds what the jet
step reads and writes.  P2IN's path reads the bits from the slots and
accumulates them into sixteen elements (`CompPOK.pinVals`); the call's one
Poseidon2 row (`CompPOK.p2Unique`) permutes them; P2OUT's path splits the
outputs into canonical bits (`CompPOK.poutVals`) and writes them as the
stack cells `pushR` describes (`CompPOK.poutCells`).
-/

namespace Circuit

open B Air BitArith

/-- Writes pushing `L` from `c` over `prev`: each cell as the memory holds it. -/
theorem wrs_pushR (M : List Cell) : ∀ (L : List Bool) (c prev : Nat),
    (∀ m, m < L.length → M[c + m]? = some (.cons (P2Jet.bitPtr (L.getD m false)) (if m = 0 then prev else c + m - 1))) →
    wrs M c (P2Jet.pushR c prev L) = true
  | [], _, _, _ => rfl
  | b :: L, c, prev, hm => by
    show ((M[c]? == some (.cons (P2Jet.bitPtr b) prev)) && wrs M (c + 1) (P2Jet.pushR (c + 1) c L)) = true
    have h0 := hm 0 (Nat.zero_lt_succ _)
    rw [Nat.add_zero, show (b :: L).getD 0 false = b from rfl, if_pos rfl] at h0
    rw [h0, beq_self_eq_true, Bool.true_and]
    apply wrs_pushR M L (c + 1) c
    intro m hml
    have := hm (m + 1) (Nat.succ_lt_succ hml)
    rw [show c + (m + 1) = c + 1 + m by omega, if_neg (Nat.succ_ne_zero m)] at this
    rw [this]
    by_cases m0 : m = 0
    · subst m0; rw [if_pos rfl]; rfl
    · rw [if_neg m0, show c + 1 + m - 1 = c + (m + 1) - 1 by omega]; rfl

/-- The slots' bits. -/
theorem bitsAt_slots (H : List Cell) (bI : Nat → Bool) (h0 : H[0]? = some .K) (h1 : H[1]? = some .I)
    (hs : ∀ i, i < 496 → H[i + 3]? = some (if bI i then .K else .app 0 1)) :
    ∀ s k, s + k ≤ 496 → P2Jet.bitsAt H (List.range' (s + 3) k) = some ((List.range' s k).map bI)
  | _, 0, _ => rfl
  | s, k + 1, hk => by
    have ih := bitsAt_slots H bI h0 h1 hs (s + 1) k (by omega)
    rw [show s + 1 + 3 = s + 3 + 1 by omega] at ih
    have hb : P2Jet.boolAt H (s + 3) = some (bI s) := by
      unfold P2Jet.boolAt
      rw [hs s (by omega)]
      cases bI s
      · show (match H[0]?, H[1]? with | some .K, some .I => some false | _, _ => none) = some false
        rw [h0, h1]
      · rfl
    show (match P2Jet.boolAt H (s + 3), P2Jet.bitsAt H (List.range' (s + 3 + 1) k) with
      | some b, some bs => some (b :: bs) | _, _ => none) = some (bI s :: (List.range' (s + 1) k).map bI)
    rw [hb, ih]

/-- Two arguments popped. -/
theorem popN_two {H : List Cell} {s a s1 b s2 : Nat} (h1 : H[s]? = some (.cons a s1)) (h2 : H[s1]? = some (.cons b s2)) :
    Mach.popN H 2 s = some ([a, b], s2) := by
  simp [Mach.popN, h1, h2]

theorem rd_take {M : List Cell} {c a : Nat} {x : Cell} (h : rd M c a = some x) : (M.take c)[a]? = some x := by
  unfold rd at h
  split at h
  · next ha => rw [List.getElem?_take, if_pos ha]; exact h
  · cases h

theorem flatMap_bits_length : ∀ ys : List Nat, (ys.flatMap (bitsOf 31)).length = 31 * ys.length
  | [] => rfl
  | y :: ys => by
    rw [List.flatMap_cons, List.length_append, flatMap_bits_length ys, Poseidon2SKI.bitsOf_length, List.length_cons]
    omega

theorem flatMap_bits_getD : ∀ (ys : List Nat) (ε j : Nat), ε < ys.length → j < 31 →
    (ys.flatMap (bitsOf 31)).getD (31 * ε + j) false = (bitsOf 31 (ys.getD ε 0)).getD j false
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | y :: ys, ε, j, hε, hj => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    cases ε with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by rw [Poseidon2SKI.bitsOf_length]; exact hj)]
      rfl
    | succ ε =>
      rw [List.getElem?_append_right (by rw [Poseidon2SKI.bitsOf_length]; omega), Poseidon2SKI.bitsOf_length,
        show 31 * (ε + 1) + j - 31 = 31 * ε + j by omega, ← List.getD_eq_getElem?_getD,
        flatMap_bits_getD ys ε j (Nat.lt_of_succ_lt_succ hε) hj, List.getD_eq_getElem?_getD]
      rfl


theorem bit_toNat_of {x : F} (h : x * (x - 1) = 0) : x = ofN (decide (x = 1)).toNat := by
  rcases bit_of h with e | e <;> rw [e] <;> rfl

theorem idx_tail {i : Nat} {a b c' d f : F} (h : [a, b, c', d, f] = (idxRow i).tail) :
    a = ofN (i / 31) ∧ b = ofN (2 ^ (i % 31)) ∧ c' = ofN (if i % 31 = 30 then 1 else 0) ∧
      d = ofN (if i % 31 < 27 then 1 else 0) ∧ f = ofN (if i = P2_BITS - 1 then 1 else 0) := by
  rw [idx_e] at h
  simp only [List.cons.injEq, and_true] at h
  exact h

theorem add_add_sub (a b c : F) : a + (b + c) - c = a + b :=
  E.eval_eq_of_norm (e := .sub (.add (.atom (.main 0 0)) (.add (.atom (.main 0 1)) (.atom (.main 0 2))))
      (.atom (.main 0 2))) (e' := .add (.atom (.main 0 0)) (.atom (.main 0 1))) (by decide)
    (fun | .main 0 0 => a | .main 0 1 => b | .main 0 2 => c | _ => 0)

/-- `a + ofN k - ofN i = a + ofN (k - i)` for `i ≤ k`. -/
theorem add_ofN_sub {a : F} {k i : Nat} (hi : i ≤ k) : a + ofN k - ofN i = a + ofN (k - i) := by
  rw [show k = (k - i) + i by omega, ofN_add, Nat.add_sub_cancel]
  exact add_add_sub _ _ _

theorem getD_map_range {α : Type} (f : Nat → α) (d : α) {n k : Nat} (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl

theorem preB_getD (b : Nat → Bool) (base : Nat) {j k : Nat} (hj : j < k) : (preB b base k).getD j false = b (base + j) :=
  getD_map_range _ _ hj

theorem ofN_val' (n : Nat) : (ofN n).val = n % P := rfl

theorem sub_add_one_eq (a b : F) : a - b + 1 = (a + 1) - b :=
  E.eval_eq_of_norm (e := .add (.sub (.atom (.main 0 0)) (.atom (.main 0 1))) (.const 1))
      (e' := .sub (.add (.atom (.main 0 0)) (.const 1)) (.atom (.main 0 1))) (by decide)
    (fun | .main 0 0 => a | .main 0 1 => b | _ => 0)

theorem popN_succ {H : List Cell} {k s x r : Nat} (h : H[s]? = some (.cons x r)) :
    Mach.popN H (k + 1) s = (Mach.popN H k r).map fun p => (x :: p.1, p.2) := by
  show (match H[s]? with | some (.cons x r) => _ | _ => none) = _
  rw [h]

/-- `popN` along a chain of stack cells. -/
theorem popN_chain (H : List Cell) (a p : Nat → Nat) : ∀ (n i : Nat),
    (∀ j, j < n → H[a (i + j)]? = some (.cons (p (i + j)) (a (i + j + 1)))) →
    Mach.popN H n (a i) = some ((List.range' i n).map p, a (i + n))
  | 0, i, _ => by simp [Mach.popN]
  | n + 1, i, hc => by
    have h0 := hc 0 (Nat.zero_lt_succ _)
    simp only [Nat.add_zero] at h0
    have ih := popN_chain H a p n (i + 1) (fun j hj => by
      have := hc (j + 1) (by omega)
      rwa [show i + (j + 1) = i + 1 + j by omega] at this)
    simp only [Mach.popN, h0, ih, Option.map_some, List.range'_succ, List.map_cons,
      show i + 1 + n = i + (n + 1) by omega]

theorem ptrBits_map (b : Nat → Bool) : ∀ L : List Nat,
    P2Jet.ptrBits (L.map fun i => P2Jet.bitPtr (b i)) = some (L.map b)
  | [] => rfl
  | i :: L => by
    simp only [List.map_cons, P2Jet.ptrBits, ptrBits_map b L]
    cases b i <;> rfl

theorem consecFrom_of (H : List Cell) (a x : Nat → Nat) : ∀ n i,
    (∀ j, j < n → H[a (i + j)]? = some (.cons (x (i + j)) (a (i + j + 1))) ∧ a (i + j + 1) + 1 = a (i + j)) →
    P2Jet.consecFrom H (a i) n = true
  | 0, _, _ => rfl
  | n + 1, i, hc => by
    obtain ⟨h0, e0⟩ := hc 0 (Nat.zero_lt_succ _)
    simp only [Nat.add_zero] at h0 e0
    have ih := consecFrom_of H a x n (i + 1) (fun j hj => by
      have := hc (j + 1) (by omega)
      rwa [show i + (j + 1) = i + 1 + j by omega] at this)
    unfold P2Jet.consecFrom
    rw [h0]
    dsimp only
    rw [e0, ih, show (a i == a i) = true from decide_eq_true rfl]
    rfl

section
variable {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg Pi Po Pp Px : Table}
  (h : CompPOK hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px)
include h

/-- **P2IN's elements** are the values of its bits, 31 to an element. -/
theorem CompPOK.pinVals {t m0 s0 : F} {e : Nat → Nat} {st : Nat → List F} (h0 : st 0 = [0, m0, s0])
    (hrows : ∀ i, i < P2_BITS → e i < Pi.h ∧ Pi.main (e i) 4 = 1 ∧ Pi.main (e i) 0 = t ∧
      Pi.main (e i) 1 = ofN i ∧ [Pi.main (e i) 3, Pi.main (e i) 13, Pi.main (e i) 14] = st i ∧
      [Pi.main (e i) 11, Pi.main (e i) 13, Pi.main (e i) 15] = st (i + 1))
    {ε : Nat} (he : ε < 16) :
    Pi.main (e (31 * ε + 30)) 10 =
      ofN (val (preB (fun i => decide (Pi.main (e i) 2 = 1)) (31 * ε) 31)) := by
  have lev : ∀ i, i < P2_BITS → Pi.main (e i) 6 = ofN (2 ^ (i % 31)) ∧
      Pi.main (e i) 7 = ofN (if i % 31 = 30 then 1 else 0) := fun i hi => by
    obtain ⟨hq, ha, _, hl, _, _⟩ := hrows i hi
    have := idx_tail (h.pinLevel hq ha hl hi)
    exact ⟨this.2.1, this.2.2.1⟩
  have next : ∀ i, i + 1 < P2_BITS → Pi.main (e (i + 1)) 3 = (1 - Pi.main (e i) 7) * Pi.main (e i) 10 := by
    intro i hi
    obtain ⟨hq, _, _, _, _, hd⟩ := hrows i (by omega)
    obtain ⟨_, _, _, _, hs', _⟩ := hrows (i + 1) hi
    rw [← hs'] at hd
    simp only [List.cons.injEq, and_true] at hd
    rw [← hd.1, (pin_eqs h.pin hq).2.2.1]
  have base0 : Pi.main (e (31 * ε)) 3 = 0 := by
    cases ε with
    | zero =>
      obtain ⟨_, _, _, _, hs0, _⟩ := hrows 0 (by decide)
      rw [h0] at hs0
      simp only [List.cons.injEq, and_true] at hs0
      exact hs0.1
    | succ ε' =>
      have hi : 31 * ε' + 30 + 1 < P2_BITS := by unfold P2_BITS; omega
      rw [show 31 * (ε' + 1) = 31 * ε' + 30 + 1 by omega, next _ hi,
        (lev _ (by omega)).2, show (31 * ε' + 30) % 31 = 30 by omega, if_pos rfl]
      show (1 - (1 : F)) * _ = 0
      rw [sub_self', zero_mul']
  have := accum (fun i => Pi.main (e i) 3) (fun i => Pi.main (e i) 10) (fun i => decide (Pi.main (e i) 2 = 1))
    (31 * ε) base0 (fun j hj => by
      have hi : 31 * ε + j < P2_BITS := by unfold P2_BITS; omega
      obtain ⟨hq, _, _, _, _, _⟩ := hrows _ hi
      have eqs := pin_eqs h.pin hq
      rw [eqs.2.1, (lev _ hi).1, show (31 * ε + j) % 31 = j by omega, ← bit_toNat_of eqs.1])
    (fun j hj => by
      have hi : 31 * ε + j + 1 < P2_BITS := by unfold P2_BITS; omega
      show Pi.main (e (31 * ε + j + 1)) 3 = _
      rw [next _ hi, (lev _ (by omega)).2, show (31 * ε + j) % 31 = j by omega, if_neg (by omega)]
      show (1 - (0 : F)) * _ = _
      rw [show (1 : F) - 0 = 1 by decide, one_mul'])
    30 (by decide)
  exact this

/-- **P2OUT's elements** are the values of its bits, each canonical. -/
theorem CompPOK.poutVals {t rest : F} {e : Nat → Nat} {st : Nat → List F} (h0 : st 0 = [rest, 0, 0, 1])
    (hrows : ∀ i, i < P2_BITS → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = t ∧
      Po.main (e i) 1 = ofN i ∧ [Po.main (e i) 2, Po.main (e i) 4, Po.main (e i) 5, Po.main (e i) 6] = st i ∧
      [Po.main (e i) 2, Po.main (e i) 14, Po.main (e i) 17, Po.main (e i) 18] = st (i + 1))
    {ε : Nat} (he : ε < 16) :
    Po.main (e (31 * ε + 30)) 13 = ofN (val (preB (fun i => decide (Po.main (e i) 3 = 1)) (31 * ε) 31)) ∧
      val (preB (fun i => decide (Po.main (e i) 3 = 1)) (31 * ε) 31) < Poseidon2.p := by
  have lev : ∀ i, i < P2_BITS → Po.main (e i) 9 = ofN (2 ^ (i % 31)) ∧
      Po.main (e i) 10 = ofN (if i % 31 = 30 then 1 else 0) ∧ Po.main (e i) 11 = ofN (if i % 31 < 27 then 1 else 0) := by
    intro i hi
    obtain ⟨hq, ha, _, hl, _, _⟩ := hrows i hi
    have := idx_tail (h.poutLevel hq ha hl hi)
    exact ⟨this.2.1, this.2.2.1, this.2.2.2.1⟩
  have next : ∀ i, i + 1 < P2_BITS → Po.main (e (i + 1)) 4 = Po.main (e i) 14 ∧
      Po.main (e (i + 1)) 5 = Po.main (e i) 17 ∧ Po.main (e (i + 1)) 6 = Po.main (e i) 18 := by
    intro i hi
    obtain ⟨_, _, _, _, _, hd⟩ := hrows i (by omega)
    obtain ⟨_, _, _, _, hs', _⟩ := hrows (i + 1) hi
    rw [← hs'] at hd
    simp only [List.cons.injEq, and_true] at hd
    exact ⟨hd.2.1.symm, hd.2.2.1.symm, hd.2.2.2.symm⟩
  have eqsAt := fun i (hi : i < P2_BITS) => pout_eqs h.pout (hrows i hi).1
  -- the element's start: nothing accumulated, the flags reset
  have base : Po.main (e (31 * ε)) 4 = 0 ∧ Po.main (e (31 * ε)) 5 = 0 ∧ Po.main (e (31 * ε)) 6 = 1 := by
    cases ε with
    | zero =>
      obtain ⟨_, _, _, _, hs0, _⟩ := hrows 0 (by decide)
      rw [h0] at hs0
      simp only [List.cons.injEq, and_true] at hs0
      exact ⟨hs0.2.1, hs0.2.2.1, hs0.2.2.2⟩
    | succ ε' =>
      have hi : 31 * ε' + 30 + 1 < P2_BITS := by unfold P2_BITS; omega
      obtain ⟨n4, n5, n6⟩ := next _ hi
      have hl := (lev (31 * ε' + 30) (by unfold P2_BITS; omega)).2.1
      rw [show (31 * ε' + 30) % 31 = 30 by omega, if_pos rfl] at hl
      have eqs := eqsAt (31 * ε' + 30) (by unfold P2_BITS; omega)
      rw [show 31 * (ε' + 1) = 31 * ε' + 30 + 1 by omega, n4, n5, n6, eqs.2.2.1, eqs.2.2.2.2.2.2.1,
        eqs.2.2.2.2.2.2.2.1, hl, show (1 : F) - ofN 1 = 0 by decide, zero_mul', zero_mul', zero_mul', zero_add']
      exact ⟨rfl, rfl, rfl⟩
  have hidx : ∀ j, j < 31 → 31 * ε + j < P2_BITS := fun j hj => by unfold P2_BITS; omega
  have bitv : ∀ j, j < 31 → Po.main (e (31 * ε + j)) 3 = ofN (decide (Po.main (e (31 * ε + j)) 3 = 1)).toNat :=
    fun j hj => bit_toNat_of (eqsAt _ (hidx j hj)).1
  have mid : ∀ j, j < 30 → Po.main (e (31 * ε + j)) 10 = 0 := fun j hj => by
    rw [(lev _ (hidx j (by omega))).2.1, show (31 * ε + j) % 31 = j by omega, if_neg (by omega)]; rfl
  have hval := accum (fun i => Po.main (e i) 4) (fun i => Po.main (e i) 13) (fun i => decide (Po.main (e i) 3 = 1))
    (31 * ε) base.1 (fun j hj => by
      show Po.main (e (31 * ε + j)) 13 = _
      rw [(eqsAt _ (hidx j hj)).2.1, (lev _ (hidx j hj)).1, show (31 * ε + j) % 31 = j by omega, ← bitv j hj])
    (fun j hj => by
      show Po.main (e (31 * ε + j + 1)) 4 = _
      rw [(next _ (by have := hidx (j + 1) (by omega); omega)).1, (eqsAt _ (hidx j (by omega))).2.2.1, mid j hj,
        show (1 : F) - 0 = 1 by decide, one_mul'])
    30 (by decide)
  have hflags := lowhi (fun i => Po.main (e i) 5) (fun i => Po.main (e i) 6) (fun i => Po.main (e i) 15)
    (fun i => Po.main (e i) 16) (fun i => decide (Po.main (e i) 3 = 1)) (31 * ε) base.2.1 base.2.2
    (fun j hj => by
      show Po.main (e (31 * ε + j)) 15 = _
      rw [(eqsAt _ (hidx j hj)).2.2.2.1, (lev _ (hidx j hj)).2.2, show (31 * ε + j) % 31 = j by omega, ← bitv j hj])
    (fun j hj => by
      show Po.main (e (31 * ε + j)) 16 = _
      rw [(eqsAt _ (hidx j hj)).2.2.2.2.1, (lev _ (hidx j hj)).2.2, show (31 * ε + j) % 31 = j by omega, ← bitv j hj])
    (fun j hj => by
      show Po.main (e (31 * ε + j + 1)) 5 = _
      rw [(next _ (by have := hidx (j + 1) (by omega); omega)).2.1, (eqsAt _ (hidx j (by omega))).2.2.2.2.2.2.1,
        mid j hj, show (1 : F) - 0 = 1 by decide, one_mul'])
    (fun j hj => by
      show Po.main (e (31 * ε + j + 1)) 6 = _
      rw [(next _ (by have := hidx (j + 1) (by omega); omega)).2.2, (eqsAt _ (hidx j (by omega))).2.2.2.2.2.2.2.1,
        mid j hj, show (1 : F) - 0 = 1 by decide, one_mul', add_zero'])
    30 (by decide)
  refine ⟨hval, canon _ _ (fun hb => ?_)⟩
  have hz := (eqsAt _ (hidx 30 (by decide))).2.2.2.2.2.1
  rw [(lev _ (hidx 30 (by decide))).2.1, show (31 * ε + 30) % 31 = 30 by omega, if_pos rfl, hflags.2,
    hflags.1, hb.1, hb.2] at hz
  exact absurd hz (by decide)

omit h in
/-- P2OUT's rows all carry the call's `rest`. -/
theorem poutRest {Po : Table} {t rest : F} {e : Nat → Nat} {st : Nat → List F} (h0 : st 0 = [rest, 0, 0, 1])
    (hrows : ∀ i, i < P2_BITS → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = t ∧
      Po.main (e i) 1 = ofN i ∧ [Po.main (e i) 2, Po.main (e i) 4, Po.main (e i) 5, Po.main (e i) 6] = st i ∧
      [Po.main (e i) 2, Po.main (e i) 14, Po.main (e i) 17, Po.main (e i) 18] = st (i + 1)) :
    ∀ i, i < P2_BITS → Po.main (e i) 2 = rest
  | 0, hi => by
    obtain ⟨_, _, _, _, hs, _⟩ := hrows 0 hi
    rw [h0] at hs
    simp only [List.cons.injEq] at hs
    exact hs.1
  | i + 1, hi => by
    obtain ⟨_, _, _, _, _, hd⟩ := hrows i (by omega)
    obtain ⟨_, _, _, _, hs, _⟩ := hrows (i + 1) hi
    rw [← hs] at hd
    simp only [List.cons.injEq] at hd
    rw [← hd.1]
    exact poutRest h0 hrows i (by omega)

/-- **P2OUT's writes**: the output bit `i` at `ctr + 495 - i`, over the cell
    below it, or over `rest` at the bottom. -/
theorem CompPOK.poutCells {t rest : F} {e : Nat → Nat} {st : Nat → List F} (h0 : st 0 = [rest, 0, 0, 1])
    (hrows : ∀ i, i < P2_BITS → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = t ∧
      Po.main (e i) 1 = ofN i ∧ [Po.main (e i) 2, Po.main (e i) 4, Po.main (e i) 5, Po.main (e i) 6] = st i ∧
      [Po.main (e i) 2, Po.main (e i) 14, Po.main (e i) 17, Po.main (e i) 18] = st (i + 1))
    (ht : t.val + P2_BITS < P) {i : Nat} (hi : i < P2_BITS) :
    (memOf Mm)[t.val + 495 - i]? = some (.cons (P2Jet.bitPtr (decide (Po.main (e i) 3 = 1)))
      (if i = 495 then rest.val else t.val + 494 - i)) := by
  obtain ⟨hq, ha, h0', hl, _, _⟩ := hrows i hi
  have eqs := pout_eqs h.pout hq
  have lv := idx_tail (h.poutLevel hq ha hl hi)
  obtain ⟨hw1, hw2⟩ := h.poutWrite hq ha
  have e20 := eqs.2.2.2.2.2.2.2.2.2.1
  have e21 := eqs.2.2.2.2.2.2.2.2.2.2.1
  have e22 := eqs.2.2.2.2.2.2.2.2.2.2.2
  rw [ha, one_mul'] at e20 e21 e22
  have f20 := sub_eq_zero e20
  have f21 := sub_eq_zero e21
  have f22 := sub_eq_zero e22
  have hi' : i ≤ 495 := by unfold P2_BITS at hi; omega
  rw [h0', hl, show P2_BITS - 1 = 495 from rfl, add_ofN_sub hi'] at f20
  have v20 : (Po.main (e i) 20).val = t.val + 495 - i := by
    rw [f20, val_add_nat (by unfold P2_BITS at ht; omega)]; omega
  rw [v20] at hw2
  rw [hw2]
  have hb := bit_toNat_of eqs.1
  have v22 : (Po.main (e i) 22).val = P2Jet.bitPtr (decide (Po.main (e i) 3 = 1)) := by
    rw [f22]
    generalize decide (Po.main (e i) 3 = 1) = b at hb
    rw [hb]; cases b <;> rfl
  rw [v22, lv.2.2.2.2, show P2_BITS - 1 = 495 from rfl] at *
  congr 2
  rw [f21, poutRest h0 hrows i hi, f20]
  by_cases h495 : i = 495
  · rw [if_pos h495, if_pos h495]
    show (ofN 1 * rest + (1 - ofN 1) * _).val = _
    rw [show (1 : F) - ofN 1 = 0 by decide, zero_mul', add_zero', ofN_one, one_mul']
  · rw [if_neg h495, if_neg h495]
    show (ofN 0 * rest + (1 - ofN 0) * (t + ofN (495 - i) - 1)).val = _
    rw [ofN_zero, zero_mul', zero_add', show (1 : F) - 0 = 1 by decide, one_mul',
      show (1 : F) = ofN 1 from rfl, show 495 - i = (494 - i) + 1 by omega, ofN_add, add_add_sub,
      val_add_nat (by unfold P2_BITS at ht; omega)]
    omega
/-- **The call's outputs**: P2OUT's bits are the bits of the permutation of
    the slot bits' elements. -/
theorem CompPOK.jetOut {t rest m0 s0 : F}
    {eI : Nat → Nat} {stI : Nat → List F} (hI0 : stI 0 = [0, m0, s0])
    (hrowsI : ∀ i, i < P2_BITS → eI i < Pi.h ∧ Pi.main (eI i) 4 = 1 ∧ Pi.main (eI i) 0 = t ∧
      Pi.main (eI i) 1 = ofN i ∧ [Pi.main (eI i) 3, Pi.main (eI i) 13, Pi.main (eI i) 14] = stI i ∧
      [Pi.main (eI i) 11, Pi.main (eI i) 13, Pi.main (eI i) 15] = stI (i + 1))
    (hallI : ∀ q, q < Pi.h → Pi.main q 4 = 1 → Pi.main q 0 = t → ∃ i, i < P2_BITS ∧ eI i = q)
    {eO : Nat → Nat} {stO : Nat → List F} (hO0 : stO 0 = [rest, 0, 0, 1])
    (hrowsO : ∀ i, i < P2_BITS → eO i < Po.h ∧ Po.main (eO i) 7 = 1 ∧ Po.main (eO i) 0 = t ∧
      Po.main (eO i) 1 = ofN i ∧ [Po.main (eO i) 2, Po.main (eO i) 4, Po.main (eO i) 5, Po.main (eO i) 6] = stO i ∧
      [Po.main (eO i) 2, Po.main (eO i) 14, Po.main (eO i) 17, Po.main (eO i) 18] = stO (i + 1))
    (hallO : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = t → ∃ i, i < P2_BITS ∧ eO i = q) :
    ∀ i, i < P2_BITS → decide (Po.main (eO i) 3 = 1) =
      (P2Jet.outBits ((List.range P2_BITS).map fun i => decide (Pi.main (eI i) 2 = 1))).getD i false := by
  let bI : Nat → Bool := fun i => decide (Pi.main (eI i) 2 = 1)
  let bO : Nat → Bool := fun i => decide (Po.main (eO i) 3 = 1)
  let bs : List Bool := (List.range P2_BITS).map bI
  obtain ⟨qs, hqs, hact, hkey, hins, huniq⟩ := h.p2Unique hrowsI hallI
  have hvals : Poseidon2SKI.valsB bs = (List.range 16).map fun ε => val (preB bI (31 * ε) 31) := by
    unfold Poseidon2SKI.valsB Poseidon2SKI.chunk
    refine List.map_congr_left fun ε hε => ?_
    apply congrArg val
    refine List.map_congr_left fun j hj => ?_
    have hε' := List.mem_range.1 hε
    have hj' := List.mem_range.1 hj
    show bs.getD (31 * ε + j) false = bI (31 * ε + j)
    exact getD_map_range _ _ (by unfold P2_BITS; omega)
  have hlen : (Poseidon2SKI.valsB bs).length = 16 := by simp [Poseidon2SKI.valsB]
  let Y := Poseidon2.permute (Poseidon2SKI.valsB bs)
  have hYlen : Y.length = 16 := Poseidon2SKI.permute_len _ hlen
  have hsound := P2Air.p2_sound_row Pp h.p2 qs hqs
  have hinsv : (P2Air.ins (Pp.env qs)).map Fin.val = (Poseidon2SKI.valsB bs).map (· % Poseidon2.p) := by
    unfold P2Air.ins
    rw [hvals, List.map_map, List.map_map]
    refine List.map_congr_left fun ε hε => ?_
    have hε' := List.mem_range.1 hε
    show (Pp.env qs (.main 0 ε)).val = _
    rw [env_main0 hqs, hins ε hε', h.pinVals hI0 hrowsI hε', ofN_val']
    rfl
  rw [hinsv, ← P2Air.permute_mod _ hlen] at hsound
  have hY : ∀ ε, ε < 16 → val (preB bO (31 * ε) 31) = Y.getD ε 0 := by
    intro ε hε
    obtain ⟨hv, hlt⟩ := h.poutVals hO0 hrowsO hε
    have hm := h.p2wMatch hrowsO hallO hqs hact hkey huniq hε
    have hg := congrArg (fun l => l.getD ε (ofN 0)) hsound
    rw [show (ofN 0 : F) = (c 0).eval (Pp.env qs) from rfl, P2Air.getD_map, show (c 0).eval (Pp.env qs) = ofN 0 from rfl,
      P2Air.getD_map] at hg
    rw [hm, hv] at hg
    have hYlt : Y.getD ε 0 < Poseidon2.p := by
      apply P2Air.permute_lt _ hlen
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hYlen]; exact hε)]
      exact List.getElem_mem _
    rw [P2Air.p_eq] at hlt hYlt
    exact ofN_inj hlt hYlt hg
  intro i hi
  have hε : i / 31 < 16 := by unfold P2_BITS at hi; omega
  have hj : i % 31 < 31 := Nat.mod_lt _ (by decide)
  have hi' : i = 31 * (i / 31) + i % 31 := by omega
  show bO i = _
  rw [hi', ← preB_getD bO (31 * (i / 31)) hj, ← Poseidon2SKI.bitsOf_val (preB bO (31 * (i / 31)) 31),
    preB_length, hY _ hε, P2Jet.outBits, flatMap_bits_getD _ _ _ (by rw [hYlen]; exact hε) hj]

/-- **A jet row is the jet's step**: `P2Jet.p2Row` over the memory takes it
    to the next row on the comb, `P2Jet.p2RowS` on the stack. -/
theorem CompPOK.jetRow {r0 : Nat} (hn : r0 + 1 < C.h) (hp : C.main r0 P2SEL = 1) (hJ : J + 1 < P) (hroot : root < P)
    (hctr : 499 ≤ (C.main r0 CTR).val) :
    P2Jet.p2Row (memOf Mm) J root (rowOf C r0) = some (rowOf C (r0 + 1)) ∨
      P2Jet.p2RowS (memOf Mm) (J + 1) (rowOf C r0) = some (rowOf C (r0 + 1)) := by
  have hr0 : r0 < C.h := Nat.lt_of_succ_lt hn
  obtain ⟨hmode, rd1, rd2, m0, m1, m2⟩ := h.jetReads hr0 hp hJ hroot
  obtain ⟨eI, stI, hI0, hIk, hrowsI, hallI⟩ := h.pinPath hr0 hp
  obtain ⟨eO, stO, hO0, _, hrowsO, hallO⟩ := h.poutPath hr0 hp
  let bI : Nat → Bool := fun i => decide (Pi.main (eI i) 2 = 1)
  let bs : List Bool := (List.range P2_BITS).map bI
  have hout := h.jetOut hI0 hrowsI hallI hO0 hrowsO hallO
  have hctrP : (C.main r0 CTR).val + P2_BITS < P := by
    have := h.ctr_lt hr0; unfold P2_BITS; have : 2 ^ 27 + 2 ^ 24 + 1 + 496 < P := by decide
    omega
  -- every input row carries the jet row's mode, and its stack pointers chain
  have hst : ∀ i, i ≤ P2_BITS → (stI i).getD 1 0 = C.main r0 P2MODE := by
    intro i
    induction i with
    | zero => intro _; rw [hI0]; rfl
    | succ i ih =>
      intro hi
      obtain ⟨_, _, _, _, hs, hd⟩ := hrowsI i (by omega)
      rw [← hd, ← ih (by omega), ← hs]; rfl
  have hmrow : ∀ i, i < P2_BITS → Pi.main (eI i) 13 = C.main r0 P2MODE := fun i hi => by
    obtain ⟨_, _, _, _, hs, _⟩ := hrowsI i hi
    rw [← hst i (by omega), ← hs]; rfl
  have hsp : ∀ i, i < P2_BITS →
      Pi.main (eI i) 14 = (stI i).getD 2 0 ∧ Pi.main (eI i) 15 = (stI (i + 1)).getD 2 0 := fun i hi => by
    obtain ⟨_, _, _, _, hs, hd⟩ := hrowsI i hi
    exact ⟨by rw [← hs]; rfl, by rw [← hd]; rfl⟩
  have hbm : C.main r0 P2MODE = 0 ∨ C.main r0 P2MODE = 1 := by
    rcases hmode with ⟨e, _⟩ | ⟨e, _⟩
    · exact .inl e
    · exact .inr e
  have hread : ∀ i, i < P2_BITS → ∃ b : Bool, Pi.main (eI i) 2 = ofN b.toNat ∧
      ((Pi.main (eI i) 13 = 0 ∧ i + 3 < Mm.h ∧ (memOf Mm)[i + 3]? = some (if b then .K else .app 0 1)) ∨
       (Pi.main (eI i) 13 = 1 ∧ (Pi.main (eI i) 14).val < Mm.h ∧
         (memOf Mm)[(Pi.main (eI i) 14).val]? = some (.cons (P2Jet.bitPtr b) (Pi.main (eI i) 15).val))) :=
    fun i hi => by
      obtain ⟨hq, ha, _, hl, _, _⟩ := hrowsI i hi
      exact h.pinRead hq ha hl hi (by rw [hmrow i hi]; exact hbm)
  have hbI : ∀ i (b : Bool), Pi.main (eI i) 2 = ofN b.toNat → bI i = b := fun i b hb => by
    show decide (Pi.main (eI i) 2 = 1) = b
    rw [hb]; cases b <;> decide
  -- the outputs, pushed over the stack below the inputs
  have hob : (P2Jet.outBits bs).length = 496 := by
    unfold P2Jet.outBits
    rw [flatMap_bits_length, Poseidon2SKI.permute_len _ (by simp [Poseidon2SKI.valsB])]
  have hw : wrs (memOf Mm) (C.main r0 CTR).val
      (P2Jet.pushR (C.main r0 CTR).val (C.main r0 P2REST).val (P2Jet.outBits bs).reverse) = true := by
    apply wrs_pushR
    intro m hm
    rw [List.length_reverse, hob] at hm
    have hi : 495 - m < P2_BITS := by unfold P2_BITS; omega
    have hc := h.poutCells hO0 hrowsO hctrP hi
    rw [show (C.main r0 CTR).val + 495 - (495 - m) = (C.main r0 CTR).val + m by omega, hout _ hi] at hc
    rw [hc]
    have hrev : (P2Jet.outBits bs).reverse.getD m false = (P2Jet.outBits bs).getD (495 - m) false := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [hob]; exact hm), hob]
    rw [hrev]
    by_cases m0' : m = 0
    · subst m0'; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (by omega), if_neg m0', show (C.main r0 CTR).val + 494 - (495 - m) = (C.main r0 CTR).val + m - 1 by omega]
  obtain ⟨n1, n2, n3⟩ := h.jetNext hn hp
  let H := (memOf Mm).take (C.main r0 CTR).val
  have hH : ∀ a, a < (C.main r0 CTR).val → H[a]? = (memOf Mm)[a]? := fun a ha => by
    show ((memOf Mm).take _)[a]? = _
    rw [List.getElem?_take, if_pos ha]
  have hslots : P2Jet.slotsOK H = true := by
    unfold P2Jet.slotsOK
    rw [hH 0 (by omega), hH 1 (by omega), hH 2 (by omega), m0, m1, m2]; rfl
  have hc' : (C.main r0 CTR).val + 496 < P := hctrP
  rcases hmode with ⟨hm0, rd0, hβ, hrest, _⟩ | ⟨hm1, rd0, hsp0⟩
  · -- on the comb: the slots hold the bits
    left
    have slot : ∀ i, i < 496 → (memOf Mm)[i + 3]? = some (if bI i then .K else .app 0 1) := by
      intro i hi
      obtain ⟨b, hb, hc⟩ := hread i hi
      rcases hc with ⟨_, _, hm⟩ | ⟨hm', _⟩
      · rw [hbI i b hb]; exact hm
      · rw [hmrow i hi, hm0] at hm'; exact absurd hm' (by decide)
    have hbits : P2Jet.bitsAt H P2Jet.slotAddrs = some bs := by
      have := bitsAt_slots H bI (by rw [hH 0 (by omega), m0]) (by rw [hH 1 (by omega), m1])
        (fun i hi => by rw [hH (i + 3) (by omega), slot i hi]) 0 496 (by decide)
      rw [Nat.zero_add] at this
      show P2Jet.bitsAt H (List.range' 3 496) = some ((List.range 496).map bI)
      rw [this, List.range_eq_range']
    rw [hrest] at hw
    unfold P2Jet.p2Row
    simp only [rowOf]
    rw [show ((memOf Mm).take (C.main r0 CTR).val)[(C.main r0 HD).val]? = some (.atom J) from rd_take rd0]
    simp only [true_and]
    have hslots' : P2Jet.slotsOK ((memOf Mm).take (C.main r0 CTR).val) = true := hslots
    have hbits' : P2Jet.bitsAt ((memOf Mm).take (C.main r0 CTR).val) P2Jet.slotAddrs = some bs := hbits
    rw [if_pos hslots', popN_two (rd_take rd1) (rd_take rd2)]
    simp only [hβ, if_true]
    rw [hbits']
    simp only [if_pos hw, hob, n1, n2, n3]
    unfold P2Jet.topOf
    rw [if_neg (by decide), show P2_BITS - 1 = 495 from rfl, show P2_BITS = 496 from rfl,
      val_add_nat (by omega), val_add_nat (by omega)]
    rfl
  · -- on the stack: the inputs are consecutive cells below `s₁`
    right
    let a : Nat → Nat := fun i => ((stI i).getD 2 0).val
    have hmh := h.mem_h
    have hcell : ∀ i, i < P2_BITS → (memOf Mm)[a i]? = some (.cons (P2Jet.bitPtr (bI i)) (a (i + 1))) ∧
        a i < Mm.h := by
      intro i hi
      obtain ⟨b, hb, hc⟩ := hread i hi
      rcases hc with ⟨hm', _⟩ | ⟨_, hlt, hm⟩
      · rw [hmrow i hi, hm1] at hm'; exact absurd hm' (by decide)
      · obtain ⟨e14, e15⟩ := hsp i hi
        rw [e14, e15] at hm; rw [e14] at hlt
        rw [hbI i b hb]; exact ⟨hm, hlt⟩
    have hstep : ∀ i, i + 1 < P2_BITS → a (i + 1) + 1 = a i := by
      intro i hi
      obtain ⟨hq, ha, _, hl, _, _⟩ := hrowsI i (by omega)
      obtain ⟨_, e21, _, _, _, _, _, e22, e12⟩ := pin_eqsR h.pin hq
      rw [ha, hmrow i (by omega), hm1, one_mul'] at e21
      have hlast := (idx_tail (h.pinLevel hq ha hl (by omega))).2.2.2.2
      rw [if_neg (show ¬ (i = P2_BITS - 1) by unfold P2_BITS at hi ⊢; omega)] at hlast
      rw [e21, hlast, show (1 : F) - ofN 0 = 1 by decide, one_mul'] at e22
      rw [e22, one_mul', sub_add_one_eq] at e12
      have e := sub_eq_zero e12
      obtain ⟨e14, e15⟩ := hsp i (by omega)
      rw [e14, e15] at e
      have h1 := (hcell (i + 1) hi).2
      have h0 := (hcell i (by omega)).2
      show ((stI (i + 1)).getD 2 0).val + 1 = ((stI i).getD 2 0).val
      have hP : a (i + 1) + 1 < P := by
        have : 2 ^ 27 + 1 < P := (by decide)
        omega
      rw [← e, ← ofN_one, val_add_nat hP]
    have ha0 : a 0 = (C.main r0 (FLD + 3)).val := by
      show ((stI 0).getD 2 0).val = _
      rw [hI0]; show (C.main r0 P2SP0).val = _; rw [hsp0]
    have haK : a P2_BITS = (C.main r0 P2REST).val := by
      show ((stI P2_BITS).getD 2 0).val = _
      rw [hIk]; rfl
    have hs1 : (C.main r0 (FLD + 3)).val < (C.main r0 CTR).val := by
      unfold rd at rd2; split at rd2
      · assumption
      · cases rd2
    have hle : ∀ i, i < P2_BITS → a i + i = a 0 := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih => intro hi; have := hstep i hi; have := ih (by omega); omega
    have hlt : ∀ i, i < P2_BITS → a i < (C.main r0 CTR).val := fun i hi => by
      have := hle i hi; rw [ha0] at this; omega
    have hHc : ∀ i, i < P2_BITS → H[a i]? = some (.cons (P2Jet.bitPtr (bI i)) (a (i + 1))) := fun i hi => by
      rw [hH _ (hlt i hi)]; exact (hcell i hi).1
    have hpop : Mach.popN H 496 (a 0) = some ((List.range' 0 496).map fun i => P2Jet.bitPtr (bI i), a 496) := by
      have := popN_chain H a (fun i => P2Jet.bitPtr (bI i)) 496 0 (fun j hj => by
        rw [Nat.zero_add]; exact hHc j hj)
      rw [Nat.zero_add] at this; exact this
    have hstk : H[(C.main r0 STK).val]? = some (.cons (C.main r0 (FLD + 2)).val (a 0)) := by
      rw [ha0]; exact rd_take rd1
    have hpop' : Mach.popN H 497 (C.main r0 STK).val =
        some ((C.main r0 (FLD + 2)).val :: (List.range' 0 496).map fun i => P2Jet.bitPtr (bI i),
          (C.main r0 P2REST).val) := by
      rw [show (497 : Nat) = 496 + 1 from rfl, popN_succ hstk, hpop, ← haK]
      rfl
    have hbits : P2Jet.ptrBits ((List.range' 0 496).map fun i => P2Jet.bitPtr (bI i)) = some bs := by
      rw [ptrBits_map bI, ← List.range_eq_range']
      rfl
    have hrun : P2Jet.stackRun H (C.main r0 STK).val = true := by
      unfold P2Jet.stackRun
      rw [hstk]
      exact consecFrom_of H a (fun i => P2Jet.bitPtr (bI i)) 495 0 (fun j hj => by
        rw [Nat.zero_add]
        exact ⟨hHc j (by unfold P2_BITS; omega), hstep j (by unfold P2_BITS; omega)⟩)
    unfold P2Jet.p2RowS
    simp only [rowOf]
    rw [show ((memOf Mm).take (C.main r0 CTR).val)[(C.main r0 HD).val]? = some (.atom (J + 1)) from rd_take rd0]
    have hslots' : P2Jet.slotsOK ((memOf Mm).take (C.main r0 CTR).val) = true := hslots
    have hrun' : P2Jet.stackRun ((memOf Mm).take (C.main r0 CTR).val) (C.main r0 STK).val = true := hrun
    have hpop'' : Mach.popN ((memOf Mm).take (C.main r0 CTR).val) 497 (C.main r0 STK).val = _ := hpop'
    simp only [true_and, hslots', hrun', and_self, if_true]
    rw [hpop'']
    simp only [hbits, if_pos hw, hob, n1, n2, n3]
    unfold P2Jet.topOf
    rw [if_neg (by decide), show P2_BITS - 1 = 495 from rfl, show P2_BITS = 496 from rfl,
      val_add_nat (by omega), val_add_nat (by omega)]
    rfl

end

end Circuit
