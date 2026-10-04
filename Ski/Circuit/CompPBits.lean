import Ski.Circuit.CompPBal

/-!
# The circuit with the Poseidon2 jet: the honest bit tables' messages

A P2IN or P2OUT row's messages (`pin_p2i`, `pout_p2o`, …): each call's
rows form a chain on `p2i` and `p2o` from the CPU's start to its end
(`accN_succ`, `lowL_succ`, `hiL_succ`), look up their levels on `p2idx`,
and at each element's last bit send its value on `p2v` or receive it on
`p2w`.
-/

namespace Circuit

open B Air Compose CompM Mach

-- ---------------------------------------------------------------------------
-- The chains' states
-- ---------------------------------------------------------------------------

theorem mod31_succ {l : Nat} (h : l % 31 ≠ 30) : (l + 1) % 31 = l % 31 + 1 ∧ l + 1 - (l + 1) % 31 = l - l % 31 := by
  have := Nat.mod_lt l (show 31 > 0 by decide)
  have e : (l + 1) % 31 = l % 31 + 1 := by
    rw [Nat.add_mod, show 1 % 31 = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  refine ⟨e, ?_⟩
  rw [e]; omega

theorem mod31_last {l : Nat} (h : l % 31 = 30) : (l + 1) % 31 = 0 := by
  rw [Nat.add_mod, h]

/-- **The element's sum moves on by the bit, and restarts after its 31st.** -/
theorem accN_succ (bs : List Bool) (l : Nat) :
    accN bs (l + 1) = if l % 31 = 30 then 0 else accN bs l + 2 ^ (l % 31) * (bs.getD l false).toNat := by
  unfold accN
  by_cases h : l % 31 = 30
  · rw [if_pos h, mod31_last h]; rfl
  · rw [if_neg h]
    obtain ⟨e1, e2⟩ := mod31_succ h
    rw [e2, e1, preB_succ, val_snoc, preB_length]
    have : l - l % 31 + l % 31 = l := Nat.sub_add_cancel (Nat.mod_le l 31)
    rw [this]; rfl

theorem lowL_succ (bs : List Bool) (l : Nat) :
    lowL bs (l + 1) = if l % 31 = 30 then false else (lowL bs l || (decide (l % 31 < 27) && bs.getD l false)) := by
  unfold lowL
  by_cases h : l % 31 = 30
  · rw [if_pos h, mod31_last h]; rfl
  · rw [if_neg h]
    obtain ⟨e1, e2⟩ := mod31_succ h
    rw [e2, e1, lowB_succ]
    have : l - l % 31 + l % 31 = l := Nat.sub_add_cancel (Nat.mod_le l 31)
    rw [this]; rfl

theorem hiL_succ (bs : List Bool) (l : Nat) :
    hiL bs (l + 1) = if l % 31 = 30 then true else (hiL bs l && (decide (l % 31 < 27) || bs.getD l false)) := by
  unfold hiL
  by_cases h : l % 31 = 30
  · rw [if_pos h, mod31_last h]; rfl
  · rw [if_neg h]
    obtain ⟨e1, e2⟩ := mod31_succ h
    rw [e2, e1, hiB_succ]
    have : l - l % 31 + l % 31 = l := Nat.sub_add_cancel (Nat.mod_le l 31)
    rw [this]; rfl

theorem accN_zero (bs : List Bool) : accN bs 0 = 0 := rfl
theorem lowL_zero (bs : List Bool) : lowL bs 0 = false := rfl
theorem hiL_zero (bs : List Bool) : hiL bs 0 = true := rfl
theorem accN_end (bs : List Bool) : accN bs P2_BITS = 0 := rfl
theorem lowL_end (bs : List Bool) : lowL bs P2_BITS = false := rfl
theorem hiL_end (bs : List Bool) : hiL bs P2_BITS = true := rfl

theorem bF_eq (b : Bool) : bF b = ofN b.toNat := by cases b <;> rfl

theorem bF_decide (P : Prop) [Decidable P] : bF (decide P) = ofN (if P then 1 else 0) := by
  by_cases h : P
  · rw [decide_eq_true h, if_pos h]; rfl
  · rw [decide_eq_false h, if_neg h]; rfl

-- ---------------------------------------------------------------------------
-- P2IN's messages
-- ---------------------------------------------------------------------------

theorem envOf_get (rw : List F) (n : Nat) : envOf rw (.main 0 n) = rw.getD n 0 := rfl

theorem pin_nowOnly : NowOnly p2inAir := by
  have h : p2inAir.inters.all (fun I => I.count.onlyAtoms nowAtom && I.fields.all (·.onlyAtoms nowAtom)) = true := rfl
  intro I hI
  have := List.all_eq_true.1 h I hI
  rw [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨this.1, this.2⟩

theorem pin_quiet : ZeroQuiet p2inAir := by
  intro I hI
  simp only [p2inAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl <;> decide

/-- What a P2IN row sends, bus by bus. -/
theorem pin_sends (c : Nat) (bs : List Bool) (l : Nat) (bus : String) (v : List F) :
    rowSendsV p2inAir bus v (pinRow c bs l) =
      (if "p2idx" = bus ∧ idxRow l = v then 1 else 0) +
      ((if "p2i" = bus ∧ [ofN c, ofN l, ofN (accN bs l)] = v then -1 else 0) +
      ((if "p2i" = bus ∧ [ofN c, ofN (l + 1), ofN (accN bs (l + 1))] = v then 1 else 0) +
      ((if "mem" = bus ∧ [ofN (l + 3), ofN (cellTag (if bs.getD l false then .K else .app 0 1)),
          0, ofN (cellFields (if bs.getD l false then Cell.K else .app 0 1)).2] = v then 1 else 0) +
      ((if "p2v" = bus ∧ [ofN c, ofN (l / 31), ofN (accN bs l + 2 ^ (l % 31) * (bs.getD l false).toNat)] = v
          then bF (decide (l % 31 = 30)) else 0) + 0)))) := by
  have g : ∀ n, envOf (pinRow c bs l) (.main 0 n) = (pinRow c bs l).getD n 0 := fun _ => rfl
  simp only [rowSendsV, p2inAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col,
    B.one, B.c, g]
  have idx : [(pinRow c bs l).getD 1 0, (pinRow c bs l).getD 5 0, (pinRow c bs l).getD 6 0,
      (pinRow c bs l).getD 7 0, (pinRow c bs l).getD 8 0, (pinRow c bs l).getD 9 0] = idxRow l := by
    show [ofN l, ofN (l / 31), ofN (2 ^ (l % 31)), bF (decide (l % 31 = 30)), bF (decide (l % 31 < 27)),
      bF (decide (l = P2_BITS - 1))] = idxRow l
    rw [bF_decide, bF_decide, bF_decide]; rfl
  have nxt : (pinRow c bs l).getD 11 0 = ofN (accN bs (l + 1)) := by
    rw [accN_succ]
    simp only [pinRow, List.getD_cons_succ, List.getD_cons_zero]
    split <;> rfl
  have m1 : (pinRow c bs l).getD 1 0 + ofN 3 = ofN (l + 3) := by
    simp only [pinRow, List.getD_cons_succ, List.getD_cons_zero]; rw [ofN_add]
  have m2 : ofN 3 - (pinRow c bs l).getD 2 0 * ofN 2 = ofN (cellTag (if bs.getD l false then .K else .app 0 1)) := by
    simp only [pinRow, List.getD_cons_succ, List.getD_cons_zero]; cases bs.getD l false <;> decide
  have m3 : ofN 1 - (pinRow c bs l).getD 2 0 = ofN (cellFields (if bs.getD l false then Cell.K else .app 0 1)).2 := by
    simp only [pinRow, List.getD_cons_succ, List.getD_cons_zero]; cases bs.getD l false <;> decide
  have a4 : (pinRow c bs l).getD 4 0 = 1 := rfl
  have e0 : (pinRow c bs l).getD 0 0 = ofN c := rfl
  have e3 : (pinRow c bs l).getD 3 0 = ofN (accN bs l) := rfl
  have e5 : (pinRow c bs l).getD 5 0 = ofN (l / 31) := rfl
  have e10 : (pinRow c bs l).getD 10 0 = ofN (accN bs l + 2 ^ (l % 31) * (bs.getD l false).toNat) := rfl
  have e12 : (pinRow c bs l).getD 12 0 = bF (decide (l % 31 = 30)) := rfl
  have e1 : (pinRow c bs l).getD 1 0 + ofN 1 = ofN (l + 1) := by
    show ofN l + 1 = _; exact ofN_succ l
  rw [idx, a4, e0, e3, nxt, m1, m2, m3, e5, e10, e12, e1]
  rfl


-- ---------------------------------------------------------------------------
-- P2OUT's messages
-- ---------------------------------------------------------------------------

theorem pout_nowOnly : NowOnly p2outAir := by
  have h : p2outAir.inters.all (fun I => I.count.onlyAtoms nowAtom && I.fields.all (·.onlyAtoms nowAtom)) = true := rfl
  intro I hI
  have := List.all_eq_true.1 h I hI
  rw [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨this.1, this.2⟩

theorem pout_quiet : ZeroQuiet p2outAir := by
  intro I hI
  simp only [p2outAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl <;> decide

/-- What a P2OUT row sends, bus by bus. -/
theorem pout_sends (c rest : Nat) (ob : List Bool) (l : Nat) (bus : String) (v : List F) :
    rowSendsV p2outAir bus v (poutRow c rest ob l) =
      (if "p2idx" = bus ∧ idxRow l = v then 1 else 0) +
      ((if "p2o" = bus ∧ [ofN c, ofN l, ofN rest, ofN (accN ob l), bF (lowL ob l), bF (hiL ob l)] = v
          then -1 else 0) +
      ((if "p2o" = bus ∧ [ofN c, ofN (l + 1), ofN rest, ofN (accN ob (l + 1)), bF (lowL ob (l + 1)),
          bF (hiL ob (l + 1))] = v then 1 else 0) +
      ((if "mem" = bus ∧ [ofN (c + (P2_BITS - 1) - l), ofN 5, ofN (P2Jet.bitPtr (ob.getD l false)),
          ofN (if l = P2_BITS - 1 then rest else c + (P2_BITS - 1) - l - 1)] = v then 1 else 0) +
      ((if "p2w" = bus ∧ [ofN c, ofN (l / 31), ofN (accN ob l + 2 ^ (l % 31) * (ob.getD l false).toNat)] = v
          then -bF (decide (l % 31 = 30)) else 0) + 0)))) := by
  have g : ∀ n, envOf (poutRow c rest ob l) (.main 0 n) = (poutRow c rest ob l).getD n 0 := fun _ => rfl
  simp only [rowSendsV, p2outAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col,
    B.one, B.c, g]
  have idx : [(poutRow c rest ob l).getD 1 0, (poutRow c rest ob l).getD 8 0, (poutRow c rest ob l).getD 9 0,
      (poutRow c rest ob l).getD 10 0, (poutRow c rest ob l).getD 11 0, (poutRow c rest ob l).getD 12 0] =
      idxRow l := by
    show [ofN l, ofN (l / 31), ofN (2 ^ (l % 31)), bF (decide (l % 31 = 30)), bF (decide (l % 31 < 27)),
      bF (decide (l = P2_BITS - 1))] = idxRow l
    rw [bF_decide, bF_decide, bF_decide]; rfl
  have n14 : (poutRow c rest ob l).getD 14 0 = ofN (accN ob (l + 1)) := by
    rw [accN_succ]
    show (if l % 31 = 30 then 0 else _) = _
    split <;> rfl
  have n17 : (poutRow c rest ob l).getD 17 0 = bF (lowL ob (l + 1)) := by
    rw [lowL_succ]
    show (if l % 31 = 30 then 0 else _) = _
    split <;> rfl
  have n18 : (poutRow c rest ob l).getD 18 0 = bF (hiL ob (l + 1)) := by
    rw [hiL_succ]
    show (if l % 31 = 30 then 1 else _) = _
    split <;> rfl
  have a7 : (poutRow c rest ob l).getD 7 0 = 1 := rfl
  have e1 : (poutRow c rest ob l).getD 1 0 + ofN 1 = ofN (l + 1) := by
    show ofN l + 1 = _; exact ofN_succ l
  have e0 : (poutRow c rest ob l).getD 0 0 = ofN c := rfl
  have e2 : (poutRow c rest ob l).getD 2 0 = ofN rest := rfl
  have e4 : (poutRow c rest ob l).getD 4 0 = ofN (accN ob l) := rfl
  have e5 : (poutRow c rest ob l).getD 5 0 = bF (lowL ob l) := rfl
  have e6 : (poutRow c rest ob l).getD 6 0 = bF (hiL ob l) := rfl
  have e8 : (poutRow c rest ob l).getD 8 0 = ofN (l / 31) := rfl
  have e13 : (poutRow c rest ob l).getD 13 0 = ofN (accN ob l + 2 ^ (l % 31) * (ob.getD l false).toNat) := rfl
  have e19 : (poutRow c rest ob l).getD 19 0 = bF (decide (l % 31 = 30)) := rfl
  have e20 : (poutRow c rest ob l).getD 20 0 = ofN (c + (P2_BITS - 1) - l) := rfl
  have e21 : (poutRow c rest ob l).getD 21 0 = ofN (if l = P2_BITS - 1 then rest else c + (P2_BITS - 1) - l - 1) := rfl
  have e22 : (poutRow c rest ob l).getD 22 0 = ofN (P2Jet.bitPtr (ob.getD l false)) := rfl
  rw [idx, a7, e0, e2, e4, e5, e6, n14, n17, n18, e1, e8, e13, e19, e20, e21, e22]
  rfl


-- ---------------------------------------------------------------------------
-- A call's sums
-- ---------------------------------------------------------------------------

theorem block31 (f : Nat → F) (base : Nat) (hf : ∀ t, t < 31 → t ≠ 30 → f (base + t) = 0) :
    (List.range 31).foldr (fun t acc => f (base + t) + acc) 0 = f (base + 30) :=
  fold_single (fun t => f (base + t)) 31 30 (by decide) (fun t ht hne => hf t ht hne)

theorem foldr_range_last (g : Nat → F) (m : Nat) :
    (List.range (m + 1)).foldr (fun e acc => g e + acc) 0 = (List.range m).foldr (fun e acc => g e + acc) 0 + g m := by
  rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, add_zero', fold_acc]

/-- **The 496 levels, by element**: a sum over the levels, nonzero only at
    each element's last, is a sum over the elements. -/
theorem sum_elems (f g : Nat → F) (hf : ∀ l, f l = if l % 31 = 30 then g (l / 31) else 0) : ∀ m,
    (List.range (31 * m)).foldr (fun l acc => f l + acc) 0 = (List.range m).foldr (fun e acc => g e + acc) 0
  | 0 => rfl
  | m + 1 => by
    have e1 : 31 * (m + 1) = 31 * m + 31 := Nat.mul_succ 31 m
    have hb := block31 f (31 * m) (fun t ht hne => by
      rw [hf, if_neg]
      rw [show (31 * m + t) % 31 = t by omega]; exact hne)
    have hg : f (31 * m + 30) = g m := by
      rw [hf, if_pos (by omega), show (31 * m + 30) / 31 = m by omega]
    rw [foldr_range_last g m, e1, List.range_add, List.foldr_append, fold_acc, List.foldr_map, sum_elems f g hf m]
    exact congrArg _ (hb.trans hg)

/-- An element's last level holds its value. -/
theorem acc_last (bs : List Bool) (e : Nat) :
    accN bs (31 * e + 30) + 2 ^ ((31 * e + 30) % 31) * (bs.getD (31 * e + 30) false).toNat =
      BitArith.val (Poseidon2SKI.chunk bs e) := by
  have h1 : (31 * e + 30) % 31 = 30 := by omega
  have h2 : 31 * e + 30 - (31 * e + 30) % 31 = 31 * e := by omega
  have hc : Poseidon2SKI.chunk bs e = preB (bitF bs) (31 * e) (30 + 1) := by
    unfold Poseidon2SKI.chunk preB bitF; rfl
  unfold accN
  rw [h2, h1, hc, preB_succ (bitF bs) (31 * e) 30, val_snoc, preB_length]
  rfl

theorem ite_and_one (b : String) (P : Prop) [Decidable P] (x : F) :
    (if b = b ∧ P then x else 0) = if P then x else 0 := by
  by_cases h : P
  · rw [if_pos ⟨rfl, h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h]

theorem ite_ne {b b' : String} (hb : b ≠ b') {P : Prop} [Decidable P] {x : F} :
    (if b = b' ∧ P then x else 0) = 0 := if_neg (fun h => hb h.1)

/-- **A call's P2IN rows telescope on `p2i`**, from `(c, 0, 0)` to
    `(c, 496, 0)`. -/
theorem pin_p2i_call (c : Nat) (bs : List Bool) (v : List F) :
    (((List.range P2_BITS).map (pinRow c bs)).map (rowSendsV p2inAir "p2i" v)).foldr (· + ·) 0 =
      ind ([ofN c, ofN P2_BITS, 0] = v) - ind ([ofN c, 0, 0] = v) := by
  rw [foldr_map_range]
  let T : Nat → List F := fun l => [ofN c, ofN l, ofN (accN bs l)]
  rw [foldr_range_congr P2_BITS (g := fun l => ind (T (l + 1) = v) - ind (T l = v)) (fun l _ => by
    rw [pin_sends, ite_ne (b := "p2idx") (b' := "p2i") (by decide), ite_ne (b := "mem") (b' := "p2i") (by decide),
      ite_ne (b := "p2v") (b' := "p2i") (by decide), ite_and_one, ite_and_one]
    simp only [zero_add', add_zero']
    rw [ite_neg_one _ 1 rfl, ite_one _ 1 rfl, sub_eq_add_neg', add_comm'])]
  rw [telescopeF T v P2_BITS]
  rfl

/-- A call's P2IN rows look up each level once. -/
theorem pin_idx_call (c : Nat) (bs : List Bool) (v : List F) :
    (((List.range P2_BITS).map (pinRow c bs)).map (rowSendsV p2inAir "p2idx" v)).foldr (· + ·) 0 =
      (List.range P2_BITS).foldr (fun l acc => ind (idxRow l = v) + acc) 0 := by
  rw [foldr_map_range]
  refine foldr_range_congr P2_BITS (fun l _ => ?_)
  rw [pin_sends, ite_and_one, ite_ne (b := "p2i") (b' := "p2idx") (by decide),
    ite_ne (b := "p2i") (b' := "p2idx") (by decide), ite_ne (b := "mem") (b' := "p2idx") (by decide),
    ite_ne (b := "p2v") (b' := "p2idx") (by decide), ite_one _ 1 rfl]
  simp only [add_zero']

/-- **A call's P2IN rows send each element's value on `p2v`.** -/
theorem pin_p2v_call (c : Nat) (bs : List Bool) (v : List F) :
    (((List.range P2_BITS).map (pinRow c bs)).map (rowSendsV p2inAir "p2v" v)).foldr (· + ·) 0 =
      (List.range 16).foldr (fun e acc =>
        ind ([ofN c, ofN e, ofN (BitArith.val (Poseidon2SKI.chunk bs e))] = v) + acc) 0 := by
  rw [foldr_map_range]
  refine sum_elems _ _ (fun l => ?_) 16
  rw [pin_sends, ite_ne (b := "p2idx") (b' := "p2v") (by decide), ite_ne (b := "p2i") (b' := "p2v") (by decide),
    ite_ne (b := "p2i") (b' := "p2v") (by decide), ite_ne (b := "mem") (b' := "p2v") (by decide), ite_and_one]
  simp only [zero_add', add_zero']
  by_cases hl : l % 31 = 30
  · rw [if_pos hl, show bF (decide (l % 31 = 30)) = 1 by rw [decide_eq_true hl]; rfl, ite_one _ 1 rfl]
    have e : l = 31 * (l / 31) + 30 := by omega
    rw [e, acc_last, show (31 * (l / 31) + 30) / 31 = l / 31 by omega]
  · rw [if_neg hl, show bF (decide (l % 31 = 30)) = 0 by rw [decide_eq_false hl]; rfl]
    split <;> rfl


/-- **A call's P2OUT rows telescope on `p2o`**, from `(c, 0, rest, 0, 0, 1)`
    to `(c, 496, rest, 0, 0, 1)`. -/
theorem pout_p2o_call (c rest : Nat) (ob : List Bool) (v : List F) :
    (((List.range P2_BITS).map (poutRow c rest ob)).map (rowSendsV p2outAir "p2o" v)).foldr (· + ·) 0 =
      ind ([ofN c, ofN P2_BITS, ofN rest, 0, 0, 1] = v) - ind ([ofN c, 0, ofN rest, 0, 0, 1] = v) := by
  rw [foldr_map_range]
  let T : Nat → List F := fun l => [ofN c, ofN l, ofN rest, ofN (accN ob l), bF (lowL ob l), bF (hiL ob l)]
  rw [foldr_range_congr P2_BITS (g := fun l => ind (T (l + 1) = v) - ind (T l = v)) (fun l _ => by
    rw [pout_sends, ite_ne (b := "p2idx") (b' := "p2o") (by decide), ite_ne (b := "mem") (b' := "p2o") (by decide),
      ite_ne (b := "p2w") (b' := "p2o") (by decide), ite_and_one, ite_and_one]
    simp only [zero_add', add_zero']
    rw [ite_neg_one _ 1 rfl, ite_one _ 1 rfl, sub_eq_add_neg', add_comm'])]
  rw [telescopeF T v P2_BITS]
  rfl

/-- A call's P2OUT rows look up each level once. -/
theorem pout_idx_call (c rest : Nat) (ob : List Bool) (v : List F) :
    (((List.range P2_BITS).map (poutRow c rest ob)).map (rowSendsV p2outAir "p2idx" v)).foldr (· + ·) 0 =
      (List.range P2_BITS).foldr (fun l acc => ind (idxRow l = v) + acc) 0 := by
  rw [foldr_map_range]
  refine foldr_range_congr P2_BITS (fun l _ => ?_)
  rw [pout_sends, ite_and_one, ite_ne (b := "p2o") (b' := "p2idx") (by decide),
    ite_ne (b := "p2o") (b' := "p2idx") (by decide), ite_ne (b := "mem") (b' := "p2idx") (by decide),
    ite_ne (b := "p2w") (b' := "p2idx") (by decide), ite_one _ 1 rfl]
  simp only [add_zero']

/-- **A call's P2OUT rows receive each element's value on `p2w`.** -/
theorem pout_p2w_call (c rest : Nat) (ob : List Bool) (v : List F) :
    (((List.range P2_BITS).map (poutRow c rest ob)).map (rowSendsV p2outAir "p2w" v)).foldr (· + ·) 0 =
      (List.range 16).foldr (fun e acc =>
        -ind ([ofN c, ofN e, ofN (BitArith.val (Poseidon2SKI.chunk ob e))] = v) + acc) 0 := by
  rw [foldr_map_range]
  refine sum_elems _ _ (fun l => ?_) 16
  rw [pout_sends, ite_ne (b := "p2idx") (b' := "p2w") (by decide), ite_ne (b := "p2o") (b' := "p2w") (by decide),
    ite_ne (b := "p2o") (b' := "p2w") (by decide), ite_ne (b := "mem") (b' := "p2w") (by decide), ite_and_one]
  simp only [zero_add', add_zero']
  by_cases hl : l % 31 = 30
  · rw [if_pos hl, show bF (decide (l % 31 = 30)) = 1 by rw [decide_eq_true hl]; rfl, ite_neg_one _ 1 rfl]
    have e : l = 31 * (l / 31) + 30 := by omega
    rw [e, acc_last, show (31 * (l / 31) + 30) / 31 = l / 31 by omega]
  · rw [if_neg hl, show bF (decide (l % 31 = 30)) = 0 by rw [decide_eq_false hl]; rfl]
    split
    · exact neg_zero_eq
    · rfl

end Circuit
