import Ski.Circuit.CompDRead

/-!
# The circuit with the `dec` jet: its four buses

The CPU and DEC talk on four buses, none with a provider: `decn` (a noun
the subject needs read at a pointer, in a role), `decb` (a bit list's
chain), `decd` (the verdict), `decx` (the result, to the CPU).  Every
message's count is `0`, `1` or `-1` (`CompDOK.signed`), so on each bus a
tuple sent is received and one received is sent (`bus_match`); here each
side is named row by row (`NeedSent`, `NeedRecv`, `ChainSent`,
`ChainRecv`, `VerdSent`, `VerdRecv`, `ResSent`, `ResRecv`), and
`CompDOK.need_recv` … `res_sent` are the four buses' matches.
-/

namespace Circuit

open B Air

/-- The `dec` jet's buses. -/
def DBus (B : String) : Prop := B = "decn" ∨ B = "decb" ∨ B = "decd" ∨ B = "decx"

/-- The CPU's messages on the jet's buses. -/
def cpuBusI : List Inter :=
  [⟨"decn", 1, sDec, [col CTR, fld 2, c 0]⟩, ⟨"decx", 1, .neg sDec, [col CTR, col DROOT, col DCTR]⟩]

theorem neg_bit {x : F} (hx : x = 0 ∨ x = 1) : -x = 0 ∨ -x = -1 := by
  rcases hx with rfl | rfl <;> decide

theorem sum_bit_of_kind {D : Table} {q dk : Nat} (hk : DKind D q dk) :
    D.main q Dec.KCELL + D.main q Dec.KATOM = 0 ∨ D.main q Dec.KCELL + D.main q Dec.KATOM = 1 := by
  rw [hk.2.1, hk.2.2.1]
  by_cases h1 : dk = 1
  · rw [if_pos h1, if_neg (by omega)]; decide
  · rw [if_neg h1]
    by_cases h2 : dk = 2
    · rw [if_pos h2]; decide
    · rw [if_neg h2]; decide

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

theorem CompDOK.dbit {q : Nat} (hq : q < D.h) :
    ∀ X ∈ [Dec.KCELL, Dec.KATOM, Dec.KCONS, Dec.KNIL, Dec.CSEND, Dec.DONE0, Dec.DONE1, Dec.SUB, Dec.HC, Dec.ASUB],
      D.main q X = 0 ∨ D.main q X = 1 := by
  have hf := decRowF_of h.dec hq
  intro X hX
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hf.kcell
  · exact hf.katom
  · exact hf.kcons
  · exact hf.knil
  · rw [hf.csend]; exact bit_mul hf.kcons (bit_one_sub hf.last)
  · rw [hf.done0]; exact bit_mul (bit_mul hf.kcons hf.last) (bit_one_sub hf.mode)
  · rw [hf.done1]; exact bit_mul hf.knil (bit_one_sub hf.mode)
  · exact hf.wbit _ (by simp [Dec.wcols])
  · exact hf.wbit _ (by simp [Dec.wcols])
  · exact hf.wbit _ (by simp [Dec.wcols])

/-- **The jet's buses are signed**: every message's count is `0`, `1` or `-1`. -/
theorem CompDOK.signed {B : String} (hB : DBus B) :
    ∀ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, SignedOn B p := by
  have nb : ∀ s : String, (s = "mem" ∨ s = "segs" ∨ s = "blind_a" ∨ s = "blind_b" ∨ s = "blind_c") → s ≠ B := by
    intro s hs e
    rw [← e] at hB
    rcases hB with h1 | h1 | h1 | h1 <;> rcases hs with h2 | h2 | h2 | h2 | h2 <;> rw [h2] at h1 <;>
      exact absurd h1 (by decide)
  intro p hp
  simp only [compDTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨fun I hI _ => ?_, fun r hr I hI hbus => ?_⟩
    · have : cpuIntersD.all (fun I => decide (1 ≤ I.weight)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.1 this I hI)
    obtain ⟨k, hk⟩ := kind_ofD h.cpu hr
    obtain ⟨_, _, _, _, _, _, hDec, _⟩ := kind_factsD hr hk
    have hd : sDec.eval (C.env r) = 0 ∨ sDec.eval (C.env r) = 1 := by
      rw [hDec]
      by_cases e : k = 12
      · rw [if_pos e]; exact .inr rfl
      · rw [if_neg e]; exact .inl rfl
    change I ∈ cpuIntersD at hI
    rw [cpuIntersD_eq] at hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd hbus (nb _ (by decide))
      | (rcases hd with e | e
         · exact .inl e
         · exact .inr (.inl e))
      | (show (E.neg sDec).eval _ = 0 ∨ (E.neg sDec).eval _ = 1 ∨ (E.neg sDec).eval _ = -1
         simp only [E.eval]
         rcases neg_bit hd with e | e
         · exact .inl e
         · exact .inr (.inr e))
      | exact absurd hbus (nb _ (by decide))
  · refine ⟨fun I hI hbus => ?_, fun r _ I hI hbus => ?_⟩ <;>
    · simp only [memAirC, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl <;> exact absurd hbus (nb _ (by decide))
  · refine ⟨fun I hI hbus => ?_, fun r _ I hI hbus => ?_⟩ <;>
    · simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hI
      subst hI; exact absurd hbus (nb _ (by decide))
  · refine ⟨fun I hI hbus => ?_, fun r _ I hI hbus => ?_⟩ <;>
    · simp only [witAir, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with rfl | rfl <;> exact absurd hbus (nb _ (by decide))
  · refine ⟨fun I hI hbus => ?_, fun r _ I hI hbus => ?_⟩ <;>
    · simp only [segsAir, List.mem_cons, List.not_mem_nil, or_false] at hI
      subst hI; exact absurd hbus (nb _ (by decide))
  · refine ⟨fun I hI _ => ?_, fun r hr I hI hbus => ?_⟩
    · have : decAirB.inters.all (fun I => decide (1 ≤ I.weight)) = true := by decide
      exact of_decide_eq_true (List.all_eq_true.1 this I hI)
    rw [show decAirB = withBlocks Dec.decAir [("blind_c", false)] from rfl, withBlocks_inters] at hI
    rcases List.mem_append.1 hI with hI | hI
    · rcases dec_bus_cases hI with ⟨hm, _⟩ | hI
      · rw [hm] at hbus; exact absurd hbus (nb _ (by decide))
      · have hbit := h.dbit hr
        have cv := col_eval hr
        obtain ⟨dk, hk⟩ := dkind_of (decRowF_of h.dec hr)
        have hsum := sum_bit_of_kind hk
        simp only [Dec.busI, List.mem_cons, List.not_mem_nil, or_false] at hI
        have col1 : ∀ X, (D.main r X = 0 ∨ D.main r X = 1) →
            (col X).eval (D.env r) = 0 ∨ (col X).eval (D.env r) = 1 ∨ (col X).eval (D.env r) = -1 := by
          intro X hX; rw [cv]; rcases hX with e | e
          · exact .inl e
          · exact .inr (.inl e)
        have neg1 : ∀ X, (D.main r X = 0 ∨ D.main r X = 1) →
            (E.neg (col X)).eval (D.env r) = 0 ∨ (E.neg (col X)).eval (D.env r) = 1 ∨
              (E.neg (col X)).eval (D.env r) = -1 := by
          intro X hX; simp only [E.eval]; rw [cv]; rcases neg_bit hX with e | e
          · exact .inl e
          · exact .inr (.inr e)
        rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · show (E.neg (E.add (col Dec.KCELL) (col Dec.KATOM))).eval _ = 0 ∨ _ = 1 ∨ _ = -1
          simp only [E.eval, cv]; rcases neg_bit hsum with e | e
          · exact .inl e
          · exact .inr (.inr e)
        · exact col1 _ (hbit _ (by simp))
        · exact col1 _ (hbit _ (by simp))
        · exact col1 _ (hbit _ (by simp))
        · exact neg1 _ (hbit _ (by simp))
        · exact col1 _ (hbit _ (by simp))
        · exact neg1 _ (hbit _ (by simp))
        · exact neg1 _ (hbit _ (by simp))
        · exact col1 _ (hbit _ (by simp))
        · exact col1 _ (hbit _ (by simp))
        · exact col1 _ (hbit _ (by simp))
        · exact col1 _ (hbit _ (by simp))
        · exact col1 _ (hbit _ (by simp))
    · obtain ⟨b, hbm, hbus', _⟩ := withBlocks_block_bus hI
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbm
      subst hbm
      rw [hbus'] at hbus; exact absurd hbus (nb _ (by decide))

/-- **A message on a jet bus is the CPU's or DEC's.** -/
theorem CompDOK.hit_split {B : String} (hB : DBus B) {v : List F} {s : F}
    (hit : ∃ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, ∃ r, r < p.2.h ∧
      ∃ I ∈ p.1.inters, I.bus = B ∧ I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = s) :
    (∃ r, r < C.h ∧ ∃ I ∈ cpuBusI, I.bus = B ∧ I.fields.map (fun e => e.eval (C.env r)) = v ∧
      I.count.eval (C.env r) = s) ∨
    (∃ q, q < D.h ∧ ∃ I ∈ Dec.busI, I.bus = B ∧ I.fields.map (fun e => e.eval (D.env q)) = v ∧
      I.count.eval (D.env q) = s) := by
  have nb : ∀ s : String, (s = "mem" ∨ s = "segs" ∨ s = "blind_a" ∨ s = "blind_b" ∨ s = "blind_c") → s ≠ B := by
    intro s hs e
    rw [← e] at hB
    rcases hB with h1 | h1 | h1 | h1 <;> rcases hs with h2 | h2 | h2 | h2 | h2 <;> rw [h2] at h1 <;>
      exact absurd h1 (by decide)
  obtain ⟨p, hp, r, hr, I, hI, hbus, hf, hc⟩ := hit
  simp only [compDTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · left
    refine ⟨r, hr, I, ?_, hbus, hf, hc⟩
    change I ∈ cpuIntersD at hI
    rw [cpuIntersD_eq] at hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd hbus (nb _ (by decide))
      | exact absurd hbus (nb _ (by decide))
      | simp [cpuBusI]
  · simp only [memAirC, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl <;> exact absurd hbus (nb _ (by decide))
  · simp only [progAirC, List.mem_cons, List.not_mem_nil, or_false] at hI
    subst hI; exact absurd hbus (nb _ (by decide))
  · simp only [witAir, witInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl <;> exact absurd hbus (nb _ (by decide))
  · simp only [segsAir, List.mem_cons, List.not_mem_nil, or_false] at hI
    subst hI; exact absurd hbus (nb _ (by decide))
  · right
    refine ⟨r, hr, I, ?_, hbus, hf, hc⟩
    rw [show decAirB = withBlocks Dec.decAir [("blind_c", false)] from rfl, withBlocks_inters] at hI
    rcases List.mem_append.1 hI with hI | hI
    · rcases dec_bus_cases hI with ⟨hm, _⟩ | hI
      · rw [hm] at hbus; exact absurd hbus (nb _ (by decide))
      · exact hI
    · obtain ⟨b, hbm, hbus', _⟩ := withBlocks_block_bus hI
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbm
      subst hbm
      rw [hbus'] at hbus; exact absurd hbus (nb _ (by decide))

end

end Circuit
