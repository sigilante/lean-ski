import Ski.Circuit.CompDTraceWr
import Ski.Circuit.CompPSat
import Ski.Circuit.CompPComplete

/-!
# Completeness of the circuit with the `dec` jet

**The honest DEC table** (`DRun.decTable`): `decair.rs`'s `dec_trace`, the
rows of every jet call of the run (`DRun.decRows`, `DecT.callRows`) padded
with zero rows.  **`decProvides_exists`**: for an honest run whose jet
calls' rows fit the DEC height, it provides the run's jet calls
(`DecProvides`): it satisfies DEC (`DecT.row_sat`), is clear past its
columns, its reads and writes are memory cells (`DecT.row_mem`,
`DecT.call_writes`), and on every other bus it sends the negation of the
honest CPU (`DecT.call_sends`).

**`decpre_complete_log`**: completeness of the circuit for `decpre p`.
-/

namespace Circuit

open B Air Compose CompM Mach Stmt Wit ComposedDText

namespace DRun

/-- **The honest DEC rows** of the run's first `K` rows: one call's rows
    per jet row. -/
def decRows (R : DRun) (K : Nat) : List DecT.DR :=
  (List.range K).flatMap fun r =>
    if R.jetAt r then DecT.callRows R.A (R.rowQ r).ctr (DecT.subj R.A (R.rowQ r)) else []

/-- **The honest DEC table** of `H` rows. -/
def decTable (R : DRun) (K H : Nat) : Table := ⟨H, ofRows ((R.decRows K).map (DecT.vec R.A)), fun _ _ => 0⟩

end DRun

namespace DecT

set_option maxRecDepth 100000 in
theorem decCons_cur : Dec.decAir.cons.all (fun e => e.onlyAtoms curAtom) = true := by decide

theorem envOf_nil : envOf [] = fun _ => (0 : F) := by
  funext a
  cases a with
  | main o c => cases o <;> rfl
  | _ => rfl

theorem dec_zero_sat : ∀ c ∈ Dec.decAir.cons, c.eval (envOf []) = 0 := by
  intro c hc
  rw [envOf_nil]
  exact of_decide_eq_true (List.all_eq_true.1 decCons_zero c hc)

theorem dec_quiet : ZeroQuiet Dec.decAir := by
  intro I hI
  rw [envOf_nil]
  exact of_decide_eq_true (List.all_eq_true.1 decInters_zero I hI)

theorem vec_sat {A : List Cell} {d : DR} (hok : RowOK A d) : ∀ c ∈ Dec.decAir.cons, c.eval (envOf (vec A d)) = 0 := by
  intro c hc
  rw [E.eval_congr (vec_env A d) c (List.all_eq_true.1 decCons_now c hc)]
  exact row_sat hok c hc

theorem vec_length (A : List Cell) (d : DR) : (vec A d).length = Dec.WIDTH := by
  unfold vec; rw [List.length_map, List.length_range]

theorem foldr_neg_ite (P : Nat → Bool) (f : Nat → F) : ∀ l : List Nat,
    l.foldr (fun r acc => (if P r then -f r else 0) + acc) 0 = -(l.foldr (fun r acc => (if P r then f r else 0) + acc) 0)
  | [] => neg_zero_eq.symm
  | r :: l => by
    simp only [List.foldr_cons]
    rw [foldr_neg_ite P f l]
    cases P r <;> simp only [Bool.false_eq_true, if_false, if_true] <;> grind

theorem bits_key {A : List Cell} {key : Nat} {m : Bool} : ∀ (n p lvl : Nat) (bw : Bool) (wc : Nat),
    ∀ d ∈ bitsRows A key m n p lvl bw wc, d.key = key
  | 0, _, _, _, _ => by intro d hd; cases hd
  | n + 1, p, lvl, bw, wc => by
    intro d hd
    unfold bitsRows at hd
    split at hd
    · rw [List.mem_singleton] at hd; subst hd; rfl
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · rfl
        · split at hd
          · cases hd
          · exact bits_key n _ _ _ _ d hd
      · cases hd

theorem noun_key {A : List Cell} {key : Nat} : ∀ (n p ro : Nat), ∀ d ∈ nounRows A key n p ro, d.key = key
  | 0, _, _ => by intro d hd; cases hd
  | n + 1, p, ro => by
    intro d hd
    unfold nounRows at hd
    split at hd
    · rcases List.mem_cons.1 hd with rfl | hd
      · rfl
      · exact bits_key _ _ _ _ _ d hd
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · rfl
        · rcases List.mem_append.1 hd with hd | hd
          · exact noun_key n _ 2 d hd
          · exact noun_key n _ 2 d hd
      · cases hd

theorem callRows_key {A : List Cell} {key p : Nat} : ∀ d ∈ callRows A key p, d.key = key := by
  intro d hd
  unfold callRows at hd
  split at hd
  · rcases List.mem_cons.1 hd with rfl | hd
    · rfl
    · exact bits_key _ _ _ _ _ d hd
  · split at hd
    · rcases List.mem_cons.1 hd with rfl | hd
      · rfl
      · rcases List.mem_append.1 hd with hd | hd
        · exact noun_key _ _ _ d hd
        · exact noun_key _ _ _ d hd
    · cases hd

theorem S_flatMap {A : List Cell} {B : String} {v : List F} (f : Nat → List DR) : ∀ l : List Nat,
    S A B v (l.flatMap f) = l.foldr (fun r acc => S A B v (f r) + acc) 0
  | [] => rfl
  | r :: l => by rw [List.flatMap_cons, S_append, S_flatMap f l]; rfl

end DecT

namespace DRun

variable {R : DRun} {m0 : Mach} {nilA : Nat} (hA : R.Honest m0 nilA)
include hA

/-- A jet row's call: its step, its counter in memory. -/
theorem jet_call {r : Nat} (hj : R.jetAt r = true) :
    DecJet.decRow R.A R.J (R.rowQ r) = some (R.rowQ (r + 1)) ∧ (R.rowQ r).ctr ≤ R.A.length := by
  obtain ⟨_, hi, hd⟩ := jetAt_spec hj
  refine ⟨hd, ?_⟩
  rw [rowQ_of_le (by omega)]
  exact ctr_le hA r (by omega)

/-- **Every honest DEC row** is well formed, reads and writes memory cells. -/
theorem decRows_ok (hAl : R.A.length < 2 ^ 24) {K : Nat} :
    ∀ d ∈ R.decRows K, DecT.OK R.A d ∧ DecT.WritesOK R.A d ∧ d.key ≤ R.A.length := by
  intro d hd
  obtain ⟨r, _, hd⟩ := List.mem_flatMap.1 hd
  cases hj : R.jetAt r with
  | false => rw [hj] at hd; cases hd
  | true =>
    rw [hj, if_pos rfl] at hd
    obtain ⟨hstep, hc⟩ := jet_call hA hj
    obtain ⟨p, rest, s, csk, ask, sks, cells, root, _, _, hpop, hrd, hfit, _, _, _⟩ := DecJet.decRow_unfold hstep
    have hok := DecT.callRows_ok (key := (R.rowQ r).ctr) (by omega) hrd hfit
    rw [DecT.popN_subj hpop] at hd
    refine ⟨hok d hd, ?_, by rw [DecT.callRows_key d hd]; exact hc⟩
    have hw := DecT.call_writes hstep
    rw [DecT.popN_subj hpop] at hw
    exact hw d hd

set_option maxRecDepth 10000 in
/-- **The honest DEC table provides the run's jet calls**, when their rows
    fit its height. -/
theorem decProvides_of (hAl : R.A.length < 2 ^ 24) {K H : Nat} (hH : 0 < H) (hHD : (R.decRows K).length ≤ H) :
    DecProvides R K (R.decTable K H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sat_ofRows hH DecT.decCons_cur (fun rw hrw c hc => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hrw
      exact DecT.vec_sat (decRows_ok hA hAl d hd).1.1 c hc) DecT.dec_zero_sat
  · intro r _ c hc
    show ofRows _ r c = 0
    exact ofRows_wide (w := Dec.WIDTH) (fun x hx => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.1 hx
      rw [DecT.vec_length]; exact Nat.le_refl _) r hc
  · exact honest_ofRows DecT.dec_nowOnly DecT.dec_quiet (fun rw hrw I hI hb hc => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hrw
      obtain ⟨h1, h2, h3⟩ := decRows_ok hA hAl d hd
      exact DecT.row_mem h1 h2 h3 I hI hb hc)
  · intro B hBm _ v
    rw [show R.decTable K H = ⟨H, ofRows ((R.decRows K).map (DecT.vec R.A)), fun _ _ => 0⟩ from rfl,
      sends_rows DecT.dec_nowOnly DecT.dec_quiet (by rw [List.length_map]; exact hHD), List.map_map]
    have e : ((R.decRows K).map (rowSendsV Dec.decAir B v ∘ DecT.vec R.A)).foldr (· + ·) 0 =
        DecT.S R.A B v (R.decRows K) := by
      unfold DecT.S
      rw [List.map_congr_left (f := rowSendsV Dec.decAir B v ∘ DecT.vec R.A) (g := fun d => DecT.sendsT R.A d B v)
        (fun d _ => DecT.vec_sends R.A d B v)]
    rw [e, decRows, DecT.S_flatMap, jetSendsD, ← DecT.foldr_neg_ite]
    refine foldr_range_congr K (fun r _ => ?_)
    cases hj : R.jetAt r with
    | false => rfl
    | true =>
      simp only [if_true]
      exact DecT.call_sends (jet_call hA hj).1 hBm v

end DRun

/-- **The DEC table exists**: an honest run whose jet calls' rows fit
    `2^LD` rows has a DEC table that provides its jet calls. -/
theorem decProvides_exists {R LD : Nat} {Rn : DRun} {m0 : Mach} {nilA : Nat}
    (hA : Rn.Honest m0 nilA) (hAl : Rn.A.length < 2 ^ 24) (hHD : (Rn.decRows (2 ^ R)).length ≤ 2 ^ LD) :
    ∃ D : Table, D.h = 2 ^ LD ∧ DecProvides Rn (2 ^ R) D :=
  ⟨Rn.decTable (2 ^ R) (2 ^ LD), rfl, DRun.decProvides_of hA hAl (Nat.two_pow_pos _) hHD⟩

/-- **Completeness of the circuit for `decpre p`**: an honest run of the
    decrement statement at the verifier's heights, its jet calls' DEC rows
    within `2^LD`, gives tables that AIRs with the normal forms of
    `compDAirs p W` accept, with Plonky3's selectors. -/
theorem decpre_complete_log {p R Lm LD : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLD : LD ≤ 20)
    {W : Nat} {Rs : List AirD} (hs : sameAirsB Rs (compDAirs p W) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpD + 3 + i) c = true)
    (hNW : BT.nleaves shpD + W ≤ 2 ^ 8)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : DRun.Honest ⟨A, JD, (cHeapO ρ shpD region (VsD p)).2, e, (VsD p).length, row⟩
      (cMachineO ρ shpD region (VsD p)) (cHeapO ρ shpD region (VsD p)).1.length)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e 0 < 2 ^ R)
    (hHD : (DRun.decRows ⟨A, JD, (cHeapO ρ shpD region (VsD p)).2, e, (VsD p).length, row⟩ (2 ^ R)).length ≤ 2 ^ LD) :
    ∃ C Mm Pg Wt Sg D, AcceptedP Rs [C, Mm, Pg, Wt, Sg, D] ∧
      Pg = progTableC (blankMO shpD W (VsD p)).heap (BT.nleaves shpD) W ∧
      Wt = witTable A (BT.nleaves shpD) W ∧
      C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ D.h = 2 ^ LD ∧ memOf Mm = A ∧ ∀ i, i ≤ e 0 → rowOf C i = row i := by
  have hAl : A.length < 2 ^ 24 := by
    rw [hlen]; exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hLm) (by decide)
  obtain ⟨D, hD, hdec⟩ := decProvides_exists (R := R) hA hAl hHD
  obtain ⟨C, Mm, Pg, Wt, Sg, hacc, hC, hPg, hWt, hCh, hMh, hmem, hrow⟩ :=
    compDG_complete_dec hR hLm hLD hs hrl hr hNW hA hfit hlen hK hD hdec
  exact ⟨C, Mm, Pg, Wt, Sg, D, hacc, hPg, hWt, hCh, hMh, hD, hmem, hrow⟩

end Circuit
