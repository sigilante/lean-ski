import Ski.ComposedO
import Ski.P2Jet
import Ski.Predicate

set_option linter.unusedSimpArgs false

open Term

/-!
# Composed statements with the Poseidon2 jet

A statement whose verifiers use the Poseidon2 jet is a list of open terms,
the jet the variable `J`, an atom in the heap (`Ski/ComposedO.lean`).

**`AcceptsCP`** is `AcceptsCJ` with one more kind of row: the jet's
(`P2Jet.p2Row`), which takes `k` and the comb's root `β` and reads the
bits from their slots.  **`composedP_sound_of`**: a table it accepts from
the composed machine of the open statement, while the root reads back as
the comb of the slots' bits, proves the closed statement with the jet
closed to any implementation of the comb contract: every verifier, applied
to the bits and the region's witness, evaluates to `K`.
**`composedP_sound`** discharges the comb's hypotheses for statements
over 496 bits (`comb_heap`), with the jet closed to
`Poseidon2SKI.Pcomb`; the root is public (`combRoot_public`).

What remains to join a proof to these theorems: that the circuit's accepted
tables give such a table (`Ski/Circuit/CompPAir.lean` holds the circuit as
data, without that proof yet).
-/

namespace CompM

open Mach Stmt Compose Wit BExpr Poseidon2SKI

-- ---------------------------------------------------------------------------
-- The AIR with the Poseidon2 jet
-- ---------------------------------------------------------------------------

/-- A row: a step, an instantiation at a listed root, a halted row repeated
    (`Air.NormRow`), or the Poseidon2 jet at the atom `J`. -/
def NormRowP (M : List Cell) (jroots : List (Nat × Nat)) (jets : List Air.Jet) (J root : Nat)
    (r r' : Air.Row) : Prop :=
  Air.NormRow M jroots jets r r' ∨ P2Jet.p2Row M J root r = some r'

/-- **The AIR with jets, segments and the Poseidon2 jet accepts**: as
    `AcceptsCJ`, each row within a segment a `NormRowP`. -/
structure AcceptsCP (M : List Cell) (m0 : Mach) (jroots : List (Nat × Nat)) (jets : List Air.Jet)
    (J root : Nat) (roots : List Nat) (nilA n : Nat) (e : Nat → Nat) (row : Nat → Air.Row) : Prop where
  npos : 0 < n
  heap0 : M.take (row 0).ctr = m0.heap
  hd0 : (row 0).hd = roots.getD 0 0
  stk0 : (row 0).stk = nilA
  ctr0 : (row 0).ctr = m0.heap.length
  emono : ∀ j, j + 1 < n → e j < e (j + 1)
  restart : ∀ j, j + 1 < n → row (e j + 1) = ⟨roots.getD (j + 1) 0, nilA, (row (e j)).ctr⟩
  trans : ∀ i, i < e (n - 1) → (∀ j, j + 1 < n → i ≠ e j) → NormRowP M jroots jets J root (row i) (row (i + 1))
  ends : ∀ j, j < n → Air.rd M (row (e j)).ctr (row (e j)).hd = some .K ∧
    Air.rd M (row (e j)).ctr (row (e j)).stk = some .nil

theorem owstep_cstep {α β : Type} {cc : DataJet.CContract α β} {j : Nat} {t u : OTerm} (h : OWStep t u) :
    DataJet.CStep cc j t u := by
  induction h with
  | S f g x => exact .S f g x
  | K x y => exact .K x y
  | I x => exact .I x
  | left x _ ih => exact .left x ih
  | right f _ ih => exact .right f ih

theorem CSteps.trans {α β : Type} {cc : DataJet.CContract α β} {j : Nat} {t u v : OTerm}
    (h₁ : DataJet.CSteps cc j t u) (h₂ : DataJet.CSteps cc j u v) : DataJet.CSteps cc j t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem owsteps_csteps {α β : Type} {cc : DataJet.CContract α β} {j : Nat} {t u : OTerm} (h : OWSteps t u) :
    DataJet.CSteps cc j t u := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (owstep_cstep h) ih

theorem bitsAt_append {H : List Cell} {as : List Nat} {bs : List Bool} (h : P2Jet.bitsAt H as = some bs)
    (cs : List Cell) : P2Jet.bitsAt (H ++ cs) as = some bs := by
  induction as generalizing bs with
  | nil => exact h
  | cons a as ih =>
    unfold P2Jet.bitsAt at h ⊢
    cases hb : P2Jet.boolAt H a with
    | none => rw [hb] at h; cases h
    | some b =>
      cases hq : P2Jet.bitsAt H as with
      | none => rw [hb, hq] at h; cases h
      | some bs' =>
        rw [hb, hq] at h
        rw [ih hq]
        have e : P2Jet.boolAt (H ++ cs) a = some b := by
          rcases P2Jet.boolAt_cases hb with ⟨rfl, ha⟩ | ⟨rfl, f, x, ha, hf, hx⟩
          · unfold P2Jet.boolAt
            rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ha).1, ha]
          · unfold P2Jet.boolAt
            rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 ha).1, ha]
            dsimp only
            rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hf).1, hf,
              List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1, hx]
        rw [e]
        exact h

theorem bitsAt_det {H : List Cell} {as : List Nat} {bs bs' : List Bool} (h : P2Jet.bitsAt H as = some bs)
    (h' : P2Jet.bitsAt H as = some bs') : bs = bs' := by
  rw [h] at h'; cases h'; rfl

/-- **The comb's reading survives growth of the heap**: from a heap where
    the slots read as `bs₀` and the root as their comb. -/
theorem combAt_ext {H : List Cell} {root : Nat} {bs₀ : List Bool} (hb : P2Jet.bitsAt H P2Jet.slotAddrs = some bs₀)
    (ho : otermAt H (H.length + 1) root = some (combT bs₀).toO) (cs : List Cell) :
    P2Jet.CombAt (H ++ cs) root := by
  intro bs hbs
  rw [bitsAt_det hbs (bitsAt_append hb cs)]
  exact otermAt_grow ho (by rw [List.length_append]; omega)

theorem combAt_take {M : List Cell} {c0 c root : Nat} {bs₀ : List Bool}
    (hb : P2Jet.bitsAt (M.take c0) P2Jet.slotAddrs = some bs₀)
    (ho : otermAt (M.take c0) ((M.take c0).length + 1) root = some (combT bs₀).toO) (hc : c0 ≤ c) :
    P2Jet.CombAt (M.take c) root := by
  have e : M.take c = M.take c0 ++ (M.take c).drop c0 := by
    have := List.take_append_drop c0 (M.take c)
    rw [List.take_take, Nat.min_eq_left hc] at this
    exact this.symm
  rw [e]
  exact combAt_ext hb ho _

/-- **A row, read back**: the counter moves forward within the table, and
    the state's open term reduces by the jet's reduction. -/
theorem normRowP_spec {M : List Cell} {jroots : List (Nat × Nat)} {jets : List Air.Jet} {J root c0 : Nat}
    (hroots : Air.RootsOK (M.take c0) jroots jets) {r r' : Air.Row} (hc0 : c0 ≤ r.ctr)
    (hc : r.ctr ≤ M.length) (hcomb : P2Jet.CombAt (M.take r.ctr) root)
    (h : NormRowP M jroots jets J root r r') {t : OTerm}
    (hdec : odecode (Air.st M r) = some t) :
    r.ctr ≤ r'.ctr ∧ r'.ctr ≤ M.length ∧
      ∃ u, odecode (Air.st M r') = some u ∧ DataJet.CSteps poseidon2Comb J t u := by
  rcases h with hn | hp
  · obtain ⟨h1, h2, hJ, _⟩ := Air.normRow_spec hroots hc0 hc hn
    obtain ⟨u, hu, hw⟩ := ojsteps_owsteps hdec hJ
    exact ⟨h1, h2, u, hu, owsteps_csteps hw⟩
  · obtain ⟨h2, u, hu, hs⟩ := P2Jet.p2Row_cstep hp hc hcomb hdec
    exact ⟨(P2Jet.p2Row_ctr_len hp hc).1, h2, u, hu, .step hs (.refl _)⟩

section

variable {M : List Cell} {m0 : Mach} {jroots : List (Nat × Nat)} {jets : List Air.Jet} {J root : Nat}
  {roots : List Nat} {nilA n : Nat} {e : Nat → Nat} {row : Nat → Air.Row}

/-- **Within a segment, the run reads back as the jet's reduction.** -/
theorem AcceptsCP.within (h : AcceptsCP M m0 jroots jets J root roots nilA n e row)
    (hroots : Air.RootsOK m0.heap jroots jets) {j : Nat} (hj : j < n)
    (hc : (row (segStart e j)).ctr ≤ M.length) (hc0 : (row 0).ctr ≤ (row (segStart e j)).ctr)
    (hcombs : ∀ c, (row 0).ctr ≤ c → P2Jet.CombAt (M.take c) root)
    {t0 : OTerm} (hdec : odecode (Air.st M (row (segStart e j))) = some t0) :
    ∀ b, segStart e j ≤ b → b ≤ e j →
      (row b).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row b).ctr ∧
      ∃ t, odecode (Air.st M (row b)) = some t ∧ DataJet.CSteps poseidon2Comb J t0 t := by
  have hr0 : Air.RootsOK (M.take (row 0).ctr) jroots jets := by rw [h.heap0]; exact hroots
  have hen : e j ≤ e (n - 1) := emono_le h.emono (by omega) (by omega)
  intro b hb1 hb2
  induction b with
  | zero =>
    have hs0 : segStart e j = 0 := by omega
    rw [hs0] at hdec ⊢
    exact ⟨by rw [← hs0]; exact hc, Nat.le_refl _, t0, hdec, .refl _⟩
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hb1 with hl | hl
    · obtain ⟨hcb, hsb, t, ht, hst⟩ := ih (by omega) (by omega)
      have hn := h.trans b (by omega) (not_end h.emono hj (by omega) (by omega))
      obtain ⟨h1, h2, u, hu, hsu⟩ := normRowP_spec hr0 (Nat.le_trans hc0 hsb) hcb
        (hcombs _ (Nat.le_trans hc0 hsb)) hn ht
      exact ⟨h2, Nat.le_trans hsb h1, u, hu, CSteps.trans hst hsu⟩
    · rw [← hl]
      exact ⟨hc, Nat.le_refl _, t0, hdec, .refl _⟩

/-- The counters of a segment's rows, without reading back. -/
theorem AcceptsCP.within_ctr (h : AcceptsCP M m0 jroots jets J root roots nilA n e row)
    (hroots : Air.RootsOK m0.heap jroots jets) {j : Nat} (hj : j < n)
    (hc : (row (segStart e j)).ctr ≤ M.length) (hc0 : (row 0).ctr ≤ (row (segStart e j)).ctr) :
    ∀ b, segStart e j ≤ b → b ≤ e j → (row b).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row b).ctr := by
  have hr0 : Air.RootsOK (M.take (row 0).ctr) jroots jets := by rw [h.heap0]; exact hroots
  have hen : e j ≤ e (n - 1) := emono_le h.emono (by omega) (by omega)
  intro b hb1 hb2
  induction b with
  | zero =>
    have hs0 : segStart e j = 0 := by omega
    rw [hs0]
    exact ⟨by rw [← hs0]; exact hc, Nat.le_refl _⟩
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hb1 with hl | hl
    · obtain ⟨hcb, hsb⟩ := ih (by omega) (by omega)
      have hn := h.trans b (by omega) (not_end h.emono hj (by omega) (by omega))
      rcases hn with hn | hp
      · obtain ⟨h1, h2, _, _⟩ := Air.normRow_spec hr0 (Nat.le_trans hc0 hsb) hcb hn
        exact ⟨h2, Nat.le_trans hsb h1⟩
      · obtain ⟨a1, a2⟩ := P2Jet.p2Row_ctr_len hp hcb
        exact ⟨a2, Nat.le_trans hsb a1⟩
    · rw [← hl]
      exact ⟨hc, Nat.le_refl _⟩

/-- **Every segment's counters**: its first row's lies between the
    machine's and the table's length, and its last row's within the table. -/
theorem AcceptsCP.runs (h : AcceptsCP M m0 jroots jets J root roots nilA n e row)
    (hroots : Air.RootsOK m0.heap jroots jets) :
    ∀ j, j < n → (row (segStart e j)).ctr ≤ M.length ∧
      m0.heap.length ≤ (row (segStart e j)).ctr ∧ (row (e j)).ctr ≤ M.length ∧
      (row (segStart e j)).ctr ≤ (row (e j)).ctr := by
  have hc0 : (row 0).ctr ≤ M.length := by
    have := congrArg List.length h.heap0
    rw [List.length_take, ← h.ctr0] at this
    omega
  have seg : ∀ j, j < n → (row (segStart e j)).ctr ≤ M.length →
      (row 0).ctr ≤ (row (segStart e j)).ctr →
      (row (e j)).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row (e j)).ctr := fun j hj hc hc0' =>
    h.within_ctr hroots hj hc hc0' (e j) (segStart_le h.emono j hj) (Nat.le_refl _)
  intro j
  induction j with
  | zero =>
    intro hn
    obtain ⟨a, b⟩ := seg 0 hn hc0 (Nat.le_refl _)
    exact ⟨hc0, by rw [show segStart e 0 = 0 from rfl, h.ctr0]; exact Nat.le_refl _, a, b⟩
  | succ j ih =>
    intro hn
    obtain ⟨_, hm, he, hse⟩ := ih (by omega)
    have hr := h.restart j hn
    have hc : (row (segStart e (j + 1))).ctr = (row (e j)).ctr := by
      show (row (e j + 1)).ctr = _
      rw [hr]
    obtain ⟨a, b⟩ := seg (j + 1) hn (by rw [hc]; exact he) (by rw [hc, h.ctr0]; omega)
    exact ⟨by rw [hc]; exact he, by rw [hc]; omega, a, b⟩

end

/-- The jet's variable closed to `Pcomb`, any other to `K`. -/
def jetEnv (J : Nat) : Nat → Term := fun i => if i = J then Pcomb else K

/-- **A table the AIR with the Poseidon2 jet accepts from the composed
    machine of an open statement proves the closed statement**, the jet's
    variable closed to any implementation of the contract: with a
    well-formed region, the template jets licensed over the filled heap,
    and the comb at `root` reading back as the bits at the slots, its bits
    and the region's witness make every verifier evaluate to `K`. -/
theorem composedP_sound_of {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Vs : List OTerm} {J root : Nat}
    (σ : Nat → Term) (himpl : DataJet.CImplements poseidon2Comb (σ J))
    {bs₀ : List Bool} (hb0 : P2Jet.bitsAt (cMachineO ρ shp region Vs).heap P2Jet.slotAddrs = some bs₀)
    (ho0 : otermAt (cMachineO ρ shp region Vs).heap ((cMachineO ρ shp region Vs).heap.length + 1) root =
      some (combT bs₀).toO)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {jroots : List (Nat × Nat)} {jets : List Air.Jet}
    (hroots : Air.RootsOK (cMachineO ρ shp region Vs).heap jroots jets)
    {M : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (h : AcceptsCP M (cMachineO ρ shp region Vs) jroots jets J root (cHeapO ρ shp region Vs).2
      (cHeapO ρ shp region Vs).1.length Vs.length e row) :
    ∃ w, cWitness ρ (BT.nleaves shp) region = some w ∧
      EvalRel (Vs.map (·.close σ), SameShape shp) (fillB shp ρ 0) w := by
  let N := BT.nleaves shp
  obtain ⟨w, hw⟩ := witnessOf_some (slots_wf ρ N hr) (by simp [slotHeap_length]; omega)
  refine ⟨w, hw, fillB_shape shp ρ 0, fun P hP => ?_⟩
  obtain ⟨V, hV, rfl⟩ := List.mem_map.1 hP
  obtain ⟨j, hj, hVj⟩ := List.getElem_of_mem hV
  have hj' : Vs[j]? = some V := by rw [List.getElem?_eq_getElem hj, hVj]
  obtain ⟨_, hdec⟩ := cMachineO_decode (Vs := Vs) hw
  have hroot := hdec j V hj'
  obtain ⟨hc, hm, _, _⟩ := h.runs hroots j hj
  let m0 := cMachineO ρ shp region Vs
  have hregs : (row (segStart e j)).hd = (cHeapO ρ shp region Vs).2.getD j 0 ∧
      (row (segStart e j)).stk = (cHeapO ρ shp region Vs).1.length := by
    cases j with
    | zero => exact ⟨h.hd0, h.stk0⟩
    | succ j =>
      have := h.restart j hj
      show (row (e j + 1)).hd = _ ∧ (row (e j + 1)).stk = _
      rw [this]
      exact ⟨rfl, rfl⟩
  have hm0 : m0.heap = M.take (row 0).ctr := h.heap0.symm
  have hc0 : (row 0).ctr = m0.heap.length := h.ctr0
  have hle : (row 0).ctr ≤ (row (segStart e j)).ctr := by rw [hc0]; exact hm
  have hlen : (Air.st M (row (segStart e j))).heap.length = (row (segStart e j)).ctr := by
    simp [Air.st, Air.take_length hc]
  have hstart : odecode (Air.st M (row (segStart e j))) =
      some (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) := by
    have e1 : V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO = appL (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) [] := rfl
    rw [e1]
    apply odecode_of
    · show otermAt (M.take (row (segStart e j)).ctr) (_ + 1) (row (segStart e j)).hd = _
      rw [hregs.1]
      rw [hm0] at hroot
      refine Air.otermAt_take hle ?_ hroot
      rw [← hm0, hlen]
      show m0.heap.length + 1 ≤ _
      omega
    · show ostackAt (M.take (row (segStart e j)).ctr) (_ + 1) (row (segStart e j)).stk = _
      rw [hregs.2]
      have hn : (M.take (row (segStart e j)).ctr)[(cHeapO ρ shp region Vs).1.length]? = some .nil := by
        have h1 : m0.heap[(cHeapO ρ shp region Vs).1.length]? = some .nil := by simp [m0, cMachineO]
        rw [hm0, List.getElem?_take] at h1
        rw [List.getElem?_take]
        split at h1
        · rw [if_pos (by omega)]; exact h1
        · cases h1
      unfold ostackAt
      rw [hn]
  have hcombs : ∀ c, (row 0).ctr ≤ c → P2Jet.CombAt (M.take c) root := fun c hcc => by
    have hb' : P2Jet.bitsAt (M.take (row 0).ctr) P2Jet.slotAddrs = some bs₀ := by rw [← hm0]; exact hb0
    have ho' : otermAt (M.take (row 0).ctr) ((M.take (row 0).ctr).length + 1) root = some (combT bs₀).toO := by
      rw [← hm0]; exact ho0
    exact combAt_take hb' ho' hcc
  obtain ⟨_, _, v, hv, hsteps⟩ := h.within hroots hj hc (by rw [hc0]; exact hm) hcombs hstart (e j)
    (segStart_le h.emono j hj) (Nat.le_refl _)
  have hK : v = .K := by
    refine odecode_K hv ?_ ?_
    · rw [← (h.ends j hj).1, Air.rd_eq]; rfl
    · rw [← (h.ends j hj).2, Air.rd_eq]; rfl
  rw [hK] at hsteps
  have hw' : WSteps (V.close σ ⬝ (fillB shp ρ 0).enc ⬝ w) K := by
    have := hsteps.close σ himpl
    change WSteps (V.close σ ⬝ (fillB shp ρ 0).enc.toO.close σ ⬝ w.toO.close σ) K at this
    rw [close_toO, close_toO] at this
    exact this
  obtain ⟨v', hev, hv'⟩ := eval_of_wsteps hw' .K
  obtain ⟨_, hhd⟩ := small_lemma_whnf hev.2 hv'
  rw [chead_K hhd.symm] at hev
  exact hev

-- ---------------------------------------------------------------------------
-- Statements over a comb of 496 bits
-- ---------------------------------------------------------------------------

/-- `pbuild` reads the heap only through its length. -/
theorem pbuild_len (bound : Nat) : ∀ (t : OTerm) (h h' : List Cell), h.length = h'.length →
    (pbuild bound h t).2 = (pbuild bound h' t).2 ∧ (pbuild bound h t).1.length = (pbuild bound h' t).1.length
  | .S, h, h', e => ⟨e, by simp [pbuild, alloc, e]⟩
  | .K, h, h', e => ⟨e, by simp [pbuild, alloc, e]⟩
  | .I, h, h', e => ⟨e, by simp [pbuild, alloc, e]⟩
  | .var x, h, h', e => by
    unfold pbuild
    by_cases hx : x < bound
    · rw [if_pos hx, if_pos hx]; exact ⟨rfl, e⟩
    · rw [if_neg hx, if_neg hx]; exact ⟨e, by simp [alloc, e]⟩
  | .app f a, h, h', e => by
    have ⟨ef2, ef1⟩ := pbuild_len bound f h h' e
    have ⟨ea2, ea1⟩ := pbuild_len bound a _ _ ef1
    show (alloc _ (.app _ _)).2 = (alloc _ (.app _ _)).2 ∧ (alloc _ _).1.length = (alloc _ _).1.length
    simp only [alloc, List.length_append, ea1, ef2, ea2]
    exact ⟨trivial, trivial⟩

/-- **The root is public**: it depends on neither the bits nor the region's
    cells, only on the region's length. -/
theorem combRoot_public (ρ ρ' : Nat → Bool) (shp : BT) {region region' : List Cell}
    (e : region.length = region'.length) : combRoot ρ shp region = combRoot ρ' shp region' :=
  (pbuild_len _ _ _ _ (by simp [slotHeap_length, e])).1

/-- A filled comb is the comb of its bits. -/
theorem fill_comb (ρ : Nat → Bool) : ∀ (n off : Nat),
    (fillB (combBT (n + 1)) ρ off).enc = combT ((List.range' off (n + 1)).map ρ)
  | 0, _ => rfl
  | n + 1, off => by
    show pairT (boolT (ρ off)) (fillB (combBT (n + 1)) ρ (off + 1)).enc = _
    rw [fill_comb ρ n (off + 1)]
    rfl

theorem range'_shift (ρ : Nat → Bool) : ∀ (s n : Nat),
    (List.range' (s + 3) n).map (fun a => ρ (a - 3)) = (List.range' s n).map ρ
  | _, 0 => rfl
  | s, n + 1 => by
    show ρ (s + 3 - 3) :: (List.range' (s + 3 + 1) n).map _ = ρ s :: (List.range' (s + 1) n).map ρ
    rw [Nat.add_sub_cancel, show s + 3 + 1 = (s + 1) + 3 by omega, range'_shift ρ (s + 1) n]

/-- The heap's slots read back as the bits. -/
theorem slots_bits {H : List Cell} {ρ : Nat → Bool} {N : Nat} (hpre : ∀ i, i < N + 3 → H[i]? = (slotHeap ρ N)[i]?) :
    ∀ (s n : Nat), s + n ≤ N →
      P2Jet.bitsAt H (List.range' (s + 3) n) = some ((List.range' (s + 3) n).map (fun a => ρ (a - 3)))
  | _, 0, _ => rfl
  | s, n + 1, hn => by
    have ih := slots_bits hpre (s + 1) n (Nat.le_trans (Nat.le_of_eq (Nat.succ_add s n)) hn)
    rw [show s + 1 + 3 = s + 3 + 1 from rfl] at ih
    have hs : s < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self s) (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right s n)) hn)
    have hc : H[s + 3]? = some (if ρ s then .K else .app 0 1) := by
      rw [hpre (s + 3) (Nat.add_lt_add_right hs 3)]; exact slotHeap_get ρ N s hs
    have h0 : H[0]? = some .K := by rw [hpre 0 (Nat.zero_lt_succ _)]; rfl
    have h1 : H[1]? = some .I := by rw [hpre 1 (Nat.succ_lt_succ (Nat.zero_lt_succ _))]; rfl
    have hb : P2Jet.boolAt H (s + 3) = some (ρ s) := by
      unfold P2Jet.boolAt
      rw [hc]
      cases ρ s
      · show (match H[0]?, H[1]? with | some .K, some .I => some false | _, _ => none) = some false
        rw [h0, h1]
      · rfl
    show (match P2Jet.boolAt H (s + 3), P2Jet.bitsAt H (List.range' (s + 3 + 1) n) with
      | some b, some bs => some (b :: bs) | _, _ => none) = some (ρ (s + 3 - 3) :: _)
    rw [hb, ih, Nat.add_sub_cancel]

/-- Adding statements only appends. -/
theorem addStmtsO_ext (pe wr : Nat) : ∀ (Ps : List OTerm) (h : List Cell),
    ∃ cs, (addStmtsO pe wr h Ps).1 = h ++ cs
  | [], h => ⟨[], by simp [addStmtsO]⟩
  | P :: Ps, h => by
    obtain ⟨c1, e1, _, _⟩ := obuild_spec P h
    obtain ⟨cs, e⟩ := addStmtsO_ext pe wr Ps
      ((obuild h P).1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr])
    exact ⟨c1 ++ [Cell.app (obuild h P).2 pe, Cell.app (obuild h P).1.length wr] ++ cs, by
      show (addStmtsO pe wr _ Ps).1 = _
      rw [e, e1]; simp⟩

/-- The composed heap of a comb statement: its slots read back as the bits,
    and the root of their encoding as their comb. -/
theorem comb_heap (ρ : Nat → Bool) (region : List Cell) (Vs : List OTerm) :
    P2Jet.bitsAt (cMachineO ρ (combBT 496) region Vs).heap P2Jet.slotAddrs = some ((List.range' 0 496).map ρ) ∧
      otermAt (cMachineO ρ (combBT 496) region Vs).heap ((cMachineO ρ (combBT 496) region Vs).heap.length + 1)
        (combRoot ρ (combBT 496) region) = some (combT ((List.range' 0 496).map ρ)).toO := by
  have hN : BT.nleaves (combBT 496) = 496 := combBT_nleaves 496 (by decide)
  unfold combRoot
  let h0 := slotHeap ρ (BT.nleaves (combBT 496)) ++ region
  have henv : ∀ x, Occ x (encO (combBT 496) 0) → x < BT.nleaves (combBT 496) + 2 →
      otermAt h0 (h0.length + 1) (slotPtr x) = some (slotVal ρ x) := by
    intro x _ hx
    exact otermAt_grow (cs := region) (k := h0.length + 1) (slot_reads ρ _ x hx)
      (by simp [h0, slotHeap_length])
  obtain ⟨cs1, e1, t1⟩ := pbuild_spec ρ (BT.nleaves (combBT 496) + 2) (encO (combBT 496) 0) h0 henv
  rw [encO_fill ρ _ (combBT 496) 0 (by rw [Nat.zero_add]; exact Nat.le_refl _)] at t1
  obtain ⟨cs, e⟩ := addStmtsO_ext (pbuild (BT.nleaves (combBT 496) + 2) h0 (encO (combBT 496) 0)).2
    (h0.length - 1) Vs (pbuild (BT.nleaves (combBT 496) + 2) h0 (encO (combBT 496) 0)).1
  have hheap : (cMachineO ρ (combBT 496) region Vs).heap =
      (pbuild (BT.nleaves (combBT 496) + 2) h0 (encO (combBT 496) 0)).1 ++ (cs ++ [.nil]) := by
    show (addStmtsO _ _ _ Vs).1 ++ [.nil] = _
    rw [e, List.append_assoc]
  constructor
  · have hpre : ∀ i, i < 496 + 3 → (cMachineO ρ (combBT 496) region Vs).heap[i]? = (slotHeap ρ 496)[i]? := by
      intro i hi
      rw [hheap, e1, List.append_assoc, List.getElem?_append_left (by simp [h0, slotHeap_length, hN]; omega)]
      show (slotHeap ρ (BT.nleaves (combBT 496)) ++ region)[i]? = _
      rw [hN, List.getElem?_append_left (by rw [slotHeap_length]; exact hi)]
    have hb := slots_bits hpre 0 496 (Nat.le_refl _)
    rw [range'_shift ρ 0 496] at hb
    exact hb
  · rw [hheap]
    have hf : (fillB (combBT 496) ρ 0).enc = combT ((List.range' 0 496).map ρ) := fill_comb ρ 495 0
    have hg := otermAt_grow (cs := cs ++ [Cell.nil])
      (k := (pbuild (BT.nleaves (combBT 496) + 2) h0 (encO (combBT 496) 0)).1.length + (cs ++ [Cell.nil]).length + 1)
      t1 (Nat.succ_le_succ (Nat.le_add_right _ _))
    rw [hf] at hg
    rw [List.length_append]
    exact hg

/-- **Soundness for comb statements.**  An accepted run of a statement over
    496 bits laid out as a comb, with the jet reading the comb's root, makes
    each verifier, with `J` closed to `Poseidon2SKI.Pcomb`, evaluate on the
    bits. -/
theorem composedP_sound {ρ : Nat → Bool} {region : List Cell} {Vs : List OTerm} {J : Nat}
    (hr : ∀ i c, region[i]? = some c → cellOK (496 + 3 + i) c = true)
    {jroots : List (Nat × Nat)} {jets : List Air.Jet}
    (hroots : Air.RootsOK (cMachineO ρ (combBT 496) region Vs).heap jroots jets)
    {M : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (h : AcceptsCP M (cMachineO ρ (combBT 496) region Vs) jroots jets J (combRoot ρ (combBT 496) region)
      (cHeapO ρ (combBT 496) region Vs).2 (cHeapO ρ (combBT 496) region Vs).1.length Vs.length e row) :
    ∃ w, cWitness ρ 496 region = some w ∧
      EvalRel (Vs.map (·.close (jetEnv J)), SameShape (combBT 496)) (fillB (combBT 496) ρ 0) w := by
  obtain ⟨hb0, ho0⟩ := comb_heap ρ region Vs
  exact composedP_sound_of (jetEnv J)
    (by show DataJet.CImplements poseidon2Comb (if J = J then Pcomb else K)
        rw [if_pos rfl]; exact Pcomb_implements) hb0 ho0
    (by rw [combBT_nleaves 496 (by decide)]; exact hr) hroots h |>.imp fun _ hw =>
      ⟨by rw [← combBT_nleaves 496 (by decide)]; exact hw.1, hw.2⟩

end CompM
