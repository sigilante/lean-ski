import Ski.ComposedO
import Ski.DecJet

/-!
# Composed statements with the `dec` jet: the run

A statement whose verifiers use the `dec` jet is a list of open terms, the
jet the variable `J`.  **`AcceptsCD`** is `AcceptsCP` (`Ski/ComposedP.lean`)
with the `dec` jet's row in place of Poseidon2's: each row within a segment
steps, halts, or, once its state decodes, takes `DecJet.decRow`'s step
(`NormRowD`).  The decode is the read-back the circuit's need tree uses for
its fuel; every row of a run from a decoded start decodes.

**`HSteps`**: what the run reads back as, head reduction with the jet's
rule at the head, `J ⬝ encNn s ⬝ R ⟶ encO (decSpec s) ⬝ R`, for subjects
`s` the memory holds (`InMem`).  The machine contracts only the head, so
the run is head reduction, which is deterministic up to the jet's row;
this is what lets a verifier's meaning be read off its run
(`Ski/DecPreSound.lean`).

**`composedD_sound_of`**: a table `AcceptsCD` accepts from the composed
machine of the open statement makes every verifier, on the bits and the
region's witness, head-reduce with the jet to `K`.
-/

open Term

namespace CompM

open Mach Stmt Compose Wit DecJet

/-- A row: a step or a halted row repeated (`Air.NormRow`, no template
    jets), or, once its state decodes, the `dec` jet's row. -/
def NormRowD (M : List Cell) (J : Nat) (r r' : Air.Row) : Prop :=
  Air.NormRow M [] [] r r' ∨ (∀ t, odecode (Air.st M r) = some t → decRow M J r = some r')

/-- A subject the memory holds. -/
def InMem (M : List Cell) (s : Dom) : Prop := ∃ root, otermAt M M.length root = some (encNn s.1).toO

/-- **Head reduction with the `dec` jet**, the jet's subjects in `A`. -/
inductive HStep (A : Dom → Prop) (J : Nat) : OTerm → OTerm → Prop
  | head {t u : OTerm} (h : OStep t u) : HStep A J t u
  | jet (s : Dom) (hs : A s) (R : List OTerm) :
      HStep A J (appL (.var J) ((encNn s.1).toO :: R)) (appL (DecJet.encO (decSpec s.1)).toO R)

inductive HSteps (A : Dom → Prop) (J : Nat) : OTerm → OTerm → Prop
  | refl (t : OTerm) : HSteps A J t t
  | step {t t' u : OTerm} (h : HStep A J t t') (hs : HSteps A J t' u) : HSteps A J t u

theorem HSteps.trans {A : Dom → Prop} {J : Nat} {t u v : OTerm} (h₁ : HSteps A J t u) (h₂ : HSteps A J u v) :
    HSteps A J t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-- **A jet row, read back**, with its subject in the memory. -/
theorem decRow_hstep {M : List Cell} {J : Nat} {r r' : Air.Row} (h : decRow M J r = some r')
    (hc : r.ctr ≤ M.length) {t : OTerm} (hdec : odecode (Air.st M r) = some t) :
    r'.ctr ≤ M.length ∧ ∃ u, odecode (Air.st M r') = some u ∧ HSteps (InMem M) J t u := by
  obtain ⟨p, rest, s, csk, ask, sks, cells, root, hhd, hs, hpop, hrd, hfit, hout, hw, rfl⟩ := decRow_unfold h
  generalize hH : M.take r.ctr = H at hhd hs hpop hrd hout
  have hHl : H.length = r.ctr := by rw [← hH, List.length_take]; omega
  have htake := Air.take_of_wrs hw
  rw [hH] at htake
  have hlen' : (M.take (r.ctr + cells.length)).length = r.ctr + cells.length := by
    rw [htake, List.length_append, hHl]
  have hcl : r.ctr + cells.length ≤ M.length := by rw [List.length_take] at hlen'; omega
  have hcpos : 1 ≤ cells.length := by
    unfold outCells at hout
    split at hout <;> (try cases hout) <;> simp [errCells, cellCells]
  refine ⟨hcl, ?_⟩
  obtain ⟨hdt, args, h1, h2, rfl⟩ := odecode_eq hdec
  replace h1 : otermAt H (H.length + 1) r.hd = some hdt := by rw [← hH]; exact h1
  replace h2 : ostackAt H (H.length + 1) r.stk = some args := by rw [← hH]; exact h2
  have hj : hdt = .var J := by
    unfold otermAt at h1; rw [hhd] at h1; cases h1; rfl
  obtain ⟨Ns, R, G, hG, hargs, hNl, hpl, hok, hR⟩ := popN_ospec 1 hpop h2
  match Ns, hNl, hok with
  | [N], _, ⟨hN, _⟩ =>
    have hNe := readSubj_ot hrd hN
    subst hNe
    rw [← hHl] at hout
    have hroot := out_ot hs hrd hout hN
    let sd : Dom := ⟨s, readSubj_wf hrd, hfit⟩
    have hmem : InMem M sd := by
      refine ⟨p, ?_⟩
      have := Air.otermAt_take (M := M) (c := r.ctr) (c' := M.length) (f := H.length + 1) (f' := M.length) hc
        (by omega) (by rw [hH]; exact hN)
      rw [List.take_length] at this
      exact this
    refine ⟨_, ?_, .step (by rw [hargs, hj]; exact HStep.jet sd hmem R) (.refl _)⟩
    show odecode ⟨M.take (r.ctr + cells.length), root, rest⟩ = _
    rw [htake]
    apply odecode_of hroot
    exact ostackAt_grow hR (by rw [List.length_append]; omega)

/-- **A row, read back**: the counter moves forward within the table, and
    the state's open term head-reduces with the jet. -/
theorem normRowD_spec {M : List Cell} {J : Nat} {r r' : Air.Row} (hc : r.ctr ≤ M.length)
    (h : NormRowD M J r r') {t : OTerm} (hdec : odecode (Air.st M r) = some t) :
    r.ctr ≤ r'.ctr ∧ r'.ctr ≤ M.length ∧ ∃ u, odecode (Air.st M r') = some u ∧ HSteps (InMem M) J t u := by
  rcases h with hn | hj
  · have hroots : Air.RootsOK (M.take r.ctr) [] [] := fun _ _ h => nomatch h
    obtain ⟨h1, h2, _, _⟩ := Air.normRow_spec hroots (Nat.le_refl _) hc hn
    refine ⟨h1, h2, ?_⟩
    rcases hn with hs | ⟨_, _, hm, _, _⟩ | ⟨_, rfl⟩
    · obtain ⟨hm, _⟩ := Air.stepRow_mstep hc hs
      rcases omstep_some hdec hm with hd | ⟨u, hu, hd⟩
      · exact ⟨t, hd, .refl t⟩
      · exact ⟨u, hd, .step (.head hu) (.refl u)⟩
    · exact nomatch hm
    · exact ⟨t, hdec, .refl t⟩
  · have hd := hj t hdec
    obtain ⟨a1, _⟩ := decRow_ctr_len hd hc
    obtain ⟨a2, hu⟩ := decRow_hstep hd hc hdec
    exact ⟨a1, a2, hu⟩

/-- **The AIR with segments and the `dec` jet accepts**: as `AcceptsCP`,
    each row within a segment a `NormRowD`. -/
structure AcceptsCD (M : List Cell) (m0 : Mach) (J : Nat) (roots : List Nat) (nilA n : Nat) (e : Nat → Nat)
    (row : Nat → Air.Row) : Prop where
  npos : 0 < n
  heap0 : M.take (row 0).ctr = m0.heap
  hd0 : (row 0).hd = roots.getD 0 0
  stk0 : (row 0).stk = nilA
  ctr0 : (row 0).ctr = m0.heap.length
  emono : ∀ j, j + 1 < n → e j < e (j + 1)
  restart : ∀ j, j + 1 < n → row (e j + 1) = ⟨roots.getD (j + 1) 0, nilA, (row (e j)).ctr⟩
  trans : ∀ i, i < e (n - 1) → (∀ j, j + 1 < n → i ≠ e j) → NormRowD M J (row i) (row (i + 1))
  ends : ∀ j, j < n → Air.rd M (row (e j)).ctr (row (e j)).hd = some .K ∧
    Air.rd M (row (e j)).ctr (row (e j)).stk = some .nil

section

variable {M : List Cell} {m0 : Mach} {J : Nat} {roots : List Nat} {nilA n : Nat} {e : Nat → Nat}
  {row : Nat → Air.Row}

/-- **Within a segment, the run reads back as head reduction with the jet.** -/
theorem AcceptsCD.within (h : AcceptsCD M m0 J roots nilA n e row) {j : Nat} (hj : j < n)
    (hc : (row (segStart e j)).ctr ≤ M.length) {t0 : OTerm} (hdec : odecode (Air.st M (row (segStart e j))) = some t0) :
    ∀ b, segStart e j ≤ b → b ≤ e j →
      (row b).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row b).ctr ∧
      ∃ t, odecode (Air.st M (row b)) = some t ∧ HSteps (InMem M) J t0 t := by
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
      obtain ⟨h1, h2, u, hu, hsu⟩ := normRowD_spec hcb hn ht
      exact ⟨h2, Nat.le_trans hsb h1, u, hu, hst.trans hsu⟩
    · rw [← hl]
      exact ⟨hc, Nat.le_refl _, t0, hdec, .refl _⟩

end

/-- **A table the AIR with the `dec` jet accepts from the composed machine
    of an open statement** makes every verifier, applied to the bits and
    the region's witness, head-reduce with the jet to `K`, the jet's
    subjects in the memory. -/
theorem composedD_sound_of {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Vs : List OTerm} {J : Nat}
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {M : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (h : AcceptsCD M (cMachineO ρ shp region Vs) J (cHeapO ρ shp region Vs).2
      (cHeapO ρ shp region Vs).1.length Vs.length e row) :
    ∃ w, cWitness ρ (BT.nleaves shp) region = some w ∧
      ∀ V ∈ Vs, HSteps (InMem M) J (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) .K := by
  let N := BT.nleaves shp
  obtain ⟨w, hw⟩ := witnessOf_some (slots_wf ρ N hr) (by simp [slotHeap_length]; omega)
  refine ⟨w, hw, ?_⟩
  obtain ⟨_, hdec⟩ := cMachineO_decode (Vs := Vs) hw
  let m0 := cMachineO ρ shp region Vs
  have hm0 : m0.heap = M.take (row 0).ctr := h.heap0.symm
  have hc0 : (row 0).ctr = m0.heap.length := h.ctr0
  have hcM : (row 0).ctr ≤ M.length := by
    have := congrArg List.length h.heap0
    rw [List.length_take, ← h.ctr0] at this
    omega
  have hregs : ∀ j, j < Vs.length → (row (segStart e j)).hd = (cHeapO ρ shp region Vs).2.getD j 0 ∧
      (row (segStart e j)).stk = (cHeapO ρ shp region Vs).1.length := by
    intro j hj
    cases j with
    | zero => exact ⟨h.hd0, h.stk0⟩
    | succ j =>
      have := h.restart j hj
      show (row (e j + 1)).hd = _ ∧ (row (e j + 1)).stk = _
      rw [this]
      exact ⟨rfl, rfl⟩
  -- a segment's start decodes to its verifier on the bits and the witness
  have hstart : ∀ j V, Vs[j]? = some V → (row (segStart e j)).ctr ≤ M.length →
      m0.heap.length ≤ (row (segStart e j)).ctr →
      odecode (Air.st M (row (segStart e j))) = some (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) := by
    intro j V hjV hc hm
    have hj : j < Vs.length := (List.getElem?_eq_some_iff.1 hjV).1
    have hroot := hdec j V hjV
    have hle : (row 0).ctr ≤ (row (segStart e j)).ctr := by rw [hc0]; exact hm
    have hlen : (Air.st M (row (segStart e j))).heap.length = (row (segStart e j)).ctr := by
      simp [Air.st, Air.take_length hc]
    have e1 : V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO = appL (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) [] := rfl
    rw [e1]
    apply odecode_of
    · show otermAt (M.take (row (segStart e j)).ctr) (_ + 1) (row (segStart e j)).hd = _
      rw [(hregs j hj).1]
      rw [hm0] at hroot
      refine Air.otermAt_take hle ?_ hroot
      rw [← hm0, hlen]
      show m0.heap.length + 1 ≤ _
      omega
    · show ostackAt (M.take (row (segStart e j)).ctr) (_ + 1) (row (segStart e j)).stk = _
      rw [(hregs j hj).2]
      have hn : (M.take (row (segStart e j)).ctr)[(cHeapO ρ shp region Vs).1.length]? = some .nil := by
        have h1 : m0.heap[(cHeapO ρ shp region Vs).1.length]? = some .nil := by simp [m0, cMachineO]
        rw [hm0, List.getElem?_take] at h1
        rw [List.getElem?_take]
        split at h1
        · rw [if_pos (by omega)]; exact h1
        · cases h1
      unfold ostackAt
      rw [hn]
  -- every segment: its start within the table, past the machine, and its run
  have hseg : ∀ j, j < Vs.length → (row (segStart e j)).ctr ≤ M.length ∧ m0.heap.length ≤ (row (segStart e j)).ctr := by
    intro j
    induction j with
    | zero => intro _; exact ⟨hcM, by rw [show segStart e 0 = 0 from rfl, hc0]; exact Nat.le_refl _⟩
    | succ j ih =>
      intro hj1
      obtain ⟨hc, hm⟩ := ih (by omega)
      obtain ⟨V, hV⟩ : ∃ V, Vs[j]? = some V := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨he, hse, _⟩ := h.within (by omega) hc (hstart j V hV hc hm) (e j) (segStart_le h.emono j (by omega))
        (Nat.le_refl _)
      have hcs : (row (segStart e (j + 1))).ctr = (row (e j)).ctr := by
        show (row (e j + 1)).ctr = _
        rw [h.restart j hj1]
      exact ⟨by rw [hcs]; exact he, by rw [hcs]; omega⟩
  intro V hV
  obtain ⟨j, hj, hVj⟩ := List.getElem_of_mem hV
  have hj' : Vs[j]? = some V := by rw [List.getElem?_eq_getElem hj, hVj]
  obtain ⟨hc, hm⟩ := hseg j hj
  obtain ⟨_, _, v, hv, hsteps⟩ := h.within hj hc (hstart j V hj' hc hm) (e j) (segStart_le h.emono j hj)
    (Nat.le_refl _)
  have hK : v = .K := by
    refine odecode_K hv ?_ ?_
    · rw [← (h.ends j hj).1, Air.rd_eq]; rfl
    · rw [← (h.ends j hj).2, Air.rd_eq]; rfl
  rw [hK] at hsteps
  exact hsteps

end CompM
