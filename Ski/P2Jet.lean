import Ski.InstOpen
import Ski.AirJet
import Ski.ZK.Poseidon2SKI

set_option linter.unusedSimpArgs false

open Term

/-!
# The Poseidon2 jet in the machine

The jet's head is an atom `j` in the heap.  When it reaches the head with
497 arguments on the stack, `k` and then 496 bits, each a Scott Boolean
(a `K` cell, or `K` applied to `I`), one step pops them, computes the
outputs, and pushes the outputs' 496 bits for `k`: each a stack cell
pointing at the heap's `K` slot (address 0) or `K I` slot (address 2).
The next head is `k`.  So the state

  `j ⬝ k ⬝ b₀ ⬝ … ⬝ b₄₉₅ ⬝ a₁ ⬝ …`  becomes  `k ⬝ c₀ ⬝ … ⬝ c₄₉₅ ⬝ a₁ ⬝ …`

with `c` the output bits of `Poseidon2SKI.poseidon2B`.

**`p2Row_cstep`**: a row that passes `p2Row` reads back, as an open term,
as one step of the contract's reduction (`DataJet.CStep.jet`).  Its
translation to SKI is `DataJet.CSteps.close` with `Poseidon2SKI.Pbits` in
the jet's place (`Pbits_implements`).
-/

namespace P2Jet

open Air Mach Poseidon2SKI BitArith Compose

/-- A Scott Boolean at `a`: a `K` cell for true, the cell `app 0 1` (`K`
    applied to `I`, through the slots) for false.  Requiring the slots'
    addresses lets the circuit check a bit with one read. -/
def boolAt (H : List Cell) (a : Nat) : Option Bool :=
  match H[a]? with
  | some .K => some true
  | some (.app 0 1) => some false
  | _ => none

/-- The Booleans at the addresses. -/
def bitsAt (H : List Cell) : List Nat → Option (List Bool)
  | [] => some []
  | a :: as =>
    match boolAt H a, bitsAt H as with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- The heap's first cells are the slots `K`, `I`, `K I`. -/
def slotsOK (H : List Cell) : Bool :=
  H[0]? == some .K && H[1]? == some .I && H[2]? == some (.app 0 1)

/-- The slot holding the Boolean `b`. -/
def bitPtr (b : Bool) : Nat := if b then 0 else 2

/-- The outputs' bits for the input bits `bs`. -/
def outBits (bs : List Bool) : List Bool := (Poseidon2.permute (valsB bs)).flatMap (bitsOf 31)

/-- Stack cells pushing `bs`, bottom first, from address `c` over the stack
    at `prev`. -/
def pushR (c prev : Nat) : List Bool → List Cell
  | [] => []
  | b :: bs => .cons (bitPtr b) prev :: pushR (c + 1) c bs

/-- The top of the stack after pushing `n` cells from `c` over `prev`. -/
def topOf (c prev n : Nat) : Nat := if n = 0 then prev else c + n - 1

/-- **The jet's row**: at the atom `j` with 497 arguments, `k` then 496
    Booleans, the outputs' bits pushed for `k` at the counter. -/
def p2Row (M : List Cell) (j : Nat) (r : Row) : Option Row :=
  let H := M.take r.ctr
  match H[r.hd]? with
  | some (.atom j') =>
    if j' = j ∧ slotsOK H = true then
      match popN H 497 r.stk with
      | some (k :: ps, rest) =>
        match bitsAt H ps with
        | some bs =>
          if wrs M r.ctr (pushR r.ctr rest (outBits bs).reverse) then
            some ⟨k, topOf r.ctr rest (outBits bs).length, r.ctr + (outBits bs).length⟩
          else none
        | none => none
      | _ => none
    else none
  | _ => none

-- ---------------------------------------------------------------------------
-- Reading back
-- ---------------------------------------------------------------------------

theorem boolAt_cases {H : List Cell} {a : Nat} {b : Bool} (h : boolAt H a = some b) :
    (b = true ∧ H[a]? = some .K) ∨ (b = false ∧ H[a]? = some (.app 0 1)) := by
  unfold boolAt at h
  split at h
  · rename_i heq; cases h; exact .inl ⟨rfl, heq⟩
  · rename_i heq; cases h; exact .inr ⟨rfl, heq⟩
  · cases h

theorem boolAt_ot {H : List Cell} (hs : slotsOK H = true) {a : Nat} {b : Bool} (h : boolAt H a = some b) :
    ∀ F, 2 ≤ F → otermAt H F a = some (boolT b).toO := by
  unfold slotsOK at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨h0, h1⟩, _⟩ := hs
  intro F hF
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 2 := ⟨F - 2, by omega⟩
  rcases boolAt_cases h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
  · show otermAt H (f + 1 + 1) a = some .K
    unfold otermAt; rw [ha]
  · show otermAt H (f + 1 + 1) a = some (.K ⬝ₒ .I)
    unfold otermAt; rw [ha]; dsimp only
    unfold otermAt; rw [h0]; unfold otermAt; rw [h1]

/-- The arguments a row pops read back as the Booleans it reads. -/
theorem bitsAt_ptrs {H : List Cell} (hs : slotsOK H = true) {F : Nat} (hF : 2 ≤ F) :
    ∀ {ps : List Nat} {Ns : List OTerm} {bs : List Bool}, OPtrsOK H F ps Ns → bitsAt H ps = some bs →
      Ns = bs.map fun b => (boolT b).toO
  | [], [], [], _, _ => rfl
  | p :: ps, N :: Ns, bs, ⟨h1, h2⟩, hb => by
    unfold bitsAt at hb
    cases hp : boolAt H p with
    | none => rw [hp] at hb; cases hb
    | some b =>
      cases hq : bitsAt H ps with
      | none => rw [hp, hq] at hb; cases hb
      | some bs' =>
        rw [hp, hq] at hb
        cases hb
        have e := boolAt_ot hs hp F hF
        rw [h1] at e
        cases e
        rw [bitsAt_ptrs hs hF h2 hq]; rfl
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | [], [], _ :: _, _, hb => nomatch hb

theorem bitsAt_length : ∀ {H : List Cell} {ps : List Nat} {bs : List Bool}, bitsAt H ps = some bs →
    bs.length = ps.length
  | _, [], bs, hb => by cases hb; rfl
  | H, p :: ps, bs, hb => by
    unfold bitsAt at hb
    cases hp : boolAt H p with
    | none => rw [hp] at hb; cases hb
    | some b =>
      cases hq : bitsAt H ps with
      | none => rw [hp, hq] at hb; cases hb
      | some bs' =>
        rw [hp, hq] at hb
        cases hb
        exact congrArg (· + 1) (bitsAt_length hq)

/-- The slots read back as the Booleans. -/
theorem slot_ot {H : List Cell} (hs : slotsOK H = true) (b : Bool) :
    ∀ F, 3 ≤ F → otermAt H F (bitPtr b) = some (boolT b).toO := by
  unfold slotsOK at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨h0, h1⟩, h2⟩ := hs
  intro F hF
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 3 := ⟨F - 3, by omega⟩
  cases b
  · show otermAt H (f + 2 + 1) 2 = some (.K ⬝ₒ .I)
    unfold otermAt; rw [h2]; dsimp only
    unfold otermAt; rw [h0]; unfold otermAt; rw [h1]
  · show otermAt H (f + 2 + 1) 0 = some .K
    unfold otermAt; rw [h0]

/-- **Pushed cells read back** as their Booleans over the stack below. -/
theorem push_ot {H : List Cell} (hs : slotsOK H = true) :
    ∀ (bs : List Bool) (c prev : Nat) (R : List OTerm) (F : Nat), 3 ≤ F →
      (∀ i, i < bs.length → H[c + i]? = (pushR c prev bs)[i]?) →
      ostackAt H F prev = some R →
      ostackAt H (F + bs.length) (topOf c prev bs.length) = some (bs.reverse.map (fun b => (boolT b).toO) ++ R)
  | [], _, _, _, _, _, _, h => h
  | b :: bs, c, prev, R, F, hF, hcells, hR => by
    have hc : H[c]? = some (.cons (bitPtr b) prev) := by
      have := hcells 0 (Nat.zero_lt_succ _); rw [Nat.add_zero] at this; exact this
    have h1 : ostackAt H (F + 1) c = some ((boolT b).toO :: R) := by
      unfold ostackAt; rw [hc]; dsimp only
      rw [slot_ot hs b (F + 1) (by omega), hR]
    have ih := push_ot hs bs (c + 1) c ((boolT b).toO :: R) (F + 1) (by omega)
      (fun i hi => by
        have := hcells (i + 1) (by simp only [List.length_cons]; omega)
        rw [show c + (i + 1) = c + 1 + i by omega] at this; exact this) h1
    have et : topOf (c + 1) c bs.length = topOf c prev (bs.length + 1) := by
      unfold topOf
      rw [if_neg (Nat.succ_ne_zero _)]
      rcases Nat.eq_zero_or_pos bs.length with hn | hn
      · rw [if_pos hn, hn]; omega
      · rw [if_neg (by omega)]; omega
    rw [et, show F + 1 + bs.length = F + (b :: bs).length by simp only [List.length_cons]; omega] at ih
    rw [List.reverse_cons, List.map_append, List.append_assoc]
    exact ih

theorem pushR_length : ∀ (c prev : Nat) (bs : List Bool), (pushR c prev bs).length = bs.length
  | _, _, [] => rfl
  | c, _, _ :: bs => congrArg (· + 1) (pushR_length (c + 1) c bs)

theorem CStep.appL {α β : Type} {cc : DataJet.CContract α β} {j : Nat} :
    ∀ (as : List OTerm) {t u : OTerm}, DataJet.CStep cc j t u → DataJet.CStep cc j (_root_.appL t as) (_root_.appL u as)
  | [], _, _, h => h
  | a :: as, _, _, h => CStep.appL as (.left a h)

/-- **A jet row reads back as one step of the jet's reduction.** -/
theorem p2Row_cstep {M : List Cell} {j : Nat} {r r' : Row} (h : p2Row M j r = some r')
    (hc : r.ctr ≤ M.length) {t : OTerm} (hdec : odecode (st M r) = some t) :
    r'.ctr ≤ M.length ∧ ∃ t', odecode (st M r') = some t' ∧ DataJet.CStep poseidon2B j t t' := by
  unfold p2Row at h
  dsimp only at h
  generalize hH : M.take r.ctr = H at h
  have hHl : H.length = r.ctr := by rw [← hH, List.length_take]; omega
  cases hhd : H[r.hd]? with
  | none => rw [hhd] at h; cases h
  | some cell =>
    rw [hhd] at h
    cases cell with
    | atom j' =>
      dsimp only at h
      by_cases hcond : j' = j ∧ slotsOK H = true
      · rw [if_pos hcond] at h
        obtain ⟨hjj, hs⟩ := hcond
        cases hpop : popN H 497 r.stk with
        | none => rw [hpop] at h; cases h
        | some q =>
          obtain ⟨qs, rest⟩ := q
          rw [hpop] at h
          cases qs with
          | nil => cases h
          | cons k ps =>
            dsimp only at h
            cases hbits : bitsAt H ps with
            | none => rw [hbits] at h; cases h
            | some bs =>
              rw [hbits] at h
              dsimp only at h
              generalize hob : outBits bs = ob at h
              generalize hcs : pushR r.ctr rest ob.reverse = cs at h
              have hcsl : cs.length = ob.length := by
                rw [← hcs, pushR_length, List.length_reverse]
              cases hw : wrs M r.ctr cs with
              | false => rw [hw] at h; cases h
              | true =>
                rw [hw] at h
                cases h
                have htake := take_of_wrs hw
                rw [hH] at htake
                have hlen' : (M.take (r.ctr + cs.length)).length = r.ctr + cs.length := by
                  rw [htake, List.length_append, hHl]
                refine ⟨?_, ?_⟩
                · show r.ctr + ob.length ≤ M.length
                  rw [List.length_take] at hlen'
                  omega
                · -- The state before.
                  obtain ⟨hdt, args, h1, h2, rfl⟩ := odecode_eq hdec
                  replace h1 : otermAt H (H.length + 1) r.hd = some hdt := by rw [← hH]; exact h1
                  replace h2 : ostackAt H (H.length + 1) r.stk = some args := by rw [← hH]; exact h2
                  have hpos : 3 ≤ H.length := by
                    unfold slotsOK at hs
                    simp only [Bool.and_eq_true, beq_iff_eq] at hs
                    have := hs.2
                    rw [List.getElem?_eq_some_iff] at this
                    obtain ⟨hl, _⟩ := this
                    omega
                  have hj : hdt = .var j := by
                    unfold otermAt at h1; rw [hhd] at h1; cases h1; rw [hjj]
                  obtain ⟨Ns, R, G, hG, hargs, hNl, hpl, hok, hR⟩ := popN_ospec 497 hpop h2
                  cases Ns with
                  | nil => cases hNl
                  | cons Nk Nb =>
                    obtain ⟨hk, hb⟩ := hok
                    have hNb := bitsAt_ptrs hs (by omega) hb hbits
                    have hbl : bs.length = 496 := by
                      rw [bitsAt_length hbits]
                      simp only [List.length_cons] at hpl; omega
                    -- The state after.
                    have hH' : M.take (r.ctr + ob.length) = H ++ cs := by rw [← hcsl]; exact htake
                    have hs' : slotsOK (H ++ cs) = true := by
                      unfold slotsOK at hs ⊢
                      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
                        List.getElem?_append_left (by omega)]
                      exact hs
                    have hcells : ∀ i, i < ob.reverse.length →
                        (H ++ cs)[r.ctr + i]? = (pushR r.ctr rest ob.reverse)[i]? := fun i _ => by
                      rw [hcs, ← hHl, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
                    have hR' : ostackAt (H ++ cs) (H.length + 1) rest = some R :=
                      ostackAt_grow hR (by omega)
                    have hpush := push_ot hs' ob.reverse r.ctr rest R (H.length + 1) (by omega)
                      hcells hR'
                    rw [List.reverse_reverse, List.length_reverse] at hpush
                    have hk' : otermAt (H ++ cs) ((H ++ cs).length + 1) k = some Nk :=
                      otermAt_grow hk (by rw [List.length_append]; omega)
                    refine ⟨appL Nk (ob.map (fun b => (boolT b).toO) ++ R), ?_, ?_⟩
                    · show odecode ⟨M.take (r.ctr + ob.length), k, topOf r.ctr rest ob.length⟩ = _
                      rw [hH']
                      apply odecode_of hk'
                      rw [List.length_append, hcsl, show H.length + ob.length + 1 =
                        H.length + 1 + ob.length by omega]
                      exact hpush
                    · rw [hargs, hj, hNb, Mach.appL_app, Mach.appL_app]
                      have hjet := DataJet.CStep.jet (c := poseidon2B) (j := j) ⟨bs, hbl⟩ Nk
                      rw [poseidon2B_encI, poseidon2B_encO, poseidon2B_spec, List.map_map, List.map_map,
                        show (Poseidon2.permute (valsB bs)).flatMap (bitsOf 31) = ob from hob] at hjet
                      exact CStep.appL R hjet
      · rw [if_neg hcond] at h; cases h
    | _ => cases h

/-- A jet row moves the counter forward. -/
theorem p2Row_ctr {M : List Cell} {j : Nat} {r r' : Row} (h : p2Row M j r = some r') : r.ctr ≤ r'.ctr := by
  unfold p2Row at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · cases h; exact Nat.le_add_right _ _
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- A jet row's writes stay within the memory table. -/
theorem p2Row_len {M : List Cell} {j : Nat} {r r' : Row} (h : p2Row M j r = some r') (hc : r.ctr ≤ M.length) :
    r'.ctr ≤ M.length := by
  unfold p2Row at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i bs _
          split at h
          · rename_i hw
            cases h
            have ht := take_of_wrs hw
            have hl := congrArg List.length ht
            rw [List.length_take, List.length_append, List.length_take, pushR_length, List.length_reverse] at hl
            show r.ctr + (outBits bs).length ≤ M.length
            omega
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

end P2Jet
