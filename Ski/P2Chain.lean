import Ski.P2PreSound

open Term

/-!
# A statement with two jet calls: a Poseidon2 chain

`p2chain h`: "I know sixteen 31-bit values whose Poseidon2 permutation,
permuted again, begins with `h`."  The values are the statement's 496
private bits, laid out as for `p2pre h` (`ComposedPText`): a comb of 496
leaves and a one-cell region.  The verifier calls the jet twice:

  `V = λ β w. J ⬝ (J₂ ⬝ CHECK_h) ⬝ β`

- The first call is the jet on the comb at the atom `J` (`P2Jet.p2Row`),
  as in `p2pre h`.  Its continuation is `J₂ ⬝ CHECK_h`, so the outputs'
  496 bits land on the stack under `CHECK_h` with `J₂` at the head.
- The second call is the jet on the stack at the atom `J₂ = J + 1`
  (`P2Jet.p2RowS`): its inputs are the first call's outputs, pointers to
  the `K` and `K I` slots.  Its outputs go to `CHECK_h`, `p2pre h`'s check.

**`p2chain_meaning`**: when `V`, with `J` closed to `Pcomb` and `J₂` to
`Pbits` (`CompM.jetEnv`), evaluates to `K` on a comb of 496 bits, the bits'
elements, permuted twice, begin with `h`.  `Pcomb` passes the first
permutation's bits to `Pbits ⬝ CHECK_h` (`Pcomb_implements`), `Pbits`
passes the second's to `CHECK_h` (`Pbits_implements`), and `CHECK_h`
reaches `K` only on `h`'s bits (`P2Pre.chk_sound`).
-/

namespace P2Chain

open Compose CompM ComposedPText Poseidon2SKI P2Pre

/-- The verifier's environment after its two arguments: `J` is `Pcomb`. -/
theorem env_J (a b : Term) : overrideC (jetEnv JP2) [0, 1] [a, b] JP2 = Pcomb := by
  show (if JP2 = 1 then b else if JP2 = 0 then a else jetEnv JP2 JP2) = Pcomb
  rw [if_neg (by decide), if_neg (by decide)]
  show (if JP2 = JP2 then Pcomb else _) = Pcomb
  rw [if_pos rfl]

/-- … and `J₂` is `Pbits`. -/
theorem env_JS (a b : Term) : overrideC (jetEnv JP2) [0, 1] [a, b] JP2S = Pbits := by
  show (if JP2S = 1 then b else if JP2S = 0 then a else jetEnv JP2 JP2S) = Pbits
  rw [if_neg (by decide), if_neg (by decide)]
  show (if JP2 + 1 = JP2 then Pcomb else if JP2 + 1 = JP2 + 1 then Pbits else K) = Pbits
  rw [if_neg (by omega), if_pos rfl]

/-- The permutation's 496 output bits. -/
theorem out_length (bs : List Bool) :
    ((Poseidon2.permute (valsB bs)).flatMap (BitArith.bitsOf 31)).length = 496 := by
  have hY : (Poseidon2.permute (valsB bs)).length = 16 := permute_len _ (by simp [valsB])
  generalize Poseidon2.permute (valsB bs) = ys at hY
  have : ∀ ys : List Nat, (ys.flatMap (BitArith.bitsOf 31)).length = 31 * ys.length := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      rw [List.flatMap_cons, List.length_append, ih, bitsOf_length, List.length_cons]
      omega
  rw [this, hY]

/-- **The meaning of the chain's verifier**: on a comb of 496 bits, it
    evaluates to `K`, with `J` closed to `Pcomb` and `J₂` to `Pbits`, only
    if the bits' elements, permuted twice, begin with `h`. -/
theorem p2chain_meaning {h : Nat} (hh : h < Poseidon2.p) {ρ : Nat → Bool} {w : Term}
    (hev : EvalRel ((VsC h).map (·.close (jetEnv JP2)), SameShape (combBT 496)) (fillB (combBT 496) ρ 0) w) :
    (Poseidon2.permute (valsB ((Poseidon2.permute (valsB ((List.range 496).map ρ))).flatMap
      (BitArith.bitsOf 31)))).getD 0 0 = h := by
  have hev' := eval_K_iff.1 (hev.2 _ (List.mem_singleton.2 rfl))
  rw [fill_comb ρ 495 0, show (List.range' 0 (495 + 1)) = List.range 496 from List.range_eq_range'.symm] at hev'
  have hlen : ((List.range 496).map ρ).length = 496 := by simp
  generalize (List.range 496).map ρ = bs at hev' hlen ⊢
  -- the verifier passes the comb to `Pcomb`, the continuation `Pbits ⬝ CHECK_h`
  have hb := absN_beta_close [0, 1] (.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h) ⬝ₒ .var 0) (jetEnv JP2)
    [combT bs, w] rfl
  generalize hσ : overrideC (jetEnv JP2) [0, 1] [combT bs, w] = σ at hb
  have hJ : σ JP2 = Pcomb := by rw [← hσ]; exact env_J _ _
  have hJS : σ JP2S = Pbits := by rw [← hσ]; exact env_JS _ _
  have h0 : σ 0 = combT bs := by rw [← hσ]; rfl
  have e1 : (OTerm.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h) ⬝ₒ .var 0).close σ =
      Pcomb ⬝ (Pbits ⬝ (checkO h).close σ) ⬝ combT bs := by
    show σ JP2 ⬝ (σ JP2S ⬝ (checkO h).close σ) ⬝ σ 0 = _
    rw [hJ, hJS, h0]
  rw [e1] at hb
  have hk1 := (wsteps_K_iff hb).1 hev'
  -- `Pcomb` passes the first permutation's bits to `Pbits ⬝ CHECK_h`
  have hP := Pcomb_implements ⟨bs, hlen⟩ (Pbits ⬝ (checkO h).close σ)
  rw [poseidon2Comb_encI, poseidon2Comb_encO, poseidon2Comb_spec] at hP
  have hk2 := (wsteps_K_iff hP).1 hk1
  dsimp only at hk2
  -- `Pbits` passes the second's to `CHECK_h`
  generalize hcs : (Poseidon2.permute (valsB bs)).flatMap (BitArith.bitsOf 31) = cs at hk2
  have hcl : cs.length = 496 := by rw [← hcs]; exact out_length bs
  have hQ := Pbits_implements ⟨cs, hcl⟩ ((checkO h).close σ)
  rw [poseidon2B_encI, poseidon2B_encO, poseidon2B_spec, appT] at hQ
  dsimp only at hQ
  have hk3 := (wsteps_K_iff hQ).1 hk2
  -- `CHECK_h` reads `h`'s bits
  have hY : (Poseidon2.permute (valsB cs)).length = 16 := permute_len _ (by simp [valsB])
  obtain ⟨y, ys, hys⟩ : ∃ y ys, Poseidon2.permute (valsB cs) = y :: ys := by
    cases hp : Poseidon2.permute (valsB cs) with
    | nil => rw [hp] at hY; cases hY
    | cons y ys => exact ⟨y, ys, rfl⟩
  rw [hys] at hk3
  rw [bits_flatMap_cons, List.map_append] at hk3
  have hc := chk_sound 465 (BitArith.bitsOf 31 h) _ (BitArith.bitsOf 31 y) _
    (by rw [bitsOf_length, bitsOf_length]) hk3
  have hy : y < Poseidon2.p := P2Air.permute_lt (valsB cs) (by simp [valsB]) y (by rw [hys]; exact List.mem_cons_self)
  have hv := congrArg BitArith.val hc
  have hp31 : Poseidon2.p < 2 ^ 31 := by decide
  rw [BitArith.val_bitsOf, BitArith.val_bitsOf, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
  rw [hys]
  exact hv

end P2Chain
