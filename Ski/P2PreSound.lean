import Ski.Circuit.CompPFinal

/-!
# What a proof of `p2pre h` proves

`p2pre_meaning`: when the verifier of `p2pre h`, with `J` closed to
`Poseidon2SKI.Pcomb`, evaluates to `K` on a comb of 496 bits, the bits'
sixteen 31-bit elements permute to a state whose first element is `h`.

- The verifier passes the comb to `Pcomb` with the continuation
  `CHECK_h`, and `Pcomb` passes the outputs' bits to it
  (`Pcomb_implements`).
- `CHECK_h` reads the first 31 bits against `h`'s.  On a wrong bit it hands
  the rest to `Θ K`, which absorbs every argument and reaches the weak head
  normal form `K (Θ K)`, never `K` (`thetaK_not_K`).  Weak reduction is
  confluent (`church_rosser`), so every reduct of a term that reaches `K`
  still reaches it; so every bit is right (`chk_sound`).

`p2preExport_sound` composes it with the circuit's soundness: an accepted
proof of `p2pre h` holds in its memory 496 bits whose elements' Poseidon2
permutation begins with `h`.
-/

open Term Compose CompM ComposedPText Poseidon2SKI

namespace P2Pre

/-- `appT` respects weak reduction of its head. -/
theorem appT_left {t t' : Term} (h : WSteps t t') : ∀ xs : List Term, WSteps (appT t xs) (appT t' xs)
  | [] => h
  | x :: xs => appT_left (h.left x) xs

/-- `Θ K`, applied to anything, reaches `K (Θ K)`. -/
theorem thetaK_absorbs : ∀ xs : List Term, WSteps (appT (BitArith.thetaT ⬝ K) xs) (K ⬝ (BitArith.thetaT ⬝ K))
  | [] => BitArith.theta_unfold K
  | x :: xs => by
    have h1 : WSteps (BitArith.thetaT ⬝ K ⬝ x) (BitArith.thetaT ⬝ K) :=
      ((BitArith.theta_unfold K).left x).trans (.single (.K _ _))
    exact (appT_left h1 xs).trans (thetaK_absorbs xs)

/-- **`Θ K` never becomes `K`**, whatever it is applied to. -/
theorem thetaK_not_K (xs : List Term) : ¬ WSteps (appT (BitArith.thetaT ⬝ K) xs) K := fun h => by
  have h' := (wsteps_K_iff (thetaK_absorbs xs)).1 h
  have := (Whnf.K1 (BitArith.thetaT ⬝ K)).wsteps_K h'
  cases this

theorem close_badO (σ : Nat → Term) : badO.close σ = BitArith.thetaT ⬝ K := by
  show BitArith.thetaT.toO.close σ ⬝ K = _
  rw [close_toO]

theorem close_ite (σ : Nat → Term) (b : Bool) (X Y : OTerm) :
    (if b then X else Y).close σ = if b then X.close σ else Y.close σ := by
  cases b <;> rfl

/-- **`chkO es m` reaches `K` only on the bits `es`.** -/
theorem chk_sound (m : Nat) : ∀ (es : List Bool) (σ : Nat → Term) (as : List Bool) (rest : List Term),
    as.length = es.length → WSteps (appT ((chkO es m).close σ) (as.map boolT ++ rest)) K → as = es
  | [], _, as, _, hl, _ => List.eq_nil_of_length_eq_zero hl
  | e :: es, σ, a :: as, rest, hl, hk => by
    have hl' : as.length = es.length := Nat.succ.inj hl
    let X : OTerm := if e then chkO es m else badO
    let Y : OTerm := if e then badO else chkO es m
    have hb := absN_beta_close [0] (.var 0 ⬝ₒ X ⬝ₒ Y) σ [boolT a] rfl
    have e1 : (OTerm.var 0 ⬝ₒ X ⬝ₒ Y).close (overrideC σ [0] [boolT a]) =
        boolT a ⬝ X.close (updC σ 0 (boolT a)) ⬝ Y.close (updC σ 0 (boolT a)) := rfl
    rw [e1] at hb
    have hs := hb.trans (Compose.boolT_sel a _ _)
    have hk' : WSteps (appT (if a then X.close (updC σ 0 (boolT a)) else Y.close (updC σ 0 (boolT a)))
        (as.map boolT ++ rest)) K :=
      (wsteps_K_iff (appT_left hs _)).1 hk
    by_cases hae : a = e
    · subst hae
      have hX : (if a then X.close (updC σ 0 (boolT a)) else Y.close (updC σ 0 (boolT a))) =
          (chkO es m).close (updC σ 0 (boolT a)) := by
        cases a <;> rfl
      rw [hX] at hk'
      rw [chk_sound m es (updC σ 0 (boolT a)) as rest hl' hk']
    · exfalso
      have hB : (if a then X.close (updC σ 0 (boolT a)) else Y.close (updC σ 0 (boolT a))) =
          BitArith.thetaT ⬝ K := by
        cases a <;> cases e
        · exact absurd rfl hae
        · exact close_badO _
        · exact close_badO _
        · exact absurd rfl hae
      rw [hB] at hk'
      exact thetaK_not_K _ hk'

theorem bits_flatMap_cons (y : Nat) (ys : List Nat) :
    (y :: ys).flatMap (BitArith.bitsOf 31) = BitArith.bitsOf 31 y ++ ys.flatMap (BitArith.bitsOf 31) := rfl

/-- The verifier's environment after its two arguments: `J` is `Pcomb`. -/
theorem env_J (a b : Term) : overrideC (jetEnv JP2) [0, 1] [a, b] JP2 = Pcomb := by
  show (if JP2 = 1 then b else if JP2 = 0 then a else jetEnv JP2 JP2) = Pcomb
  rw [if_neg (by decide), if_neg (by decide)]
  show (if JP2 = JP2 then Pcomb else _) = Pcomb
  rw [if_pos rfl]

theorem env_0 (σ : Nat → Term) (a b : Term) : overrideC σ [0, 1] [a, b] 0 = a := rfl

theorem close_body (σ : Nat → Term) (h : Nat) :
    (OTerm.var JP2 ⬝ₒ checkO h ⬝ₒ .var 0).close σ = σ JP2 ⬝ (checkO h).close σ ⬝ σ 0 := rfl

/-- **The meaning of the verifier**: on a comb of 496 bits, it evaluates to
    `K`, with `J` closed to `Pcomb`, only if the bits' elements permute to a
    state beginning with `h`. -/
theorem p2pre_meaning {h : Nat} (hh : h < Poseidon2.p) {ρ : Nat → Bool} {w : Term}
    (hev : EvalRel ((VsP h).map (·.close (jetEnv JP2)), SameShape (combBT 496)) (fillB (combBT 496) ρ 0) w) :
    (Poseidon2.permute (valsB ((List.range 496).map ρ))).getD 0 0 = h := by
  have hev' := eval_K_iff.1 (hev.2 _ (List.mem_singleton.2 rfl))
  rw [fill_comb ρ 495 0, show (List.range' 0 (495 + 1)) = List.range 496 from List.range_eq_range'.symm] at hev'
  have hlen : ((List.range 496).map ρ).length = 496 := by simp
  generalize (List.range 496).map ρ = bs at hev' hlen ⊢
  -- the verifier passes the comb to `Pcomb`
  have hb := absN_beta_close [0, 1] (.var JP2 ⬝ₒ checkO h ⬝ₒ .var 0) (jetEnv JP2) [combT bs, w] rfl
  generalize hσ : overrideC (jetEnv JP2) [0, 1] [combT bs, w] = σ at hb
  have hJ : σ JP2 = Pcomb := by rw [← hσ]; exact env_J _ _
  have h0 : σ 0 = combT bs := by rw [← hσ]; rfl
  have e1 : (OTerm.var JP2 ⬝ₒ checkO h ⬝ₒ .var 0).close σ = Pcomb ⬝ (checkO h).close σ ⬝ combT bs := by
    rw [close_body, hJ, h0]
  rw [e1] at hb
  have hk1 := (wsteps_K_iff hb).1 hev'
  -- `Pcomb` passes the outputs' bits to `CHECK_h`
  have hP := Pcomb_implements ⟨bs, hlen⟩ ((checkO h).close σ)
  rw [poseidon2Comb_encI, poseidon2Comb_encO, poseidon2Comb_spec] at hP
  have hk2 := (wsteps_K_iff hP).1 hk1
  -- `CHECK_h` reads `h`'s bits
  have hY : (Poseidon2.permute (valsB bs)).length = 16 := permute_len _ (by simp [valsB])
  obtain ⟨y, ys, hys⟩ : ∃ y ys, Poseidon2.permute (valsB bs) = y :: ys := by
    cases hp : Poseidon2.permute (valsB bs) with
    | nil => rw [hp] at hY; cases hY
    | cons y ys => exact ⟨y, ys, rfl⟩
  rw [hys] at hk2
  dsimp only at hk2
  rw [bits_flatMap_cons, List.map_append] at hk2
  have hc := chk_sound 465 (BitArith.bitsOf 31 h) _ (BitArith.bitsOf 31 y) _
    (by rw [bitsOf_length, bitsOf_length]) hk2
  have hy : y < Poseidon2.p := P2Air.permute_lt (valsB bs) (by simp [valsB]) y (by rw [hys]; exact List.mem_cons_self)
  have hv := congrArg BitArith.val hc
  have hp31 : Poseidon2.p < 2 ^ 31 := by decide
  rw [BitArith.val_bitsOf, BitArith.val_bitsOf, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
  rw [hys]
  exact hv

end P2Pre

namespace Circuit

open Air

/-- **Soundness of `p2pre h`**: an accepted proof of the statement, for
    AIRs with the normal forms of `compPAirs h`, holds in its memory 496
    bits whose sixteen 31-bit elements permute, by Poseidon2, to a state
    beginning with `h`. -/
theorem p2preExport_sound {h : Nat} (hh : h < Poseidon2.p) {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compPAirs h) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧
      (Poseidon2.permute (valsB ((List.range 496).map (bitsM (memOf Mm))))).getD 0 0 = h := by
  obtain ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, w, _, hev⟩ := compPExport_sound hs hacc
  exact ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, P2Pre.p2pre_meaning hh hev⟩

end Circuit
