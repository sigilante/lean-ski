import Ski.P2Commit

/-!
# The jet's verifiers accept honest bits

The converse of `P2Pre.p2pre_meaning` and `P2Commit.p2commit_meaning`:
on a comb of 496 bits whose Poseidon2 permutation begins with `h`, the
verifier of `p2pre h`, with `J` closed to `Pcomb`, evaluates to `K`
(`p2pre_complete`); on bits whose commitment is `c` and which meet `pat`,
so does the verifier of `p2commit c pat` (`p2commit_complete`).  Both hold
for every witness `w`, which the verifiers ignore.

- `CHECK_h` passes the bits of `h` and absorbs the 465 after them
  (`chk_complete`); `CHECK_c` passes the bits of `c`, absorbs 248 and
  returns the argument after them (`chkX_complete`, `P2Commit.absorbX_steps`).
- `PAT` passes each bit its entry allows (`selT_complete`, `patO_complete`).
-/

open Term Compose CompM ComposedPText Poseidon2SKI

namespace P2Complete

open P2Pre P2Commit

/-- `[x₁ … xₘ] K` takes `m` arguments to `K`. -/
theorem absorbO_K (σ : Nat → Term) : ∀ (m : Nat) (xs : List Term), xs.length = m →
    WSteps (appT ((absorbO m).close σ) xs) K
  | 0, [], _ => .refl _
  | m + 1, x :: xs, hl => by
    have h1 : WSteps (appT ((absorbO (m + 1)).close σ) (x :: xs)) (appT ((absorbO m).close σ) xs) :=
      appT_left (.single (.K _ _)) xs
    exact h1.trans (absorbO_K σ m xs (Nat.succ.inj hl))

/-- One bit read: the bit `e` itself selects the branch that reads on. -/
theorem read_bit (σ : Nat → Term) (e : Bool) (X Y : OTerm) :
    WSteps ((absN [0] (.var 0 ⬝ₒ X ⬝ₒ Y)).close σ ⬝ boolT e)
      (if e then X.close (updC σ 0 (boolT e)) else Y.close (updC σ 0 (boolT e))) := by
  have hb := absN_beta_close [0] (.var 0 ⬝ₒ X ⬝ₒ Y) σ [boolT e] rfl
  have e1 : (OTerm.var 0 ⬝ₒ X ⬝ₒ Y).close (overrideC σ [0] [boolT e]) =
      boolT e ⬝ X.close (updC σ 0 (boolT e)) ⬝ Y.close (updC σ 0 (boolT e)) := rfl
  rw [e1] at hb
  exact hb.trans (Compose.boolT_sel e _ _)

/-- **`chkO es m` reaches `K` on the bits `es` and `m` more.** -/
theorem chk_complete (m : Nat) : ∀ (es : List Bool) (σ : Nat → Term) (xs : List Term), xs.length = m →
    WSteps (appT ((chkO es m).close σ) (es.map boolT ++ xs)) K
  | [], σ, xs, hl => absorbO_K σ m xs hl
  | e :: es, σ, xs, hl => by
    have hr := read_bit σ e (if e then chkO es m else badO) (if e then badO else chkO es m)
    have hX : (if e then (if e then chkO es m else badO).close (updC σ 0 (boolT e))
        else (if e then badO else chkO es m).close (updC σ 0 (boolT e))) =
        (chkO es m).close (updC σ 0 (boolT e)) := by cases e <;> rfl
    rw [hX] at hr
    exact (appT_left hr _).trans (chk_complete m es _ xs hl)

/-- **`chkX es F` passes the bits `es` on to `F`.** -/
theorem chkX_complete (F : OTerm) : ∀ (es : List Bool) (σ : Nat → Term) (rest : List Term),
    ∃ σ', WSteps (appT ((chkX es F).close σ) (es.map boolT ++ rest)) (appT (F.close σ') rest)
  | [], σ, rest => ⟨σ, .refl _⟩
  | e :: es, σ, rest => by
    have hr := read_bit σ e (if e then chkX es F else badO) (if e then badO else chkX es F)
    have hX : (if e then (if e then chkX es F else badO).close (updC σ 0 (boolT e))
        else (if e then badO else chkX es F).close (updC σ 0 (boolT e))) =
        (chkX es F).close (updC σ 0 (boolT e)) := by cases e <;> rfl
    rw [hX] at hr
    obtain ⟨σ', h⟩ := chkX_complete F es (updC σ 0 (boolT e)) rest
    exact ⟨σ', (appT_left hr _).trans h⟩

/-- **A test passes a bit its entry allows.** -/
theorem selT_complete (p : Option Bool) (b : Bool) (X : Term) (h : ∀ t, p = some t → b = t) :
    WSteps (selT p (boolT b) X) X := by
  cases p with
  | none => exact .refl _
  | some t =>
    rw [h t rfl]
    cases t
    · exact Compose.boolT_sel false _ _
    · exact Compose.boolT_sel true _ _

theorem patHolds_tail {p : Option Bool} {ps : List (Option Bool)} {b : Bool} {bs : List Bool}
    (h : PatHolds (p :: ps) (b :: bs)) : PatHolds ps bs := fun i t hi => h (i + 1) t hi

theorem patHolds_head {p : Option Bool} {ps : List (Option Bool)} {b : Bool} {bs : List Bool}
    (h : PatHolds (p :: ps) (b :: bs)) : ∀ t, p = some t → b = t := fun t hp => by
  have := h 0 t (by rw [hp]; rfl)
  exact Option.some.inj this

/-- **`PAT` reaches `K` on bits that meet it.** -/
theorem patO_complete : ∀ (pat : List (Option Bool)) (bs : List Bool) (σ : Nat → Term), pat.length = bs.length →
    0 < bs.length → PatHolds pat bs → WSteps ((patO pat).close σ ⬝ combT bs) K
  | [p], [b], σ, _, _, hp => by
    have hb := absN_beta_close [0] (selO p (.var 0) .K) σ [boolT b] rfl
    rw [close_selO] at hb
    exact hb.trans (selT_complete p b K (patHolds_head hp))
  | p :: q :: ps, b :: c :: bs, σ, hl, _, hp => by
    let body : OTerm := selO p (.var 1) (patO (q :: ps) ⬝ₒ .var 2)
    have h1 := absN_beta_close [0] (.var 0 ⬝ₒ absN [1, 2] body) σ [combT (b :: c :: bs)] rfl
    have e1 : (OTerm.var 0 ⬝ₒ absN [1, 2] body).close (overrideC σ [0] [combT (b :: c :: bs)]) =
        pairT (boolT b) (combT (c :: bs)) ⬝ (absN [1, 2] body).close (updC σ 0 (combT (b :: c :: bs))) := rfl
    rw [e1] at h1
    have h2 := pairT_app (boolT b) (combT (c :: bs)) ((absN [1, 2] body).close (updC σ 0 (combT (b :: c :: bs))))
    have h3 := absN_beta_close [1, 2] body (updC σ 0 (combT (b :: c :: bs))) [boolT b, combT (c :: bs)] rfl
    let σ2 := overrideC (updC σ 0 (combT (b :: c :: bs))) [1, 2] [boolT b, combT (c :: bs)]
    have e3 : body.close σ2 = selT p (boolT b) ((patO (q :: ps)).close σ2 ⬝ combT (c :: bs)) := by
      show (selO p (.var 1) (patO (q :: ps) ⬝ₒ .var 2)).close σ2 = _
      rw [close_selO]; rfl
    rw [e3] at h3
    have h4 := selT_complete p b ((patO (q :: ps)).close σ2 ⬝ combT (c :: bs)) (patHolds_head hp)
    exact h1.trans (h2.trans (h3.trans (h4.trans
      (patO_complete (q :: ps) (c :: bs) σ2 (Nat.succ.inj hl) (Nat.zero_lt_succ _) (patHolds_tail hp)))))
  | [], _, _, hl, hp, _ => by rw [← hl] at hp; exact absurd hp (Nat.lt_irrefl 0)
  | [_], [], _, _, hp, _ => absurd hp (Nat.lt_irrefl 0)
  | [_], _ :: _ :: _, _, hl, _, _ => Nat.noConfusion (Nat.succ.inj hl)
  | _ :: _ :: _, [], _, hl, _, _ => Nat.noConfusion hl
  | _ :: _ :: _, [_], _, hl, _, _ => Nat.noConfusion (Nat.succ.inj hl)

theorem flatMap_length31 : ∀ ys : List Nat, (ys.flatMap (BitArith.bitsOf 31)).length = 31 * ys.length :=
  cbits_length

/-- The jet passes the outputs' bits to its continuation. -/
theorem jet_step (bs : List Bool) (hl : bs.length = 496) (k : Term) :
    WSteps (Pcomb ⬝ k ⬝ combT bs)
      (appT k (((Poseidon2.permute (valsB bs)).flatMap (BitArith.bitsOf 31)).map boolT)) := by
  have hP := Pcomb_implements ⟨bs, hl⟩ k
  rw [poseidon2Comb_encI, poseidon2Comb_encO, poseidon2Comb_spec] at hP
  exact hP

theorem evalRel_of {V : OTerm} {ρ : Nat → Bool} {w : Term}
    (h : WSteps (V.close (jetEnv JP2) ⬝ combT ((List.range 496).map ρ) ⬝ w) K) :
    EvalRel ([V].map (·.close (jetEnv JP2)), SameShape (combBT 496)) (fillB (combBT 496) ρ 0) w := by
  refine ⟨fillB_shape _ ρ 0, fun P hP => ?_⟩
  rw [List.map_cons, List.map_nil, List.mem_singleton] at hP
  rw [hP, fill_comb ρ 495 0, show (List.range' 0 (495 + 1)) = List.range 496 from List.range_eq_range'.symm]
  exact eval_K_iff.2 h

/-- **The verifier of `p2pre h` accepts a preimage**: on 496 bits whose
    elements permute to a state beginning with `h`, with any witness. -/
theorem p2pre_complete {h : Nat} {ρ : Nat → Bool}
    (hperm : (Poseidon2.permute (valsB ((List.range 496).map ρ))).getD 0 0 = h) (w : Term) :
    EvalRel ((VsP h).map (·.close (jetEnv JP2)), SameShape (combBT 496)) (fillB (combBT 496) ρ 0) w := by
  apply evalRel_of
  have hlen : ((List.range 496).map ρ).length = 496 := by rw [List.length_map, List.length_range]
  generalize (List.range 496).map ρ = bs at hperm hlen ⊢
  have hb := absN_beta_close [0, 1] (.var JP2 ⬝ₒ checkO h ⬝ₒ .var 0) (jetEnv JP2) [combT bs, w] rfl
  generalize hσ : overrideC (jetEnv JP2) [0, 1] [combT bs, w] = σ at hb
  have hJ : σ JP2 = Pcomb := by rw [← hσ]; exact P2Pre.env_J _ _
  have h0 : σ 0 = combT bs := by rw [← hσ]; rfl
  rw [close_body, hJ, h0] at hb
  refine hb.trans ((jet_step bs hlen _).trans ?_)
  have hY : (Poseidon2.permute (valsB bs)).length = 16 := permute_len _ (valsB_length bs)
  obtain ⟨y, ys, hys⟩ : ∃ y ys, Poseidon2.permute (valsB bs) = y :: ys := by
    cases hp : Poseidon2.permute (valsB bs) with
    | nil => rw [hp] at hY; cases hY
    | cons y ys => exact ⟨y, ys, rfl⟩
  rw [hys] at hY hperm ⊢
  have hy : y = h := hperm
  rw [bits_flatMap_cons, List.map_append, hy]
  exact chk_complete 465 (BitArith.bitsOf 31 h) σ _
    (by rw [List.length_map, flatMap_length31, Nat.succ.inj hY])

/-- **The verifier of `p2commit c pat` accepts an opening**: on 496 bits
    whose commitment is `c` and which meet `pat`, with any witness. -/
theorem p2commit_complete {c : List Nat} {pat : List (Option Bool)} (hpat : pat.length = 496) {ρ : Nat → Bool}
    (hc : commitB ((List.range 496).map ρ) = c) (hp : PatHolds pat ((List.range 496).map ρ)) (w : Term) :
    EvalRel ([verifierC c pat].map (·.close (jetEnv JP2)), SameShape (combBT 496)) (fillB (combBT 496) ρ 0) w := by
  apply evalRel_of
  have hlen : ((List.range 496).map ρ).length = 496 := by rw [List.length_map, List.length_range]
  generalize (List.range 496).map ρ = bs at hc hp hlen ⊢
  have hb := absN_beta_close [100, 101] (.var JP2 ⬝ₒ checkC c ⬝ₒ .var 100 ⬝ₒ (patO pat ⬝ₒ .var 100))
    (jetEnv JP2) [combT bs, w] rfl
  generalize hσ : overrideC (jetEnv JP2) [100, 101] [combT bs, w] = σ at hb
  have hJ : σ JP2 = Pcomb := by rw [← hσ]; exact P2Commit.env_J _ _
  have h0 : σ 100 = combT bs := by rw [← hσ]; rfl
  rw [close_bodyC, hJ, h0] at hb
  refine hb.trans ((appT_left (jet_step bs hlen ((checkC c).close σ)) [(patO pat).close σ ⬝ combT bs]).trans ?_)
  rw [← appT_append]
  have hsplit : (Poseidon2.permute (valsB bs)).flatMap (BitArith.bitsOf 31) =
      cbits ((Poseidon2.permute (valsB bs)).take 8) ++ cbits ((Poseidon2.permute (valsB bs)).drop 8) := by
    show _ = List.flatMap _ _ ++ List.flatMap _ _
    rw [← List.flatMap_append, List.take_append_drop]
  have hc' : (Poseidon2.permute (valsB bs)).take 8 = c := hc
  rw [hsplit, hc', List.map_append, List.append_assoc]
  obtain ⟨σ', h1⟩ := chkX_complete (absorbX 248 .I) (cbits c) σ
    ((cbits ((Poseidon2.permute (valsB bs)).drop 8)).map boolT ++ [(patO pat).close σ ⬝ combT bs])
  have hYl : (Poseidon2.permute (valsB bs)).length = 16 := permute_len _ (valsB_length bs)
  have hdrop : (cbits ((Poseidon2.permute (valsB bs)).drop 8)).length = 248 := by
    rw [cbits_length, List.length_drop, hYl]
  have h2 := absorbX_steps .I σ' 248 ((cbits ((Poseidon2.permute (valsB bs)).drop 8)).map boolT)
    [(patO pat).close σ ⬝ combT bs] (by rw [List.length_map, hdrop])
  have h3 : WSteps (appT (OTerm.I.close σ') [(patO pat).close σ ⬝ combT bs]) ((patO pat).close σ ⬝ combT bs) :=
    .single (.I _)
  exact h1.trans (h2.trans (h3.trans (patO_complete pat bs σ (by rw [hpat, hlen]) (by rw [hlen]; decide) hp)))

end P2Complete
