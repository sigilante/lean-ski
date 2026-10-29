import Ski.P2PreSound
import Ski.DataJet

/-!
# What a proof of `p2commit c pat` proves, and the hidden hand-off

`p2commit c pat` states: 496 private bits, a value and randomness of
eight 31-bit elements each, whose Poseidon2 compression is `c` and whose
bits meet the pattern `pat`.  Its verifier is
`λ β w. J ⬝ CHECK_c ⬝ β ⬝ (PAT ⬝ β)`.

- `p2commit_meaning`: when the verifier, with `J` closed to `Pcomb`,
  evaluates to `K` on a comb of 496 bits, the bits' commitment is `c` and
  the bits meet `pat`.  `CHECK_c` reads the first eight outputs' 248 bits
  against `c`'s (`chkX_sound`), absorbs the other eight
  (`absorbX_steps`), and returns the argument after them, `PAT ⬝ β`; a
  required bit that is wrong selects `Θ K`, which never reaches `K`
  (`selT_sound`, `patO_sound`).
- `verifierC_occ`: the verifier's only free variable is the jet's, so the
  circuit's soundness applies (`p2commitExport_sound`).
- `handoff` and `p2commit_chain`: two accepted proofs over one commitment
  `c`.  The second's memory holds bits meeting both patterns, or the two
  memories encode openings that collide.  It needs the first pattern to
  fix value bits only (`ValueOnly`), and both to fix bit 30 of each value
  element to 0 (`Canonical`).  The collision is the one the two proofs'
  tables encode, not merely one that exists: every compression of
  sixteen elements to eight has collisions.
-/

open Term Compose CompM ComposedPText Poseidon2SKI

namespace P2Commit

open P2Pre

/-- **`chkX es F` reaches `K` only on the bits `es`**, and then `F` does on
    what follows them. -/
theorem chkX_sound (F : OTerm) : ∀ (es : List Bool) (σ : Nat → Term) (as : List Bool) (rest : List Term),
    as.length = es.length → WSteps (appT ((chkX es F).close σ) (as.map boolT ++ rest)) K →
      as = es ∧ ∃ σ', WSteps (appT (F.close σ') rest) K
  | [], σ, as, rest, hl, hk => by
    have : as = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    exact ⟨rfl, σ, hk⟩
  | e :: es, σ, a :: as, rest, hl, hk => by
    have hl' : as.length = es.length := Nat.succ.inj hl
    let X : OTerm := if e then chkX es F else badO
    let Y : OTerm := if e then badO else chkX es F
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
          (chkX es F).close (updC σ 0 (boolT a)) := by
        cases a <;> rfl
      rw [hX] at hk'
      obtain ⟨h1, h2⟩ := chkX_sound F es (updC σ 0 (boolT a)) as rest hl' hk'
      exact ⟨by rw [h1], h2⟩
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

/-- `absorbX m F` passes over `m` arguments to `F`. -/
theorem absorbX_steps (F : OTerm) (σ : Nat → Term) : ∀ (m : Nat) (xs rest : List Term), xs.length = m →
    WSteps (appT ((absorbX m F).close σ) (xs ++ rest)) (appT (F.close σ) rest)
  | 0, [], rest, _ => .refl _
  | m + 1, x :: xs, rest, hl => by
    have h1 : WSteps (K ⬝ (absorbX m F).close σ ⬝ x) ((absorbX m F).close σ) := .single (.K _ _)
    exact (appT_left h1 (xs ++ rest)).trans (absorbX_steps F σ m xs rest (Nat.succ.inj hl))


/-- A pattern holds on the bits: each fixed entry is its bit. -/
def PatHolds (pat : List (Option Bool)) (bs : List Bool) : Prop :=
  ∀ (i : Nat) (b : Bool), pat[i]? = some (some b) → bs[i]? = some b

/-- A pattern's test of one bit, closed. -/
def selT : Option Bool → Term → Term → Term
  | none, _, X => X
  | some true, a, X => a ⬝ X ⬝ (BitArith.thetaT ⬝ K)
  | some false, a, X => a ⬝ (BitArith.thetaT ⬝ K) ⬝ X

theorem close_selO (σ : Nat → Term) (p : Option Bool) (A B : OTerm) :
    (selO p A B).close σ = selT p (A.close σ) (B.close σ) := by
  cases p with
  | none => rfl
  | some t => cases t <;> (show _ = _; simp only [selO, selT, close_app', close_badO])

/-- **A test passes only its bit**, and then its continuation reaches `K`. -/
theorem selT_sound (p : Option Bool) (b : Bool) (X : Term) (h : WSteps (selT p (boolT b) X) K) :
    (∀ t, p = some t → b = t) ∧ WSteps X K := by
  cases p with
  | none => exact And.intro (fun _ e => nomatch e) h
  | some t =>
    have hs := Compose.boolT_sel b
    cases t <;> cases b
    · exact And.intro (fun _ e => by cases e; rfl) ((wsteps_K_iff (hs _ _)).1 h)
    · exact absurd ((wsteps_K_iff (hs _ _)).1 h) (thetaK_not_K [])
    · exact absurd ((wsteps_K_iff (hs _ _)).1 h) (thetaK_not_K [])
    · exact And.intro (fun _ e => by cases e; rfl) ((wsteps_K_iff (hs _ _)).1 h)

/-- **The pattern's check reaches `K` only on bits it holds on.** -/
theorem patO_sound : ∀ (pat : List (Option Bool)) (bs : List Bool) (σ : Nat → Term), pat.length = bs.length →
    0 < bs.length → WSteps ((patO pat).close σ ⬝ combT bs) K → PatHolds pat bs
  | [p], [b], σ, _, _, hk => by
    have hb := absN_beta_close [0] (selO p (.var 0) .K) σ [boolT b] rfl
    rw [close_selO] at hb
    have := selT_sound p b K ((wsteps_K_iff hb).1 hk)
    unfold PatHolds
    intro i t hi
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi ⊢; exact this.1 t hi
    | succ i => rw [List.getElem?_cons_succ, List.getElem?_nil] at hi; nomatch hi
  | p :: q :: ps, b :: c :: bs, σ, hl, _, hk => by
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
    have hk' := (wsteps_K_iff (h1.trans (h2.trans h3))).1 hk
    obtain ⟨hp, hX⟩ := selT_sound p b _ hk'
    have ih := patO_sound (q :: ps) (c :: bs) σ2 (Nat.succ.inj hl) (Nat.zero_lt_succ _) hX
    unfold PatHolds
    intro i t hi
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi ⊢; exact hp t hi
    | succ i => exact ih i t hi
  | [], _, _, hl, hp, _ => by rw [← hl] at hp; exact absurd hp (Nat.lt_irrefl 0)
  | [_], [], _, _, hp, _ => absurd hp (Nat.lt_irrefl 0)
  | [_], _ :: _ :: _, _, hl, _, _ => Nat.noConfusion (Nat.succ.inj hl)
  | _ :: _ :: _, [], _, hl, _, _ => Nat.noConfusion hl
  | _ :: _ :: _, [_], _, hl, _, _ => Nat.noConfusion (Nat.succ.inj hl)


/-- 31-bit elements are their bits. -/
theorem cbits_inj : ∀ (a b : List Nat), a.length = b.length → (∀ x ∈ a, x < 2 ^ 31) → (∀ x ∈ b, x < 2 ^ 31) →
    cbits a = cbits b → a = b
  | [], [], _, _, _, _ => rfl
  | x :: a, y :: b, hl, ha, hb, h => by
    have h' : BitArith.bitsOf 31 x ++ cbits a = BitArith.bitsOf 31 y ++ cbits b := h
    obtain ⟨e1, e2⟩ := List.append_inj h' (by rw [bitsOf_length, bitsOf_length])
    have hv := congrArg BitArith.val e1
    rw [BitArith.val_bitsOf, BitArith.val_bitsOf, Nat.mod_eq_of_lt (ha x List.mem_cons_self),
      Nat.mod_eq_of_lt (hb y List.mem_cons_self)] at hv
    rw [hv, cbits_inj a b (Nat.succ.inj hl) (fun z hz => ha z (List.mem_cons_of_mem _ hz))
      (fun z hz => hb z (List.mem_cons_of_mem _ hz)) e2]
  | [], _ :: _, hl, _, _, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _, _, _ => Nat.noConfusion hl

theorem cbits_length : ∀ a : List Nat, (cbits a).length = 31 * a.length
  | [] => rfl
  | x :: a => by
    show (BitArith.bitsOf 31 x ++ cbits a).length = _
    rw [List.length_append, bitsOf_length, cbits_length a, List.length_cons]; omega

theorem env_J (a b : Term) : overrideC (jetEnv JP2) [100, 101] [a, b] JP2 = Pcomb := by
  show (if JP2 = 101 then b else if JP2 = 100 then a else jetEnv JP2 JP2) = Pcomb
  rw [if_neg (by decide), if_neg (by decide)]
  show (if JP2 = JP2 then Pcomb else _) = Pcomb
  rw [if_pos rfl]

theorem close_bodyC (σ : Nat → Term) (c : List Nat) (pat : List (Option Bool)) :
    (OTerm.var JP2 ⬝ₒ checkC c ⬝ₒ .var 100 ⬝ₒ (patO pat ⬝ₒ .var 100)).close σ =
      σ JP2 ⬝ (checkC c).close σ ⬝ σ 100 ⬝ ((patO pat).close σ ⬝ σ 100) := rfl

/-- **The meaning of the commit verifier**: on a comb of 496 bits, it
    evaluates to `K`, with `J` closed to `Pcomb`, only if the bits' elements
    permute to a state whose first eight elements are `c`, and the bits hold
    the pattern. -/
theorem p2commit_meaning {c : List Nat} {pat : List (Option Bool)} (hc : c.length = 8)
    (hcp : ∀ x ∈ c, x < Poseidon2.p) (hpat : pat.length = 496) {ρ : Nat → Bool} {w : Term}
    (hev : EvalRel ([verifierC c pat].map (·.close (jetEnv JP2)), SameShape (combBT 496))
      (fillB (combBT 496) ρ 0) w) :
    (Poseidon2.permute (valsB ((List.range 496).map ρ))).take 8 = c ∧ PatHolds pat ((List.range 496).map ρ) := by
  have hev' := eval_K_iff.1 (hev.2 _ (List.mem_singleton.2 rfl))
  rw [fill_comb ρ 495 0, show (List.range' 0 (495 + 1)) = List.range 496 from List.range_eq_range'.symm] at hev'
  have hlen : ((List.range 496).map ρ).length = 496 := by simp
  generalize (List.range 496).map ρ = bs at hev' hlen ⊢
  have hb := absN_beta_close [100, 101] (.var JP2 ⬝ₒ checkC c ⬝ₒ .var 100 ⬝ₒ (patO pat ⬝ₒ .var 100)) (jetEnv JP2)
    [combT bs, w] rfl
  generalize hσ : overrideC (jetEnv JP2) [100, 101] [combT bs, w] = σ at hb
  have hJ : σ JP2 = Pcomb := by rw [← hσ]; exact env_J _ _
  have h0 : σ 100 = combT bs := by rw [← hσ]; rfl
  rw [close_bodyC, hJ, h0] at hb
  have hk1 := (wsteps_K_iff hb).1 hev'
  have hP := Pcomb_implements ⟨bs, hlen⟩ ((checkC c).close σ)
  rw [poseidon2Comb_encI, poseidon2Comb_encO, poseidon2Comb_spec] at hP
  have hk2 := (wsteps_K_iff (appT_left hP [(patO pat).close σ ⬝ combT bs])).1 hk1
  rw [← appT_append] at hk2
  dsimp only at hk2
  have hYl : (Poseidon2.permute (valsB bs)).length = 16 := permute_len _ (by simp [valsB])
  have hsplit : (Poseidon2.permute (valsB bs)).flatMap (BitArith.bitsOf 31) =
      cbits ((Poseidon2.permute (valsB bs)).take 8) ++ cbits ((Poseidon2.permute (valsB bs)).drop 8) := by
    show _ = List.flatMap _ _ ++ List.flatMap _ _
    rw [← List.flatMap_append, List.take_append_drop]
  rw [hsplit, List.map_append, List.append_assoc] at hk2
  have h8 : ((Poseidon2.permute (valsB bs)).take 8).length = 8 := by rw [List.length_take, hYl]; rfl
  obtain ⟨heq, σ', hrest⟩ := chkX_sound (absorbX 248 .I) (cbits c) σ (cbits ((Poseidon2.permute (valsB bs)).take 8)) _
    (by rw [cbits_length, cbits_length, h8, hc]) hk2
  have hlt : ∀ x ∈ Poseidon2.permute (valsB bs), x < 2 ^ 31 := fun x hx => by
    have := P2Air.permute_lt _ (by simp [valsB]) x hx
    have : Poseidon2.p < 2 ^ 31 := by decide
    omega
  refine ⟨cbits_inj _ _ (by rw [h8, hc]) (fun x hx => hlt x (List.mem_of_mem_take hx))
    (fun x hx => by have := hcp x hx; have : Poseidon2.p < 2 ^ 31 := (by decide); omega) heq, ?_⟩
  have hdrop : (cbits ((Poseidon2.permute (valsB bs)).drop 8)).length = 248 := by
    rw [cbits_length, List.length_drop, hYl]
  have ha := absorbX_steps .I σ' 248 ((cbits ((Poseidon2.permute (valsB bs)).drop 8)).map boolT)
    [(patO pat).close σ ⬝ combT bs] (by rw [List.length_map, hdrop])
  have hI := (wsteps_K_iff ha).1 hrest
  have hpk := (wsteps_K_iff (.single (.I _) : WSteps (Term.I ⬝ ((patO pat).close σ ⬝ combT bs)) _)).1 hI
  exact patO_sound pat bs σ (by rw [hpat, hlen]) (by rw [hlen]; decide) hpk


theorem absorbX_occ {x : Nat} {F : OTerm} : ∀ m, Occ x (absorbX m F) → Occ x F
  | 0, h => h
  | m + 1, h => by
    cases h with
    | left _ h => nomatch h
    | right _ h => exact absorbX_occ m h

theorem chkX_closed {x : Nat} {F : OTerm} (hF : ¬ Occ x F) : ∀ es, ¬ Occ x (chkX es F)
  | [], h => hF h
  | e :: es, h => by
    obtain ⟨h', hx⟩ := occ_abs h
    have side : ∀ (b : Bool), ¬ Occ x (if b then chkX es F else badO) ∧ ¬ Occ x (if b then badO else chkX es F) := by
      intro b; cases b
      · exact ⟨Circuit.badO_closed x, chkX_closed hF es⟩
      · exact ⟨chkX_closed hF es, Circuit.badO_closed x⟩
    cases h' with
    | left _ h'' =>
      cases h'' with
      | left _ h3 => cases h3; exact hx rfl
      | right _ h3 => exact (side e).1 h3
    | right _ h'' => exact (side e).2 h''

theorem selO_occ {x : Nat} {a X : OTerm} : ∀ p, Occ x (selO p a X) → Occ x a ∨ Occ x X
  | none, h => .inr h
  | some true, h => by
    cases h with
    | left _ h =>
      cases h with
      | left _ h => exact .inl h
      | right _ h => exact .inr h
    | right _ h => exact absurd h (Circuit.badO_closed x)
  | some false, h => by
    cases h with
    | left _ h =>
      cases h with
      | left _ h => exact .inl h
      | right _ h => exact absurd h (Circuit.badO_closed x)
    | right _ h => exact .inr h

theorem patO_closed (x : Nat) : ∀ pat, ¬ Occ x (patO pat)
  | [], h => nomatch h
  | [p], h => by
    obtain ⟨h', hx⟩ := occ_abs h
    rcases selO_occ p h' with h3 | h3
    · cases h3; exact hx rfl
    · nomatch h3
  | p :: q :: ps, h => by
    obtain ⟨h', hx0⟩ := occ_abs h
    cases h' with
    | left _ h3 => cases h3; exact hx0 rfl
    | right _ h3 =>
      obtain ⟨h4, hx1⟩ := occ_abs h3
      obtain ⟨h5, hx2⟩ := occ_abs h4
      rcases selO_occ p h5 with h6 | h6
      · cases h6; exact hx1 rfl
      · cases h6 with
        | left _ h7 => exact patO_closed x (q :: ps) h7
        | right _ h7 => cases h7; exact hx2 rfl

theorem checkC_closed (c : List Nat) (x : Nat) : ¬ Occ x (checkC c) :=
  chkX_closed (fun h => by have h0 : Occ x OTerm.I := absorbX_occ 248 h; cases h0) (cbits c)

/-- **The commit verifier's only variable is the jet's.** -/
theorem verifierC_occ (c : List Nat) (pat : List (Option Bool)) (x : Nat) (hx : Occ x (verifierC c pat)) :
    x = JP2 := by
  obtain ⟨h1, hx0⟩ := occ_abs hx
  obtain ⟨h2, hx1⟩ := occ_abs h1
  cases h2 with
  | left _ h3 =>
    cases h3 with
    | left _ h4 =>
      cases h4 with
      | left _ h5 => cases h5; rfl
      | right _ h5 => exact absurd h5 (checkC_closed c x)
    | right _ h4 => cases h4; exact absurd rfl hx0
  | right _ h3 =>
    cases h3 with
    | left _ h4 => exact absurd h4 (patO_closed x pat)
    | right _ h4 => cases h4; exact absurd rfl hx0


-- ---------------------------------------------------------------------------
-- Two stages over one commitment
-- ---------------------------------------------------------------------------

/-- The commitment of 496 bits: their sixteen elements' permutation,
    truncated to eight. -/
def commitB (bs : List Bool) : List Nat := (Poseidon2.permute (valsB bs)).take 8

/-- A pattern fixes value bits only, none of the randomness's 248. -/
def ValueOnly (pat : List (Option Bool)) : Prop := ∀ i b, pat[i]? = some (some b) → i < 248

/-- A pattern keeps the value canonical: bit 30 of each of its eight
    elements is 0, so each is below `2^30 < p`. -/
def Canonical (pat : List (Option Bool)) : Prop := ∀ e, e < 8 → pat[31 * e + 30]? = some (some false)

def toF (x : Nat) : DataJet.F := ⟨x % Poseidon2.p, Nat.mod_lt _ (by decide)⟩

/-- The opening 496 bits encode: the value's eight elements and the
    randomness's eight, reduced. -/
def openB (bs : List Bool) : List DataJet.F × List DataJet.F :=
  (((valsB bs).take 8).map toF, ((valsB bs).drop 8).map toF)

theorem val_append_false : ∀ l : List Bool, BitArith.val (l ++ [false]) = BitArith.val l
  | [] => rfl
  | b :: l => by
    show b.toNat + 2 * BitArith.val (l ++ [false]) = _
    rw [val_append_false l]; rfl

theorem chunk_length (bs : List Bool) (e : Nat) : (chunk bs e).length = 31 := by
  rw [chunk, List.length_map, List.length_range]

/-- An element whose bit 30 is 0 is below `2^30`. -/
theorem chunk_lt (bs : List Bool) (e : Nat) (h : bs.getD (31 * e + 30) false = false) :
    BitArith.val (chunk bs e) < 2 ^ 30 := by
  have hc : chunk bs e = (List.range 30).map (fun j => bs.getD (31 * e + j) false) ++ [false] := by
    rw [chunk, List.range_succ, List.map_append, List.map_cons, List.map_nil, h]
  rw [hc, val_append_false]
  have := val_lt ((List.range 30).map (fun j => bs.getD (31 * e + j) false))
  rwa [List.length_map, List.length_range] at this

theorem getD_of_pat {pat : List (Option Bool)} {bs : List Bool} (hp : PatHolds pat bs) {i : Nat} {b : Bool}
    (hi : pat[i]? = some (some b)) : bs.getD i false = b := by
  rw [List.getD_eq_getElem?_getD, hp i b hi]; rfl

theorem valsB_take_mem {bs : List Bool} {x : Nat} (hx : x ∈ (valsB bs).take 8) :
    ∃ e, e < 8 ∧ x = BitArith.val (chunk bs e) := by
  rw [valsB, ← List.map_take, List.take_range] at hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  exact ⟨e, List.mem_range.1 he, rfl⟩

/-- A canonical pattern's bits have a canonical value. -/
theorem value_lt {pat : List (Option Bool)} {bs : List Bool} (hk : Canonical pat) (hp : PatHolds pat bs) :
    ∀ x ∈ (valsB bs).take 8, x < Poseidon2.p := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := valsB_take_mem hx
  have h1 : BitArith.val (chunk bs e) < 2 ^ 30 := chunk_lt bs e (getD_of_pat hp (hk e he))
  have h30 : (2 : Nat) ^ 30 < Poseidon2.p := by decide
  rw [hxe]
  exact Nat.lt_trans h1 h30

theorem map_mod_of_lt : ∀ l : List Nat, (∀ x ∈ l, x < Poseidon2.p) → l.map (· % Poseidon2.p) = l
  | [], _ => rfl
  | x :: l, h => by
    rw [List.map_cons, Nat.mod_eq_of_lt (h x List.mem_cons_self),
      map_mod_of_lt l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem map_toF_val (l : List Nat) : (l.map toF).map Fin.val = l.map (· % Poseidon2.p) := by
  rw [List.map_map]; rfl

theorem openB_commit (bs : List Bool) :
    DataJet.commit (openB bs).1 (openB bs).2 = commitB bs := by
  show (Poseidon2.permute ((((valsB bs).take 8).map toF ++ ((valsB bs).drop 8).map toF).map Fin.val)).take 8 = _
  rw [← List.map_append, List.take_append_drop, map_toF_val, ← P2Air.permute_mod _ (valsB_length bs)]
  rfl

theorem openB_opening (bs : List Bool) : DataJet.Opening (openB bs) := by
  refine ⟨?_, ?_⟩
  · show (((valsB bs).take 8).map toF).length = 8
    rw [List.length_map, List.length_take, valsB_length]; rfl
  · show (((valsB bs).drop 8).map toF).length = 8
    rw [List.length_map, List.length_drop, valsB_length]

/-- Equal values mean equal value bits. -/
theorem value_bits {bs bs' : List Bool} (h : (valsB bs).take 8 = (valsB bs').take 8) {i : Nat} (hi : i < 248) :
    bs.getD i false = bs'.getD i false := by
  have he : i / 31 < 8 := (Nat.div_lt_iff_lt_mul (by decide)).2 hi
  have hj : i % 31 < 31 := Nat.mod_lt _ (by decide)
  have hv : BitArith.val (chunk bs (i / 31)) = BitArith.val (chunk bs' (i / 31)) := by
    have h1 := congrArg (·[i / 31]?) h
    simp only [List.getElem?_take, if_pos he, valsB, List.getElem?_map,
      List.getElem?_range (Nat.lt_trans he (by decide : 8 < 16)), Option.map_some, Option.some.injEq] at h1
    exact h1
  have hc : chunk bs (i / 31) = chunk bs' (i / 31) := by
    rw [← bitsOf_val (chunk bs (i / 31)), ← bitsOf_val (chunk bs' (i / 31)), hv, chunk_length, chunk_length]
  have h2 := congrArg (·[i % 31]?) hc
  simp only [chunk, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at h2
  rwa [Nat.div_add_mod] at h2

theorem patHolds_of_getD {pat : List (Option Bool)} {bs bs' : List Bool} (hp : PatHolds pat bs)
    (hl : bs'.length = 496) (hv : ValueOnly pat)
    (heq : ∀ i, i < 248 → bs.getD i false = bs'.getD i false) : PatHolds pat bs' := by
  intro i b hi
  have h248 := hv i b hi
  have hlt : i < bs'.length := by rw [hl]; exact Nat.lt_trans h248 (by decide)
  rw [List.getElem?_eq_getElem hlt]
  have := heq i h248
  rw [getD_of_pat hp hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] at this
  exact congrArg some this.symm

/-- **Two stages over one commitment.**  Two values, each holding its
    stage's pattern, under one commitment: either the second's bits hold
    both patterns, or the two openings are a collision of the
    compression.  The first pattern fixes value bits only; both keep the
    value canonical. -/
theorem handoff (pat₁ pat₂ : List (Option Bool)) {bs₁ bs₂ : List Bool} (hl₂ : bs₂.length = 496)
    (hv₁ : ValueOnly pat₁) (hk₁ : Canonical pat₁) (hk₂ : Canonical pat₂)
    (hp₁ : PatHolds pat₁ bs₁) (hp₂ : PatHolds pat₂ bs₂) (hc : commitB bs₁ = commitB bs₂) :
    (PatHolds pat₁ bs₂ ∧ PatHolds pat₂ bs₂) ∨ DataJet.Collision (openB bs₁) (openB bs₂) :=
  match decEq ((valsB bs₁).take 8) ((valsB bs₂).take 8) with
  | isTrue e => .inl ⟨patHolds_of_getD hp₁ hl₂ hv₁ (fun _ hi => value_bits e hi), hp₂⟩
  | isFalse e => .inr ⟨openB_opening bs₁, openB_opening bs₂, fun h => e (by
      have h' := congrArg (List.map Fin.val) h
      show (valsB bs₁).take 8 = (valsB bs₂).take 8
      have a := map_toF_val ((valsB bs₁).take 8)
      have b := map_toF_val ((valsB bs₂).take 8)
      rw [map_mod_of_lt _ (value_lt hk₁ hp₁)] at a
      rw [map_mod_of_lt _ (value_lt hk₂ hp₂)] at b
      rw [← a, ← b]; exact h'),
    (openB_commit bs₁).trans (hc.trans (openB_commit bs₂).symm)⟩

-- ---------------------------------------------------------------------------
-- The chain's conditions, decided
-- ---------------------------------------------------------------------------

/-- `ValueOnly`, decided: every entry past bit 248 is free. -/
def valueOnlyB (pat : List (Option Bool)) : Bool := (pat.drop 248).all (· == none)

/-- `Canonical`, decided. -/
def canonicalB (pat : List (Option Bool)) : Bool :=
  (List.range 8).all fun e => pat[31 * e + 30]? == some (some false)

theorem valueOnlyB_sound {pat : List (Option Bool)} (h : valueOnlyB pat = true) : ValueOnly pat := by
  intro i b hi
  match Nat.lt_or_ge i 248 with
  | .inl hl => exact hl
  | .inr hge =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
    have hk : (pat.drop 248)[k]? = some (some b) := by rw [List.getElem?_drop]; exact hi
    have hm := List.mem_of_getElem? hk
    have := List.all_eq_true.1 h _ hm
    nomatch this

theorem canonicalB_sound {pat : List (Option Bool)} (h : canonicalB pat = true) : Canonical pat :=
  fun e he => eq_of_beq (List.all_eq_true.1 h e (List.mem_range.2 he))

/-- **The chain's conditions**: two `p2commit` statements with one
    commitment, both valid, both patterns fixing value bits only and
    keeping the value canonical.  The theorem needs value bits only of the
    first pattern; the second's keeps a stage from publishing randomness
    bits, which would weaken the commitment's hiding. -/
def chainB : PStmt → PStmt → Bool
  | .commit c₁ pat₁, .commit c₂ pat₂ => (PStmt.commit c₁ pat₁).ok && (PStmt.commit c₂ pat₂).ok &&
    c₁ == c₂ && valueOnlyB pat₁ && valueOnlyB pat₂ && canonicalB pat₁ && canonicalB pat₂
  | _, _ => false

theorem ok_commit {c : List Nat} {pat : List (Option Bool)} (h : (PStmt.commit c pat).ok = true) :
    c.length = 8 ∧ (∀ x ∈ c, x < Poseidon2.p) ∧ pat.length = 496 := by
  have h' : ((c.length == 8 && c.all (· < Poseidon2.p)) && pat.length == 496) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h'
  exact ⟨eq_of_beq h'.1.1, fun x hx => of_decide_eq_true (List.all_eq_true.1 h'.1.2 x hx), eq_of_beq h'.2⟩

/-- `chainB` decides the chain's hypotheses. -/
theorem chainB_sound {st₁ st₂ : PStmt} (h : chainB st₁ st₂ = true) :
    ∃ c pat₁ pat₂, st₁ = .commit c pat₁ ∧ st₂ = .commit c pat₂ ∧
      c.length = 8 ∧ (∀ x ∈ c, x < Poseidon2.p) ∧ pat₁.length = 496 ∧ pat₂.length = 496 ∧
      ValueOnly pat₁ ∧ Canonical pat₁ ∧ Canonical pat₂ := by
  match st₁, st₂, h with
  | .commit c₁ pat₁, .commit c₂ pat₂, h =>
    have h' : ((((((PStmt.commit c₁ pat₁).ok && (PStmt.commit c₂ pat₂).ok) && c₁ == c₂) && valueOnlyB pat₁) &&
        valueOnlyB pat₂) && canonicalB pat₁ && canonicalB pat₂) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨⟨⟨ok₁, ok₂⟩, hc⟩, hv⟩, _⟩, hk₁⟩, hk₂⟩ := h'
    obtain ⟨hl, hlt, hp₁⟩ := ok_commit ok₁
    obtain ⟨_, _, hp₂⟩ := ok_commit ok₂
    rw [← eq_of_beq hc]
    exact ⟨c₁, pat₁, pat₂, rfl, rfl, hl, hlt, hp₁, hp₂, valueOnlyB_sound hv, canonicalB_sound hk₁,
      canonicalB_sound hk₂⟩

end P2Commit

namespace Circuit

open Air P2Commit

/-- The 496 bits an accepted proof's memory holds. -/
def memBits (Mm : Table) : List Bool := (List.range 496).map (bitsM (memOf Mm))

theorem memBits_length (Mm : Table) : (memBits Mm).length = 496 := by
  rw [memBits, List.length_map, List.length_range]

/-- **What a proof of `p2commit c pat` proves**: an accepted proof, for
    AIRs with the normal forms of the statement's circuit, holds in its
    memory 496 bits whose commitment is `c` and which hold `pat`. -/
theorem p2commitExport_sound {c : List Nat} {pat : List (Option Bool)} (hc : c.length = 8)
    (hcp : ∀ x ∈ c, x < Poseidon2.p) (hpat : pat.length = 496) {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compPAirsG [verifierC c pat]) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧
      commitB (memBits Mm) = c ∧ PatHolds pat (memBits Mm) := by
  obtain ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, _, _, hev⟩ := compPExportG_sound (Vs := [verifierC c pat])
    (Nat.zero_lt_succ _) (fun V hV x hx => by
      rw [List.mem_singleton.1 hV] at hx
      exact .inl (verifierC_occ c pat x hx)) hs hacc
  exact ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, p2commit_meaning hc hcp hpat hev⟩

/-- **The hidden hand-off**: accepted proofs of `p2commit c pat₁` and
    `p2commit c pat₂`, over one commitment `c`.  The memory of the second
    holds bits that meet both patterns, or the openings the two memories
    encode are a collision of the compression.  The first pattern fixes
    value bits only, and both keep the value canonical. -/
theorem p2commit_chain {c : List Nat} {pat₁ pat₂ : List (Option Bool)} (hc : c.length = 8)
    (hcp : ∀ x ∈ c, x < Poseidon2.p) (hpat₁ : pat₁.length = 496) (hpat₂ : pat₂.length = 496)
    (hv₁ : ValueOnly pat₁) (hk₁ : Canonical pat₁) (hk₂ : Canonical pat₂)
    {Rs₁ Rs₂ : List AirD} {ts₁ ts₂ : List Table}
    (hs₁ : sameAirsB Rs₁ (compPAirsG [verifierC c pat₁]) = true) (hacc₁ : AcceptedP Rs₁ ts₁)
    (hs₂ : sameAirsB Rs₂ (compPAirsG [verifierC c pat₂]) = true) (hacc₂ : AcceptedP Rs₂ ts₂) :
    ∃ Mm₁ Mm₂, ts₁[1]? = some Mm₁ ∧ ts₂[1]? = some Mm₂ ∧ commitB (memBits Mm₂) = c ∧
      ((PatHolds pat₁ (memBits Mm₂) ∧ PatHolds pat₂ (memBits Mm₂)) ∨
        DataJet.Collision (openB (memBits Mm₁)) (openB (memBits Mm₂))) := by
  obtain ⟨_, Mm₁, _, _, _, _, _, _, _, rfl, hc₁, hp₁⟩ := p2commitExport_sound hc hcp hpat₁ hs₁ hacc₁
  obtain ⟨_, Mm₂, _, _, _, _, _, _, _, rfl, hc₂, hp₂⟩ := p2commitExport_sound hc hcp hpat₂ hs₂ hacc₂
  exact ⟨Mm₁, Mm₂, rfl, rfl, hc₂,
    handoff pat₁ pat₂ (memBits_length Mm₂) hv₁ hk₁ hk₂ hp₁ hp₂ (hc₁.trans hc₂.symm)⟩

/-- **The hand-off, as `ski-air compp-chain` checks it**: two statements
    `composed chain-p2` accepts (`chainB`), and an accepted proof of each
    for AIRs with the normal forms of its circuit. -/
theorem p2commit_chainB {st₁ st₂ : PStmt} (hb : chainB st₁ st₂ = true)
    {Rs₁ Rs₂ : List AirD} {ts₁ ts₂ : List Table}
    (hs₁ : sameAirsB Rs₁ (compPAirsG st₁.Vs) = true) (hacc₁ : AcceptedP Rs₁ ts₁)
    (hs₂ : sameAirsB Rs₂ (compPAirsG st₂.Vs) = true) (hacc₂ : AcceptedP Rs₂ ts₂) :
    ∃ c pat₁ pat₂, st₁ = .commit c pat₁ ∧ st₂ = .commit c pat₂ ∧
      ∃ Mm₁ Mm₂, ts₁[1]? = some Mm₁ ∧ ts₂[1]? = some Mm₂ ∧ commitB (memBits Mm₂) = c ∧
        ((PatHolds pat₁ (memBits Mm₂) ∧ PatHolds pat₂ (memBits Mm₂)) ∨
          DataJet.Collision (openB (memBits Mm₁)) (openB (memBits Mm₂))) := by
  obtain ⟨c, pat₁, pat₂, rfl, rfl, hc, hcp, hp₁, hp₂, hv, hk₁, hk₂⟩ := chainB_sound hb
  exact ⟨c, pat₁, pat₂, rfl, rfl, p2commit_chain hc hcp hp₁ hp₂ hv hk₁ hk₂ hs₁ hacc₁ hs₂ hacc₂⟩

end Circuit
