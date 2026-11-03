import Ski.ComposedDText

/-!
# What a proof of `decpre p` proves

`decpre_meaning`: when the verifier of `decpre p`, with `J` closed to any
implementation `P` of the `dec` contract (`DataJet.Implements
DecJet.decContract P`; skinock's `jetT decF` is one, `dec_transport`),
evaluates to `K` on the encoded subject `s`, the subject's decrement is a
cell whose head is the atom `p`: `decSpec s = some [d r]` with `val d = p`.

- The verifier passes `J ⬝ w` to `CHECK_p`, and `P` takes `encNn s` to
  `encO (decSpec s)` (`Implements`).
- `CHECK_p` eliminates the result: a crash, an atom, or a cell headed by
  a cell hands the rest to `Θ K`, which absorbs every argument and never
  reaches `K` (`thetaK_not_K`); a cell headed by an atom has its bits read
  against `p`'s (`chkL_sound`).  Weak reduction is confluent
  (`church_rosser`), so every reduct of a term that reaches `K` still
  reaches it.
-/

open Term Compose DecJet ComposedDText BitArith

namespace DecPre

theorem appT_left {t t' : Term} (h : WSteps t t') : ∀ xs : List Term, WSteps (appT t xs) (appT t' xs)
  | [] => h
  | x :: xs => appT_left (h.left x) xs

/-- `Θ K`, applied to anything, reaches `K (Θ K)`. -/
theorem thetaK_absorbs : ∀ xs : List Term, WSteps (appT (thetaT ⬝ K) xs) (K ⬝ (thetaT ⬝ K))
  | [] => theta_unfold K
  | x :: xs => by
    have h1 : WSteps (thetaT ⬝ K ⬝ x) (thetaT ⬝ K) :=
      ((theta_unfold K).left x).trans (.single (.K _ _))
    exact (appT_left h1 xs).trans (thetaK_absorbs xs)

/-- **`Θ K` never becomes `K`**, whatever it is applied to. -/
theorem thetaK_not_K (xs : List Term) : ¬ WSteps (appT (thetaT ⬝ K) xs) K := fun h => by
  have h' := (wsteps_K_iff (thetaK_absorbs xs)).1 h
  have := (Whnf.K1 (thetaT ⬝ K)).wsteps_K h'
  cases this

theorem close_badO (σ : Nat → Term) : badO.close σ = thetaT ⬝ K := by
  show thetaT.toO.close σ ⬝ K = _
  rw [close_toO]

theorem close_ite (σ : Nat → Term) (b : Bool) (X Y : OTerm) :
    (if b then X else Y).close σ = if b then X.close σ else Y.close σ := by
  cases b <;> rfl

/-- A term reaching `Θ K` applied to arguments never reaches `K`. -/
theorem not_K_of_bad {t : Term} (xs : List Term) (h : WSteps t (appT (thetaT ⬝ K) xs)) : ¬ WSteps t K :=
  fun hk => thetaK_not_K xs ((wsteps_K_iff h).1 hk)

/-- Scott list elimination: `nil n c ↠ n`, `cons b t n c ↠ c b t`. -/
theorem nil_elim (n c : Term) : WSteps (bl [] ⬝ n ⬝ c) n := .single (.K _ _)

theorem cons_elim (b : Bool) (bs : List Bool) (n c : Term) :
    WSteps (bl (b :: bs) ⬝ n ⬝ c) (c ⬝ boolT b ⬝ bl bs) :=
  (WSteps.left _ (.single (.K _ _))).trans (pairT_app _ _ _)

/-- **`chkL es` reaches `K` only on the bits `es`.** -/
theorem chkL_sound : ∀ (es : List Bool) (σ : Nat → Term) (bs : List Bool),
    WSteps ((chkL es).close σ ⬝ bl bs) K → bs = es
  | [], σ, bs, hk => by
    have hb := absN_beta_close [0] (.var 0 ⬝ₒ .K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ badO))) σ [bl bs] rfl
    have e1 : (OTerm.var 0 ⬝ₒ .K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ badO))).close (overrideC σ [0] [bl bs]) =
        bl bs ⬝ K ⬝ (K ⬝ (K ⬝ badO.close (overrideC σ [0] [bl bs]))) := rfl
    rw [e1, close_badO] at hb
    cases bs with
    | nil => rfl
    | cons b bs' =>
      exfalso
      have h2 := hb.trans ((cons_elim b bs' _ _).trans
        ((WSteps.left _ (.single (.K _ _))).trans (.single (.K _ _))))
      exact not_K_of_bad [] h2 hk
  | e :: es, σ, bs, hk => by
    let X : OTerm := if e then chkL es ⬝ₒ .var 2 else badO
    let Y : OTerm := if e then badO else chkL es ⬝ₒ .var 2
    have hb := absN_beta_close [0] (.var 0 ⬝ₒ badO ⬝ₒ absN [1, 2] (.var 1 ⬝ₒ X ⬝ₒ Y)) σ [bl bs] rfl
    generalize hσ : overrideC σ [0] [bl bs] = σ' at hb
    have e1 : (OTerm.var 0 ⬝ₒ badO ⬝ₒ absN [1, 2] (.var 1 ⬝ₒ X ⬝ₒ Y)).close σ' =
        σ' 0 ⬝ badO.close σ' ⬝ (absN [1, 2] (.var 1 ⬝ₒ X ⬝ₒ Y)).close σ' := rfl
    have h0 : σ' 0 = bl bs := by rw [← hσ]; rfl
    rw [e1, close_badO, h0] at hb
    cases bs with
    | nil =>
      exfalso
      exact not_K_of_bad [] (hb.trans (nil_elim _ _)) hk
    | cons b bs' =>
      have h2 := hb.trans (cons_elim b bs' _ _)
      have hb2 := absN_beta_close [1, 2] (.var 1 ⬝ₒ X ⬝ₒ Y) σ' [boolT b, bl bs'] rfl
      generalize hσ2 : overrideC σ' [1, 2] [boolT b, bl bs'] = σ'' at hb2
      have e2 : (OTerm.var 1 ⬝ₒ X ⬝ₒ Y).close σ'' = σ'' 1 ⬝ X.close σ'' ⬝ Y.close σ'' := rfl
      have h1 : σ'' 1 = boolT b := by rw [← hσ2]; rfl
      have h2' : σ'' 2 = bl bs' := by rw [← hσ2]; rfl
      rw [e2, h1] at hb2
      have h3 := h2.trans (hb2.trans (Compose.boolT_sel b _ _))
      have hk' := (wsteps_K_iff h3).1 hk
      by_cases hbe : b = e
      · subst hbe
        have hX : (if b then X.close σ'' else Y.close σ'') = (chkL es).close σ'' ⬝ bl bs' := by
          cases b
          · show Y.close σ'' = _
            show (chkL es ⬝ₒ .var 2).close σ'' = _
            show (chkL es).close σ'' ⬝ σ'' 2 = _
            rw [h2']
          · show X.close σ'' = _
            show (chkL es ⬝ₒ .var 2).close σ'' = _
            show (chkL es).close σ'' ⬝ σ'' 2 = _
            rw [h2']
        rw [hX] at hk'
        rw [chkL_sound es σ'' bs' hk']
      · exfalso
        have hB : (if b then X.close σ'' else Y.close σ'') = thetaT ⬝ K := by
          cases b <;> cases e
          · exact absurd rfl hbe
          · exact close_badO _
          · exact close_badO _
          · exact absurd rfl hbe
        rw [hB] at hk'
        exact thetaK_not_K [] hk'

/-- **`CHECK_p` reaches `K` only on a cell headed by the atom `p`.** -/
theorem checkD_sound (p : Nat) (σ : Nat → Term) (o : Option Nn)
    (hk : WSteps ((checkD p).close σ ⬝ encO o) K) :
    ∃ d r, o = some (.cell (.atom d) r) ∧ d = bitsN p := by
  have hb := absN_beta_close [0]
    (.var 0 ⬝ₒ badO ⬝ₒ absN [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO) ⬝ₒ badO ⬝ₒ badO)
    σ [encO o] rfl
  generalize hσ : overrideC σ [0] [encO o] = σ' at hb
  have e1 : (OTerm.var 0 ⬝ₒ badO ⬝ₒ absN [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO) ⬝ₒ badO ⬝ₒ badO).close σ' =
      σ' 0 ⬝ badO.close σ' ⬝ (absN [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO)).close σ' ⬝
        badO.close σ' ⬝ badO.close σ' := rfl
  have h0 : σ' 0 = encO o := by rw [← hσ]; rfl
  rw [e1, close_badO, h0] at hb
  have hk' := (wsteps_K_iff hb).1 hk
  cases o with
  | none =>
    exfalso
    exact not_K_of_bad [] (errT_elim _ _ _ _) hk'
  | some s =>
    cases s with
    | atom b =>
      exfalso
      exact not_K_of_bad [bl b] (atomT_elim _ _ _ _ _) hk'
    | cell h t =>
      have h2 := (wsteps_K_iff (cellT_elim _ _ _ _ _ _)).1 hk'
      have hb2 := absN_beta_close [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO) σ' [encNn h, encNn t] rfl
      generalize hσ2 : overrideC σ' [1, 2] [encNn h, encNn t] = σ'' at hb2
      have e2 : (OTerm.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO).close σ'' =
          σ'' 1 ⬝ (chkL (bitsN p)).close σ'' ⬝ badO.close σ'' ⬝ badO.close σ'' ⬝ badO.close σ'' := rfl
      have h1 : σ'' 1 = encNn h := by rw [← hσ2]; rfl
      rw [e2, close_badO, h1] at hb2
      have h3 := (wsteps_K_iff hb2).1 h2
      cases h with
      | atom d =>
        have h4 := (wsteps_K_iff (atomT_elim _ _ _ _ _)).1 h3
        exact ⟨d, t, rfl, chkL_sound _ _ _ h4⟩
      | cell h1' t1' =>
        exfalso
        exact not_K_of_bad [encNn h1', encNn t1'] (cellT_elim _ _ _ _ _ _) h3

/-- The jet's variable closed to an implementation, any other to `K`. -/
def envD (P : Term) : Nat → Term := fun i => if i = JD then P else K

theorem env_J (P : Term) (a b : Term) : overrideC (envD P) [0, 1] [a, b] JD = P := by
  show (if JD = 1 then b else if JD = 0 then a else envD P JD) = P
  rw [if_neg (by decide), if_neg (by decide)]
  show (if JD = JD then P else K) = P
  rw [if_pos rfl]

/-- **The meaning of the verifier**: on the encoded subject `s`, it
    evaluates to `K`, with `J` closed to an implementation `P` of the `dec`
    contract, only if the subject's decrement is a cell headed by the atom
    `p`. -/
theorem decpre_meaning {p : Nat} {P : Term} (hP : DataJet.Implements decContract P) (s : Dom) (β : Term)
    (hev : WSteps ((verifierD p).close (envD P) ⬝ β ⬝ encNn s.1) K) :
    ∃ d r, decSpec s.1 = some (.cell (.atom d) r) ∧ val d = p := by
  have hb := absN_beta_close [0, 1] (checkD p ⬝ₒ (.var JD ⬝ₒ .var 1)) (envD P) [β, encNn s.1] rfl
  generalize hσ : overrideC (envD P) [0, 1] [β, encNn s.1] = σ at hb
  have hJ : σ JD = P := by rw [← hσ]; exact env_J _ _ _
  have h1 : σ 1 = encNn s.1 := by rw [← hσ]; rfl
  have e1 : (checkD p ⬝ₒ (.var JD ⬝ₒ .var 1)).close σ = (checkD p).close σ ⬝ (σ JD ⬝ σ 1) := rfl
  rw [e1, hJ, h1] at hb
  have hk1 := (wsteps_K_iff hb).1 hev
  have hP' := hP s
  rw [decContract_encI, decContract_encO, decContract_spec] at hP'
  have hk2 := (wsteps_K_iff (WSteps.right _ hP')).1 hk1
  obtain ⟨d, r, ho, rfl⟩ := checkD_sound p σ _ hk2
  exact ⟨_, r, ho, val_bitsN p⟩

/-- The same, from the composed statement's evaluation relation, the
    region's witness being the encoded subject. -/
theorem decpre_meaning_eval {p : Nat} {P : Term} (hP : DataJet.Implements decContract P) (s : Dom) {β : BT}
    (hev : EvalRel ((VsD p).map (·.close (envD P)), CompM.SameShape shpD) β (encNn s.1)) :
    ∃ d r, decSpec s.1 = some (.cell (.atom d) r) ∧ val d = p :=
  decpre_meaning hP s β.enc (eval_K_iff.1 (hev.2 _ (List.mem_singleton.2 rfl)))

-- ---------------------------------------------------------------------------
-- Completeness: the verifier accepts every subject whose decrement is `p`
-- ---------------------------------------------------------------------------

/-- **`chkL es` reaches `K` on the bits `es`.** -/
theorem chkL_complete : ∀ (es : List Bool) (σ : Nat → Term), WSteps ((chkL es).close σ ⬝ bl es) K
  | [], σ => by
    have hb := absN_beta_close [0] (.var 0 ⬝ₒ .K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ badO))) σ [bl []] rfl
    have e1 : (OTerm.var 0 ⬝ₒ .K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ badO))).close (overrideC σ [0] [bl []]) =
        bl [] ⬝ K ⬝ (K ⬝ (K ⬝ badO.close (overrideC σ [0] [bl []]))) := rfl
    rw [e1] at hb
    exact hb.trans (nil_elim _ _)
  | e :: es, σ => by
    let X : OTerm := if e then chkL es ⬝ₒ .var 2 else badO
    let Y : OTerm := if e then badO else chkL es ⬝ₒ .var 2
    have hb := absN_beta_close [0] (.var 0 ⬝ₒ badO ⬝ₒ absN [1, 2] (.var 1 ⬝ₒ X ⬝ₒ Y)) σ [bl (e :: es)] rfl
    generalize hσ : overrideC σ [0] [bl (e :: es)] = σ' at hb
    have e1 : (OTerm.var 0 ⬝ₒ badO ⬝ₒ absN [1, 2] (.var 1 ⬝ₒ X ⬝ₒ Y)).close σ' =
        σ' 0 ⬝ badO.close σ' ⬝ (absN [1, 2] (.var 1 ⬝ₒ X ⬝ₒ Y)).close σ' := rfl
    have h0 : σ' 0 = bl (e :: es) := by rw [← hσ]; rfl
    rw [e1, h0] at hb
    have h2 := hb.trans (cons_elim e es _ _)
    have hb2 := absN_beta_close [1, 2] (.var 1 ⬝ₒ X ⬝ₒ Y) σ' [boolT e, bl es] rfl
    generalize hσ2 : overrideC σ' [1, 2] [boolT e, bl es] = σ'' at hb2
    have e2 : (OTerm.var 1 ⬝ₒ X ⬝ₒ Y).close σ'' = σ'' 1 ⬝ X.close σ'' ⬝ Y.close σ'' := rfl
    have h1 : σ'' 1 = boolT e := by rw [← hσ2]; rfl
    have h2' : σ'' 2 = bl es := by rw [← hσ2]; rfl
    rw [e2, h1] at hb2
    have h3 := h2.trans (hb2.trans (Compose.boolT_sel e _ _))
    have hX : (if e then X.close σ'' else Y.close σ'') = (chkL es).close σ'' ⬝ bl es := by
      cases e
      · show (chkL es ⬝ₒ .var 2).close σ'' = _
        show (chkL es).close σ'' ⬝ σ'' 2 = _
        rw [h2']
      · show (chkL es ⬝ₒ .var 2).close σ'' = _
        show (chkL es).close σ'' ⬝ σ'' 2 = _
        rw [h2']
    rw [hX] at h3
    exact h3.trans (chkL_complete es σ'')

/-- **`CHECK_p` reaches `K` on a cell headed by the atom `p`.** -/
theorem checkD_complete (p : Nat) (σ : Nat → Term) (r : Nn) :
    WSteps ((checkD p).close σ ⬝ encO (some (.cell (.atom (bitsN p)) r))) K := by
  have hb := absN_beta_close [0]
    (.var 0 ⬝ₒ badO ⬝ₒ absN [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO) ⬝ₒ badO ⬝ₒ badO)
    σ [encO (some (.cell (.atom (bitsN p)) r))] rfl
  generalize hσ : overrideC σ [0] [encO (some (.cell (.atom (bitsN p)) r))] = σ' at hb
  have e1 : (OTerm.var 0 ⬝ₒ badO ⬝ₒ absN [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO) ⬝ₒ badO ⬝ₒ badO).close σ' =
      σ' 0 ⬝ badO.close σ' ⬝ (absN [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO)).close σ' ⬝
        badO.close σ' ⬝ badO.close σ' := rfl
  have h0 : σ' 0 = cellT (encNn (.atom (bitsN p))) (encNn r) := by rw [← hσ]; rfl
  rw [e1, h0] at hb
  have h2 := hb.trans (cellT_elim _ _ _ _ _ _)
  have hb2 := absN_beta_close [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO) σ'
    [encNn (.atom (bitsN p)), encNn r] rfl
  generalize hσ2 : overrideC σ' [1, 2] [encNn (.atom (bitsN p)), encNn r] = σ'' at hb2
  have e2 : (OTerm.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO).close σ'' =
      σ'' 1 ⬝ (chkL (bitsN p)).close σ'' ⬝ badO.close σ'' ⬝ badO.close σ'' ⬝ badO.close σ'' := rfl
  have h1 : σ'' 1 = atomT (bl (bitsN p)) := by rw [← hσ2]; rfl
  rw [e2, h1] at hb2
  exact h2.trans (hb2.trans ((atomT_elim _ _ _ _ _).trans (chkL_complete _ _)))

/-- The decrement of a well-formed subject is canonical. -/
theorem decSpec_canon {s : Nn} (hs : s.wf = true) {d : List Bool} {r : Nn}
    (h : decSpec s = some (.cell (.atom d) r)) : canonB d = true := by
  match s, hs, h with
  | .cell (.atom (b :: bs)) _, hs, h =>
    cases h
    have : canonB (b :: bs) = true := by
      simp only [Nn.wf, Bool.and_eq_true] at hs; exact hs.1
    exact decB_canon this

/-- **The verifier accepts**: on the encoded subject `s` whose decrement is
    a cell headed by the atom `p`, with `J` closed to any implementation of
    the contract, the verifier evaluates to `K`; the converse of
    `decpre_meaning`. -/
theorem decpre_complete {p : Nat} {P : Term} (hP : DataJet.Implements decContract P) (s : Dom)
    (hs : ∃ d r, decSpec s.1 = some (.cell (.atom d) r) ∧ val d = p) (β : Term) :
    WSteps ((verifierD p).close (envD P) ⬝ β ⬝ encNn s.1) K := by
  obtain ⟨d, r, hd, hv⟩ := hs
  have hdp : d = bitsN p :=
    canon_val_inj (decSpec_canon s.2.1 hd) (canonB_bitsN p) (by rw [hv, val_bitsN])
  have hb := absN_beta_close [0, 1] (checkD p ⬝ₒ (.var JD ⬝ₒ .var 1)) (envD P) [β, encNn s.1] rfl
  generalize hσ : overrideC (envD P) [0, 1] [β, encNn s.1] = σ at hb
  have hJ : σ JD = P := by rw [← hσ]; exact env_J _ _ _
  have h1 : σ 1 = encNn s.1 := by rw [← hσ]; rfl
  have e1 : (checkD p ⬝ₒ (.var JD ⬝ₒ .var 1)).close σ = (checkD p).close σ ⬝ (σ JD ⬝ σ 1) := rfl
  rw [e1, hJ, h1] at hb
  have hP' := hP s
  rw [decContract_encI, decContract_encO, decContract_spec, hd, hdp] at hP'
  exact hb.trans ((WSteps.right _ hP').trans (checkD_complete p σ r))

end DecPre
