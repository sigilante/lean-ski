import Ski.Circuit.CompDFinal

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

**`Circuit.decpreExport_sound`** composes it with the circuit's soundness:
an accepted proof of `decpre p` holds in its memory a subject in the jet's
domain whose decrement is a cell headed by the atom `p`.  The circuit
gives a run of the verifier on the bit and the region's witness that
head-reduces with the jet to `K` (`Circuit.compDExport_sound`); head
reduction is deterministic up to the jet, and the verifier head-reduces
to the jet applied to a reduct of the witness and `CHECK_p`'s
continuations (`verifier_spine`), so the run's first jet step fires there,
on a subject the memory holds (`first_jet`), and the rest of the run is
`CHECK_p` on its decrement (`decpre_hsteps`).
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

-- ---------------------------------------------------------------------------
-- The run's meaning: the jet fires on the witness's reduct, at the head
-- ---------------------------------------------------------------------------

namespace DecPre

open CompM Mach

theorem mem_false {x : Nat} : ∀ {t : OTerm}, ¬ Occ x t → t.mem x = false
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var y, h => by
    simp only [OTerm.mem, beq_eq_false_iff_ne]
    intro e; subst e; exact h (.var _)
  | .app f a, h => by
    simp only [OTerm.mem, Bool.or_eq_false_iff]
    exact ⟨mem_false (fun hf => h (.left _ hf)), mem_false (fun ha => h (.right _ ha))⟩

/-- The verifier's check of the head, once it is a cell's. -/
def chkX (p : Nat) : OTerm := absN [1, 2] (.var 1 ⬝ₒ chkL (bitsN p) ⬝ₒ badO ⬝ₒ badO ⬝ₒ badO)

theorem checkD_eq (p : Nat) : checkD p = absN [0] (.var 0 ⬝ₒ badO ⬝ₒ chkX p ⬝ₒ badO ⬝ₒ badO) := rfl

theorem chkX_closed (p x : Nat) : ¬ Occ x (chkX p) := fun h => by
  obtain ⟨h3, h4⟩ := Circuit.occ_absN [1, 2] h
  rcases Circuit.occ_app h3 with h3 | h3
  · rcases Circuit.occ_app h3 with h3 | h3
    · rcases Circuit.occ_app h3 with h3 | h3
      · rcases Circuit.occ_app h3 with h3 | h3
        · cases h3; exact h4 (by simp)
        · exact Circuit.chkL_closed _ x h3
      · exact Circuit.badD_closed x h3
    · exact Circuit.badD_closed x h3
  · exact Circuit.badD_closed x h3

/-- **The verifier reduces to the jet on the witness**, with `CHECK_p`'s
    continuations. -/
theorem verifier_spine (p : Nat) (β w : Term) :
    OWSteps (verifierD p ⬝ₒ β.toO ⬝ₒ w.toO) (appL (.var JD) [w.toO, badO, chkX p, badO, badO]) := by
  have h1 := absN_beta [0, 1] [β, w] (checkD p ⬝ₒ (.var JD ⬝ₒ .var 1)) ⟨by decide, by decide, trivial⟩ rfl
  have e1 : substL [0, 1] [β, w] (checkD p ⬝ₒ (.var JD ⬝ₒ .var 1)) = checkD p ⬝ₒ (.var JD ⬝ₒ w.toO) := by
    show ((checkD p ⬝ₒ (.var JD ⬝ₒ .var 1)).subst (single 0 β.toO)).subst (single 1 w.toO) = _
    show OTerm.app (((checkD p).subst (single 0 β.toO)).subst (single 1 w.toO))
      (OTerm.app ((single 0 β.toO JD).subst (single 1 w.toO)) ((single 0 β.toO 1).subst (single 1 w.toO))) = _
    rw [subst_single_of_not_mem (mem_false (Circuit.checkD_closed p 0)),
      subst_single_of_not_mem (mem_false (Circuit.checkD_closed p 1)),
      single_ne _ (by decide : JD ≠ 0), single_ne _ (by decide : 1 ≠ 0)]
    show OTerm.app (checkD p) (OTerm.app (single 1 w.toO JD) (single 1 w.toO 1)) = _
    rw [single_ne _ (by decide : JD ≠ 1), single_self]
  rw [e1] at h1
  have h2 := abs_beta 0 (.var JD ⬝ₒ w.toO) (.var 0 ⬝ₒ badO ⬝ₒ chkX p ⬝ₒ badO ⬝ₒ badO)
  have e2 : (OTerm.var 0 ⬝ₒ badO ⬝ₒ chkX p ⬝ₒ badO ⬝ₒ badO).subst (single 0 (.var JD ⬝ₒ w.toO)) =
      appL (.var JD) [w.toO, badO, chkX p, badO, badO] := by
    show OTerm.app (OTerm.app (OTerm.app (OTerm.app (single 0 (.var JD ⬝ₒ w.toO) 0)
      (badO.subst (single 0 (.var JD ⬝ₒ w.toO)))) ((chkX p).subst (single 0 (.var JD ⬝ₒ w.toO))))
      (badO.subst (single 0 (.var JD ⬝ₒ w.toO)))) (badO.subst (single 0 (.var JD ⬝ₒ w.toO))) = _
    rw [single_self, subst_single_of_not_mem (mem_false (Circuit.badD_closed 0)),
      subst_single_of_not_mem (mem_false (chkX_closed p 0))]
    rfl
  rw [e2] at h2
  exact h1.trans h2

-- The spine of a weak reduction to a variable-headed term (as
-- `Probe.owsteps_spine`, without its section's quotation table).

/-- Pairwise weak reduction of two lists of terms. -/
inductive AllW : List OTerm → List OTerm → Prop
  | nil : AllW [] []
  | cons {a b : OTerm} {as bs : List OTerm} : OWSteps a b → AllW as bs → AllW (a :: as) (b :: bs)

theorem AllW.refl : ∀ (as : List OTerm), AllW as as
  | [] => .nil
  | a :: as => .cons (.refl a) (AllW.refl as)

theorem AllW.trans : ∀ {as bs cs : List OTerm}, AllW as bs → AllW bs cs → AllW as cs
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2 => .cons (h1.trans h2) (AllW.trans t1 t2)

theorem AllW.snoc : ∀ {as bs : List OTerm} {a b : OTerm}, AllW as bs → OWSteps a b →
    AllW (as ++ [a]) (bs ++ [b])
  | [], [], _, _, .nil, h => .cons h .nil
  | _ :: _, _ :: _, _, _, .cons h1 t1, h => .cons h1 (AllW.snoc t1 h)

theorem oparI_spineN {c : Nat} (n : Nat) : ∀ (fs : List OTerm) {w : OTerm}, fs.length = n →
    OParI w (appL (.var c) fs) → ∃ fs', w = appL (.var c) fs' ∧ AllW fs' fs := by
  induction n with
  | zero =>
    intro fs w hl h
    rw [List.length_eq_zero_iff] at hl
    subst hl
    cases h
    exact ⟨[], rfl, .nil⟩
  | succ n ih =>
    intro fs w hl h
    have hne : fs ≠ [] := by intro e; subst e; cases hl
    rw [← List.dropLast_concat_getLast hne, appL_snoc] at h
    cases h with
    | app h1 hx =>
      obtain ⟨fs', e, hall⟩ := ih fs.dropLast (by rw [List.length_dropLast, hl]; rfl) h1
      subst e
      refine ⟨fs' ++ [_], by rw [appL_snoc], ?_⟩
      have := hall.snoc hx.wsteps
      rw [List.dropLast_concat_getLast hne] at this
      exact this

theorem oparIs_spine {c : Nat} {w v : OTerm} (h : OParIs w v) :
    ∀ {fs : List OTerm}, v = appL (.var c) fs → ∃ fs', w = appL (.var c) fs' ∧ AllW fs' fs := by
  induction h with
  | refl _ => exact fun e => ⟨_, e, AllW.refl _⟩
  | step h _ ih =>
    intro fs e
    obtain ⟨fs1, e1, h1⟩ := ih e
    subst e1
    obtain ⟨fs0, e0, h0⟩ := oparI_spineN fs1.length fs1 rfl h
    exact ⟨fs0, e0, h0.trans h1⟩

theorem owsteps_spineD {t : OTerm} {c : Nat} {fs : List OTerm} (h : OWSteps t (appL (.var c) fs)) :
    ∃ fs', OSteps t (appL (.var c) fs') ∧ AllW fs' fs := by
  obtain ⟨t', h1, h2⟩ := owsteps_split h
  obtain ⟨fs', e, hall⟩ := oparIs_spine h2 rfl
  exact ⟨fs', e ▸ h1, hall⟩

/-- An open term's arguments. -/
def oargs : OTerm → List OTerm
  | .app f x => oargs f ++ [x]
  | _ => []

theorem oargs_appL : ∀ (l : List OTerm) (f : OTerm), oargs (appL f l) = oargs f ++ l
  | [], _ => by simp [appL]
  | x :: l, f => by rw [show appL f (x :: l) = appL (f ⬝ₒ x) l from rfl, oargs_appL l]; simp [oargs]

theorem appL_var_inj {c : Nat} {l₁ l₂ : List OTerm} (h : appL (.var c) l₁ = appL (.var c) l₂) : l₁ = l₂ := by
  have := congrArg oargs h
  rw [oargs_appL, oargs_appL] at this
  simpa [oargs] using this

theorem osteps_of_neutral {t u : OTerm} (hn : ONeutral t) (h : OSteps t u) : u = t := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hn.no_step hs).elim

/-- **The first jet step is where head reduction stops**: a run to `K`
    from a term whose head reduction reaches a neutral term `n` fires the
    jet at `n`. -/
theorem first_jet {A : Dom → Prop} {J : Nat} : ∀ {t u : OTerm}, HSteps A J t u → u = .K →
    ∀ {n : OTerm}, OSteps t n → ONeutral n →
      ∃ s R, A s ∧ n = appL (.var J) ((encNn s.1).toO :: R) ∧ HSteps A J (appL (encO (decSpec s.1)).toO R) .K := by
  intro t u h
  induction h with
  | refl t =>
    intro hu n hn nn
    subst hu
    rw [osteps_of_neutral nn (by
      cases hn with
      | refl => exact .refl _
      | step hs _ => cases hs) |>.symm] at nn
    · cases nn
  | step hs hrest ih =>
    intro hu n hn nn
    cases hs with
    | head hst =>
      cases hn with
      | refl => exact (nn.no_step hst).elim
      | step h1 h2 =>
        rw [OStep.det h1 hst] at h2
        exact ih hu h2 nn
    | jet s hA R =>
      have hnt := osteps_of_neutral (ONeutral.appL _ (.var J)) hn
      subst hnt
      subst hu
      exact ⟨s, R, hA, rfl, hrest⟩

/-- **Closing the run** to an implementation of the contract. -/
theorem HSteps.close {A : Dom → Prop} {J : Nat} (σ : Nat → Term) (hσ : DataJet.Implements decContract (σ J))
    {t u : OTerm} (h : HSteps A J t u) : WSteps (t.close σ) (u.close σ) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih =>
    refine WSteps.trans ?_ ih
    cases hs with
    | head hst => exact .single (OStep.close σ hst).weak
    | jet s _ R =>
      rw [_root_.close_appL, _root_.close_appL]
      show WSteps (appT (σ J ⬝ (encNn s.1).toO.close σ) _) _
      rw [close_toO, close_toO]
      exact appT_left (hσ s) _

theorem allW_appT (σ : Nat → Term) : ∀ {l₁ l₂ : List OTerm}, AllW l₁ l₂ → ∀ (E : Term),
    WSteps (appT E (l₁.map (OTerm.close σ))) (appT E (l₂.map (OTerm.close σ)))
  | [], [], .nil, _ => .refl _
  | _ :: _, _ :: _, .cons h t, E => by
    show WSteps (appT (E ⬝ _) _) (appT (E ⬝ _) _)
    exact (appT_left (WSteps.right E (h.close σ)) _).trans (allW_appT σ t _)

/-- **What a run of the verifier of `decpre p` means**: its head reduction
    with the jet reaches `K` only if a subject the jet took has a decrement
    that is a cell headed by the atom `p`. -/
theorem decpre_hsteps {p : Nat} {P : Term} (hP : DataJet.Implements decContract P) {A : Dom → Prop} {β w : Term}
    (h : HSteps A JD (verifierD p ⬝ₒ β.toO ⬝ₒ w.toO) .K) :
    ∃ s, A s ∧ ∃ d r, decSpec s.1 = some (.cell (.atom d) r) ∧ val d = p := by
  obtain ⟨fs', h1, hall⟩ := owsteps_spineD (verifier_spine p β w)
  obtain ⟨s, R, hA, hn, hrest⟩ := first_jet h rfl h1 (ONeutral.appL _ (.var _))
  have e := appL_var_inj hn
  subst e
  cases hall with
  | cons _ hR =>
  refine ⟨s, hA, ?_⟩
  let σ := envD P
  have hJ : σ JD = P := by show (if JD = JD then P else K) = P; rw [if_pos rfl]
  have hc := HSteps.close σ (by rw [hJ]; exact hP) hrest
  rw [_root_.close_appL, close_toO] at hc
  have hc2 := (wsteps_K_iff (allW_appT σ hR (encO (decSpec s.1)))).1 hc
  have hb := absN_beta_close [0] (.var 0 ⬝ₒ badO ⬝ₒ chkX p ⬝ₒ badO ⬝ₒ badO) σ [encO (decSpec s.1)] rfl
  rw [← checkD_eq] at hb
  have e3 : (OTerm.var 0 ⬝ₒ badO ⬝ₒ chkX p ⬝ₒ badO ⬝ₒ badO).close (overrideC σ [0] [encO (decSpec s.1)]) =
      appT (encO (decSpec s.1)) ([badO, chkX p, badO, badO].map (OTerm.close σ)) := by
    show encO (decSpec s.1) ⬝ badO.close _ ⬝ (chkX p).close _ ⬝ badO.close _ ⬝ badO.close _ =
      encO (decSpec s.1) ⬝ badO.close σ ⬝ (chkX p).close σ ⬝ badO.close σ ⬝ badO.close σ
    rw [close_badO, close_badO, close_agree (fun i hi => absurd hi (chkX_closed p i))]
  rw [e3] at hb
  have hk := (wsteps_K_iff hb).2 hc2
  obtain ⟨d, r, ho, hd⟩ := checkD_sound p σ _ hk
  exact ⟨d, r, ho, by rw [hd, val_bitsN]⟩

end DecPre

namespace Circuit

open Air

/-- **Soundness of `decpre p`**: an accepted proof of the statement, for
    AIRs with the normal forms of `compDAirs p W`, holds in its memory a
    subject in the jet's domain whose decrement, under any implementation
    of the contract (skinock's `jetT decF`), is a cell headed by the atom
    `p`. -/
theorem decpreExport_sound {p W : Nat} {P : Term} (hP : DataJet.Implements DecJet.decContract P)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirs p W) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧
      ∃ (s : DecJet.Dom) (root : Nat), Mach.otermAt (memOf Mm) (memOf Mm).length root = some (DecJet.encNn s.1).toO ∧
        ∃ d r, DecJet.decSpec s.1 = some (.cell (.atom d) r) ∧ BitArith.val d = p := by
  obtain ⟨C, Mm, Pg, Wt, Sg, D, rfl, w, _, hrun⟩ := compDExport_sound hs hacc
  obtain ⟨s, ⟨root, hroot⟩, hd⟩ := DecPre.decpre_hsteps hP hrun
  exact ⟨C, Mm, Pg, Wt, Sg, D, rfl, s, root, hroot, hd⟩

end Circuit
