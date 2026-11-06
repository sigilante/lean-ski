import Ski.Univ

open Term

/-!
# A CL-definable Kleene tree

Component 4 of `notes/mech-kleene.md`.  This module discharges the hypothesis
`CantorTotal.Kleene` of `CantorTotal.no_lift_cantor_total`, so that there is no
lift at Cantor space under totality on the definable streams, unconditionally
(`no_lift_cantor_total'`).

For each `e`, let `P e = dec e ⬝ num e ⬝ K ⬝ (K ⬝ I)`, the term numbered `e`
applied to its own number, then read as a boolean.  `verdict N e` is what `P e`
reaches within `N` head steps: `some true` at `K`, `some false` at `K ⬝ x`, and
`none` otherwise or out of steps.  A word `w` is in the tree `T` iff
`verdict |w| e ≠ some w[e]` for every `e < |w|`.  This is the diagonal: every
infinite path disagrees, somewhere, with every definable function total on the
numerals.

- `closed`: a verdict found with less fuel stands with more (`Univ.bnd_mono_le`).
- `infinite`: choose each bit against its verdict.
- `noPath`: a definable stream `s` gives the term `nthT ⬝ s`, which is numbered
  (`Univ.dec_surj`).  At its own number its run converges to `s`'s bit there, so
  every long enough prefix of `s` leaves `T`.
- `decides`: the closed term `tauT` computes membership on a stream's prefixes,
  from `Univ.evalC_spec`, `Univ.decC_num` and `Univ.liftN_spec`.
-/

namespace KleeneTree

open NoLift LiftBool Search CantorLift CantorTotal Univ NatFan Requote

-- ---------------------------------------------------------------------------
-- The tree, in Lean
-- ---------------------------------------------------------------------------

/-- The diagonal test term. -/
def P (e : Nat) : Term := dec e ⬝ num e ⬝ K ⬝ (K ⬝ I)

/-- Reading a whnf as a boolean. -/
def classify : Option Term → Option Bool
  | some .K => some true
  | some (.app .K _) => some false
  | _ => none

def verdict (N e : Nat) : Option Bool := classify (bnd N (P e))

/-- `e`'s check passes for the bit `b` at fuel `N`. -/
def okB (N e : Nat) (b : Bool) : Bool := !(verdict N e == some b)

/-- All checks below `k`, at fuel `N`, for the bits `f`. -/
def allOk (N : Nat) (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => okB N k (f k) && allOk N f k

def T (w : List Bool) : Bool := allOk w.length (fun e => w.getD e false) w.length

theorem allOk_iff (N : Nat) (f : Nat → Bool) : ∀ k, allOk N f k = true ↔ ∀ e, e < k → verdict N e ≠ some (f e)
  | 0 => by simp [allOk]
  | k + 1 => by
    rw [allOk, Bool.and_eq_true, allOk_iff N f k]
    constructor
    · rintro ⟨h1, h2⟩ e he
      by_cases hek : e = k
      · subst hek; simpa [okB] using h1
      · exact h2 e (by omega)
    · intro h
      refine ⟨?_, fun e he => h e (by omega)⟩
      simpa [okB] using h k (by omega)

theorem allOk_congr (N : Nat) {f g : Nat → Bool} : ∀ k, (∀ e, e < k → f e = g e) → allOk N f k = allOk N g k
  | 0, _ => rfl
  | k + 1, h => by rw [allOk, allOk, h k (by omega), allOk_congr N k fun e he => h e (by omega)]

theorem pre_length : ∀ (bits : Nat → Bool) n, (CantorTotal.pre bits n).length = n
  | _, 0 => rfl
  | bits, n + 1 => by simp [CantorTotal.pre, pre_length _ n]

theorem pre_getD : ∀ (bits : Nat → Bool) n e, e < n → (CantorTotal.pre bits n).getD e false = bits e
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | bits, n + 1, 0, _ => by simp [CantorTotal.pre]
  | bits, n + 1, e + 1, h => by
    simp only [CantorTotal.pre, List.getD_cons_succ]
    exact pre_getD (fun i => bits (i + 1)) n e (by omega)

theorem T_pre (bits : Nat → Bool) (n : Nat) : T (pre bits n) = allOk n bits n := by
  rw [T, pre_length]
  exact allOk_congr n n fun e he => pre_getD bits n e he

-- ---------------------------------------------------------------------------
-- The three tree properties
-- ---------------------------------------------------------------------------

theorem verdict_mono {N M e : Nat} (h : N ≤ M) {b : Bool} (hv : verdict N e = some b) :
    verdict M e = some b := by
  unfold verdict at hv ⊢
  cases hb : bnd N (P e) with
  | none => rw [hb] at hv; simp [classify] at hv
  | some v => rw [bnd_mono_le h hb]; rw [hb] at hv; exact hv

theorem T_closed (w v : List Bool) (h : T (w ++ v) = true) : T w = true := by
  rw [T, allOk_iff] at h ⊢
  intro e he hv
  have hv' := verdict_mono (M := (w ++ v).length) (by simp) hv
  have hget : (w ++ v).getD e false = w.getD e false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left he]
  exact h e (by simp; omega) (by rw [hget]; exact hv')

theorem T_infinite (k : Nat) : ∃ w : List Bool, w.length = k ∧ T w = true := by
  let w := (List.range k).map fun e => match verdict k e with
    | some b => !b
    | none => false
  refine ⟨w, by simp [w], ?_⟩
  rw [T, allOk_iff]
  intro e he
  have hl : w.length = k := by simp [w]
  rw [hl] at he ⊢
  have hg : w.getD e false = (match verdict k e with | some b => !b | none => false) := by
    simp [w, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]
  rw [hg]
  cases verdict k e with
  | none => simp
  | some b => cases b <;> simp

/-- A whnf that reduces to a boolean is classified as that boolean. -/
theorem classify_whnf {v : Term} {b : Bool} (hv : Whnf v) (h : WSteps v (boolT b)) :
    classify (some v) = some b := by
  cases b with
  | true => rw [hv.wsteps_K h]; rfl
  | false =>
    obtain ⟨x, rfl, _⟩ := whnf_to_KI hv h
    rfl

theorem T_noPath (bits : Nat → Bool) (s : Term) (hs : IsStream bits s) : ∃ N, T (pre bits N) = false := by
  obtain ⟨e, he⟩ := dec_surj (nthT ⬝ s)
  have hlt : e < (CantorTotal.pre bits (e + 1)).length := by rw [pre_length]; omega
  have hget : (CantorTotal.pre bits (e + 1)).get ⟨e, hlt⟩ = bits e := by
    have := pre_getD bits (e + 1) e (by omega)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at this
    simpa using this
  have hbit : WSteps (nthT ⬝ s ⬝ num e) (boolT (bits e)) := by
    have h0 := nth_spec (CantorTotal.pre bits (e + 1)) s e hlt (hs (e + 1))
    rw [hget] at h0
    exact h0
  have hP : WSteps (P e) (boolT (bits e)) := by
    unfold P; rw [he]
    exact (WSteps.left _ (WSteps.left _ hbit)).trans (by cases bits e <;> exact sel _ _ _)
  obtain ⟨n0, v, hrun, hv, hvb⟩ := head_run hP
  have hverd : ∀ N, n0 ≤ N → verdict N e = some (bits e) := fun N hN => by
    unfold verdict; rw [bnd_of_run n0 hrun hv N hN]; exact classify_whnf hv hvb
  refine ⟨max n0 (e + 1), ?_⟩
  rw [T_pre]
  cases h : allOk (max n0 (e + 1)) bits (max n0 (e + 1)) with
  | false => rfl
  | true =>
    exact absurd (hverd _ (by omega)) ((allOk_iff _ _ _).1 h e (by omega))

-- ---------------------------------------------------------------------------
-- The tree, as a closed term on stream prefixes
-- ---------------------------------------------------------------------------

/-- `codeP e = App (App (App (dec e) (lift e)) ⟨K⟩) ⟨K I⟩`, the code of `P e`. -/
def codePC : Term :=
  toTerm (absN [0] (Requote.appC.toO ⬝ₒ (Requote.appC.toO ⬝ₒ (Requote.appC.toO ⬝ₒ (decC.toO ⬝ₒ .var 0)
    ⬝ₒ (liftN.toO ⬝ₒ .var 0)) ⬝ₒ (quoteT K).toO) ⬝ₒ (quoteT (K ⬝ I)).toO))

theorem codePC_spec (e : Nat) : WSteps (codePC ⬝ num e) (quoteT (P e)) := by
  have h := absN_beta_close [0] (Requote.appC.toO ⬝ₒ (Requote.appC.toO ⬝ₒ (Requote.appC.toO ⬝ₒ (decC.toO ⬝ₒ .var 0)
    ⬝ₒ (liftN.toO ⬝ₒ .var 0)) ⬝ₒ (quoteT K).toO) ⬝ₒ (quoteT (K ⬝ I)).toO) (fun _ => K) [num e] rfl
  simp only [OTerm.close, close_toO, appT] at h
  refine h.trans ?_
  exact WSteps.left _ (WSteps.right _ (WSteps.left _ (WSteps.right _
    (WSteps.app (WSteps.right _ (decC_num e)) (liftN_spec e)))))

/-- `checkWith b c = c true (not b) true (λ f x. f true b true (λ _ _. true))`,
    over `b` (0), `c` (1), `f` (2), `x` (3), and `4`, `5`. -/
def cwIn : OTerm := absN [2, 3] (.var 2 ⬝ₒ .K ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ absN [4, 5] .K)
def checkWith : Term := toTerm (absN [0, 1] (.var 1 ⬝ₒ .K ⬝ₒ (notT.toO ⬝ₒ .var 0) ⬝ₒ .K ⬝ₒ cwIn))

theorem checkWith_spec (b : Bool) (v : Term) :
    WSteps (checkWith ⬝ boolT b ⬝ quoteT v) (boolT (!(classify (some v) == some b))) := by
  have h := absN_beta_close [0, 1] (.var 1 ⬝ₒ .K ⬝ₒ (notT.toO ⬝ₒ .var 0) ⬝ₒ .K ⬝ₒ cwIn) (fun _ => K)
    [boolT b, quoteT v] rfl
  simp only [OTerm.close, close_toO, appT] at h
  refine h.trans ?_
  let σ := overrideC (fun _ => K) [0, 1] [boolT b, quoteT v]
  have inner : ∀ f x, WSteps (cwIn.close σ ⬝ f ⬝ x) (f ⬝ K ⬝ boolT b ⬝ K ⬝ (absN [4, 5] OTerm.K).close
      (overrideC σ [2, 3] [f, x])) := fun f x => by
    have h2 := absN_beta_close [2, 3] (.var 2 ⬝ₒ .K ⬝ₒ .var 0 ⬝ₒ .K ⬝ₒ absN [4, 5] .K) σ [f, x] rfl
    simp only [OTerm.close, appT] at h2
    exact h2
  have k45 : ∀ σ' a c, WSteps ((absN [4, 5] OTerm.K).close σ' ⬝ a ⬝ c) K := fun σ' a c => by
    have h3 := absN_beta_close [4, 5] OTerm.K σ' [a, c] rfl
    simp only [OTerm.close, appT] at h3
    exact h3
  cases v with
  | S =>
    rw [show (!(classify (some S) == some b)) = true by simp [classify]]
    exact quoteS_elim _ _ _ _
  | K =>
    rw [show (!(classify (some K) == some b)) = !b by cases b <;> simp [classify]]
    exact (quoteK_elim _ _ _ _).trans (not_spec b)
  | I =>
    rw [show (!(classify (some I) == some b)) = true by simp [classify]]
    exact quoteI_elim _ _ _ _
  | app f x =>
    refine (quoteApp_elim f x _ _ _ _).trans ((inner _ _).trans ?_)
    cases f with
    | S =>
      rw [show (!(classify (some (S ⬝ x)) == some b)) = true by simp [classify]]
      exact quoteS_elim _ _ _ _
    | K =>
      rw [show (!(classify (some (K ⬝ x)) == some b)) = b by cases b <;> simp [classify]]
      exact quoteK_elim _ _ _ _
    | I =>
      rw [show (!(classify (some (I ⬝ x)) == some b)) = true by simp [classify]]
      exact quoteI_elim _ _ _ _
    | app g y =>
      rw [show (!(classify (some (g ⬝ y ⬝ x)) == some b)) = true by simp [classify]]
      exact (quoteApp_elim g y _ _ _ _).trans (k45 _ _ _)

/-- `checkC N e b = evalC N (codeP e) true (checkWith b)`. -/
def checkC : Term :=
  toTerm (absN [0, 1, 2] (evalC.toO ⬝ₒ .var 0 ⬝ₒ (codePC.toO ⬝ₒ .var 1) ⬝ₒ .K ⬝ₒ (checkWith.toO ⬝ₒ .var 2)))

theorem checkC_spec (N e : Nat) (b : Bool) : WSteps (checkC ⬝ num N ⬝ num e ⬝ boolT b) (boolT (okB N e b)) := by
  have h := absN_beta_close [0, 1, 2]
    (evalC.toO ⬝ₒ .var 0 ⬝ₒ (codePC.toO ⬝ₒ .var 1) ⬝ₒ .K ⬝ₒ (checkWith.toO ⬝ₒ .var 2)) (fun _ => K)
    [num N, num e, boolT b] rfl
  simp only [OTerm.close, close_toO, appT] at h
  refine (h.trans (WSteps.left _ (WSteps.left _ ((WSteps.right _ (codePC_spec e)).trans (evalC_spec N (P e)))))).trans ?_
  unfold okB verdict
  cases hb : bnd N (P e) with
  | none => simpa [mcode, classify, boolT] using nothing_sel _ _
  | some v => exact (just_sel _ _ _).trans (checkWith_spec b v)

/-- `go N s k = k true (λ k'. checkC N k' (nth s k') (go N s k') false)`,
    over `r` (0), `N` (1), `s` (2), `k` (3), `k'` (4). -/
def goBody : OTerm :=
  .var 3 ⬝ₒ .K ⬝ₒ absN [4] (checkC.toO ⬝ₒ .var 1 ⬝ₒ .var 4 ⬝ₒ (nthT.toO ⬝ₒ .var 2 ⬝ₒ .var 4)
    ⬝ₒ (.var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 4) ⬝ₒ (K ⬝ I).toO)
def goStepK : Term := toTerm (absN [0, 1, 2, 3] goBody)
def goK : Term := fixSelf goStepK (fixB goStepK)

theorem goK_unroll : WSteps goK (goStepK ⬝ goK) := by
  have h := (fixSelf_unroll (F := goStepK) (Steps.refl (fixB goStepK))).weak
  have hI : WSteps (fixSelf goStepK (I ⬝ fixB goStepK)) goK := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem goK_case (Nt s k : Term) : ∃ X, WSteps (goK ⬝ Nt ⬝ s ⬝ k) (k ⬝ K ⬝ X) ∧
    ∀ k', WSteps (X ⬝ k') (checkC ⬝ Nt ⬝ k' ⬝ (nthT ⬝ s ⬝ k') ⬝ (goK ⬝ Nt ⬝ s ⬝ k') ⬝ (K ⬝ I)) := by
  have h := absN_beta_close [0, 1, 2, 3] goBody (fun _ => K) [goK, Nt, s, k] rfl
  simp only [goBody, OTerm.close, close_toO, appT] at h
  refine ⟨_, (WSteps.left _ (WSteps.left _ (WSteps.left _ goK_unroll))).trans h, fun k' => ?_⟩
  have h2 := absN_beta_close [4] (checkC.toO ⬝ₒ .var 1 ⬝ₒ .var 4 ⬝ₒ (nthT.toO ⬝ₒ .var 2 ⬝ₒ .var 4)
    ⬝ₒ (.var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 4) ⬝ₒ (K ⬝ I).toO)
    (overrideC (fun _ => K) [0, 1, 2, 3] [goK, Nt, s, k]) [k'] rfl
  simp only [OTerm.close, close_toO, appT] at h2
  exact h2

theorem nth_stream {bits : Nat → Bool} {s : Term} (hs : IsStream bits s) (e : Nat) :
    WSteps (nthT ⬝ s ⬝ num e) (boolT (bits e)) := by
  have hlt : e < (CantorTotal.pre bits (e + 1)).length := by rw [pre_length]; omega
  have hget : (CantorTotal.pre bits (e + 1)).get ⟨e, hlt⟩ = bits e := by
    have := pre_getD bits (e + 1) e (by omega)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at this
    simpa using this
  have h0 := nth_spec (CantorTotal.pre bits (e + 1)) s e hlt (hs (e + 1))
  rw [hget] at h0
  exact h0

theorem goK_spec {bits : Nat → Bool} {s : Term} (hs : IsStream bits s) (N : Nat) :
    ∀ k, WSteps (goK ⬝ num N ⬝ s ⬝ num k) (boolT (allOk N bits k))
  | 0 => by
    obtain ⟨X, hX, _⟩ := goK_case (num N) s (num 0)
    exact hX.trans (.single (.K _ _))
  | k + 1 => by
    obtain ⟨X, hX, hXs⟩ := goK_case (num N) s (num (k + 1))
    refine (hX.trans ((succS_wsteps (num k) _ X).trans (hXs _))).trans ?_
    have hc := (WSteps.right _ (nth_stream hs k)).trans (checkC_spec N k (bits k))
    refine (WSteps.left _ (WSteps.left _ hc)).trans ((WSteps.left _ (WSteps.right _ (goK_spec hs N k))).trans ?_)
    refine (and_wsteps _ _).trans ?_
    cases h : okB N k (bits k)
    · simp only [allOk, h, Bool.false_and, Bool.false_eq_true, if_false, boolT]; exact .refl _
    · simp only [allOk, h, Bool.true_and, if_true]; exact .refl _

/-- **`τ s n = go n s n`**: membership of a stream's prefix of length `n`. -/
def tauT : Term := toTerm (absN [0, 1] (goK.toO ⬝ₒ .var 1 ⬝ₒ .var 0 ⬝ₒ .var 1))

theorem tau_decides : Decides tauT T := by
  intro bits s hs n
  have h := absN_beta_close [0, 1] (goK.toO ⬝ₒ .var 1 ⬝ₒ .var 0 ⬝ₒ .var 1) (fun _ => K) [s, num n] rfl
  simp only [OTerm.close, close_toO, appT] at h
  rw [T_pre]
  exact h.trans (goK_spec hs n n)

-- ---------------------------------------------------------------------------
-- The Kleene tree, and the unconditional theorem
-- ---------------------------------------------------------------------------

/-- **A CL-definable Kleene tree.** -/
theorem kleene : Kleene tauT T where
  decides := tau_decides
  closed := T_closed
  infinite := T_infinite
  noPath := T_noPath

/-- **No lift at Cantor space under totality alone**, unconditionally: no closed
    term lifts every functional total on the definable streams. -/
theorem no_lift_cantor_total' (L : Term) : ¬ ∀ f, TotalS f → LiftsOn Streams L f :=
  fun hL => no_lift_cantor_total kleene L hL

end KleeneTree
