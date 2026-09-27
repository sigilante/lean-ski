import Ski.Fuel
open Term

/-!
# Execution-trace certificates

A run's witness is the list of terms it visited.  `certified t ts u` checks,
by re-running `step?` on each consecutive pair, that `ts` is the contraction
sequence from `t` to `u`; `certified_sound` is the theorem a verifier relies
on and `certified_complete` says every reduction has such a certificate.
`traceF` produces the certificate the fuel interpreter itself took: one row
per contraction, each row checked by the same three rules.

A proof system hides a trace's contents but not its length, and the number
of contractions depends on the witness.  So the certificate a prover
commits to is **budget-exact** (`certifiedPad`): exactly `k` rows for a
public budget `k`, one per contraction while a head redex exists and then
one per repeated no-redex check.  `certified_pad_iff` says such a
certificate exists exactly when the fuelled interpreter at `k` returns the
value; `certifiedPad_unique` that it is unique; `certified_pad_budgets` that
a run of `s` contractions is certified at exactly the budgets `k ≥ s + 1`.
-/

/-- `ts` is the sequence of terms strictly between `t` and `u`. -/
def certified : Term → List Term → Term → Bool
  | t, [], u => t == u
  | t, t' :: ts, u => step? t == some t' && certified t' ts u

theorem certified_sound : ∀ {ts : List Term} {t u : Term},
    certified t ts u = true → Steps t u
  | [], t, u, h => by
    simp only [certified, beq_iff_eq] at h
    subst h
    exact .refl t
  | t' :: ts, t, u, h => by
    simp only [certified, Bool.and_eq_true, beq_iff_eq] at h
    exact .step (step?_sound h.1) (certified_sound h.2)

theorem certified_complete {t u : Term} (h : Steps t u) :
    ∃ ts, certified t ts u = true := by
  induction h with
  | refl t => exact ⟨[], by simp [certified]⟩
  | @step t t' u h _ ih =>
    obtain ⟨ts, hts⟩ := ih
    exact ⟨t' :: ts, by simp [certified, step?_complete h, hts]⟩

/-- The certificate the fuel interpreter produces: the intermediate terms and
    the final weak head normal form. -/
def traceF : Nat → Term → Option (List Term × Term)
  | 0, _ => none
  | k + 1, t =>
    match step? t with
    | none => some ([], t)
    | some t' => (traceF k t').map (fun p => (t' :: p.1, p.2))

theorem traceF_certified : ∀ {k : Nat} {t : Term} {ts : List Term} {u : Term},
    traceF k t = some (ts, u) → certified t ts u = true ∧ Whnf u
  | 0, _, _, _, h => by simp [traceF] at h
  | k + 1, t, ts, u, h => by
    cases hs : step? t with
    | none =>
      simp only [traceF, hs] at h
      cases h
      exact ⟨by simp [certified], step?_none hs⟩
    | some t' =>
      simp only [traceF, hs] at h
      cases hr : traceF k t' with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨ps, pu⟩ := p
        simp only [hr, Option.map] at h
        cases h
        have ⟨hc, hw⟩ := traceF_certified hr
        exact ⟨by simp [certified, hs, hc], hw⟩

-- ---------------------------------------------------------------------------
-- Budget-exact certificates
-- ---------------------------------------------------------------------------

/-- One row of a budget-exact trace: contract the head redex, or, at a weak
    head normal form, stay. -/
def padStep (t : Term) : Term := (step? t).getD t

theorem padStep_of_some {t t' : Term} (h : step? t = some t') : padStep t = t' := by
  unfold padStep; rw [h]; rfl

theorem padStep_of_none {t : Term} (h : step? t = none) : padStep t = t := by
  unfold padStep; rw [h]; rfl

/-- **A budget-exact certificate.**  `ts` is the state after every row but
    the last, and the last row checks that `u` has no redex, so the
    certificate has `ts.length + 1` rows.  While a head redex exists a row
    contracts it; afterwards a row repeats the no-redex check, which leaves
    the term unchanged.  The number of rows is the public budget and says
    nothing of how many contractions there were. -/
def certifiedPad : Term → List Term → Term → Bool
  | t, [], u => t == u && (step? t).isNone
  | t, t' :: ts, u => padStep t == t' && certifiedPad t' ts u

/-- At a weak head normal form, any number of check rows. -/
theorem certifiedPad_stutter {t : Term} (h : step? t = none) :
    ∀ n, certifiedPad t (List.replicate n t) t = true
  | 0 => by
    show (t == t && (step? t).isNone) = true
    rw [h, beq_self_eq_true']; rfl
  | n + 1 => by
    show (padStep t == t && certifiedPad t (List.replicate n t) t) = true
    rw [padStep_of_none h, certifiedPad_stutter h n, beq_self_eq_true']; rfl

theorem evalF_pad : ∀ {ts : List Term} {t u : Term},
    certifiedPad t ts u = true → evalF (ts.length + 1) t = some u
  | [], t, u, h => by
    have h' : (t == u && (step? t).isNone) = true := h
    rw [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨htu, hn⟩ := h'
    subst htu
    have hn : step? t = none := Option.isNone_iff_eq_none.mp hn
    show (match step? t with | none => some t | some t' => evalF 0 t') = some t
    rw [hn]
  | t' :: ts, t, u, h => by
    have h' : (padStep t == t' && certifiedPad t' ts u) = true := h
    rw [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨hp, hc⟩ := h'
    have ih := evalF_pad hc
    show (match step? t with | none => some t | some t'' => evalF (ts.length + 1) t'') = some u
    cases hs : step? t with
    | some t'' =>
      rw [padStep_of_some hs] at hp
      subst hp
      exact ih
    | none =>
      rw [padStep_of_none hs] at hp
      subst hp
      have e : evalF (ts.length + 1) t = some t := by
        show (match step? t with | none => some t | some t'' => evalF ts.length t'') = some t
        rw [hs]
      rw [e] at ih
      exact ih

theorem pad_of_evalF : ∀ {k : Nat} {t u : Term}, evalF k t = some u →
    ∃ ts, ts.length + 1 = k ∧ certifiedPad t ts u = true
  | 0, _, _, h => by cases h
  | k + 1, t, u, h => by
    have h' : (match step? t with | none => some t | some t' => evalF k t') = some u := h
    cases hs : step? t with
    | none =>
      rw [hs] at h'
      cases h'
      exact ⟨List.replicate k t, by rw [List.length_replicate], certifiedPad_stutter hs k⟩
    | some t' =>
      rw [hs] at h'
      cases k with
      | zero => cases h'
      | succ k =>
        obtain ⟨ts, hl, hc⟩ := pad_of_evalF h'
        refine ⟨t' :: ts, by rw [List.length_cons, hl], ?_⟩
        show (padStep t == t' && certifiedPad t' ts u) = true
        rw [padStep_of_some hs, beq_self_eq_true', hc]; rfl

/-- **The budget-exact certificate is the fuelled interpreter.**  A
    certificate of exactly `k` rows from `t` to `u` exists iff `evalF k t`
    returns `u`. -/
theorem certified_pad_iff {k : Nat} {t u : Term} :
    (∃ ts, ts.length + 1 = k ∧ certifiedPad t ts u = true) ↔ evalF k t = some u := by
  constructor
  · intro ⟨ts, hl, hc⟩
    rw [← hl]
    exact evalF_pad hc
  · exact pad_of_evalF

/-- What a verifier relies on: a padded certificate ends in the value. -/
theorem certifiedPad_sound {ts : List Term} {t u : Term} (h : certifiedPad t ts u = true) :
    Eval t u :=
  evalF_sound (evalF_pad h)

/-- A certificate at a budget is unique: the prover has no freedom. -/
theorem certifiedPad_unique : ∀ {ts ts' : List Term} {t u u' : Term},
    certifiedPad t ts u = true → certifiedPad t ts' u' = true → ts.length = ts'.length →
    ts = ts' ∧ u = u'
  | [], [], t, u, u', h, h', _ => by
    have a : (t == u && (step? t).isNone) = true := h
    have b : (t == u' && (step? t).isNone) = true := h'
    rw [Bool.and_eq_true, beq_iff_eq] at a b
    exact ⟨rfl, a.1.symm.trans b.1⟩
  | [], _ :: _, _, _, _, _, _, hl => by cases hl
  | _ :: _, [], _, _, _, _, _, hl => by cases hl
  | x :: ts, y :: ts', t, u, u', h, h', hl => by
    have a : (padStep t == x && certifiedPad x ts u) = true := h
    have b : (padStep t == y && certifiedPad y ts' u') = true := h'
    rw [Bool.and_eq_true, beq_iff_eq] at a b
    have hxy : x = y := a.1.symm.trans b.1
    subst hxy
    have ih := certifiedPad_unique a.2 b.2 (Nat.succ.inj hl)
    exact ⟨by rw [ih.1], ih.2⟩

/-- `runF` counts the contractions `evalF` makes. -/
theorem evalF_of_runF : ∀ {k s : Nat} {t u : Term}, runF k t = some (u, s) →
    ∀ k', evalF k' t = some u ↔ s + 1 ≤ k'
  | 0, _, _, _, h, _ => by cases h
  | k + 1, s, t, u, h, k' => by
    have h' : (match step? t with
        | none => some (t, 0)
        | some t' => (runF k t').map (fun p => (p.1, p.2 + 1))) = some (u, s) := h
    cases hs : step? t with
    | none =>
      rw [hs] at h'
      cases h'
      constructor
      · intro he
        cases k' with
        | zero => cases he
        | succ k' => exact Nat.succ_le_succ (Nat.zero_le _)
      · intro hle
        cases k' with
        | zero => cases hle
        | succ k' =>
          show (match step? t with | none => some t | some t' => evalF k' t') = some t
          rw [hs]
    | some t' =>
      rw [hs] at h'
      dsimp only at h'
      cases hr : runF k t' with
      | none => rw [hr] at h'; cases h'
      | some p =>
        rw [hr] at h'
        obtain ⟨pu, ps⟩ := p
        have e : (pu, ps + 1) = (u, s) := Option.some.inj h'
        cases e
        have ih := evalF_of_runF hr
        cases k' with
        | zero =>
          constructor
          · intro he; cases he
          · intro hle; cases hle
        | succ k' =>
          have ek : evalF (k' + 1) t = evalF k' t' := by
            show (match step? t with | none => some t | some t' => evalF k' t') = evalF k' t'
            rw [hs]
          rw [ek, ih k']
          exact ⟨Nat.succ_le_succ, Nat.le_of_succ_le_succ⟩

/-- **The budgets at which a run is certified.**  A term that reaches `u` in
    `s` contractions has a budget-exact certificate at exactly the budgets
    `k ≥ s + 1`: one row per contraction and at least the final check. -/
theorem certified_pad_budgets {k s : Nat} {t u : Term} (h : runF k t = some (u, s)) (k' : Nat) :
    (∃ ts, ts.length + 1 = k' ∧ certifiedPad t ts u = true) ↔ s + 1 ≤ k' := by
  rw [certified_pad_iff]
  exact evalF_of_runF h k'
