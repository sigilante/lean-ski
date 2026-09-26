import Ski.Fuel
open Term

/-!
# Execution-trace certificates

A run's witness is the list of terms it visited.  `certified t ts u` checks,
by re-running `step?` on each consecutive pair, that `ts` is the contraction
sequence from `t` to `u`; `certified_sound` is the theorem a verifier relies
on and `certified_complete` says every reduction has such a certificate.
`traceF` produces the certificate the fuel interpreter itself took.  This is
the shape a zero-knowledge prover consumes: one row per contraction, each
row checked by the same three rules.
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
