import Ski.ZK.FSMultiViews

/-!
# A query count the distinguisher chooses

`FSMultiQueries` fixes the distinguisher's query count `k`.  A distinguisher
that stops adaptively, after the first answers on which its rule `s` says
stop, at most `k` queries, sees a prefix of the `k`-query run's answers: the
run's answers after `j` queries are its last `j` (`runR4_drop`), so its view
is the `k`-run's view truncated (`truncStop`), at the first `j` where `s`
fires (`truncStop_advRun`, `stopTime`).  A function of the `k`-run's view, it
keeps `zkbT_queries`'s bound with no added error (`zkbT_queries_stop`): the
queries it never makes are padding, charged as the `k`-run's hits.  Not
shown: a tighter error counting only the queries made.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **The run's answers after `j` queries are the last `j` of a longer run.** -/
theorem runR4_drop {W : Type} (K1 K2 K3 K4 n1 m : Nat) (φ : Nat → W → Nat) (nxt : List Nat → Nat × Nat × W)
    (H : Nat × Nat × Nat × Nat) (j : Nat) : ∀ d,
    (runR4 K1 K2 K3 K4 n1 m φ nxt H (j + d)).drop d = runR4 K1 K2 K3 K4 n1 m φ nxt H j
  | 0 => rfl
  | d + 1 => by
    show (_ :: runR4 K1 K2 K3 K4 n1 m φ nxt H (j + d)).drop (d + 1) = _
    rw [List.drop_succ_cons]; exact runR4_drop K1 K2 K3 K4 n1 m φ nxt H j d

/-- The stopping time: the first `j ≤ k` at whose answers `g j` the rule
    `s` fires, else `k`. -/
def stopTime (s : List Nat → Bool) (k : Nat) (g : Nat → List Nat) : Nat :=
  ((List.range (k + 1)).find? (fun j => s (g j))).getD k

/-- The `k`-run's answers (newest first) truncated where the rule `s` first
    fires on the answers so far. -/
def truncStop (s : List Nat → Bool) (k : Nat) (L : List Nat) : List Nat :=
  L.drop (k - stopTime s k (fun j => L.drop (k - j)))

theorem find?_congr {α : Type} {p q : α → Bool} : ∀ (l : List α), (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons]
    rw [h a (List.mem_cons_self ..), find?_congr l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem stopTime_le (s : List Nat → Bool) (k : Nat) (g : Nat → List Nat) : stopTime s k g ≤ k := by
  unfold stopTime
  cases e : (List.range (k + 1)).find? (fun j => s (g j)) with
  | none => exact Nat.le_refl _
  | some j => exact Nat.le_of_lt_succ (List.mem_range.1 (List.mem_of_find?_eq_some e))

/-- **The truncated `k`-run is the stopping distinguisher's view**: its
    answers after the first `j ≤ k` queries at which `s` fires. -/
theorem truncStop_advRun (K1 K2 K3 K4 k : Nat) (nxt : List Nat → Nat × Nat × Unit) (s : List Nat → Bool)
    (H : Nat × Nat × Nat × Nat) :
    truncStop s k (advRun K1 K2 K3 K4 k nxt H) =
      advRun K1 K2 K3 K4 (stopTime s k (fun j => advRun K1 K2 K3 K4 j nxt H)) nxt H := by
  have hd : ∀ j, j ≤ k → (advRun K1 K2 K3 K4 k nxt H).drop (k - j) = advRun K1 K2 K3 K4 j nxt H := by
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    unfold advRun
    rw [Nat.add_sub_cancel_left]
    exact runR4_drop K1 K2 K3 K4 1 0 (fun m _ => m) nxt H j d
  have hs : stopTime s k (fun j => (advRun K1 K2 K3 K4 k nxt H).drop (k - j)) =
      stopTime s k (fun j => advRun K1 K2 K3 K4 j nxt H) := by
    unfold stopTime
    rw [find?_congr (q := fun j => s (advRun K1 K2 K3 K4 j nxt H)) _
      (fun j hj => by show s (List.drop (k - j) (advRun K1 K2 K3 K4 k nxt H)) = _; rw [hd j (Nat.le_of_lt_succ (List.mem_range.1 hj))])]
  unfold truncStop
  rw [hs]
  exact hd _ (stopTime_le _ _ _)

/-- **A distinguisher stopping adaptively keeps the bound**: its view, the
    `k`-run truncated by its rule `s` (`truncStop_advRun`), is a function of
    `zkbT_queries`'s view, so the bound and error carry over. -/
theorem zkbT_queries_stop {XA CA VA : Type} {K1 K2 K3 K4 KA εA δ k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4) (ST : (Nat × Nat × Nat × Nat → Nat) → Nat) (hST : Lin ST)
    (smA : (XA → Nat) → Nat) (hsA : Lin smA) (SCA : (CA → Nat) → Nat) (hcA : Lin SCA)
    (c4 : Comm ST SCA) (c5 : Comm ST smA)
    (rvA : Nat × Nat × Nat × Nat → XA → VA) (pts : CA → XA → Nat × Nat × Nat × Nat) (cv : CA → Nat × Nat × Nat × Nat)
    (svA : Nat × Nat × Nat × Nat → CA → XA → VA)
    (hA : ZKBT ST KA smA SCA rvA (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) (cv c)) svA εA)
    (okA : CA → Bool) (hokA : ∀ f g : CA → Nat, (∀ c, okA c = true → f c ≤ g c) → SCA f ≤ SCA g)
    (hcv : ∀ c, okA c = true → (cv c).1 < K1 ∧ (cv c).2.1 < K2 ∧ (cv c).2.2.1 < K3 ∧ (cv c).2.2.2 < K4)
    (nxt : List Nat → Nat × Nat × Unit)
    (hcol : SCA (fun ca => smA (fun xa => ST (fun H => indB (advHit K1 K2 K3 K4 k nxt H (pts ca xa))))) ≤ δ)
    (s : List Nat → Bool) :
    ZKBT ST KA (fun f : XA × Unit → Nat => smA (fun xa => f (xa, ())))
      (fun g : CA × Unit → Nat => SCA (fun ca => g (ca, ())))
      (fun H x => (rvA H x.1, truncStop s k (advRun K1 K2 K3 K4 k nxt H)))
      (fun H c x => prog4 K1 K2 K3 K4 H (pts c.1 x.1) (cv c.1))
      (fun H c x => (svA H c.1 x.1, truncStop s k (advRun K1 K2 K3 K4 k nxt H)))
      (εA + δ) := fun E =>
  zkbT_queries h1 h2 h3 h4 ST hST smA hsA SCA hcA c4 c5 rvA pts cv svA hA okA hokA hcv nxt hcol
    (fun H v => E H (v.1, truncStop s k v.2))

end Circuit
