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
queries it never makes are padding, charged as the `k`-run's hits.  A
strategy (or rule) drawn uniformly from `R`, each meeting a bound at the
same programming, meets it at `R` times the draws and the error, the same
fraction (`zkbT_mix`).  The strategy may depend on the statements, which
are fixed before the tables are drawn (`nxt` is any function).  Charged only
for the queries it makes: the stopping time reads only the answers up to it
(`stopUp_congr`), so a programming those queries miss leaves the stopped
view unchanged (`truncStop_prog`), and the collision term counts their hits
alone, never more than the `k`-run's (`advHitS`, `advHitS_le`,
`zkbT_queries_stopT`, over `zkbT_queriesV`, `zkbT_queries`
for any query view).  Not shown: statements chosen after seeing the tables.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- Scanning up from `i`, at most `f` more steps, for the first `j` at whose
    answers `g j` the rule `s` fires. -/
def stopUp (s : List Nat → Bool) (g : Nat → List Nat) : Nat → Nat → Nat
  | i, 0 => i
  | i, f + 1 => if s (g i) then i else stopUp s g (i + 1) f

/-- The stopping time: the first `j ≤ k` at whose answers `g j` the rule
    `s` fires, else `k`. -/
def stopTime (s : List Nat → Bool) (k : Nat) (g : Nat → List Nat) : Nat :=
  stopUp s g 0 k

/-- The `k`-run's answers (newest first) truncated where the rule `s` first
    fires on the answers so far. -/
def truncStop (s : List Nat → Bool) (k : Nat) (L : List Nat) : List Nat :=
  L.drop (k - stopTime s k (fun j => L.drop (k - j)))

theorem stopUp_ge (s : List Nat → Bool) (g : Nat → List Nat) : ∀ i f, i ≤ stopUp s g i f
  | i, 0 => Nat.le_refl i
  | i, f + 1 => by
    unfold stopUp; split
    · exact Nat.le_refl i
    · exact Nat.le_trans (Nat.le_succ i) (stopUp_ge s g (i + 1) f)

theorem stopUp_le (s : List Nat → Bool) (g : Nat → List Nat) : ∀ i f, stopUp s g i f ≤ i + f
  | i, 0 => Nat.le_refl i
  | i, f + 1 => by
    unfold stopUp; split
    · exact Nat.le_add_right i _
    · have := stopUp_le s g (i + 1) f
      rwa [Nat.add_assoc, Nat.add_comm 1 f] at this

/-- **The stopping time reads only the answers up to it.** -/
theorem stopUp_congr (s : List Nat → Bool) (g g' : Nat → List Nat) : ∀ i f,
    (∀ j, j ≤ stopUp s g i f → g' j = g j) → stopUp s g' i f = stopUp s g i f
  | i, 0, _ => rfl
  | i, f + 1, h => by
    have hi : g' i = g i := h i (stopUp_ge s g i (f + 1))
    unfold stopUp
    rw [hi]
    split
    · rfl
    · next hs =>
      refine stopUp_congr s g g' (i + 1) f (fun j hj => h j ?_)
      unfold stopUp; rw [if_neg hs]; exact hj

theorem stopTime_le (s : List Nat → Bool) (k : Nat) (g : Nat → List Nat) : stopTime s k g ≤ k := by
  have := stopUp_le s g 0 k; rwa [Nat.zero_add] at this

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
      stopTime s k (fun j => advRun K1 K2 K3 K4 j nxt H) :=
    stopUp_congr s _ _ 0 k (fun j hj => hd j (Nat.le_trans hj (stopTime_le s k _)))
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

/-- **A strategy drawn at random keeps the bound**: if each of `R`
    strategies (or rules, or any index `r` of the view) meets a `ZKBT` bound
    at the same programming, the strategy drawn uniformly, its index shown
    in the view, meets it over `R` times the draws at `R` times the error,
    the same fraction. -/
theorem zkbT_mix {T X C V : Type} {K ε R : Nat} {ST : (T → Nat) → Nat} (hST : Lin ST) {sm : (X → Nat) → Nat}
    {SC : (C → Nat) → Nat} (hSC : Lin SC) {pg : T → C → X → T}
    (rv : Nat → T → X → V) (sv : Nat → T → C → X → V)
    (h : ∀ r, r < R → ZKBT ST K sm SC (rv r) pg (sv r) ε) :
    ZKBT ST K (fun f : Nat × X → Nat => sumTo R (fun r => sm (fun x => f (r, x)))) SC
      (fun H rx => (rx.1, rv rx.1 H rx.2)) (fun H c rx => pg H c rx.2) (fun H c rx => (rx.1, sv rx.1 H c rx.2))
      (R * ε) := by
  intro E
  show K * ST (fun H => sumTo R (fun r => sm (fun x => indB (E H (r, rv r H x))))) ≤
    ST (fun H => SC (fun c => sumTo R (fun r => sm (fun x => indB (E (pg H c x) (r, sv r H c x)))))) + R * ε
  rw [hST R (fun r H => sm (fun x => indB (E H (r, rv r H x)))), sumTo_mul]
  have e2 : (fun H => SC (fun c => sumTo R (fun r => sm (fun x => indB (E (pg H c x) (r, sv r H c x)))))) =
      fun H => sumTo R (fun r => SC (fun c => sm (fun x => indB (E (pg H c x) (r, sv r H c x))))) :=
    funext fun H => hSC R (fun r c => sm (fun x => indB (E (pg H c x) (r, sv r H c x))))
  rw [e2, hST R (fun r H => SC (fun c => sm (fun x => indB (E (pg H c x) (r, sv r H c x))))),
    ← sumTo_const ε R, ← sumTo_add]
  exact sumTo_mono _ (fun r hr => h r hr (fun H v => E H (r, v)))

/-- **`zkbT_queries` for any query view**: a view `vw` of the tables,
    unchanged by an in-range programming whose point its flag `hit` misses
    (`hv`), beside a proof; the error gains the flagged hits. -/
theorem zkbT_queriesV {XA CA VA W : Type} {K1 K2 K3 K4 KA εA δ : Nat}
    (ST : (Nat × Nat × Nat × Nat → Nat) → Nat) (hST : Lin ST)
    (smA : (XA → Nat) → Nat) (hsA : Lin smA) (SCA : (CA → Nat) → Nat) (hcA : Lin SCA)
    (c4 : Comm ST SCA) (c5 : Comm ST smA)
    (rvA : Nat × Nat × Nat × Nat → XA → VA) (pts : CA → XA → Nat × Nat × Nat × Nat) (cv : CA → Nat × Nat × Nat × Nat)
    (svA : Nat × Nat × Nat × Nat → CA → XA → VA)
    (hA : ZKBT ST KA smA SCA rvA (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) (cv c)) svA εA)
    (okA : CA → Bool) (hokA : ∀ f g : CA → Nat, (∀ c, okA c = true → f c ≤ g c) → SCA f ≤ SCA g)
    (hcv : ∀ c, okA c = true → (cv c).1 < K1 ∧ (cv c).2.1 < K2 ∧ (cv c).2.2.1 < K3 ∧ (cv c).2.2.2 < K4)
    (vw : Nat × Nat × Nat × Nat → W) (hit : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Bool)
    (hv : ∀ H p a, a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4 → hit H p = false →
      vw (prog4 K1 K2 K3 K4 H p a) = vw H)
    (hcol : SCA (fun ca => smA (fun xa => ST (fun H => indB (hit H (pts ca xa))))) ≤ δ) :
    ZKBT ST KA (fun f : XA × Unit → Nat => smA (fun xa => f (xa, ())))
      (fun g : CA × Unit → Nat => SCA (fun ca => g (ca, ())))
      (fun H x => (rvA H x.1, vw H))
      (fun H c x => prog4 K1 K2 K3 K4 H (pts c.1 x.1) (cv c.1))
      (fun H c x => (svA H c.1 x.1, vw H))
      (εA + δ) := by
  have hB : ZKBT ST 1 (fun f : Unit → Nat => f ()) (fun g : Unit → Nat => g ()) (fun H _ => vw H)
      (fun H _ _ => H) (fun H _ _ => vw H) 0 := fun E => by
    rw [Nat.one_mul, Nat.add_zero]; exact Nat.le_refl _
  have h := zkbT_pair ST hST smA hsA (fun f : Unit → Nat => f ()) (fun _ _ => rfl) SCA hcA (fun g : Unit → Nat => g ())
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) c4 c5 (fun _ => rfl)
    rvA (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) (cv c)) svA
    (fun H _ => vw H) (fun H _ _ => H) (fun H _ _ => vw H) hA hB
    (fun H ca xa _ => hit H (pts ca xa)) okA hokA
    (fun H ca xa _ hok hc => hv H (pts ca xa) (cv ca) (hcv ca hok) hc)
    hcol
  intro E
  have := h E
  simp only [Nat.one_mul, Nat.mul_one, Nat.zero_mul, Nat.add_zero] at this
  exact this

/-- The stopping distinguisher's hits: only the queries made before it
    stops. -/
def advHitS (K1 K2 K3 K4 k : Nat) (nxt : List Nat → Nat × Nat × Unit) (s : List Nat → Bool)
    (H p : Nat × Nat × Nat × Nat) : Bool :=
  advHit K1 K2 K3 K4 (stopTime s k (fun j => advRun K1 K2 K3 K4 j nxt H)) nxt H p

/-- **The stopped view is unchanged by a programming its queries made miss.** -/
theorem truncStop_prog {K1 K2 K3 K4 k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (nxt : List Nat → Nat × Nat × Unit) (s : List Nat → Bool) (H p a : Nat × Nat × Nat × Nat)
    (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (hm : advHitS K1 K2 K3 K4 k nxt s H p = false) :
    truncStop s k (advRun K1 K2 K3 K4 k nxt (prog4 K1 K2 K3 K4 H p a)) = truncStop s k (advRun K1 K2 K3 K4 k nxt H) := by
  rw [truncStop_advRun, truncStop_advRun]
  generalize hJ : stopTime s k (fun j => advRun K1 K2 K3 K4 j nxt H) = J
  have hm' : advHit K1 K2 K3 K4 J nxt H p = false := by rw [← hJ]; exact hm
  have hrun : advRun K1 K2 K3 K4 J nxt (prog4 K1 K2 K3 K4 H p a) = advRun K1 K2 K3 K4 J nxt H :=
    runR4_prog h1 h2 h3 h4 _ nxt H p a ha J (fun r hr e => by
      have hit : advHit K1 K2 K3 K4 J nxt H p = true := List.any_eq_true.2 ⟨r, hr, decide_eq_true e⟩
      rw [hm'] at hit; exact Bool.false_ne_true hit)
  have hag : ∀ j, j ≤ J → advRun K1 K2 K3 K4 j nxt (prog4 K1 K2 K3 K4 H p a) = advRun K1 K2 K3 K4 j nxt H := by
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    have e1 := runR4_drop K1 K2 K3 K4 1 0 (fun m _ => m) nxt (prog4 K1 K2 K3 K4 H p a) j d
    have e2 := runR4_drop K1 K2 K3 K4 1 0 (fun m _ => m) nxt H j d
    unfold advRun at hrun ⊢
    rw [← e1, ← e2, hrun]
  have hst : stopTime s k (fun j => advRun K1 K2 K3 K4 j nxt (prog4 K1 K2 K3 K4 H p a)) = J := by
    rw [← hJ]
    exact stopUp_congr s _ _ 0 k (fun j hj => hag j (hJ ▸ hj))
  rw [hst, hrun]

/-- **A distinguisher stopping adaptively, charged only for the queries it
    makes**: `zkbT_queries_stop` with the collision term over the hits of
    the queries before its stopping time (`advHitS`). -/
theorem zkbT_queries_stopT {XA CA VA : Type} {K1 K2 K3 K4 KA εA δ k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4) (ST : (Nat × Nat × Nat × Nat → Nat) → Nat) (hST : Lin ST)
    (smA : (XA → Nat) → Nat) (hsA : Lin smA) (SCA : (CA → Nat) → Nat) (hcA : Lin SCA)
    (c4 : Comm ST SCA) (c5 : Comm ST smA)
    (rvA : Nat × Nat × Nat × Nat → XA → VA) (pts : CA → XA → Nat × Nat × Nat × Nat) (cv : CA → Nat × Nat × Nat × Nat)
    (svA : Nat × Nat × Nat × Nat → CA → XA → VA)
    (hA : ZKBT ST KA smA SCA rvA (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) (cv c)) svA εA)
    (okA : CA → Bool) (hokA : ∀ f g : CA → Nat, (∀ c, okA c = true → f c ≤ g c) → SCA f ≤ SCA g)
    (hcv : ∀ c, okA c = true → (cv c).1 < K1 ∧ (cv c).2.1 < K2 ∧ (cv c).2.2.1 < K3 ∧ (cv c).2.2.2 < K4)
    (nxt : List Nat → Nat × Nat × Unit) (s : List Nat → Bool)
    (hcol : SCA (fun ca => smA (fun xa => ST (fun H => indB (advHitS K1 K2 K3 K4 k nxt s H (pts ca xa))))) ≤ δ) :
    ZKBT ST KA (fun f : XA × Unit → Nat => smA (fun xa => f (xa, ())))
      (fun g : CA × Unit → Nat => SCA (fun ca => g (ca, ())))
      (fun H x => (rvA H x.1, truncStop s k (advRun K1 K2 K3 K4 k nxt H)))
      (fun H c x => prog4 K1 K2 K3 K4 H (pts c.1 x.1) (cv c.1))
      (fun H c x => (svA H c.1 x.1, truncStop s k (advRun K1 K2 K3 K4 k nxt H)))
      (εA + δ) :=
  zkbT_queriesV ST hST smA hsA SCA hcA c4 c5 rvA pts cv svA hA okA hokA hcv
    (fun H => truncStop s k (advRun K1 K2 K3 K4 k nxt H)) (advHitS K1 K2 K3 K4 k nxt s)
    (fun H p a ha hm => truncStop_prog h1 h2 h3 h4 nxt s H p a ha hm) hcol

theorem readsR4_drop {W : Type} (K1 K2 K3 K4 n1 m : Nat) (φ : Nat → W → Nat) (nxt : List Nat → Nat × Nat × W)
    (H : Nat × Nat × Nat × Nat) (j : Nat) : ∀ d,
    (readsR4 K1 K2 K3 K4 n1 m φ nxt H (j + d)).drop d = readsR4 K1 K2 K3 K4 n1 m φ nxt H j
  | 0 => rfl
  | d + 1 => by
    show (_ :: readsR4 K1 K2 K3 K4 n1 m φ nxt H (j + d)).drop (d + 1) = _
    rw [List.drop_succ_cons]; exact readsR4_drop K1 K2 K3 K4 n1 m φ nxt H j d

/-- **The tighter count is tighter**: a hit among the queries made is a hit
    of the `k`-run. -/
theorem advHitS_le (K1 K2 K3 K4 k : Nat) (nxt : List Nat → Nat × Nat × Unit) (s : List Nat → Bool)
    (H p : Nat × Nat × Nat × Nat) :
    advHitS K1 K2 K3 K4 k nxt s H p = true → advHit K1 K2 K3 K4 k nxt H p = true := by
  intro h
  unfold advHitS at h
  generalize hJ : stopTime s k (fun j => advRun K1 K2 K3 K4 j nxt H) = J at h
  have hJk : J ≤ k := hJ ▸ stopTime_le s k _
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hJk
  obtain ⟨r, hr, e⟩ := List.any_eq_true.1 h
  refine List.any_eq_true.2 ⟨r, ?_, e⟩
  rw [← readsR4_drop K1 K2 K3 K4 1 0 (fun m _ => m) nxt H J d] at hr
  exact List.mem_of_mem_drop hr

end Circuit
