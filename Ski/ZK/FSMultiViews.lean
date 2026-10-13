import Ski.ZK.FSMultiInterleave

/-!
# Queries chosen from earlier proofs' views

A distinguisher may choose its queries from the transcripts it has seen.
Such queries cost nothing where they are made: a bound for a proof, or for a
composite of proofs, gives the same bound for its view together with the
answers to queries chosen from that view, answered at the tables, and in the
simulation at the simulator's programmed tables (`zkbT_post`).  A later
proof's programming may overwrite their points: composed with it through
`zkbT_pair`, the view with its chosen queries is unchanged where both the
view's reads and the queries' miss (`postRun_read`, the queries' reads made
at the unprogrammed tables from the earlier view), and the collision term
counts the queries' hits on the later proof's points too (`zkbT_post_pair`).
The queries depend on the tables and the earlier draws, not on the later
proof's draw, so they add at most `k δq` hits, `δq` the later proof's spread
(`post_hits_le`).  Applied stage by stage, each result feeding the next as
its earlier stage, queries chosen from every earlier view and answer
interleave with the proofs; no `n`-fold theorem packages this, each stage
supplying its own reads and counts.  Not modelled: statements chosen from
earlier views (each proof's statement is fixed); a query count or strategy
shape that varies (`k` fixed).
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **Queries chosen from the views cost nothing where they are made**: a
    bound for a proof (or a composite of proofs) gives the same bound for its
    view together with the answers `q v H` to queries chosen from the view
    `v` and answered at the tables; in the simulation they are answered at
    the simulator's programmed tables. -/
theorem zkbT_post {T X C V W : Type} {K ε : Nat} {ST : (T → Nat) → Nat} {sm : (X → Nat) → Nat}
    {SC : (C → Nat) → Nat} {rv : T → X → V} {pg : T → C → X → T} {sv : T → C → X → V}
    (h : ZKBT ST K sm SC rv pg sv ε) (q : V → T → W) :
    ZKBT ST K sm SC (fun H x => (rv H x, q (rv H x) H)) pg (fun H c x => (sv H c x, q (sv H c x) (pg H c x))) ε :=
  fun E => h (fun H v => E H (v, q v H))

/-- The view-chosen queries' answers: `k` adaptive queries, the strategy
    chosen by the view `v`. -/
def postRun {V : Type} (K1 K2 K3 K4 k : Nat) (nxt : V → List Nat → Nat × Nat × Unit) (v : V)
    (H : Nat × Nat × Nat × Nat) : List Nat :=
  advRun K1 K2 K3 K4 k (nxt v) H

/-- **A view with its chosen queries is unchanged by a programming both miss**:
    the view's own reads miss (`hrv`), so the view and the strategy are the
    same, and the queries' reads at `H` miss (`runR4_prog`).  This is the
    `hread` a later proof's `zkbT_pair` asks of it. -/
theorem postRun_read {X V : Type} {K1 K2 K3 K4 k : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (rv : Nat × Nat × Nat × Nat → X → V) (nxt : V → List Nat → Nat × Nat × Unit) (H H' p a : Nat × Nat × Nat × Nat)
    (hH' : H' = prog4 K1 K2 K3 K4 H p a)
    (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (x : X) (hrv : rv H' x = rv H x)
    (hm : (advRd K1 K2 K3 K4 k (nxt (rv H x)) H).any (fun r => decide (coord4 r.1 p = r.2)) = false) :
    (rv H' x, postRun K1 K2 K3 K4 k nxt (rv H' x) H') = (rv H x, postRun K1 K2 K3 K4 k nxt (rv H x) H) := by
  rw [hrv]
  unfold postRun
  rw [hH', advRd_hrd h1 h2 h3 h4 _ H p a ha hm]

/-- **Queries chosen from an earlier stage's view, then a later proof**: an
    earlier stage `B` (a proof or a composite, its view `rvB`, its own reads
    flagged by `colB`) followed by `k` queries chosen from its view, then a
    proof `A` programming its points.  The pair keeps `zkbT_pair`'s bound,
    the collision term now counting the queries' hits on `A`'s points too
    (`hcol`). -/
theorem zkbT_post_pair {XA XB CA CB VA VB : Type} {K1 K2 K3 K4 KA KB εA εB δ k : Nat}
    (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (ST : (Nat × Nat × Nat × Nat → Nat) → Nat) (hST : Lin ST)
    (smA : (XA → Nat) → Nat) (hsA : Lin smA) (smB : (XB → Nat) → Nat) (hsB : Lin smB)
    (SCA : (CA → Nat) → Nat) (hcA : Lin SCA) (SCB : (CB → Nat) → Nat)
    (c1 : Comm smA smB) (c2 : Comm ST smB) (c3 : Comm SCA smB) (c4 : Comm ST SCA) (c5 : Comm ST smA)
    (c7 : Comm smA SCB)
    (rvA : Nat × Nat × Nat × Nat → XA → VA) (pts : CA → XA → Nat × Nat × Nat × Nat) (cv : CA → Nat × Nat × Nat × Nat)
    (svA : Nat × Nat × Nat × Nat → CA → XA → VA)
    (rvB : Nat × Nat × Nat × Nat → XB → VB) (pgB : Nat × Nat × Nat × Nat → CB → XB → Nat × Nat × Nat × Nat)
    (svB : Nat × Nat × Nat × Nat → CB → XB → VB)
    (hA : ZKBT ST KA smA SCA rvA (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) (cv c)) svA εA)
    (hB : ZKBT ST KB smB SCB rvB pgB svB εB)
    (nxt : VB → List Nat → Nat × Nat × Unit)
    (colB : Nat × Nat × Nat × Nat → CA → XA → XB → Bool) (okA : CA → Bool)
    (hokA : ∀ f g : CA → Nat, (∀ c, okA c = true → f c ≤ g c) → SCA f ≤ SCA g)
    (hcv : ∀ c, okA c = true → (cv c).1 < K1 ∧ (cv c).2.1 < K2 ∧ (cv c).2.2.1 < K3 ∧ (cv c).2.2.2 < K4)
    (hreadB : ∀ H ca xa xb, okA ca = true → colB H ca xa xb = false →
      rvB (prog4 K1 K2 K3 K4 H (pts ca xa) (cv ca)) xb = rvB H xb)
    (hcol : SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => indB (colB H ca xa xb ||
      (advRd K1 K2 K3 K4 k (nxt (rvB H xb)) H).any (fun r => decide (coord4 r.1 (pts ca xa) = r.2))))))) ≤ δ) :
    ZKBT ST (KB * KA) (fun f : XA × XB → Nat => smB (fun xb => smA (fun xa => f (xa, xb))))
      (fun g : CA × CB → Nat => SCA (fun ca => SCB (fun cb => g (ca, cb))))
      (fun H x => (rvA H x.1, (rvB H x.2, postRun K1 K2 K3 K4 k nxt (rvB H x.2) H)))
      (fun H c x => prog4 K1 K2 K3 K4 (pgB H c.2 x.2) (pts c.1 x.1) (cv c.1))
      (fun H c x => (svA (pgB H c.2 x.2) c.1 x.1,
        (svB H c.2 x.2, postRun K1 K2 K3 K4 k nxt (svB H c.2 x.2) (pgB H c.2 x.2))))
      (KB * (εA * smB (fun _ => 1)) + εB * SCA (fun _ => smA (fun _ => 1)) + KB * δ) :=
  zkbT_pair ST hST smA hsA smB hsB SCA hcA SCB c1 c2 c3 c4 c5 c7
    rvA (fun H c x => prog4 K1 K2 K3 K4 H (pts c x) (cv c)) svA
    (fun H x => (rvB H x, postRun K1 K2 K3 K4 k nxt (rvB H x) H)) pgB
    (fun H c x => (svB H c x, postRun K1 K2 K3 K4 k nxt (svB H c x) (pgB H c x)))
    hA (zkbT_post hB (fun v H => postRun K1 K2 K3 K4 k nxt v H))
    (fun H ca xa xb => colB H ca xa xb ||
      (advRd K1 K2 K3 K4 k (nxt (rvB H xb)) H).any (fun r => decide (coord4 r.1 (pts ca xa) = r.2)))
    okA hokA
    (fun H ca xa xb hok hc => by
      rw [Bool.or_eq_false_iff] at hc
      exact postRun_read h1 h2 h3 h4 rvB nxt H _ (pts ca xa) (cv ca) rfl (hcv ca hok) xb
        (hreadB H ca xa xb hok hc.1) hc.2)
    hcol

/-- **The view-chosen queries add at most `k δq` hits**: at fixed tables and
    earlier draw, the queries are a fixed list of `k` reads, so with every
    coordinate of the later proof's points spreading (`hsp`) they hit at
    most `k δq` of its draws, beside the earlier stage's own hits. -/
theorem post_hits_le {XA VB : Type} {K1 K2 K3 K4 k δq : Nat} (smA : (XA → Nat) → Nat) (hsA : Lin smA)
    (pts : XA → Nat × Nat × Nat × Nat) (hsp : ∀ i v, smA (fun xa => indB (decide (coord4 i (pts xa) = v))) ≤ δq)
    (nxt : VB → List Nat → Nat × Nat × Unit) (vB : VB) (H : Nat × Nat × Nat × Nat) (colB : XA → Bool) :
    smA (fun xa => indB (colB xa || (advRd K1 K2 K3 K4 k (nxt vB) H).any
      (fun r => decide (coord4 r.1 (pts xa) = r.2)))) ≤ smA (fun xa => indB (colB xa)) + k * δq := by
  refine Nat.le_trans (sm_mono smA hsA (fun xa => indB_or_le _ _)) ?_
  rw [sm_add smA hsA]
  refine Nat.add_le_add_left ?_ _
  have h := reads_hits_le smA hsA pts δq hsp (advRd K1 K2 K3 K4 k (nxt vB) H)
  rwa [advRd_length] at h

end Circuit
