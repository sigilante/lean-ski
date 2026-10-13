import Ski.ZK.FSMultiMix
import Ski.ZK.FSMultiViews

/-!
# Queries chosen from each proof's view, `n` proofs

`FSMultiViews` composes a proof with queries chosen from an earlier view
stage by stage.  Here the own-view case composes in one theorem: `n`
four-round proofs, each followed by `kq` adaptive queries its distinguisher
chooses from that proof's own view (`postRun`): a component's view is the
proof's view with the answers (`postV`, its simulated view `postSv`), its
bound unchanged (`zkbT_post`), its reads the proof's and the queries' (`rdP
i H x ++ advRd …`, the queries' made at the tables from the view there,
`postRun_read`), so `zkbT_powD_rd` composes them (`fs4_postInterleave`). The
queries' hits on the later proofs' points are charged to their spread, `kq`
more reads per proof.  Queries chosen from all `n` views at once, made after
the proofs, add nothing to any composite bound (`zkbT_postAll`).  Queries
chosen from every earlier view and answer at once, made between proofs,
compose `n`-fold as `zkbT_powD` does, `zkbT_post_pair` iterated (`VQ`,
`rvQ`, `svQ`, `zkbT_powQ`), each stage's hit flag `col` and collision bound
`hcol` hypotheses as in `zkbT_powD`.  Not shown: those discharged from read
lists and spread for the circuits (`post_hits_le` bounds a phase's own
share, `kq δq`; a read list for `rvQ` in the manner of `zkbT_powD_rd`,
flagging every earlier proof's and phase's reads, is not built); query
counts varying by phase; pure query phases between proofs here
(`fs4_interleave` has them); statements chosen from views are
`FSMultiAdapt`'s.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- A proof's view with the answers to queries chosen from it. -/
def postV {O : Type} (K1 K2 K3 K4 kq : Nat) (nxtV : Nat → Nat × Nat × Nat × O → List Nat → Nat × Nat × Unit)
    (rvP : (i : Nat) → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Nat × Nat × Nat × O)
    (i : Nat) (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) :
    (Nat × Nat × Nat × O) × List Nat :=
  (rvP i H x, postRun K1 K2 K3 K4 kq (nxtV i) (rvP i H x) H)

/-- **`n` proofs, each followed by queries chosen from its view**:
    `fs4_powDT`'s proofs with read lists (`hrdP`) and spread (`hsp`), each
    component's view the proof's with `kq` view-chosen answers. -/
theorem fs4_postInterleave {O : Type} {m K2 K4 N4 T1 T2 T3 kq : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (D : Nat → FS4DT O)
    (nxtV : Nat → Nat × Nat × Nat × O → List Nat → Nat × Nat × Unit)
    (rdP : Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → List (Nat × Nat))
    (hrdP : ∀ i H p a x, a.1 < Q4 * Q4 ∧ a.2.1 < K2 ∧ a.2.2.1 < Q4 ∧ a.2.2.2 < K4 →
      (rdP i H x).any (fun r => decide (coord4 r.1 p = r.2)) = false →
      read4T (Q4 * Q4) K2 Q4 K4 (D i).m1 (D i).m2 (D i).m3 (D i).q (D i).out (prog4 (Q4 * Q4) K2 Q4 K4 H p a) x =
        read4T (Q4 * Q4) K2 Q4 K4 (D i).m1 (D i).m2 (D i).m3 (D i).q (D i).out H x)
    (RP : Nat → Nat) (hRP : ∀ i H x, (rdP i H x).length ≤ RP i)
    (δq : Nat → Nat)
    (hsp : ∀ n c tab v, (D n).sm m (fun x => indB (decide (coord4 tab ((D n).pts c x) = v))) ≤ δq n) :
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo T1 (fun H1 =>
      sumTo T2 (fun H2 => sumTo T3 (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))
    let K := K4 * (Q4 * Q4 * (K2 * Q4))
    (∀ i, ZKBT ST K ((D i).sm m) SC (read4T (Q4 * Q4) K2 Q4 K4 (D i).m1 (D i).m2 (D i).m3 (D i).q (D i).out)
      (fun H c x => prog4 (Q4 * Q4) K2 Q4 K4 H ((D i).pts c x) c) (D i).sv (D i).ε) →
    ∀ n, ZKBT ST (KPowD (fun _ => K) n) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => (D i).sm m) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => SC) n)
      (rvPowD (postV (Q4 * Q4) K2 Q4 K4 kq nxtV
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 (D i).m1 (D i).m2 (D i).m3 (D i).q (D i).out)) n)
      (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun _ => true) (fun i => (D i).pts) (fun _ c => c)) n)
      (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun _ => true) (fun i => (D i).pts) (fun _ c => c))
        (fun i H c x => ((D i).sv H c x, postRun (Q4 * Q4) K2 Q4 K4 kq (nxtV i) ((D i).sv H c x)
          (prog4 (Q4 * Q4) K2 Q4 K4 H ((D i).pts c x) c))) n)
      (errPowD (fun _ => K) (fun i => (D i).sm m) (fun _ => SC) (fun i => (D i).ε)
        (fun n => SC (fun _ => ST (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => (D i).sm m) n
          (fun _ => rSum (fun i => RP i + kq) n * δq n)))) n) := by
  intro ST SC K hzk
  have hQ : 0 < Q4 * Q4 := Nat.mul_pos Q4_pos Q4_pos
  have hST : Lin ST := lin_sum4 _ _ _ _
  have hSC : Lin SC := lin_sum4 _ _ _ _
  let ok := fun (c : Nat × Nat × Nat × Nat) =>
    decide (c.1 < Q4 * Q4) && decide (c.2.1 < K2) && decide (c.2.2.1 < Q4) && decide (c.2.2.2 < K4)
  have hok : ∀ f g : Nat × Nat × Nat × Nat → Nat, (∀ c, ok c = true → f c ≤ g c) → SC f ≤ SC g := by
    intro f g h
    refine sumTo_mono _ (fun c4 h4 => sumTo_mono _ (fun c1 h1 => sumTo_mono _ (fun c2 h2 => sumTo_mono _ (fun c3 h3 =>
      h _ ?_))))
    simp only [ok, h1, h2, h3, h4, decide_true, Bool.and_self]
  have hcv : ∀ c, ok c = true → c.1 < Q4 * Q4 ∧ c.2.1 < K2 ∧ c.2.2.1 < Q4 ∧ c.2.2.2 < K4 := by
    intro c h
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  refine zkbT_powD_rd (fun _ => K) ST hST (fun i => (D i).sm m) (fun i => lin_sm _ _ _ _) (fun _ => SC) (fun _ => hSC)
    (fun i j => comm_sm (lin_sm _ _ _ _) _ _ _ _) (fun i => comm_sum4 (lin_sm _ _ _ _) _ _ _ _)
    (fun i j => comm_sum4 (lin_sm _ _ _ _) _ _ _ _) (fun i => comm_sum4 (lin_sum4 _ _ _ _) _ _ _ _)
    (fun i j => comm_sm (lin_sum4 _ _ _ _) _ _ _ _) (fun _ => true)
    _ _ (fun _ c => c) _ (fun i => (D i).ε) (fun i => ?_) (fun _ => ok) (fun _ => hok) (fun _ => hcv)
    (fun i H x => rdP i H x ++ advRd (Q4 * Q4) K2 Q4 K4 kq (nxtV i
      (read4T (Q4 * Q4) K2 Q4 K4 (D i).m1 (D i).m2 (D i).m3 (D i).q (D i).out H x)) H)
    (fun i H p a x ha hm => ?_) (fun i => RP i + kq) (fun i H x => ?_) δq (fun n _ => hsp n)
  · exact zkbT_post (hzk i) (fun v H => postRun (Q4 * Q4) K2 Q4 K4 kq (nxtV i) v H)
  · rw [List.any_append, Bool.or_eq_false_iff] at hm
    exact postRun_read hQ hK2 Q4_pos hK4 _ (nxtV i) H _ p a rfl ha x (hrdP i H p a x ha hm.1) hm.2
  · rw [List.length_append, advRd_length]; exact Nat.add_le_add_right (hRP i H x) _

/-- **Queries chosen from all `n` views at once, after the proofs**: any
    composite bound (`fs4_powDT`, `fs4_interleave`, `fs4_postInterleave`, …)
    keeps its error for its whole view with `kq` adaptive queries chosen from
    that whole view, answered at the final tables (`zkbT_post`). -/
theorem zkbT_postAll {X C V : Type} {K ε kq K1 K2 K3 K4 : Nat} {ST : (Nat × Nat × Nat × Nat → Nat) → Nat}
    {sm : (X → Nat) → Nat} {SC : (C → Nat) → Nat} {rv : Nat × Nat × Nat × Nat → X → V}
    {pg : Nat × Nat × Nat × Nat → C → X → Nat × Nat × Nat × Nat} {sv : Nat × Nat × Nat × Nat → C → X → V}
    (h : ZKBT ST K sm SC rv pg sv ε) (nxt : V → List Nat → Nat × Nat × Unit) :
    ZKBT ST K sm SC (fun H x => (rv H x, postRun K1 K2 K3 K4 kq nxt (rv H x) H)) pg
      (fun H c x => (sv H c x, postRun K1 K2 K3 K4 kq nxt (sv H c x) (pg H c x))) ε :=
  zkbT_post h (fun v H => postRun K1 K2 K3 K4 kq nxt v H)

/-- The composite view with queries between proofs: before proof `n`
    programs, `kq` queries chosen from the whole view so far, every earlier
    proof's and every earlier answer. -/
def VQ (V : Nat → Type) : Nat → Type
  | 0 => Unit
  | n + 1 => V n × (VQ V n × List Nat)

/-- Its real view. -/
def rvQ {X V : Nat → Type} (K1 K2 K3 K4 kq : Nat) (rv : (i : Nat) → Nat × Nat × Nat × Nat → X i → V i)
    (nxt : (n : Nat) → VQ V n → List Nat → Nat × Nat × Unit) :
    (n : Nat) → Nat × Nat × Nat × Nat → PowD X n → VQ V n
  | 0, _, _ => ()
  | n + 1, H, x => (rv n H x.1, (rvQ K1 K2 K3 K4 kq rv nxt n H x.2,
      postRun K1 K2 K3 K4 kq (nxt n) (rvQ K1 K2 K3 K4 kq rv nxt n H x.2) H))

/-- Its simulated view, each stage at the tables the earlier stages
    programmed. -/
def svQ {X C V : Nat → Type} (K1 K2 K3 K4 kq : Nat)
    (pts : (i : Nat) → C i → X i → Nat × Nat × Nat × Nat) (cv : (i : Nat) → C i → Nat × Nat × Nat × Nat)
    (sv : (i : Nat) → Nat × Nat × Nat × Nat → C i → X i → V i)
    (nxt : (n : Nat) → VQ V n → List Nat → Nat × Nat × Unit) :
    (n : Nat) → Nat × Nat × Nat × Nat → PowD C n → PowD X n → VQ V n
  | 0, _, _, _ => ()
  | n + 1, H, c, x =>
    (sv n (pgPowD (fun i H c x => prog4 K1 K2 K3 K4 H (pts i c x) (cv i c)) n H c.2 x.2) c.1 x.1,
     (svQ K1 K2 K3 K4 kq pts cv sv nxt n H c.2 x.2,
      postRun K1 K2 K3 K4 kq (nxt n) (svQ K1 K2 K3 K4 kq pts cv sv nxt n H c.2 x.2)
        (pgPowD (fun i H c x => prog4 K1 K2 K3 K4 H (pts i c x) (cv i c)) n H c.2 x.2)))

/-- **`n` proofs with queries chosen from every earlier view between them**
    (`zkbT_post_pair` iterated as `zkbT_powD` iterates `zkbT_pair`): before
    proof `n` programs, `kq` queries chosen from the whole view so far.  The
    composite view's reads, flagged by `col n` (`hread`), and the queries'
    reads count toward each stage's collisions (`hcol`). -/
theorem zkbT_powQ {X C V : Nat → Type} {K1 K2 K3 K4 kq : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (K : Nat → Nat) (ST : (Nat × Nat × Nat × Nat → Nat) → Nat) (hST : Lin ST)
    (sm : (i : Nat) → (X i → Nat) → Nat) (hs : ∀ i, Lin (sm i))
    (sc : (i : Nat) → (C i → Nat) → Nat) (hc : ∀ i, Lin (sc i))
    (c1 : ∀ i j, Comm (sm i) (sm j)) (c2 : ∀ i, Comm ST (sm i)) (c3 : ∀ i j, Comm (sc i) (sm j))
    (c4 : ∀ i, Comm ST (sc i)) (c7 : ∀ i j, Comm (sm i) (sc j))
    (rv : (i : Nat) → Nat × Nat × Nat × Nat → X i → V i)
    (pts : (i : Nat) → C i → X i → Nat × Nat × Nat × Nat) (cv : (i : Nat) → C i → Nat × Nat × Nat × Nat)
    (sv : (i : Nat) → Nat × Nat × Nat × Nat → C i → X i → V i)
    (ε δ : Nat → Nat)
    (hzk : ∀ i, ZKBT ST (K i) (sm i) (sc i) (rv i) (fun H c x => prog4 K1 K2 K3 K4 H (pts i c x) (cv i c)) (sv i) (ε i))
    (nxt : (n : Nat) → VQ V n → List Nat → Nat × Nat × Unit)
    (ok : (i : Nat) → C i → Bool) (hok : ∀ i (f g : C i → Nat), (∀ c, ok i c = true → f c ≤ g c) → sc i f ≤ sc i g)
    (hcv : ∀ i c, ok i c = true → (cv i c).1 < K1 ∧ (cv i c).2.1 < K2 ∧ (cv i c).2.2.1 < K3 ∧ (cv i c).2.2.2 < K4)
    (col : (n : Nat) → Nat × Nat × Nat × Nat → C n → X n → PowD X n → Bool)
    (hread : ∀ n H ca xa xb, ok n ca = true → col n H ca xa xb = false →
      rvQ K1 K2 K3 K4 kq rv nxt n (prog4 K1 K2 K3 K4 H (pts n ca xa) (cv n ca)) xb = rvQ K1 K2 K3 K4 kq rv nxt n H xb)
    (hcol : ∀ n, sc n (fun ca => sm n (fun xa => ST (fun H => smPowD sm n (fun xb => indB (col n H ca xa xb ||
      (advRd K1 K2 K3 K4 kq (nxt n (rvQ K1 K2 K3 K4 kq rv nxt n H xb)) H).any
        (fun r => decide (coord4 r.1 (pts n ca xa) = r.2))))))) ≤ δ n) :
    ∀ n, ZKBT ST (KPowD K n) (smPowD sm n) (scPowD sc n) (rvQ K1 K2 K3 K4 kq rv nxt n)
      (pgPowD (fun i H c x => prog4 K1 K2 K3 K4 H (pts i c x) (cv i c)) n)
      (svQ K1 K2 K3 K4 kq pts cv sv nxt n) (errPowD K sm sc ε δ n)
  | 0 => fun E => by
    show 1 * ST (fun H => indB (E H ())) ≤ ST (fun H => indB (E H ())) + 0
    rw [Nat.one_mul, Nat.add_zero]; exact Nat.le_refl _
  | n + 1 => by
    have ih := zkbT_powQ h1 h2 h3 h4 K ST hST sm hs sc hc c1 c2 c3 c4 c7 rv pts cv sv ε δ hzk nxt ok hok hcv col
      hread hcol n
    exact zkbT_post_pair h1 h2 h3 h4 ST hST (sm n) (hs n) (smPowD sm n) (lin_smPowD hs n) (sc n) (hc n) (scPowD sc n)
      (comm_smPowD' (fun i => c1 n i) n) (comm_smPowD' c2 n) (comm_smPowD' (fun i => c3 n i) n) (c4 n) (c2 n)
      (comm_scPowD' (fun i => c7 n i) n)
      (rv n) (pts n) (cv n) (sv n) (rvQ K1 K2 K3 K4 kq rv nxt n)
      (pgPowD (fun i H c x => prog4 K1 K2 K3 K4 H (pts i c x) (cv i c)) n) (svQ K1 K2 K3 K4 kq pts cv sv nxt n)
      (hzk n) ih (nxt n) (col n) (ok n) (hok n) (hcv n) (hread n) (hcol n)

end Circuit
