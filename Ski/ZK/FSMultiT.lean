import Ski.ZK.ROMFSRead4

/-!
# Several proofs under one oracle, the views reading the tables

`FSMulti` composes proofs whose views read the oracle tables only at their
own messages, so another proof's programming changes a view only where the
messages hit its points (`read4_beside`).  Here the views may read the
tables beyond their messages.  A simulated view reads the tables before its
own proof's programming (`ZKBT`), and the composition carries that through
(`fs_twoT`, `zkbT_pair`, `zkbT_powD`).  A real output reads the tables at
points it flags (`hq`): a programming those reads miss leaves it unchanged
(`read4T_beside`), and a read that hits another proof's programmed point
carries the reader's first message, as its messages do, so the collision
bound is unchanged (`read4T_powD`).  One proof's four rounds take this shape
with its openings reading the tables (`fs_open4_absT`, over `fs_open4T`).

Limits.  `hq`, `hout` and `hpq` are hypotheses: no circuit's openings
discharge them yet.  `hpq` holds only for reads at points whose low digit
is the reader's first commitment (an opening reading a whole table cannot
meet it; one reading `rget K2 (m1 x + n1 k) H.2` can), so each opening's
reads must be confined to such points (a read fixed before that commitment
is absorbed breaks it).  The distinguisher sees the final tables and the
views; queries made before a proof's programming are `FSMultiQueries`'
(`zkbT_queries`), and queries interleaved with several proofs are not
modelled.  The statements are fixed in advance, and the
simulator's witness-freedom is each instance's to check.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **`fs_two` with the simulators' views reading the tables** (`svA H`,
    `svB H`), each the tables before its own programming:
    the tables `T` counted by `ST`; proof A with randomness counted by
    `smA`, real view `rvA H xa` read from the tables, simulator challenges
    counted by `SCA`, its programming `pgA H ca xa` and view `svA ca xa`;
    the same for B.  Each proof's own bound against every event of the
    tables and its view (`hA`, `hB`).  The second proof's real view on the
    first's programmed tables is its view on the tables themselves unless
    its messages hit the first's programmed answers (`col`, `hread`).  The
    real count with both proofs reading the tables is within both errors
    and the collisions of the simulators', B programmed and then A. -/
theorem fs_twoT {T XA XB CA CB VA VB : Type} {KA KB εA εB : Nat}
    (ST : (T → Nat) → Nat) (hST : Lin ST)
    (smA : (XA → Nat) → Nat) (hsA : Lin smA) (smB : (XB → Nat) → Nat) (hsB : Lin smB)
    (SCA : (CA → Nat) → Nat) (hcA : Lin SCA) (SCB : (CB → Nat) → Nat)
    (c1 : Comm smA smB) (c2 : Comm ST smB) (c3 : Comm SCA smB) (c4 : Comm ST SCA) (c5 : Comm ST smA)
    (rvA : T → XA → VA) (pgA : T → CA → XA → T) (svA : T → CA → XA → VA)
    (rvB : T → XB → VB) (pgB : T → CB → XB → T) (svB : T → CB → XB → VB)
    (hA : ∀ E : T → VA → Bool, KA * ST (fun H => smA (fun x => indB (E H (rvA H x)))) ≤
      ST (fun H => SCA (fun c => smA (fun x => indB (E (pgA H c x) (svA H c x))))) + εA)
    (hB : ∀ E : T → VB → Bool, KB * ST (fun H => smB (fun x => indB (E H (rvB H x)))) ≤
      ST (fun H => SCB (fun c => smB (fun x => indB (E (pgB H c x) (svB H c x))))) + εB)
    (col : T → CA → XA → XB → Bool) (okA : CA → Bool)
    (hokA : ∀ f g : CA → Nat, (∀ c, okA c = true → f c ≤ g c) → SCA f ≤ SCA g)
    (hread : ∀ H ca xa xb, okA ca = true → col H ca xa xb = false → rvB (pgA H ca xa) xb = rvB H xb)
    (E : T → VA → VB → Bool) :
    KB * (KA * ST (fun H => smB (fun xb => smA (fun xa => indB (E H (rvA H xa) (rvB H xb)))))) ≤
      SCA (fun ca => smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb =>
        indB (E (pgA (pgB H cb xb) ca xa) (svA (pgB H cb xb) ca xa) (svB H cb xb))))))) +
      KB * (εA * smB (fun _ => 1)) + εB * SCA (fun _ => smA (fun _ => 1)) +
      KB * SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => indB (col H ca xa xb))))) := by
  -- the first proof simulated, the second real on the programmed tables
  have s1 : KA * ST (fun H => smB (fun xb => smA (fun xa => indB (E H (rvA H xa) (rvB H xb))))) ≤
      smB (fun xb => ST (fun H => SCA (fun ca => smA (fun xa =>
        indB (E (pgA H ca xa) (svA H ca xa) (rvB (pgA H ca xa) xb)))))) + εA * smB (fun _ => 1) := by
    rw [← c2 (fun H xb => smA (fun xa => indB (E H (rvA H xa) (rvB H xb)))), ← smK smB hsB]
    refine Nat.le_trans (sm_mono smB hsB (fun xb => hA (fun H v => E H v (rvB H xb)))) (Nat.le_of_eq ?_)
    rw [sm_add smB hsB, smC smB hsB]
  -- the second proof's reads off the first's programming, but for collisions
  have hpt : ∀ H ca xa xb, okA ca = true → indB (E (pgA H ca xa) (svA H ca xa) (rvB (pgA H ca xa) xb)) ≤
      indB (E (pgA H ca xa) (svA H ca xa) (rvB H xb)) + indB (col H ca xa xb) := fun H ca xa xb hok => by
    cases hc : col H ca xa xb
    · rw [hread H ca xa xb hok hc]; exact Nat.le_add_right _ _
    · exact Nat.le_trans (indB_le _) (Nat.le_add_left _ _)
  let g2 := fun (H : T) (ca : CA) (xa : XA) (xb : XB) => indB (E (pgA H ca xa) (svA H ca xa) (rvB H xb))
  let cl := fun (H : T) (ca : CA) (xa : XA) (xb : XB) => indB (col H ca xa xb)
  let sim := fun (H : T) (ca : CA) (xa : XA) (cb : CB) (xb : XB) =>
    indB (E (pgA (pgB H cb xb) ca xa) (svA (pgB H cb xb) ca xa) (svB H cb xb))
  have s2 : smB (fun xb => ST (fun H => SCA (fun ca => smA (fun xa =>
        indB (E (pgA H ca xa) (svA H ca xa) (rvB (pgA H ca xa) xb)))))) ≤
      SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) := by
    refine Nat.le_trans (sm_mono smB hsB (fun xb => sm_mono ST hST (fun H => hokA _ _ (fun ca hok =>
      sm_mono smA hsA (fun xa => hpt H ca xa xb hok))))) (Nat.le_of_eq ?_)
    calc smB (fun xb => ST (fun H => SCA (fun ca => smA (fun xa => g2 H ca xa xb + cl H ca xa xb))))
        = ST (fun H => smB (fun xb => SCA (fun ca => smA (fun xa => g2 H ca xa xb + cl H ca xa xb)))) :=
          c2 (fun H xb => SCA (fun ca => smA (fun xa => g2 H ca xa xb + cl H ca xa xb)))
      _ = ST (fun H => SCA (fun ca => smB (fun xb => smA (fun xa => g2 H ca xa xb + cl H ca xa xb)))) :=
          congrArg ST (funext fun H => c3 (fun ca xb => smA (fun xa => g2 H ca xa xb + cl H ca xa xb)))
      _ = ST (fun H => SCA (fun ca => smA (fun xa => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) :=
          congrArg ST (funext fun H => congrArg SCA (funext fun ca => c1 (fun xa xb => g2 H ca xa xb + cl H ca xa xb)))
      _ = SCA (fun ca => ST (fun H => smA (fun xa => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) :=
          (c4 (fun H ca => smA (fun xa => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))).symm
      _ = _ := congrArg SCA (funext fun ca => (c5 (fun H xa => smB (fun xb => g2 H ca xa xb + cl H ca xa xb))).symm)
  have s3 : KB * SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) ≤
      SCA (fun ca => smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb))))) +
      εB * SCA (fun _ => smA (fun _ => 1)) +
      KB * SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => cl H ca xa xb)))) := by
    have hpc : ∀ ca xa, KB * ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)) ≤
        ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb))) + εB +
          KB * ST (fun H => smB (fun xb => cl H ca xa xb)) := fun ca xa => by
      have e : ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)) =
          ST (fun H => smB (fun xb => g2 H ca xa xb)) + ST (fun H => smB (fun xb => cl H ca xa xb)) := by
        rw [← sm_add ST hST]; exact congrArg ST (funext fun H => sm_add smB hsB _ _)
      rw [e, Nat.mul_add]
      exact Nat.add_le_add_right (hB (fun H v => E (pgA H ca xa) (svA H ca xa) v)) _
    calc KB * SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb))))
        = SCA (fun ca => smA (fun xa => KB * ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) := by
          rw [← smK SCA hcA]; exact congrArg SCA (funext fun ca => (smK smA hsA _ _).symm)
      _ ≤ SCA (fun ca => smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb))) + εB +
            KB * ST (fun H => smB (fun xb => cl H ca xa xb)))) :=
          sm_mono SCA hcA (fun ca => sm_mono smA hsA (fun xa => hpc ca xa))
      _ = _ := by
        have e1 : ∀ ca, smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb))) + εB +
            KB * ST (fun H => smB (fun xb => cl H ca xa xb))) =
            smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb => sim H ca xa cb xb)))) + εB * smA (fun _ => 1) +
              KB * smA (fun xa => ST (fun H => smB (fun xb => cl H ca xa xb))) := fun ca => by
          rw [sm_add smA hsA, sm_add smA hsA, smC smA hsA, smK smA hsA]
        rw [congrArg SCA (funext e1), sm_add SCA hcA, sm_add SCA hcA, smK SCA hcA, smK SCA hcA]
  calc KB * (KA * ST (fun H => smB (fun xb => smA (fun xa => indB (E H (rvA H xa) (rvB H xb))))))
      ≤ KB * (SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => g2 H ca xa xb + cl H ca xa xb)))) +
          εA * smB (fun _ => 1)) := Nat.mul_le_mul_left _ (Nat.le_trans s1 (Nat.add_le_add_right s2 _))
    _ ≤ _ := by
      rw [Nat.mul_add]
      have := Nat.add_le_add_right s3 (KB * (εA * smB (fun _ => 1)))
      refine Nat.le_trans this (Nat.le_of_eq ?_)
      ac_rfl

/-- **`ZKB` with the simulator's view reading the tables**: `sv H c x`, the
    tables before its programming `pg H c x`. -/
def ZKBT {T X C V : Type} (ST : (T → Nat) → Nat) (K : Nat) (sm : (X → Nat) → Nat) (SC : (C → Nat) → Nat)
    (rv : T → X → V) (pg : T → C → X → T) (sv : T → C → X → V) (ε : Nat) : Prop :=
  ∀ E : T → V → Bool, K * ST (fun H => sm (fun x => indB (E H (rv H x)))) ≤
    ST (fun H => SC (fun c => sm (fun x => indB (E (pg H c x) (sv H c x))))) + ε

/-- **`zkb_pair` with the simulators' views reading the tables**: the pair's draws counted B over A, its
    challenges A over B, its view both views, the second proof's answers
    programmed and then the first's.  Its error is both errors over the
    other's draws and the collisions. -/
theorem zkbT_pair {T XA XB CA CB VA VB : Type} {KA KB εA εB δ : Nat}
    (ST : (T → Nat) → Nat) (hST : Lin ST)
    (smA : (XA → Nat) → Nat) (hsA : Lin smA) (smB : (XB → Nat) → Nat) (hsB : Lin smB)
    (SCA : (CA → Nat) → Nat) (hcA : Lin SCA) (SCB : (CB → Nat) → Nat)
    (c1 : Comm smA smB) (c2 : Comm ST smB) (c3 : Comm SCA smB) (c4 : Comm ST SCA) (c5 : Comm ST smA)
    (c7 : Comm smA SCB)
    (rvA : T → XA → VA) (pgA : T → CA → XA → T) (svA : T → CA → XA → VA)
    (rvB : T → XB → VB) (pgB : T → CB → XB → T) (svB : T → CB → XB → VB)
    (hA : ZKBT ST KA smA SCA rvA pgA svA εA) (hB : ZKBT ST KB smB SCB rvB pgB svB εB)
    (col : T → CA → XA → XB → Bool) (okA : CA → Bool)
    (hokA : ∀ f g : CA → Nat, (∀ c, okA c = true → f c ≤ g c) → SCA f ≤ SCA g)
    (hread : ∀ H ca xa xb, okA ca = true → col H ca xa xb = false → rvB (pgA H ca xa) xb = rvB H xb)
    (hcol : SCA (fun ca => smA (fun xa => ST (fun H => smB (fun xb => indB (col H ca xa xb))))) ≤ δ) :
    ZKBT ST (KB * KA) (fun f : XA × XB → Nat => smB (fun xb => smA (fun xa => f (xa, xb))))
      (fun g : CA × CB → Nat => SCA (fun ca => SCB (fun cb => g (ca, cb))))
      (fun H x => (rvA H x.1, rvB H x.2)) (fun H c x => pgA (pgB H c.2 x.2) c.1 x.1)
      (fun H c x => (svA (pgB H c.2 x.2) c.1 x.1, svB H c.2 x.2))
      (KB * (εA * smB (fun _ => 1)) + εB * SCA (fun _ => smA (fun _ => 1)) + KB * δ) := by
  intro E
  have h := fs_twoT ST hST smA hsA smB hsB SCA hcA SCB c1 c2 c3 c4 c5 rvA pgA svA rvB pgB svB hA hB col okA hokA
    hread (fun H a b => E H (a, b))
  rw [Nat.mul_assoc]
  refine Nat.le_trans h ?_
  have e : SCA (fun ca => smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb =>
      indB (E (pgA (pgB H cb xb) ca xa) (svA (pgB H cb xb) ca xa, svB H cb xb))))))) =
      ST (fun H => SCA (fun ca => SCB (fun cb => smB (fun xb => smA (fun xa =>
        indB (E (pgA (pgB H cb xb) ca xa) (svA (pgB H cb xb) ca xa, svB H cb xb))))))) := by
    let G := fun (ca : CA) (xa : XA) (H : T) (cb : CB) (xb : XB) =>
      indB (E (pgA (pgB H cb xb) ca xa) (svA (pgB H cb xb) ca xa, svB H cb xb))
    calc SCA (fun ca => smA (fun xa => ST (fun H => SCB (fun cb => smB (fun xb => G ca xa H cb xb)))))
        = SCA (fun ca => ST (fun H => smA (fun xa => SCB (fun cb => smB (fun xb => G ca xa H cb xb))))) :=
          congrArg SCA (funext fun ca => c5 (fun H xa => SCB (fun cb => smB (fun xb => G ca xa H cb xb))))
      _ = ST (fun H => SCA (fun ca => smA (fun xa => SCB (fun cb => smB (fun xb => G ca xa H cb xb))))) :=
          c4 (fun H ca => smA (fun xa => SCB (fun cb => smB (fun xb => G ca xa H cb xb))))
      _ = ST (fun H => SCA (fun ca => SCB (fun cb => smA (fun xa => smB (fun xb => G ca xa H cb xb))))) :=
          congrArg ST (funext fun H => congrArg SCA (funext fun ca =>
            (c7 (fun xa cb => smB (fun xb => G ca xa H cb xb))).symm))
      _ = _ := congrArg ST (funext fun H => congrArg SCA (funext fun ca => congrArg SCB (funext fun cb =>
            (c1 (fun xa xb => G ca xa H cb xb)).symm)))
  rw [e]
  have := Nat.mul_le_mul_left KB hcol
  dsimp only
  omega

/-- The simulators' views of `n` proofs, each reading the tables before its
    own programming, after the earlier proofs'. -/
def svPowDT {T : Type} {X C V : Nat → Type} (pg : (i : Nat) → T → C i → X i → T) (sv : (i : Nat) → T → C i → X i → V i) :
    (n : Nat) → T → PowD C n → PowD X n → PowD V n
  | 0, _, _, _ => ()
  | n + 1, H, c, x => (sv n (pgPowD pg n H c.2 x.2) c.1 x.1, svPowDT pg sv n H c.2 x.2)

/-- **`zkb_powD` with the simulators' views reading the tables**: proof `i` with its
    own draws, challenges, views, programming and bound; each pair of
    counts commuting.  Together they keep the bound, the error `errPowD`. -/
theorem zkbT_powD {T : Type} {X C V : Nat → Type} (K : Nat → Nat) (ST : (T → Nat) → Nat) (hST : Lin ST)
    (sm : (i : Nat) → (X i → Nat) → Nat) (hs : ∀ i, Lin (sm i))
    (sc : (i : Nat) → (C i → Nat) → Nat) (hc : ∀ i, Lin (sc i))
    (c1 : ∀ i j, Comm (sm i) (sm j)) (c2 : ∀ i, Comm ST (sm i)) (c3 : ∀ i j, Comm (sc i) (sm j))
    (c4 : ∀ i, Comm ST (sc i)) (c7 : ∀ i j, Comm (sm i) (sc j))
    (rv : (i : Nat) → T → X i → V i) (pg : (i : Nat) → T → C i → X i → T) (sv : (i : Nat) → T → C i → X i → V i)
    (ε δ : Nat → Nat) (hzk : ∀ i, ZKBT ST (K i) (sm i) (sc i) (rv i) (pg i) (sv i) (ε i))
    (ok : (i : Nat) → C i → Bool) (hok : ∀ i (f g : C i → Nat), (∀ c, ok i c = true → f c ≤ g c) → sc i f ≤ sc i g)
    (col : (n : Nat) → T → C n → X n → PowD X n → Bool)
    (hread : ∀ n H ca xa xb, ok n ca = true → col n H ca xa xb = false →
      rvPowD rv n (pg n H ca xa) xb = rvPowD rv n H xb)
    (hcol : ∀ n, sc n (fun ca => sm n (fun xa => ST (fun H => smPowD sm n (fun xb => indB (col n H ca xa xb))))) ≤
      δ n) :
    ∀ n, ZKBT ST (KPowD K n) (smPowD sm n) (scPowD sc n) (rvPowD rv n) (pgPowD pg n) (svPowDT pg sv n)
      (errPowD K sm sc ε δ n)
  | 0 => fun E => by
    show 1 * ST (fun H => indB (E H ())) ≤ ST (fun H => indB (E H ())) + 0
    rw [Nat.one_mul, Nat.add_zero]; exact Nat.le_refl _
  | n + 1 => by
    have ih := zkbT_powD K ST hST sm hs sc hc c1 c2 c3 c4 c7 rv pg sv ε δ hzk ok hok col hread hcol n
    exact zkbT_pair ST hST (sm n) (hs n) (smPowD sm n) (lin_smPowD hs n) (sc n) (hc n) (scPowD sc n)
      (comm_smPowD' (fun i => c1 n i) n) (comm_smPowD' c2 n) (comm_smPowD' (fun i => c3 n i) n) (c4 n) (c2 n)
      (comm_scPowD' (fun i => c7 n i) n)
      (rv n) (pg n) (sv n) (rvPowD rv n) (pgPowD pg n) (svPowDT pg sv n) (hzk n) ih (col n) (ok n) (hok n) (hread n)
      (hcol n)

/-- `read4` with the output reading the four tables too. -/
def read4T {X O : Type} (K1 K2 K3 K4 : Nat) (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat)
    (q : Nat → Nat → Nat → X → Nat) (out : Nat × Nat × Nat × Nat → Nat → Nat → Nat → Nat → X → O)
    (H : Nat × Nat × Nat × Nat) (x : X) : Nat × Nat × Nat × O :=
  (m1 x, m2 (rget K1 (m1 x) H.1) x, m3 (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1) x,
   out H (rget K4 (q (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1)
        (rget K3 (m3 (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1) x) H.2.2.1) x) H.2.2.2)
     (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1)
     (rget K3 (m3 (rget K1 (m1 x) H.1) (rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1) x) H.2.2.1) x)

/-- **A table-reading view reads the programmed tables as the tables, but
    for hits**: of its messages (`hit4`) or of the output's own reads
    (`hq`), the output unchanged by a programming of in-range answers its reads
    miss (`hout`). -/
theorem read4T_beside {X O : Type} {K1 K2 K3 K4 : Nat} (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3) (h4 : 0 < K4)
    (m1 : X → Nat) (m2 : Nat → X → Nat) (m3 : Nat → Nat → X → Nat) (q : Nat → Nat → Nat → X → Nat)
    (out : Nat × Nat × Nat × Nat → Nat → Nat → Nat → Nat → X → O)
    (hq : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → X → Bool)
    (hout : ∀ H p a c4 c1 c2 c3 x, a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4 → hq H p x = false →
      out (prog4 K1 K2 K3 K4 H p a) c4 c1 c2 c3 x = out H c4 c1 c2 c3 x)
    (H p a : Nat × Nat × Nat × Nat)
    (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (x : X)
    (hh : (hit4 K1 K2 K3 m1 m2 m3 q H p x || hq H p x) = false) :
    read4T K1 K2 K3 K4 m1 m2 m3 q out (prog4 K1 K2 K3 K4 H p a) x = read4T K1 K2 K3 K4 m1 m2 m3 q out H x := by
  rw [Bool.or_eq_false_iff] at hh
  obtain ⟨hh, hqf⟩ := hh
  have ho := hout H p a
  obtain ⟨b1, b2, b3, b4⟩ := ha
  simp only [hit4, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hh
  obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hh
  have e1 : rget K1 (m1 x) (rset K1 p.1 H.1 a.1) = rget K1 (m1 x) H.1 := rget_rset_ne h1 n1 b1
  have e2 : rget K2 (m2 (rget K1 (m1 x) H.1) x) (rset K2 p.2.1 H.2.1 a.2.1) =
      rget K2 (m2 (rget K1 (m1 x) H.1) x) H.2.1 := rget_rset_ne h2 n2 b2
  have e3 := rget_rset_ne (H := H.2.2.1) h3 n3 b3
  have e4 := rget_rset_ne (H := H.2.2.2) h4 n4 b4
  simp only [read4T]
  rw [ho _ _ _ _ _ ⟨b1, b2, b3, b4⟩ hqf]
  simp only [prog4, e1, e2, e3, e4]

/-- **`hout` is met by an output reading the tables**: one that reads the
    second table at a point `M x`, flagged where the programmed point is
    there.  (`hpq` then asks `M x` to carry the reader's first commitment as
    its low digit.) -/
theorem read2_hout {X O : Type} {K1 K2 K3 K4 : Nat} (h2 : 0 < K2) (M : X → Nat) (g : Nat → Nat → Nat → Nat → Nat → X → O)
    (H p a : Nat × Nat × Nat × Nat) (c4 c1 c2 c3 : Nat) (x : X)
    (ha : a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4) (hq : decide (p.2.1 = M x) = false) :
    (fun (T : Nat × Nat × Nat × Nat) c4 c1 c2 c3 x => g (rget K2 (M x) T.2.1) c4 c1 c2 c3 x)
      (prog4 K1 K2 K3 K4 H p a) c4 c1 c2 c3 x =
    (fun (T : Nat × Nat × Nat × Nat) c4 c1 c2 c3 x => g (rget K2 (M x) T.2.1) c4 c1 c2 c3 x) H c4 c1 c2 c3 x := by
  have hne : M x ≠ p.2.1 := fun e => by rw [e] at hq; simp at hq
  show g (rget K2 (M x) (rset K2 p.2.1 H.2.1 a.2.1)) c4 c1 c2 c3 x = g (rget K2 (M x) H.2.1) c4 c1 c2 c3 x
  rw [rget_rset_ne h2 hne ha.2.1]

/-- **`n` four-round proofs under one oracle, the views reading the
    tables** (`read4_powD` over `read4T` and `ZKBT`): each real output's
    reads of the tables are flagged by `hq`, the output unchanged by a
    programming its reads miss (`hout`), and a read that hits another
    proof's programmed point carries the reader's first message (`hpq`), as
    its messages do; the collision bound is `read4_powD`'s.  Each simulated
    view reads the tables before its proof's programming. -/
theorem read4T_powD {X C O : Type} {K1 K2 K3 K4 : Nat} (K : Nat → Nat) (h1 : 0 < K1) (h2 : 0 < K2) (h3 : 0 < K3)
    (h4 : 0 < K4)
    (ST : (Nat × Nat × Nat × Nat → Nat) → Nat) (hST : Lin ST)
    (sm : Nat → (X → Nat) → Nat) (hs : ∀ i, Lin (sm i)) (sc : (C → Nat) → Nat) (hc : Lin sc)
    (c1 : ∀ i j, Comm (sm i) (sm j)) (c2 : ∀ i, Comm ST (sm i)) (c3 : ∀ i, Comm sc (sm i)) (c4 : Comm ST sc)
    (c7 : ∀ i, Comm (sm i) sc)
    (m1 : Nat → X → Nat) (m2 : Nat → Nat → X → Nat) (m3 : Nat → Nat → Nat → X → Nat)
    (q : Nat → Nat → Nat → Nat → X → Nat) (out : Nat → Nat × Nat × Nat × Nat → Nat → Nat → Nat → Nat → X → O)
    (hq : Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → X → Bool)
    (hout : ∀ i H p a c4 c1 c2 c3 x, a.1 < K1 ∧ a.2.1 < K2 ∧ a.2.2.1 < K3 ∧ a.2.2.2 < K4 → hq i H p x = false →
      out i (prog4 K1 K2 K3 K4 H p a) c4 c1 c2 c3 x = out i H c4 c1 c2 c3 x)
    (pts : Nat → C → X → Nat × Nat × Nat × Nat) (cv : C → Nat × Nat × Nat × Nat)
    (sv : Nat → Nat × Nat × Nat × Nat → C → X → Nat × Nat × Nat × O) (ε : Nat → Nat)
    (hzk : ∀ i, ZKBT ST (K i) (sm i) sc (read4T K1 K2 K3 K4 (m1 i) (m2 i) (m3 i) (q i) (out i))
      (fun H c x => prog4 K1 K2 K3 K4 H (pts i c x) (cv c)) (sv i) (ε i))
    (ok : C → Bool) (hok : ∀ f g : C → Nat, (∀ c, ok c = true → f c ≤ g c) → sc f ≤ sc g)
    (hcv : ∀ c, ok c = true → (cv c).1 < K1 ∧ (cv c).2.1 < K2 ∧ (cv c).2.2.1 < K3 ∧ (cv c).2.2.2 < K4)
    (hp2 : ∀ j n c xa c1 x, m2 j c1 x = (pts n c xa).2.1 → m1 j x = (pts n c xa).1)
    (hp3 : ∀ j n c xa c1 c2 x, m3 j c1 c2 x = (pts n c xa).2.2.1 → m1 j x = (pts n c xa).1)
    (hp4 : ∀ j n c xa c1 c2 c3 x, q j c1 c2 c3 x = (pts n c xa).2.2.2 → m1 j x = (pts n c xa).1)
    (hpq : ∀ j n c xa H x, hq j H (pts n c xa) x = true → m1 j x = (pts n c xa).1)
    (δ₀ : Nat → Nat) (hsp : ∀ j v, sm j (fun x => indB (decide (m1 j x = v))) ≤ δ₀ j) :
    ∀ n, ZKBT ST (KPowD K n) (smPowD (X := fun _ => X) sm n) (scPowD (C := fun _ => C) (fun _ => sc) n)
      (rvPowD (fun i => read4T K1 K2 K3 K4 (m1 i) (m2 i) (m3 i) (q i) (out i)) n)
      (pgPowD (fun i H c x => prog4 K1 K2 K3 K4 H (pts i c x) (cv c)) n) (svPowDT (fun i H c x => prog4 K1 K2 K3 K4 H (pts i c x) (cv c)) sv n)
      (errPowD K sm (fun _ => sc) ε (fun j => sc (fun _ => sm j (fun _ => ST (fun _ => hitBD sm δ₀ j)))) n) := by
  let hit := fun (n : Nat) (H : Nat × Nat × Nat × Nat) (c : C) (xa : X) (j : Nat) (x : X) =>
    hit4 K1 K2 K3 (m1 j) (m2 j) (m3 j) (q j) H (pts n c xa) x || hq j H (pts n c xa) x
  have hread : ∀ n H ca xa xb, ok ca = true → hitPowD (hit n H ca xa) n xb = false →
      rvPowD (fun i => read4T K1 K2 K3 K4 (m1 i) (m2 i) (m3 i) (q i) (out i)) n
        (prog4 K1 K2 K3 K4 H (pts n ca xa) (cv ca)) xb =
      rvPowD (fun i => read4T K1 K2 K3 K4 (m1 i) (m2 i) (m3 i) (q i) (out i)) n H xb :=
    fun n H ca xa xb hok hx => readPowD _ H _ (hit n H ca xa)
      (fun j x hj => read4T_beside h1 h2 h3 h4 (m1 j) (m2 j) (m3 j) (q j) (out j) (hq j) (hout j) H (pts n ca xa)
        (cv ca) (hcv ca hok) x hj) n xb hx
  have hhit : ∀ n H ca xa j x, indB (hit n H ca xa j x) ≤ indB (decide (m1 j x = (pts n ca xa).1)) := by
    intro n H ca xa j x
    cases hh : hit n H ca xa j x
    · exact Nat.zero_le _
    · have e : m1 j x = (pts n ca xa).1 := by
        simp only [hit, hit4, Bool.or_eq_true, decide_eq_true_eq] at hh
        rcases hh with (((e | e) | e) | e) | e
        · exact e
        · exact hp2 j n ca xa _ x e
        · exact hp3 j n ca xa _ _ x e
        · exact hp4 j n ca xa _ _ _ x e
        · exact hpq j n ca xa H x e
      have ed : decide (m1 j x = (pts n ca xa).1) = true := decide_eq_true e
      rw [ed]; exact Nat.le_refl _
  have hcol : ∀ n, sc (fun ca => sm n (fun xa => ST (fun H => smPowD (X := fun _ => X) sm n (fun xb =>
      indB (hitPowD (hit n H ca xa) n xb))))) ≤ sc (fun _ => sm n (fun _ => ST (fun _ => hitBD sm δ₀ n))) :=
    fun n => sm_mono sc hc (fun ca => sm_mono (sm n) (hs n) (fun xa => sm_mono ST hST (fun H =>
      hitPowD_le hs (hit n H ca xa) (fun j => Nat.le_trans (sm_mono (sm j) (hs j) (hhit n H ca xa j))
        (hsp j _)) n)))
  exact zkbT_powD (X := fun _ => X) (C := fun _ => C) K ST hST sm hs (fun _ => sc) (fun _ => hc) c1 c2
    (fun _ j => c3 j) (fun _ => c4) (fun i _ => c7 i)
    (fun i => read4T K1 K2 K3 K4 (m1 i) (m2 i) (m3 i) (q i) (out i))
    (fun i H c x => prog4 K1 K2 K3 K4 H (pts i c x) (cv c)) sv ε _ hzk (fun _ => ok) (fun _ => hok)
    (fun n H ca xa xb => hitPowD (hit n H ca xa) n xb) hread hcol



set_option maxRecDepth 100000 in
/-- **`fs_open4T` in `ZKBT`'s shape**, the openings reading the tables: the four tables one, counted by `ST`,
    the four challenges one, counted by `SC`; the real view reads the
    tables, the simulator programs them. -/
theorem fs_open4_absT {PV PB D1 O1 P1 D2 O2 P2 D3 O3 P3 W : Type} {NR m e1 e2 NS1 NS2 NS3 K2 K3 K4 n1 n2 n3 : Nat}
    (hK2 : 0 < K2) (hK3 : 0 < K3) (hK4 : 0 < K4)
    (φ : Nat → W → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (rv sv : Nat → Nat → Nat → EF → EF → Nat → (Nat → Tup) → TViewN PV PB) (gz : Nat → Nat → Bool)
    {Bz : Nat} (hgz : sumTo K2 (fun c2 => sumTo K3 (fun c3 => indB (!gz c2 c3))) ≤ Bz)
    (g4 : Nat → Bool) {B4 : Nat} (hB4 : sumTo K4 (fun c4 => indB (!g4 c4)) ≤ B4)
    (hrv : ∀ c4 c2 c3 α β r t, rv c4 c2 c3 α β r t = none ∨ ∃ p x y, rv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (hsv : ∀ c4 c2 c3 α β r t, ∃ p x y, sv c4 c2 c3 α β r t = some (p, α, β, x, y))
    (oz : TViewN PV PB → W) (hoz : ∀ c4 c2 c3 α β r t, oz (rv c4 c2 c3 α β r t) = oz (rv 0 c2 c3 α β r t))
    (h1 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) + e1 + e2)
    (h2 : ∀ c4 c2 c3, g4 c4 = true → gz c2 c3 = true → ∀ E : TViewN PV PB → Bool,
      tsumN NR m (fun α β r t => indB (genB β && E (sv c4 c2 c3 α β r t))) ≤
        tsumN NR m (fun α β r t => indB (genB β && E (rv c4 c2 c3 α β r t))) + e1 + e2)
    (Com1 : D1 → Nat → Nat) 
    (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → D1 → Nat → P1) (op1 : Nat → D1 → O1) (sd1 : Nat → O1 → D1) (d1 : D1)
    (hc1 : ComHides NS1 Com1) 
    (hp1 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS1 Com1 (Pf1 c4 T1 T2 T3 T4 M) (op1 c4)) (hr1 : ∀ d σ, Com1 d σ < n1)
    (ov1 : Nat → TViewN PV PB → Option O1) (hov1 : ∀ c4, ov1 c4 none = none) (main1 : (Nat → Tup) → Nat → D1)
    (hsd1 : ∀ c4 t r, op1 c4 (sd1 c4 (op1 c4 (main1 t r))) = op1 c4 (main1 t r))
    (Com2 : D2 → Nat → Nat) 
    (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → D2 → Nat → P2) (op2 : Nat → D2 → O2) (sd2 : Nat → O2 → D2) (d2 : D2)
    (hc2 : ComHides NS2 Com2) 
    (hp2 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS2 Com2 (Pf2 c4 T1 T2 T3 T4 M) (op2 c4)) (hr2 : ∀ d σ, Com2 d σ < n2)
    (ov2 : Nat → TViewN PV PB → Option O2) (hov2 : ∀ c4, ov2 c4 none = none) (main2 : Nat → (Nat → Tup) → Nat → D2)
    (hsd2 : ∀ c4 c t r, op2 c4 (sd2 c4 (op2 c4 (main2 c t r))) = op2 c4 (main2 c t r))
    (Com3 : D3 → Nat → Nat) 
    (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → D3 → Nat → P3) (op3 : Nat → D3 → O3) (sd3 : Nat → O3 → D3) (d3 : D3)
    (hc3 : ComHides NS3 Com3) 
    (hp3 : ∀ c4 T1 T2 T3 T4 M, ComPfHides NS3 Com3 (Pf3 c4 T1 T2 T3 T4 M) (op3 c4)) (hr3 : ∀ d σ, Com3 d σ < n3)
    (ov3 : Nat → TViewN PV PB → Option O3) (hov3 : ∀ c4, ov3 c4 none = none) (main3 : Nat → Nat → (Nat → Tup) → Nat → D3)
    (hsd3 : ∀ c4 c c' t r, op3 c4 (sd3 c4 (op3 c4 (main3 c c' t r))) = op3 c4 (main3 c c' t r))
    (hvo1 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op1 c4 (main1 t r)))
    (hvo2 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op2 c4 (main2 c t r)))
    (hvo3 : ∀ c4 c2 c3 c r t, rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3 c4 (rv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3 c4 (main3 c c2 t r)))
    (sop1 : Nat → Nat → Nat → Nat → (Nat → Tup) → O1) (sop2 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O2)
    (sop3 : Nat → Nat → Nat → Nat → Nat → (Nat → Tup) → O3)
    (hsvo1 : ∀ c4 c2 c3 c r t, ov1 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1 c4 c2 c3 r t))
    (hsvo2 : ∀ c4 c2 c3 c r t, ov2 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop2 c4 c2 c3 c r t))
    (hsvo3 : ∀ c4 c2 c3 c r t, ov3 c4 (sv c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop3 c4 c2 c3 c r t)) :
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1 (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN m (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + n1 * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 T1 T2 T3 T4 (m3 c1 c2 x) (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (Pf3 c4 T1 T2 T3 T4 (m3 c1 c2 x)) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 _c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * Com2 (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + n1 * comPair NS2 n2 Com2 Com3
        (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (T1 T2 T3 T4 c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x) (sd1 c4 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (Pf3 c4 T1 T2 T3 T4 (s3 c4 c1 c2 c3 x)) (sd2 c4 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       sv c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K3 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (oz (rv 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (K3 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo K3 (fun c3 => f (c1, c2, c3, c4)))))
    let rvT := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1 x, m2 (r1 (H.1, H.2.1, H.2.2.1, x)) x, m3 (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x)) x,
       rvo H.1 H.2.1 H.2.2.1 H.2.2.2 (rget K4 (Mq (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1 (H.1, H.2.1, H.2.2.1, x)) (r2 (H.1, H.2.1, H.2.2.1, x))
         (r3 (H.1, H.2.1, H.2.2.1, x)) x)
    let pgT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset K3 (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φ (s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x) (oz (sv c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2 c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3 c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svo (pgT H c x).1 (pgT H c x).2.1 (pgT H c x).2.2.1 (pgT H c x).2.2.2 c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1 × Option (P2 × P3) × TViewN PV PB) → Bool,
    K4 * (Q4 * Q4 * (K2 * K3)) * ST (fun H => sm (fun x => indB (E H (rvT H x)))) ≤
    ST (fun H => SC (fun c => sm (fun x => indB (E (pgT H c x) (svT H c x))))) +
      K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (K3 ^ (n1 * (n2 * n3)) *
        (K2 * (K3 * (NS1 * (NS2 * NS3 * (e1 + e2)))) +
          (Q4 * (P * P) * (K2 * K3) + Q4 * Q4 * Bz) * (NS1 * (NS2 * NS3 * (NR * (Q4 ^ m * 1)))))))) +
          B4 * (Q4 * Q4 * (K2 * K3) * sm4 (fun _ => 1))) := by
  intro sm m1 m2 m3 rvo s1 s2 s3 svo sm4 r1 r2 r3 Mq ST SC rvT pgT svT E
  have h := fs_open4T hK2 hK3 hK4 φ hφ rv sv gz hgz g4 hB4 hrv hsv oz hoz h1 h2 Com1 Pf1 op1 sd1 d1 hc1 hp1 hr1 ov1 hov1 main1 hsd1 Com2 Pf2 op2 sd2 d2 hc2 hp2 hr2 ov2 hov2 main2 hsd2 Com3 Pf3 op3 sd3 d3 hc3 hp3 hr3 ov3 hov3 main3 hsd3 hvo1 hvo2 hvo3 sop1 sop2 sop3 hsvo1 hsvo2 hsvo3 (fun H1 H2 H3 H4 a b c v => E (H1, H2, H3, H4) (a, b, c, v))
  rw [Nat.mul_assoc]
  refine Nat.le_trans h (Nat.add_le_add_right (Nat.le_of_eq ?_) _)
  refine sumTo_congr _ (fun H4 _ => ?_)
  rw [sumTo_exch _ ((Q4 * Q4) ^ n1) K4]
  refine sumTo_congr _ (fun H1 _ => ?_)
  rw [sumTo_exch _ (K2 ^ (n1 * n2)) K4]
  refine sumTo_congr _ (fun H2 _ => ?_)
  rw [sumTo_exch _ (K3 ^ (n1 * (n2 * n3))) K4]

end Circuit
