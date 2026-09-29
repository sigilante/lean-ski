import Ski.Circuit.ProbeSat

/-!
# The honest probe tables balance

The probe CPU's messages off `mem` are the jet CPU's, on the run that skips
the probe rows, and its probe messages (`PRun.cpuP_split`).  The jet
messages balance as in the jet circuit; the probe messages balance bus by
bus: each chain telescopes along its rows, and each lookup of a child is a
field its parent's end row pops, counted there.
-/

namespace Circuit

open B Air JetTable Mach

theorem foldr_acc_gen {α : Type} (f : α → F) (x : F) : ∀ l : List α,
    l.foldr (fun b acc => f b + acc) x = l.foldr (fun b acc => f b + acc) 0 + x
  | [] => (zero_add' x).symm
  | b :: l => by simp only [List.foldr_cons]; rw [foldr_acc_gen f x l, add_assoc']

/-- The probe messages a row sends on a bus. -/
def probeSendsAt (ρ : Atom → F) (bus : String) (v : List F) : F :=
  probeInters.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ) = v then
    I.count.eval ρ else 0) + acc) 0

/-- The jet messages vanish on a row neither instantiating nor looking up a root argument. -/
theorem jetPart_zero (ρ : Atom → F) (h1 : ρ (.main 0 (SEL + 11)) = 0) (h2 : ρ (.main 0 J_RA) = 0)
    (bus : String) (v : List F) :
    jetInters.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ) = v then
      I.count.eval ρ else 0) + acc) 0 = 0 := by
  simp only [jetInters, List.foldr_cons, List.foldr_nil, E.eval, sInst, B.col, h1, h2]
  have z : ∀ (P : Prop) [Decidable P], (if P then (0 : F) else 0) = 0 := fun P _ => by split <;> rfl
  have zn : ∀ (P : Prop) [Decidable P], (if P then -(0 : F) else 0) = 0 := fun P _ => by split <;> decide
  rw [z, z, z, zn, z, zn, z]
  decide

theorem interPart_congr {ρ ρ' : Atom → F} {p : Atom → Bool} (h : ∀ a, p a = true → ρ a = ρ' a)
    (bus : String) (v : List F) : ∀ L : List Inter,
    L.all (fun I => I.count.onlyAtoms p && I.fields.all (·.onlyAtoms p)) = true →
    L.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ) = v then I.count.eval ρ else 0) + acc) 0 =
      L.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ρ') = v then I.count.eval ρ' else 0) + acc) 0
  | [], _ => rfl
  | I :: L, hL => by
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at hL
    obtain ⟨⟨hc, hf⟩, hL⟩ := hL
    simp only [List.foldr_cons]
    rw [interPart_congr h bus v L hL, E.eval_congr h _ hc,
      List.map_congr_left (fun e he => E.eval_congr h e (hf e he))]

theorem jetInters_atoms : jetInters.all (fun I => I.count.onlyAtoms PRun.atomJJ && I.fields.all (·.onlyAtoms PRun.atomJJ)) =
    true := by decide

theorem pw_nowOnly : NowOnly pwAir := by
  have h : pwAir.inters.all (fun I => I.count.onlyAtoms nowAtom && I.fields.all (·.onlyAtoms nowAtom)) = true := rfl
  intro I hI
  have := List.all_eq_true.1 h I hI
  rw [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨this.1, this.2⟩

theorem pw_quiet : ZeroQuiet pwAir := by
  intro I hI
  simp only [pwAir, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl <;> decide

theorem pw_pwch (i c b k q : Nat) (v : List F) :
    rowSendsV pwAir "pwch" v (PRun.pwRow i c b k q) =
      ind ([ofN i, ofN c, ofN b, ofN k, ofN (q + 1)] = v) - ind ([ofN i, ofN c, ofN b, ofN k, ofN q] = v) := by
  simp only [rowSendsV, pwAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval,
    B.col, B.one, B.c, ofN_one, true_and]
  have ev : ∀ n, envOf (PRun.pwRow i c b k q) (.main 0 n) = (PRun.pwRow i c b k q).getD n 0 := fun _ => rfl
  rw [ev 0, ev 1, ev 2, ev 3, ev 4, ev 5]
  show (if [ofN i, ofN c, ofN b, ofN k, ofN q] = v then -(1 : F) else 0) +
    ((if [ofN i, ofN c, ofN b, ofN k, ofN q + 1] = v then (1 : F) else 0) +
    ((if "mem" = "pwch" ∧ _ then _ else 0) + ((if "mem" = "pwch" ∧ _ then _ else 0) + 0))) = _
  rw [if_neg (show ¬ ("mem" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)), add_zero', add_zero',
    ite_neg_one _ 1 rfl, ← ofN_one, ← ofN_add, ite_one _ (ofN 1) rfl, sub_eq_add_neg', add_comm', add_zero']

/-- The probe messages on `PWCH`. -/
theorem probeSends_pwch (ρ : Atom → F) (v : List F) :
    probeSendsAt ρ "pwch" v =
      (if [ρ (.main 0 J_CLK), ρ (.main 0 CTR), ρ (.main 0 S_BASE), ρ (.main 0 (S_BASE + 1)), 0] = v then
        ρ (.main 0 (SEL + 12)) + ρ (.main 0 (SEL + 13)) else 0) +
      (if [ρ (.main 0 J_CLK), ρ (.main 0 CTR), ρ (.main 0 S_BASE), ρ (.main 0 (S_BASE + 1)),
          ρ (.main 0 (S_BASE + 1))] = v then -(ρ (.main 0 (SEL + 12)) + ρ (.main 0 (SEL + 13))) else 0) := by
  unfold probeSendsAt
  simp only [probeInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col,
    B.c, sPLater, sProbe, sPFirst, true_and, ofN_zero, B.one, ofN_one]
  rw [if_neg (show ¬ ("plan" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("plan" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "pwch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

/-- The probe messages on `PLAN`. -/
theorem probeSends_plan (ρ : Atom → F) (v : List F) :
    probeSendsAt ρ "plan" v =
      (if ρ (.main 0 P_CNT) :: (List.range 6).map (fun i => ρ (.main 0 (S_BASE + i))) = v then
        ρ (.main 0 (SEL + 12)) + ρ (.main 0 (SEL + 13)) else 0) +
      (if (ρ (.main 0 P_CNT) - 1) :: (List.range 6).map (fun i => ρ (.main 0 (E_BASE + i))) = v then
        ρ (.main 0 (SEL + 13)) else 0) := by
  unfold probeSendsAt
  simp only [probeInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.map_map, E.eval, B.col,
    B.c, sPLater, sProbe, sPFirst, true_and, ofN_zero, B.one, ofN_one]
  rw [if_neg (show ¬ ("popch" = "plan" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "plan" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "plan" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "plan" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "plan" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "plan" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "plan" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "plan" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "plan" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']
  rfl

theorem ofN_ite (P : Prop) [Decidable P] : ofN (if P then 1 else 0) = if P then 1 else 0 := by
  split <;> rfl

theorem ite_and_left {P Q : Prop} [Decidable P] [Decidable Q] (hP : P) (a b : Nat) :
    (if P ∧ Q then a else b) = if Q then a else b := by
  rcases (inferInstance : Decidable Q) with hq | hq
  · rw [if_neg (fun h => hq h.2), if_neg hq]
  · rw [if_pos ⟨hP, hq⟩, if_pos hq]

theorem add_sub_right (a b : F) : a + b - b = a :=
  E.eval_eq_of_norm (e := .sub (.add (.atom (.main 0 0)) (.atom (.main 0 1))) (.atom (.main 0 1)))
    (e' := .atom (.main 0 0)) (by decide) (at4 a b 0 0)

theorem planRow_mem {plan : List Air.Seg} {j : Nat} {s : Air.Seg} (hs : plan[j]? = some s) :
    ofN j :: segCols s ∈ planRows plan :=
  padCopies_super (List.mem_map.2 ⟨(s, j), List.mem_zipIdx_iff_getElem?.2 hs, rfl⟩)

-- ---------------------------------------------------------------------------
-- Counting two ways
-- ---------------------------------------------------------------------------

theorem sumTo_comm (f : Nat → Nat → Nat) (n : Nat) : ∀ K,
    sumTo K (fun i => sumTo n (fun c => f i c)) = sumTo n (fun c => sumTo K (fun i => f i c))
  | 0 => (sumTo_eq_zero n (fun _ _ => rfl)).symm
  | K + 1 => by
    show sumTo K (fun i => sumTo n (fun c => f i c)) + sumTo n (fun c => f K c) = _
    rw [sumTo_comm f n K, ← sumTo_add]
    rfl

theorem sumTo_at {f : Nat → Nat} {x : Nat} : ∀ n, x < n → (∀ c, c < n → c ≠ x → f c = 0) → sumTo n f = f x
  | 0, hx, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, hx, h => by
    show sumTo n f + f n = f x
    rcases Nat.lt_or_ge x n with h' | h'
    · rw [sumTo_at n h' (fun c hc hne => h c (by omega) hne), h n (by omega) (by omega), Nat.add_zero]
    · have : x = n := by omega
      subst this
      rw [sumTo_eq_zero x (fun q hq => h q (by omega) (by omega)), Nat.zero_add]

theorem sumTo_mul_left (a : Nat) (f : Nat → Nat) : ∀ n, sumTo n (fun c => a * f c) = a * sumTo n f
  | 0 => rfl
  | n + 1 => by
    show sumTo n (fun c => a * f c) + a * f n = a * (sumTo n f + f n)
    rw [sumTo_mul_left a f n, Nat.mul_add]

theorem ite_mul_one (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then 1 else 0) * (if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  rcases (inferInstance : Decidable P) with hp | hp
  · rw [if_neg hp, if_neg (show ¬ (P ∧ Q) from fun h => hp h.1), Nat.zero_mul]
  · rw [if_pos hp, Nat.one_mul]
    rcases (inferInstance : Decidable Q) with hq | hq
    · rw [if_neg hq, if_neg (show ¬ (P ∧ Q) from fun h => hq h.2)]
    · rw [if_pos hq, if_pos (show P ∧ Q from ⟨hp, hq⟩)]

theorem sumTo_mul_right (a : Nat) (f : Nat → Nat) (n : Nat) : sumTo n (fun c => f c * a) = sumTo n f * a := by
  rw [Nat.mul_comm, ← sumTo_mul_left]
  exact sumTo_congr n (fun q _ => Nat.mul_comm _ _)

theorem ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) (a b : Nat) :
    (if P then a else b) = if Q then a else b := by
  rcases (inferInstance : Decidable Q) with hq | hq
  · rw [if_neg (fun hp => hq (h.1 hp)), if_neg hq]
  · rw [if_pos (h.2 hq), if_pos hq]

/-- The probe messages on `SEGEND`. -/
theorem probeSends_segend (ρ : Atom → F) (v : List F) :
    probeSendsAt ρ "segend" v =
      (if [ρ (.main 0 P_CNT) - 1, ρ (.main 0 J_CLK)] = v then -ρ (.main 0 P_NKIDS) else 0) +
      (if [ρ (.main 0 (S_BASE + 4)), ρ (.main 0 P_CLKP)] = v then ρ (.main 0 (SEL + 13)) else 0) := by
  unfold probeSendsAt
  simp only [probeInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col,
    B.c, sPLater, sProbe, sPFirst, true_and, ofN_zero, B.one, ofN_one]
  rw [if_neg (show ¬ ("plan" = "segend" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("plan" = "segend" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "segend" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "segend" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "segend" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "segend" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "segend" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "segend" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "segend" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

namespace PRun

variable {R : PRun} {t : Term} (hA : AcceptsP R.A (load t) R.roots R.jets R.plan R.p R.fld R.row)
include hA

/-- **The probe CPU's messages off `mem`**: the jet CPU's on the run that
    skips the probe rows, and the probe messages. -/
theorem cpuP_split {bus : String} (hb : bus ≠ "mem") {K : Nat} (v : List F) (hd0 stk0 ctr0 n la : Nat) :
    tableSends (cpuAirP hd0 stk0 ctr0 n la) (R.cpuTableP K) bus v =
      tableSends (cpuAirJ hd0 stk0 ctr0) (R.J.cpuTable K) bus v +
      (List.range K).foldr (fun i acc => probeSendsAt ((R.cpuTableP K).env i) bus v + acc) 0 := by
  unfold tableSends
  show (List.range K).foldr _ 0 = (List.range K).foldr _ 0 + _
  rw [fold_add2 (fun r => rowSends (cpuAirJ hd0 stk0 ctr0) (R.J.cpuTable K) bus v r)
    (fun i => probeSendsAt ((R.cpuTableP K).env i) bus v)]
  apply foldr_range_congr K
  intro i hi
  rw [cpuP_rowSends_off hb, List.foldr_append, foldr_acc_gen, cpu_rowSends_jet hb]
  congr 1
  have hi' : i < K := List.mem_range.1 (List.mem_range.2 hi)
  cases hp : R.isP i with
  | false =>
    exact interPart_congr (env_agreeP hA hi hp) bus v jetInters jetInters_atoms
  | true =>
    have e1 : (R.cpuTableP K).env i (.main 0 (SEL + 11)) = 0 := by
      show R.cpuColP K ((i + 0) % K) (SEL + 11) = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi, R.colP_sel hp (by decide)]
      rcases Nat.decEq i 0 with h0 | h0
      · rw [if_neg h0, if_neg (by decide)]
      · rw [if_pos h0, if_neg (by decide)]
    have e2 : (R.cpuTableP K).env i (.main 0 J_RA) = 0 := by
      show R.cpuColP K ((i + 0) % K) J_RA = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi, R.colP_jet hp (by decide) (by decide) (by decide)]
    have hn : R.J.instAt i = none := by
      unfold JRun.instAt; rw [if_pos (show R.J.skip i = true from hp)]
    have e3 : (R.J.cpuTable K).env i (.main 0 (SEL + 11)) = 0 := by
      show R.J.cpuCol ((i + 0) % K) (SEL + 11) = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
      unfold JRun.cpuCol; rw [hn]; simp only
      rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (by have := kindOf_lt R.J.A (R.J.rowQ i); omega)]
    have e4 : (R.J.cpuTable K).env i (.main 0 J_RA) = 0 := by
      show R.J.cpuCol ((i + 0) % K) J_RA = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
      unfold JRun.cpuCol; rw [hn]; simp only
      rw [if_neg (by decide), if_neg (by decide)]
    rw [jetPart_zero _ e1 e2, jetPart_zero _ e3 e4]

omit hA in
/-- **POP's messages**: the jet pops' and the probe pops'. -/
theorem popP_split {K HP : Nat} (hHP : (R.popRowsP K).length ≤ HP) (bus : String) (v : List F) :
    tableSends popAir (R.popTableP K HP) bus v =
      tableSends popAir (R.J.popTable K (R.J.popRows K).length) bus v +
      (List.range K).foldr (fun i acc => ((R.probePops i).map (rowSendsV popAir bus v)).foldr (· + ·) 0 + acc) 0 := by
  rw [show R.popTableP K HP = ⟨HP, ofRows (R.popRowsP K), fun _ _ => 0⟩ from rfl,
    show R.J.popTable K (R.J.popRows K).length =
      ⟨(R.J.popRows K).length, ofRows (R.J.popRows K), fun _ _ => 0⟩ from rfl,
    sends_rows pop_nowOnly pop_quiet hHP, sends_rows pop_nowOnly pop_quiet (Nat.le_refl _), popRowsP,
    JRun.popRows, foldr_flatMap, foldr_flatMap, fold_add2]
  apply foldr_range_congr K
  intro i _
  rw [popRowsAtP, List.map_append, List.foldr_append, foldr_flatMap.fold_acc' id]

omit hA in
/-- The probe messages on `POPCH`. -/
theorem probeSends_popch (ρ : Atom → F) (v : List F) :
    probeSendsAt ρ "popch" v =
      (if [ρ (.main 0 J_CLK), ρ (.main 0 CTR), 0, ρ (.main 0 STK)] = v then ρ (.main 0 (SEL + 13)) else 0) +
      (if [ρ (.main 0 J_CLK), ρ (.main 0 CTR), ρ (.main 0 (E_BASE + 3)), ρ (.main 0 E_REST)] = v then
        -ρ (.main 0 (SEL + 13)) else 0) := by
  unfold probeSendsAt
  simp only [probeInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col,
    B.c, sPLater, sProbe, sPFirst, true_and, ofN_zero, B.one, ofN_one]
  rw [if_neg (show ¬ ("plan" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("plan" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("segend" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("pwch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

variable (hroots : RootsOK (load t).heap R.roots R.jets)
include hroots

omit hroots in
/-- A later probe row's POP rows, along its pops. -/
theorem probePops_eq {i : Nat} (hp : R.isP i = true) (h0 : 0 < R.pcnt i) :
    ∃ σ ξ : Nat → Nat, σ 0 = (R.row i).stk ∧ σ (R.seg (R.pcnt i - 1)).arity = R.restE i ∧
      R.fld (R.pcnt i - 1) = (List.range (R.seg (R.pcnt i - 1)).arity).map ξ ∧
      R.probePops i = (List.range (R.seg (R.pcnt i - 1)).arity).map (fun f =>
        popRow i (R.row i).ctr f (σ f) (ξ f) (σ (f + 1)) (R.uses (R.pcnt i - 1) f)) ∧
      ∀ f, f < (R.seg (R.pcnt i - 1)).arity →
        rd R.A (R.row i).ctr (σ f) = some (.cons (ξ f) (σ (f + 1))) := by
  obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
  obtain ⟨_, hpops, _⟩ := later_end hA hjn h0
  rw [hpj] at hpops
  have hp' : popR (fun a => R.A[a]?) (R.row i).ctr (R.seg (R.pcnt i - 1)).arity (R.row i).stk =
      some (R.fld (R.pcnt i - 1), R.restE i) := hpops
  obtain ⟨σ, ξ, hs0, hsk, hps, hs⟩ := popsOf_spec (A := R.A) _ _ hp'
  refine ⟨σ, ξ, hs0, hsk, hps, ?_, fun f hf => (hs f hf).2⟩
  unfold probePops
  rw [if_pos ⟨hp, h0⟩]
  apply List.ext_getElem
  · rw [List.length_map, List.length_zipIdx, popsOf_length hp', List.length_map, List.length_range]
  · intro f h1 h2
    rw [List.length_map, List.length_range] at h2
    rw [List.getElem_map, List.getElem_map, List.getElem_zipIdx, List.getElem_range]
    have e := (hs f h2).1
    rw [List.getElem?_eq_some_iff] at e
    obtain ⟨_, e⟩ := e
    simp only [Nat.zero_add]
    rw [e]

omit hroots in
/-- At a row that is no later probe row, the probe CPU sends nothing on `POPCH`. -/
theorem sel13_zero {K i : Nat} (hi : i < K) (h : ¬ (R.isP i = true ∧ 0 < R.pcnt i)) :
    (R.cpuTableP K).env i (.main 0 (SEL + 13)) = 0 := by
  show R.cpuColP K ((i + 0) % K) (SEL + 13) = 0
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
  cases hp : R.isP i with
  | false => rw [R.colP_low hp (by decide), R.J_sel_probe i (.inr rfl)]
  | true =>
    have h0 : R.pcnt i = 0 := Nat.eq_zero_of_not_pos (fun hpos => h ⟨hp, hpos⟩)
    rw [R.colP_sel hp (by decide), if_pos ((pr_zero hA hp).2 h0), if_neg (by decide)]

/-- **The probe chains on `POPCH` telescope.** -/
theorem bal_popch_probe {K : Nat} (hK : R.last < K) (v : List F) :
    (List.range K).foldr (fun i acc => probeSendsAt ((R.cpuTableP K).env i) "popch" v + acc) 0 +
      (List.range K).foldr (fun i acc => ((R.probePops i).map (rowSendsV popAir "popch" v)).foldr (· + ·) 0 + acc) 0
      = 0 := by
  rw [fold_add2]
  apply foldr_zero_all
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [probeSends_popch]
  by_cases hc : R.isP i = true ∧ 0 < R.pcnt i
  · obtain ⟨hp, h0⟩ := hc
    obtain ⟨σ, ξ, hs0, hsk, _, hrows, _⟩ := probePops_eq hA hp h0
    have cv : ∀ c, (R.cpuTableP K).env i (.main 0 c) = R.cpuColP K i c := fun c => by
      show R.cpuColP K ((i + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi']
    obtain ⟨_, rCTR, _⟩ := pr_regs hA hK hp
    have rSTK : R.cpuColP K i STK = ofN (R.row i).stk := by
      rw [regP hA (by decide), JRun.rowQ_lt (by show i < R.last + 1; have := isP_lt hA hp; omega)]; rfl
    have hi0 : i ≠ 0 := fun e => by rw [(pr_zero hA hp).1 e] at h0; exact absurd h0 (by decide)
    have h13 : R.cpuColP K i (SEL + 13) = 1 := by
      rw [R.colP_sel hp (by decide), if_neg hi0, if_pos rfl]
    rw [cv, cv, cv, cv, cv, cv, h13, R.colP_clk' K i, rCTR, rSTK, R.colP_x hp (by decide), R.colP_x hp (by decide),
      R.probeX_E i h0 (m := 3) (by decide), R.probeX_rest i h0, ite_one _ 1 rfl, ite_neg_one _ 1 rfl]
    rw [hrows, foldr_map_range]
    let T : Nat → List F := fun f => [ofN i, ofN (R.row i).ctr, ofN f, ofN (σ f)]
    rw [foldr_range_congr _ (fun f _ => JRun.pop_popch i (R.row i).ctr f (σ f) (ξ f) (σ (f + 1))
      (R.uses (R.pcnt i - 1) f) v)]
    have tele := telescopeF T v (R.seg (R.pcnt i - 1)).arity
    simp only [T] at tele
    rw [tele, ← hs0, ← hsk, ← ofN_zero]
    show ind _ + -ind _ + (ind _ - ind _) = 0
    exact E.eval_eq_of_norm
      (e := .add (.add (.atom (.main 0 0)) (.neg (.atom (.main 0 1)))) (.sub (.atom (.main 0 1)) (.atom (.main 0 0))))
      (e' := .const (ofN 0)) (by decide) (at4 _ _ 0 0)
  · have hz := sel13_zero hA hi' hc
    rw [hz, ite_zero _ _ rfl, ite_neg_zero _ _ rfl, zero_add']
    unfold probePops
    rw [if_neg hc]; rfl

omit hroots in
/-- **The probe chains on `PWCH` telescope**: each probe row's markers. -/
theorem bal_pwch {K HW : Nat} (hK : R.last < K) (hHW : (R.pwRows K).length ≤ HW) (v : List F) :
    (List.range K).foldr (fun i acc => probeSendsAt ((R.cpuTableP K).env i) "pwch" v + acc) 0 +
      tableSends pwAir (R.pwTable K HW) "pwch" v = 0 := by
  rw [show R.pwTable K HW = ⟨HW, ofRows (R.pwRows K), fun _ _ => 0⟩ from rfl,
    sends_rows pw_nowOnly pw_quiet hHW, pwRows, foldr_flatMap, fold_add2]
  apply foldr_zero_all
  intro i hi
  have hi' := List.mem_range.1 hi
  have cv : ∀ c, (R.cpuTableP K).env i (.main 0 c) = R.cpuColP K i c := fun c => by
    show R.cpuColP K ((i + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi']
  rw [probeSends_pwch, cv, cv, cv, cv, cv, cv]
  cases hp : R.isP i with
  | true =>
    have hs : R.cpuColP K i (SEL + 12) + R.cpuColP K i (SEL + 13) = 1 := by
      rw [R.colP_sel hp (by decide), R.colP_sel hp (by decide)]
      rcases Nat.decEq i 0 with h0 | h0
      · rw [if_neg h0, if_neg (by decide), if_pos rfl, zero_add']
      · rw [if_pos h0, if_pos rfl, if_neg (by decide), add_zero']
    obtain ⟨_, rCTR, _⟩ := pr_regs hA hK hp
    rw [hs, R.colP_clk' K i, rCTR, R.colP_x hp (by decide), R.colP_x hp (by decide),
      show S_BASE = S_BASE + 0 from rfl, R.probeX_s i (m := 0) (by decide), R.probeX_s i (m := 1) (by decide),
      ite_one _ 1 rfl, ite_neg_one _ 1 rfl]
    have hrows : R.pwRowsAt i = (List.range (R.seg (R.pcnt i)).k).map fun q =>
        pwRow i (R.row i).ctr (R.seg (R.pcnt i)).base (R.seg (R.pcnt i)).k q := by
      unfold pwRowsAt; rw [if_pos hp]
    rw [hrows, foldr_map_range]
    let T : Nat → List F := fun q => [ofN i, ofN (R.row i).ctr, ofN (R.seg (R.pcnt i)).base, ofN (R.seg (R.pcnt i)).k, ofN q]
    rw [foldr_range_congr _ (fun q _ => pw_pwch i (R.row i).ctr (R.seg (R.pcnt i)).base (R.seg (R.pcnt i)).k q v)]
    have tele := telescopeF T v (R.seg (R.pcnt i)).k
    simp only [T] at tele
    rw [tele, ← ofN_zero]
    show ind _ + -ind _ + (ind _ - ind _) = 0
    exact E.eval_eq_of_norm
      (e := .add (.add (.atom (.main 0 0)) (.neg (.atom (.main 0 1)))) (.sub (.atom (.main 0 1)) (.atom (.main 0 0))))
      (e' := .const (ofN 0)) (by decide) (at4 _ _ 0 0)
  | false =>
    rw [R.colP_low hp (c := SEL + 12) (by decide), R.colP_low hp (c := SEL + 13) (by decide),
      R.J_sel_probe i (.inl rfl), R.J_sel_probe i (.inr rfl),
      add_zero', ite_zero _ _ rfl, ite_neg_zero _ _ rfl, zero_add']
    unfold pwRowsAt; rw [hp]; rfl

omit hA hroots in
theorem segCols_S {K i : Nat} (hi : i < K) (hp : R.isP i = true) :
    (List.range 6).map (fun m => (R.cpuTableP K).env i (.main 0 (S_BASE + m))) = segCols (R.seg (R.pcnt i)) := by
  have cv : ∀ c, (R.cpuTableP K).env i (.main 0 c) = R.cpuColP K i c := fun c => by
    show R.cpuColP K ((i + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
  simp only [range6, List.map_cons, List.map_nil, cv]
  rw [R.colP_x hp (by decide), R.colP_x hp (by decide), R.colP_x hp (by decide), R.colP_x hp (by decide),
    R.colP_x hp (by decide), R.colP_x hp (by decide), R.probeX_s i (m := 0) (by decide),
    R.probeX_s i (m := 1) (by decide), R.probeX_s i (m := 2) (by decide), R.probeX_s i (m := 3) (by decide),
    R.probeX_s i (m := 4) (by decide), R.probeX_s i (m := 5) (by decide)]
  rfl

omit hA hroots in
theorem segCols_E {K i : Nat} (hi : i < K) (hp : R.isP i = true) (h0 : 0 < R.pcnt i) :
    (List.range 6).map (fun m => (R.cpuTableP K).env i (.main 0 (E_BASE + m))) = segCols (R.seg (R.pcnt i - 1)) := by
  have cv : ∀ c, (R.cpuTableP K).env i (.main 0 c) = R.cpuColP K i c := fun c => by
    show R.cpuColP K ((i + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
  simp only [range6, List.map_cons, List.map_nil, cv]
  rw [R.colP_x hp (by decide), R.colP_x hp (by decide), R.colP_x hp (by decide), R.colP_x hp (by decide),
    R.colP_x hp (by decide), R.colP_x hp (by decide), R.probeX_E i h0 (m := 0) (by decide),
    R.probeX_E i h0 (m := 1) (by decide), R.probeX_E i h0 (m := 2) (by decide), R.probeX_E i h0 (m := 3) (by decide),
    R.probeX_E i h0 (m := 4) (by decide), R.probeX_E i h0 (m := 5) (by decide)]
  rfl

omit hroots in
/-- **`PLAN` balances**: the probe rows look up each plan row as often as
    the provider counts. -/
theorem bal_plan {K : Nat} (hK : R.last < K) (v : List F) :
    (List.range K).foldr (fun i acc => probeSendsAt ((R.cpuTableP K).env i) "plan" v + acc) 0 +
      tableSends (planAir R.plan) (provTable (planRows R.plan) (R.cntPlan K)) "plan" v = 0 := by
  rw [show planAir R.plan = providerAir "plan" 7 (planRows R.plan) from rfl, prov_sends (planRows_len R.plan)]
  apply bal_lookup
  · unfold cntPlan
    rw [← fold_ofN]
    apply foldr_range_congr K
    intro i hi
    have cv : ∀ c, (R.cpuTableP K).env i (.main 0 c) = R.cpuColP K i c := fun c => by
      show R.cpuColP K ((i + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
    rw [probeSends_plan]
    cases hp : R.isP i with
    | false =>
      rw [cv, cv, cv, R.colP_low hp (c := SEL + 12) (by decide), R.colP_low hp (c := SEL + 13) (by decide),
        R.J_sel_probe i (.inl rfl), R.J_sel_probe i (.inr rfl), add_zero', ite_zero _ _ rfl, ite_zero _ _ rfl,
        add_zero']
      rfl
    | true =>
      rw [if_pos rfl, segCols_S hi hp, cv P_CNT, R.colP_cnt, cv (SEL + 12), cv (SEL + 13),
        R.colP_sel hp (m := 12) (by decide), R.colP_sel hp (m := 13) (by decide), ofN_add, ofN_ite]
      rcases Nat.decEq i 0 with h0 | h0
      · have hj0 : 0 < R.pcnt i := Nat.pos_of_ne_zero (fun e => h0 ((pr_zero hA hp).2 e))
        rw [if_neg h0, if_neg (show ¬ (12 = 13) by decide), if_pos (show 13 = 13 from rfl), zero_add',
          segCols_E hi hp hj0, ite_and_left hj0, ofN_ite]
        obtain ⟨m, hm⟩ : ∃ m, R.pcnt i = m + 1 := ⟨R.pcnt i - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel, ofN_add, ofN_one, add_sub_right]
      · have hj0 : R.pcnt i = 0 := (pr_zero hA hp).1 h0
        rw [if_pos h0, if_pos (show 12 = 12 from rfl), if_neg (show ¬ (13 = 12) by decide), add_zero',
          ite_zero _ _ rfl, add_zero',
          if_neg (show ¬ (0 < R.pcnt i ∧ _) from fun h => by rw [hj0] at h; exact absurd h.1 (by decide)),
          ofN_zero, add_zero']
  · intro hc
    obtain ⟨i, hi, hpos⟩ := JRun.sumTo_pos_ex hc
    cases hp : R.isP i with
    | false => rw [hp] at hpos; exact absurd hpos (Nat.lt_irrefl 0)
    | true =>
      obtain ⟨hjn, _⟩ := isP_pcnt hA hp
      rw [hp, if_pos rfl] at hpos
      by_cases h1 : ofN (R.pcnt i) :: segCols (R.seg (R.pcnt i)) = v
      · rw [← h1]; exact planRow_mem (seg_get hA hjn)
      · by_cases h2 : 0 < R.pcnt i ∧ ofN (R.pcnt i - 1) :: segCols (R.seg (R.pcnt i - 1)) = v
        · rw [← h2.2]; exact planRow_mem (seg_get hA (by omega))
        · rw [if_neg h1, if_neg h2] at hpos; exact absurd hpos (Nat.lt_irrefl 0)

omit hroots in
/-- **Each segment starts at exactly one row.** -/
theorem count_start {K q : Nat} (hK : R.last < K) (hq : q < R.n) :
    sumTo K (fun i => if R.isP i = true ∧ R.pcnt i = q then 1 else 0) = 1 := by
  have hl := p_mono hA hq (Nat.le_refl _)
  refine sumTo_eq_one K (x := R.p q) (by unfold last at hK; omega)
    (by rw [if_pos ⟨isP_p hA hq, pcnt_p hA (Nat.le_of_lt hq)⟩]) (fun i _ hne => ?_)
  rw [if_neg]
  intro ⟨hp, hc⟩
  apply hne
  rw [← (isP_pcnt hA hp).2, hc]

/-- A parent's end row key: its count and clock. -/
def segKey (R : PRun) (q : Nat) : List F := [ofN q, ofN (R.p (q + 1))]

omit hroots in
/-- A row's `SEGEND` messages: a later probe row looks up its parent's end
    row and provides its own, once per child. -/
theorem segend_row {K i : Nat} (hK : R.last < K) (hi : i < K) (v : List F) :
    probeSendsAt ((R.cpuTableP K).env i) "segend" v =
      ofN (if R.isP i = true ∧ 0 < R.pcnt i ∧ R.segKey (R.seg (R.pcnt i)).parent = v then 1 else 0) -
      ofN (if R.isP i = true ∧ 0 < R.pcnt i then R.nkids (R.pcnt i - 1) * (if R.segKey (R.pcnt i - 1) = v then 1 else 0)
        else 0) := by
  have cv : ∀ c, (R.cpuTableP K).env i (.main 0 c) = R.cpuColP K i c := fun c => by
    show R.cpuColP K ((i + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
  rw [probeSends_segend, cv, cv, cv, cv, cv, cv]
  cases hp : R.isP i with
  | false =>
    rw [R.colP_high hp (c := P_NKIDS) (by decide), R.normX_zero (c := P_NKIDS) (by decide)
      (.inr ⟨by decide, by decide, by decide⟩), R.colP_low hp (c := SEL + 13) (by decide), R.J_sel_probe i (.inr rfl),
      ite_neg_zero _ _ rfl, ite_zero _ _ rfl, if_neg (fun h => Bool.false_ne_true h.1),
      if_neg (fun h => Bool.false_ne_true h.1), ofN_zero, sub_self', add_zero']
  | true =>
    rcases Nat.decEq i 0 with h0 | h0
    · have hj0 : 0 < R.pcnt i := Nat.pos_of_ne_zero (fun e => h0 ((pr_zero hA hp).2 e))
      obtain ⟨m, hm⟩ : ∃ m, R.pcnt i = m + 1 := ⟨R.pcnt i - 1, by omega⟩
      have hpi : R.p (m + 1) = i := by rw [← hm]; exact (isP_pcnt hA hp).2
      rw [R.colP_cnt, R.colP_clk' K i, R.colP_x hp (show P_CNT ≤ P_NKIDS by decide), R.probeX_nkids i hj0,
        R.colP_x hp (show P_CNT ≤ S_BASE + 4 by decide), R.probeX_s i (m := 4) (by decide),
        R.colP_x hp (show P_CNT ≤ P_CLKP by decide), R.probeX_clkp i hj0, R.colP_sel hp (by decide), if_neg h0,
        if_pos (show 13 = 13 from rfl), if_pos (show true = true ∧ 0 < R.pcnt i from ⟨rfl, hj0⟩),
        ite_iff (show (true = true ∧ 0 < R.pcnt i ∧ R.segKey (R.seg (R.pcnt i)).parent = v) ↔
          R.segKey (R.seg (R.pcnt i)).parent = v from ⟨fun h => h.2.2, fun h => ⟨rfl, hj0, h⟩⟩)]
      rw [hm, Nat.add_sub_cancel, ofN_add, ofN_one, add_sub_right]
      show (if [ofN m, ofN i] = v then -ofN (R.nkids m) else 0) +
          (if [ofN (R.seg (m + 1)).parent, ofN (R.p ((R.seg (m + 1)).parent + 1))] = v then 1 else 0) =
        ofN (if [ofN (R.seg (m + 1)).parent, ofN (R.p ((R.seg (m + 1)).parent + 1))] = v then 1 else 0) -
          ofN (R.nkids m * if [ofN m, ofN (R.p (m + 1))] = v then 1 else 0)
      rw [hpi, ofN_ite]
      rcases (inferInstance : Decidable ([ofN m, ofN i] = v)) with h1 | h1
      · rw [if_neg h1, if_neg h1, Nat.mul_zero, ofN_zero, zero_add', sub_eq_add_neg']
        show _ = _ + -0; rw [show -(0 : F) = 0 by decide, add_zero']
      · rw [if_pos h1, if_pos h1, Nat.mul_one, sub_eq_add_neg', add_comm']
    · have hj0 : R.pcnt i = 0 := (pr_zero hA hp).1 h0
      rw [R.colP_x hp (show P_CNT ≤ P_NKIDS by decide), R.probeX_first hj0 (by decide) (by decide) (by decide),
        R.colP_sel hp (by decide), if_pos h0, if_neg (show ¬ (13 = 12) by decide), ite_neg_zero _ _ rfl,
        ite_zero _ _ rfl, if_neg (fun h => by rw [hj0] at h; exact absurd h.2.1 (by decide)),
        if_neg (fun h => by rw [hj0] at h; exact absurd h.2 (by decide)), ofN_zero, sub_self', add_zero']

omit hroots in
theorem look_expand (v : List F) (i : Nat) :
    (if R.isP i = true ∧ 0 < R.pcnt i ∧ R.segKey (R.seg (R.pcnt i)).parent = v then 1 else 0) =
      sumTo R.n (fun c => (if R.isP i = true ∧ R.pcnt i = c then 1 else 0) *
        (if 0 < c ∧ R.segKey (R.seg c).parent = v then 1 else 0)) := by
  cases hp : R.isP i with
  | false =>
    rw [if_neg (fun h => Bool.false_ne_true h.1)]
    exact (sumTo_eq_zero _ (fun c _ => by rw [if_neg (fun h => Bool.false_ne_true h.1), Nat.zero_mul])).symm
  | true =>
    obtain ⟨hjn, _⟩ := isP_pcnt hA hp
    rw [sumTo_at (x := R.pcnt i) R.n hjn (fun c _ hne => by rw [if_neg (fun h => hne h.2.symm), Nat.zero_mul]),
      if_pos (show true = true ∧ R.pcnt i = R.pcnt i from ⟨rfl, rfl⟩), Nat.one_mul]
    exact ite_iff ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩ 1 0

omit hroots in
theorem prov_expand (v : List F) (i : Nat) :
    (if R.isP i = true ∧ 0 < R.pcnt i then R.nkids (R.pcnt i - 1) * (if R.segKey (R.pcnt i - 1) = v then 1 else 0)
      else 0) =
      sumTo R.n (fun c => (if R.isP i = true ∧ R.pcnt i = (R.seg c).parent + 1 then 1 else 0) *
        (if 0 < c ∧ R.segKey (R.seg c).parent = v then 1 else 0)) := by
  by_cases hc : R.isP i = true ∧ 0 < R.pcnt i
  · rw [if_pos hc]
    unfold nkids
    rw [← sumTo_mul_right]
    apply sumTo_congr
    intro c _
    rw [ite_mul_one, ite_mul_one]
    apply ite_iff
    constructor
    · intro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨hc.1, by omega⟩, h1, ?_⟩
      rw [h2]; exact h3
    · intro ⟨⟨_, h2⟩, h1, h3⟩
      refine ⟨⟨h1, by omega⟩, ?_⟩
      rw [show R.pcnt i - 1 = (R.seg c).parent by omega]; exact h3
  · rw [if_neg hc]
    refine (sumTo_eq_zero _ (fun c _ => ?_)).symm
    rw [if_neg (fun h => hc ⟨h.1, by omega⟩), Nat.zero_mul]

variable (hpar : ∀ c, 0 < c → c < R.n → (R.seg c).parent < c)
include hpar

omit hroots in
/-- **`SEGEND` balances**: each child looks up its parent's end row, which
    provides once per child. -/
theorem bal_segend {K : Nat} (hK : R.last < K) (v : List F) :
    (List.range K).foldr (fun i acc => probeSendsAt ((R.cpuTableP K).env i) "segend" v + acc) 0 = 0 := by
  rw [foldr_range_congr K (fun i hi => segend_row hA hK hi v), fold_sub, fold_ofN, fold_ofN]
  have e1 : sumTo K (fun i => if R.isP i = true ∧ 0 < R.pcnt i ∧ R.segKey (R.seg (R.pcnt i)).parent = v then 1 else 0)
      = sumTo R.n (fun c => if 0 < c ∧ R.segKey (R.seg c).parent = v then 1 else 0) := by
    rw [sumTo_congr K (fun i _ => look_expand hA v i), sumTo_comm]
    apply sumTo_congr
    intro c hc
    rw [sumTo_mul_right, count_start hA hK hc, Nat.one_mul]
  have e2 : sumTo K (fun i => if R.isP i = true ∧ 0 < R.pcnt i then
        R.nkids (R.pcnt i - 1) * (if R.segKey (R.pcnt i - 1) = v then 1 else 0) else 0)
      = sumTo R.n (fun c => if 0 < c ∧ R.segKey (R.seg c).parent = v then 1 else 0) := by
    rw [sumTo_congr K (fun i _ => prov_expand hA v i), sumTo_comm]
    apply sumTo_congr
    intro c hc
    rw [sumTo_mul_right]
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [if_neg (fun h => by omega), Nat.mul_zero]
    · rw [count_start hA hK (by have := hpar c h0 hc; omega), Nat.one_mul]
  rw [e1, e2, sub_self']

end PRun

end Circuit
