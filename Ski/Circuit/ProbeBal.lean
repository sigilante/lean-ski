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

end PRun

end Circuit
#print axioms Circuit.PRun.bal_pwch
