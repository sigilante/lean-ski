import Ski.Circuit.JetSat

/-!
# The honest jet tables balance

Every bus balances on the honest tables (`JRun.balanced`):

- **`mem`**: every message is a memory cell's tuple, and the memory table
  receives each as often as it is sent;
- **`roots`**, **`hdr`**, **`tmpl`**: each tuple's count sits on its first
  provider row;
- **`popch`**, **`wch`**: each instantiation's chain telescopes, from the
  CPU's start through its POP (INSTW) rows to the CPU's end;
- **`arg`**: each pop provides its argument as often as the jet's cells
  and root read it.

POP and INSTW messages depend only on the row itself, so a table built
from rows sends the sum of its rows' messages (`sends_rows`).
-/

namespace Circuit

open B Air JetTable Mach

-- ---------------------------------------------------------------------------
-- Tables built from rows
-- ---------------------------------------------------------------------------

/-- A row vector, as an environment: its columns now. -/
def envOf (rw : List F) : Atom → F
  | .main 0 c => rw.getD c 0
  | _ => 0

/-- Atoms of the current row only. -/
def nowAtom : Atom → Bool
  | .main 0 _ => true
  | _ => false

/-- What one row vector sends on `bus` with tuple `v`. -/
def rowSendsV (A : AirD) (bus : String) (v : List F) (rw : List F) : F :=
  A.inters.foldr (fun I acc =>
    (if I.bus = bus ∧ I.fields.map (fun e => e.eval (envOf rw)) = v then I.count.eval (envOf rw) else 0) + acc) 0

/-- An AIR whose messages read only the current row. -/
def NowOnly (A : AirD) : Prop :=
  ∀ I ∈ A.inters, I.count.onlyAtoms nowAtom = true ∧ ∀ e ∈ I.fields, e.onlyAtoms nowAtom = true

theorem rowSends_rows {A : AirD} (hA : NowOnly A) {rows : List (List F)} {H : Nat} {q : Nat} (hq : q < H)
    (bus : String) (v : List F) :
    rowSends A ⟨H, ofRows rows, fun _ _ => 0⟩ bus v q = rowSendsV A bus v (rows.getD q []) := by
  have ag : ∀ a, nowAtom a = true → (Table.env ⟨H, ofRows rows, fun _ _ => 0⟩ q) a = envOf (rows.getD q []) a := by
    intro a ha
    cases a with
    | main o c =>
      cases o with
      | zero => show ofRows rows ((q + 0) % H) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]; rfl
      | succ o => simp [nowAtom] at ha
    | _ => simp [nowAtom] at ha
  unfold rowSends rowSendsV
  have : ∀ (l : List Inter), (∀ I ∈ l, I ∈ A.inters) →
      l.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval ((⟨H, ofRows rows, fun _ _ => 0⟩ : Table).env q)) = v
        then I.count.eval ((⟨H, ofRows rows, fun _ _ => 0⟩ : Table).env q) else 0) + acc) 0 =
      l.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval (envOf (rows.getD q []))) = v
        then I.count.eval (envOf (rows.getD q [])) else 0) + acc) 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons I l ih =>
      simp only [List.foldr_cons]
      obtain ⟨hc, hf⟩ := hA I (hl I List.mem_cons_self)
      have e1 : I.fields.map (fun e => e.eval ((⟨H, ofRows rows, fun _ _ => 0⟩ : Table).env q)) =
          I.fields.map (fun e => e.eval (envOf (rows.getD q []))) :=
        List.map_congr_left (fun e he => E.eval_congr ag e (hf e he))
      rw [e1, E.eval_congr ag _ hc, ih (fun J hJ => hl J (List.mem_cons_of_mem _ hJ))]
  exact this _ (fun _ h => h)

/-- The empty row sends nothing, for an AIR whose counts vanish on zeros. -/
def ZeroQuiet (A : AirD) : Prop := ∀ I ∈ A.inters, I.count.eval (envOf []) = 0

theorem rowSendsV_nil {A : AirD} (hz : ZeroQuiet A) (bus : String) (v : List F) : rowSendsV A bus v [] = 0 := by
  unfold rowSendsV
  apply foldr_zero_init
  intro I hI
  split
  · exact hz I hI
  · rfl

theorem foldr_range_split (f : Nat → F) (L : Nat) : ∀ H, L ≤ H → (∀ q, L ≤ q → q < H → f q = 0) →
    (List.range H).foldr (fun q acc => f q + acc) 0 = (List.range L).foldr (fun q acc => f q + acc) 0
  | 0, hL, _ => by rw [Nat.le_zero.1 hL]
  | H + 1, hL, hz => by
    rcases Nat.lt_or_ge L (H + 1) with h | h
    · rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, hz H (by omega) (Nat.lt_succ_self H),
        zero_add', foldr_range_split f L H (by omega) (fun q h1 h2 => hz q h1 (Nat.lt_succ_of_lt h2))]
    · rw [Nat.le_antisymm hL h]

theorem foldr_range_list (g : List F → F) : ∀ rows : List (List F),
    (List.range rows.length).foldr (fun q acc => g (rows.getD q []) + acc) 0 = (rows.map g).foldr (· + ·) 0
  | [] => rfl
  | r :: rs => by
    rw [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    simp only [List.getD_cons_zero, List.map_cons, List.foldr_cons, List.getD_cons_succ]
    congr 1
    exact foldr_range_list g rs

/-- **A table built from rows sends its rows' messages.** -/
theorem sends_rows {A : AirD} (hA : NowOnly A) (hz : ZeroQuiet A) {rows : List (List F)} {H : Nat}
    (hH : rows.length ≤ H) (bus : String) (v : List F) :
    tableSends A ⟨H, ofRows rows, fun _ _ => 0⟩ bus v = (rows.map (rowSendsV A bus v)).foldr (· + ·) 0 := by
  unfold tableSends
  show (List.range H).foldr (fun q acc => rowSends A ⟨H, ofRows rows, fun _ _ => 0⟩ bus v q + acc) 0 = _
  rw [foldr_range_congr H (fun q hq => rowSends_rows hA hq bus v)]
  rw [foldr_range_split _ rows.length H hH (fun q h1 _ => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]; exact rowSendsV_nil hz bus v)]
  exact foldr_range_list _ rows

theorem foldr_flatMap (g : List F → F) (f : Nat → List (List F)) : ∀ l : List Nat,
    ((l.flatMap f).map g).foldr (· + ·) 0 = l.foldr (fun i acc => ((f i).map g).foldr (· + ·) 0 + acc) 0
  | [] => rfl
  | i :: l => by
    rw [List.flatMap_cons, List.map_append, List.foldr_append, List.foldr_cons, foldr_flatMap g f l]
    rw [fold_acc' (fun (x : F) => x)]
where
  fold_acc' (h : F → F) : ∀ (xs : List F) (x : F), xs.foldr (· + ·) x = xs.foldr (· + ·) 0 + x
    | [], x => (zero_add' x).symm
    | y :: ys, x => by simp only [List.foldr_cons]; rw [fold_acc' h ys x, add_assoc']

theorem pop_nowOnly : NowOnly popAir := by
  have h : popAir.inters.all (fun I => I.count.onlyAtoms nowAtom && I.fields.all (·.onlyAtoms nowAtom)) = true := rfl
  intro I hI
  have := List.all_eq_true.1 h I hI
  rw [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨this.1, this.2⟩

theorem instw_nowOnly : NowOnly instwAir := by
  have h : instwAir.inters.all (fun I => I.count.onlyAtoms nowAtom && I.fields.all (·.onlyAtoms nowAtom)) = true := rfl
  intro I hI
  have := List.all_eq_true.1 h I hI
  rw [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨this.1, this.2⟩

theorem pop_quiet : ZeroQuiet popAir := by
  intro I hI
  simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl <;> decide

theorem instw_quiet : ZeroQuiet instwAir := by
  intro I hI
  simp only [instwAir, instwInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- An indicator in the field. -/
def ind (P : Prop) [Decidable P] : F := if P then 1 else 0

/-- **A chain telescopes.** -/
theorem telescopeF (T : Nat → List F) (v : List F) : ∀ k,
    (List.range k).foldr (fun j acc => (ind (T (j + 1) = v) - ind (T j = v)) + acc) 0 = ind (T k = v) - ind (T 0 = v)
  | 0 => by show (0 : F) = _ - _; rw [sub_self']
  | k + 1 => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, add_zero', fold_acc,
      telescopeF T v k]
    exact E.eval_eq_of_norm
      (e := .add (.sub (.atom (.main 0 0)) (.atom (.main 0 1))) (.sub (.atom (.main 0 2)) (.atom (.main 0 0))))
      (e' := .sub (.atom (.main 0 2)) (.atom (.main 0 1))) (by decide)
      (at4 (ind (T k = v)) (ind (T 0 = v)) (ind (T (k + 1) = v)) 0)

/-- The CPU's chain messages on `POPCH`, for any CPU table. -/
theorem cpu_popch_gen {hd0 stk0 ctr0 : Nat} (C : Table) (r : Nat) (v : List F) :
    rowSends (cpuAirJ hd0 stk0 ctr0) C "popch" v r =
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), 0, C.env r (.main 0 STK)] = v then
      C.env r (.main 0 (SEL + 11)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_K), C.env r (.main 0 J_REST)] = v then
      -C.env r (.main 0 (SEL + 11)) else 0) := by
  rw [cpu_rowSends_jet (by decide)]
  simp only [jetInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col, B.c, sInst,
    true_and, ofN_zero]
  rw [if_neg (show ¬ ("roots" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

/-- The CPU's chain messages on `WCH`, for any CPU table. -/
theorem cpu_wch_gen {hd0 stk0 ctr0 : Nat} (C : Table) (r : Nat) (v : List F) :
    rowSends (cpuAirJ hd0 stk0 ctr0) C "wch" v r =
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_G), 0] = v then
      C.env r (.main 0 (SEL + 11)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_G), C.env r (.main 0 J_N)] = v then
      -C.env r (.main 0 (SEL + 11)) else 0) := by
  rw [cpu_rowSends_jet (by decide)]
  simp only [jetInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col, B.c, sInst,
    true_and, ofN_zero]
  rw [if_neg (show ¬ ("roots" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

theorem ite_one (P : Prop) [Decidable P] (x : F) (hx : x = 1) : (if P then x else 0) = ind P := by
  rw [hx]; rfl

theorem ite_neg_one (P : Prop) [Decidable P] (x : F) (hx : x = 1) : (if P then -x else 0) = -ind P := by
  rw [hx]; unfold ind; split
  · rfl
  · decide

theorem ite_zero (P : Prop) [Decidable P] (x : F) (hx : x = 0) : (if P then x else 0) = 0 := by
  rw [hx]; split <;> rfl

theorem ite_neg_zero (P : Prop) [Decidable P] (x : F) (hx : x = 0) : (if P then -x else 0) = 0 := by
  rw [hx]; split
  · decide
  · rfl

theorem fold_add2 (a b : Nat → F) : ∀ l : List Nat,
    l.foldr (fun i acc => a i + acc) 0 + l.foldr (fun i acc => b i + acc) 0 = l.foldr (fun i acc => (a i + b i) + acc) 0
  | [] => by show (0 : F) + 0 = 0; decide
  | i :: l => by
    simp only [List.foldr_cons]
    rw [← fold_add2 a b l]
    exact E.eval_eq_of_norm
      (e := .add (.add (.atom (.main 0 0)) (.atom (.main 0 1))) (.add (.atom (.main 0 2)) (.atom (.main 0 3))))
      (e' := .add (.add (.atom (.main 0 0)) (.atom (.main 0 2))) (.add (.atom (.main 0 1)) (.atom (.main 0 3))))
      (by decide) (at4 _ _ _ _)

theorem foldr_zero_all (f : Nat → F) : ∀ l : List Nat, (∀ i ∈ l, f i = 0) → l.foldr (fun i acc => f i + acc) 0 = 0 :=
  fold_zero f

theorem foldr_map_range (f : Nat → List F) (g : List F → F) (k : Nat) :
    (((List.range k).map f).map g).foldr (· + ·) 0 = (List.range k).foldr (fun j acc => g (f j) + acc) 0 := by
  rw [List.map_map, List.foldr_map]; rfl

namespace JRun

variable (R : JRun)

theorem popRowsAt_eq {i g : Nat} {J : Air.Jet} (h : R.instAt i = some (g, J)) :
    ∃ σ ξ : Nat → Nat, σ 0 = (R.row i).stk ∧ σ J.xs.length = R.rest i J ∧
      R.ps i J = (List.range J.xs.length).map ξ ∧
      R.popRowsAt i = (List.range J.xs.length).map (fun j =>
        popRow i (R.row i).ctr j (σ j) (ξ j) (σ (j + 1)) (usesOf J j)) ∧
      ∀ j, j < J.xs.length → rd R.A (R.row i).ctr (σ j) = some (.cons (ξ j) (σ (j + 1))) := by
  obtain ⟨hp, _, _, _⟩ := inst_spec h
  have hp' : popR (fun a => R.A[a]?) (R.row i).ctr J.xs.length (R.row i).stk = some (R.ps i J, R.rest i J) := hp
  obtain ⟨σ, ξ, h0, hk, hps, hs⟩ := popsOf_spec (A := R.A) J.xs.length (R.row i).stk hp'
  refine ⟨σ, ξ, h0, hk, hps, ?_, fun j hj => (hs j hj).2⟩
  unfold popRowsAt
  rw [h]
  simp only
  apply List.ext_getElem
  · rw [List.length_map, List.length_zipIdx, popsOf_length hp', List.length_map, List.length_range]
  · intro j h1 h2
    rw [List.length_map, List.length_range] at h2
    rw [List.getElem_map, List.getElem_map, List.getElem_zipIdx, List.getElem_range]
    have e := (hs j h2).1
    rw [List.getElem?_eq_some_iff] at e
    obtain ⟨_, e⟩ := e
    simp only [Nat.zero_add]
    rw [e]

theorem pop_popch (i c j s x s' u : Nat) (v : List F) :
    rowSendsV popAir "popch" v (popRow i c j s x s' u) =
      ind ([ofN i, ofN c, ofN (j + 1), ofN s'] = v) - ind ([ofN i, ofN c, ofN j, ofN s] = v) := by
  obtain ⟨g0, g1, g2, g3, _, g5, _, g7, _⟩ := popRow_get i c j s x s' u
  simp only [rowSendsV, popAir, popInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval,
    B.col, B.one, B.c, ofN_one, true_and]
  have ev : ∀ n, envOf (popRow i c j s x s' u) (.main 0 n) = (popRow i c j s x s' u).getD n 0 := fun _ => rfl
  rw [ev 0, ev 1, ev 2, ev 3, ev 5, ev 7, g0, g1, g2, g3, g5, g7,
    if_neg (show ¬ ("mem" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)), add_zero', add_zero',
    ite_neg_one _ 1 rfl, ← ofN_one, ← ofN_add, ite_one _ (ofN 1) rfl, add_zero', sub_eq_add_neg', add_comm']

/-- The CPU's columns at an instantiation row. -/
theorem inst_cols {K i g : Nat} {J : Air.Jet} (hi : i < K) (h : R.instAt i = some (g, J)) (c : Nat) :
    (R.cpuTable K).env i (.main 0 c) = R.instCol i g J c := by
  show R.cpuCol ((i + 0) % K) c = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
  unfold cpuCol; rw [h]

/-- **`POPCH` balances**: each instantiation's chain telescopes. -/
theorem bal_popch {K HP : Nat}
    (hHP : (R.popRows K).length ≤ HP) (v : List F) :
    tableSends (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (R.cpuTable K) "popch" v +
      tableSends popAir (R.popTable K HP) "popch" v = 0 := by
  rw [show R.popTable K HP = ⟨HP, ofRows (R.popRows K), fun _ _ => 0⟩ from rfl,
    sends_rows pop_nowOnly pop_quiet hHP, popRows, foldr_flatMap]
  unfold tableSends
  show (List.range K).foldr _ 0 + _ = 0
  rw [foldr_range_congr K (fun i hi => cpu_popch_gen (R.cpuTable K) i v)]
  rw [fold_add2]
  apply foldr_zero_all
  intro i hi
  have hi' := List.mem_range.1 hi
  cases hn : R.instAt i with
  | none =>
    have hs : (R.cpuTable K).env i (.main 0 (SEL + 11)) = 0 := by
      show R.cpuCol ((i + 0) % K) (SEL + 11) = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi']
      unfold cpuCol; rw [hn]; simp only
      rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (Nat.ne_of_gt (kindOf_lt _ _))]
    rw [ite_zero _ _ hs, ite_neg_zero _ _ hs, zero_add']
    unfold popRowsAt; rw [hn]; rfl
  | some p =>
    obtain ⟨g, J⟩ := p
    obtain ⟨σ, ξ, h0, hk, _, hrows, _⟩ := R.popRowsAt_eq hn
    have cv := R.inst_cols hi' hn
    rw [cv, cv, cv, cv, cv, cv, show R.instCol i g J (SEL + 11) = 1 from rfl,
      show R.instCol i g J J_CLK = ofN i from rfl, show R.instCol i g J CTR = ofN (R.row i).ctr from rfl,
      show R.instCol i g J STK = ofN (R.row i).stk from rfl, show R.instCol i g J J_K = ofN J.xs.length from rfl,
      show R.instCol i g J J_REST = ofN (R.rest i J) from rfl, ite_one _ 1 rfl, ite_neg_one _ 1 rfl]
    rw [hrows, foldr_map_range]
    let T : Nat → List F := fun j => [ofN i, ofN (R.row i).ctr, ofN j, ofN (σ j)]
    rw [foldr_range_congr J.xs.length (fun j _ => pop_popch i (R.row i).ctr j (σ j) (ξ j) (σ (j + 1)) (usesOf J j) v)]
    have tele := telescopeF T v J.xs.length
    simp only [T] at tele
    rw [tele, ← h0, ← hk, ← ofN_zero]
    exact E.eval_eq_of_norm
      (e := .add (.add (.atom (.main 0 0)) (.neg (.atom (.main 0 1)))) (.sub (.atom (.main 0 1)) (.atom (.main 0 0))))
      (e' := .const (ofN 0)) (by decide) (at4 _ _ 0 0)

end JRun

theorem instwRow_get (i c g j : Nat) (ps : List Nat) (cl : Nat × Option (Op × Op)) :
    (instwRow i c g j ps cl).getD 0 0 = ofN i ∧ (instwRow i c g j ps cl).getD 1 0 = ofN c ∧
    (instwRow i c g j ps cl).getD 2 0 = ofN g ∧ (instwRow i c g j ps cl).getD 3 0 = ofN j ∧
    (instwRow i c g j ps cl).getD 17 0 = 1 := by
  obtain ⟨t, ops⟩ := cl
  cases ops with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some ab =>
    obtain ⟨a, b⟩ := ab
    cases a <;> cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem instw_wch (i c g j : Nat) (ps : List Nat) (cl : Nat × Option (Op × Op)) (v : List F) :
    rowSendsV instwAir "wch" v (instwRow i c g j ps cl) =
      ind ([ofN i, ofN c, ofN g, ofN (j + 1)] = v) - ind ([ofN i, ofN c, ofN g, ofN j] = v) := by
  obtain ⟨g0, g1, g2, g3, g17⟩ := instwRow_get i c g j ps cl
  simp only [rowSendsV, instwAir, instwInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval,
    B.col, B.one, B.c, ofN_one, true_and]
  have ev : ∀ n, envOf (instwRow i c g j ps cl) (.main 0 n) = (instwRow i c g j ps cl).getD n 0 := fun _ => rfl
  rw [ev 0, ev 1, ev 2, ev 3, ev 17, g0, g1, g2, g3, g17,
    if_neg (show ¬ ("arg" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("tmpl" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    zero_add', zero_add', add_zero', add_zero',
    ite_neg_one _ 1 rfl, ← ofN_one, ← ofN_add, ite_one _ (ofN 1) rfl, sub_eq_add_neg', add_comm']
  rw [add_zero']

namespace JRun

variable (R : JRun)

theorem instwRowsAt_eq {i g : Nat} {J : Air.Jet} (h : R.instAt i = some (g, J)) :
    R.instwRowsAt i = (List.range (symCells J J.body 0).1.length).map (fun j =>
      instwRow i (R.row i).ctr g j (R.ps i J) ((symCells J J.body 0).1.getD j (0, none))) := by
  unfold instwRowsAt
  rw [h]
  simp only
  apply List.ext_getElem
  · rw [List.length_map, List.length_zipIdx, List.length_map, List.length_range]
  · intro j h1 h2
    rw [List.length_map, List.length_range] at h2
    rw [List.getElem_map, List.getElem_map, List.getElem_zipIdx, List.getElem_range]
    simp only [Nat.zero_add]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl

/-- **`WCH` balances**: each instantiation's writes telescope. -/
theorem bal_wch {K HW : Nat}
    (hHW : (R.instwRows K).length ≤ HW) (v : List F) :
    tableSends (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (R.cpuTable K) "wch" v +
      tableSends instwAir (R.instwTable K HW) "wch" v = 0 := by
  rw [show R.instwTable K HW = ⟨HW, ofRows (R.instwRows K), fun _ _ => 0⟩ from rfl,
    sends_rows instw_nowOnly instw_quiet hHW, instwRows, foldr_flatMap]
  unfold tableSends
  show (List.range K).foldr _ 0 + _ = 0
  rw [foldr_range_congr K (fun i hi => cpu_wch_gen (R.cpuTable K) i v)]
  rw [fold_add2]
  apply foldr_zero_all
  intro i hi
  have hi' := List.mem_range.1 hi
  cases hn : R.instAt i with
  | none =>
    have hs : (R.cpuTable K).env i (.main 0 (SEL + 11)) = 0 := by
      show R.cpuCol ((i + 0) % K) (SEL + 11) = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi']
      unfold cpuCol; rw [hn]; simp only
      rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (Nat.ne_of_gt (kindOf_lt _ _))]
    rw [ite_zero _ _ hs, ite_neg_zero _ _ hs, zero_add']
    unfold instwRowsAt; rw [hn]; rfl
  | some p =>
    obtain ⟨g, J⟩ := p
    have cv := R.inst_cols hi' hn
    rw [cv, cv, cv, cv, cv, show R.instCol i g J (SEL + 11) = 1 from rfl,
      show R.instCol i g J J_CLK = ofN i from rfl, show R.instCol i g J CTR = ofN (R.row i).ctr from rfl,
      show R.instCol i g J J_G = ofN g from rfl,
      show R.instCol i g J J_N = ofN (symCells J J.body 0).1.length from rfl, ite_one _ 1 rfl, ite_neg_one _ 1 rfl]
    rw [R.instwRowsAt_eq hn, foldr_map_range]
    let T : Nat → List F := fun j => [ofN i, ofN (R.row i).ctr, ofN g, ofN j]
    rw [foldr_range_congr _ (fun j _ => instw_wch i (R.row i).ctr g j (R.ps i J) _ v)]
    have tele := telescopeF T v (symCells J J.body 0).1.length
    simp only [T] at tele
    rw [tele, ← ofN_zero]
    exact E.eval_eq_of_norm
      (e := .add (.add (.atom (.main 0 0)) (.neg (.atom (.main 0 1)))) (.sub (.atom (.main 0 1)) (.atom (.main 0 0))))
      (e' := .const (ofN 0)) (by decide) (at4 _ _ 0 0)

end JRun

-- ---------------------------------------------------------------------------
-- Arguments
-- ---------------------------------------------------------------------------

theorem argIx_lt : ∀ {xs : List Nat} {y i : Nat}, argIx xs y = some i → i < xs.length
  | [], _, _, h => by cases h
  | x :: xs, y, i, h => by
    unfold argIx at h
    cases hr : argIx xs y with
    | some i' =>
      rw [hr] at h
      cases h
      have := argIx_lt hr
      simp only [List.length_cons]; omega
    | none =>
      rw [hr] at h
      simp only at h
      split at h
      · cases h; simp
      · cases h

/-- An operand's argument, if any, is below the arity. -/
def ArgBelow (k : Nat) (o : Op) : Prop := ∀ i, o = .arg i → i < k

/-- **Every argument a template reads is a formal.** -/
theorem symCells_args (J : Air.Jet) : ∀ (body : OTerm) (off : Nat),
    (∀ cl ∈ (symCells J body off).1, ∀ a b, cl.2 = some (a, b) → ArgBelow J.xs.length a ∧ ArgBelow J.xs.length b) ∧
      ArgBelow J.xs.length (symCells J body off).2
  | .S, _ => ⟨fun cl h => (by
        rcases List.mem_singleton.1 (show cl ∈ [(((0 : Nat)), (none : Option (Op × Op)))] from h) with rfl
        intro a b e; cases e), fun i e => (by cases e)⟩
  | .K, _ => ⟨fun cl h => (by
        rcases List.mem_singleton.1 (show cl ∈ [(((1 : Nat)), (none : Option (Op × Op)))] from h) with rfl
        intro a b e; cases e), fun i e => (by cases e)⟩
  | .I, _ => ⟨fun cl h => (by
        rcases List.mem_singleton.1 (show cl ∈ [(((2 : Nat)), (none : Option (Op × Op)))] from h) with rfl
        intro a b e; cases e), fun i e => (by cases e)⟩
  | .var x, off => by
    refine ⟨fun cl h => by simp only [symCells, List.not_mem_nil] at h, fun i e => ?_⟩
    have e' : (symCells J (.var x) off).2 = varOp J x := rfl
    rw [e'] at e
    unfold varOp at e
    split at e
    · next i' h => cases e; exact argIx_lt h
    · cases e
  | .app f a, off => by
    obtain ⟨hf, hrf⟩ := symCells_args J f off
    obtain ⟨ha, hra⟩ := symCells_args J a (off + (symCells J f off).1.length)
    refine ⟨fun cl h => ?_, fun i e => by unfold symCells at e; cases e⟩
    unfold symCells at h
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hf cl h
      · exact ha cl h
    · rw [List.mem_singleton] at h; subst h
      intro x y e
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨hrf, hra⟩

/-- Whether an operand reads the argument a tuple names. -/
def argCnt (i : Nat) (ps : List Nat) (v : List F) : Op → Nat
  | .arg a => if [ofN i, ofN a, ofN (ps.getD a 0)] = v then 1 else 0
  | _ => 0

def cellArgCnt (i : Nat) (ps : List Nat) (v : List F) (cl : Nat × Option (Op × Op)) : Nat :=
  match cl.2 with
  | some (a, b) => argCnt i ps v a + argCnt i ps v b
  | none => 0

theorem sumTo_single_val (x c : Nat) : ∀ n, x < n → sumTo n (fun q => if q = x then (if true then c else 0) else 0) = c
  | 0, hx => absurd hx (Nat.not_lt_zero _)
  | n + 1, hx => by
    show sumTo n _ + (if n = x then (if true then c else 0) else 0) = c
    rcases Nat.lt_or_ge x n with h | h
    · rw [sumTo_single_val x c n h, if_neg (Nat.ne_of_gt h), Nat.add_zero]
    · have e : n = x := Nat.le_antisymm h (Nat.le_of_lt_succ hx)
      rw [if_pos e, sumTo_congr n (g := fun _ => 0) (fun q hq => if_neg (by omega)), sumTo_zero (fun _ => rfl) n,
        Nat.zero_add]; rfl

/-- Uses of each argument, summed against the arguments' tuples, are the
    reads. -/
theorem sum_isArg {k : Nat} (y : Nat → Nat) (o : Op) (ho : ArgBelow k o) :
    sumTo k (fun j => isArg j o * y j) = match o with | .arg a => y a | _ => 0 := by
  cases o with
  | arg a =>
    have ha := ho a rfl
    show sumTo k (fun j => (if a = j then 1 else 0) * y j) = y a
    have e : ∀ j, (if a = j then 1 else 0) * y j = if j = a then (if true then y a else 0) else 0 := by
      intro j
      rcases Nat.decEq j a with h | h
      · rw [if_neg (Ne.symm h), if_neg h, Nat.zero_mul]
      · subst h; rw [if_pos rfl, if_pos rfl, Nat.one_mul]; rfl
    rw [sumTo_congr k (fun j _ => e j)]
    exact sumTo_single_val a (y a) k ha
  | local_ j => show sumTo k (fun _ => 0 * _) = 0; exact sumTo_zero (fun _ => Nat.zero_mul _) k
  | glob g => show sumTo k (fun _ => 0 * _) = 0; exact sumTo_zero (fun _ => Nat.zero_mul _) k

theorem sumTo_listSum {α : Type} (k : Nat) (y : Nat → Nat) (f : α → Nat → Nat) : ∀ l : List α,
    sumTo k (fun j => (l.map fun c => f c j).sum * y j) = (l.map fun c => sumTo k (fun j => f c j * y j)).sum
  | [] => sumTo_zero (fun _ => Nat.zero_mul _) k
  | c :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [sumTo_congr k (fun j _ => Nat.add_mul (f c j) _ (y j)), sumTo_add, sumTo_listSum k y f l]

theorem sumTo_shift (g : Nat → Nat) : ∀ n, sumTo (n + 1) g = g 0 + sumTo n (fun j => g (j + 1))
  | 0 => by show 0 + g 0 = g 0 + 0; omega
  | n + 1 => by
    show sumTo (n + 1) g + g (n + 1) = g 0 + (sumTo n (fun j => g (j + 1)) + g (n + 1))
    rw [sumTo_shift g n]; omega

theorem listSum_sumTo {α : Type} (f : α → Nat) (d : α) : ∀ l : List α,
    (l.map f).sum = sumTo l.length (fun j => f (l.getD j d))
  | [] => rfl
  | c :: l => by
    rw [List.map_cons, List.sum_cons, List.length_cons, sumTo_shift, listSum_sumTo f d l]
    rfl

/-- The CPU's argument message, for any CPU table. -/
theorem cpu_arg_gen {hd0 stk0 ctr0 : Nat} (C : Table) (r : Nat) (v : List F) :
    rowSends (cpuAirJ hd0 stk0 ctr0) C "arg" v r =
    if [C.env r (.main 0 J_CLK), C.env r (.main 0 J_RV), C.env r (.main 0 J_XROOT)] = v then
      C.env r (.main 0 J_RA) else 0 := by
  rw [cpu_rowSends_jet (by decide)]
  simp only [jetInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col, B.c, sInst,
    true_and, ofN_zero]
  rw [if_neg (show ¬ ("roots" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

theorem ofN_ind (P : Prop) [Decidable P] : ofN (if P then 1 else 0) = ind P := by
  unfold ind; split <;> rfl

/-- An operand's argument read, in the field. -/
theorem argCnt_ofN (i : Nat) (ps : List Nat) (v : List F) (o : Op) :
    (if [ofN i, (opCols o).getD 3 0, ofN (argVal ps o)] = v then (opCols o).getD 1 0 else 0) =
      ofN (argCnt i ps v o) := by
  cases o with
  | arg a => show (if [ofN i, ofN a, ofN (ps.getD a 0)] = v then ofN 1 else 0) = ofN (if _ then 1 else 0)
             split <;> rfl
  | local_ j => show (if _ then ofN 0 else 0) = ofN 0; split <;> rfl
  | glob a => show (if _ then ofN 0 else 0) = ofN 0; split <;> rfl

theorem instw_arg (i c g j : Nat) (ps : List Nat) (cl : Nat × Option (Op × Op)) (hcl : cl.2 = none ∧ cl.1 < 3 ∨
    (cl.1 = 3 ∧ ∃ a b, cl.2 = some (a, b))) (v : List F) :
    rowSendsV instwAir "arg" v (instwRow i c g j ps cl) = ofN (cellArgCnt i ps v cl) := by
  obtain ⟨t, ops⟩ := cl
  simp only [rowSendsV, instwAir, instwInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval,
    B.col, B.one, B.c, ofN_one, true_and]
  rw [if_neg (show ¬ ("wch" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("tmpl" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)), add_zero', add_zero', add_zero',
    add_zero']
  have ev : ∀ n, envOf (instwRow i c g j ps (t, ops)) (.main 0 n) = (instwRow i c g j ps (t, ops)).getD n 0 :=
    fun _ => rfl
  simp only [ev]
  rcases hcl with ⟨hno, ht⟩ | ⟨_, a, b, hso⟩
  · simp only at hno ht; subst hno
    rw [JRun.instwRow_none i c g j t ps ht]
    have z6 : ([ofN i, ofN c, ofN g, ofN j, ofN t, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : List F).getD 6 0 = 0 := rfl
    have z10 : ([ofN i, ofN c, ofN g, ofN j, ofN t, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] : List F).getD 10 0 = 0 := rfl
    rw [z6, z10, ite_zero _ _ rfl, ite_zero _ _ rfl, zero_add']; rfl
  · simp only at hso; subst hso
    obtain ⟨hops, _, _, _, h15, h16, _⟩ := JRun.instwRow_some_get i c g j t ps a b
    have g0 := (instwRow_get i c g j ps (t, some (a, b))).1
    rw [g0, (hops 1 (by decide)).1, (hops 3 (by decide)).1, (hops 1 (by decide)).2, (hops 3 (by decide)).2, h15, h16,
      argCnt_ofN, argCnt_ofN, add_zero', ← ofN_add]
    rfl

theorem pop_arg (i c j s x s' u : Nat) (v : List F) :
    rowSendsV popAir "arg" v (popRow i c j s x s' u) = -ofN (u * if [ofN i, ofN j, ofN x] = v then 1 else 0) := by
  obtain ⟨g0, _, g2, _, g4, _, g6, _, _⟩ := JRun.popRow_get i c j s x s' u
  simp only [rowSendsV, popAir, popInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval,
    B.col, B.one, B.c, ofN_one, true_and]
  have ev : ∀ n, envOf (popRow i c j s x s' u) (.main 0 n) = (popRow i c j s x s' u).getD n 0 := fun _ => rfl
  rw [if_neg (show ¬ ("popch" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "arg" ∧ _) from fun h' => absurd h'.1 (by decide)), zero_add', zero_add', zero_add',
    add_zero', ev 0, ev 2, ev 4, ev 6, g0, g2, g4, g6]
  split
  · rw [Nat.mul_one]
  · rw [Nat.mul_zero, ofN_zero]; decide

theorem fold_neg_ofN (a : Nat → Nat) : ∀ H,
    (List.range H).foldr (fun q acc => -ofN (a q) + acc) 0 = -ofN (sumTo H a)
  | 0 => by show (0 : F) = -ofN 0; decide
  | H + 1 => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, fold_acc, fold_neg_ofN a H, add_zero']
    show _ = -ofN (sumTo H a + a H)
    rw [ofN_add]
    exact E.eval_eq_of_norm (e := .add (.neg (.atom (.main 0 0))) (.neg (.atom (.main 0 1))))
      (e' := .neg (.add (.atom (.main 0 0)) (.atom (.main 0 1)))) (by decide) (at4 _ _ 0 0)

/-- The argument reads of a jet at an instantiation, counted two ways. -/
theorem uses_reads (J : Air.Jet) (i : Nat) (ps : List Nat) (ξ : Nat → Nat)
    (hps : ps = (List.range J.xs.length).map ξ) (v : List F) :
    sumTo J.xs.length (fun j => usesOf J j * if [ofN i, ofN j, ofN (ξ j)] = v then 1 else 0) =
      ((symCells J J.body 0).1.map (cellArgCnt i ps v)).sum + argCnt i ps v (symCells J J.body 0).2 := by
  obtain ⟨hcells, hroot⟩ := symCells_args J J.body 0
  let y := fun j => if [ofN i, ofN j, ofN (ξ j)] = v then 1 else 0
  have hy : ∀ a, a < J.xs.length → argCnt i ps v (.arg a) = y a := by
    intro a ha
    show (if [ofN i, ofN a, ofN (ps.getD a 0)] = v then 1 else 0) = _
    rw [hps, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha]; rfl
  have hop : ∀ o, ArgBelow J.xs.length o → sumTo J.xs.length (fun j => isArg j o * y j) = argCnt i ps v o := by
    intro o ho
    rw [sum_isArg y o ho]
    cases o with
    | arg a => exact (hy a (ho a rfl)).symm
    | local_ _ => rfl
    | glob _ => rfl
  unfold usesOf
  have e := sumTo_listSum J.xs.length y (fun cl j => cellUses j cl) (symCells J J.body 0).1
  rw [sumTo_congr _ (fun j _ => Nat.add_mul _ _ (y j)), sumTo_add, e, hop _ hroot]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro cl hcl
  obtain ⟨t, ops⟩ := cl
  cases ops with
  | none => exact sumTo_zero (fun _ => Nat.zero_mul _) _
  | some ab =>
    obtain ⟨a, b⟩ := ab
    obtain ⟨ha, hb⟩ := hcells _ hcl a b rfl
    show sumTo _ (fun j => cellUses j (t, some (a, b)) * y j) = argCnt i ps v a + argCnt i ps v b
    show sumTo _ (fun j => (isArg j a + isArg j b) * y j) = argCnt i ps v a + argCnt i ps v b
    rw [sumTo_congr _ (fun j _ => Nat.add_mul _ _ (y j)), sumTo_add, hop a ha, hop b hb]

namespace JRun

variable (R : JRun)

/-- **`ARG` balances**: each pop provides its argument as often as the jet
    reads it. -/
theorem bal_arg {K HP HW : Nat}
    (hHP : (R.popRows K).length ≤ HP) (hHW : (R.instwRows K).length ≤ HW) (v : List F) :
    tableSends (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (R.cpuTable K) "arg" v +
      (tableSends popAir (R.popTable K HP) "arg" v + tableSends instwAir (R.instwTable K HW) "arg" v) = 0 := by
  rw [show R.popTable K HP = ⟨HP, ofRows (R.popRows K), fun _ _ => 0⟩ from rfl,
    show R.instwTable K HW = ⟨HW, ofRows (R.instwRows K), fun _ _ => 0⟩ from rfl,
    sends_rows pop_nowOnly pop_quiet hHP, sends_rows instw_nowOnly instw_quiet hHW, popRows, instwRows,
    foldr_flatMap, foldr_flatMap]
  unfold tableSends
  show (List.range K).foldr _ 0 + _ = 0
  rw [foldr_range_congr K (fun i hi => cpu_arg_gen (R.cpuTable K) i v)]
  rw [fold_add2, fold_add2]
  apply foldr_zero_all
  intro i hi
  have hi' := List.mem_range.1 hi
  cases hn : R.instAt i with
  | none =>
    have hra : (R.cpuTable K).env i (.main 0 J_RA) = 0 := by
      show R.cpuCol ((i + 0) % K) J_RA = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi']
      unfold cpuCol; rw [hn]; simp only; rw [if_neg (by decide), if_neg (by decide)]
    rw [ite_zero _ _ hra, zero_add']
    unfold popRowsAt instwRowsAt; rw [hn]
    show (0 : F) + 0 = 0; decide
  | some p =>
    obtain ⟨g, J⟩ := p
    obtain ⟨σ, ξ, _, _, hps, hrows, _⟩ := R.popRowsAt_eq hn
    have cv := R.inst_cols hi' hn
    rw [cv, cv, cv, cv, show R.instCol i g J J_CLK = ofN i from rfl,
      show R.instCol i g J J_RV = (opCols (symCells J J.body 0).2).getD 3 0 from rfl,
      show R.instCol i g J J_XROOT = ofN (argVal (R.ps i J) (symCells J J.body 0).2) from rfl,
      show R.instCol i g J J_RA = (opCols (symCells J J.body 0).2).getD 1 0 from rfl, argCnt_ofN]
    rw [hrows, foldr_map_range, R.instwRowsAt_eq hn, foldr_map_range]
    rw [foldr_range_congr _ (fun j _ => pop_arg i (R.row i).ctr j (σ j) (ξ j) (σ (j + 1)) (usesOf J j) v)]
    rw [foldr_range_congr _ (fun j hj => instw_arg i (R.row i).ctr g j (R.ps i J) _
      (symCells_cells J J.body 0 _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj)) v)]
    rw [fold_neg_ofN, fold_ofN, uses_reads J i (R.ps i J) ξ hps v,
      listSum_sumTo (cellArgCnt i (R.ps i J) v) (0, none)]
    rw [ofN_add]
    exact E.eval_eq_of_norm
      (e := .add (.atom (.main 0 0)) (.add (.neg (.add (.atom (.main 0 1)) (.atom (.main 0 0)))) (.atom (.main 0 1))))
      (e' := .const 0) (by decide) (at4 _ _ 0 0)

end JRun

-- ---------------------------------------------------------------------------
-- Providers
-- ---------------------------------------------------------------------------

theorem provRow_fields {name : String} {w : Nat} {rows : List (List F)} {cnt : List F → Nat}
    (hlen : ∀ x ∈ rows, x.length = w) {q : Nat} (hq : q < rows.length) :
    ((List.range w).map prec).map (fun e => e.eval ((provTable rows cnt).env q)) = rows[q] := by
  rw [List.map_map]
  have e : ∀ i, (fun e => E.eval ((provTable rows cnt).env q) e) (prec i) = rows[q].getD i 0 := by
    intro i
    show ofRows rows ((q + 0) % rows.length) i = _
    rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
    unfold ofRows; rw [List.getD_eq_getElem?_getD (l := rows), List.getElem?_eq_getElem hq]; rfl
  rw [show (List.range w).map ((fun e => E.eval ((provTable rows cnt).env q) e) ∘ prec) =
    (List.range w).map (fun i => rows[q].getD i 0) from List.map_congr_left (fun i _ => e i),
    ← hlen _ (List.getElem_mem hq), map_getD_self]

theorem firstOcc_true {rows : List (List F)} {m : Nat} (h : ∀ j, j < m → rows.getD j [] ≠ rows.getD m []) :
    firstOcc rows m = true :=
  List.all_eq_true.2 fun j hj => by
    rw [Bool.not_eq_true', decide_eq_false_iff_not]; exact h j (List.mem_range.1 hj)

theorem firstOcc_false {rows : List (List F)} {m q : Nat} (hmq : m < q) (h : rows.getD m [] = rows.getD q []) :
    firstOcc rows q = false := by
  cases hc : firstOcc rows q with
  | false => rfl
  | true =>
    have := List.all_eq_true.1 hc m (List.mem_range.2 hmq)
    rw [h, decide_eq_true rfl] at this
    cases this

/-- **A provider receives each tuple's count once**, on its first row. -/
theorem prov_sends {name : String} {w : Nat} {rows : List (List F)} {cnt : List F → Nat}
    (hlen : ∀ x ∈ rows, x.length = w) (v : List F) :
    tableSends (providerAir name w rows) (provTable rows cnt) name v = -(if v ∈ rows then ofN (cnt v) else 0) := by
  have hrow : ∀ q, q < rows.length → rowSends (providerAir name w rows) (provTable rows cnt) name v q =
      if rows.getD q [] = v then -(if firstOcc rows q then ofN (cnt (rows.getD q [])) else 0) else 0 := by
    intro q hq
    have eg : rows.getD q [] = rows[q] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl
    simp only [rowSends, providerAir, List.foldr_cons, List.foldr_nil, true_and]
    rw [provRow_fields (name := name) hlen hq, add_zero', eg]
    show (if rows[q] = v then -((provTable rows cnt).main ((q + 0) % rows.length) 0) else 0) = _
    rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
    show (if rows[q] = v then -(if firstOcc rows q then ofN (cnt (rows.getD q [])) else 0) else 0) = _
    rw [eg]
  unfold tableSends
  show (List.range rows.length).foldr _ 0 = _
  cases hv : decide (v ∈ rows) with
  | false =>
    have hv' := of_decide_eq_false hv
    rw [if_neg hv']
    rw [fold_zero _ _ (fun q hq => by
      have hq' := List.mem_range.1 hq
      rw [hrow q hq', if_neg (fun e => hv' (by
        rw [← e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq']; exact List.getElem_mem hq'))])]
    decide
  | true =>
    have hv' := of_decide_eq_true hv
    rw [if_pos hv']
    obtain ⟨q1, hq1, e1⟩ := List.getElem_of_mem hv'
    have hp1 : decide (rows.getD q1 [] = v) = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq1]; exact decide_eq_true e1
    obtain ⟨m, hm, hpm, hmin⟩ := Edges.exists_first (fun q => decide (rows.getD q [] = v)) q1 hp1
    have hmL : m < rows.length := Nat.lt_of_le_of_lt hm hq1
    have em : rows.getD m [] = v := of_decide_eq_true hpm
    rw [fold_single _ rows.length m hmL (fun q hq hne => by
      rw [hrow q hq]
      split
      · next eq =>
        rcases Nat.lt_or_ge q m with hlt | hge
        · exact absurd (decide_eq_true eq) (by rw [hmin q hlt]; decide)
        · rw [firstOcc_false (show m < q by omega) (by rw [em, eq]), if_neg (by decide)]; decide
      · rfl)]
    rw [hrow m hmL, if_pos em, firstOcc_true (fun j hj => by
      rw [em]; intro e; have := hmin j hj; rw [decide_eq_true e] at this; cases this), em, if_pos rfl]

theorem cpu_roots_gen {hd0 stk0 ctr0 : Nat} (C : Table) (r : Nat) (v : List F) :
    rowSends (cpuAirJ hd0 stk0 ctr0) C "roots" v r =
    if [C.env r (.main 0 HD), C.env r (.main 0 J_G)] = v then C.env r (.main 0 (SEL + 11)) else 0 := by
  rw [cpu_rowSends_jet (by decide)]
  simp only [jetInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col, B.c, sInst,
    true_and, ofN_zero]
  rw [if_neg (show ¬ ("hdr" = "roots" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "roots" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "roots" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "roots" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "roots" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "roots" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

theorem cpu_hdr_gen {hd0 stk0 ctr0 : Nat} (C : Table) (r : Nat) (v : List F) :
    rowSends (cpuAirJ hd0 stk0 ctr0) C "hdr" v r =
    if [C.env r (.main 0 J_G), C.env r (.main 0 J_K), C.env r (.main 0 J_N), C.env r (.main 0 J_RL),
      C.env r (.main 0 J_RA), C.env r (.main 0 J_RG), C.env r (.main 0 J_RV)] = v then
      C.env r (.main 0 (SEL + 11)) else 0 := by
  rw [cpu_rowSends_jet (by decide)]
  simp only [jetInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col, B.c, sInst,
    true_and, ofN_zero]
  rw [if_neg (show ¬ ("roots" = "hdr" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "hdr" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "hdr" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "hdr" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "hdr" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "hdr" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

theorem instw_tmpl (i c g j : Nat) (ps : List Nat) (cl : Nat × Option (Op × Op)) (v : List F) :
    rowSendsV instwAir "tmpl" v (instwRow i c g j ps cl) = ind (tmplRow g j cl = v) := by
  have g17 := (instwRow_get i c g j ps cl).2.2.2.2
  simp only [rowSendsV, instwAir, instwInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval,
    B.col, B.one, B.c, ofN_one, true_and]
  rw [if_neg (show ¬ ("arg" = "tmpl" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "tmpl" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "tmpl" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "tmpl" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("mem" = "tmpl" ∧ _) from fun h' => absurd h'.1 (by decide)),
    zero_add', zero_add', zero_add', zero_add', add_zero', add_zero']
  have ev : envOf (instwRow i c g j ps cl) (.main 0 17) = 1 := g17
  rw [ev]
  have ef : List.map (fun e => E.eval (envOf (instwRow i c g j ps cl)) e)
      (List.map (fun i => E.atom (Atom.main 0 (2 + i))) (List.range 11)) = tmplRow g j cl := by
    rw [List.map_map]
    have hl : (tmplRow g j cl).length = 11 := tmplRow_len g j cl
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, hl]
    · intro q h1 h2
      rw [List.getElem_map, List.getElem_range]
      show (instwRow i c g j ps cl).getD (2 + q) 0 = _
      unfold instwRow
      rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, Nat.add_comm 2 q,
        List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_append_left h2,
        List.getElem?_eq_getElem h2]
      rfl
  rw [ef]; rfl

/-- Lookup counts meet their provider. -/
theorem bal_lookup {x : F} {cnt : Nat} {P : Prop} [Decidable P] (hx : x = ofN cnt) (hc : 0 < cnt → P) :
    x + -(if P then ofN cnt else 0) = 0 := by
  rw [hx]
  split
  · exact E.eval_eq_of_norm (e := .add (.atom (.main 0 0)) (.neg (.atom (.main 0 0)))) (e' := .const 0) (by decide)
      (at4 _ 0 0 0)
  · next hP =>
    have : cnt = 0 := by rcases Nat.eq_zero_or_pos cnt with h | h
                         · exact h
                         · exact absurd (hc h) hP
    rw [this]; decide

theorem padCopies_super {x : List F} : ∀ {rows : List (List F)}, x ∈ rows → x ∈ padCopies rows
  | [], h => nomatch h
  | r :: rs, h => List.mem_append_left _ h

namespace JRun

variable (R : JRun)

theorem sumTo_pos_ex {f : Nat → Nat} {n : Nat} (h : 0 < sumTo n f) : ∃ q, q < n ∧ 0 < f q := sumTo_pos n h

/-- **`ROOTS` balances.** -/
theorem bal_roots {K : Nat} (v : List F) :
    tableSends (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (R.cpuTable K) "roots" v +
      tableSends (rootsAir R.roots) (provTable (rootsRows R.roots) (R.cntRoots K)) "roots" v = 0 := by
  rw [show rootsAir R.roots = providerAir "roots" 2 (rootsRows R.roots) from rfl,
    prov_sends (rootsRows_len R.roots)]
  apply bal_lookup
  · unfold tableSends cntRoots
    show (List.range K).foldr _ 0 = _
    rw [← fold_ofN]
    apply foldr_range_congr K
    intro i hi
    rw [cpu_roots_gen]
    cases hn : R.instAt i with
    | none =>
      rw [ite_zero _ _ (by
        show R.cpuCol ((i + 0) % K) (SEL + 11) = 0
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
        unfold cpuCol; rw [hn]; simp only
        rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (Nat.ne_of_gt (kindOf_lt _ _))])]
      simp only [hn]; rfl
    | some p =>
      obtain ⟨g, J⟩ := p
      have cv := R.inst_cols hi hn
      rw [cv, cv, cv, show R.instCol i g J HD = ofN (R.row i).hd from rfl, show R.instCol i g J J_G = ofN g from rfl,
        show R.instCol i g J (SEL + 11) = 1 from rfl]
      simp only [hn]
      rw [ofN_ind]; rfl
  · intro hc
    obtain ⟨i, _, hp⟩ := sumTo_pos_ex hc
    cases hn : R.instAt i with
    | none => simp only [hn] at hp; exact absurd hp (Nat.lt_irrefl 0)
    | some p =>
      obtain ⟨g, J⟩ := p
      simp only [hn] at hp
      split at hp
      · next e =>
        rw [← e]
        exact padCopies_super (List.mem_map.2 ⟨((R.row i).hd, g), (instAt_some hn).2.1, rfl⟩)
      · exact absurd hp (Nat.lt_irrefl 0)

/-- **`HDR` balances.** -/
theorem bal_hdr {K : Nat} (v : List F) :
    tableSends (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (R.cpuTable K) "hdr" v +
      tableSends (hdrAir R.jets) (provTable (hdrRows R.jets) (R.cntHdr K)) "hdr" v = 0 := by
  rw [show hdrAir R.jets = providerAir "hdr" 7 (hdrRows R.jets) from rfl, prov_sends (hdrRows_len R.jets)]
  apply bal_lookup
  · unfold tableSends cntHdr
    show (List.range K).foldr _ 0 = _
    rw [← fold_ofN]
    apply foldr_range_congr K
    intro i hi
    rw [cpu_hdr_gen]
    cases hn : R.instAt i with
    | none =>
      rw [ite_zero _ _ (by
        show R.cpuCol ((i + 0) % K) (SEL + 11) = 0
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
        unfold cpuCol; rw [hn]; simp only
        rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (Nat.ne_of_gt (kindOf_lt _ _))])]
      simp only [hn]; rfl
    | some p =>
      obtain ⟨g, J⟩ := p
      have cv := R.inst_cols hi hn
      rw [cv, cv, cv, cv, cv, cv, cv, cv, show R.instCol i g J (SEL + 11) = 1 from rfl]
      simp only [hn]
      rw [ofN_ind]
      show ind (_ = v) = ind (hdrRow J g = v)
      have e : [R.instCol i g J J_G, R.instCol i g J J_K, R.instCol i g J J_N, R.instCol i g J J_RL,
          R.instCol i g J J_RA, R.instCol i g J J_RG, R.instCol i g J J_RV] = hdrRow J g := by
        show [ofN g, ofN J.xs.length, ofN (symCells J J.body 0).1.length, (opCols (symCells J J.body 0).2).getD 0 0,
          (opCols (symCells J J.body 0).2).getD 1 0, (opCols (symCells J J.body 0).2).getD 2 0,
          (opCols (symCells J J.body 0).2).getD 3 0] = [ofN g, ofN J.xs.length, ofN (symCells J J.body 0).1.length] ++
          opCols (symCells J J.body 0).2
        cases (symCells J J.body 0).2 <;> rfl
      rw [e]
  · intro hc
    obtain ⟨i, _, hp⟩ := sumTo_pos_ex hc
    cases hn : R.instAt i with
    | none => simp only [hn] at hp; exact absurd hp (Nat.lt_irrefl 0)
    | some p =>
      obtain ⟨g, J⟩ := p
      simp only [hn] at hp
      split at hp
      · next e =>
        rw [← e]
        have hJ := (instAt_some hn).2.2.1
        obtain ⟨hg, hJg⟩ := List.getElem?_eq_some_iff.1 hJ
        exact padCopies_super (List.mem_map.2 ⟨(J, g), List.mem_zipIdx_iff_getElem?.2 (by
          simp only [Nat.sub_zero]; rw [List.getElem?_eq_getElem hg, hJg]), rfl⟩)
      · exact absurd hp (Nat.lt_irrefl 0)

end JRun

theorem zipIdx_sum {α : Type} (l : List α) (f : α → Nat → Nat) (d : α) :
    (l.zipIdx.map fun p => f p.1 p.2).sum = sumTo l.length (fun j => f (l.getD j d) j) := by
  rw [listSum_sumTo (fun p => f p.1 p.2) (d, 0) l.zipIdx, List.length_zipIdx]
  apply sumTo_congr
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_zipIdx]; exact hj),
    List.getElem_zipIdx, List.getD_eq_getElem?_getD (l := l), List.getElem?_eq_getElem hj]
  simp only [Nat.zero_add, Option.getD_some]

namespace JRun

variable (R : JRun)

/-- **`TMPL` balances.** -/
theorem bal_tmpl {K HW : Nat} (hHW : (R.instwRows K).length ≤ HW) (v : List F) :
    tableSends instwAir (R.instwTable K HW) "tmpl" v +
      tableSends (tmplAir R.jets) (provTable (tmplRows R.jets) (R.cntTmpl K)) "tmpl" v = 0 := by
  rw [show tmplAir R.jets = providerAir "tmpl" 11 (tmplRows R.jets) from rfl, prov_sends (tmplRows_len R.jets)]
  apply bal_lookup
  · rw [show R.instwTable K HW = ⟨HW, ofRows (R.instwRows K), fun _ _ => 0⟩ from rfl,
      sends_rows instw_nowOnly instw_quiet hHW, instwRows, foldr_flatMap]
    unfold cntTmpl
    rw [← fold_ofN]
    apply foldr_range_congr K
    intro i _
    cases hn : R.instAt i with
    | none => unfold instwRowsAt; rw [hn]; rfl
    | some p =>
      obtain ⟨g, J⟩ := p
      rw [R.instwRowsAt_eq hn, foldr_map_range]
      rw [foldr_range_congr _ (fun j _ => instw_tmpl i (R.row i).ctr g j (R.ps i J) _ v)]
      simp only [← ofN_ind]
      rw [fold_ofN]
      rw [zipIdx_sum (symCells J J.body 0).1 (fun cl j => if tmplRow g j cl = v then 1 else 0) (0, none)]
  · intro hc
    obtain ⟨i, _, hp⟩ := sumTo_pos_ex hc
    cases hn : R.instAt i with
    | none => simp only [hn] at hp; exact absurd hp (Nat.lt_irrefl 0)
    | some p =>
      obtain ⟨g, J⟩ := p
      simp only [hn] at hp
      rw [zipIdx_sum (symCells J J.body 0).1 (fun cl j => if tmplRow g j cl = v then 1 else 0) (0, none)] at hp
      obtain ⟨j, hj, hq⟩ := sumTo_pos_ex hp
      split at hq
      · next e =>
        rw [← e]
        have hJ := (instAt_some hn).2.2.1
        obtain ⟨hg, hJg⟩ := List.getElem?_eq_some_iff.1 hJ
        apply padCopies_super
        refine List.mem_flatMap.2 ⟨(J, g), List.mem_zipIdx_iff_getElem?.2 (by
          simp only [Nat.sub_zero]; rw [List.getElem?_eq_getElem hg, hJg]), ?_⟩
        refine List.mem_map.2 ⟨((symCells J J.body 0).1.getD j (0, none), j), List.mem_zipIdx_iff_getElem?.2 ?_, rfl⟩
        simp only [Nat.sub_zero]
        rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      · exact absurd hq (Nat.lt_irrefl 0)

end JRun

-- ---------------------------------------------------------------------------
-- Memory: every message is a cell's tuple
-- ---------------------------------------------------------------------------

theorem wrs_get {A : List Cell} : ∀ {c : Nat} {ws : List Cell}, wrs A c ws = true →
    ∀ j (hj : j < ws.length), A[c + j]? = some ws[j]
  | _, [], _, j, hj => absurd hj (Nat.not_lt_zero _)
  | c, w :: ws, h, j, hj => by
    unfold wrs at h
    rw [Bool.and_eq_true] at h
    cases j with
    | zero => rw [Nat.add_zero]; exact beq_iff_eq.1 h.1
    | succ j =>
      have := wrs_get h.2 j (by simp only [List.length_cons] at hj; omega)
      rw [show c + (j + 1) = c + 1 + j by omega]; exact this

theorem cpuInters_atomsJ : cpuInters.all (fun I => I.count.onlyAtoms cpuAtomJ && I.fields.all (·.onlyAtoms cpuAtomJ)) =
    true := by decide

theorem cellTag_cellOf {c : Nat} {ps : List Nat} {cl : Nat × Option (Op × Op)}
    (h : (cl.2 = none ∧ cl.1 < 3) ∨ (cl.1 = 3 ∧ ∃ a b, cl.2 = some (a, b))) :
    cellTag (JetTable.cellOf c ps cl) = cl.1 := by
  obtain ⟨t, ops⟩ := cl
  rcases h with ⟨hno, ht⟩ | ⟨ht, a, b, hso⟩
  · simp only at hno ht; subst hno
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl <;> rfl
  · simp only at ht hso; subst ht hso; rfl

namespace JRun

variable (R : JRun)

/-- **The CPU's memory messages are honest.** -/
theorem cpu_honestJ (hA : JOK R) (hsk : ∀ i, R.skip i = false) {K : Nat} :
    ∀ r, r < (R.cpuTable K).h → ∀ I ∈ cpuInters ++ jetInters, I.bus = "mem" →
      I.count.eval ((R.cpuTable K).env r) ≠ 0 →
      ∃ m, m < R.A.length ∧ I.fields.map (fun c => c.eval ((R.cpuTable K).env r)) = tupleOf R.A m := by
  intro r (hr : r < K) I hI hbus hc
  rcases List.mem_append.1 hI with hI | hI
  · cases hn : R.instAt r with
    | none =>
      have hv := base_valid hA hn (hsk r)
      have cong := E.eval_congr (R.env_agree hr hn)
      have ha := List.all_eq_true.1 cpuInters_atomsJ I hI
      rw [Bool.and_eq_true, List.all_eq_true] at ha
      rw [cong _ ha.1] at hc
      obtain ⟨m, hm, e⟩ := cpu_honestAt (M := R.A) (row := R.rowQ) (k := K) hr hv I hI hc
      refine ⟨m, hm, ?_⟩
      rw [← e]
      exact List.map_congr_left (fun c hc' => cong c (ha.2 c hc'))
    | some p =>
      obtain ⟨g, J⟩ := p
      exfalso
      have hsel : SelsAre (R.cpuTable K) r 11 := fun j hj => by
        show R.cpuCol r (SEL + j) = _
        unfold cpuCol; rw [hn]; exact R.instCol_sel r g J hj
      obtain ⟨hacts, _, happ, hS, _⟩ := inst_facts hr hsel
      simp only [cpuInters, writeInters, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hI
      rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hc (hacts 0 (by decide))
      · exact hc (hacts 1 (by decide))
      · exact hc (hacts 2 (by decide))
      · exact hc (hacts 3 (by decide))
      · exact hc happ
      all_goals exact hc hS
  · simp only [jetInters, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd hbus (by decide)

/-- **POP's memory messages are honest**: each reads a stack cell. -/
theorem pop_honest {K HP : Nat} :
    ∀ q, q < (R.popTable K HP).h → ∀ I ∈ popAir.inters, I.bus = "mem" →
      I.count.eval ((R.popTable K HP).env q) ≠ 0 →
      ∃ m, m < R.A.length ∧ I.fields.map (fun c => c.eval ((R.popTable K HP).env q)) = tupleOf R.A m := by
  intro q (hq : q < HP) I hI hbus hc
  have cv : ∀ c, (col c).eval ((R.popTable K HP).env q) = ofRows (R.popRows K) q c := by
    intro c; show ofRows (R.popRows K) ((q + 0) % HP) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
  simp only [popAir, popInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl
  · exact absurd hbus (by decide)
  · exact absurd hbus (by decide)
  · rcases ofRows_cases (R.popRows K) q with ⟨rw, hmem, hrw⟩ | hz
    · obtain ⟨i, g, J, j, s, x, s', _, hn, hget, rfl⟩ := R.popRows_mem hmem
      obtain ⟨_, hAs, _⟩ := R.pop_facts hn hget
      obtain ⟨hm, ht⟩ := tuple_get hAs
      obtain ⟨_, _, _, g3, g4, g5, _, _, _⟩ := popRow_get i (R.row i).ctr j s x s' (usesOf J j)
      refine ⟨s, hm, ?_⟩
      rw [ht]
      simp only [List.map_cons, List.map_nil, cv, hrw, g3, g4, g5, B.c, E.eval]
      rfl
    · exact absurd (by show (col 7).eval _ = 0; rw [cv, hz]) hc
  · exact absurd hbus (by decide)

/-- **INSTW's memory messages are honest**: each writes its cell. -/
theorem instw_honest {K HW : Nat} :
    ∀ q, q < (R.instwTable K HW).h → ∀ I ∈ instwAir.inters, I.bus = "mem" →
      I.count.eval ((R.instwTable K HW).env q) ≠ 0 →
      ∃ m, m < R.A.length ∧ I.fields.map (fun c => c.eval ((R.instwTable K HW).env q)) = tupleOf R.A m := by
  intro q (hq : q < HW) I hI hbus hc
  have cv : ∀ c, (col c).eval ((R.instwTable K HW).env q) = ofRows (R.instwRows K) q c := by
    intro c; show ofRows (R.instwRows K) ((q + 0) % HW) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
  simp only [instwAir, instwInters, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hbus (by decide)
  · exact absurd hbus (by decide)
  · exact absurd hbus (by decide)
  · exact absurd hbus (by decide)
  · exact absurd hbus (by decide)
  rcases ofRows_cases (R.instwRows K) q with ⟨rw, hmem, hrw⟩ | hz
  · obtain ⟨i, g, J, j, cl, _, hn, hcl, rfl⟩ := R.instwRows_mem hmem
    obtain ⟨_, _, hw, _⟩ := inst_spec hn
    have hj : j < (symCells J J.body 0).1.length := (List.getElem?_eq_some_iff.1 hcl).1
    have hclj : (symCells J J.body 0).1[j] = cl := (List.getElem?_eq_some_iff.1 hcl).2
    have hA := wrs_get hw j (by rw [List.length_map]; exact hj)
    rw [List.getElem_map, hclj] at hA
    obtain ⟨hm, ht⟩ := tuple_get hA
    have hshape := symCells_cells J J.body 0 cl (List.mem_of_getElem? hcl)
    refine ⟨(R.row i).ctr + j, hm, ?_⟩
    rw [ht, cellTag_cellOf hshape]
    obtain ⟨g0, g1, g2, g3, _⟩ := instwRow_get i (R.row i).ctr g j (R.ps i J) cl
    have e4 : (instwRow i (R.row i).ctr g j (R.ps i J) cl).getD 4 0 = ofN cl.1 := by
      obtain ⟨t, ops⟩ := cl
      cases ops with
      | none => rfl
      | some ab => obtain ⟨a, b⟩ := ab; cases a <;> cases b <;> rfl
    have e13 : (instwRow i (R.row i).ctr g j (R.ps i J) cl).getD 13 0 =
        ofN (cellFields (JetTable.cellOf (R.row i).ctr (R.ps i J) cl)).1 := by
      obtain ⟨t, ops⟩ := cl
      cases ops with
      | none => rfl
      | some ab => obtain ⟨a, b⟩ := ab; cases a <;> cases b <;> rfl
    have e14 : (instwRow i (R.row i).ctr g j (R.ps i J) cl).getD 14 0 =
        ofN (cellFields (JetTable.cellOf (R.row i).ctr (R.ps i J) cl)).2 := by
      obtain ⟨t, ops⟩ := cl
      cases ops with
      | none => rfl
      | some ab => obtain ⟨a, b⟩ := ab; cases a <;> cases b <;> rfl
    simp only [List.map_cons, List.map_nil, E.eval, cv, hrw, g1, g3, e4, e13, e14]
    rw [ofN_add]
  · exact absurd (by show (col 17).eval _ = 0; rw [cv, hz]) hc

end JRun

/-- A table's `mem` messages are memory cells' tuples. -/
def HonestMem (A : List Cell) (X : AirD) (T : Table) : Prop :=
  ∀ r, r < T.h → ∀ I ∈ X.inters, I.bus = "mem" → I.count.eval (T.env r) ≠ 0 →
    ∃ m, m < A.length ∧ I.fields.map (fun c => c.eval (T.env r)) = tupleOf A m

/-- `a + (-(a + (b + (c + d))) + (b + (c + d))) = 0`, by normal forms. -/
theorem bal4_identity (a b c d : F) : a + (-(a + (b + (c + d))) + (b + (c + d))) = 0 :=
  E.eval_eq_of_norm
    (e := .add (.atom (.main 0 0)) (.add (.neg (.add (.atom (.main 0 0)) (.add (.atom (.main 0 1))
      (.add (.atom (.main 0 2)) (.atom (.main 0 3)))))) (.add (.atom (.main 0 1))
      (.add (.atom (.main 0 2)) (.atom (.main 0 3))))))
    (e' := .const 0) (by decide) (at4 a b c d)

/-- **`mem` balances**: the memory table receives each cell's tuple as often
    as the CPU, the program, POP and INSTW send it. -/
theorem bal_mem4 {A : List Cell} {cpu prog pop instw : AirD} {C Pg Po Iw : Table} (hML : A.length < P)
    (hc : HonestMem A cpu C) (hp : HonestMem A prog Pg) (ho : HonestMem A pop Po) (hw : HonestMem A instw Iw)
    (v : List F) :
    tableSends cpu C "mem" v + (tableSends memAir (memTableJ A cpu prog pop instw C Pg Po Iw) "mem" v +
      (tableSends prog Pg "mem" v + (tableSends pop Po "mem" v + tableSends instw Iw "mem" v))) = 0 := by
  let Mm := memTableJ A cpu prog pop instw C Pg Po Iw
  have hrow : ∀ m, m < A.length → rowSends memAir Mm "mem" v m =
      if tupleOf A m = v then -(tableSends cpu C "mem" (tupleOf A m) + (tableSends prog Pg "mem" (tupleOf A m) +
        (tableSends pop Po "mem" (tupleOf A m) + tableSends instw Iw "mem" (tupleOf A m)))) else 0 := by
    intro m hm
    have hm' : m < Mm.h := hm
    simp only [rowSends, memAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, B.col, E.eval,
      env_main0 hm', true_and, add_zero']
    rfl
  cases hany : (List.range A.length).any (fun m => decide (tupleOf A m = v)) with
  | true =>
    obtain ⟨m0, hm0, e0⟩ := List.any_eq_true.1 hany
    have hm0 := List.mem_range.1 hm0
    have e0 := of_decide_eq_true e0
    have hmem : tableSends memAir Mm "mem" v = -(tableSends cpu C "mem" v + (tableSends prog Pg "mem" v +
        (tableSends pop Po "mem" v + tableSends instw Iw "mem" v))) := by
      show List.foldr (fun r acc => rowSends memAir Mm "mem" v r + acc) 0 (List.range A.length) = _
      rw [fold_single _ A.length m0 hm0, hrow m0 hm0, if_pos e0, e0]
      intro b hb hne
      rw [hrow b hb, if_neg]
      intro e
      rw [← e0] at e
      have := congrArg List.head? e
      simp only [tupleOf, List.head?_cons, Option.some.injEq] at this
      exact hne (ofN_inj (Nat.lt_trans hb hML) (Nat.lt_trans hm0 hML) this)
    rw [hmem]
    exact bal4_identity _ _ _ _
  | false =>
    have hno : ¬ ∃ m, m < A.length ∧ v = tupleOf A m := by
      rintro ⟨m, hm, e⟩
      have := List.any_eq_false.1 hany m (List.mem_range.2 hm)
      exact this (decide_eq_true e.symm)
    have z : ∀ {X : AirD} {T : Table}, HonestMem A X T → tableSends X T "mem" v = 0 := fun hX =>
      sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
        (fun r hr I hI hb hc => by obtain ⟨m, hm, e⟩ := hX r hr I hI hb hc; exact ⟨m, hm, e⟩) hno
    have h4 : tableSends memAir Mm "mem" v = 0 := by
      show List.foldr (fun r acc => rowSends memAir Mm "mem" v r + acc) 0 (List.range A.length) = 0
      apply fold_zero
      intro m hm
      rw [hrow m (List.mem_range.1 hm), if_neg (fun e => hno ⟨m, List.mem_range.1 hm, e.symm⟩)]
    rw [z hc, z hp, z ho, z hw, h4]; decide

end Circuit
