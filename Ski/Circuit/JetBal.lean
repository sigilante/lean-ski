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
theorem bal_popch {m0 : Mach} (hA : AcceptsJ R.A m0 R.roots R.jets R.k R.row) {K HP : Nat}
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
    have hv := base_valid hA hn
    have hs : (R.cpuTable K).env i (.main 0 (SEL + 11)) = 0 := by
      show R.cpuCol ((i + 0) % K) (SEL + 11) = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi']
      unfold cpuCol; rw [hn]; simp only
      rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (Nat.ne_of_gt (shape hv).lt)]
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
theorem bal_wch {m0 : Mach} (hA : AcceptsJ R.A m0 R.roots R.jets R.k R.row) {K HW : Nat}
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
    have hv := base_valid hA hn
    have hs : (R.cpuTable K).env i (.main 0 (SEL + 11)) = 0 := by
      show R.cpuCol ((i + 0) % K) (SEL + 11) = 0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi']
      unfold cpuCol; rw [hn]; simp only
      rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (Nat.ne_of_gt (shape hv).lt)]
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

end Circuit
