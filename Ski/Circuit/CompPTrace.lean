import Ski.Circuit.CompPBits

/-!
# The Poseidon2 table's honest row

The trace of `p2RowT c s` (defined in `CompPHonest.lean`): the inputs, then each round's columns, the last
sixteen the permutation's output (`traceAll_last`, `rounds_spec`); 650
columns in all, then the key and the activity (`p2RowT_len`).  The row
receives the inputs on `p2v` and sends the outputs on `p2w`
(`p2_sends_v`, `p2_sends_w`).
-/

namespace Circuit

open B Air Compose CompM Mach Poseidon2SKI

/-- The columns a round adds. -/
def lenR : P2Air.Round → Nat
  | .l0 => 16
  | .full _ => 48
  | .part _ => 18

theorem traceR_len (r : P2Air.Round) (hr : ∀ rc, r = .full rc → rc.length = 16) (vs : List Nat)
    (hv : vs.length = 16) : (traceR r vs).length = lenR r ∧ (r.spec vs).length = 16 := by
  cases r with
  | l0 =>
    have : (Poseidon2.extLinear vs).length = 16 := by rw [extLinear_split]; exact mixL_len _ (mat4L_len _ hv)
    exact ⟨this, this⟩
  | full rc =>
    have hc := hr rc rfl
    have h3 : (Poseidon2.extRound vs rc).length = 16 := by
      rw [extRound_split]; exact mixL_len _ (mat4L_len _ (sboxL_len rc vs hv hc))
    refine ⟨?_, h3⟩
    simp only [traceR, lenR]
    rw [List.length_append, List.length_append, List.length_map, List.length_map, List.length_range, h3]
  | part c =>
    have h3 : (Poseidon2.intRound vs c).length = 16 := by
      rw [intRound_split]; exact intLinear_len _ (by rw [sbox0L_len]; exact hv)
    refine ⟨?_, h3⟩
    simp only [traceR, lenR]
    rw [List.length_append, h3]; rfl

/-- A round's columns end with its new state. -/
theorem traceR_spec (r : P2Air.Round) (vs : List Nat) : ∃ X, traceR r vs = X ++ r.spec vs := by
  cases r with
  | l0 => exact ⟨[], rfl⟩
  | full rc => exact ⟨_, rfl⟩
  | part c => exact ⟨_, rfl⟩

theorem traceAll_len : ∀ (rs : List P2Air.Round), P2Air.RcOK rs → ∀ vs : List Nat, vs.length = 16 →
    (traceAll rs vs).length = (rs.map lenR).sum
  | [], _, _, _ => rfl
  | r :: rs, ⟨hr, hrs⟩, vs, hv => by
    obtain ⟨h1, h2⟩ := traceR_len r hr vs hv
    show (traceR r vs ++ traceAll rs (r.spec vs)).length = lenR r + (rs.map lenR).sum
    rw [List.length_append, h1, traceAll_len rs hrs _ h2]

/-- **The rounds' columns end with the last state.** -/
theorem traceAll_last : ∀ (rs : List P2Air.Round) (vs : List Nat), rs ≠ [] →
    ∃ X, traceAll rs vs = X ++ rs.foldl (fun v r => r.spec v) vs
  | [], _, h => absurd rfl h
  | [r], vs, _ => by
    obtain ⟨X, hX⟩ := traceR_spec r vs
    exact ⟨X, by show traceR r vs ++ [] = _; rw [List.append_nil, hX]; rfl⟩
  | r :: r' :: rs, vs, _ => by
    obtain ⟨X, hX⟩ := traceAll_last (r' :: rs) (r.spec vs) (List.cons_ne_nil _ _)
    exact ⟨traceR r vs ++ X, by show traceR r vs ++ traceAll (r' :: rs) (r.spec vs) = _; rw [hX, List.append_assoc]; rfl⟩

/-- The rounds' columns: with the sixteen inputs, 650 (`P2Air.COLS`); the
    output is the last sixteen, from column 634. -/
theorem rounds_len : (P2Air.rounds.map lenR).sum = 634 := by decide

theorem getD_append_lt {α : Type} (l l' : List α) (d : α) {i : Nat} (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem getD_append_ge {α : Type} (l l' : List α) (d : α) {i : Nat} (h : l.length ≤ i) :
    (l ++ l').getD i d = l'.getD (i - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

theorem getD_map_ofN (l : List Nat) (i : Nat) : (l.map ofN).getD i 0 = ofN (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem p2RowT_trace (s : List Nat) (hs : s.length = 16) :
    ∃ X, s ++ traceAll P2Air.rounds s = X ++ Poseidon2.permute s ∧ X.length = 634 := by
  obtain ⟨X, hX⟩ := traceAll_last P2Air.rounds s (by decide)
  rw [P2Air.rounds_spec] at hX
  have hl := traceAll_len P2Air.rounds P2Air.rounds_rcOK s hs
  rw [rounds_len, hX, List.length_append, permute_len s hs] at hl
  refine ⟨s ++ X, by rw [hX, List.append_assoc], ?_⟩
  rw [List.length_append, hs]; omega

theorem p2RowT_len (c : Nat) (s : List Nat) (hs : s.length = 16) : (p2RowT c s).length = 652 := by
  obtain ⟨X, hX, hl⟩ := p2RowT_trace s hs
  unfold p2RowT
  rw [hX, List.length_append, List.length_map, List.length_append, hl, permute_len s hs]; rfl

theorem p2Pad_len : p2Pad.length = 652 := by
  obtain ⟨X, hX, hl⟩ := p2RowT_trace (List.replicate 16 0) (List.length_replicate)
  unfold p2Pad
  rw [hX, List.length_append, List.length_map, List.length_append, hl,
    permute_len _ List.length_replicate]; rfl

theorem p2Pad_act : p2Pad.getD P2Air.ACT 0 = 0 := by
  obtain ⟨X, hX, hl⟩ := p2RowT_trace (List.replicate 16 0) (List.length_replicate)
  have hm : ((List.replicate 16 0 ++ traceAll P2Air.rounds (List.replicate 16 0)).map ofN).length = 650 := by
    rw [List.length_map, hX, List.length_append, hl, permute_len _ List.length_replicate]
  unfold p2Pad
  rw [getD_append_ge _ _ _ (by rw [hm]; decide), hm]; rfl

/-- The row's entries: the inputs, the outputs, the key, the activity. -/
theorem p2RowT_get (c : Nat) (s : List Nat) (hs : s.length = 16) :
    (∀ e, e < 16 → (p2RowT c s).getD e 0 = ofN (s.getD e 0)) ∧
    (∀ e, e < 16 → (p2RowT c s).getD (634 + e) 0 = ofN ((Poseidon2.permute s).getD e 0)) ∧
    (p2RowT c s).getD P2Air.KEY 0 = ofN c ∧ (p2RowT c s).getD P2Air.ACT 0 = 1 := by
  obtain ⟨X, hX, hl⟩ := p2RowT_trace s hs
  have hp := permute_len s hs
  have hm : ((s ++ traceAll P2Air.rounds s).map ofN).length = 650 := by
    rw [List.length_map, hX, List.length_append, hl, hp]
  unfold p2RowT
  refine ⟨fun e he => ?_, fun e he => ?_, ?_, ?_⟩
  · rw [getD_append_lt _ _ _ (by rw [hm]; omega), getD_map_ofN, getD_append_lt _ _ _ (by rw [hs]; exact he)]
  · rw [getD_append_lt _ _ _ (by rw [hm]; omega), getD_map_ofN, hX,
      getD_append_ge _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
  · rw [getD_append_ge _ _ _ (by rw [hm]; decide), hm]; rfl
  · rw [getD_append_ge _ _ _ (by rw [hm]; decide), hm]; rfl


-- ---------------------------------------------------------------------------
-- The Poseidon2 row's messages
-- ---------------------------------------------------------------------------

theorem p2Out_get {e : Nat} (he : e < 16) : P2Air.p2Out.getD e (c 0) = col (634 + e) := by
  rw [show P2Air.p2Out = P2Air.colsFrom 634 from rfl]
  exact getD_map_range (fun i => col (634 + i)) _ he

theorem p2_nowOnly : NowOnly P2Air.p2Air := by
  intro I hI
  rw [p2Air_inters] at hI
  rcases List.mem_append.1 hI with hI | hI <;> obtain ⟨e, he, rfl⟩ := List.mem_map.1 hI
  · refine ⟨rfl, fun x hx => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rfl
  · refine ⟨rfl, fun x hx => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rfl
    · rfl
    · rw [p2Out_get (List.mem_range.1 he)]; rfl

theorem p2_quiet : ZeroQuiet P2Air.p2Air := by
  intro I hI
  rw [p2Air_inters] at hI
  rcases List.mem_append.1 hI with hI | hI <;> obtain ⟨e, _, rfl⟩ := List.mem_map.1 hI
  · show -((envOf [] (.main 0 P2Air.ACT))) = 0
    exact neg_zero_eq
  · rfl

/-- One interaction's send from a row vector. -/
def sendI (rw : List F) (bus : String) (v : List F) (I : Inter) : F :=
  if I.bus = bus ∧ I.fields.map (fun e => e.eval (envOf rw)) = v then I.count.eval (envOf rw) else 0

theorem rowSendsV_maps (A : AirD) (f g : Nat → Inter) (hA : A.inters = (List.range 16).map f ++ (List.range 16).map g)
    (rw : List F) (bus : String) (v : List F) :
    rowSendsV A bus v rw = (List.range 16).foldr (fun e acc => sendI rw bus v (f e) + acc) 0 +
      (List.range 16).foldr (fun e acc => sendI rw bus v (g e) + acc) 0 := by
  show A.inters.foldr (fun I acc => sendI rw bus v I + acc) 0 = _
  rw [hA, List.foldr_append, List.foldr_map, List.foldr_map, fold_acc]

/-- **The Poseidon2 row receives its inputs on `p2v`.** -/
theorem p2_sends_v (cc : Nat) (s : List Nat) (hs : s.length = 16) (v : List F) :
    rowSendsV P2Air.p2Air "p2v" v (p2RowT cc s) =
      (List.range 16).foldr (fun e acc => -ind ([ofN cc, ofN e, ofN (s.getD e 0)] = v) + acc) 0 := by
  obtain ⟨gi, _, gk, ga⟩ := p2RowT_get cc s hs
  rw [rowSendsV_maps _ _ _ p2Air_inters]
  rw [fold_zero (fun e => sendI (p2RowT cc s) "p2v" v
    (⟨"p2w", 1, col P2Air.ACT, [col P2Air.KEY, c e, P2Air.p2Out.getD e (c 0)]⟩ : Inter)) _
    (fun e _ => if_neg (fun h => absurd (show "p2w" = "p2v" from h.1) (by decide))), add_zero']
  refine foldr_range_congr 16 (fun e he => ?_)
  show (if "p2v" = "p2v" ∧ [envOf _ (.main 0 P2Air.KEY), ofN e, envOf _ (.main 0 e)] = v
    then -(envOf (p2RowT cc s) (.main 0 P2Air.ACT)) else 0) = _
  rw [envOf_get, envOf_get, envOf_get, gk, ga, gi e he, ite_and_one, ite_neg_one _ 1 rfl]

/-- **The Poseidon2 row sends its outputs on `p2w`.** -/
theorem p2_sends_w (cc : Nat) (s : List Nat) (hs : s.length = 16) (v : List F) :
    rowSendsV P2Air.p2Air "p2w" v (p2RowT cc s) =
      (List.range 16).foldr (fun e acc => ind ([ofN cc, ofN e, ofN ((Poseidon2.permute s).getD e 0)] = v) + acc) 0 := by
  obtain ⟨_, go, gk, ga⟩ := p2RowT_get cc s hs
  rw [rowSendsV_maps _ _ _ p2Air_inters]
  rw [fold_zero (fun e => sendI (p2RowT cc s) "p2w" v
    (⟨"p2v", 1, .neg (col P2Air.ACT), [col P2Air.KEY, c e, col e]⟩ : Inter)) _
    (fun e _ => if_neg (fun h => absurd (show "p2v" = "p2w" from h.1) (by decide))), zero_add']
  refine foldr_range_congr 16 (fun e he => ?_)
  show (if "p2w" = "p2w" ∧ [envOf _ (.main 0 P2Air.KEY), ofN e, (P2Air.p2Out.getD e (c 0)).eval (envOf _)] = v
    then envOf (p2RowT cc s) (.main 0 P2Air.ACT) else 0) = _
  rw [p2Out_get he, envOf_get, envOf_get, gk, ga]
  show (if "p2w" = "p2w" ∧ [ofN cc, ofN e, (p2RowT cc s).getD (634 + e) 0] = v then 1 else 0) = _
  rw [go e he, ite_and_one]
  rfl

/-- **A padding row sends nothing**: it is inactive. -/
theorem p2Pad_sends (bus : String) (v : List F) : rowSendsV P2Air.p2Air bus v p2Pad = 0 := by
  rw [rowSendsV_maps _ _ _ p2Air_inters]
  have ha : envOf p2Pad (.main 0 P2Air.ACT) = 0 := by rw [envOf_get]; exact p2Pad_act
  generalize p2Pad = pr at ha ⊢
  rw [fold_zero _ _ (fun e _ => by
      unfold sendI
      exact ite_zero _ _ (by show -(envOf pr (.main 0 P2Air.ACT)) = 0; rw [ha]; exact neg_zero_eq)),
    fold_zero _ _ (fun e _ => by
      unfold sendI
      exact ite_zero _ _ ha)]
  exact add_zero' 0

end Circuit
