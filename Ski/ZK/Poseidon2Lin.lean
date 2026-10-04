import Ski.Circuit.P2Air

/-!
# Linear forms of expressions, modulo `p`

A normalizer for the linear part of Poseidon2's expressions (`Ex`, over
sixteen numbered inputs): `Ex.lin` gives an expression's coefficients and
constant modulo `p`, or `none` when it is not linear.  It is sound
(`lin_sound`): the expression's value is that form's, modulo `p`.  So two
linear maps over sixteen inputs are equal when the kernel finds their
coefficient rows equal (`linRows_sound`), and a matrix product is checked
the same way, by substituting one map's expressions into the other's.

`matVec p M s` is a matrix `M`, as its rows, applied to `s` modulo `p`.
-/

namespace Poseidon2.Lin

open Poseidon2SKI (Ex)

/-- `Σ cᵢ · ρ (j + i)`. -/
def dotF : List Nat → Nat → (Nat → Nat) → Nat
  | [], _, _ => 0
  | c :: cs, j, ρ => c * ρ j + dotF cs (j + 1) ρ

/-- The row of `n` entries from position `j` that is 1 at `i`, else 0. -/
def unitL (i : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | j, n + 1 => (if j = i then 1 else 0) :: unitL i (j + 1) n

def addL (c d : List Nat) : List Nat := List.zipWith (fun a b => (a + b) % p) c d

def scaleL (k : Nat) (c : List Nat) : List Nat := c.map fun a => k * a % p

/-- An expression's coefficients on inputs `0 … 15` and its constant,
    modulo `p`; `none` unless it is linear. -/
def lin : Ex → Option (List Nat × Nat)
  | .var i => if i < 16 then some (unitL i 0 16, 0) else none
  | .lit n => some (List.replicate 16 0, n % p)
  | .add a b => do
    let (c, k) ← lin a
    let (d, m) ← lin b
    some (addL c d, (k + m) % p)
  | .mul a b => do
    let (c, k) ← lin a
    let (d, m) ← lin b
    if c.all (· == 0) then some (scaleL k d, k * m % p)
    else if d.all (· == 0) then some (scaleL m c, k * m % p)
    else none
  | .md a => lin a
  | .sbox _ => none

-- ---------------------------------------------------------------------------
-- dotF's arithmetic
-- ---------------------------------------------------------------------------

theorem dotF_unitL (i : Nat) (ρ : Nat → Nat) :
    ∀ n j, dotF (unitL i j n) j ρ = if j ≤ i ∧ i < j + n then ρ i else 0
  | 0, j => by
    show 0 = _
    rw [if_neg (fun h => Nat.lt_irrefl i (Nat.lt_of_lt_of_le h.2 (Nat.le_trans (Nat.le_of_eq (Nat.add_zero j)) h.1)))]
  | n + 1, j => by
    show (if j = i then 1 else 0) * ρ j + dotF (unitL i (j + 1) n) (j + 1) ρ = _
    rw [dotF_unitL i ρ n (j + 1)]
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, if_neg (fun h => Nat.lt_irrefl j (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) h.1)),
        if_pos ⟨Nat.le_refl j, Nat.lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.succ_le_succ (Nat.le_add_right j n))⟩,
        Nat.one_mul, Nat.add_zero]
    · rw [if_neg hji, Nat.zero_mul, Nat.zero_add]
      by_cases hin : j + 1 ≤ i ∧ i < j + 1 + n
      · rw [if_pos hin, if_pos ⟨Nat.le_of_succ_le hin.1, by rw [Nat.add_right_comm] at hin; exact
          (Nat.add_assoc j n 1 ▸ hin.2)⟩]
      · rw [if_neg hin, if_neg]
        intro h
        apply hin
        refine ⟨Nat.lt_of_le_of_ne h.1 hji, ?_⟩
        rw [Nat.add_right_comm]; exact (Nat.add_assoc j n 1 ▸ h.2)

theorem dotF_unit (i : Nat) (hi : i < 16) (ρ : Nat → Nat) : dotF (unitL i 0 16) 0 ρ = ρ i := by
  rw [dotF_unitL, if_pos ⟨Nat.zero_le i, by rw [Nat.zero_add]; exact hi⟩]

theorem dotF_zero (ρ : Nat → Nat) : ∀ (c : List Nat) (j : Nat), c.all (· == 0) = true → dotF c j ρ = 0
  | [], _, _ => rfl
  | c :: cs, j, h => by
    have h' : (c == 0) = true ∧ cs.all (· == 0) = true := by
      rw [List.all_cons, Bool.and_eq_true] at h; exact h
    show c * ρ j + dotF cs (j + 1) ρ = 0
    rw [beq_iff_eq.mp h'.1, Nat.zero_mul, Nat.zero_add, dotF_zero ρ cs (j + 1) h'.2]

theorem replicate_all (n : Nat) : (List.replicate n 0).all (· == 0) = true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.all_cons, ih]; rfl

theorem dotF_addL (ρ : Nat → Nat) : ∀ (c d : List Nat) (j : Nat), c.length = d.length →
    dotF (addL c d) j ρ % p = (dotF c j ρ + dotF d j ρ) % p
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (by intro h; cases h)
  | _ :: _, [], _, h => absurd h (by intro h; cases h)
  | a :: c, b :: d, j, h => by
    show ((a + b) % p * ρ j + dotF (addL c d) (j + 1) ρ) % p =
      ((a * ρ j + dotF c (j + 1) ρ) + (b * ρ j + dotF d (j + 1) ρ)) % p
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, dotF_addL ρ c d (j + 1) (Nat.succ.inj h),
      ← Nat.add_mod, Nat.add_mul]
    congr 1
    rw [Nat.add_assoc, Nat.add_assoc]
    congr 1
    rw [← Nat.add_assoc, Nat.add_comm (b * ρ j), Nat.add_assoc]

theorem dotF_scaleL (ρ : Nat → Nat) (k : Nat) : ∀ (c : List Nat) (j : Nat),
    dotF (scaleL k c) j ρ % p = k * dotF c j ρ % p
  | [], _ => by show 0 % p = k * 0 % p; rw [Nat.mul_zero]
  | a :: c, j => by
    show (k * a % p * ρ j + dotF (scaleL k c) (j + 1) ρ) % p = k * (a * ρ j + dotF c (j + 1) ρ) % p
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, dotF_scaleL ρ k c (j + 1), ← Nat.add_mod,
      Nat.mul_add, Nat.mul_assoc]

theorem unitL_length (i : Nat) : ∀ n j, (unitL i j n).length = n
  | 0, _ => rfl
  | n + 1, j => by show (unitL i (j + 1) n).length + 1 = n + 1; rw [unitL_length i n]

theorem lin_length : ∀ (e : Ex) (c : List Nat) (k : Nat), lin e = some (c, k) → c.length = 16
  | .var i, c, k, h => by
    unfold lin at h
    by_cases hi : i < 16
    · rw [if_pos hi] at h; cases h; exact unitL_length i 16 0
    · rw [if_neg hi] at h; cases h
  | .lit n, c, k, h => by cases h; exact List.length_replicate
  | .add a b, c, k, h => by
    unfold lin at h
    cases ha : lin a with
    | none => rw [ha] at h; cases h
    | some ck =>
      cases hb : lin b with
      | none => rw [ha, hb] at h; cases h
      | some dm =>
        rw [ha, hb] at h
        cases h
        show (List.zipWith _ ck.1 dm.1).length = 16
        rw [List.length_zipWith, lin_length a ck.1 ck.2 ha, lin_length b dm.1 dm.2 hb]; rfl
  | .mul a b, c, k, h => by
    unfold lin at h
    cases ha : lin a with
    | none => rw [ha] at h; cases h
    | some ck =>
      cases hb : lin b with
      | none => rw [ha, hb] at h; cases h
      | some dm =>
        rw [ha, hb] at h
        dsimp only [Option.bind, bind] at h
        by_cases hc : ck.1.all (· == 0) = true
        · rw [if_pos hc] at h; cases h
          show (List.map _ dm.1).length = 16
          rw [List.length_map]; exact lin_length b dm.1 dm.2 hb
        · rw [if_neg hc] at h
          by_cases hd : dm.1.all (· == 0) = true
          · rw [if_pos hd] at h; cases h
            show (List.map _ ck.1).length = 16
            rw [List.length_map]; exact lin_length a ck.1 ck.2 ha
          · rw [if_neg hd] at h; cases h
  | .md a, c, k, h => lin_length a c k h
  | .sbox _, _, _, h => by cases h

/-- **The normalizer is sound**: a linear expression's value is its
    form's, modulo `p`. -/
theorem lin_sound (ρ : Nat → Nat) : ∀ (e : Ex) (c : List Nat) (k : Nat), lin e = some (c, k) →
    e.eval ρ % p = (dotF c 0 ρ + k) % p
  | .var i, c, k, h => by
    unfold lin at h
    by_cases hi : i < 16
    · rw [if_pos hi] at h; cases h
      show ρ i % p = _
      rw [dotF_unit i hi, Nat.add_zero]
    · rw [if_neg hi] at h; cases h
  | .lit n, c, k, h => by
    cases h
    show n % p = _
    rw [dotF_zero ρ _ 0 (replicate_all 16), Nat.zero_add, Nat.mod_mod]
  | .add a b, c, k, h => by
    unfold lin at h
    cases ha : lin a with
    | none => rw [ha] at h; cases h
    | some ck =>
      cases hb : lin b with
      | none => rw [ha, hb] at h; cases h
      | some dm =>
        rw [ha, hb] at h
        cases h
        show (a.eval ρ + b.eval ρ) % p = (dotF (addL ck.1 dm.1) 0 ρ + (ck.2 + dm.2) % p) % p
        rw [Nat.add_mod (a.eval ρ), lin_sound ρ a ck.1 ck.2 ha, lin_sound ρ b dm.1 dm.2 hb, ← Nat.add_mod,
          Nat.add_mod (dotF (addL ck.1 dm.1) 0 ρ), dotF_addL ρ ck.1 dm.1 0
            (by rw [lin_length a ck.1 ck.2 ha, lin_length b dm.1 dm.2 hb]), Nat.mod_mod, ← Nat.add_mod]
        congr 1
        rw [Nat.add_assoc, Nat.add_assoc]
        congr 1
        rw [← Nat.add_assoc, Nat.add_comm ck.2, Nat.add_assoc]
  | .mul a b, c, k, h => by
    unfold lin at h
    cases ha : lin a with
    | none => rw [ha] at h; cases h
    | some ck =>
      cases hb : lin b with
      | none => rw [ha, hb] at h; cases h
      | some dm =>
        rw [ha, hb] at h
        dsimp only [Option.bind, bind] at h
        have hA := lin_sound ρ a ck.1 ck.2 ha
        have hB := lin_sound ρ b dm.1 dm.2 hb
        show a.eval ρ * b.eval ρ % p = _
        by_cases hc : ck.1.all (· == 0) = true
        · rw [if_pos hc] at h; cases h
          rw [dotF_zero ρ ck.1 0 hc, Nat.zero_add] at hA
          rw [Nat.mul_mod, hA, hB, ← Nat.mul_mod, Nat.add_mod (dotF (scaleL ck.2 dm.1) 0 ρ),
            dotF_scaleL, Nat.mod_mod, ← Nat.add_mod, Nat.mul_add]
        · rw [if_neg hc] at h
          by_cases hd : dm.1.all (· == 0) = true
          · rw [if_pos hd] at h; cases h
            rw [dotF_zero ρ dm.1 0 hd, Nat.zero_add] at hB
            rw [Nat.mul_mod, hA, hB, ← Nat.mul_mod, Nat.add_mod (dotF (scaleL dm.2 ck.1) 0 ρ),
              dotF_scaleL, Nat.mod_mod, ← Nat.add_mod, Nat.mul_comm, Nat.mul_add, Nat.mul_comm dm.2 ck.2]
          · rw [if_neg hd] at h; cases h
  | .md a, c, k, h => by
    show a.eval ρ % p % p = _
    rw [Nat.mod_mod]; exact lin_sound ρ a c k h
  | .sbox _, _, _, h => by cases h

-- ---------------------------------------------------------------------------
-- Rows of reduced linear forms
-- ---------------------------------------------------------------------------

/-- The coefficient row of `md a` with `a` linear and no constant. -/
def linRow : Ex → Option (List Nat)
  | .md a => match lin a with
    | some (c, 0) => some c
    | _ => none
  | _ => none

/-- Each expression's row, or `none`. -/
def linRows (es : List Ex) : Option (List (List Nat)) := es.mapM linRow

theorem linRow_sound (ρ : Nat → Nat) (e : Ex) (c : List Nat) (h : linRow e = some c) :
    e.eval ρ = dotF c 0 ρ % p := by
  cases e with
  | md a =>
    change (match lin a with | some (c, 0) => some c | _ => none) = some c at h
    cases ha : lin a with
    | none => rw [ha] at h; cases h
    | some ck =>
      obtain ⟨c', k⟩ := ck
      rw [ha] at h
      cases k with
      | zero =>
        cases h
        show a.eval ρ % p = _
        rw [lin_sound ρ a c 0 ha, Nat.add_zero]
      | succ k => cases h
  | _ => cases h

/-- **Rows checked are rows computed**: if the kernel finds the rows
    `M`, the expressions compute `M` applied to the inputs. -/
theorem linRows_sound (ρ : Nat → Nat) : ∀ (es : List Ex) (M : List (List Nat)), linRows es = some M →
    es.map (Ex.eval ρ) = M.map (fun c => dotF c 0 ρ % p)
  | [], M, h => by cases h; rfl
  | e :: es, M, h => by
    unfold linRows at h
    rw [List.mapM_cons] at h
    cases he : linRow e with
    | none => rw [he] at h; cases h
    | some c =>
      cases hes : es.mapM linRow with
      | none => rw [he, hes] at h; cases h
      | some cs =>
        rw [he, hes] at h
        cases h
        show Ex.eval ρ e :: es.map (Ex.eval ρ) = (dotF c 0 ρ % p) :: cs.map _
        rw [linRow_sound ρ e c he, linRows_sound ρ es cs hes]

-- ---------------------------------------------------------------------------
-- Matrices on lists
-- ---------------------------------------------------------------------------

/-- `Σ rᵢ · sᵢ`, over the shorter of the two. -/
def dot : List Nat → List Nat → Nat
  | r :: rs, x :: xs => r * x + dot rs xs
  | _, _ => 0

/-- A matrix, as its rows, applied to `s` modulo `q`. -/
def matVec (q : Nat) (M : List (List Nat)) (s : List Nat) : List Nat := M.map fun r => dot r s % q

theorem dot_dotF : ∀ (r s : List Nat) (j : Nat), r.length ≤ s.length - j →
    dot r (s.drop j) = dotF r j (fun i => s.getD i 0)
  | [], s, j, _ => by cases s.drop j <;> rfl
  | c :: cs, s, j, h => by
    have hj : j < s.length := by
      have : 0 < s.length - j := Nat.lt_of_lt_of_le (Nat.succ_pos _) h
      exact Nat.lt_of_sub_pos this
    rw [List.drop_eq_getElem_cons hj]
    show c * s[j] + dot cs (s.drop (j + 1)) = c * s.getD j 0 + dotF cs (j + 1) _
    rw [dot_dotF cs s (j + 1) (by
      rw [Nat.sub_add_eq]; exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h)),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- The vector of sixteen inputs as an environment. -/
def env (s : List Nat) : Nat → Nat := fun i => s.getD i 0

theorem matVec_rows (M : List (List Nat)) (s : List Nat) (hM : ∀ r ∈ M, r.length ≤ s.length) :
    matVec p M s = M.map (fun c => dotF c 0 (env s) % p) := by
  unfold matVec
  apply List.map_congr_left
  intro r hr
  show dot r s % p = dotF r 0 (fun i => s.getD i 0) % p
  rw [← dot_dotF r s 0 (by rw [Nat.sub_zero]; exact hM r hr), List.drop_zero]

/-- The expression of a row: `md (Σ rᵢ · xᵢ)`. -/
def rowEx (r : List Nat) : Ex :=
  .md ((r.zipIdx).foldr (fun (c, i) acc => .add (.mul (.lit c) (.var i)) acc) (.lit 0))

theorem rowEx_eval_aux (ρ : Nat → Nat) : ∀ (r : List Nat) (j : Nat),
    ((r.zipIdx j).foldr (fun (c, i) acc => Ex.add (.mul (.lit c) (.var i)) acc) (.lit 0)).eval ρ = dotF r j ρ
  | [], _ => rfl
  | c :: cs, j => by
    show c * ρ j + _ = c * ρ j + dotF cs (j + 1) ρ
    rw [rowEx_eval_aux ρ cs (j + 1)]

theorem rowEx_eval (ρ : Nat → Nat) (r : List Nat) : (rowEx r).eval ρ = dotF r 0 ρ % p := by
  show _ % p = _
  rw [show r.zipIdx = r.zipIdx 0 from rfl, rowEx_eval_aux]

/-- A matrix applied to a vector is its row expressions' values. -/
theorem matVec_eval (M : List (List Nat)) (s : List Nat) (hM : ∀ r ∈ M, r.length ≤ s.length) :
    matVec p M s = (M.map rowEx).map (Ex.eval (env s)) := by
  rw [matVec_rows M s hM, List.map_map]
  apply List.map_congr_left
  intro r _
  exact (rowEx_eval (env s) r).symm

end Poseidon2.Lin
