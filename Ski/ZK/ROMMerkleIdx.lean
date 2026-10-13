import Ski.ZK.ROMMerkleRows

/-!
# FRI's query indices pick the opened leaves

`ROMMerkleRows` opens the leaves whose point in every opened group lies in
that group's query set (`isOfRows`).  Here each opened group's query set
holds the points `xs l k` of FRI's queried leaves `l ∈ idx` (for sets built
from the indices, `qSets`).  Every queried leaf is then opened
(`isOfRows_of_mem`), so the circuits' `hposO` holds with the opened set the
queried indices (`sud_hposO_idx`, `wit_hposO_idx`, `comp_hposO_idx`, by
`posRows_hposO`).  Conversely, among the `L` real leaves, when one opened
group places them at distinct points, every opened leaf is queried
(`mem_of_isOfRows`): the opened real leaves are exactly `idx`
(`isOfRows_iff`, `isOfRows_qSets_iff`; per circuit `sud_opened_iff`,
`wit_opened_iff`, `comp_opened_iff`).  The separation is asked only below
`L`: no map from all of `Nat` into the field is injective.  Points read off
the leaf index meet it for `L ≤ P` (`xsW_inj`, `sud_opened_iff_xsW`).  They show the
separation satisfiable, not the circuits' conditions that query points
lie off the trace domain (`hS16` …), which the LDE points `xsL` below
meet.

Mixed heights fit the converse.  In Plonky3 a shorter matrix's row serves
a block of leaves: leaf `l` reads row `l / 2 ^ sh k` of group `k`, where
`sh k` is the group's height deficit (`xsSh`).  The shorter groups' points
repeat, but the tallest group (`sh k0 = 0`) separates the leaves when its
`L` rows' points are distinct (`xsSh_inj`), so the tallest matrix's index
decides the opened leaf (`isOfRows_xsSh_iff`, for sets built by `qSets`;
the per-circuit theorems take any `xs`).

FRI's query points are the LDE coset `31 · ⟨ω⟩` at each group's row,
stored bit-reversed as Plonky3 stores them (`xsL`, `revBits`).  They lie
off every trace domain (`xsL_off`, by `lde_off_trace`), and the tallest
group's `2 ^ (bl k0 + 1)` points are distinct (`xsL_inj`, `revBits_inj`).
The faithful choice is `bl k` the group's LDE log height less one and
`sh k = bl 0 - bl k`, group 0 the tallest (for the Sudoku circuit,
`sudBl`, `sud_fri_leaves_std`, which assumes `tP ≤ 15`: evaluated, the
Sudoku program table has `progTp = 14` with no clues and with all 81, its
heap `24063` and `24225` cells, but no theorem bounds it below `23` for
every puzzle); `sud_fri_leaves` holds for any `bl`, `sh`
with `sh 0 = 0`, which at that choice asks the program table no
taller than `2 ^ 16` (`tP ≤ 15`), and `bl 0 ≤ 26` asks a log blowup of at
most 11.  For the Sudoku circuit with its query
sets built from FRI's indices at these points, the off-trace conditions
`hS16`, `hS10`, `hSP` hold, `hposO` holds at the queried leaves, and the
opened real leaves are exactly the queried ones (`sud_fri_leaves`).  The
Sudoku circuit's bound over the Merkle commitment then holds with these
query sets (`friS`), the rows' positions and the queried leaves opened,
those hypotheses discharged (`sud_fs_open4ROMM_fri`).  The
PCS views (`pcsZ`) and `hposO` read the same sets `S16 c4` ….  The
hidden-term and composed circuits likewise (`wit_fri_leaves`,
`wit_fs_open4ROMM_fri`, `comp_fri_leaves`, `comp_fs_open4ROMM_fri`), the
tallest opened group `k0` a parameter there, since their program tables
may outgrow the traces; the program and statement tables' heights come
from `wit_prog_height` and `comp_pub_heights`, the composed traces' from
`htM`, `htC` with `Lm, R ≤ 20`.

Not shown: that the indices are those Plonky3 draws from the fourth
challenge (`idx c4` is any list of leaves below the first round's tallest
height, assumed to be the global maximum height Plonky3 draws below; the size
conditions `hsz16` … stay hypotheses bounding its length); FRI's own layer
commitments and their openings (`friX` takes FRI as a function);
Plonky3's injection of shorter rows at internal nodes
(`compress_and_inject`), here the shared row `l / 2 ^ sh k` at the leaf;
and per-matrix salts.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The query sets of `G` groups generated from FRI's query indices: group
    `k`'s set holds the queried leaves' points `xs l k`. -/
def qSets (xs : Nat → Nat → F) (G : Nat) (idx : List Nat) : List (List F) :=
  (List.range G).map (fun k => idx.map (fun l => xs l k))

theorem qSets_getD {xs : Nat → Nat → F} {G : Nat} {idx : List Nat} {k : Nat} (hk : k < G) :
    (qSets xs G idx).getD k [] = idx.map (fun l => xs l k) := by
  unfold qSets
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- **Every queried leaf is opened**, when each opened group's query set
    holds the queried leaves' points. -/
theorem isOfRows_of_mem {Ss : List (List F)} {xs : Nat → Nat → F} {idx mk : List Nat} {l : Nat}
    (hS : ∀ k ∈ mk, Ss.getD k [] = idx.map (fun l => xs l k)) (hl : l ∈ idx) : isOfRows Ss mk xs l = true := by
  unfold isOfRows
  rw [List.all_eq_true]
  intro k hk
  rw [decide_eq_true_eq, hS k hk]
  exact List.mem_map.2 ⟨l, hl, rfl⟩

/-- **Every opened real leaf is queried**, when the queried indices are
    real leaves (`hidx`) and one opened group `k0` places the `L` real
    leaves at distinct points. -/
theorem mem_of_isOfRows {Ss : List (List F)} {xs : Nat → Nat → F} {idx mk : List Nat} {L l k0 : Nat}
    (hS : ∀ k ∈ mk, Ss.getD k [] = idx.map (fun l => xs l k)) (hidx : ∀ l ∈ idx, l < L) (hk0 : k0 ∈ mk)
    (hinj : ∀ l l', l < L → l' < L → xs l k0 = xs l' k0 → l = l') (hl : l < L) :
    isOfRows Ss mk xs l = true → l ∈ idx := by
  intro h
  unfold isOfRows at h
  have hm := of_decide_eq_true (List.all_eq_true.1 h k0 hk0)
  rw [hS k0 hk0] at hm
  obtain ⟨l', hl', e⟩ := List.mem_map.1 hm
  rw [← hinj l' l (hidx l' hl') hl e]; exact hl'

/-- **The opened real leaves are exactly the queried indices.** -/
theorem isOfRows_iff {Ss : List (List F)} {xs : Nat → Nat → F} {idx mk : List Nat} {L k0 : Nat}
    (hS : ∀ k ∈ mk, Ss.getD k [] = idx.map (fun l => xs l k)) (hidx : ∀ l ∈ idx, l < L) (hk0 : k0 ∈ mk)
    (hinj : ∀ l l', l < L → l' < L → xs l k0 = xs l' k0 → l = l') {l : Nat} (hl : l < L) :
    isOfRows Ss mk xs l = true ↔ l ∈ idx :=
  ⟨mem_of_isOfRows hS hidx hk0 hinj hl, isOfRows_of_mem hS⟩

/-- **`qSets` of FRI's indices: the opened real leaves are exactly the
    queried ones.** -/
theorem isOfRows_qSets_iff {xs : Nat → Nat → F} {G : Nat} {idx mk : List Nat} {L k0 : Nat}
    (hmk : ∀ k ∈ mk, k < G) (hidx : ∀ l ∈ idx, l < L) (hk0 : k0 ∈ mk)
    (hinj : ∀ l l', l < L → l' < L → xs l k0 = xs l' k0 → l = l') {l : Nat} (hl : l < L) :
    isOfRows (qSets xs G idx) mk xs l = true ↔ l ∈ idx :=
  isOfRows_iff (fun k hk => qSets_getD (hmk k hk)) hidx hk0 hinj hl

/-- Mixed heights: leaf `l` reads row `l / 2 ^ sh k` of group `k`, at point
    `pt k` of that row. -/
def xsSh (pt : Nat → Nat → F) (sh : Nat → Nat) (l k : Nat) : F :=
  pt k (l / 2 ^ sh k)

/-- The tallest group (`sh k0 = 0`) separates the `L` real leaves when its
    `L` rows' points are distinct. -/
theorem xsSh_inj {pt : Nat → Nat → F} {sh : Nat → Nat} {L k0 : Nat} (h0 : sh k0 = 0)
    (hpt : ∀ i j, i < L → j < L → pt k0 i = pt k0 j → i = j) :
    ∀ l l', l < L → l' < L → xsSh pt sh l k0 = xsSh pt sh l' k0 → l = l' := by
  intro l l' hl hl' e
  unfold xsSh at e
  rw [h0, Nat.pow_zero, Nat.div_one, Nat.div_one] at e
  exact hpt l l' hl hl' e

/-- **With mixed heights, the tallest group's index decides the opened
    leaf**: the opened real leaves are exactly the queried ones. -/
theorem isOfRows_xsSh_iff {pt : Nat → Nat → F} {sh : Nat → Nat} {G L : Nat} {idx mk : List Nat} {k0 : Nat}
    (hmk : ∀ k ∈ mk, k < G) (hidx : ∀ l ∈ idx, l < L) (hk0 : k0 ∈ mk) (h0 : sh k0 = 0)
    (hpt : ∀ i j, i < L → j < L → pt k0 i = pt k0 j → i = j) {l : Nat} (hl : l < L) :
    isOfRows (qSets (xsSh pt sh) G idx) mk (xsSh pt sh) l = true ↔ l ∈ idx :=
  isOfRows_qSets_iff hmk hidx hk0 (xsSh_inj h0 hpt) hl

/-- Points read off the leaf index. -/
def xsW (l _ : Nat) : F := ⟨l % P, Nat.mod_lt _ (by decide)⟩

/-- **The separation is satisfiable**: points read off the leaf index are
    distinct below `P`. -/
theorem xsW_inj {L k0 : Nat} (hL : L ≤ P) : ∀ l l', l < L → l' < L → xsW l k0 = xsW l' k0 → l = l' := by
  intro l l' hl hl' e
  have e' := congrArg Fin.val e
  simp only [xsW] at e'
  rwa [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hl hL), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hl' hL)] at e'

/-- The low `n` bits of `i`, reversed. -/
def revBits : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, i => i % 2 * 2 ^ n + revBits n (i / 2)

theorem revBits_lt : ∀ n i, revBits n i < 2 ^ n
  | 0, _ => by simp [revBits]
  | n + 1, i => by
    have ih := revBits_lt n (i / 2)
    have h2 : i % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
    show i % 2 * 2 ^ n + revBits n (i / 2) < 2 ^ (n + 1)
    rw [Nat.pow_succ]
    calc i % 2 * 2 ^ n + revBits n (i / 2) < i % 2 * 2 ^ n + 2 ^ n := Nat.add_lt_add_left ih _
      _ = (i % 2 + 1) * 2 ^ n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ n * 2 := Nat.mul_comm _ _

theorem revBits_inj : ∀ n i j, i < 2 ^ n → j < 2 ^ n → revBits n i = revBits n j → i = j
  | 0, i, j, hi, hj, _ => by simp at hi hj; omega
  | n + 1, i, j, hi, hj, e => by
    have ri := revBits_lt n (i / 2)
    have rj := revBits_lt n (j / 2)
    change i % 2 * 2 ^ n + revBits n (i / 2) = j % 2 * 2 ^ n + revBits n (j / 2) at e
    have hm : i % 2 = j % 2 := by
      have a := Nat.mod_lt i (show 0 < 2 by decide)
      have b := Nat.mod_lt j (show 0 < 2 by decide)
      rcases Nat.lt_or_ge (i % 2) 1 with h | h <;> rcases Nat.lt_or_ge (j % 2) 1 with h' | h'
      · omega
      · have : i % 2 = 0 := by omega
        have : j % 2 = 1 := by omega
        simp only [*, Nat.zero_mul, Nat.one_mul, Nat.zero_add] at e; omega
      · have : i % 2 = 1 := by omega
        have : j % 2 = 0 := by omega
        simp only [*, Nat.zero_mul, Nat.one_mul, Nat.zero_add] at e; omega
      · omega
    rw [hm] at e
    have e' := Nat.add_left_cancel e
    have hd := revBits_inj n (i / 2) (j / 2) (by rw [Nat.pow_succ] at hi; omega) (by rw [Nat.pow_succ] at hj; omega) e'
    omega

/-- FRI's query points: leaf `l` reads row `l / 2 ^ sh k` of group `k`, stored
    bit-reversed, on the LDE coset `31 · ⟨bbGen (bl k + 1)⟩` (Plonky3's
    `x = GENERATOR · ω ^ reverse_bits_len (index >> bits_reduced, log_h)`). -/
def xsL (bl sh : Nat → Nat) (l k : Nat) : F :=
  31 * fpow (bbGen (bl k + 1)) (revBits (bl k + 1) (l / 2 ^ sh k))

/-- **FRI's query points lie off every trace domain** (`lde_off_trace`):
    a query set built from any indices meets the circuits' `hS16`, `hS10`,
    `hSP` and the rest. -/
theorem xsL_off {bl sh : Nat → Nat} (hbl : ∀ k, bl k ≤ 26) {tb : Nat} (htb : tb ≤ 26) (idx : List Nat) (k : Nat) :
    ∀ x ∈ idx.map (fun l => xsL bl sh l k), x ∉ cosetL 1 (bbGen (tb + 1)) (2 ^ (tb + 1)) := by
  intro x hx
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
  exact lde_off_trace htb (hbl k) _

theorem mul31_cancel {a b : F} (h : 31 * a = 31 * b) : a = b := by
  have e : (31 : F) * (a - b) = 0 := by
    rw [show (31 : F) * (a - b) = 31 * a - 31 * b from
      fid (e := E.const 31 * (v 0 - v 1)) (e' := E.const 31 * v 0 - E.const 31 * v 1) (by decide) [a, b], h, sub_self']
  rcases mul_eq_zero e with e | e
  · exact absurd e (by decide)
  · exact sub_eq_zero e

/-- **The tallest group separates the real leaves**: its `2 ^ (bl k0 + 1)`
    LDE points are distinct (`fpow_inj`). -/
theorem xsL_inj {bl sh : Nat → Nat} {k0 : Nat} (h0 : sh k0 = 0) (hb : bl k0 ≤ 26) :
    ∀ l l', l < 2 ^ (bl k0 + 1) → l' < 2 ^ (bl k0 + 1) → xsL bl sh l k0 = xsL bl sh l' k0 → l = l' := by
  intro l l' hl hl' e
  unfold xsL at e
  rw [h0, Nat.pow_zero, Nat.div_one, Nat.div_one] at e
  exact revBits_inj _ l l' hl hl' (fpow_inj (bbGen_half (bl k0) hb) (revBits_lt _ _) (revBits_lt _ _) (mul31_cancel e))

/-- The query sets built from FRI's indices at the LDE points: group `k`'s
    set at fourth challenge `c4`. -/
def friS (bl sh : Nat → Nat) (idx : Nat → List Nat) (k c4 : Nat) : List F :=
  (idx c4).map (fun l => xsL bl sh l k)

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

/-- **The Sudoku circuit's `hposO` at FRI's queried leaves**: its first
    round opens groups `0, 2, 4, 6` (`S16`, `S16`, `S10`, `SP`); when each
    set holds the queried leaves' points, the opened values fix the queried
    leaves' positions (`posRows_hposO` at `isOfRows_of_mem`). -/
theorem sud_hposO_idx {tP : Nat} {S16 S10 SP : Nat → List F} {qv : EF → EF → List EF → F → List F → List F → List EF}
    {xs : Nat → Nat → F} {idx : Nat → List Nat} {h : List (List F) → Nat} {L NSl Mh : Nat}
    (h0 : ∀ c4, S16 c4 = (idx c4).map (fun l => xs l 0)) (h2 : ∀ c4, S16 c4 = (idx c4).map (fun l => xs l 2))
    (h4 : ∀ c4, S10 c4 = (idx c4).map (fun l => xs l 4)) (h6 : ∀ c4, SP c4 = (idx c4).map (fun l => xs l 6)) :
    ∀ c4 d d', opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d =
        opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows xs [0, 2, 4, 6] h L NSl Mh d l a = posRows xs [0, 2, 4, 6] h L NSl Mh d' l a := by
  intro c4 d d' e l a hl
  refine posRows_hposO _ d d' e l a (isOfRows_of_mem (fun k hk => ?_) (of_decide_eq_true hl))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact h0 c4
  · exact h2 c4
  · exact h4 c4
  · exact h6 c4

/-- **The hidden-term circuit's `hposO` at FRI's queried leaves** (groups
    `0, 2, 4, 6`: `S10`, `S10`, `S9`, `SP`). -/
theorem wit_hposO_idx {tP : Nat} {S10 S9 SP : Nat → List F} {qv : EF → EF → List EF → F → List F → List F → List EF}
    {xs : Nat → Nat → F} {idx : Nat → List Nat} {h : List (List F) → Nat} {L NSl Mh : Nat}
    (h0 : ∀ c4, S10 c4 = (idx c4).map (fun l => xs l 0)) (h2 : ∀ c4, S10 c4 = (idx c4).map (fun l => xs l 2))
    (h4 : ∀ c4, S9 c4 = (idx c4).map (fun l => xs l 4)) (h6 : ∀ c4, SP c4 = (idx c4).map (fun l => xs l 6)) :
    ∀ c4 d d', opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d =
        opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows xs [0, 2, 4, 6] h L NSl Mh d l a = posRows xs [0, 2, 4, 6] h L NSl Mh d' l a := by
  intro c4 d d' e l a hl
  refine posRows_hposO _ d d' e l a (isOfRows_of_mem (fun k hk => ?_) (of_decide_eq_true hl))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact h0 c4
  · exact h2 c4
  · exact h4 c4
  · exact h6 c4

/-- **The composed circuit's `hposO` at FRI's queried leaves** (groups
    `0, 2, 4, 6, 8`: `SM`, `SC`, `S9`, `SP`, `SS`). -/
theorem comp_hposO_idx {tbM tbC tpP tpS : Nat} {SM SC S9 SP SS : Nat → List F}
    {qv : EF → EF → List EF → F → List F → List F → List EF} {xs : Nat → Nat → F} {idx : Nat → List Nat}
    {h : List (List F) → Nat} {L NSl Mh : Nat}
    (h0 : ∀ c4, SM c4 = (idx c4).map (fun l => xs l 0)) (h2 : ∀ c4, SC c4 = (idx c4).map (fun l => xs l 2))
    (h4 : ∀ c4, S9 c4 = (idx c4).map (fun l => xs l 4)) (h6 : ∀ c4, SP c4 = (idx c4).map (fun l => xs l 6))
    (h8 : ∀ c4, SS c4 = (idx c4).map (fun l => xs l 8)) :
    ∀ c4 d d', opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8] d =
        opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows xs [0, 2, 4, 6, 8] h L NSl Mh d l a = posRows xs [0, 2, 4, 6, 8] h L NSl Mh d' l a := by
  intro c4 d d' e l a hl
  refine posRows_hposO _ d d' e l a (isOfRows_of_mem (fun k hk => ?_) (of_decide_eq_true hl))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact h0 c4
  · exact h2 c4
  · exact h4 c4
  · exact h6 c4
  · exact h8 c4

/-- **The Sudoku circuit's opened real leaves are FRI's queried indices**
    (groups `0, 2, 4, 6`: `S16`, `S16`, `S10`, `SP`). -/
theorem sud_opened_iff {tP : Nat} {S16 S10 SP : List F} {ζ : EF} {qv : EF → EF → List EF → F → List F → List F → List EF}
    {xs : Nat → Nat → F} {idx : List Nat} {L : Nat} (h0 : S16 = idx.map (fun l => xs l 0))
    (h2 : S16 = idx.map (fun l => xs l 2)) (h4 : S10 = idx.map (fun l => xs l 4)) (h6 : SP = idx.map (fun l => xs l 6))
    (hidx : ∀ l ∈ idx, l < L) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6])
    (hinj : ∀ l l', l < L → l' < L → xs l k0 = xs l' k0 → l = l') {l : Nat} (hl : l < L) :
    isOfRows ((sudGroups tP S16 S10 SP ζ qv).map (·.base.S)) [0, 2, 4, 6] xs l = true ↔ l ∈ idx := by
  refine isOfRows_iff (fun k hk => ?_) hidx hk0 hinj hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact h0
  · exact h2
  · exact h4
  · exact h6

/-- **The hidden-term circuit's opened real leaves are FRI's queried
    indices** (groups `0, 2, 4, 6`: `S10`, `S10`, `S9`, `SP`). -/
theorem wit_opened_iff {tP : Nat} {S10 S9 SP : List F} {ζ : EF} {qv : EF → EF → List EF → F → List F → List F → List EF}
    {xs : Nat → Nat → F} {idx : List Nat} {L : Nat} (h0 : S10 = idx.map (fun l => xs l 0))
    (h2 : S10 = idx.map (fun l => xs l 2)) (h4 : S9 = idx.map (fun l => xs l 4)) (h6 : SP = idx.map (fun l => xs l 6))
    (hidx : ∀ l ∈ idx, l < L) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6])
    (hinj : ∀ l l', l < L → l' < L → xs l k0 = xs l' k0 → l = l') {l : Nat} (hl : l < L) :
    isOfRows ((wGroups tP S10 S9 SP ζ qv).map (·.base.S)) [0, 2, 4, 6] xs l = true ↔ l ∈ idx := by
  refine isOfRows_iff (fun k hk => ?_) hidx hk0 hinj hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact h0
  · exact h2
  · exact h4
  · exact h6

/-- **The composed circuit's opened real leaves are FRI's queried indices**
    (groups `0, 2, 4, 6, 8`: `SM`, `SC`, `S9`, `SP`, `SS`). -/
theorem comp_opened_iff {tbM tbC tpP tpS : Nat} {SM SC S9 SP SS : List F} {ζ : EF}
    {qv : EF → EF → List EF → F → List F → List F → List EF} {xs : Nat → Nat → F} {idx : List Nat} {L : Nat}
    (h0 : SM = idx.map (fun l => xs l 0)) (h2 : SC = idx.map (fun l => xs l 2)) (h4 : S9 = idx.map (fun l => xs l 4))
    (h6 : SP = idx.map (fun l => xs l 6)) (h8 : SS = idx.map (fun l => xs l 8)) (hidx : ∀ l ∈ idx, l < L)
    {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6, 8]) (hinj : ∀ l l', l < L → l' < L → xs l k0 = xs l' k0 → l = l')
    {l : Nat} (hl : l < L) :
    isOfRows ((cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv).map (·.base.S)) [0, 2, 4, 6, 8] xs l = true ↔ l ∈ idx := by
  refine isOfRows_iff (fun k hk => ?_) hidx hk0 hinj hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h2
  · exact h4
  · exact h6
  · exact h8

/-- **`sud_opened_iff` at points read off the leaf index**: its hypotheses
    met, the query sets built from `idx`, for `L ≤ P`. -/
theorem sud_opened_iff_xsW {tP : Nat} {ζ : EF} {qv : EF → EF → List EF → F → List F → List F → List EF}
    {idx : List Nat} {L : Nat} (hL : L ≤ P) (hidx : ∀ l ∈ idx, l < L) {l : Nat} (hl : l < L) :
    isOfRows ((sudGroups tP (idx.map (fun l => xsW l 0)) (idx.map (fun l => xsW l 4)) (idx.map (fun l => xsW l 6))
      ζ qv).map (·.base.S)) [0, 2, 4, 6] xsW l = true ↔ l ∈ idx :=
  sud_opened_iff rfl rfl rfl rfl hidx (List.mem_cons_self ..) (xsW_inj hL) hl

/-- **The Sudoku circuit with FRI's query sets**: the sets `S16`, `S10`,
    `SP` built from FRI's indices `idx c4` at the LDE points `xsL` (groups
    `0, 2` share a height) meet the circuit's off-trace conditions, the
    circuit's `hposO` holds at the queried leaves, and the opened real leaves
    are exactly the queried ones. -/
theorem sud_fri_leaves {tP : Nat} {qv : EF → EF → List EF → F → List F → List F → List EF}
    {bl sh : Nat → Nat} (hbl : ∀ k, bl k ≤ 26) (h20 : bl 2 = bl 0) (s20 : sh 2 = sh 0) (hs0 : sh 0 = 0)
    (htP : tP ≤ 26) {idx : Nat → List Nat} (hidx : ∀ c4, ∀ l ∈ idx c4, l < 2 ^ (bl 0 + 1))
    {h : List (List F) → Nat} {NSl Mh : Nat} :
    let S16 := fun c4 => (idx c4).map (fun l => xsL bl sh l 0)
    let S10 := fun c4 => (idx c4).map (fun l => xsL bl sh l 4)
    let SP := fun c4 => (idx c4).map (fun l => xsL bl sh l 6)
    (∀ c4, ∀ x ∈ S16 c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) ∧ (∀ c4, ∀ x ∈ S10 c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) ∧
    (∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1))) ∧
    (∀ c4 d d', opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d =
        opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows (xsL bl sh) [0, 2, 4, 6] h (2 ^ (bl 0 + 1)) NSl Mh d l a =
          posRows (xsL bl sh) [0, 2, 4, 6] h (2 ^ (bl 0 + 1)) NSl Mh d' l a) ∧
    (∀ c4 l, l < 2 ^ (bl 0 + 1) →
      (isOfRows ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] (xsL bl sh) l = true ↔
        l ∈ idx c4)) := by
  intro S16 S10 SP
  have h2 : ∀ c4, S16 c4 = (idx c4).map (fun l => xsL bl sh l 2) := fun c4 => by
    show (idx c4).map (fun l => xsL bl sh l 0) = _
    unfold xsL; rw [h20, s20]
  refine ⟨fun c4 => xsL_off hbl (tb := 15) (by decide) _ 0, fun c4 => xsL_off hbl (tb := 9) (by decide) _ 4,
    fun c4 => xsL_off hbl htP _ 6, sud_hposO_idx (fun _ => rfl) h2 (fun _ => rfl) (fun _ => rfl), ?_⟩
  intro c4 l hl
  exact sud_opened_iff rfl (h2 c4) rfl rfl (hidx c4) (List.mem_cons_self ..) (xsL_inj hs0 (hbl 0)) hl

set_option maxRecDepth 100000 in
/-- **`sud_fs_open4ROMM` with FRI's query sets and the rows as leaves**: the
    query sets built from FRI's indices `idx c4` at the LDE points `xsL`
    (`friS`), the leaves' positions the rows' (`posRows`), the opened set the
    queried indices; `hS16`, `hS10`, `hSP`, `hposO`, `hdist`, `hlt` and `hs`
    discharged (`sud_fri_leaves`, `posRows_*`).  `hsz16` … stay, bounding
    the number of queries. -/
theorem sud_fs_open4ROMM_fri {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    {bl sh : Nat → Nat} {idx : Nat → List Nat}
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hsz16 : ∀ c4, 2 * ((friS bl sh idx 0) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ c4, 2 * ((friS bl sh idx 4) c4).length + 8 ≤ 2 ^ 10)
    (hszP : ∀ c4, 2 * ((friS bl sh idx 6) c4).length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V)
    (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NSl L KA sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKA : 0 < KA) (hN : 0 < NSl) (hKL : KQ = KA ^ L)
    (hbl : ∀ k, bl k ≤ 26) (h20 : bl 2 = bl 0) (s20 : sh 2 = sh 0) (hs0 : sh 0 = 0)
    (hidx : ∀ c4, ∀ l ∈ idx c4, l < L) (hL : L = 2 ^ (bl 0 + 1))
    {h : List (List F) → Nat} {Mh : Nat} (hMh : 0 < Mh) (hnQ : L * (NSl * Mh) ≤ nQ) (hsQ : 1 ≤ sQ) (g : List (List (List F)) → List Nat → Pq)
    (nxt : Pq → Nat → List Nat → Nat) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((sudGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (sudSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.1, opCw (sudSsC tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF → Bool) :
    let opS := fun (c4 : Nat) => opF ((sudGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]
    let Com1 := comM KA NSl L (posRows (xsL bl sh) [0, 2, 4, 6] h L NSl Mh)
    let Pf1 := fun (c4 : Nat) => pfM KA NSl L kQ (posRows (xsL bl sh) [0, 2, 4, 6] h L NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let Cmi := comMI KA NSl L L (posRows (xsL bl sh) [0, 2, 4, 6] h L NSl Mh)
    let Pfi := fun (c4 : Nat) => pfMI KA NSl L L kQ (posRows (xsL bl sh) [0, 2, 4, 6] h L NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP ((friS bl sh idx 0) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let sm4R := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    KQ * (K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4R (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 => sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
          (K2 * (Q4 * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * Q4) * (K4 ^ N4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
        (KQ * (L * (KA ^ nQ * (NSl ^ (L - 1) * (sQ * kQ)))) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1))))))))) := by
  have htP26 : tP ≤ 26 := by
    rw [htp]; exact Nat.le_trans (sud_prog_height hc hA hlen).1 (by decide)
  subst hL
  exact sud_fs_open4ROMM off hc hA hacc hlen hk htp (friS bl sh idx 0) (friS bl sh idx 4) (friS bl sh idx 6)
    qv wm wc ww wp hlwm hlwc hlww hlwp hK2
    hK4 φ hφ (sud_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hs0 htP26 hidx).1 (sud_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hs0 htP26 hidx).2.1 (sud_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hs0 htP26 hidx).2.2.1 hsz16 hsz hszP αd
    hB4 fri hncw NR2 Rb Ro hKA hN hKL (posRows (xsL bl sh) [0, 2, 4, 6] h _ NSl Mh)
    (fun d l l' a b hl hl' hne => posRows_dist d l l' a b hl hl' hne) (fun d l a hl => Nat.lt_of_lt_of_le (posRows_lt hN hMh d l a hl) hnQ) g (fun d l v => Nat.le_trans (posRows_spread (Nat.two_pow_pos _) d l v) hsQ) nxt (fun c4 l => decide (l ∈ idx c4)) (sud_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hs0 htP26 hidx).2.2.2.1 d1 Com2 Pf2
    hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3
    E

/-- The Sudoku circuit's group heights: LDE log height less one of group `k`
    at log blowup `r` (groups `0`–`3` the `2 ^ 16` traces, `4`, `5` the
    `2 ^ 10` table, `6`, `7` the program table `2 ^ (tP + 1)`). -/
def sudBl (tP r k : Nat) : Nat :=
  if k < 4 then 15 + r else if k < 6 then 9 + r else tP + r

/-- **`sud_fri_leaves` at the circuit's own heights**: `bl := sudBl tP r`,
    `sh k := bl 0 - bl k`, for a program table no taller than the traces
    (`tP ≤ 15`) and a log blowup `r ≤ 11`. -/
theorem sud_fri_leaves_std {tP r : Nat} (htP : tP ≤ 15) (hr : r ≤ 11)
    {qv : EF → EF → List EF → F → List F → List F → List EF} {idx : Nat → List Nat}
    (hidx : ∀ c4, ∀ l ∈ idx c4, l < 2 ^ (sudBl tP r 0 + 1)) {h : List (List F) → Nat} {NSl Mh : Nat} :
    let bl := sudBl tP r
    let sh := fun k => sudBl tP r 0 - sudBl tP r k
    let S16 := fun c4 => (idx c4).map (fun l => xsL bl sh l 0)
    let S10 := fun c4 => (idx c4).map (fun l => xsL bl sh l 4)
    let SP := fun c4 => (idx c4).map (fun l => xsL bl sh l 6)
    (∀ c4, ∀ x ∈ S16 c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) ∧ (∀ c4, ∀ x ∈ S10 c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) ∧
    (∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1))) ∧
    (∀ c4 d d', opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d =
        opF ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows (xsL bl sh) [0, 2, 4, 6] h (2 ^ (bl 0 + 1)) NSl Mh d l a =
          posRows (xsL bl sh) [0, 2, 4, 6] h (2 ^ (bl 0 + 1)) NSl Mh d' l a) ∧
    (∀ c4 l, l < 2 ^ (bl 0 + 1) →
      (isOfRows ((sudGroups tP (S16 c4) (S10 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] (xsL bl sh) l = true ↔
        l ∈ idx c4)) := by
  intro bl sh
  have hbl : ∀ k, bl k ≤ 26 := fun k => by
    show sudBl tP r k ≤ 26
    unfold sudBl; split
    · exact Nat.le_trans (Nat.add_le_add_left hr 15) (by decide)
    · split
      · exact Nat.le_trans (Nat.add_le_add_left hr 9) (by decide)
      · exact Nat.le_trans (Nat.add_le_add htP hr) (by decide)
  exact sud_fri_leaves (bl := bl) (sh := sh) (h := h) (NSl := NSl) (Mh := Mh) (tP := tP) (qv := qv) hbl rfl rfl (Nat.sub_self _)
    (Nat.le_trans htP (by decide)) hidx

/-- **The hidden-term circuit with FRI's query sets** (`sud_fri_leaves` for
    groups `0, 2, 4, 6`: `S10`, `S10`, `S9`, `SP`): the tallest opened group
    `k0` need not be group 0, the program table reaching `2 ^ 24`. -/
theorem wit_fri_leaves {tP : Nat} {qv : EF → EF → List EF → F → List F → List F → List EF}
    {bl sh : Nat → Nat} (hbl : ∀ k, bl k ≤ 26) (h20 : bl 2 = bl 0) (s20 : sh 2 = sh 0) {k0 : Nat}
    (hk0 : k0 ∈ [0, 2, 4, 6]) (hs0 : sh k0 = 0)
    (htP : tP ≤ 26) {idx : Nat → List Nat} (hidx : ∀ c4, ∀ l ∈ idx c4, l < 2 ^ (bl k0 + 1))
    {h : List (List F) → Nat} {NSl Mh : Nat} :
    let S10 := fun c4 => (idx c4).map (fun l => xsL bl sh l 0)
    let S9 := fun c4 => (idx c4).map (fun l => xsL bl sh l 4)
    let SP := fun c4 => (idx c4).map (fun l => xsL bl sh l 6)
    (∀ c4, ∀ x ∈ S10 c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) ∧ (∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9)) ∧
    (∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1))) ∧
    (∀ c4 d d', opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d =
        opF ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows (xsL bl sh) [0, 2, 4, 6] h (2 ^ (bl k0 + 1)) NSl Mh d l a =
          posRows (xsL bl sh) [0, 2, 4, 6] h (2 ^ (bl k0 + 1)) NSl Mh d' l a) ∧
    (∀ c4 l, l < 2 ^ (bl k0 + 1) →
      (isOfRows ((wGroups tP (S10 c4) (S9 c4) (SP c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6] (xsL bl sh) l = true ↔
        l ∈ idx c4)) := by
  intro S10 S9 SP
  have h2 : ∀ c4, S10 c4 = (idx c4).map (fun l => xsL bl sh l 2) := fun c4 => by
    show (idx c4).map (fun l => xsL bl sh l 0) = _
    unfold xsL; rw [h20, s20]
  refine ⟨fun c4 => xsL_off hbl (tb := 9) (by decide) _ 0, fun c4 => xsL_off hbl (tb := 8) (by decide) _ 4,
    fun c4 => xsL_off hbl htP _ 6, wit_hposO_idx (fun _ => rfl) h2 (fun _ => rfl) (fun _ => rfl), ?_⟩
  intro c4 l hl
  exact wit_opened_iff rfl (h2 c4) rfl rfl (hidx c4) hk0 (xsL_inj hs0 (hbl k0)) hl

set_option maxRecDepth 100000 in
/-- **`wit_fs_open4ROMM` with FRI's query sets and the rows as leaves**
    (`sud_fs_open4ROMM_fri` for the hidden-term circuit, the tallest opened
    group `k0`): `hS10`, `hS9`, `hSP`, `hposO`, `hdist`, `hlt` and `hs`
    discharged; `hsz10` … stay. -/
theorem wit_fs_open4ROMM_fri {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
    (hwl : ws.length = W) (hW8 : W ≤ 2 ^ 8) {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (wMachine ws (Vt ⬝ x)) k row)
    (hK : rd A (row (k - 1)).ctr (row (k - 1)).hd = some .K ∧ rd A (row (k - 1)).ctr (row (k - 1)).stk = some .nil)
    (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10)
    {tP : Nat} (htp : tP = progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W)
    {bl sh : Nat → Nat} {idx : Nat → List Nat}
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hsz10 : ∀ c4, 2 * ((friS bl sh idx 0) c4).length + 8 ≤ 2 ^ 10) (hsz9 : ∀ c4, 2 * ((friS bl sh idx 4) c4).length + 8 ≤ 2 ^ 9)
    (hszP : ∀ c4, 2 * ((friS bl sh idx 6) c4).length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NSl L KA sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKA : 0 < KA) (hN : 0 < NSl) (hKL : KQ = KA ^ L)
    (hbl : ∀ k, bl k ≤ 26) (h20 : bl 2 = bl 0) (s20 : sh 2 = sh 0) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6])
    (hs0 : sh k0 = 0) (hidx : ∀ c4, ∀ l ∈ idx c4, l < L) (hL : L = 2 ^ (bl k0 + 1))
    {h : List (List F) → Nat} {Mh : Nat} (hMh : 0 < Mh) (hnQ : L * (NSl * Mh) ≤ nQ) (hsQ : 1 ≤ sQ) (g : List (List (List F)) → List Nat → Pq)
    (nxt : Pq → Nat → List Nat → Nat) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((wGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (wSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.1, opCw (wSsC tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) EF → Bool) :
    let opS := fun (c4 : Nat) => opF ((wGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6]
    let Com1 := comM KA NSl L (posRows (xsL bl sh) [0, 2, 4, 6] h L NSl Mh)
    let Pf1 := fun (c4 : Nat) => pfM KA NSl L kQ (posRows (xsL bl sh) [0, 2, 4, 6] h L NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let Cmi := comMI KA NSl L L (posRows (xsL bl sh) [0, 2, 4, 6] h L NSl Mh)
    let Pfi := fun (c4 : Nat) => pfMI KA NSl L L kQ (posRows (xsL bl sh) [0, 2, 4, 6] h L NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP ((friS bl sh idx 0) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP ((friS bl sh idx 0) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let sm4R := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    KQ * (K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4R (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 => sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
          (K2 * (Q4 * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * Q4) * (K4 ^ N4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
        (KQ * (L * (KA ^ nQ * (NSl ^ (L - 1) * (sQ * kQ)))) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1))))))))) := by
  have htP26 : tP ≤ 26 := by
    rw [htp]; exact Nat.le_trans (wit_prog_height hwl hA hlen).2.1 (by decide)
  subst hL
  exact wit_fs_open4ROMM off hwf hwl hW8 hA hK hlen hk htp (friS bl sh idx 0)
    (friS bl sh idx 4) (friS bl sh idx 6) qv wm wc ww wp hlwm hlwc hlww
    hlwp hK2 hK4 φ hφ (wit_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hk0 hs0 htP26 hidx).1 (wit_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hk0 hs0 htP26 hidx).2.1 (wit_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hk0 hs0 htP26 hidx).2.2.1 hsz10 hsz9
    hszP αd hB4 fri hncw NR2 Rb Ro hKA hN
    hKL (posRows (xsL bl sh) [0, 2, 4, 6] h _ NSl Mh) (fun d l l' a b hl hl' hne => posRows_dist d l l' a b hl hl' hne) (fun d l a hl => Nat.lt_of_lt_of_le (posRows_lt hN hMh d l a hl) hnQ) g (fun d l v => Nat.le_trans (posRows_spread (Nat.two_pow_pos _) d l v) hsQ) nxt (fun c4 l => decide (l ∈ idx c4)) (wit_fri_leaves (tP := tP) (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl h20 s20 hk0 hs0 htP26 hidx).2.2.2.1 d1
    Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3
    hr3 d3 E

/-- **The composed circuit with FRI's query sets** (groups `0, 2, 4, 6, 8`:
    `SM`, `SC`, `S9`, `SP`, `SS`, five heights): the tallest opened group
    `k0` is any of them. -/
theorem comp_fri_leaves {tbM tbC tpP tpS : Nat} {qv : EF → EF → List EF → F → List F → List F → List EF}
    {bl sh : Nat → Nat} (hbl : ∀ k, bl k ≤ 26) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6, 8]) (hs0 : sh k0 = 0)
    (hM : tbM ≤ 26) (hC : tbC ≤ 26) (hP : tpP ≤ 26) (hSg : tpS ≤ 26)
    {idx : Nat → List Nat} (hidx : ∀ c4, ∀ l ∈ idx c4, l < 2 ^ (bl k0 + 1))
    {h : List (List F) → Nat} {NSl Mh : Nat} :
    let SM := fun c4 => (idx c4).map (fun l => xsL bl sh l 0)
    let SC := fun c4 => (idx c4).map (fun l => xsL bl sh l 2)
    let S9 := fun c4 => (idx c4).map (fun l => xsL bl sh l 4)
    let SP := fun c4 => (idx c4).map (fun l => xsL bl sh l 6)
    let SS := fun c4 => (idx c4).map (fun l => xsL bl sh l 8)
    (∀ c4, ∀ x ∈ SM c4, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1))) ∧
    (∀ c4, ∀ x ∈ SC c4, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1))) ∧
    (∀ c4, ∀ x ∈ S9 c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9)) ∧
    (∀ c4, ∀ x ∈ SP c4, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1))) ∧
    (∀ c4, ∀ x ∈ SS c4, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1))) ∧
    (∀ c4 d d', opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8] d =
        opF ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8] d' →
      ∀ l a, decide (l ∈ idx c4) = true →
        posRows (xsL bl sh) [0, 2, 4, 6, 8] h (2 ^ (bl k0 + 1)) NSl Mh d l a =
          posRows (xsL bl sh) [0, 2, 4, 6, 8] h (2 ^ (bl k0 + 1)) NSl Mh d' l a) ∧
    (∀ c4 l, l < 2 ^ (bl k0 + 1) →
      (isOfRows ((cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) EF.zero qv).map (·.base.S))
        [0, 2, 4, 6, 8] (xsL bl sh) l = true ↔ l ∈ idx c4)) := by
  intro SM SC S9 SP SS
  refine ⟨fun c4 => xsL_off hbl hM _ 0, fun c4 => xsL_off hbl hC _ 2, fun c4 => xsL_off hbl (tb := 8) (by decide) _ 4,
    fun c4 => xsL_off hbl hP _ 6, fun c4 => xsL_off hbl hSg _ 8,
    comp_hposO_idx (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), ?_⟩
  intro c4 l hl
  exact comp_opened_iff rfl rfl rfl rfl rfl (hidx c4) hk0 (xsL_inj hs0 (hbl k0)) hl

set_option maxRecDepth 100000 in
/-- **`comp_fs_open4ROMM` with FRI's query sets and the rows as leaves**
    (`sud_fs_open4ROMM_fri` for the composed circuit, the tallest opened group
    `k0`): `hSM`, `hSC`, `hS9`, `hSP`, `hSS`, `hposO`, `hdist`, `hlt` and `hs`
    discharged, the tables' heights from `comp_pub_heights`; `hszM` … stay. -/
theorem comp_fs_open4ROMM_fri {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
    {W : Nat} {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8)
    {tbM tbC tpP tpS : Nat} (htM : tbM + 1 = Lm) (htC : tbC + 1 = R)
    (htP : tpP = progTpC (blankM shp W Ps).heap (BT.nleaves shp) W) (htS : tpS = segTp (blankRoots shp W Ps))
    {bl sh : Nat → Nat} {idx : Nat → List Nat}
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp Lwsg : Nat} (hlwm : ∀ c, (wm c).length = Lwm)
    (hlwc : ∀ c, (wc c).length = Lwc) (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    (hlwsg : ∀ c, (wsg c).length = Lwsg)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ m w, φ m w < N4)
    (hszM : ∀ c4, 2 * ((friS bl sh idx 0) c4).length + 8 ≤ 2 ^ (tbM + 1)) (hszC : ∀ c4, 2 * ((friS bl sh idx 2) c4).length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : ∀ c4, 2 * ((friS bl sh idx 4) c4).length + 8 ≤ 2 ^ 9) (hszP : ∀ c4, 2 * ((friS bl sh idx 6) c4).length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : ∀ c4, 2 * ((friS bl sh idx 8) c4).length + 8 ≤ 2 ^ (tpS + 1)) {ncw : Nat} (αd : Nat → EF) {B4 : Nat}
    (hB4 : sumTo K4 (fun c4 => indB (!genB (αd c4))) ≤ B4) (fri : Nat → EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {NSl L KA sQ kQ nQ KQ NS2 NS3 n2 n3 : Nat} (hKA : 0 < KA) (hN : 0 < NSl) (hKL : KQ = KA ^ L)
    (hbl : ∀ k, bl k ≤ 26) {k0 : Nat} (hk0 : k0 ∈ [0, 2, 4, 6, 8])
    (hs0 : sh k0 = 0) (hidx : ∀ c4, ∀ l ∈ idx c4, l < L) (hL : L = 2 ^ (bl k0 + 1))
    {h : List (List F) → Nat} {Mh : Nat} (hMh : 0 < Mh) (hnQ : L * (NSl * Mh) ≤ nQ) (hsQ : 1 ≤ sQ) (g : List (List (List F)) → List Nat → Pq)
    (nxt : Pq → Nat → List Nat → Nat) (d1 : List (List (List F)))
    (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → List (List (List F)) → Nat → P2) (hc2 : ComHides NS2 Com2)
    (hp2 : ∀ c4, ComPfHides NS2 Com2 (Pf2 c4) (opF ((cGroups tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9]))
    (hr2 : ∀ d σ, Com2 d σ < n2) (d2 : List (List (List F)))
    (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3 : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ComHides NS3 Com3)
    (hp3 : ∀ c4, ComPfHides NS3 Com3 (Pf3 c4) (fun d => (opQ (cSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4)) d.1, opCw (cSsC tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4)) d.2)))
    (hr3 : ∀ d σ, Com3 d σ < n3) (d3 : List (List (List (List F))) × List (List (List F)))
    (E : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Pq × List Nat) × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
    let opS := fun (c4 : Nat) => opF ((cGroups tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) EF.zero qv).map (·.base.S)) [0, 2, 4, 6, 8]
    let Com1 := comM KA NSl L (posRows (xsL bl sh) [0, 2, 4, 6, 8] h L NSl Mh)
    let Pf1 := fun (c4 : Nat) => pfM KA NSl L kQ (posRows (xsL bl sh) [0, 2, 4, 6, 8] h L NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let Cmi := comMI KA NSl L L (posRows (xsL bl sh) [0, 2, 4, 6, 8] h L NSl Mh)
    let Pfi := fun (c4 : Nat) => pfMI KA NSl L L kQ (posRows (xsL bl sh) [0, 2, 4, 6, 8] h L NSl Mh) ((fun c4 l => decide (l ∈ idx c4)) c4) (opS c4) g nxt
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS ((friS bl sh idx 0) 0) ((friS bl sh idx 2) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) ((friS bl sh idx 8) 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => compTables m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableC m.heap N W)
      (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
    let tv := fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t
    let pb := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W),
      terminal pre β (segsAir roots) (segsPub roots))
    let ptm := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))
    let M := (allEntries (compTables m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm
      (progTableC m.heap N W) Wt (segsPub roots))).length
    let q0 := cGroups tbM tbC tpP tpS ((friS bl sh idx 0) 0) ((friS bl sh idx 2) 0) ((friS bl sh idx 4) 0) ((friS bl sh idx 6) 0) ((friS bl sh idx 8) 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
    let sm := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ * KQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let smR := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo (NSl ^ L * KA ^ nQ) (fun σ1 => sumTo (NS2 * NS3) (fun σ => sumTo NR (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1 := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1 (main1 x.2.2.2 x.2.2.1) x.1
    let m2 := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * Com2 (main2 c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2)
    let m3 := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1 x + KQ * comPair NS2 n2 Com2 Com3 (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1 c4 (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1 c4 (main1 x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2 c4) (ov3 c4) (rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2 (Pf2 c4) (Pf3 c4) (main2 c1 x.2.2.2 x.2.2.1, main3 c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Cmi (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * Com2 (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2)
    let s3 := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1 c4 c1 c2 c3 x + KQ * comPair NS2 n2 Com2 Com3
        (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svo := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pfi c4 (sdF (Ss c4) mk1 (sop1 c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2 (Pf2 c4) (Pf3 c4) (sdF (Ss c4) mk2 (sop2 c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3 c4 (sop3 c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4 := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => sm (fun x => g (H1, H2, H3, x)))))
    let sm4R := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 =>
        sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 => smR (fun x => g (H1, H2, H3, x)))))
    let r1 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1 y.2.2.2) y.1
    let r2 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2 (r1 y) y.2.2.2) y.2.1
    let r3 := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3 (r1 y) (r2 y) y.2.2.2) y.2.2.1
    let Mq := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φ (m3 (r1 y) (r2 y) y.2.2.2)
      (ozF (rvF 0 (r2 y) (r3 y) (efOf (r1 y / Q4)) (efOf (r1 y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    KQ * (K4 * (Q4 * Q4 * (K2 * Q4) * sumTo (K4 ^ N4) (fun H4 => sm4R (fun y =>
        indB (E y.1 y.2.1 y.2.2.1 H4 (m1 y.2.2.2) (m2 (r1 y) y.2.2.2) (m3 (r1 y) (r2 y) y.2.2.2)
          (rvo (rget K4 (Mq y) H4) (r1 y) (r2 y) (r3 y) y.2.2.2)))))) ≤
      sumTo (K4 ^ N4) (fun H4 => sumTo K4 (fun c4 =>
        sumTo ((Q4 * Q4) ^ KQ) (fun H1 => sumTo (K2 ^ (KQ * n2)) (fun H2 => sumTo (Q4 ^ (KQ * (n2 * n3))) (fun H3 =>
        sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => sm (fun x =>
          indB (E (rset (Q4 * Q4) (s1 c4 c1 c2 c3 x) H1 c1) (rset K2 (s2 c4 c1 c2 c3 x) H2 c2)
            (rset Q4 (s3 c4 c1 c2 c3 x) H3 c3) (rset K4 (φ (s3 c4 c1 c2 c3 x) (ozF (svF c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2))) H4 c4)
            (s1 c4 c1 c2 c3 x) (s2 c4 c1 c2 c3 x) (s3 c4 c1 c2 c3 x) (svo c4 c1 c2 c3 x))))))))))) +
        K4 ^ N4 * (K4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
          (K2 * (Q4 * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
            (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * ((NSl ^ L * KA ^ nQ * KQ) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1)))))))) +
            B4 * (Q4 * Q4 * (K2 * Q4) * sm4 (fun _ => 1))) +
      K4 * (Q4 * Q4 * (K2 * Q4) * (K4 ^ N4 * ((Q4 * Q4) ^ KQ * (K2 ^ (KQ * n2) * (Q4 ^ (KQ * (n2 * n3)) *
        (KQ * (L * (KA ^ nQ * (NSl ^ (L - 1) * (sQ * kQ)))) * (NS2 * NS3 * (NR * (Q4 ^ 2 * 1))))))))) := by
  have hM26 : tbM ≤ 26 := by omega
  have hC26 : tbC ≤ 26 := by omega
  have hph := comp_pub_heights hR hrl hA hlen hLm hK
  have hP26 : tpP ≤ 26 := by rw [htP]; exact Nat.le_trans hph.1 (by decide)
  have hS26 : tpS ≤ 26 := by rw [htS]; exact Nat.le_trans hph.2.2.1 (by decide)
  subst hL
  exact comp_fs_open4ROMM off hR hrl hr hA hlen hLm hK hNW htM
    htC htP htS (friS bl sh idx 0) (friS bl sh idx 2) (friS bl sh idx 4) (friS bl sh idx 6) (friS bl sh idx 8) qv wm
    wc ww wp wsg hlwm hlwc hlww hlwp hlwsg hK2
    hK4 φ hφ (comp_fri_leaves (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl hk0 hs0 hM26 hC26 hP26 hS26 hidx).1 (comp_fri_leaves (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl hk0 hs0 hM26 hC26 hP26 hS26 hidx).2.1 (comp_fri_leaves (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl hk0 hs0 hM26 hC26 hP26 hS26 hidx).2.2.1 (comp_fri_leaves (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl hk0 hs0 hM26 hC26 hP26 hS26 hidx).2.2.2.1 (comp_fri_leaves (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl hk0 hs0 hM26 hC26 hP26 hS26 hidx).2.2.2.2.1 hszM hszC
    hsz9 hszP hszS αd hB4 fri hncw NR2 Rb Ro
    hKA hN hKL (posRows (xsL bl sh) [0, 2, 4, 6, 8] h _ NSl Mh) (fun d l l' a b hl hl' hne => posRows_dist d l l' a b hl hl' hne) (fun d l a hl => Nat.lt_of_lt_of_le (posRows_lt hN hMh d l a hl) hnQ) g (fun d l v => Nat.le_trans (posRows_spread (Nat.two_pow_pos _) d l v) hsQ) nxt (fun c4 l => decide (l ∈ idx c4))
    (comp_fri_leaves (qv := qv) (h := h) (NSl := NSl) (Mh := Mh) hbl hk0 hs0 hM26 hC26 hP26 hS26 hidx).2.2.2.2.2.1 d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3
    hc3 hp3 hr3 d3 E

end

end Circuit
