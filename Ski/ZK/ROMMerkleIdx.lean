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
lie off the trace domain (`hS16` …), which LDE coset points
`shift · ω ^ l` would meet.

Mixed heights fit the converse.  In Plonky3 a shorter matrix's row serves
a block of leaves: leaf `l` reads row `l / 2 ^ sh k` of group `k`, where
`sh k` is the group's height deficit (`xsSh`).  The shorter groups' points
repeat, but the tallest group (`sh k0 = 0`) separates the leaves when its
`L` rows' points are distinct (`xsSh_inj`), so the tallest matrix's index
decides the opened leaf (`isOfRows_xsSh_iff`, for sets built by `qSets`;
the per-circuit theorems take any `xs`).

Not shown: that the circuits' query sets (`S16`, `S10`, `SP` and the
others) are the points of indices FRI draws from the fourth challenge (the
per-circuit theorems take it as hypotheses `h0` … on each set); that the
tallest group's points are distinct (a hypothesis, `hinj`); FRI's own
layer commitments and their openings (`friX` takes FRI as a function);
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

end

end Circuit
