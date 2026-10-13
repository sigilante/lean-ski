import Ski.ZK.HideWire

/-!
# A BabyBear trace group

The committed group of a table of `2^(tb+1)` rows: its trace points
`⟨bbGen (tb+1)⟩`, its masks on the interleaved coset (`HidingFriPcs`), its
next row `bbGen (tb+1) ·`, its query points `S` and out-of-domain points
`ζ, g ζ` (`bbGroup`).  It meets `QGroup.OK` when the query points lie off
the trace, `ζ` lies off `F` and `2 |S| + 8 ≤ 2^(tb+1)` (`bbGroup_OK`);
Plonky3's `HidingFriPcs` budget, `N ≥ 2 (q + 8)` at two opening points,
implies the last.  It has the shape `tabsHonest_corpus_ite`'s `hgrp`
asks (`bbGroup_hgrp`).  Plonky3's query points lie on the LDE coset
`31 · ⟨ω⟩`, and since 31 generates `F*` (`31^(2^27) ≠ 1`, checked by the
kernel) that coset misses every trace domain (`lde_off_trace`).
-/

namespace Circuit

open ZKF

/-- **The trace group of a table of `2^(tb+1)` rows.** -/
def bbGroup (tb : Nat) (S : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF) : QGroup :=
  ⟨⟨cosetL 1 (bbGen (tb + 1)) (2 ^ (tb + 1)), cosetL (bbGen (tb + 2)) (bbGen (tb + 1)) (2 ^ (tb + 1)), S,
    [ζ, (EF.ofF (bbGen (tb + 1))).mul ζ], 2 ^ (tb + 1)⟩, (bbGen (tb + 1) * ·), qv⟩

theorem bbGen_ne {b : Nat} (hb : b ≤ 26) : bbGen (b + 1) ≠ 0 := fun e => by
  have := bbGen_half b hb
  rw [e, show 2 ^ b = (2 ^ b - 1) + 1 by have := Nat.one_le_two_pow (n := b); omega] at this
  exact absurd (by rw [← this]; show (0 : F) = fpow 0 (2 ^ b - 1) * 0; rw [mul_zero']) (by decide : (0 : F) ≠ -1)

/-- `g ζ` lies off `F` when `ζ` does and `g ≠ 0`. -/
theorem mul_off_F {g : F} (hg : g ≠ 0) {ζ : EF} (hζ : ∀ x : F, EF.ofF x ≠ ζ) : ∀ x : F, EF.ofF x ≠ (EF.ofF g).mul ζ :=
  fun x e => hζ (finv g * x) (by
    rw [← EF.ofF_mul, e, ← EF.mul_assoc, EF.ofF_mul, finv_mul hg]
    exact EF.one_mul ζ)

/-- A point is on the trace after one step only if it was before. -/
theorem prev_on_trace {g : F} {n : Nat} (hn : 0 < n) (hg : fpow g n = 1) (hgz : g ≠ 0) {s : F}
    (h : g * s ∈ cosetL 1 g n) : s ∈ cosetL 1 g n := by
  obtain ⟨r, hr, e⟩ := mem_coset h
  rw [one_mul'] at e
  -- `s = g^(r-1)`, or `g^(n-1)` when `r = 0`
  refine mem_coset_iff.2 ⟨(r + n - 1) % n, Nat.mod_lt _ hn, ?_⟩
  rw [one_mul', ← fpow_mod hg]
  have hcancel : g * s = g * fpow g (r + n - 1) := by
    rw [e, fpow_succ', show r + n - 1 + 1 = r + n by omega, fpow_add', hg, mul_one']
  have := congrArg (finv g * ·) hcancel
  rwa [← mul_assoc', ← mul_assoc', finv_mul hgz, one_mul', one_mul'] at this

/-- **The trace group meets `QGroup.OK`.** -/
theorem bbGroup_OK {tb : Nat} (ht : tb ≤ 25) {S : List F} {ζ : EF} {qv : EF → EF → List EF → F → List F → List F → List EF}
    (hS : ∀ x ∈ S, x ∉ cosetL 1 (bbGen (tb + 1)) (2 ^ (tb + 1))) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hsz : 2 * S.length + 8 ≤ 2 ^ (tb + 1)) : (bbGroup tb S ζ qv).OK := by
  obtain ⟨hg, _⟩ := bb_trace tb (by omega)
  have hgz := bbGen_ne (b := tb) (by omega)
  have hn : 0 < 2 ^ (tb + 1) := Nat.two_pow_pos _
  refine ⟨cosetL_length _ _ _, cosetL_length _ _ _, bb_masks tb ht, fun x hx => ⟨fun hxS => hS x hxS hx, ?_⟩,
    fun z hz => ?_, ?_⟩
  · intro hxS
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hxS
    exact hS s hs (prev_on_trace hn hg hgz hx)
  · rcases List.mem_cons.1 hz with rfl | hz
    · exact hζ
    · rcases List.mem_singleton.1 hz with rfl
      exact mul_off_F hgz hζ
  · show 2 * S.length + 4 * 2 ≤ 2 ^ (tb + 1); omega

/-- **The trace group's shape**, as `tabsHonest_corpus_ite`'s `hgrp` asks. -/
theorem bbGroup_hgrp {tb : Nat} (ht : tb ≤ 25) (S : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) :
    (bbGroup tb S ζ qv).base.T = cosetL 1 (bbGen (tb + 1)) (2 ^ (tb + 1)) ∧ (bbGroup tb S ζ qv).base.S = S ∧
    (bbGroup tb S ζ qv).base.Z = [ζ, (EF.ofF (bbGen (tb + 1))).mul ζ] ∧
    (bbGroup tb S ζ qv).nxt = (bbGen (tb + 1) * ·) ∧
    (cosetL 1 (bbGen (tb + 1)) (2 ^ (tb + 1)) ++ (bbGroup tb S ζ qv).base.R).Nodup ∧
    (bbGroup tb S ζ qv).base.R.length ≤ 2 ^ (tb + 1) :=
  ⟨rfl, rfl, rfl, rfl, bb_masks tb ht, by show (cosetL _ _ _).length ≤ _; rw [cosetL_length]; exact Nat.le_refl _⟩

-- ---------------------------------------------------------------------------
-- Plonky3's chunks on BabyBear, every chunk hypothesis at once
-- ---------------------------------------------------------------------------

/-- **Plonky3's chunks of a table of `2^(tb+1)` rows**, `2^(lq+1)` of them
    on the quotient domain `31 · ⟨bbGen (tb+lq+2)⟩`: every chunk
    hypothesis of `tabsHonest_corpus_ite`. -/
theorem bb_chunks {tb lq : Nat} (hk : tb + lq + 1 ≤ 26) :
    let ω := bbGen (tb + lq + 2)
    let l := 2 ^ (lq + 1) - 1
    let n := 2 ^ (tb + 1)
    (31 : F) ≠ 0 ∧ fpow ω (2 ^ (tb + lq + 1)) = -1 ∧
    ((p3cs 31 ω l n).length + 1) * n = 2 ^ (tb + lq + 1 + 1) ∧
    (p3cs 31 ω l n).map (·.H) ++ [p3dom 31 ω l n l] = splitD 31 ω ((p3cs 31 ω l n).length + 1) n ∧
    (p3cs 31 ω l n).length + 1 = 2 ^ (lq + 1) ∧
    (∀ ch ∈ p3cs 31 ω l n, ch.c ≠ 0) ∧ p3c 31 ω n l ≠ 0 ∧ p3κ 31 ω l n ≠ 0 ∧
    (∀ (qs : List (List F)) (ql : List F), qs.length = (p3cs 31 ω l n).length →
      ∀ j (hj : j < (allL (p3cs 31 ω l n) (p3dom 31 ω l n l) (p3c 31 ω n l) qs ql).length) s',
      ((allL (p3cs 31 ω l n) (p3dom 31 ω l n l) (p3c 31 ω n l) qs ql)[j]'hj).1 =
        cosetL s' (fpow ω ((p3cs 31 ω l n).length + 1)) n →
      ((allL (p3cs 31 ω l n) (p3dom 31 ω l n l) (p3c 31 ω n l) qs ql)[j]'hj).2.2.1 =
        finv (opv s' (allL (p3cs 31 ω l n) (p3dom 31 ω l n l) (p3c 31 ω n l) qs ql) j) * finv (p3κ 31 ω l n)) ∧
    (∀ ch ∈ p3cs 31 ω l n, ch.m ≠ 0) ∧
    (∀ ch ∈ p3cs 31 ω l n, ch.H.Nodup) ∧ (p3dom 31 ω l n l).Nodup := by
  intro ω l n
  have h31 : (31 : F) ≠ 0 := by decide
  have hhalf := bbGen_half (tb + lq + 1) hk
  have hl : l + 1 = 2 ^ (lq + 1) := by have := Nat.one_le_two_pow (n := lq + 1); omega
  have hN : (l + 1) * n = 2 ^ (tb + lq + 1 + 1) := by
    rw [hl, ← Nat.pow_add]; congr 1; omega
  obtain ⟨hdom, hc, hcl, hκ, hw, hm0⟩ := p3_static h31 hhalf hN (Nat.two_pow_pos _)
  have hcs : (p3cs 31 ω l n).length = l := by unfold p3cs; rw [List.length_map, List.length_range]
  have hNodup : ∀ H ∈ splitD 31 ω (l + 1) n, H.Nodup := fun H hH => split_member_nodup h31 hhalf hN hH
  have hdom' : (p3cs 31 ω l n).map (·.H) ++ [p3dom 31 ω l n l] = splitD 31 ω (l + 1) n := by
    rw [hdom, hcs]
  exact ⟨h31, hhalf, by rw [hcs]; exact hN, hdom, by rw [hcs]; exact hl, hc, hcl, hκ, hw, hm0,
    fun ch hch => hNodup _ (by rw [← hdom']; exact List.mem_append_left _ (List.mem_map_of_mem hch)),
    hNodup _ (by rw [← hdom']; exact List.mem_append_right _ List.mem_cons_self)⟩

/-- **The table's sets meet `CSet.OK`** from its parts. -/
theorem airQTabG_ok {AF : EF → EF → List EF → AirD} {g : F} {m : Nat} {preP : Nat → List F} {gis : List Nat}
    {κ : F} {cs : List Chunk} {Hl : List F} {cl : F} {S : List F} {ζ : EF} {ws : List (EF → EF → List F)}
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hdet : (mz ζ).det ≠ 0) (hS4 : S.length + 4 ≤ m + 1)
    (hcm : ∀ ch ∈ cs, ch.c ≠ 0 ∧ ch.m ≠ 0) (hcl : cl ≠ 0) :
    ∀ c ∈ (airQTabG AF g m preP gis κ cs Hl cl S ζ ws).sets, c.OK := fun c hc => by
  unfold QTab.sets airQTabG at hc
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hc
  exact ⟨hζ, hdet, hS4, hcm, hcl⟩

/-- Plonky3's chunks of a table of `m + 1` rows, `2^(lq+1)` of them. -/
def bbCs (tb lq m : Nat) : List Chunk := p3cs 31 (bbGen (tb + lq + 2)) (2 ^ (lq + 1) - 1) (m + 1)
def bbHl (tb lq m : Nat) : List F := p3dom 31 (bbGen (tb + lq + 2)) (2 ^ (lq + 1) - 1) (m + 1) (2 ^ (lq + 1) - 1)
def bbCl (tb lq m : Nat) : F := p3c 31 (bbGen (tb + lq + 2)) (m + 1) (2 ^ (lq + 1) - 1)
def bbκ (tb lq m : Nat) : F := p3κ 31 (bbGen (tb + lq + 2)) (2 ^ (lq + 1) - 1) (m + 1)

/-- **One private table over BabyBear, honest at every challenge**:
    `tabsHonest_corpus_ite` with the trace groups `bbGroup`, Plonky3's
    chunks and the preprocessed columns interpolated, every domain and
    chunk fact and the groups' shape discharged.  Left: the AIR's check
    (`AirP3`); the run's tables, columns and terminal (`hb`); one fixed
    preprocessed table `P0` every `tab t` shares (`hpre0`); the groups
    list with `bbGroup` at `gm` and `gp` (`hqm`, `hqp`, `hcl'`); the
    transcript's tables (`hmem`); the height `m + 1 = 2^(tb+1)` with
    `1 ≤ lq` and `tb + lq + 1 ≤ 26`; and the query and out-of-domain
    points (`hSoff`, which `lde_off_trace` gives for Plonky3's queries,
    `|S| + 4 ≤ m + 1`, `ζ ∉ F`, `(mz ζ).det ≠ 0`). -/
theorem tabsHonest_bb (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    {A : AirD} (hP : AirP3 A = true) {tb lq m gm gp : Nat} {tm : EF → EF → List EF → EF} (ht : tb ≤ 25) (hlq : 1 ≤ lq)
    (hk : tb + lq + 1 ≤ 26) (hm : m + 1 = 2 ^ (tb + 1))
    {S : List F} {ζ : EF} {ws : List (EF → EF → List F)} {qs : List QGroup}
    {cols : (Nat → Tup) → EF → EF → List (List (List F))} {qv1 qv2 : EF → EF → List EF → F → List F → List F → List EF}
    (hqm : ∃ h : gm < qs.length, qs[gm]'h = bbGroup tb S ζ qv1)
    (hqp : ∃ h : gp < qs.length, qs[gp]'h = bbGroup tb S ζ qv2)
    (tab : (Nat → Tup) → Table) (P0 : Table) (hpre0 : ∀ t, (tab t).pre = P0.pre)
    (tabs : (Nat → Tup) → List (AirD × Table)) (hmem : ∀ t, (A, tab t) ∈ tabs t)
    (hcl' : ∀ t α β, ∀ j ∈ [gm, gp], j < (cols t α β).length)
    (hb : ∀ t α β, Sat A (tab t) ∧ (tab t).h = m + 1 ∧
      (cols t α β).getD gm [] = mainCols (tab t) A.width ∧
      (cols t α β).getD gp [] = permCols (tab t) (busAlphas (prefixOf α (off β)) A) β (corpusLs A) ∧
      tm α β (tv (prefixOf α (off β)) β t) = terminal (prefixOf α (off β)) β A (tab t))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hdet : (mz ζ).det ≠ 0)
    (hSoff : ∀ x ∈ S, x ∉ cosetL 1 (bbGen (tb + 1)) (m + 1)) (hS4 : S.length + 4 ≤ m + 1) :
    ∀ t α β ms, TabsHonest
      (fun c => c.JS α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      [airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β v) A.width
        (corpusLs A)) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) [gm, gp] (bbκ tb lq m) (bbCs tb lq m)
        (bbHl tb lq m) (bbCl tb lq m) S ζ ws]
      [if Aborts (prefixOf α (off β)) β (tabs t) = false then
          airData (withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β (tv (prefixOf α (off β)) β t))
            A.width (corpusLs A)) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) (bbCs tb lq m) (bbHl tb lq m)
            ws α β (catAt (mpolysMulti (qs.map QGroup.ext) (cols t α β) ms) [gm, gp])
          else canonData (airQTabG (fun α β v => withLup A (busAlphas (prefixOf α (off β)) A) β (tm α β v)
            A.width (corpusLs A)) (bbGen (tb + 1)) m (preInterp P0 (bbGen (tb + 1)) m) [gm, gp] (bbκ tb lq m)
            (bbCs tb lq m) (bbHl tb lq m) (bbCl tb lq m) S ζ ws).sets α β (tv (prefixOf α (off β)) β t)
            (openMulti (qs.map QGroup.ext) (cols t α β) ms)] := by
  obtain ⟨hg, hinj⟩ := bb_trace tb (by omega)
  rw [← hm] at hg hinj
  have hch := bb_chunks (tb := tb) (lq := lq) hk
  simp only [← hm] at hch
  obtain ⟨hshift, hhalf, hN, hdom, hL, hc, hcl, hκ, hw, hm0, hHn, hHln⟩ := hch
  have hpre := fun i => preInterp_spec P0 (g := bbGen (tb + 1)) (m := m) hinj i
  have hpos : 2 ≤ 2 ^ (tb + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (tb + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hbig : 2 ^ (tb + 1) ≤ 2 ^ 26 := Nat.pow_le_pow_right (by decide) (by omega)
  refine tabsHonest_corpus_ite off tv hP (tm := tm) (lq := lq) tab tabs hmem (fun j hj => ?_) hcl'
    (fun t α β => ?_) hg hinj (fun i => by have := (hpre i).1; omega) hζ
    (fun x hx => fvan_ne x _ (hSoff x hx)) hc hcl hκ hshift hhalf hN hdom hL
    (Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hlq)) (by omega)
    (by show 2 * (2 * (m + 1) - 1) + 1 + 1 ≤ 2013265921; omega) hw
    (airQTabG_ok hζ hdet hS4 (fun ch hch => ⟨hc ch hch, hm0 ch hch⟩) hcl) hHn hHln
  · rcases List.mem_cons.1 hj with rfl | hj
    · obtain ⟨h, e⟩ := hqm
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := bbGroup_hgrp ht S ζ qv1
      rw [← hm] at e1 e5 e6
      exact ⟨h, by rw [e]; exact e1, by rw [e]; exact e2, by rw [e]; exact e3, by rw [e]; exact e4,
        by rw [e]; exact e5, by rw [e]; exact e6⟩
    · rcases List.mem_singleton.1 hj with rfl
      obtain ⟨h, e⟩ := hqp
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := bbGroup_hgrp ht S ζ qv2
      rw [← hm] at e1 e5 e6
      exact ⟨h, by rw [e]; exact e1, by rw [e]; exact e2, by rw [e]; exact e3, by rw [e]; exact e4,
        by rw [e]; exact e5, by rw [e]; exact e6⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hb t α β
    exact ⟨h1, h2, h3, h4, h5, fun r i hr => by rw [hpre0]; exact (hpre i).2 r hr⟩

-- ---------------------------------------------------------------------------
-- The query points lie off the trace
-- ---------------------------------------------------------------------------

theorem fpow_one_pow (x : F) (a b : Nat) (h : fpow x a = 1) : fpow x (a * b) = 1 := by
  rw [fpow_mul', h, fpow_one']

/-- Every BabyBear two-adic generator's `2^27`-th power is one. -/
theorem bbGen_pow27 {b : Nat} (hb : b ≤ 26) : fpow (bbGen (b + 1)) (2 ^ 27) = 1 := by
  rw [show 2 ^ 27 = 2 ^ (b + 1) * 2 ^ (26 - b) by rw [← Nat.pow_add]; congr 1; omega]
  exact fpow_one_pow _ _ _ (bb_trace b hb).1

/-- 31 generates `F*`, so its `2^27`-th power is not one (the kernel computes it). -/
theorem gen31_pow27 : fpow (31 : F) (2 ^ 27) ≠ 1 := by
  rw [← fpowFast_eq 28 _ _ (by decide)]; decide

/-- **The LDE coset `31 · ⟨ω⟩` lies off every trace domain**: Plonky3's
    query points `31 · ωᵉ`, `ω` a two-adic generator, are not in
    `⟨bbGen (tb+1)⟩`. -/
theorem lde_off_trace {tb b : Nat} (htb : tb ≤ 26) (hb : b ≤ 26) (e : Nat) :
    (31 : F) * fpow (bbGen (b + 1)) e ∉ cosetL 1 (bbGen (tb + 1)) (2 ^ (tb + 1)) := fun hx => by
  obtain ⟨r, _, hr⟩ := mem_coset hx
  rw [one_mul'] at hr
  have h1 : fpow ((31 : F) * fpow (bbGen (b + 1)) e) (2 ^ 27) = fpow (fpow (bbGen (tb + 1)) r) (2 ^ 27) := by rw [hr]
  rw [fpow_mul_distrib, ← fpow_mul', Nat.mul_comm, fpow_mul', bbGen_pow27 hb, fpow_one', mul_one',
    ← fpow_mul', Nat.mul_comm, fpow_mul', bbGen_pow27 htb, fpow_one'] at h1
  exact gen31_pow27 h1

end Circuit
