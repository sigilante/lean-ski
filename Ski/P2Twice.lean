import Ski.P2Chain
import Ski.P2Once
import Ski.ZK.CompPHonest
import Ski.Circuit.CompPCompleteFinal

/-!
# The chain's verifier calls the Poseidon2 jet exactly twice

`p2chain h`'s verifier is `S (K K) (J ⬝ (J₂ ⬝ CHECK_h))`, `J₂ = J + 1`
(`verifierChainO_eq`).  Its run passes through three phases, each a
property of the term the rows read back as:

- **the frame** (`P2Once.Outer` with the part `GQ`, `UQ`): `S (K K) g b w`,
  `K K b u w`, `K u w`, `u`, with `g = J ⬝ (J₂ ⬝ d)` and `u = g ⬝ b`, `d` free
  of both atoms.  Its head is never `J₂`, so no stack row fires there; the
  comb row fires at `u = J ⬝ (J₂ ⬝ d) ⬝ b`, its continuation `J₂ ⬝ d` and
  nothing after the comb;
- **the stack** (`Sp`): `J₂ ⬝ d ⬝ bits …`, every argument free of `J` and
  `J₂`.  It holds no `J`, so no comb row fires; the stack row fires at its
  head;
- **the rest**: free of both atoms, so no jet row fires, until `K`.

So a run calls the jet exactly twice, first on the comb and then on the
stack (`twice_of`): an honest run's `calls` is `2` (`P2Run.calls_two`,
`runP_calls_two`), and every accepted proof of `p2chain h` has exactly two
jet rows (`Circuit.p2chain_twice`), the analog of `p2pre_once`.

Its verifier accepts honest bits (`P2Chain.p2chain_complete`): the converse
of `p2chain_meaning`, as `P2Complete.p2pre_complete` is of `p2pre_meaning`.
-/

open Term Compose CompM ComposedPText Poseidon2SKI

namespace P2Once

open Mach Stmt Wit

theorem free_var_ne {J x : Nat} (hx : x ≠ J) : Free J (.var x) := fun h => by
  generalize e : OTerm.var x = t at h
  cases h with
  | var => injection e with e; exact hx e
  | left => cases e
  | right => cases e

-- ---------------------------------------------------------------------------
-- The chain's jet part
-- ---------------------------------------------------------------------------

/-- The chain's part: `g = J ⬝ (J₂ ⬝ d)`, applied `J ⬝ (J₂ ⬝ d) ⬝ b`, `d` free of
    both atoms. -/
def GQ (J : Nat) (g : OTerm) : Prop := ∃ d, Free J d ∧ Free (J + 1) d ∧ g = .var J ⬝ₒ (.var (J + 1) ⬝ₒ d)
def UQ (J : Nat) (u : OTerm) : Prop :=
  ∃ d b, Free J d ∧ Free (J + 1) d ∧ Free J b ∧ u = .var J ⬝ₒ (.var (J + 1) ⬝ₒ d) ⬝ₒ b

/-- **The comb row in the chain's part**: no arguments after the comb, the
    continuation `J₂ ⬝ d`. -/
theorem uq_jet {J : Nat} {k β : OTerm} {R : List OTerm} (h : UQ J (appL (.var J) (k :: β :: R))) :
    R = [] ∧ ∃ d, Free J d ∧ Free (J + 1) d ∧ k = .var (J + 1) ⬝ₒ d := by
  obtain ⟨d, b, h1, h2, _, e⟩ := h
  have hn := congrArg nargs e
  rw [nargs_appL] at hn
  match R, hn with
  | [], _ =>
    have e' : OTerm.var J ⬝ₒ k ⬝ₒ β = .var J ⬝ₒ (.var (J + 1) ⬝ₒ d) ⬝ₒ b := e
    injection e' with e1 _
    injection e1 with _ e2
    exact ⟨rfl, d, h1, h2, e2⟩
  | _ :: R, hn =>
    have : nargs (OTerm.var J) + (R.length + 3) = 2 := hn
    exact absurd this (by omega)

theorem partQ (J : Nat) : Part J (GQ J) (UQ J) where
  gstep := by
    rintro _ _ ⟨d, h1, h2, rfl⟩ hs
    cases hs with
    | left _ hs => nomatch hs
    | right _ hs =>
      cases hs with
      | left _ hs => nomatch hs
      | right _ hs => exact ⟨_, free_step h1 hs, free_step h2 hs, rfl⟩
  gapp := by
    rintro _ b ⟨d, h1, h2, rfl⟩ hb
    exact ⟨d, b, h1, h2, hb, rfl⟩
  ustep := by
    rintro _ _ ⟨d, b, h1, h2, hb, rfl⟩ hs
    cases hs with
    | left _ hs =>
      cases hs with
      | left _ hs => nomatch hs
      | right _ hs =>
        cases hs with
        | left _ hs => nomatch hs
        | right _ hs => exact ⟨_, b, free_step h1 hs, free_step h2 hs, hb, rfl⟩
    | right _ hs => exact ⟨d, _, h1, h2, free_step hb hs, rfl⟩
  gocc := by
    rintro _ ⟨d, _, _, rfl⟩
    exact .left _ (.var _)
  uocc := by
    rintro _ ⟨d, b, _, _, _, rfl⟩
    exact .left _ (.left _ (.var _))
  ujet := by
    intro k β R h
    obtain ⟨hR, d, h1, _, hk⟩ := uq_jet h
    subst hR hk
    exact ⟨free_app (free_var_ne (by omega)) h1, fun _ hx => nomatch hx⟩

/-- **The frame's head is never `J₂`.** -/
theorem outerQ_head {J : Nat} {t : OTerm} (ht : Outer J (GQ J) (UQ J) t) : headO t ≠ .var (J + 1) := by
  cases ht with
  | o0 => exact fun e => nomatch e
  | o1 => exact fun e => nomatch e
  | o2 => exact fun e => nomatch e
  | o3 hu =>
    obtain ⟨d, b, _, _, _, rfl⟩ := hu
    intro e
    have : OTerm.var J = .var (J + 1) := e
    injection this with e'
    omega

/-- **A comb row in the frame** is at `u = J ⬝ (J₂ ⬝ d) ⬝ b`. -/
theorem outerQ_jet {J : Nat} {k β : OTerm} {R : List OTerm}
    (ht : Outer J (GQ J) (UQ J) (appL (.var J) (k :: β :: R))) :
    R = [] ∧ ∃ d, Free J d ∧ Free (J + 1) d ∧ k = .var (J + 1) ⬝ₒ d := by
  have hh := headO_appL (.var J) (k :: β :: R)
  generalize e : appL (.var J) (k :: β :: R) = t at ht hh
  cases ht with
  | o0 => nomatch hh
  | o1 => nomatch hh
  | o2 => nomatch hh
  | o3 hu => subst e; exact uq_jet hu

-- ---------------------------------------------------------------------------
-- The stack phase: a spine at `c`, every argument free of `y`
-- ---------------------------------------------------------------------------

/-- `c ⬝ a₁ ⬝ … ⬝ aₙ`, every `aᵢ` free of `y`. -/
inductive Sp (c y : Nat) : OTerm → Prop
  | var : Sp c y (.var c)
  | app {f a : OTerm} : Sp c y f → Free y a → Sp c y (f ⬝ₒ a)

theorem sp_head {c y : Nat} {t : OTerm} (h : Sp c y t) : headO t = .var c := by
  induction h with
  | var => rfl
  | app _ _ ih => exact ih

theorem not_sp_K {c y : Nat} : ¬ Sp c y .K := fun h => nomatch h

theorem sp_step {c y : Nat} {t u : OTerm} (ht : Sp c y t) (hs : OWStep t u) : Sp c y u := by
  induction ht generalizing u with
  | var => nomatch hs
  | app hf ha ih =>
    cases hs with
    | S f g x =>
      have := sp_head hf
      exact nomatch this
    | K x y =>
      have := sp_head hf
      exact nomatch this
    | I x => nomatch hf
    | left _ h => exact .app (ih h) ha
    | right _ h => exact .app hf (free_step ha h)

theorem sp_steps {c y : Nat} {t u : OTerm} (ht : Sp c y t) (hs : OWSteps t u) : Sp c y u := by
  induction hs with
  | refl _ => exact ht
  | step h _ ih => exact ih (sp_step ht h)

theorem sp_appL {c y : Nat} : ∀ {t : OTerm} {as : List OTerm}, Sp c y t → (∀ x ∈ as, Free y x) →
    Sp c y (appL t as)
  | _, [], h, _ => h
  | t, a :: as, h, ha => sp_appL (t := t ⬝ₒ a) (as := as) (.app h (ha a List.mem_cons_self))
      (fun x hx => ha x (List.mem_cons_of_mem a hx))

theorem sp_appL_inv {c y : Nat} : ∀ {t : OTerm} {as : List OTerm}, Sp c y (appL t as) →
    Sp c y t ∧ ∀ x ∈ as, Free y x
  | _, [], h => ⟨h, fun _ hx => nomatch hx⟩
  | _, a :: as, h => by
    obtain ⟨h1, h2⟩ := sp_appL_inv (as := as) h
    cases h1 with
    | app hf ha =>
      refine ⟨hf, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact h2 x hx

-- ---------------------------------------------------------------------------
-- The run
-- ---------------------------------------------------------------------------

/-- **A run of the chain's verifier calls the jet twice**: of the rows
    before its end, each a plain row (`sel` false) or a jet row (`sel`
    true), exactly two are jet rows. -/
theorem twice_of {ρ : Nat → Bool} {shp : BT} {region : List Cell} {V : OTerm} {J root : Nat}
    {g : OTerm} (hg : GQ J g) (hV : V = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ g)
    {bs₀ : List Bool} (hb0 : P2Jet.bitsAt (cMachineO ρ shp region [V]).heap P2Jet.slotAddrs = some bs₀)
    (ho0 : otermAt (cMachineO ρ shp region [V]).heap ((cMachineO ρ shp region [V]).heap.length + 1) root =
      some (combT bs₀).toO)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {M : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (h : AcceptsCP M (cMachineO ρ shp region [V]) [] [] J root (cHeapO ρ shp region [V]).2
      (cHeapO ρ shp region [V]).1.length 1 e row)
    (sel : Nat → Bool)
    (hsel : ∀ i, i < e 0 → (sel i = false ∧ Air.NormRow M [] [] (row i) (row (i + 1))) ∨
      (sel i = true ∧ (P2Jet.p2Row M J root (row i) = some (row (i + 1)) ∨
        P2Jet.p2RowS M (J + 1) (row i) = some (row (i + 1))))) :
    ∃ r0 r1, r0 < r1 ∧ r1 < e 0 ∧ sel r0 = true ∧ sel r1 = true ∧
      ∀ r, r < e 0 → sel r = true → r = r0 ∨ r = r1 := by
  have hp := partQ J
  let N := BT.nleaves shp
  let m0 := cMachineO ρ shp region [V]
  obtain ⟨w, hw⟩ := witnessOf_some (slots_wf ρ N hr) (by simp [slotHeap_length]; omega)
  obtain ⟨_, hdecV⟩ := cMachineO_decode (Vs := [V]) hw
  have hroot := hdecV 0 V rfl
  have hroots : Air.RootsOK m0.heap [] [] := fun _ _ h' => absurd h' List.not_mem_nil
  obtain ⟨hc, hm, _, _⟩ := h.runs hroots 0 Nat.zero_lt_one
  replace hc : (row 0).ctr ≤ M.length := hc
  have hm0 : m0.heap = M.take (row 0).ctr := h.heap0.symm
  have hc0 : (row 0).ctr = m0.heap.length := h.ctr0
  have hr0 : Air.RootsOK (M.take (row 0).ctr) [] [] := fun _ _ h' => absurd h' List.not_mem_nil
  have hlen : (Air.st M (row 0)).heap.length = (row 0).ctr := by
    simp [Air.st, Air.take_length hc]
  have hstart : odecode (Air.st M (row 0)) = some (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) := by
    have e1 : V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO = appL (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) [] := rfl
    rw [e1]
    apply odecode_of
    · show otermAt (M.take (row 0).ctr) (_ + 1) (row 0).hd = _
      rw [h.hd0]
      rw [hm0] at hroot
      refine Air.otermAt_take (Nat.le_refl _) ?_ hroot
      rw [← hm0, hlen, hc0]
      exact Nat.le_refl _
    · show ostackAt (M.take (row 0).ctr) (_ + 1) (row 0).stk = _
      rw [h.stk0]
      have hn : (M.take (row 0).ctr)[(cHeapO ρ shp region [V]).1.length]? = some .nil := by
        rw [← hm0]; simp [m0, cMachineO]
      unfold ostackAt
      rw [hn]
  have hcombs : ∀ c, (row 0).ctr ≤ c → P2Jet.CombAt (M.take c) root := fun c hcc => by
    have hb' : P2Jet.bitsAt (M.take (row 0).ctr) P2Jet.slotAddrs = some bs₀ := by rw [← hm0]; exact hb0
    have ho' : otermAt (M.take (row 0).ctr) ((M.take (row 0).ctr).length + 1) root = some (combT bs₀).toO := by
      rw [← hm0]; exact ho0
    exact combAt_take hb' ho' hcc
  -- the claim, row by row: the frame, the stack, or the rest
  have claim : ∀ b, b ≤ e 0 → ∃ t, odecode (Air.st M (row b)) = some t ∧
      (row 0).ctr ≤ (row b).ctr ∧ (row b).ctr ≤ M.length ∧
      ((Outer J (GQ J) (UQ J) t ∧ ∀ i, i < b → sel i = false) ∨
        (Free J t ∧ Sp (J + 1) (J + 1) t ∧
          ∃ r0, r0 < b ∧ sel r0 = true ∧ ∀ i, i < b → sel i = true → i = r0) ∨
        (Free J t ∧ Free (J + 1) t ∧ ∃ r0 r1, r0 < r1 ∧ r1 < b ∧ sel r0 = true ∧ sel r1 = true ∧
          ∀ i, i < b → sel i = true → i = r0 ∨ i = r1)) := by
    intro b
    induction b with
    | zero =>
      intro _
      refine ⟨_, hstart, Nat.le_refl _, hc, .inl ⟨?_, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩⟩
      rw [hV]
      exact .o0 hg (free_toO J _) (free_toO J _)
    | succ b ih =>
      intro hb
      obtain ⟨t, hdec, hcl, hcu, hph⟩ := ih (Nat.le_of_succ_le hb)
      rcases hsel b hb with ⟨hs, hn⟩ | ⟨hs, hj | hj⟩
      · -- a plain row keeps each phase
        obtain ⟨h1, h2, hJ, _⟩ := Air.normRow_spec hr0 hcl hcu hn
        obtain ⟨u, hu, hwu⟩ := ojsteps_owsteps hdec hJ
        refine ⟨u, hu, Nat.le_trans hcl h1, h2, ?_⟩
        rcases hph with ⟨ho, hall⟩ | ⟨hf, hsp, r0, hr0b, hsr, huniq⟩ |
            ⟨hf, hf1, r0, r1, h01, h1b, hs0, hs1, huniq⟩
        · refine .inl ⟨outer_steps hp ho hwu, fun i hi => ?_⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
          · exact hall i hi
          · exact hs
        · refine .inr (.inl ⟨free_steps hf hwu, sp_steps hsp hwu, r0, Nat.lt_succ_of_lt hr0b, hsr,
            fun i hi hsi => ?_⟩)
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
          · exact huniq i hi hsi
          · rw [hs] at hsi; cases hsi
        · refine .inr (.inr ⟨free_steps hf hwu, free_steps hf1 hwu, r0, r1, h01, Nat.lt_succ_of_lt h1b, hs0,
            hs1, fun i hi hsi => ?_⟩)
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
          · exact huniq i hi hsi
          · rw [hs] at hsi; cases hsi
      · -- the comb row: only in the frame, into the stack
        obtain ⟨a1, a2⟩ := P2Jet.p2Row_ctr_len hj hcu
        obtain ⟨_, Nk, bs, R, _, rfl, hd⟩ := P2Jet.p2Row_step hj hcu (hcombs _ hcl) hdec
        rcases hph with ⟨ho, hall⟩ | ⟨hf, _⟩ | ⟨hf, _⟩
        · obtain ⟨rfl, d, hd1, hd2, rfl⟩ := outerQ_jet ho
          rw [List.append_nil] at hd
          have hbits : ∀ x ∈ ((Poseidon2.permute (valsB bs)).flatMap (BitArith.bitsOf 31)).map
              (fun b => (boolT b).toO), ∀ y, Free y x := fun x hx y => by
            obtain ⟨z, _, rfl⟩ := List.mem_map.1 hx
            exact free_toO _ _
          refine ⟨_, hd, Nat.le_trans hcl a1, a2, .inr (.inl ⟨?_, ?_, b, Nat.lt_succ_self _, hs,
            fun i hi hsi => ?_⟩)⟩
          · exact free_appL (free_app (free_var_ne (by omega)) hd1) (fun x hx => hbits x hx J)
          · exact sp_appL (.app .var hd2) (fun x hx => hbits x hx (J + 1))
          · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
            · rw [hall i hi] at hsi; cases hsi
            · rfl
        · exact absurd (occ_head (headO_appL _ _)) hf
        · exact absurd (occ_head (headO_appL _ _)) hf
      · -- the stack row: only in the stack, into the rest
        obtain ⟨a1, a2⟩ := P2Jet.p2RowS_ctr_len hj hcu
        obtain ⟨_, Nk, bs, R, _, rfl, hd⟩ := P2Jet.p2RowS_step hj hcu hdec
        rcases hph with ⟨ho, _⟩ | ⟨hf, hsp, r0, hr0b, hsr, huniq⟩ | ⟨_, hf1, _⟩
        · exact absurd (headO_appL _ _) (outerQ_head ho)
        · have hargs := (sp_appL_inv hsp).2
          have hfr := (free_appL_inv hf).2
          have hfree : ∀ y, (∀ x ∈ Nk :: ((bs.map fun b => (boolT b).toO) ++ R), Free y x) →
              Free y (appL Nk (((Poseidon2.permute (valsB bs)).flatMap (BitArith.bitsOf 31)).map
                (fun b => (boolT b).toO) ++ R)) := fun y hy =>
            free_appL (hy Nk List.mem_cons_self) (fun x hx => by
              rcases List.mem_append.1 hx with hx | hx
              · obtain ⟨z, _, rfl⟩ := List.mem_map.1 hx
                exact free_toO _ _
              · exact hy x (List.mem_cons_of_mem _ (List.mem_append_right _ hx)))
          refine ⟨_, hd, Nat.le_trans hcl a1, a2, .inr (.inr ⟨hfree J hfr, hfree (J + 1) hargs, r0, b, hr0b,
            Nat.lt_succ_self _, hsr, hs, fun i hi hsi => ?_⟩)⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
          · exact .inl (huniq i hi hsi)
          · exact .inr rfl
        · exact absurd (occ_head (headO_appL _ _)) hf1
  obtain ⟨t, hdec, _, _, hph⟩ := claim (e 0) (Nat.le_refl _)
  have hK : t = .K := by
    refine odecode_K hdec ?_ ?_
    · rw [← (h.ends 0 Nat.zero_lt_one).1, Air.rd_eq]; rfl
    · rw [← (h.ends 0 Nat.zero_lt_one).2, Air.rd_eq]; rfl
  rcases hph with ⟨ho, _⟩ | ⟨_, hsp, _⟩ | ⟨_, _, r0, r1, h01, h1b, hs0, hs1, hu⟩
  · rw [hK] at ho; exact absurd ho (not_outer_K hp)
  · rw [hK] at hsp; exact absurd hsp not_sp_K
  · exact ⟨r0, r1, h01, h1b, hs0, hs1, hu⟩

theorem checkO_free' (h x : Nat) : Free x (checkO h) := checkO_free h x

/-- **The chain's verifier, abstracted**: `S (K K) (J ⬝ (J₂ ⬝ CHECK_h))`. -/
theorem verifierChainO_eq (h : Nat) :
    verifierChainO h = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h)) := by
  have hc : ∀ x, (checkO h).mem x = false := fun x => mem_false_of_free (checkO_free h x)
  show abs 0 (abs 1 (.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h) ⬝ₒ .var 0)) = _
  have m1 : (OTerm.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h) ⬝ₒ .var 0).mem 1 = false := by
    show ((JP2 == 1 || (JP2S == 1 || (checkO h).mem 1)) || (0 == 1)) = false
    rw [hc]; rfl
  rw [abs_of_not_mem m1, abs_app, if_neg (by
    show ¬ ((OTerm.K.mem 0 || ((JP2 == 0 || (JP2S == 0 || (checkO h).mem 0)) || (0 == 0))) = false)
    rw [hc]; decide), if_neg (fun e => nomatch e.1)]
  show OTerm.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ abs 0 (.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h) ⬝ₒ .var 0) = _
  rw [abs_app, if_neg (by
    show ¬ (((JP2 == 0 || (JP2S == 0 || (checkO h).mem 0)) || (0 == 0)) = false)
    rw [hc]; decide), if_pos ⟨rfl, by show (JP2 == 0 || (JP2S == 0 || (checkO h).mem 0)) = false; rw [hc]; rfl⟩]

/-- The chain's verifier's part. -/
theorem chain_GQ (h : Nat) : GQ JP2 (.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h)) :=
  ⟨checkO h, checkO_free h JP2, checkO_free h (JP2 + 1), rfl⟩

end P2Once

-- ---------------------------------------------------------------------------
-- The honest run: `calls = 2`
-- ---------------------------------------------------------------------------

namespace Circuit

open B Air Compose CompM Mach

namespace P2Run

variable {R : P2Run}

/-- Exactly two indices `r0 ≠ r1` satisfy `p`: below `K`, as many as lie
    below `K`. -/
theorem filter_two (p : Nat → Bool) {r0 r1 : Nat} (h01 : r0 < r1) (hp : ∀ i, p i = true ↔ i = r0 ∨ i = r1) :
    ∀ n, ((List.range n).filter p).length = min n (r0 + 1) - min n r0 + (min n (r1 + 1) - min n r1)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, filter_two p h01 hp n, List.filter_cons,
      List.filter_nil]
    cases hk : p n with
    | false =>
      have h0 : n ≠ r0 := fun e => by have := (hp n).2 (.inl e); rw [hk] at this; cases this
      have h1 : n ≠ r1 := fun e => by have := (hp n).2 (.inr e); rw [hk] at this; cases this
      rw [if_neg Bool.false_ne_true, List.length_nil]
      omega
    | true =>
      have := (hp n).1 hk
      rw [if_pos rfl, List.length_cons, List.length_nil]
      omega

/-- **An honest run of the chain's verifier calls the jet twice**: its
    `calls` is `2`, so the public level table is `idxPub 2`. -/
theorem calls_two {ρ : Nat → Bool} {shp : BT} {region : List Cell} {V : OTerm}
    {g : OTerm} (hg : P2Once.GQ R.J g) (hV : V = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ g)
    {bs₀ : List Bool} (hb0 : P2Jet.bitsAt (cMachineO ρ shp region [V]).heap P2Jet.slotAddrs = some bs₀)
    (ho0 : otermAt (cMachineO ρ shp region [V]).heap ((cMachineO ρ shp region [V]).heap.length + 1) R.root =
      some (Poseidon2SKI.combT bs₀).toO)
    (hr : ∀ i c, region[i]? = some c → Wit.cellOK (BT.nleaves shp + 3 + i) c = true)
    (hseg : R.segRoots = (cHeapO ρ shp region [V]).2) (hn : R.n = 1)
    (hA : AcceptsCP R.A (cMachineO ρ shp region [V]) [] [] R.J R.root R.segRoots (cHeapO ρ shp region [V]).1.length
      R.n R.e R.row) {K : Nat} (hK : R.e 0 < K) :
    R.calls K = 2 := by
  have hA' := hA
  rw [hseg, hn] at hA'
  have hnr : ∀ i, isRestart R.e R.n i = false := fun i => by
    cases h : isRestart R.e R.n i
    · rfl
    · obtain ⟨j, hj, _⟩ := isRestart_iff.1 h; omega
  have he : R.e (R.n - 1) = R.e 0 := by rw [hn]
  obtain ⟨r0, r1, h01, h1, hs0, hs1, hu⟩ := P2Once.twice_of hg hV hb0 ho0 hr hA' R.jetAt (fun i hi => by
    cases hj : R.jetAt i with
    | false => exact .inl ⟨rfl, plain_row hA (by rw [he]; exact hi) (hnr i) hj⟩
    | true =>
      obtain ⟨_, hlt, hp2⟩ := jetAt_spec hj
      rw [rowQ_of_le (by omega), rowQ_of_le (by omega)] at hp2
      exact .inr ⟨rfl, hp2⟩)
  unfold calls
  rw [filter_two R.jetAt h01 (fun i => ⟨fun h => ?_, fun h => ?_⟩) K]
  · omega
  · have := (jetAt_spec h).2.1
    exact hu i (by rw [← he]; exact this) h
  · rcases h with rfl | rfl
    · exact hs0
    · exact hs1

end P2Run

open Stmt Wit P2Once

set_option maxRecDepth 100000 in
/-- **`p2chain h`'s honest run calls the jet twice**: `runP_calls_one` for the
    chain, so its level table is the published `idxPub 2`. -/
theorem runP_calls_two {h : Nat} {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = 1)
    (hr : ∀ i c, region[i]? = some c → Wit.cellOK (BT.nleaves shpP + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCP A (cMachineO ρ shpP region (VsC h)) [] [] JP2 rootP
      (cHeapO ρ shpP region (VsC h)).2 (cHeapO ρ shpP region (VsC h)).1.length (VsC h).length e row)
    {K : Nat} (hK : e 0 < K) :
    (runP ρ region (VsC h) A e row).calls K = 2 := by
  obtain ⟨hb0, ho0⟩ := comb_heap ρ region (VsC h)
  have hroot : rootP = combRoot ρ (combBT 496) region :=
    combRoot_public (fun _ => false) ρ shpP (by rw [hrl]; rfl)
  rw [← hroot] at ho0
  exact P2Run.calls_two (R := runP ρ region (VsC h) A e row) (chain_GQ h) (verifierChainO_eq h) hb0 ho0 hr rfl rfl
    hA hK

set_option maxRecDepth 100000 in
/-- **An accepted proof of a verifier in the chain's frame has exactly two
    jet rows**: its CPU table has exactly two rows with `P2SEL = 1`, and `0`
    on every other (`compP_once` with `twice_of`). -/
theorem compP_twice {V g : OTerm} (hg : GQ JP2 g) (hV : V = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ g)
    (hocc : ∀ x, Occ x V → x = JP2 ∨ x = JP2 + 1) {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compPAirsG [V]) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧
      ∃ r0 r1, r0 < r1 ∧ r1 < C.h ∧ C.main r0 P2SEL = 1 ∧ C.main r1 P2SEL = 1 ∧
        ∀ r, r < C.h → r ≠ r0 → r ≠ r1 → C.main r P2SEL = 0 := by
  have hacc' := accepted_transfer hs ((acceptedP_iff_of (compPG_guarded [V]) hs ts).1 hacc)
  obtain ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, ok⟩ := compPOK_ofG hacc'
  refine ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, ?_⟩
  have hv : ∀ V' ∈ [V], ∀ x, Occ x V' → x < JP2 + 2 := fun V' hV' x hx => by
    rw [List.mem_singleton.1 hV'] at hx
    rcases hocc x hx with rfl | rfl <;> omega
  have hP : JP2 + 2 < P := by decide
  have hroot : rootP < P := by
    have := ok.heap_lt
    have hfit := cMachineO_fitsB (JP2 + 2) (fun _ => false) shpP (List.replicate 1 .S) [V]
      (fun i c h' => blank_region 1 i c h' _) hv
    have : rootP < (blankMO shpP 1 [V]).heap.length := hfit.2.2
    omega
  have h499 : 499 ≤ (blankMO shpP 1 [V]).heap.length := by
    have := blankO_prefix shpP 1 [V]
    rw [shpP_nleaves] at this
    omega
  have hJ : JP2 + 1 < P := by decide
  have hcp := ok.acceptsCP hv (Nat.zero_lt_succ _) hP hJ hroot h499
  have hl : (regionM (memOf Mm) (BT.nleaves shpP) 1).length = (List.replicate 1 Cell.S).length := by
    rw [List.length_replicate]; exact ok.region_len
  obtain ⟨_, hstk, hR, _, _, _⟩ := cMachineO_public (bitsM (memOf Mm)) (fun _ => false) shpP
    (regionM (memOf Mm) (BT.nleaves shpP) 1) (List.replicate 1 .S) [V] hl
  have hroot' : rootP = combRoot (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) :=
    combRoot_public _ _ shpP (by rw [hl]; rfl)
  have hroots : blankRootsO shpP 1 [V] = (cHeapO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).2 :=
    hR.symm
  have hnil : (blankMO shpP 1 [V]).stk =
      (cHeapO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).1.length := hstk.symm
  rw [hroot', hroots, hnil] at hcp
  have hwf := ok.regionWF
  obtain ⟨hb0, ho0⟩ := comb_heap (bitsM (memOf Mm)) (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]
  have hend : endRow (rsF C) (C.h - 1) [V].length 0 = C.h - 1 := endRow_last _ _ _ (Nat.zero_lt_succ _)
  have hc := ok.cnt_last
  rw [blankRootsO_length] at hc
  -- the rows before the end: plain, or the jet's
  have hsel : ∀ i, i < endRow (rsF C) (C.h - 1) [V].length 0 →
      (decide (C.main i P2SEL = 1) = false ∧ Air.NormRow (memOf Mm) [] [] (rowOf C i) (rowOf C (i + 1))) ∨
      (decide (C.main i P2SEL = 1) = true ∧
        (P2Jet.p2Row (memOf Mm) JP2 (combRoot (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1))
          (rowOf C i) = some (rowOf C (i + 1)) ∨
          P2Jet.p2RowS (memOf Mm) (JP2 + 1) (rowOf C i) = some (rowOf C (i + 1)))) := by
    intro i hi
    rw [hend] at hi
    have hrs : rsF C i = 0 := by
      rcases Nat.lt_or_ge (rsF C i) 1 with h1 | h1
      · omega
      · obtain ⟨j, hj, _⟩ := endRow_of_one _ ok.rs_le hc hi (by have := ok.rs_le i; omega)
        exact absurd hj (by show ¬ (j + 1 < 1); omega)
    have hrs' : C.main i RS = 0 := by
      rw [rsF_eq (by omega)] at hrs
      rw [← ofN_val (C.main i RS), hrs]; rfl
    rw [← hroot']
    rcases ok.normRowSel (by omega) hrs' hJ hroot h499 with ⟨h0, hn⟩ | ⟨h1, hj⟩
    · exact .inl ⟨by rw [h0]; decide, hn⟩
    · exact .inr ⟨by rw [h1]; decide, hj⟩
  have hb0' : P2Jet.bitsAt (cMachineO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).heap
      P2Jet.slotAddrs = some ((List.range' 0 496).map (bitsM (memOf Mm))) := hb0
  have ho0' : otermAt (cMachineO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).heap
      ((cMachineO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).heap.length + 1)
      (combRoot (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1)) =
      some (combT ((List.range' 0 496).map (bitsM (memOf Mm)))).toO := ho0
  have hwf' : ∀ i c, (regionM (memOf Mm) (BT.nleaves shpP) 1)[i]? = some c →
      cellOK (BT.nleaves shpP + 3 + i) c = true := hwf
  obtain ⟨r0, r1, h01, hr1, hs0, hs1, huniq⟩ :=
    twice_of (shp := shpP) hg hV hb0' ho0' hwf' hcp _ hsel
  rw [hend] at hr1 huniq
  have huniq' : ∀ r, r < C.h → C.main r P2SEL = 1 → r = r0 ∨ r = r1 := by
    intro r hr hr1'
    rcases Nat.lt_or_ge r (C.h - 1) with hlt | hge
    · exact huniq r hlt (decide_eq_true hr1')
    · -- the last row reads `K` at its head, not the jet
      exfalso
      have hrl : r = C.h - 1 := by omega
      have ends := (hcp.ends 0 (Nat.zero_lt_succ _)).1
      rw [hend, ← hrl] at ends
      have : rd (memOf Mm) (rowOf C r).ctr (rowOf C r).hd = rd (memOf Mm) (C.main r CTR).val (C.main r HD).val := rfl
      rw [this] at ends
      rcases (ok.jetReads hr hr1' hJ hroot).1 with ⟨_, hjr, _⟩ | ⟨_, hjr, _⟩
      · rw [hjr] at ends; cases ends
      · rw [hjr] at ends; cases ends
  refine ⟨r0, r1, h01, by omega, of_decide_eq_true hs0, of_decide_eq_true hs1, fun r hr hne0 hne1 => ?_⟩
  -- every other row's selector is clear: it is `0` or `1` by its kind
  obtain ⟨k, hk⟩ := kind_ofP2 ok.cpu hr
  rw [hk.2.2.2]
  split
  · next h12 =>
    rcases huniq' r hr (by rw [hk.2.2.2, if_pos h12]) with rfl | rfl
    · exact absurd rfl hne0
    · exact absurd rfl hne1
  · rfl

/-- **Every accepted proof of `p2chain h` has exactly two jet rows**: its CPU
    table has exactly two rows with `P2SEL = 1`, and `0` on every other (the
    analog of `p2pre_once`). -/
theorem p2chain_twice {h : Nat} {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compPAirsG (VsC h)) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧
      ∃ r0 r1, r0 < r1 ∧ r1 < C.h ∧ C.main r0 P2SEL = 1 ∧ C.main r1 P2SEL = 1 ∧
        ∀ r, r < C.h → r ≠ r0 → r ≠ r1 → C.main r P2SEL = 0 :=
  compP_twice (chain_GQ h) (verifierChainO_eq h) (verifierChainO_occ h) hs hacc

end Circuit

-- ---------------------------------------------------------------------------
-- The chain's verifier accepts honest bits
-- ---------------------------------------------------------------------------

namespace P2Chain

open Compose CompM ComposedPText Poseidon2SKI P2Pre P2Complete

/-- **The verifier of `p2chain h` accepts a chain's preimage**: on 496 bits
    whose elements, permuted twice, give a state beginning with `h`, with
    any witness.  The converse of `p2chain_meaning`, as `p2pre_complete` is
    of `p2pre_meaning`: `Pcomb` passes the first permutation's bits to
    `Pbits ⬝ CHECK_h`, `Pbits` the second's to `CHECK_h`, which passes
    `h`'s bits and absorbs the rest (`chk_complete`). -/
theorem p2chain_complete {h : Nat} {ρ : Nat → Bool}
    (hperm : (Poseidon2.permute (valsB ((Poseidon2.permute (valsB ((List.range 496).map ρ))).flatMap
      (BitArith.bitsOf 31)))).getD 0 0 = h) (w : Term) :
    EvalRel ((VsC h).map (·.close (jetEnv JP2)), SameShape (combBT 496)) (fillB (combBT 496) ρ 0) w := by
  apply evalRel_of
  have hlen : ((List.range 496).map ρ).length = 496 := by rw [List.length_map, List.length_range]
  generalize (List.range 496).map ρ = bs at hperm hlen ⊢
  have hb := absN_beta_close [0, 1] (.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h) ⬝ₒ .var 0) (jetEnv JP2)
    [combT bs, w] rfl
  generalize hσ : overrideC (jetEnv JP2) [0, 1] [combT bs, w] = σ at hb
  have hJ : σ JP2 = Pcomb := by rw [← hσ]; exact env_J _ _
  have hJS : σ JP2S = Pbits := by rw [← hσ]; exact env_JS _ _
  have h0 : σ 0 = combT bs := by rw [← hσ]; rfl
  have e1 : (OTerm.var JP2 ⬝ₒ (.var JP2S ⬝ₒ checkO h) ⬝ₒ .var 0).close σ =
      Pcomb ⬝ (Pbits ⬝ (checkO h).close σ) ⬝ combT bs := by
    show σ JP2 ⬝ (σ JP2S ⬝ (checkO h).close σ) ⬝ σ 0 = _
    rw [hJ, hJS, h0]
  rw [e1] at hb
  -- the first call: `Pcomb` passes its outputs to `Pbits ⬝ CHECK_h`
  refine hb.trans ((jet_step bs hlen _).trans ?_)
  generalize hcs : (Poseidon2.permute (valsB bs)).flatMap (BitArith.bitsOf 31) = cs at hperm ⊢
  have hcl : cs.length = 496 := by rw [← hcs]; exact out_length bs
  -- the second: `Pbits` passes its outputs to `CHECK_h`
  have hQ := Pbits_implements ⟨cs, hcl⟩ ((checkO h).close σ)
  rw [poseidon2B_encI, poseidon2B_encO, poseidon2B_spec, appT] at hQ
  dsimp only at hQ
  refine hQ.trans ?_
  -- `CHECK_h` reads `h`'s bits
  have hY : (Poseidon2.permute (valsB cs)).length = 16 := permute_len _ (valsB_length cs)
  obtain ⟨y, ys, hys⟩ : ∃ y ys, Poseidon2.permute (valsB cs) = y :: ys := by
    cases hp : Poseidon2.permute (valsB cs) with
    | nil => rw [hp] at hY; cases hY
    | cons y ys => exact ⟨y, ys, rfl⟩
  rw [hys] at hY hperm ⊢
  have hy : y = h := hperm
  rw [bits_flatMap_cons, List.map_append, hy]
  exact chk_complete 465 (BitArith.bitsOf 31 h) σ _
    (by rw [List.length_map, flatMap_length31, Nat.succ.inj hY])

end P2Chain
