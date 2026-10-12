import Ski.ZK.TranscriptN
import Ski.Circuit.CompJComplete

/-!
# Zero knowledge of the composed circuit with jets

**`compJ_transcript`**: the transcript of a proof of the composed circuit
with jets is simulatable, over a hiding PCS: `transcript_zkN` for the tree
of eight private tables and seven blinding tuples that `compJAirs` and
`bench/plonky3/src/compj.rs` blind,

    WIT —a— CPU —b— MEM,   CPU —c— POP —d— INSTW —e— TMPL —f— HDR —g— ROOTS,

in the tree's order memory, CPU, witness, POP, INSTW, TMPL, HDR, ROOTS
(vertex `k + 1` hangs on `jetPar (k + 1)` by edge `k`).  The program and
segment tables are public, their terminals the simulator's `tp`.

The prover's tables must balance with the public program and segment
tables and carry clear blinding flags (`UnblindedCJ`); the honest tables
of milestone 6, with the honest program and witness tables, do
(`CRun.honest_zk`).
-/

namespace Circuit

open ZKF B Air JetTable Compose CompM Mach

-- ---------------------------------------------------------------------------
-- The tree
-- ---------------------------------------------------------------------------

/-- Each vertex's parent: CPU on memory, the witness and POP on the CPU,
    then the chain POP, INSTW, TMPL, HDR, ROOTS. -/
def jetPar : Nat → Nat
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | _ => 0

theorem jetPar_ok : ∀ k, jetPar (k + 1) ≤ k
  | 0 => Nat.le_refl 0
  | 1 => Nat.le_refl 1
  | 2 => by decide
  | 3 => by decide
  | 4 => by decide
  | 5 => by decide
  | 6 => by decide
  | _ + 7 => Nat.zero_le _

/-- Each edge's bus. -/
def jetBus : Nat → String
  | 0 => "blind_b"
  | 1 => "blind_a"
  | 2 => "blind_c"
  | 3 => "blind_d"
  | 4 => "blind_e"
  | 5 => "blind_f"
  | _ => "blind_g"

/-- Each edge's direction: the child sends on `blind_b` and `blind_a`, and
    receives on `blind_c` … `blind_g`. -/
def jetSg (k : Nat) : Bool := decide (2 ≤ k)

/-- **The tree's view, unfolded.** -/
theorem viewT_jet (β : EF) (pre : String → EF) (x : Nat → EF) (t : Nat → Tup) :
    viewT β (fun k => pre (jetBus k)) jetSg jetPar 8 x t =
      [(x 0).sub (blindTerm β (pre "blind_b") (t 0)),
       (((x 1).sub (EF.zero.sub (blindTerm β (pre "blind_c") (t 2)))).sub (blindTerm β (pre "blind_a") (t 1))).add
         (blindTerm β (pre "blind_b") (t 0)),
       (x 2).add (blindTerm β (pre "blind_a") (t 1)),
       ((x 3).sub (EF.zero.sub (blindTerm β (pre "blind_d") (t 3)))).add
         (EF.zero.sub (blindTerm β (pre "blind_c") (t 2))),
       ((x 4).sub (EF.zero.sub (blindTerm β (pre "blind_e") (t 4)))).add
         (EF.zero.sub (blindTerm β (pre "blind_d") (t 3))),
       ((x 5).sub (EF.zero.sub (blindTerm β (pre "blind_f") (t 5)))).add
         (EF.zero.sub (blindTerm β (pre "blind_e") (t 4))),
       ((x 6).sub (EF.zero.sub (blindTerm β (pre "blind_g") (t 6)))).add
         (EF.zero.sub (blindTerm β (pre "blind_f") (t 5))),
       (x 7).add (EF.zero.sub (blindTerm β (pre "blind_g") (t 6)))] :=
  rfl

-- ---------------------------------------------------------------------------
-- Identities by normal forms
-- ---------------------------------------------------------------------------

/-- A chain vertex: received `u`, sent `v`. -/
theorem ef_mid (x u v : EF) : (x.sub u).add v = (x.sub (EF.zero.sub v)).add (EF.zero.sub u) :=
  Q.eq_of_norm (p := ((Q.var 0).sub (Q.var 1)).add (Q.var 2))
    (q := ((Q.var 0).sub ((Q.var 3).sub (Q.var 2))).add ((Q.var 3).sub (Q.var 1)))
    (by decide) (env4 x u v EF.zero)

/-- The last leaf: received `u`. -/
theorem ef_last (x u : EF) : x.sub u = x.add (EF.zero.sub u) :=
  Q.eq_of_norm (p := (Q.var 0).sub (Q.var 1)) (q := (Q.var 0).add ((⟨k 0, k 0, k 0, k 0⟩ : Q).sub (Q.var 1)))
    (by decide) (env3 x u EF.zero)

/-- The CPU: received `u` on `blind_a`, sent `v` on `blind_b` and `w` on
    `blind_c`. -/
theorem ef_cpu (x u v w : EF) : ((x.sub u).add v).add w = ((x.sub (EF.zero.sub w)).sub u).add v :=
  Q.eq_of_norm (p := (((Q.var 0).sub (Q.var 1)).add (Q.var 2)).add (Q.var 3))
    (q := (((Q.var 0).sub ((⟨k 0, k 0, k 0, k 0⟩ : Q).sub (Q.var 3))).sub (Q.var 1)).add (Q.var 2))
    (by decide) (env8 x u v w EF.zero EF.zero EF.zero EF.zero)

-- ---------------------------------------------------------------------------
-- A blinded table's terminal
-- ---------------------------------------------------------------------------

theorem avoid_off {c i : Nat} (h : ¬ (c ≤ i ∧ i < c + 5)) (o : Nat) : avoid c (.main o i) = true := by
  show (!(decide (c ≤ i) && decide (i < c + 5))) = true
  by_cases h1 : c ≤ i
  · rw [decide_eq_true h1, decide_eq_false (fun h2 => h ⟨h1, h2⟩)]; rfl
  · rw [decide_eq_false h1]; rfl

/-- A blinding message off another block's columns. -/
theorem blindInter_avoids {bus : String} {c d : Nat} (neg : Bool) (h : c + 5 ≤ d ∨ d + 5 ≤ c) :
    (blindInter bus d neg).avoids c = true := by
  have ha : ∀ j, j < 5 → avoid c (.main 0 (d + j)) = true := fun j hj => avoid_off (by omega) 0
  have h0 := ha 0 (by decide)
  have h1 := ha 1 (by decide)
  have h2 := ha 2 (by decide)
  have h3 := ha 3 (by decide)
  have h4 := ha 4 (by decide)
  rw [Nat.add_zero] at h0
  unfold Inter.avoids blindInter
  cases neg <;>
    simp only [E.onlyAtoms, List.all_cons, List.all_nil, h0, h1, h2, h3, h4, Bool.and_self, if_true, if_false,
      Bool.false_eq_true]

/-- The blocks of a table with a received and a sent tuple. -/
theorem withBlocks2_inters (A : AirD) (b1 b2 : String) :
    (withBlocks A [(b1, false), (b2, true)]).inters =
      A.inters ++ blindInter b1 A.width true :: [blindInter b2 (A.width + 5) false] := rfl

theorem withBlocks1_inters (A : AirD) (b1 : String) :
    (withBlocks A [(b1, false)]).inters = A.inters ++ blindInter b1 A.width true :: [] := rfl

/-- **A table receiving `a` and sending `d`**: its blinded terminal. -/
theorem terminal_wb2 (pre : String → EF) (β : EF) {A : AirD} {b1 b2 : String}
    (hav : ∀ I ∈ A.inters, I.avoids A.width = true ∧ I.avoids (A.width + 5) = true) {T : Table} (hh : 0 < T.h)
    (hw : Wide A T) (a d : Tup) :
    terminal pre β (withBlocks A [(b1, false), (b2, true)]) ((T.setBlind A.width a).setBlind (A.width + 5) d) =
      ((terminal pre β (withBlocks A [(b1, false), (b2, true)]) T).sub (blindTerm β (pre b1) a)).add
        (blindTerm β (pre b2) d) := by
  have e1 := terminal_setBlind pre β (withBlocks2_inters A b1 b2) (fun I hI => (hav I hI).1)
    (fun I hI => by
      simp only [List.mem_singleton] at hI; rw [hI]; exact blindInter_avoids false (.inl (Nat.le_refl _)))
    T hh (fun r hr => hw r hr _ (by omega)) a
  have hinters : (withBlocks A [(b1, false), (b2, true)]).inters =
      (A.inters ++ [blindInter b1 A.width true]) ++ blindInter b2 (A.width + 5) false :: [] := by
    rw [withBlocks2_inters, List.append_assoc]; rfl
  have e2 := terminal_setBlind pre β hinters
    (fun I hI => by
      rcases List.mem_append.1 hI with hI | hI
      · exact (hav I hI).2
      · simp only [List.mem_singleton] at hI; rw [hI]; exact blindInter_avoids true (.inr (Nat.le_refl _)))
    (fun I hI => absurd hI List.not_mem_nil) (T.setBlind A.width a) hh
    (fun r hr => by rw [setBlind_other a (Nat.le_refl _)]; exact hw r hr _ (by omega)) d
  rw [e2, e1, ofF_neg_mul, ofF_one_mul]

/-- **A table receiving `a`**: its blinded terminal. -/
theorem terminal_wb1 (pre : String → EF) (β : EF) {A : AirD} {b1 : String}
    (hav : ∀ I ∈ A.inters, I.avoids A.width = true) {T : Table} (hh : 0 < T.h) (hw : Wide A T) (a : Tup) :
    terminal pre β (withBlocks A [(b1, false)]) (T.setBlind A.width a) =
      (terminal pre β (withBlocks A [(b1, false)]) T).sub (blindTerm β (pre b1) a) := by
  rw [terminal_setBlind pre β (withBlocks1_inters A b1) hav (fun I hI => absurd hI List.not_mem_nil) T hh
    (fun r hr => hw r hr _ (by omega)) a, ofF_neg_mul]

/-- Ten elements as leaves. -/
def env10 (a b c d e f g h i j : EF) : Atom → F
  | .main 0 0 => a.x0
  | .main 0 1 => a.x1
  | .main 0 2 => a.x2
  | .main 0 3 => a.x3
  | .main 0 4 => b.x0
  | .main 0 5 => b.x1
  | .main 0 6 => b.x2
  | .main 0 7 => b.x3
  | .main 0 8 => c.x0
  | .main 0 9 => c.x1
  | .main 0 10 => c.x2
  | .main 0 11 => c.x3
  | .main 0 12 => d.x0
  | .main 0 13 => d.x1
  | .main 0 14 => d.x2
  | .main 0 15 => d.x3
  | .main 0 16 => e.x0
  | .main 0 17 => e.x1
  | .main 0 18 => e.x2
  | .main 0 19 => e.x3
  | .main 0 20 => f.x0
  | .main 0 21 => f.x1
  | .main 0 22 => f.x2
  | .main 0 23 => f.x3
  | .main 0 24 => g.x0
  | .main 0 25 => g.x1
  | .main 0 26 => g.x2
  | .main 0 27 => g.x3
  | .main 0 28 => h.x0
  | .main 0 29 => h.x1
  | .main 0 30 => h.x2
  | .main 0 31 => h.x3
  | .main 0 32 => i.x0
  | .main 0 33 => i.x1
  | .main 0 34 => i.x2
  | .main 0 35 => i.x3
  | .main 0 36 => j.x0
  | .main 0 37 => j.x1
  | .main 0 38 => j.x2
  | .main 0 39 => j.x3
  | _ => 0

-- ---------------------------------------------------------------------------
-- The published terminals
-- ---------------------------------------------------------------------------

/-- **The eight private tables before blinding**: each has a row, and its
    blinding flags are clear (the blinded ones' columns past the base AIR's
    width, the CPU's at `BLAJ`, `BLBJ`, `BLCJ`, the memory's at `5`, the
    witness table's at `WT_BLIND`). -/
structure UnblindedCJ (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Wt Rt Hd Tm Po Iw : Table) : Prop where
  hc : 0 < C.h
  hm : 0 < Mm.h
  hw : 0 < Wt.h
  hr : 0 < Rt.h
  hd : 0 < Hd.h
  ht : 0 < Tm.h
  hp : 0 < Po.h
  hi : 0 < Iw.h
  za : ∀ r, r < C.h → C.main r (BLAJ + 4) = 0
  zb : ∀ r, r < C.h → C.main r (BLBJ + 4) = 0
  zc : ∀ r, r < C.h → C.main r (BLCJ + 4) = 0
  zm : ∀ r, r < Mm.h → Mm.main r (5 + 4) = 0
  zw : ∀ r, r < Wt.h → Wt.main r (WT_BLIND + 4) = 0
  wr : Wide (providerAir "roots" 2 (rootsRowsCJ roots)) Rt
  wd : Wide (providerAir "hdr" 7 (hdrRowsCJ jets)) Hd
  wt : Wide (providerAir "tmpl" 11 (tmplRowsCJ jets)) Tm
  wp : Wide popAir Po
  wi : Wide instwAir Iw

/-- The unblinded private terminals, in the tree's order. -/
def cjBase (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA N W : Nat) (roots : List (Nat × Nat))
    (jets : List Air.Jet) (C Mm Wt Rt Hd Tm Po Iw : Table) : Nat → EF
  | 0 => terminal pre β memAirC Mm
  | 1 => terminal pre β (cpuAirCJ hd0 stk0 ctr0 n nilA) C
  | 2 => terminal pre β (witAir N W) Wt
  | 3 => terminal pre β popAirCJ Po
  | 4 => terminal pre β instwAirCJ Iw
  | 5 => terminal pre β (tmplAirCJ jets) Tm
  | 6 => terminal pre β (hdrAirCJ jets) Hd
  | _ => terminal pre β (rootsAirCJ roots) Rt

/-- **What a proof of the composed circuit with jets publishes of its
    witness**: the blinded private tables' terminals, in the tree's order;
    `t k` is edge `k`'s tuple (`compj.rs`'s `tb, ta, tc, td, te, tf, tg`). -/
def compJViewN (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA N W : Nat) (roots : List (Nat × Nat))
    (jets : List Air.Jet) (C Mm Wt Rt Hd Tm Po Iw : Table) (t : Nat → Tup) : List EF :=
  [terminal pre β memAirC (Mm.setBlind 5 (t 0)),
   terminal pre β (cpuAirCJ hd0 stk0 ctr0 n nilA) (((C.setBlind BLAJ (t 1)).setBlind BLBJ (t 0)).setBlind BLCJ (t 2)),
   terminal pre β (witAir N W) (Wt.setBlind WT_BLIND (t 1)),
   terminal pre β popAirCJ ((Po.setBlind popAir.width (t 2)).setBlind (popAir.width + 5) (t 3)),
   terminal pre β instwAirCJ ((Iw.setBlind instwAir.width (t 3)).setBlind (instwAir.width + 5) (t 4)),
   terminal pre β (tmplAirCJ jets) ((Tm.setBlind 1 (t 4)).setBlind 6 (t 5)),
   terminal pre β (hdrAirCJ jets) ((Hd.setBlind 1 (t 5)).setBlind 6 (t 6)),
   terminal pre β (rootsAirCJ roots) (Rt.setBlind 1 (t 6))]

/-- The CPU's messages but its blinding ones. -/
theorem cpuCJ_inters (hd0 stk0 ctr0 n nilA : Nat) : (cpuAirCJ hd0 stk0 ctr0 n nilA).inters =
    cpuIntersCJ.take 16 ++ blindInter "blind_a" BLAJ true ::
      [blindInter "blind_b" BLBJ false, blindInter "blind_c" BLCJ false] := rfl

/-- **The CPU's blinded terminal.** -/
theorem terminal_cpuCJ (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA : Nat) {C : Table} (hh : 0 < C.h)
    (za : ∀ r, r < C.h → C.main r (BLAJ + 4) = 0) (zb : ∀ r, r < C.h → C.main r (BLBJ + 4) = 0)
    (zc : ∀ r, r < C.h → C.main r (BLCJ + 4) = 0) (a b c : Tup) :
    terminal pre β (cpuAirCJ hd0 stk0 ctr0 n nilA) (((C.setBlind BLAJ a).setBlind BLBJ b).setBlind BLCJ c) =
      (((terminal pre β (cpuAirCJ hd0 stk0 ctr0 n nilA) C).sub (blindTerm β (pre "blind_a") a)).add
        (blindTerm β (pre "blind_b") b)).add (blindTerm β (pre "blind_c") c) := by
  have hA : ∀ I ∈ cpuIntersCJ.take 16, I.avoids BLAJ = true := all_mem (by decide)
  have hB : ∀ I ∈ cpuIntersCJ.take 16, I.avoids BLBJ = true := all_mem (by decide)
  have hC : ∀ I ∈ cpuIntersCJ.take 16, I.avoids BLCJ = true := all_mem (by decide)
  have eA := terminal_setBlind pre β (cpuCJ_inters hd0 stk0 ctr0 n nilA) hA
    (all_mem (l := [blindInter "blind_b" BLBJ false, blindInter "blind_c" BLCJ false]) (by decide)) C hh za a
  have iB : (cpuAirCJ hd0 stk0 ctr0 n nilA).inters =
      (cpuIntersCJ.take 16 ++ [blindInter "blind_a" BLAJ true]) ++ blindInter "blind_b" BLBJ false ::
        [blindInter "blind_c" BLCJ false] := rfl
  have eB := terminal_setBlind pre β iB
    (fun I hI => by
      rcases List.mem_append.1 hI with hI | hI
      · exact hB I hI
      · exact all_mem (l := [blindInter "blind_a" BLAJ true]) (by decide) I hI)
    (all_mem (l := [blindInter "blind_c" BLCJ false]) (by decide)) (C.setBlind BLAJ a) hh
    (fun r hr => by rw [setBlind_other a (by decide)]; exact zb r hr) b
  have iC : (cpuAirCJ hd0 stk0 ctr0 n nilA).inters =
      (cpuIntersCJ.take 16 ++ [blindInter "blind_a" BLAJ true, blindInter "blind_b" BLBJ false]) ++
        blindInter "blind_c" BLCJ false :: [] := rfl
  have eC := terminal_setBlind pre β iC
    (fun I hI => by
      rcases List.mem_append.1 hI with hI | hI
      · exact hC I hI
      · exact all_mem (l := [blindInter "blind_a" BLAJ true, blindInter "blind_b" BLBJ false]) (by decide) I hI)
    (fun I hI => absurd hI List.not_mem_nil) ((C.setBlind BLAJ a).setBlind BLBJ b) hh
    (fun r hr => by rw [setBlind_other b (by decide), setBlind_other a (by decide)]; exact zc r hr) c
  rw [eC, eB, eA, ofF_neg_mul, ofF_one_mul, ofF_one_mul]

/-- **The published terminals are the tree's view** of the unblinded ones. -/
theorem compJ_chain (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA N W : Nat) {roots : List (Nat × Nat)}
    {jets : List Air.Jet} {C Mm Wt Rt Hd Tm Po Iw : Table} (h : UnblindedCJ roots jets C Mm Wt Rt Hd Tm Po Iw)
    (t : Nat → Tup) :
    compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t =
      viewT β (fun k => pre (jetBus k)) jetSg jetPar 8
        (cjBase pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw) t := by
  rw [viewT_jet]
  have bt := fun (b : String) (a : Tup) => blindTerm β (pre b) a
  have e0 : terminal pre β memAirC (Mm.setBlind 5 (t 0)) =
      (terminal pre β memAirC Mm).sub (blindTerm β (pre "blind_b") (t 0)) := by
    rw [terminal_setBlind pre β (L1 := [⟨"mem", 0, .neg (col 4), [col 0, col 1, col 2, col 3]⟩]) (L2 := [])
      (bus := "blind_b") (c := 5) (neg := true) rfl (all_mem (l := [_]) (by decide))
      (fun I hI => absurd hI List.not_mem_nil) Mm h.hm h.zm (t 0), ofF_neg_mul]
  have e2 : terminal pre β (witAir N W) (Wt.setBlind WT_BLIND (t 1)) =
      (terminal pre β (witAir N W) Wt).add (blindTerm β (pre "blind_a") (t 1)) := by
    rw [terminal_setBlind pre β (L1 := [witInters.head (by decide)]) (L2 := []) (bus := "blind_a") (c := WT_BLIND)
      (neg := false) rfl (all_mem (l := [_]) (by decide)) (fun I hI => absurd hI List.not_mem_nil) Wt h.hw h.zw
      (t 1), ofF_one_mul]
  have e1 := terminal_cpuCJ pre β hd0 stk0 ctr0 n nilA h.hc h.za h.zb h.zc (t 1) (t 0) (t 2)
  have e3 : terminal pre β popAirCJ ((Po.setBlind popAir.width (t 2)).setBlind (popAir.width + 5) (t 3)) = _ :=
    terminal_wb2 pre β (A := popAir) (b1 := "blind_c") (b2 := "blind_d")
      (fun I hI => ⟨all_mem (l := popAir.inters) (by decide) I hI, all_mem (l := popAir.inters) (by decide) I hI⟩)
      h.hp h.wp (t 2) (t 3)
  have e4 : terminal pre β instwAirCJ ((Iw.setBlind instwAir.width (t 3)).setBlind (instwAir.width + 5) (t 4)) = _ :=
    terminal_wb2 pre β (A := instwAir) (b1 := "blind_d") (b2 := "blind_e")
      (fun I hI => ⟨all_mem (l := instwAir.inters) (by decide) I hI, all_mem (l := instwAir.inters) (by decide) I hI⟩)
      h.hi h.wi (t 3) (t 4)
  have e5 : terminal pre β (tmplAirCJ jets) ((Tm.setBlind 1 (t 4)).setBlind 6 (t 5)) = _ :=
    terminal_wb2 pre β (A := providerAir "tmpl" 11 (tmplRowsCJ jets)) (b1 := "blind_e") (b2 := "blind_f")
      (fun I hI => by
        simp only [providerAir, List.mem_singleton] at hI; subst hI
        exact ⟨(by decide : Inter.avoids 1 (⟨"tmpl", 0, (col 0).neg, (List.range 11).map prec⟩ : Inter) = true), (by decide : Inter.avoids 6 (⟨"tmpl", 0, (col 0).neg, (List.range 11).map prec⟩ : Inter) = true)⟩)
      h.ht h.wt (t 4) (t 5)
  have e6 : terminal pre β (hdrAirCJ jets) ((Hd.setBlind 1 (t 5)).setBlind 6 (t 6)) = _ :=
    terminal_wb2 pre β (A := providerAir "hdr" 7 (hdrRowsCJ jets)) (b1 := "blind_f") (b2 := "blind_g")
      (fun I hI => by
        simp only [providerAir, List.mem_singleton] at hI; subst hI
        exact ⟨(by decide : Inter.avoids 1 (⟨"hdr", 0, (col 0).neg, (List.range 7).map prec⟩ : Inter) = true), (by decide : Inter.avoids 6 (⟨"hdr", 0, (col 0).neg, (List.range 7).map prec⟩ : Inter) = true)⟩)
      h.hd h.wd (t 5) (t 6)
  have e7 : terminal pre β (rootsAirCJ roots) (Rt.setBlind 1 (t 6)) = _ :=
    terminal_wb1 pre β (A := providerAir "roots" 2 (rootsRowsCJ roots)) (b1 := "blind_g")
      (fun I hI => by
        simp only [providerAir, List.mem_singleton] at hI; subst hI
        exact (by decide : Inter.avoids 1 (⟨"roots", 0, (col 0).neg, (List.range 2).map prec⟩ : Inter) = true))
      h.hr h.wr (t 6)
  unfold compJViewN
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  simp only [List.cons.injEq, and_true]
  refine ⟨rfl, ef_cpu _ _ _ _, rfl, ef_mid _ _ _, ef_mid _ _ _, ef_mid _ _ _, ef_mid _ _ _, ef_last _ _⟩

/-- **The unblinded private terminals sum to minus the public ones'**, by
    LogUp's completeness over balanced tables. -/
theorem compJ_sum (pre : String → EF) (β : EF) {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat}
    {segRoots : List Nat} {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Pg Wt Sg Rt Hd Tm Po Iw : Table}
    (hb : Balanced (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw)) :
    sumL (cjBase pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw) (List.range 8) =
      EF.zero.sub ((terminal pre β (progAirC heap N W) Pg).add (terminal pre β (segsAir segRoots) Sg)) := by
  have hl := logup_sum pre β _ hb
  have z : (⟨k 0, k 0, k 0, k 0⟩ : Q).eval (env10 EF.zero EF.zero EF.zero EF.zero EF.zero EF.zero EF.zero
      EF.zero EF.zero EF.zero) = EF.zero := rfl
  let c := terminal pre β (cpuAirCJ hd0 stk0 ctr0 n nilA) C
  let m := terminal pre β memAirC Mm
  let pg := terminal pre β (progAirC heap N W) Pg
  let w := terminal pre β (witAir N W) Wt
  let sg := terminal pre β (segsAir segRoots) Sg
  let rt := terminal pre β (rootsAirCJ roots) Rt
  let hd := terminal pre β (hdrAirCJ jets) Hd
  let tm := terminal pre β (tmplAirCJ jets) Tm
  let po := terminal pre β popAirCJ Po
  let iw := terminal pre β instwAirCJ Iw
  have hl' : c.add (m.add (pg.add (w.add (sg.add (rt.add (hd.add (tm.add (po.add (iw.add EF.zero))))))))) =
      EF.zero := hl
  have e : sumL (cjBase pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw) (List.range 8) =
      (c.add (m.add (pg.add (w.add (sg.add (rt.add (hd.add (tm.add (po.add (iw.add EF.zero)))))))))).sub
        (pg.add sg) := by
    show m.add (c.add (w.add (po.add (iw.add (tm.add (hd.add (rt.add EF.zero))))))) = _
    let O : Q := ⟨k 0, k 0, k 0, k 0⟩
    exact Q.eq_of_norm
      (p := (Q.var 1).add ((Q.var 0).add ((Q.var 3).add ((Q.var 8).add ((Q.var 9).add ((Q.var 7).add
        ((Q.var 6).add ((Q.var 5).add O))))))))
      (q := ((Q.var 0).add ((Q.var 1).add ((Q.var 2).add ((Q.var 3).add ((Q.var 4).add ((Q.var 5).add
        ((Q.var 6).add ((Q.var 7).add ((Q.var 8).add ((Q.var 9).add O)))))))))).sub ((Q.var 2).add (Q.var 4)))
      (by decide) (env10 c m pg w sg rt hd tm po iw)
  rw [e, hl']


-- ---------------------------------------------------------------------------
-- The transcript
-- ---------------------------------------------------------------------------

/-- **The transcript of a proof of the composed circuit with jets is
    simulatable**, over a hiding PCS: `transcript_zkN` for the tree of eight
    private tables and seven tuples (`compJ_chain`).  The prover's tables
    balance with the public program and segment tables and carry clear
    blinding flags before it blinds them with the edges' tuples `t`; so the
    simulator's `tp` and `pb`, the public tables' terminals, are public.
    Given at most `M` LogUp messages and a PCS whose view is within `ε` of a
    simulator's (`PCSCloseN`), the simulated transcript matches the real one
    on every event `E`, up to the non-generic challenges, the aborts and the
    PCS, over the `Q4 · Q4 · NR · Q4^7` draws. -/
theorem compJ_transcript {PV : Type} (off : EF → String → EF) (NR ε : Nat)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
    {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {segRoots : List Nat}
    {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Wt Rt Hd Tm Po Iw : Table}
    (hb : Balanced (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm (progTableC heap N W) Wt
      (segsPub segRoots) Rt Hd Tm Po Iw))
    (h : UnblindedCJ roots jets C Mm Wt Rt Hd Tm Po Iw)
    (hpcs : PCSCloseN off NR (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets
      C Mm Wt Rt Hd Tm Po Iw t) pcs psim ε)
    (E : TViewN PV (EF × EF) → Bool) :
    let tabs := fun t : Nat → Tup => compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets
      (((C.setBlind BLAJ (t 1)).setBlind BLBJ (t 0)).setBlind BLCJ (t 2)) (Mm.setBlind 5 (t 0))
      (progTableC heap N W) (Wt.setBlind WT_BLIND (t 1)) (segsPub segRoots) (Rt.setBlind 1 (t 6))
      ((Hd.setBlind 1 (t 5)).setBlind 6 (t 6)) ((Tm.setBlind 1 (t 4)).setBlind 6 (t 5))
      ((Po.setBlind popAir.width (t 2)).setBlind (popAir.width + 5) (t 3))
      ((Iw.setBlind instwAir.width (t 3)).setBlind (instwAir.width + 5) (t 4))
    let tv := fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t
    let pb := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W),
      terminal pre β (segsAir segRoots) (segsPub segRoots))
    let tp := fun pre β => (terminal pre β (progAirC heap N W) (progTableC heap N W)).add
      (terminal pre β (segsAir segRoots) (segsPub segRoots))
    let M := (allEntries (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm (progTableC heap N W)
      Wt (segsPub segRoots) Rt Hd Tm Po Iw)).length
    tsumN NR 7 (fun α β r t => indB (E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR 7 (fun α β r t => indB (E (simVN off pb jetBus jetSg jetPar 8 tp psim α β r t))) +
        Q4 * (NR * Q4 ^ 7 * (P * P)) + Q4 * (NR * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * ε)) ∧
    tsumN NR 7 (fun α β r t => indB (E (simVN off pb jetBus jetSg jetPar 8 tp psim α β r t))) ≤
      tsumN NR 7 (fun α β r t => indB (E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * Q4 ^ 7 * (P * P)) + Q4 * (NR * (Q4 ^ 7 * M)) + Q4 * (Q4 * (Q4 ^ 7 * ε)) :=
  transcript_zkN (m := 7) jetPar_ok
    (xu := fun pre β => cjBase pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw)
    (fun pre β t => compJ_chain pre β hd0 stk0 ctr0 n nilA N W h t)
    (fun pre β => compJ_sum pre β hb)
    (fun t => Nat.le_of_eq (by rw [allEntries_length, allEntries_length]; rfl)) hpcs E


-- ---------------------------------------------------------------------------
-- The honest prover's tables
-- ---------------------------------------------------------------------------

/-- The honest witness table's blinding flag is clear. -/
theorem witT_flag {a0 : Nat} {A : List Cell} {N W : Nat} (r : Nat) :
    (witTableG a0 A N W).main r (WT_BLIND + 4) = 0 := by
  show witColG a0 A N W r (WT_BLIND + 4) = 0
  unfold witColG
  split
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  · rfl

namespace CRun

variable {R : CRun} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCJ R.A m0 R.jroots R.jets R.segRoots nilA R.n R.e R.row) (hroots : RootsOK m0.heap R.jroots R.jets)
  {K : Nat} (hK : R.e (R.n - 1) < K)

include hA hroots hK in
/-- **The honest tables meet `compJ_transcript`'s hypotheses**: milestone
    6's tables, with the honest program and witness tables (the bits
    literal, the region well formed, the public cells the statement's),
    balance with the public program and segment tables, and their blinding
    flags are clear (`balancedCJ`, `segs_honestCJ`). -/
theorem honest_zk (hd0 stk0 ctr0 : Nat) {heap : List Cell} {N W : Nat}
    (hA0 : 0 < R.A.length) (hML : R.A.length < P) (hn : R.segRoots.length = R.n) (hnP : R.n < P)
    {HP HW : Nat} (hHP : (R.J.popRows K).length ≤ HP) (hHW : (R.J.instwRows K).length ≤ HW) (hHP0 : 0 < HP)
    (hHW0 : 0 < HW)
    (hprov : 0 < (rootsRowsCJ R.jroots).length ∧ 0 < (hdrRowsCJ R.jets).length ∧ 0 < (tmplRowsCJ R.jets).length)
    (hpub : ∀ i, i < heap.length → ¬ (3 ≤ i ∧ i < 3 + N + W) → i < R.A.length ∧ R.A.getD i .nil = heap.getD i .nil)
    (hbits : ∀ i, i < N → R.A.getD (3 + i) .nil = .K ∨ R.A.getD (3 + i) .nil = .app 0 1)
    (hreg : ∀ i, i < W → Wit.cellOK (3 + N + i) (R.A.getD (3 + N + i) .nil) = true)
    (hlenW : 3 + N + W ≤ R.A.length) (hNW : N + W ≤ 2 ^ 8) :
    Balanced (compJTables hd0 stk0 ctr0 R.n nilA heap N W R.segRoots R.jroots R.jets (R.cpuTableCJ K)
      (memTable5 R.A (cpuAirCJ hd0 stk0 ctr0 R.n nilA) (progAirC heap N W) popAirCJ instwAirCJ (witAir N W)
        (R.cpuTableCJ K) (progTableC heap N W) (R.J.popTable K HP) (R.J.instwTable K HW) (witTable R.A N W))
      (progTableC heap N W) (witTable R.A N W) (segsPub R.segRoots)
      (provTableCJ (rootsRowsCJ R.jroots) (R.J.cntRoots K)) (provTableCJ (hdrRowsCJ R.jets) (R.J.cntHdr K))
      (provTableCJ (tmplRowsCJ R.jets) (R.J.cntTmpl K)) (R.J.popTable K HP) (R.J.instwTable K HW)) ∧
    UnblindedCJ R.jroots R.jets (R.cpuTableCJ K)
      (memTable5 R.A (cpuAirCJ hd0 stk0 ctr0 R.n nilA) (progAirC heap N W) popAirCJ instwAirCJ (witAir N W)
        (R.cpuTableCJ K) (progTableC heap N W) (R.J.popTable K HP) (R.J.instwTable K HW) (witTable R.A N W))
      (witTable R.A N W)
      (provTableCJ (rootsRowsCJ R.jroots) (R.J.cntRoots K)) (provTableCJ (hdrRowsCJ R.jets) (R.J.cntHdr K))
      (provTableCJ (tmplRowsCJ R.jets) (R.J.cntTmpl K)) (R.J.popTable K HP) (R.J.instwTable K HW) := by
  refine ⟨?_, ?_⟩
  · rw [← segs_honestCJ hA hK hd0 stk0 ctr0 R.n nilA hn hnP]
    exact balancedCJ hA hroots hd0 stk0 ctr0 hML hn hnP hHP hHW
      (fun r hr I hI _ hc => progC_honest hpub r hr I hI hc)
      (witT_honest (a0 := 3) (fun _ => by decide) hbits hreg hlenW) witT_blindZero
  · have hK0 : 0 < K := by omega
    have hWt : 0 < (witTable R.A N W).h := by
      show 0 < (witRowsG 3 N W).length
      rw [witRowsG_len hNW]; exact Nat.two_pow_pos 9
    exact {
      hc := hK0
      hm := hA0
      hw := hWt
      hr := hprov.1
      hd := hprov.2.1
      ht := hprov.2.2
      hp := hHP0
      hi := hHW0
      za := fun r _ => R.colCJ_blind (i := r) (c := BLAJ + 4) (by decide) (by decide)
      zb := fun r _ => R.colCJ_blind (i := r) (c := BLBJ + 4) (by decide) (by decide)
      zc := fun r _ => R.colCJ_blind (i := r) (c := BLCJ + 4) (by decide) (by decide)
      zm := fun _ _ => rfl
      zw := fun r _ => witT_flag r
      wr := provCJ_wide
      wd := provCJ_wide
      wt := provCJ_wide
      wp := R.J.pop_wide
      wi := R.J.instw_wide }

end CRun

end Circuit
