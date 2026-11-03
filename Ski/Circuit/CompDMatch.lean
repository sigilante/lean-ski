import Ski.Circuit.CompDBus

/-!
# The circuit with the `dec` jet: the four buses, matched

Each bus's sends and receives, row by row, and their matches
(`CompDOK.need_recv`, `need_sent`, `chain_recv`, `chain_sent`,
`verd_sent`, `res_sent`), from `bus_match` over the signed buses.
-/

namespace Circuit

open B Air

/-- **A need on `decn`**: the CPU's jet row asks for its subject, in the
    role `0`; a `Cell` row asks for its head (role `1` under the subject,
    `2` else) and its tail (role `2`). -/
def NeedSent (C D : Table) (v : List F) : Prop :=
  (∃ r, r < C.h ∧ C.main r DECSEL = 1 ∧ v = [C.main r CTR, C.main r (FLD + 2), 0]) ∨
  (∃ q, q < D.h ∧ D.main q Dec.KCELL = 1 ∧
    (v = [D.main q Dec.KEY, D.main q (Dec.DFLD + 43), ofN 2 - D.main q Dec.H0] ∨
      v = [D.main q Dec.KEY, D.main q (Dec.DFLD + 47), ofN 2]))

/-- A need received: by a `Cell` or an `Atom` row, at its key, pointer and role. -/
def NeedRecv (D : Table) (v : List F) : Prop :=
  ∃ q, q < D.h ∧ D.main q Dec.KCELL + D.main q Dec.KATOM = 1 ∧ v = [D.main q Dec.KEY, D.main q Dec.PC, D.main q Dec.RO]

/-- **A chain's step on `decb`**: an `Atom` row starts its bits' chain (mode
    `0` for the head, `1` else); a `Cons` row that is not the last passes
    on to its tail. -/
def ChainSent (D : Table) (v : List F) : Prop :=
  (∃ q, q < D.h ∧ D.main q Dec.KATOM = 1 ∧
    v = [D.main q Dec.KEY, D.main q (Dec.DFLD + 45), 1 - D.main q Dec.H1, 0, D.main q Dec.H1, 0]) ∨
  (∃ q, q < D.h ∧ D.main q Dec.CSEND = 1 ∧
    v = [D.main q Dec.KEY, D.main q (Dec.DFLD + 29), D.main q Dec.MODE, D.main q Dec.LVL + 1, D.main q Dec.NBW,
      D.main q Dec.WCN])

def ChainRecv (D : Table) (v : List F) : Prop :=
  ∃ q, q < D.h ∧ (D.main q Dec.KCONS = 1 ∨ D.main q Dec.KNIL = 1) ∧
    v = [D.main q Dec.KEY, D.main q Dec.PC, D.main q Dec.MODE, D.main q Dec.LVL, D.main q Dec.BW, D.main q Dec.WC]

/-- **The verdict on `decd`**: the head's last `Cons` in mode `0`, its nil, or
    a cell head; received by the subject's `Cell` row. -/
def VerdSent (D : Table) (v : List F) : Prop :=
  ∃ q, q < D.h ∧ ((D.main q Dec.DONE0 = 1 ∧ v = [D.main q Dec.KEY, 0, D.main q Dec.WCN]) ∨
    (D.main q Dec.DONE1 = 1 ∧ v = [D.main q Dec.KEY, 1, D.main q Dec.WC]) ∨
    (D.main q Dec.HC = 1 ∧ v = [D.main q Dec.KEY, 1, 0]))

def VerdRecv (D : Table) (v : List F) : Prop :=
  ∃ q, q < D.h ∧ D.main q Dec.SUB = 1 ∧ v = [D.main q Dec.KEY, D.main q Dec.ERR, D.main q Dec.WC]

/-- **The result on `decx`**: the subject's row sends its root and counter;
    the CPU's jet row receives them. -/
def ResSent (D : Table) (v : List F) : Prop :=
  ∃ q, q < D.h ∧ ((D.main q Dec.SUB = 1 ∧ v = [D.main q Dec.KEY, D.main q Dec.KEY + ofN 12 * D.main q Dec.ERR,
      D.main q Dec.KEY + ofN 12 + D.main q Dec.WC + ofN 3 * D.main q Dec.ERR]) ∨
    (D.main q Dec.ASUB = 1 ∧ v = [D.main q Dec.KEY, D.main q Dec.KEY, D.main q Dec.KEY + ofN 3]))

def ResRecv (C : Table) (v : List F) : Prop :=
  ∃ r, r < C.h ∧ C.main r DECSEL = 1 ∧ v = [C.main r CTR, C.main r DROOT, C.main r DCTR]

theorem cpuBusI_mem : ∀ I ∈ cpuBusI, I ∈ cpuIntersD := by
  intro I hI
  rw [cpuIntersD_eq]
  simp only [cpuBusI, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl <;> simp

theorem neg_ne_one {x : F} (hx : x = 0 ∨ x = 1) : -x ≠ 1 := by rcases hx with rfl | rfl <;> decide
theorem bit_ne_neg {x : F} (hx : x = 0 ∨ x = 1) : x ≠ -1 := by rcases hx with rfl | rfl <;> decide
theorem neg_eq_neg_one {x : F} (hx : x = 0 ∨ x = 1) (h : -x = -1) : x = 1 := by
  rcases hx with rfl | rfl
  · exact absurd h (by decide)
  · rfl

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

theorem CompDOK.cpu_dsel {r : Nat} (hr : r < C.h) : C.main r DECSEL = 0 ∨ C.main r DECSEL = 1 :=
  bit_of (dec_bitD h.cpu hr)

/-- The DEC side of a hit, as a DEC message. -/
theorem CompDOK.decHit {B : String} {v : List F} {s : F} {q : Nat} (hq : q < D.h) {I : Inter}
    (hI : I ∈ Dec.busI) (hb : I.bus = B) (hf : I.fields.map (fun e => e.eval (D.env q)) = v)
    (hc : I.count.eval (D.env q) = s) :
    ∃ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, ∃ r, r < p.2.h ∧
      ∃ I ∈ p.1.inters, I.bus = B ∧ I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = s :=
  ⟨(decAirB, D), by simp [compDTables], q, hq, I, decI_mem (.inl hI), hb, hf, hc⟩

theorem CompDOK.cpuHit {B : String} {v : List F} {s : F} {r : Nat} (hr : r < C.h) {I : Inter}
    (hI : I ∈ cpuBusI) (hb : I.bus = B) (hf : I.fields.map (fun e => e.eval (C.env r)) = v)
    (hc : I.count.eval (C.env r) = s) :
    ∃ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, ∃ r, r < p.2.h ∧
      ∃ I ∈ p.1.inters, I.bus = B ∧ I.fields.map (fun e => e.eval (p.2.env r)) = v ∧ I.count.eval (p.2.env r) = s :=
  ⟨(cpuAirDec hd0 stk0 ctr0 n nilA J, C), by simp [compDTables], r, hr, I, cpuBusI_mem I hI, hb, hf, hc⟩

/-- **A need is received.** -/
theorem CompDOK.need_recv {v : List F} (hs : NeedSent C D v) : NeedRecv D v := by
  have hit : ∃ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, ∃ r, r < p.2.h ∧
      ∃ I ∈ p.1.inters, I.bus = "decn" ∧ I.fields.map (fun e => e.eval (p.2.env r)) = v ∧
        I.count.eval (p.2.env r) = 1 := by
    rcases hs with ⟨r, hr, hd, rfl⟩ | ⟨q, hq, hk, rfl | rfl⟩
    · have cv := col_eval hr
      exact h.cpuHit hr (I := ⟨"decn", 1, sDec, [col CTR, fld 2, c 0]⟩) (by simp [cpuBusI]) rfl
        (by simp [fld, cv]; rfl) (by show (col DECSEL).eval _ = 1; rw [cv, hd])
    · have cv := col_eval hq
      exact h.decHit hq (I := ⟨"decn", 1, col Dec.KCELL, [col Dec.KEY, Dec.f2 21, .sub (c 2) (col Dec.H0)]⟩)
        (by simp [Dec.busI]) rfl (by simp [Dec.f2, cv, E.eval, c]) (by rw [cv, hk])
    · have cv := col_eval hq
      exact h.decHit hq (I := ⟨"decn", 1, col Dec.KCELL, [col Dec.KEY, Dec.f2 23, c 2]⟩)
        (by simp [Dec.busI]) rfl (by simp [Dec.f2, cv, E.eval, c]) (by rw [cv, hk])
  obtain hm := bus_match h.bal h.hts (h.signed (.inl rfl)) hit
  rcases h.hit_split (.inl rfl) hm with ⟨r, hr, I, hI, hb, hf, hc⟩ | ⟨q, hq, I, hI, hb, hf, hc⟩
  · simp only [cpuBusI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · exact absurd (show C.main r DECSEL = -1 by rw [← col_eval hr]; exact hc) (bit_ne_neg (h.cpu_dsel hr))
    · exact absurd hb (by decide)
  · have cv := col_eval hq
    obtain ⟨dk, hk⟩ := dkind_of (decRowF_of h.dec hq)
    simp only [Dec.busI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [E.eval, cv] at hc
      exact ⟨q, hq, neg_eq_neg_one (sum_bit_of_kind hk) hc, by rw [← hf]; simp [cv]⟩
    all_goals first
      | exact absurd hb (by decide)
      | (simp only [E.eval, cv] at hc
         exact absurd hc (bit_ne_neg (h.dbit hq _ (by simp))))

/-- **A need received was sent.** -/
theorem CompDOK.need_sent {v : List F} (hr : NeedRecv D v) : NeedSent C D v := by
  obtain ⟨q, hq, hk, rfl⟩ := hr
  have cv := col_eval hq
  have hit := h.decHit hq (I := ⟨"decn", 1, .neg (.add (col Dec.KCELL) (col Dec.KATOM)), [col Dec.KEY, col Dec.PC,
      col Dec.RO]⟩) (B := "decn") (s := -1) (v := [D.main q Dec.KEY, D.main q Dec.PC, D.main q Dec.RO]) (by simp [Dec.busI]) rfl (by simp [cv]) (by simp only [E.eval, cv, hk])
  obtain hm := bus_match' h.bal h.hts (h.signed (.inl rfl)) hit
  rcases h.hit_split (.inl rfl) hm with ⟨r, hr, I, hI, hb, hf, hc⟩ | ⟨q', hq', I, hI, hb, hf, hc⟩
  · simp only [cpuBusI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · have cv' := col_eval hr
      refine .inl ⟨r, hr, by rw [← cv']; exact hc, ?_⟩
      rw [← hf]; simp [fld, cv']; rfl
    · exact absurd hb (by decide)
  · have cv' := col_eval hq'
    obtain ⟨dk, hk'⟩ := dkind_of (decRowF_of h.dec hq')
    simp only [Dec.busI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [E.eval, cv'] at hc
      exact absurd hc (neg_ne_one (sum_bit_of_kind hk'))
    · simp only [cv'] at hc
      exact .inr ⟨q', hq', hc, .inl (by rw [← hf]; simp [Dec.f2, cv', E.eval, c])⟩
    · simp only [cv'] at hc
      exact .inr ⟨q', hq', hc, .inr (by rw [← hf]; simp [Dec.f2, cv', E.eval, c])⟩
    all_goals exact absurd hb (by decide)


/-- **A chain's step is received.** -/
theorem CompDOK.chain_recv {v : List F} (hs : ChainSent D v) : ChainRecv D v := by
  have hit : ∃ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, ∃ r, r < p.2.h ∧
      ∃ I ∈ p.1.inters, I.bus = "decb" ∧ I.fields.map (fun e => e.eval (p.2.env r)) = v ∧
        I.count.eval (p.2.env r) = 1 := by
    rcases hs with ⟨q, hq, hk, rfl⟩ | ⟨q, hq, hk, rfl⟩
    · have cv := col_eval hq
      exact h.decHit hq (I := ⟨"decb", 1, col Dec.KATOM, [col Dec.KEY, Dec.f2 22, .sub one (col Dec.H1), c 0,
        col Dec.H1, c 0]⟩) (by simp [Dec.busI]) rfl (by simp [Dec.f2, cv, E.eval, c, one, ofN_one, ofN_zero]) (by rw [cv, hk])
    · have cv := col_eval hq
      exact h.decHit hq (I := ⟨"decb", 1, col Dec.CSEND, [col Dec.KEY, Dec.f2 14, col Dec.MODE,
        .add (col Dec.LVL) one, col Dec.NBW, col Dec.WCN]⟩) (by simp [Dec.busI]) rfl
        (by simp [Dec.f2, cv, E.eval, c, one, ofN_one, ofN_zero]) (by rw [cv, hk])
  obtain hm := bus_match h.bal h.hts (h.signed (.inr (.inl rfl))) hit
  rcases h.hit_split (.inr (.inl rfl)) hm with ⟨r, hr, I, hI, hb, hf, hc⟩ | ⟨q, hq, I, hI, hb, hf, hc⟩
  · simp only [cpuBusI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl <;> exact absurd hb (by decide)
  · have cv := col_eval hq
    simp only [Dec.busI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd hb (by decide)
      | (simp only [E.eval, cv] at hc
         exact ⟨q, hq, .inl (neg_eq_neg_one (h.dbit hq _ (by simp)) hc), by rw [← hf]; simp [cv]⟩)
      | (simp only [E.eval, cv] at hc
         exact ⟨q, hq, .inr (neg_eq_neg_one (h.dbit hq _ (by simp)) hc), by rw [← hf]; simp [cv]⟩)
      | (simp only [E.eval, cv] at hc
         exact absurd hc (bit_ne_neg (h.dbit hq _ (by simp))))

/-- **A chain's step received was sent.** -/
theorem CompDOK.chain_sent {v : List F} (hr : ChainRecv D v) : ChainSent D v := by
  obtain ⟨q, hq, hk, rfl⟩ := hr
  have cv := col_eval hq
  have hit : ∃ p ∈ compDTables hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D, ∃ r, r < p.2.h ∧
      ∃ I ∈ p.1.inters, I.bus = "decb" ∧ I.fields.map (fun e => e.eval (p.2.env r)) =
        [D.main q Dec.KEY, D.main q Dec.PC, D.main q Dec.MODE, D.main q Dec.LVL, D.main q Dec.BW, D.main q Dec.WC] ∧
        I.count.eval (p.2.env r) = -1 := by
    rcases hk with hk | hk
    · exact h.decHit hq (I := ⟨"decb", 1, .neg (col Dec.KCONS), [col Dec.KEY, col Dec.PC, col Dec.MODE, col Dec.LVL,
        col Dec.BW, col Dec.WC]⟩) (by simp [Dec.busI]) rfl (by simp [cv]) (by simp only [E.eval, cv, hk])
    · exact h.decHit hq (I := ⟨"decb", 1, .neg (col Dec.KNIL), [col Dec.KEY, col Dec.PC, col Dec.MODE, col Dec.LVL,
        col Dec.BW, col Dec.WC]⟩) (by simp [Dec.busI]) rfl (by simp [cv]) (by simp only [E.eval, cv, hk])
  obtain hm := bus_match' h.bal h.hts (h.signed (.inr (.inl rfl))) hit
  rcases h.hit_split (.inr (.inl rfl)) hm with ⟨r, hr, I, hI, hb, hf, hc⟩ | ⟨q', hq', I, hI, hb, hf, hc⟩
  · simp only [cpuBusI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl <;> exact absurd hb (by decide)
  · have cv' := col_eval hq'
    simp only [Dec.busI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd hb (by decide)
      | (simp only [E.eval, cv'] at hc
         exact absurd hc (neg_ne_one (h.dbit hq' _ (by simp))))
      | (simp only [cv'] at hc
         exact .inl ⟨q', hq', hc, by rw [← hf]; simp [Dec.f2, cv', E.eval, c, one, ofN_one, ofN_zero]⟩)
      | (simp only [cv'] at hc
         exact .inr ⟨q', hq', hc, by rw [← hf]; simp [Dec.f2, cv', E.eval, c, one, ofN_one, ofN_zero]⟩)

/-- **The verdict received was sent.** -/
theorem CompDOK.verd_sent {v : List F} (hr : VerdRecv D v) : VerdSent D v := by
  obtain ⟨q, hq, hk, rfl⟩ := hr
  have cv := col_eval hq
  have hit := h.decHit hq (I := ⟨"decd", 1, .neg (col Dec.SUB), [col Dec.KEY, col Dec.ERR, col Dec.WC]⟩)
    (B := "decd") (s := -1) (v := [D.main q Dec.KEY, D.main q Dec.ERR, D.main q Dec.WC])
    (by simp [Dec.busI]) rfl (by simp [cv]) (by simp only [E.eval, cv, hk])
  obtain hm := bus_match' h.bal h.hts (h.signed (.inr (.inr (.inl rfl)))) hit
  rcases h.hit_split (.inr (.inr (.inl rfl))) hm with ⟨r, hr, I, hI, hb, hf, hc⟩ | ⟨q', hq', I, hI, hb, hf, hc⟩
  · simp only [cpuBusI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl <;> exact absurd hb (by decide)
  · have cv' := col_eval hq'
    simp only [Dec.busI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd hb (by decide)
      | (simp only [E.eval, cv'] at hc
         exact absurd hc (neg_ne_one (h.dbit hq' _ (by simp))))
      | (simp only [cv'] at hc
         exact ⟨q', hq', .inl ⟨hc, by rw [← hf]; simp [cv', E.eval, c, ofN_one, ofN_zero]⟩⟩)
      | (simp only [cv'] at hc
         exact ⟨q', hq', .inr (.inl ⟨hc, by rw [← hf]; simp [cv', E.eval, c, ofN_one, ofN_zero]⟩)⟩)
      | (simp only [cv'] at hc
         exact ⟨q', hq', .inr (.inr ⟨hc, by rw [← hf]; simp [cv', E.eval, c, ofN_one, ofN_zero]⟩)⟩)

/-- **The result the CPU receives was sent** by a subject's row. -/
theorem CompDOK.res_sent {v : List F} (hr : ResRecv C v) : ResSent D v := by
  obtain ⟨r, hr, hd, rfl⟩ := hr
  have cv := col_eval hr
  have hit := h.cpuHit hr (I := ⟨"decx", 1, .neg sDec, [col CTR, col DROOT, col DCTR]⟩)
    (B := "decx") (s := -1) (v := [C.main r CTR, C.main r DROOT, C.main r DCTR])
    (by simp [cpuBusI]) rfl (by simp [cv]) (by simp only [sDec, E.eval, cv, hd])
  obtain hm := bus_match' h.bal h.hts (h.signed (.inr (.inr (.inr rfl)))) hit
  rcases h.hit_split (.inr (.inr (.inr rfl))) hm with ⟨r', hr', I, hI, hb, hf, hc⟩ | ⟨q', hq', I, hI, hb, hf, hc⟩
  · simp only [cpuBusI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · exact absurd hb (by decide)
    · simp only [sDec, E.eval, col_eval hr'] at hc
      exact absurd hc (neg_ne_one (h.cpu_dsel hr'))
  · have cv' := col_eval hq'
    simp only [Dec.busI, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd hb (by decide)
      | (simp only [cv'] at hc
         exact ⟨q', hq', .inl ⟨hc, by rw [← hf]; simp [cv', E.eval, c, ofN_one, ofN_zero]⟩⟩)
      | (simp only [cv'] at hc
         exact ⟨q', hq', .inr ⟨hc, by rw [← hf]; simp [cv', E.eval, c, ofN_one, ofN_zero]⟩⟩)

end

end Circuit
