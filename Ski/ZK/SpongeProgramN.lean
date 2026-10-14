import Ski.ZK.SpongeProgram

/-!
# Challenges squeezed from the permutation at many positions

`SpongeProgram` trades one squeezed answer for an independent value.  The
Sudoku composites interleave `n` proofs that share the fourth table, so
here the answers at the `n` proofs' squeeze positions are traded at once.

- **The exchange.** Over the permutation tables, `K^K` times those where
  `f` holds at the context, `P` and `P`'s answers at distinct positions
  read off the context is at most the pairs `(P, H4)` where `f` holds at
  the context, `P` with those answers exchanged for `H4`'s (`progL`), and
  `H4`'s answers; plus `K^(K-1)` times the exchanges that change the
  context or a later position's answer (`badS`, `squeeze_tableN`).  The
  proof exchanges one position at a time by `squeeze_swapG`; positions
  that coincide are taken once (`dedupL`).
- **The exchanges' cost.** When exchanging values outside a set `S` leaves
  the context, a position costs at most `|S| + n` values, or `K` when its
  answer lies in `S` (`badS_le`).  With the context `n` runs of `k`
  queries, `S` is their answers.
- **Runs that share positions.** The runs read one after another form one
  adaptive run (`nxtCat`, `runAdp_nxtC`).  Runs may share positions at
  equal times, as proofs sharing a prefix do.  Two runs at one position at
  different times give two answers at distinct positions with equal `κ`,
  or an answer with a first position's `κ` (`shift_colRV`).  A squeeze
  position sits at time `k`, after every query, so a squeezed answer some
  run has seen is such a collision (`hit_colRV`), on at most
  `(0 + ⋯ + (nk-1) + nk n) F / (K - nk)` of the tables (`colRV_countP`,
  `badS_runs_countP`).
- **The composite.** A bound over `P`, a shared `H4` and the other tables,
  every distinguisher, the real view reading the `n` challenges from `H4`
  through a lookup at the squeeze positions (`getAt`) and depending on `P`
  otherwise only through the runs, and any simulator programming `H4`,
  gives the bound with the challenges read from `P`; the simulated
  distinguisher sees `P` with its answers at the positions `pos` reads off
  `P` and the simulated view exchanged for the programmed table's
  (`zk_squeezeN`).
  Per table the error is `n (nk + n) / K + n (0 + ⋯ + (nk-1) + nk n) /
  (Q (1 - nk/K))`, `Q = K / F` the capacity's tail.  `zk_squeezeN_sat08`
  meets every hypothesis at 0.8's duplex, `n` proofs with their own first
  positions and blocks.

Limits.  Every run makes exactly `k > 0` queries before its squeeze, and
the squeezes are the transcript's last uses of the permutation.  For
`nk ≥ K` both sides vanish and the bound says nothing.  Not
shown: `zk_squeezeN` applied to `sud_interleaveLG`, which needs `H4` kept
apart from the other tables, the fourth challenge read at a full state
through `getAt`, and the sponge files' chains as runs; the first three
challenges squeezed from the permutation as well.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-! ### Exchanging the answers at many positions -/

/-- The permutation `P` with its answer at each position of `ps` exchanged
    for the table `H4`'s answer there, the last position first. -/
def progL (K : Nat) : List Nat → Nat → Nat → Nat
  | [], _, P => P
  | p :: rest, H4, P => vswap K (rget K p (progL K rest H4 P)) (rget K p H4) (progL K rest H4 P)

theorem progL_nil (K H4 P : Nat) : progL K [] H4 P = P := rfl

/-- `progL` reads `H4` only at the positions of `ps`. -/
theorem progL_rset {K p c : Nat} (hK : 0 < K) (hc : c < K) (H4 P : Nat) :
    ∀ ps : List Nat, p ∉ ps → progL K ps (rset K p H4 c) P = progL K ps H4 P
  | [], _ => rfl
  | q :: rest, h => by
    have hq : q ≠ p := fun e => h (e ▸ List.mem_cons_self)
    have hr : p ∉ rest := fun e => h (List.mem_cons_of_mem _ e)
    show vswap K (rget K q (progL K rest (rset K p H4 c) P)) (rget K q (rset K p H4 c)) (progL K rest (rset K p H4 c) P) =
      vswap K (rget K q (progL K rest H4 P)) (rget K q H4) (progL K rest H4 P)
    rw [progL_rset hK hc H4 P rest hr, rget_rset_ne hK hq hc]

theorem map_rset {K p c : Nat} (hK : 0 < K) (hc : c < K) (H4 : Nat) (ps : List Nat) (h : p ∉ ps) :
    ps.map (fun v => rget K v (rset K p H4 c)) = ps.map (fun v => rget K v H4) :=
  List.map_congr_left (fun _ hv => rget_rset_ne hK (fun e => h (e ▸ hv)) hc)

/-- The exchanges that change the context or the later positions' answers,
    position by position: at `p` followed by `rest`, the values `u` whose
    exchange with `P`'s answer at `p` changes `ctx P` or `P`'s answers at
    `rest`. -/
def badS {α : Type} [DecidableEq α] (K : Nat) (ctx : Nat → α) (P : Nat) : List Nat → Nat
  | [] => 0
  | p :: rest => sumTo K (fun u => indB (!decide ((ctx (vswap K u (rget K p P) P),
      rest.map (fun v => rget K v (vswap K u (rget K p P) P))) = (ctx P, rest.map (fun v => rget K v P))))) +
    badS K ctx P rest

/-- **Squeezed answers at many positions traded for a table.**  The
    positions `ps (ctx P)`, distinct and below `K`, are read off the
    context.  `K^K` times the permutation tables where `f` holds at the
    context, the table and its answers at the positions is at most the
    pairs `(P, H4)` where `f` holds at the context, `P` with those answers
    exchanged for `H4`'s (`progL`), and `H4`'s answers there; plus
    `K^(K-1)` times the exchanges that change the context or a later
    position's answer (`badS`). -/
theorem squeeze_tableN {α : Type} [DecidableEq α] {K : Nat} (hK : 0 < K) (ctx : Nat → α) :
    ∀ (m : Nat) (ps : α → List Nat) (f : α → Nat → List Nat → Bool),
    (∀ c, (ps c).Nodup) → (∀ c, ∀ v ∈ ps c, v < K) → (∀ P, (ps (ctx P)).length ≤ m) →
    K ^ K * sumTo (K ^ K) (fun P => indB (permB K P && f (ctx P) P ((ps (ctx P)).map (fun v => rget K v P)))) ≤
      sumTo (K ^ K) (fun P => sumTo (K ^ K) (fun H4 =>
        indB (permB K P && f (ctx P) (progL K (ps (ctx P)) H4 P) ((ps (ctx P)).map (fun v => rget K v H4))))) +
      K ^ (K - 1) * sumTo (K ^ K) (fun P => indB (permB K P) * badS K ctx P (ps (ctx P)))
  | 0, ps, f, _, _, hl => by
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_add_right _ _)
    rw [sumTo_mul]
    refine sumTo_congr _ (fun P _ => ?_)
    have e : ps (ctx P) = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (hl P))
    simp only [e, List.map_nil, progL_nil, sumTo_const]
  | m + 1, ps, f, hnd, hlt, hl => by
    have hKK : K ^ K = K * K ^ (K - 1) := by
      calc K ^ K = K ^ (K - 1 + 1) := by rw [Nat.sub_add_cancel hK]
        _ = K * K ^ (K - 1) := Nat.pow_succ'
    -- the tables with no position, and the others
    let RE := sumTo (K ^ K) (fun P => indB (permB K P &&
      ((ps (ctx P)).isEmpty && f (ctx P) P ((ps (ctx P)).map (fun v => rget K v P)))))
    let RN := sumTo (K ^ K) (fun P => indB (permB K P &&
      (!(ps (ctx P)).isEmpty && f (ctx P) P ((ps (ctx P)).map (fun v => rget K v P)))))
    let IE := sumTo (K ^ K) (fun P => sumTo (K ^ K) (fun H4 => indB (permB K P &&
      ((ps (ctx P)).isEmpty && f (ctx P) (progL K (ps (ctx P)) H4 P) ((ps (ctx P)).map (fun v => rget K v H4))))))
    let IN := sumTo (K ^ K) (fun P => sumTo (K ^ K) (fun H4 => indB (permB K P &&
      (!(ps (ctx P)).isEmpty && f (ctx P) (progL K (ps (ctx P)) H4 P) ((ps (ctx P)).map (fun v => rget K v H4))))))
    have split : ∀ (b e x : Bool), indB (b && x) = indB (b && (e && x)) + indB (b && (!e && x)) := by
      intro b e x; cases b <;> cases e <;> cases x <;> rfl
    have hR : sumTo (K ^ K) (fun P => indB (permB K P && f (ctx P) P ((ps (ctx P)).map (fun v => rget K v P)))) =
        RE + RN := by
      rw [← sumTo_add]; exact sumTo_congr _ (fun P _ => split _ _ _)
    have hI : sumTo (K ^ K) (fun P => sumTo (K ^ K) (fun H4 =>
        indB (permB K P && f (ctx P) (progL K (ps (ctx P)) H4 P) ((ps (ctx P)).map (fun v => rget K v H4))))) =
        IE + IN := by
      rw [← sumTo_add]
      refine sumTo_congr _ (fun P _ => ?_)
      rw [← sumTo_add]; exact sumTo_congr _ (fun H4 _ => split _ _ _)
    -- with no position, nothing is exchanged
    have hE : K ^ K * RE = IE := by
      rw [sumTo_mul]
      refine sumTo_congr _ (fun P _ => ?_)
      cases hp : ps (ctx P) with
      | nil => simp only [List.map_nil, progL_nil, sumTo_const]
      | cons p rest =>
        rw [show (p :: rest).isEmpty = false from rfl]
        simp only [Bool.false_and, Bool.and_false, show indB false = 0 from rfl, Nat.mul_zero, sumTo_const]
    -- the first position exchanged by `squeeze_swapG`
    let ctx' : Nat → α × List Nat := fun P => (ctx P, ((ps (ctx P)).tail).map (fun v => rget K v P))
    let φ' : α × List Nat → Nat := fun c => (ps c.1).headD 0
    have hφ' : ∀ c, φ' c < K := fun c => by
      show (ps c.1).headD 0 < K
      cases hp : ps c.1 with
      | nil => exact hK
      | cons p _ => exact hlt c.1 p (hp ▸ List.mem_cons_self)
    let f' : α × List Nat → Nat → Nat → Bool := fun c Q a => !(ps c.1).isEmpty && f c.1 Q (a :: c.2)
    let g' : α × List Nat → Bool := fun c => !(ps c.1).isEmpty
    have sq := squeeze_swapG hK ctx' φ' hφ' f' g' (fun c Q a h => by
      simp only [f', Bool.and_eq_true] at h; exact h.1)
    have hRN : sumTo (K ^ K) (fun P => indB (permB K P && f' (ctx' P) P (rget K (φ' (ctx' P)) P))) = RN := by
      refine sumTo_congr _ (fun P _ => ?_)
      show indB (permB K P && (!(ps (ctx P)).isEmpty && f (ctx P) P
          (rget K ((ps (ctx P)).headD 0) P :: ((ps (ctx P)).tail).map (fun v => rget K v P)))) =
        indB (permB K P && (!(ps (ctx P)).isEmpty && f (ctx P) P ((ps (ctx P)).map (fun v => rget K v P))))
      cases ps (ctx P) <;> rfl
    -- the later positions, by induction, for each value `w`
    let fw : Nat → α → Nat → List Nat → Bool := fun w c Q as =>
      !(ps c).isEmpty && f c (vswap K (rget K ((ps c).headD 0) Q) w Q) (w :: as)
    have hnd' : ∀ c, ((ps c).tail).Nodup := fun c => by
      cases hp : ps c with
      | nil => exact List.nodup_nil
      | cons p rest => have := hnd c; rw [hp] at this; exact (List.nodup_cons.1 this).2
    have hlt' : ∀ c, ∀ v ∈ (ps c).tail, v < K := fun c v hv => by
      cases hp : ps c with
      | nil => rw [hp] at hv; exact absurd hv List.not_mem_nil
      | cons p rest => rw [hp] at hv; exact hlt c v (hp ▸ List.mem_cons_of_mem _ hv)
    have hl' : ∀ P, ((ps (ctx P)).tail).length ≤ m := fun P => by
      rw [List.length_tail]; have := hl P; omega
    have ih := fun w => squeeze_tableN hK ctx m (fun c => (ps c).tail) (fw w) hnd' hlt' hl'
    let Bt := K ^ (K - 1) * sumTo (K ^ K) (fun P => indB (permB K P) * badS K ctx P ((ps (ctx P)).tail))
    let B1 := sumTo (K ^ K) (fun H => sumTo K (fun u => indB (permB K H && g' (ctx' H) &&
      !decide (ctx' (vswap K u (rget K (φ' (ctx' H)) H) H) = ctx' H))))
    -- the values `w` summed: the first position read from `H4`
    have hIw : sumTo K (fun w => sumTo (K ^ K) (fun P => sumTo (K ^ K) (fun H4 => indB (permB K P &&
        fw w (ctx P) (progL K ((ps (ctx P)).tail) H4 P) (((ps (ctx P)).tail).map (fun v => rget K v H4)))))) =
        K * IN := by
      rw [sumTo_exch _ (K ^ K) K, sumTo_mul]
      refine sumTo_congr _ (fun P _ => ?_)
      rw [sumTo_exch _ (K ^ K) K]
      show sumTo (K ^ K) (fun H4 => sumTo K (fun w => indB (permB K P && (!(ps (ctx P)).isEmpty &&
          f (ctx P) (vswap K (rget K ((ps (ctx P)).headD 0) (progL K ((ps (ctx P)).tail) H4 P)) w
            (progL K ((ps (ctx P)).tail) H4 P)) (w :: ((ps (ctx P)).tail).map (fun v => rget K v H4)))))) =
        K * sumTo (K ^ K) (fun H4 => indB (permB K P && (!(ps (ctx P)).isEmpty &&
          f (ctx P) (progL K (ps (ctx P)) H4 P) ((ps (ctx P)).map (fun v => rget K v H4)))))
      cases hp : ps (ctx P) with
      | nil =>
        simp only [show ([] : List Nat).isEmpty = true from rfl, Bool.not_true, Bool.false_and,
          Bool.and_false, show indB false = 0 from rfl, sumTo_const, Nat.mul_zero]
      | cons p rest =>
        have hpr : p ∉ rest := by have := hnd (ctx P); rw [hp] at this; exact (List.nodup_cons.1 this).1
        have hpK : p < K := hlt (ctx P) p (hp ▸ List.mem_cons_self)
        let F := fun (H4 c : Nat) => indB (permB K P && (!(p :: rest).isEmpty &&
          f (ctx P) (vswap K (rget K p (progL K rest H4 P)) c (progL K rest H4 P)) (c :: rest.map (fun v => rget K v H4))))
        have e1 : sumTo (K ^ K) (fun H4 => sumTo K (fun w => F H4 w)) =
            sumTo (K ^ K) (fun H4 => sumTo K (fun c => F (rset K p H4 c) c)) := by
          refine sumTo_congr _ (fun H4 _ => sumTo_congr _ (fun c hc => ?_))
          show F H4 c = indB (permB K P && (!(p :: rest).isEmpty &&
            f (ctx P) (vswap K (rget K p (progL K rest (rset K p H4 c) P)) c (progL K rest (rset K p H4 c) P))
              (c :: rest.map (fun v => rget K v (rset K p H4 c)))))
          rw [progL_rset hK hc H4 P rest hpr, map_rset hK hc H4 rest hpr]
        refine Eq.trans e1 (Eq.trans (oracle_reprog_get hK hpK F) ?_)
        rfl
    -- the exchanges counted position by position
    have hB : Bt + K ^ (K - 1) * B1 ≤ K ^ (K - 1) * sumTo (K ^ K) (fun P => indB (permB K P) * badS K ctx P (ps (ctx P))) := by
      rw [← Nat.mul_add, ← sumTo_add]
      refine Nat.mul_le_mul_left _ (sumTo_mono _ (fun P _ => ?_))
      show indB (permB K P) * badS K ctx P ((ps (ctx P)).tail) + sumTo K (fun u => indB (permB K P &&
          !(ps (ctx P)).isEmpty && !decide ((ctx (vswap K u (rget K ((ps (ctx P)).headD 0) P) P),
            ((ps (ctx (vswap K u (rget K ((ps (ctx P)).headD 0) P) P))).tail).map
              (fun v => rget K v (vswap K u (rget K ((ps (ctx P)).headD 0) P) P))) =
            (ctx P, ((ps (ctx P)).tail).map (fun v => rget K v P))))) ≤
        indB (permB K P) * badS K ctx P (ps (ctx P))
      cases hp : ps (ctx P) with
      | nil =>
        refine Nat.le_of_eq (Eq.trans (congrArg (indB (permB K P) * badS K ctx P [] + ·)
          (Eq.trans (sumTo_congr _ (fun u _ => ?_)) (Eq.trans (sumTo_const 0 K) (Nat.mul_zero K)))) rfl)
        rw [show ([] : List Nat).isEmpty = true from rfl, Bool.not_true, Bool.and_false, Bool.false_and]; rfl
      | cons p rest =>
        show indB (permB K P) * badS K ctx P rest + _ ≤ indB (permB K P) * (_ + badS K ctx P rest)
        rw [Nat.mul_add, Nat.add_comm (indB (permB K P) * _)]
        refine Nat.add_le_add_right ?_ _
        rw [sumTo_mul]
        refine sumTo_mono _ (fun u _ => ?_)
        cases hP : permB K P
        · exact Nat.zero_le _
        · show indB (true && !(p :: rest).isEmpty && !decide ((ctx (vswap K u (rget K p P) P),
              ((ps (ctx (vswap K u (rget K p P) P))).tail).map (fun v => rget K v (vswap K u (rget K p P) P))) =
              (ctx P, rest.map (fun v => rget K v P)))) ≤
            indB true * indB (!decide ((ctx (vswap K u (rget K p P) P), rest.map (fun v => rget K v (vswap K u (rget K p P) P))) =
              (ctx P, rest.map (fun v => rget K v P))))
          rw [show indB true = 1 from rfl, Nat.one_mul]
          by_cases hc : ctx (vswap K u (rget K p P) P) = ctx P
          · rw [hc, hp]; exact Nat.le_refl _
          · have n1 : ¬ ((ctx (vswap K u (rget K p P) P), ((ps (ctx (vswap K u (rget K p P) P))).tail).map
                (fun v => rget K v (vswap K u (rget K p P) P))) = (ctx P, rest.map (fun v => rget K v P))) :=
              fun e => hc (Prod.mk.inj e).1
            have n2 : ¬ ((ctx (vswap K u (rget K p P) P), rest.map (fun v => rget K v (vswap K u (rget K p P) P))) =
                (ctx P, rest.map (fun v => rget K v P))) := fun e => hc (Prod.mk.inj e).1
            show indB (true && !(p :: rest).isEmpty && !decide _) ≤ indB (!decide _)
            rw [decide_eq_false n1, decide_eq_false n2]; exact Nat.le_refl _
    -- assembled
    rw [hR, hI, Nat.mul_add, hE, Nat.add_assoc]
    refine Nat.add_le_add_left ?_ _
    have step : K * (K ^ K * RN) ≤ K * (IN + Bt + K ^ (K - 1) * B1) := by
      calc K * (K ^ K * RN) = K ^ K * (K * RN) := Nat.mul_left_comm _ _ _
        _ ≤ K ^ K * (sumTo K (fun w => sumTo (K ^ K) (fun P => indB (permB K P &&
              f' (ctx' P) (vswap K (rget K (φ' (ctx' P)) P) w P) w))) + B1) := by
            rw [← hRN]; exact Nat.mul_le_mul_left _ sq
        _ = sumTo K (fun w => K ^ K * sumTo (K ^ K) (fun P => indB (permB K P &&
              fw w (ctx P) P (((ps (ctx P)).tail).map (fun v => rget K v P))))) + K ^ K * B1 := by
            rw [Nat.mul_add, sumTo_mul]
        _ ≤ sumTo K (fun w => sumTo (K ^ K) (fun P => sumTo (K ^ K) (fun H4 => indB (permB K P &&
              fw w (ctx P) (progL K ((ps (ctx P)).tail) H4 P) (((ps (ctx P)).tail).map (fun v => rget K v H4))))) +
              Bt) + K ^ K * B1 :=
            Nat.add_le_add_right (sumTo_mono _ (fun w _ => ih w)) _
        _ = K * (IN + Bt + K ^ (K - 1) * B1) := by
            rw [sumTo_add, hIw, sumTo_const, hKK, Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add]
    exact Nat.le_trans (Nat.le_of_mul_le_mul_left step hK) (by rw [Nat.add_assoc]; exact Nat.add_le_add_left hB _)

/-- **The exchanges that change the context, counted by a sensitive set**:
    when exchanging two values outside `S` leaves the context, each position
    of a distinct list `l` costs at most `A + |rest|` values `u`, `A ≥ |S|`,
    unless its answer lies in `S`, when it costs at most `K`. -/
theorem badS_le {α : Type} [DecidableEq α] {K A : Nat} (hK : 0 < K) (ctx : Nat → α) {P : Nat}
    (hP : permB K P = true) (S : List Nat) (hS : S.length ≤ A)
    (hinv : ∀ u a, u < K → a < K → u ∉ S → a ∉ S → ctx (vswap K u a P) = ctx P) :
    ∀ l : List Nat, l.Nodup → (∀ v ∈ l, v < K) →
      badS K ctx P l ≤ l.length * (A + l.length) + K * (l.length * indB (l.any (fun p => decide (rget K p P ∈ S))))
  | [], _, _ => Nat.zero_le _
  | p :: rest, hnd, hlt => by
    have hpr : p ∉ rest := (List.nodup_cons.1 hnd).1
    have hpK : p < K := hlt p List.mem_cons_self
    have ih := badS_le hK ctx hP S hS hinv rest (List.nodup_cons.1 hnd).2 (fun v hv => hlt v (List.mem_cons_of_mem _ hv))
    let a := rget K p P
    have ha : a < K := rget_lt hK _ _
    -- the head position's cost
    have head : sumTo K (fun u => indB (!decide ((ctx (vswap K u a P), rest.map (fun v => rget K v (vswap K u a P))) =
        (ctx P, rest.map (fun v => rget K v P))))) ≤ (A + rest.length) + K * indB (decide (a ∈ S)) := by
      by_cases haS : a ∈ S
      · rw [decide_eq_true haS, show indB true = 1 from rfl, Nat.mul_one]
        exact Nat.le_trans (Nat.le_trans (sumTo_mono _ (fun u _ => indB_le_one _))
          (Nat.le_of_eq (Eq.trans (sumTo_const 1 K) (Nat.mul_one K)))) (Nat.le_add_left _ _)
      · rw [decide_eq_false haS, show indB false = 0 from rfl, Nat.mul_zero, Nat.add_zero]
        have pt : ∀ u, u < K → indB (!decide ((ctx (vswap K u a P), rest.map (fun v => rget K v (vswap K u a P))) =
            (ctx P, rest.map (fun v => rget K v P)))) ≤ indB (decide (u ∈ S ++ rest.map (fun v => rget K v P))) := by
          intro u hu
          by_cases hm : u ∈ S ++ rest.map (fun v => rget K v P)
          · rw [decide_eq_true hm]; exact indB_le_one _
          · have huS : u ∉ S := fun h => hm (List.mem_append_left _ h)
            have hur : u ∉ rest.map (fun v => rget K v P) := fun h => hm (List.mem_append_right _ h)
            have e1 := hinv u a hu ha huS haS
            have e2 : rest.map (fun v => rget K v (vswap K u a P)) = rest.map (fun v => rget K v P) :=
              List.map_congr_left (fun v hv => by
                have hvK : v < K := hlt v (List.mem_cons_of_mem _ hv)
                rw [rget_vswap hK hu ha hvK]
                refine swapV_ne (fun e => hur (List.mem_map.2 ⟨v, hv, e⟩)) (fun e => ?_)
                exact hpr (permB_inj hP hvK hpK e ▸ hv))
            rw [e1, e2, decide_eq_true rfl]; exact Nat.zero_le _
        refine Nat.le_trans (sumTo_mono _ pt) (Nat.le_trans (count_mem K _) ?_)
        rw [List.length_append, List.length_map]
        exact Nat.add_le_add_right hS _
    show sumTo K _ + badS K ctx P rest ≤ (rest.length + 1) * (A + (rest.length + 1)) +
      K * ((rest.length + 1) * indB (decide (a ∈ S) || rest.any (fun p => decide (rget K p P ∈ S))))
    refine Nat.le_trans (Nat.add_le_add head ih) ?_
    have hor1 : indB (decide (a ∈ S)) ≤ indB (decide (a ∈ S) || rest.any (fun p => decide (rget K p P ∈ S))) := by
      cases decide (a ∈ S) <;> cases rest.any (fun p => decide (rget K p P ∈ S)) <;> decide
    have hor2 : indB (rest.any (fun p => decide (rget K p P ∈ S))) ≤
        indB (decide (a ∈ S) || rest.any (fun p => decide (rget K p P ∈ S))) := by
      cases decide (a ∈ S) <;> cases rest.any (fun p => decide (rget K p P ∈ S)) <;> decide
    have h1 : A + rest.length + rest.length * (A + rest.length) ≤ (rest.length + 1) * (A + (rest.length + 1)) := by
      rw [Nat.succ_mul, Nat.add_comm (rest.length * _)]
      exact Nat.add_le_add (Nat.add_le_add_left (Nat.le_succ _) _) (Nat.mul_le_mul_left _ (Nat.le_succ _))
    have h2 : K * indB (decide (a ∈ S)) + K * (rest.length * indB (rest.any (fun p => decide (rget K p P ∈ S)))) ≤
        K * ((rest.length + 1) * indB (decide (a ∈ S) || rest.any (fun p => decide (rget K p P ∈ S)))) := by
      rw [← Nat.mul_add, Nat.succ_mul, Nat.add_comm _ (indB _)]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add hor1 (Nat.mul_le_mul_left _ hor2))
    calc A + rest.length + K * indB (decide (a ∈ S)) +
          (rest.length * (A + rest.length) + K * (rest.length * indB (rest.any (fun p => decide (rget K p P ∈ S)))))
        = (A + rest.length + rest.length * (A + rest.length)) +
          (K * indB (decide (a ∈ S)) + K * (rest.length * indB (rest.any (fun p => decide (rget K p P ∈ S))))) := by
          ac_rfl
      _ ≤ _ := Nat.add_le_add h1 h2

/-! ### `n` sponge runs -/

/-- `l` with each value kept at its last occurrence. -/
def dedupL : List Nat → List Nat
  | [] => []
  | a :: l => if a ∈ l then dedupL l else a :: dedupL l

theorem mem_dedupL {v : Nat} : ∀ l, v ∈ dedupL l ↔ v ∈ l
  | [] => Iff.rfl
  | a :: l => by
    unfold dedupL
    by_cases h : a ∈ l
    · rw [if_pos h, mem_dedupL l]
      exact ⟨List.mem_cons_of_mem _, fun hv => (List.mem_cons.1 hv).elim (fun e => e ▸ h) id⟩
    · rw [if_neg h, List.mem_cons, List.mem_cons, mem_dedupL l]

theorem nodup_dedupL : ∀ l, (dedupL l).Nodup
  | [] => List.nodup_nil
  | a :: l => by
    unfold dedupL
    by_cases h : a ∈ l
    · rw [if_pos h]; exact nodup_dedupL l
    · rw [if_neg h]; exact List.nodup_cons.2 ⟨fun hm => h ((mem_dedupL l).1 hm), nodup_dedupL l⟩

theorem length_dedupL : ∀ l, (dedupL l).length ≤ l.length
  | [] => Nat.le_refl _
  | a :: l => by
    unfold dedupL
    by_cases h : a ∈ l
    · rw [if_pos h]; exact Nat.le_trans (length_dedupL l) (Nat.le_succ _)
    · rw [if_neg h]; exact Nat.succ_le_succ (length_dedupL l)

/-- The runs of `n` proofs, each `k` adaptive forward queries, the newest
    proof first. -/
def runsN (K : Nat) (nxtI : Nat → List Nat → Nat) (k : Nat) (P : Nat) : Nat → List (List (Nat × Nat))
  | 0 => []
  | n + 1 => runAdp K (nxtI n) P k :: runsN K nxtI k P n

theorem runsN_length (K : Nat) (nxtI : Nat → List Nat → Nat) (k P : Nat) : ∀ n, (runsN K nxtI k P n).length = n
  | 0 => rfl
  | n + 1 => by show (runsN K nxtI k P n).length + 1 = n + 1; rw [runsN_length K nxtI k P n]

/-- The squeeze positions of runs listed newest first, proof `i` the one
    below `i` others. -/
def sqOf (nxtI : Nat → List Nat → Nat) : List (List (Nat × Nat)) → List Nat
  | [] => []
  | r :: c => nxtI c.length (r.map Prod.snd) :: sqOf nxtI c

theorem sqOf_length (K : Nat) (nxtI : Nat → List Nat → Nat) (k P : Nat) :
    ∀ n, (sqOf nxtI (runsN K nxtI k P n)).length = n
  | 0 => rfl
  | n + 1 => by
    show (sqOf nxtI (runsN K nxtI k P n)).length + 1 = n + 1; rw [sqOf_length K nxtI k P n]

/-- Every answer of every run. -/
def allAnsOf : List (List (Nat × Nat)) → List Nat
  | [] => []
  | r :: c => r.map Prod.snd ++ allAnsOf c

/-- The position of a run at time `s`: its first at `0`, its squeeze at `k`. -/
def posT (K : Nat) (nxt : List Nat → Nat) (P s : Nat) : Nat := nxt ((runAdp K nxt P s).map Prod.snd)

theorem allAnsOf_length (K : Nat) (nxtI : Nat → List Nat → Nat) (k P : Nat) :
    ∀ n, (allAnsOf (runsN K nxtI k P n)).length = n * k
  | 0 => by show 0 = 0 * k; rw [Nat.zero_mul]
  | n + 1 => by
    show ((runAdp K (nxtI n) P k).map Prod.snd ++ allAnsOf (runsN K nxtI k P n)).length = (n + 1) * k
    rw [List.length_append, List.length_map, runAdp_length, allAnsOf_length K nxtI k P n, Nat.succ_mul, Nat.add_comm]

theorem mem_allAnsOf {K : Nat} {nxtI : Nat → List Nat → Nat} {k P u : Nat} :
    ∀ n, u ∈ allAnsOf (runsN K nxtI k P n) → ∃ i, i < n ∧ u ∈ (runAdp K (nxtI i) P k).map Prod.snd
  | 0, h => absurd h List.not_mem_nil
  | n + 1, h => by
    rcases List.mem_append.1 h with h | h
    · exact ⟨n, Nat.lt_succ_self _, h⟩
    · obtain ⟨i, hi, hu⟩ := mem_allAnsOf n h
      exact ⟨i, Nat.lt_succ_of_lt hi, hu⟩

theorem mem_sqOf {K : Nat} {nxtI : Nat → List Nat → Nat} {k P p : Nat} :
    ∀ n, p ∈ sqOf nxtI (runsN K nxtI k P n) → ∃ j, j < n ∧ p = posT K (nxtI j) P k
  | 0, h => absurd h List.not_mem_nil
  | n + 1, h => by
    rcases List.mem_cons.1 h with h | h
    · refine ⟨n, Nat.lt_succ_self _, ?_⟩
      rw [h, runsN_length]; rfl
    · obtain ⟨j, hj, e⟩ := mem_sqOf n h
      exact ⟨j, Nat.lt_succ_of_lt hj, e⟩

/-- **Exchanging two values no run has seen leaves every run.** -/
theorem runsN_vswap {K a b : Nat} (hK : 0 < K) (ha : a < K) (hb : b < K) (nxtI : Nat → List Nat → Nat)
    (hnx : ∀ i l, nxtI i l < K) (k P : Nat) :
    ∀ n, a ∉ allAnsOf (runsN K nxtI k P n) → b ∉ allAnsOf (runsN K nxtI k P n) →
      runsN K nxtI k (vswap K a b P) n = runsN K nxtI k P n
  | 0, _, _ => rfl
  | n + 1, hA, hB => by
    show runAdp K (nxtI n) (vswap K a b P) k :: runsN K nxtI k (vswap K a b P) n =
      runAdp K (nxtI n) P k :: runsN K nxtI k P n
    rw [runAdp_vswap hK ha hb (nxtI n) (hnx n) k P (fun h => hA (List.mem_append_left _ h))
        (fun h => hB (List.mem_append_left _ h)),
      runsN_vswap hK ha hb nxtI hnx k P n (fun h => hA (List.mem_append_right _ h))
        (fun h => hB (List.mem_append_right _ h))]

/-! ### The runs as one run -/

/-- The next position of the runs queried one after another, `k` queries
    each. -/
def nxtCat (k : Nat) (nxtI : Nat → List Nat → Nat) (l : List Nat) : Nat :=
  nxtI (l.length / k) (l.take (l.length % k))

theorem runAdp_mem_add {K : Nat} (nxt : List Nat → Nat) (P : Nat) {y : Nat × Nat} (m : Nat) :
    ∀ d, y ∈ runAdp K nxt P m → y ∈ runAdp K nxt P (m + d)
  | 0, h => h
  | d + 1, h => List.mem_cons_of_mem _ (runAdp_mem_add (K := K) nxt P m d h)

/-- **Proof `i`'s run is a segment of the one run.** -/
theorem runAdp_nxtC {K k : Nat} (hk : 0 < k) (nxtI : Nat → List Nat → Nat) (P i : Nat) :
    ∀ t, t ≤ k → runAdp K (nxtCat k nxtI) P (i * k + t) = runAdp K (nxtI i) P t ++ runAdp K (nxtCat k nxtI) P (i * k)
  | 0, _ => rfl
  | t + 1, ht => by
    have ih := runAdp_nxtC (K := K) hk nxtI P i t (Nat.le_of_succ_le ht)
    have htk : t < k := ht
    have hl : ((runAdp K (nxtCat k nxtI) P (i * k + t)).map Prod.snd).length = t + i * k := by
      rw [List.length_map, runAdp_length, Nat.add_comm]
    have hn : nxtCat k nxtI ((runAdp K (nxtCat k nxtI) P (i * k + t)).map Prod.snd) =
        nxtI i ((runAdp K (nxtI i) P t).map Prod.snd) := by
      show nxtI (((runAdp K (nxtCat k nxtI) P (i * k + t)).map Prod.snd).length / k)
        (((runAdp K (nxtCat k nxtI) P (i * k + t)).map Prod.snd).take
          (((runAdp K (nxtCat k nxtI) P (i * k + t)).map Prod.snd).length % k)) = _
      rw [hl, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt htk, Nat.zero_add, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt htk, ih, List.map_append]
      rw [List.take_left' (by rw [List.length_map, runAdp_length])]
    show (nxtCat k nxtI ((runAdp K (nxtCat k nxtI) P (i * k + t)).map Prod.snd),
        rget K (nxtCat k nxtI ((runAdp K (nxtCat k nxtI) P (i * k + t)).map Prod.snd)) P) ::
        runAdp K (nxtCat k nxtI) P (i * k + t) = _
    rw [hn, ih]; rfl

theorem mem_runAdp_nxtC {K k n : Nat} (hk : 0 < k) (nxtI : Nat → List Nat → Nat) (P : Nat) {i : Nat} (hi : i < n)
    {y : Nat × Nat} (hy : y ∈ runAdp K (nxtI i) P k) : y ∈ runAdp K (nxtCat k nxtI) P (n * k) := by
  have e := runAdp_nxtC (K := K) hk nxtI P i k (Nat.le_refl _)
  have h1 : y ∈ runAdp K (nxtCat k nxtI) P (i * k + k) := by rw [e]; exact List.mem_append_left _ hy
  have h2 : i * k + k + (n * k - (i * k + k)) = n * k := by
    have : i * k + k ≤ n * k := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    omega
  rw [← h2]; exact runAdp_mem_add _ P _ _ h1

/-! ### A squeeze position on another run's query is a collision -/

theorem mem_runAdp_posT {K : Nat} (nxt : List Nat → Nat) (P : Nat) :
    ∀ k, ∀ z ∈ runAdp K nxt P k, ∃ s, s < k ∧ z = (posT K nxt P s, rget K (posT K nxt P s) P)
  | 0, _, h => absurd h List.not_mem_nil
  | k + 1, z, h => by
    rcases List.mem_cons.1 h with e | e
    · exact ⟨k, Nat.lt_succ_self _, e⟩
    · obtain ⟨s, hs, e'⟩ := mem_runAdp_posT nxt P k z e
      exact ⟨s, Nat.lt_succ_of_lt hs, e'⟩

theorem posT_mem {K : Nat} (nxt : List Nat → Nat) (P : Nat) {s k : Nat} (hs : s < k) :
    (posT K nxt P s, rget K (posT K nxt P s) P) ∈ runAdp K nxt P k := by
  have h : (posT K nxt P s, rget K (posT K nxt P s) P) ∈ runAdp K nxt P (s + 1) := List.mem_cons_self
  have e : s + 1 + (k - (s + 1)) = k := by omega
  rw [← e]; exact runAdp_mem_add nxt P _ _ h

/-- The first positions of `n` proofs. -/
def firstsN (nxtI : Nat → List Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => nxtI n [] :: firstsN nxtI n

theorem firstsN_length (nxtI : Nat → List Nat → Nat) : ∀ n, (firstsN nxtI n).length = n
  | 0 => rfl
  | n + 1 => by show (firstsN nxtI n).length + 1 = n + 1; rw [firstsN_length nxtI n]

theorem mem_firstsN (nxtI : Nat → List Nat → Nat) {i : Nat} : ∀ n, i < n → nxtI i [] ∈ firstsN nxtI n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rcases Nat.lt_or_ge i n with hi | hi
    · exact List.mem_cons_of_mem _ (mem_firstsN nxtI n hi)
    · have e : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hi
      rw [e]; exact List.mem_cons_self

/-- **Two runs at one position at different times give a collision in the
    one run**: with each position after the first keeping `κ` of the answer
    before it, proof `i` at time `s` and proof `j` at a later time `t ≤ k`
    at the same position give two answers at distinct positions with equal
    `κ`, or an answer with a first position's `κ`. -/
theorem shift_colRV {K k n : Nat} (hk : 0 < k) (κ : Nat → Nat) (nxtI : Nat → List Nat → Nat)
    (hκ : ∀ i a l, κ (nxtI i (a :: l)) = κ a) (P : Nat) :
    ∀ s t i j, i < n → j < n → s < t → t ≤ k → posT K (nxtI i) P s = posT K (nxtI j) P t →
      colRV (fun a b => decide (κ a = κ b)) (firstsN nxtI n) (runAdp K (nxtCat k nxtI) P (n * k)) = true
  | s, 0, _, _, _, _, hst, _, _ => absurd hst (Nat.not_lt_zero _)
  | 0, t + 1, i, j, hi, hj, _, htk, e => by
    have hB := mem_runAdp_nxtC (K := K) hk nxtI P hj (posT_mem (nxtI j) P (k := k) htk)
    have hκe : κ (nxtI i []) = κ (rget K (posT K (nxtI j) P t) P) := by
      have := congrArg κ e
      rw [show posT K (nxtI i) P 0 = nxtI i [] from rfl] at this
      rw [this]; exact hκ j _ _
    unfold colRV
    rw [Bool.or_eq_true]
    refine Or.inr (List.any_eq_true.2 ⟨_, hB, List.any_eq_true.2 ⟨_, mem_firstsN nxtI n hi, decide_eq_true hκe⟩⟩)
  | s + 1, t + 1, i, j, hi, hj, hst, htk, e => by
    have hst' : s < t := Nat.lt_of_succ_lt_succ hst
    have hκe : κ (rget K (posT K (nxtI i) P s) P) = κ (rget K (posT K (nxtI j) P t) P) := by
      have h1 : κ (posT K (nxtI i) P (s + 1)) = κ (rget K (posT K (nxtI i) P s) P) := hκ i _ _
      have h2 : κ (posT K (nxtI j) P (t + 1)) = κ (rget K (posT K (nxtI j) P t) P) := hκ j _ _
      exact h1.symm.trans ((congrArg κ e).trans h2)
    by_cases hp : posT K (nxtI i) P s = posT K (nxtI j) P t
    · exact shift_colRV hk κ nxtI hκ P s t i j hi hj hst' (Nat.le_of_succ_le htk) hp
    · have hA := mem_runAdp_nxtC (K := K) hk nxtI P hi (posT_mem (nxtI i) P (k := k) (Nat.lt_trans hst' htk))
      have hB := mem_runAdp_nxtC (K := K) hk nxtI P hj (posT_mem (nxtI j) P (k := k) htk)
      unfold colRV
      rw [Bool.or_eq_true]
      exact Or.inl (colR_of_mem _ (rel_symm κ) _ _ _ hA hB hp (decide_eq_true hκe))

/-- **A squeezed answer some run has seen is a collision in the one run.** -/
theorem hit_colRV {K k n : Nat} (hk : 0 < k) (κ : Nat → Nat) (nxtI : Nat → List Nat → Nat) (hnx : ∀ i l, nxtI i l < K)
    (hκ : ∀ i a l, κ (nxtI i (a :: l)) = κ a) {P : Nat} (hP : permB K P = true)
    (h : (dedupL (sqOf nxtI (runsN K nxtI k P n))).any
      (fun p => decide (rget K p P ∈ allAnsOf (runsN K nxtI k P n))) = true) :
    colRV (fun a b => decide (κ a = κ b)) (firstsN nxtI n) (runAdp K (nxtCat k nxtI) P (n * k)) = true := by
  obtain ⟨p, hp, hpa⟩ := List.any_eq_true.1 h
  obtain ⟨j, hj, ep⟩ := mem_sqOf n ((mem_dedupL _).1 hp)
  obtain ⟨i, hi, hu⟩ := mem_allAnsOf n (of_decide_eq_true hpa)
  obtain ⟨z, hz, hz2⟩ := List.mem_map.1 hu
  obtain ⟨s, hs, ez⟩ := mem_runAdp_posT (K := K) (nxtI i) P k z hz
  have e : rget K (posT K (nxtI i) P s) P = rget K (posT K (nxtI j) P k) P := by
    rw [← ep, ← hz2, ez]
  have epos := permB_inj hP (hnx i _) (hnx j _) e
  exact shift_colRV hk κ nxtI hκ P s k i j hi hj hs (Nat.le_refl _) epos

/-- **The exchanges that change `n` runs**: with `k > 0` queries each, each
    position after the first keeping `κ` of the answer before it, `κ`'s
    fibres below `K` at most `F`, the exchanges `badS` counts over the
    proofs' distinct squeeze positions, times `K - nk`, are at most
    `(K - nk) n (nk + n)` per permutation table plus `K n` times the
    collision count `(0 + ⋯ + (nk-1) + nk n) F` per table. -/
theorem badS_runs_countP {K F k n : Nat} (hK : 0 < K) (hk : 0 < k) (κ : Nat → Nat)
    (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (nxtI : Nat → List Nat → Nat) (hnx : ∀ i l, nxtI i l < K) (hκ : ∀ i a l, κ (nxtI i (a :: l)) = κ a) :
    (K - n * k) * sumTo (K ^ K) (fun P => indB (permB K P) *
        badS K (fun P => runsN K nxtI k P n) P (dedupL (sqOf nxtI (runsN K nxtI k P n)))) ≤
      (K - n * k) * (n * (n * k + n)) * sumTo (K ^ K) (fun P => indB (permB K P)) +
      K * n * ((sumTo (n * k) (fun j => j) + n * k * n) * F * sumTo (K ^ K) (fun P => indB (permB K P))) := by
  let cl := fun a b => decide (κ a = κ b)
  have hcol := colRV_countP hK cl (rel_symm κ) (fib_rel κ hF) (firstsN nxtI n) (nxtCat k nxtI)
    (fun l => hnx _ _) (n * k)
  rw [firstsN_length] at hcol
  have pt : ∀ P, P < K ^ K → indB (permB K P) * badS K (fun P => runsN K nxtI k P n) P
      (dedupL (sqOf nxtI (runsN K nxtI k P n))) ≤
      n * (n * k + n) * indB (permB K P) +
        K * n * indB (permB K P && colRV cl (firstsN nxtI n) (runAdp K (nxtCat k nxtI) P (n * k))) := by
    intro P _
    cases hP : permB K P
    · exact Nat.le_trans (Nat.le_of_eq (Nat.zero_mul _)) (Nat.zero_le _)
    · rw [show indB true = 1 from rfl, Nat.one_mul, Nat.mul_one, Bool.true_and]
      let l := dedupL (sqOf nxtI (runsN K nxtI k P n))
      have hl : l.length ≤ n := by
        exact Nat.le_trans (length_dedupL _) (Nat.le_of_eq (sqOf_length K nxtI k P n))
      have hb := badS_le (A := n * k) hK (fun P => runsN K nxtI k P n) hP (allAnsOf (runsN K nxtI k P n))
        (Nat.le_of_eq (allAnsOf_length K nxtI k P n))
        (fun u a hu ha huS haS => runsN_vswap hK hu ha nxtI hnx k P n huS haS) l (nodup_dedupL _)
        (fun v hv => by
          obtain ⟨j, _, e⟩ := mem_sqOf n ((mem_dedupL _).1 hv)
          rw [e]; exact hnx _ _)
      refine Nat.le_trans hb (Nat.add_le_add ?_ ?_)
      · exact Nat.mul_le_mul hl (Nat.add_le_add_left hl _)
      · rw [Nat.mul_assoc]
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul hl ?_)
        cases ha : l.any (fun p => decide (rget K p P ∈ allAnsOf (runsN K nxtI k P n)))
        · exact Nat.zero_le _
        · rw [hit_colRV hk κ nxtI hnx hκ hP ha]; exact Nat.le_refl _
  refine Nat.le_trans (Nat.mul_le_mul_left _ (sumTo_mono _ pt)) ?_
  rw [sumTo_add, Nat.mul_add, ← sumTo_mul, ← sumTo_mul, ← Nat.mul_assoc]
  refine Nat.add_le_add_left ?_ _
  rw [Nat.mul_left_comm]
  exact Nat.mul_le_mul_left _ hcol

/-! ### The fourth challenges of `n` proofs squeezed from the permutation -/

/-- The answer `as` lists for the position `v` of `ps`, or `0`. -/
def getAt : List Nat → List Nat → Nat → Nat
  | p :: ps, a :: as, v => if v = p then a else getAt ps as v
  | _, _, _ => 0

theorem getAt_map (g : Nat → Nat) {v : Nat} : ∀ ps : List Nat, v ∈ ps → getAt ps (ps.map g) v = g v
  | [], h => absurd h List.not_mem_nil
  | p :: ps, h => by
    show (if v = p then g p else getAt ps (ps.map g) v) = g v
    by_cases e : v = p
    · rw [if_pos e, e]
    · rw [if_neg e]; exact getAt_map g ps ((List.mem_cons.1 h).resolve_left e)

/-- **The fourth challenges of `n` proofs squeezed from the permutation.**
    `zk_squeeze` at `n` proofs sharing `H4`, proof `i`'s run `k > 0` adaptive
    forward queries chosen by the other tables `H` and the draws `x`.  The
    real view reads the challenges through a lookup at the proofs' distinct
    squeeze positions (`getAt`), from `H4` in `hyp` and from `P` in the
    conclusion, and depends on `P` otherwise only through the runs.  The
    simulator of `hyp` is any: it programs the other tables and `H4`
    together (`pgJ`), knowing `P`, and may read the programmed tables.  In the conclusion the distinguisher sees `P` with its
    answers at the positions `pos` reads off `P` and the simulated view
    exchanged for the programmed table's (`progL`).  The error gains the
    exchanges and collisions of all `n` runs (`badS_runs_countP`). -/
theorem zk_squeezeN {T X C V : Type} {K F k n K4w ε : Nat} (hK : 0 < K) (hk : 0 < k) (κ : Nat → Nat)
    (hF : ∀ v, sumTo K (fun u => indB (decide (κ u = v))) ≤ F)
    (ST : (T → Nat) → Nat) (hST : Lin ST) (sm : (X → Nat) → Nat) (hsm : Lin sm) (SC : (C → Nat) → Nat)
    (nxtI : T → X → Nat → List Nat → Nat) (hnx : ∀ H x i l, nxtI H x i l < K)
    (hκ : ∀ H x i a l, κ (nxtI H x i (a :: l)) = κ a)
    (rv : List (List (Nat × Nat)) → T → X → (Nat → Nat) → V)
    (pgJ : Nat → T → Nat → C → X → T × Nat) (sv : Nat → T → Nat → C → X → V)
    (pos : Nat → T → V → List Nat)
    (hpr : ∀ P H x g, pos P H (rv (runsN K (nxtI H x) k P n) H x g) =
      dedupL (sqOf (nxtI H x) (runsN K (nxtI H x) k P n)))
    (hyp : ∀ D : Nat → Nat → T → V → Bool,
      K4w * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
        indB (D P H4 H (rv (runsN K (nxtI H x) k P n) H x
          (getAt (dedupL (sqOf (nxtI H x) (runsN K (nxtI H x) k P n)))
            ((dedupL (sqOf (nxtI H x) (runsN K (nxtI H x) k P n))).map (fun v => rget K v H4))))))))) ≤
      ST (fun H => SC (fun c => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
        indB (D P (pgJ P H H4 c x).2 (pgJ P H H4 c x).1 (sv P H H4 c x))))))) + ε)
    (E : Nat → T → V → Bool) :
    (K - n * k) * (K4w * (K ^ K * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P &&
        E P H (rv (runsN K (nxtI H x) k P n) H x
          (getAt (dedupL (sqOf (nxtI H x) (runsN K (nxtI H x) k P n)))
            ((dedupL (sqOf (nxtI H x) (runsN K (nxtI H x) k P n))).map (fun v => rget K v P)))))))))) ≤
      (K - n * k) * (ST (fun H => SC (fun c => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) *
        sumTo (K ^ K) (fun H4 => indB (E (progL K (pos P (pgJ P H H4 c x).1 (sv P H H4 c x)) (pgJ P H H4 c x).2 P)
          (pgJ P H H4 c x).1 (sv P H H4 c x))))))) + ε) +
      K4w * (K ^ (K - 1) * (ST (fun _ => sm (fun _ => 1)) *
        (((K - n * k) * (n * (n * k + n)) + K * n * ((sumTo (n * k) (fun j => j) + n * k * n) * F)) *
          sumTo (K ^ K) (fun P => indB (permB K P))))) := by
  let DE : Nat → Nat → T → V → Bool := fun P H4 H' v => E (progL K (pos P H' v) H4 P) H' v
  have h := hyp DE
  let ps := fun (H : T) (x : X) (c : List (List (Nat × Nat))) => dedupL (sqOf (nxtI H x) c)
  let real := fun (H : T) (x : X) => sumTo (K ^ K) (fun P => indB (permB K P &&
    E P H (rv (runsN K (nxtI H x) k P n) H x (getAt (ps H x (runsN K (nxtI H x) k P n))
      ((ps H x (runsN K (nxtI H x) k P n)).map (fun v => rget K v P))))))
  let R4 := fun (H : T) (x : X) => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
    indB (DE P H4 H (rv (runsN K (nxtI H x) k P n) H x (getAt (ps H x (runsN K (nxtI H x) k P n))
      ((ps H x (runsN K (nxtI H x) k P n)).map (fun v => rget K v H4)))))))
  let Bad := fun (H : T) (x : X) => K ^ (K - 1) * sumTo (K ^ K) (fun P => indB (permB K P) *
    badS K (fun P => runsN K (nxtI H x) k P n) P (ps H x (runsN K (nxtI H x) k P n)))
  let ErrN := ((K - n * k) * (n * (n * k + n)) + K * n * ((sumTo (n * k) (fun j => j) + n * k * n) * F)) *
    sumTo (K ^ K) (fun P => indB (permB K P))
  -- the table exchange at each `H` and `x`
  have htab : ∀ H x, K ^ K * real H x ≤ R4 H x + Bad H x := fun H x => by
    have t := squeeze_tableN hK (fun P => runsN K (nxtI H x) k P n) n (ps H x)
      (fun c T as => E T H (rv c H x (getAt (ps H x c) as))) (fun c => nodup_dedupL _)
      (fun c v hv => by
        show v < K
        have hv' := (mem_dedupL _).1 hv
        clear hv
        induction c with
        | nil => exact absurd hv' List.not_mem_nil
        | cons r c ih => rcases List.mem_cons.1 hv' with e | e
                         · rw [e]; exact hnx _ _ _ _
                         · exact ih e)
      (fun P => Nat.le_trans (length_dedupL _) (Nat.le_of_eq (sqOf_length K _ k P n)))
    refine Nat.le_trans t (Nat.add_le_add_right (Nat.le_of_eq ?_) _)
    refine sumTo_congr _ (fun P _ => ?_)
    rw [sumTo_mul]
    refine sumTo_congr _ (fun H4 _ => ?_)
    rw [← indB_and]
    show indB (permB K P && E (progL K (ps H x (runsN K (nxtI H x) k P n)) H4 P) H _) =
      indB (permB K P && E (progL K (pos P H (rv (runsN K (nxtI H x) k P n) H x _)) H4 P) H _)
    rw [hpr]
  -- the exchanges and collisions of the runs
  have hbad : ∀ H x, (K - n * k) * Bad H x ≤ K ^ (K - 1) * ErrN := fun H x => by
    have b := badS_runs_countP hK hk κ hF (nxtI H x) (hnx H x) (hκ H x) (n := n)
    show (K - n * k) * (K ^ (K - 1) * _) ≤ _
    rw [Nat.mul_left_comm]
    refine Nat.mul_le_mul_left _ (Nat.le_trans b (Nat.le_of_eq ?_))
    show _ = ((K - n * k) * (n * (n * k + n)) + K * n * ((sumTo (n * k) (fun j => j) + n * k * n) * F)) * _
    rw [Nat.add_mul _ (K * n * ((sumTo (n * k) (fun j => j) + n * k * n) * F)), Nat.mul_assoc (K * n)]
  have smm : ∀ {f g : X → Nat}, (∀ x, f x ≤ g x) → sm f ≤ sm g := fun h => sm_mono sm hsm h
  have stm : ∀ {f g : T → Nat}, (∀ H, f H ≤ g H) → ST f ≤ ST g := fun h => sm_mono ST hST h
  have e1 : (K - n * k) * (K4w * (K ^ K * ST (fun H => sm (fun x => real H x)))) =
      K4w * ST (fun H => sm (fun x => (K - n * k) * (K ^ K * real H x))) := by
    rw [Nat.mul_left_comm, ← smK ST hST, ← smK ST hST]
    refine congrArg (K4w * ·) (congrArg ST (funext fun H => ?_))
    rw [smK sm hsm, smK sm hsm]
  calc (K - n * k) * (K4w * (K ^ K * ST (fun H => sm (fun x => real H x))))
      = K4w * ST (fun H => sm (fun x => (K - n * k) * (K ^ K * real H x))) := e1
    _ ≤ K4w * ST (fun H => sm (fun x => (K - n * k) * R4 H x + K ^ (K - 1) * ErrN)) :=
        Nat.mul_le_mul_left _ (stm (fun H => smm (fun x => by
          refine Nat.le_trans (Nat.mul_le_mul_left _ (htab H x)) ?_
          rw [Nat.mul_add]; exact Nat.add_le_add_left (hbad H x) _)))
    _ = (K - n * k) * (K4w * ST (fun H => sm (fun x => R4 H x))) +
        K4w * (K ^ (K - 1) * (ST (fun _ => sm (fun _ => 1)) * ErrN)) := by
        have e2 : ∀ H, sm (fun x => (K - n * k) * R4 H x + K ^ (K - 1) * ErrN) =
            (K - n * k) * sm (fun x => R4 H x) + K ^ (K - 1) * ErrN * sm (fun _ => 1) := fun H => by
          rw [sm_add sm hsm, smK sm hsm, smC sm hsm]
        rw [congrArg ST (funext e2), sm_add ST hST, smK ST hST, smK ST hST, Nat.mul_add,
          Nat.mul_left_comm K4w (K - n * k), Nat.mul_assoc (K ^ (K - 1)), Nat.mul_comm ErrN]
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

/-- A count commuting with finite sums takes a weighted double sum out. -/
theorem lin_swap2 {Y : Type} (S : (Y → Nat) → Nat) (hS : Lin S) (N M : Nat) (a : Nat → Nat) (g : Nat → Nat → Y → Nat) :
    S (fun y => sumTo N (fun P => a P * sumTo M (fun Q => g P Q y))) =
      sumTo N (fun P => a P * sumTo M (fun Q => S (g P Q))) := by
  rw [hS N (fun P y => a P * sumTo M (fun Q => g P Q y))]
  refine sumTo_congr _ (fun P _ => ?_)
  rw [smK S hS, hS M (fun Q y => g P Q y)]

/-- **A composite's `ZKBT` gives `zk_squeezeN`'s hypothesis.**  The
    composite's tables are a permutation `P` and tables `join H H4`, counted
    by `ST` over `H` and uniformly over `H4`; its real view at
    `join H H4` is `RV P H x H4`, and its programming and simulated view at
    `join H H4` are `pgJ`'s and `SV`'s.  Then the bound holds with the counts
    in `zk_squeezeN`'s order, for every distinguisher reading `P`, `H4` and
    `H` apart (`split` undoes `join`). -/
theorem hypN_of_zkbT {T X C V TT : Type} {K K4w ε : Nat} (ST : (T → Nat) → Nat) (hST : Lin ST)
    (sm : (X → Nat) → Nat) (hsm : Lin sm) (SC : (C → Nat) → Nat) (hSC : Lin SC)
    (join : T → Nat → TT) (split : TT → T × Nat) (hsplit : ∀ H H4, split (join H H4) = (H, H4))
    (rvC : Nat × TT → X → V) (pgC : Nat × TT → C → X → Nat × TT) (svC : Nat × TT → C → X → V)
    (h : ZKBT (fun f : Nat × TT → Nat => sumTo (K ^ K) (fun P => indB (permB K P) *
      sumTo (K ^ K) (fun H4 => ST (fun H => f (P, join H H4))))) K4w sm SC rvC pgC svC ε)
    (RV : Nat → T → X → Nat → V) (pgJ : Nat → T → Nat → C → X → T × Nat) (SV : Nat → T → Nat → C → X → V)
    (hrv : ∀ P H H4 x, rvC (P, join H H4) x = RV P H x H4)
    (hpg : ∀ P H H4 c x, pgC (P, join H H4) c x = (P, join (pgJ P H H4 c x).1 (pgJ P H H4 c x).2))
    (hsv : ∀ P H H4 c x, svC (P, join H H4) c x = SV P H H4 c x)
    (D : Nat → Nat → T → V → Bool) :
    K4w * ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
      indB (D P H4 H (RV P H x H4)))))) ≤
    ST (fun H => SC (fun c => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
      indB (D P (pgJ P H H4 c x).2 (pgJ P H H4 c x).1 (SV P H H4 c x))))))) + ε := by
  have hE := h (fun PH v => D PH.1 (split PH.2).2 (split PH.2).1 v)
  have e1 : ST (fun H => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
      indB (D P H4 H (RV P H x H4)))))) =
      sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 => ST (fun H => sm (fun x =>
        indB ((fun PH v => D PH.1 (split PH.2).2 (split PH.2).1 v) (P, join H H4) (rvC (P, join H H4) x)))))) := by
    rw [← lin_swap2 ST hST]
    refine congrArg ST (funext fun H => ?_)
    rw [← lin_swap2 sm hsm]
    refine congrArg sm (funext fun x => sumTo_congr _ (fun P _ => congrArg (indB (permB K P) * ·)
      (sumTo_congr _ (fun H4 _ => ?_))))
    show indB (D P H4 H (RV P H x H4)) = indB (D P (split (join H H4)).2 (split (join H H4)).1 (rvC (P, join H H4) x))
    rw [hsplit, hrv]
  have e2 : ST (fun H => SC (fun c => sm (fun x => sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
      indB (D P (pgJ P H H4 c x).2 (pgJ P H H4 c x).1 (SV P H H4 c x))))))) =
      sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 => ST (fun H => SC (fun c => sm (fun x =>
        indB ((fun PH v => D PH.1 (split PH.2).2 (split PH.2).1 v) (pgC (P, join H H4) c x)
          (svC (P, join H H4) c x))))))) := by
    rw [← lin_swap2 ST hST]
    refine congrArg ST (funext fun H => ?_)
    rw [← lin_swap2 SC hSC]
    refine congrArg SC (funext fun c => ?_)
    rw [← lin_swap2 sm hsm]
    refine congrArg sm (funext fun x => sumTo_congr _ (fun P _ => congrArg (indB (permB K P) * ·)
      (sumTo_congr _ (fun H4 _ => ?_))))
    show indB (D P (pgJ P H H4 c x).2 (pgJ P H H4 c x).1 (SV P H H4 c x)) =
      indB (D (pgC (P, join H H4) c x).1 (split (pgC (P, join H H4) c x).2).2 (split (pgC (P, join H H4) c x).2).1
        (svC (P, join H H4) c x))
    rw [hpg, hsv, hsplit]
  rw [e1, e2]
  exact hE

/-- **`zk_squeezeN`'s hypotheses hold together, at 0.8's duplex**: `n`
    proofs, proof `i` from its own first position `p1 i` with its own
    blocks, `k > 0` absorptions and empty-buffer squeezes each; the view the
    challenges at the proofs' squeeze positions; the simulator reading the
    table as the real view does, so `hyp` holds exactly.  The conclusion
    says the permutation and its answers at the `n` squeeze positions look
    as the permutation does with those answers exchanged for a uniform
    table's, up to the runs' exchanges and collisions. -/
theorem zk_squeezeN_sat08 {R p Q SQ k n : Nat} (hR : 0 < R) (hp : 0 < p) (hQ : 0 < Q) (hk : 0 < k)
    (p1 : Nat → Nat) (h1 : ∀ i, p1 i < p ^ R * (p * Q)) (blk : Nat → List Nat → Nat)
    (E : Nat → Unit → List Nat → Bool) :
    let K := p ^ R * (p * Q)
    let nxtI := fun i => nxt08 R p Q SQ (p1 i) (blk i)
    let ps := fun P => dedupL (sqOf nxtI (runsN K nxtI k P n))
    (K - n * k) * (1 * (K ^ K * sumTo (K ^ K) (fun P => indB (permB K P &&
        E P () ((sqOf nxtI (runsN K nxtI k P n)).map (getAt (ps P) ((ps P).map (fun v => rget K v P)))))))) ≤
      (K - n * k) * (sumTo (K ^ K) (fun P => indB (permB K P) * sumTo (K ^ K) (fun H4 =>
        indB (E (progL K (ps P) H4 P) () ((sqOf nxtI (runsN K nxtI k P n)).map
          (getAt (ps P) ((ps P).map (fun v => rget K v H4))))))) + 0) +
      1 * (K ^ (K - 1) * (1 * (((K - n * k) * (n * (n * k + n)) +
        K * n * ((sumTo (n * k) (fun j => j) + n * k * n) * (p ^ R * p))) * sumTo (K ^ K) (fun P => indB (permB K P))))) := by
  intro K nxtI ps
  have hK : 0 < K := Nat.mul_pos (Nat.pow_pos hp) (Nat.mul_pos hp hQ)
  exact zk_squeezeN (T := Unit) (X := Unit) (C := Unit) (K4w := 1) (ε := 0) hK hk (κ08 (p ^ R) p Q)
    (κ08_count (Nat.mul_pos (Nat.pow_pos hp) hp)) (fun f => f ()) (fun _ _ => rfl) (fun f => f ()) (fun _ _ => rfl)
    (fun f => f ()) (fun _ _ => nxtI) (fun _ _ i => nxt08_lt (SQ := SQ) hR hp hQ (h1 i) (blk i))
    (fun _ _ i => nxt08_κ (SQ := SQ) (p1 := p1 i) hR hp hQ (blk i))
    (fun c _ _ g => (sqOf nxtI c).map g) (fun _ H H4 _ _ => (H, H4))
    (fun P _ H4 _ _ => (sqOf nxtI (runsN K nxtI k P n)).map (getAt (ps P) ((ps P).map (fun v => rget K v H4))))
    (fun P _ _ => ps P) (fun _ _ _ _ => rfl)
    (fun D => by rw [Nat.one_mul, Nat.add_zero]; exact Nat.le_refl _) E

end Circuit
