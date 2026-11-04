import Ski.Circuit.CompDTraceBus

/-!
# The DEC rows' messages, by kind, and their chains telescoping

Per kind of row, its messages on `decn`, `decb`, `decd`, `decx` as
indicator sums; then the chains of a call telescope: the nouns' needs on
`decn` close up to the subject's (`DecT.callN`), the bits' chains on `decb`
close (`callB`), the head's verdict on `decd` meets the subject's
(`callD`), and the subject's row sends the result on `decx` (`callX`).
-/

namespace Circuit

open B Air

namespace DecT

theorem bF_t {P : Prop} [Decidable P] (h : P) : bF (decide P) = 1 := by simp [bF, h]
theorem bF_f {P : Prop} [Decidable P] (h : ¬P) : bF (decide P) = 0 := by simp [bF, h]

theorem bF_true : bF true = 1 := rfl
theorem bF_false : bF false = 0 := rfl

theorem ite_ind {t v : List F} (c : F) : (if t = v then c else 0) = c * ind (t = v) := by
  unfold ind; split
  · exact (mul_one' c).symm
  · exact (mul_zero' c).symm

section Rows
variable {A : List Cell} {d : DR} {v : List F}

-- decn

theorem n_bits (hk : d.kind = 3 ∨ d.kind = 4) : sendsT A d "decn" v = 0 := by
  rw [sendN]
  rw [kc, ka, bF_f (by omega), bF_f (by omega)]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem n_atom (hk : d.kind = 2) : sendsT A d "decn" v = -ind ([ofN d.key, ofN d.p, ofN d.ro] = v) := by
  rw [sendN]
  rw [kc, ka, bF_f (by omega), bF_t hk]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem n_cell (hk : d.kind = 1) {hh tt : Nat} (h21 : (sl A d 21).2.2.2 = hh) (h23 : (sl A d 23).2.2.2 = tt) :
    sendsT A d "decn" v = -ind ([ofN d.key, ofN d.p, ofN d.ro] = v) +
      (ind ([ofN d.key, ofN hh, ofN 2 - h0 d] = v) + ind ([ofN d.key, ofN tt, ofN 2] = v)) := by
  rw [sendN]
  rw [kc, ka, bF_t hk, bF_f (by omega), h21, h23]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

-- decb

theorem b_nil (hk : d.kind = 4) :
    sendsT A d "decb" v = -ind ([ofN d.key, ofN d.p, bF d.m, ofN d.lvl, bF d.bw, ofN d.wc] = v) := by
  rw [sendB]
  rw [ka, ks, kn, bF_f (by omega), bF_f (by omega), bF_t hk]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem b_consL (hk : d.kind = 3) (hl : d.last = true) :
    sendsT A d "decb" v = -ind ([ofN d.key, ofN d.p, bF d.m, ofN d.lvl, bF d.bw, ofN d.wc] = v) := by
  rw [sendB]
  rw [ka, ks, kn, bF_f (by omega), bF_t hk, bF_f (by omega)]
  rw [vL, hl]
  rw [show (1 - bF true : F) = 0 by decide]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem b_cons (hk : d.kind = 3) (hl : d.last = false) {t : Nat} (h14 : (sl A d 14).2.2.2 = t) :
    sendsT A d "decb" v = -ind ([ofN d.key, ofN d.p, bF d.m, ofN d.lvl, bF d.bw, ofN d.wc] = v) +
      ind ([ofN d.key, ofN t, bF d.m, ofN (d.lvl + 1), bF (d.bw && !d.bit),
        ofN (d.wc + 6 * (if d.bw then 1 else 0))] = v) := by
  rw [sendB]
  rw [ka, ks, kn, bF_f (by omega), bF_t hk, bF_f (by omega), h14]
  have e1 : ofN (d.lvl + 1) = ofN d.lvl + 1 := by rw [ofN_add]; rfl
  have e2 : bF (d.bw && !d.bit) = vBW d * (1 - vBIT d) := by
    simp only [vBW, vBIT]; cases d.bw <;> cases d.bit <;> decide
  have e3 : ofN (d.wc + 6 * (if d.bw then 1 else 0)) = ofN d.wc + ofN 6 * vWR d := by
    simp only [vWR, vDROP, vBW, vBIT, vL, hl, ofN_add, ofN_mul]
    cases d.bw <;> cases d.bit <;> rfl
  rw [e1, e2, e3]
  rw [vL, hl]
  rw [show (1 - bF false : F) = 1 by decide]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem b_atom (hk : d.kind = 2) {b : Nat} (h22 : (sl A d 22).2.2.2 = b) :
    sendsT A d "decb" v = ind ([ofN d.key, ofN b, bF (d.ro != 1), ofN 0, bF (d.ro == 1), ofN 0] = v) := by
  rw [sendB]
  rw [ka, ks, kn, bF_t hk, bF_f (by omega), bF_f (by omega), h22]
  have e1 : h1 d = bF (d.ro == 1) := by
    unfold h1
    by_cases h : d.ro = 1
    · rw [bF_t (P := (d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 1) ⟨.inr hk, h⟩, h]; rfl
    · rw [bF_f (P := (d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 1) (by omega), beq_false_of_ne h]; rfl
  have e2 : (1 : F) - bF (d.ro == 1) = bF (d.ro != 1) := by
    unfold bne; cases d.ro == 1 <;> decide
  rw [e1, e2]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem b_cell (hk : d.kind = 1) : sendsT A d "decb" v = 0 := by
  rw [sendB]
  rw [ka, ks, kn, bF_f (by omega), bF_f (by omega), bF_f (by omega)]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

-- decd

theorem d_zero (hk : 1 ≤ d.kind ∧ d.kind ≤ 4) (h1' : d.kind = 1 → d.ro ≠ 0 ∧ d.ro ≠ 1)
    (h3 : d.kind = 3 ∨ d.kind = 4 → d.m = true) : sendsT A d "decd" v = 0 := by
  rw [sendD]
  have hs : vSUB d = 0 := by
    unfold vSUB kc h0
    by_cases h : d.kind = 1
    · rw [bF_f (P := (d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 0) (by have := h1' h; omega), mul_zero']
    · rw [bF_f h, zero_mul']
  have hc : kc d * h1 d = 0 := by
    unfold kc h1
    by_cases h : d.kind = 1
    · rw [bF_f (P := (d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 1) (by have := h1' h; omega), mul_zero']
    · rw [bF_f h, zero_mul']
  have hd0 : ks d * vL d * (1 - vM d) = 0 := by
    unfold ks
    by_cases h : d.kind = 3
    · rw [vM, h3 (.inl h)]; rw [show (1 - bF true : F) = 0 by decide, mul_zero']
    · rw [bF_f h, zero_mul', zero_mul']
  have hd1 : kn d * (1 - vM d) = 0 := by
    unfold kn
    by_cases h : d.kind = 4
    · rw [vM, h3 (.inr h)]; rw [show (1 - bF true : F) = 0 by decide, mul_zero']
    · rw [bF_f h, zero_mul']
  rw [hs, hc, hd0, hd1]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem d_nil (hk : d.kind = 4) (hm : d.m = false) : sendsT A d "decd" v = ind ([ofN d.key, ofN 1, ofN d.wc] = v) := by
  rw [sendD]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show kc d * h1 d = 0 by unfold kc; rw [bF_f (by omega), zero_mul'],
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], show kn d = 1 by unfold kn; rw [bF_t hk], vM, hm]
  rw [show (1 - bF false : F) = 1 by decide]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem d_consL (hk : d.kind = 3) (hm : d.m = false) (hl : d.last = true) :
    sendsT A d "decd" v = ind ([ofN d.key, ofN 0, ofN (d.wc + (if d.bw && !d.bit then 6 else 0))] = v) := by
  rw [sendD]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show kc d * h1 d = 0 by unfold kc; rw [bF_f (by omega), zero_mul'],
    show ks d = 1 by unfold ks; rw [bF_t hk], show kn d = 0 by unfold kn; rw [bF_f (by omega)], vM, hm, vL, hl]
  have e3 : ofN (d.wc + (if d.bw && !d.bit then 6 else 0)) = ofN d.wc + ofN 6 * vWR d := by
    simp only [vWR, vDROP, vBW, vBIT, vL, hl, ofN_add]
    cases d.bw <;> cases d.bit <;> rfl
  rw [e3]
  rw [show (1 - bF false : F) = 1 by decide, show bF true = 1 from rfl]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem d_cons (hk : d.kind = 3) (hl : d.last = false) : sendsT A d "decd" v = 0 := by
  rw [sendD]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show kc d * h1 d = 0 by unfold kc; rw [bF_f (by omega), zero_mul'],
    show kn d = 0 by unfold kn; rw [bF_f (by omega)], vL, hl]
  rw [show bF false = 0 from rfl]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem d_cellH (hk : d.kind = 1) (hro : d.ro = 1) : sendsT A d "decd" v = ind ([ofN d.key, ofN 1, ofN 0] = v) := by
  rw [sendD]
  rw [show vSUB d = 0 by unfold vSUB h0; rw [bF_f (by omega), mul_zero'],
    show kc d * h1 d = 1 by unfold kc h1; rw [bF_t hk, bF_t ⟨.inl hk, hro⟩]; rfl,
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], show kn d = 0 by unfold kn; rw [bF_f (by omega)]]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem d_cellS (hk : d.kind = 1) (hro : d.ro = 0) :
    sendsT A d "decd" v = -ind ([ofN d.key, bF d.err, ofN d.wc] = v) := by
  rw [sendD]
  rw [show vSUB d = 1 by unfold vSUB kc h0; rw [bF_t hk, bF_t ⟨.inl hk, hro⟩]; rfl,
    show kc d * h1 d = 0 by unfold h1; rw [bF_f (by omega), mul_zero'],
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], show kn d = 0 by unfold kn; rw [bF_f (by omega)]]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

-- decx

theorem x_zero (hk : d.kind = 1 ∨ d.kind = 2 → d.ro ≠ 0) : sendsT A d "decx" v = 0 := by
  rw [sendX]
  have : h0 d = 0 := by
    unfold h0
    rw [bF_f]; intro ⟨h1, h2⟩; exact hk h1 h2
  rw [show vSUB d = 0 by unfold vSUB; rw [this, mul_zero'], this, mul_zero']
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem x_cell (hk : d.kind = 1) (hro : d.ro = 0) : sendsT A d "decx" v =
    ind ([ofN d.key, ofN d.key + ofN 12 * bF d.err, ofN d.key + ofN 12 + ofN d.wc + ofN 3 * bF d.err] = v) := by
  rw [sendX]
  rw [show vSUB d = 1 by unfold vSUB kc h0; rw [bF_t hk, bF_t ⟨.inl hk, hro⟩]; rfl,
    show ka d * h0 d = 0 by unfold ka; rw [bF_f (by omega), zero_mul']]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem x_atom (hk : d.kind = 2) (hro : d.ro = 0) : sendsT A d "decx" v =
    ind ([ofN d.key, ofN d.key, ofN d.key + ofN 3] = v) := by
  rw [sendX]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show ka d * h0 d = 1 by unfold ka h0; rw [bF_t hk, bF_t ⟨.inr hk, hro⟩]; rfl]
  (try unfold ind); repeat' split
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

end Rows

-- ---------------------------------------------------------------------------
-- Sums over rows
-- ---------------------------------------------------------------------------

/-- What a list of rows sends on `B` with the tuple `v`. -/
def S (A : List Cell) (B : String) (v : List F) (L : List DR) : F :=
  (L.map (fun d => sendsT A d B v)).foldr (· + ·) 0

section Sums
variable {A : List Cell} {B : String} {v : List F}

theorem S_cons (d : DR) (L : List DR) : S A B v (d :: L) = sendsT A d B v + S A B v L := rfl

theorem S_nil : S A B v [] = 0 := rfl

theorem S_append : ∀ (L1 L2 : List DR), S A B v (L1 ++ L2) = S A B v L1 + S A B v L2
  | [], L2 => (zero_add' _).symm
  | d :: L1, L2 => by rw [List.cons_append, S_cons, S_cons, S_append L1 L2, add_assoc']

theorem S_zero : ∀ {L : List DR}, (∀ d ∈ L, sendsT A d B v = 0) → S A B v L = 0
  | [], _ => rfl
  | d :: L, h => by
    rw [S_cons, h d List.mem_cons_self, S_zero (fun d' hd => h d' (List.mem_cons_of_mem _ hd))]; exact zero_add' 0

end Sums

theorem tel3 (a b c : F) : -a + (b + c) + (-b + -c) = -a :=
  E.eval_eq_of_norm (e := .add (.add (.neg (.atom (.main 0 0))) (.add (.atom (.main 0 1)) (.atom (.main 0 2))))
    (.add (.neg (.atom (.main 0 1))) (.neg (.atom (.main 0 2))))) (e' := .neg (.atom (.main 0 0))) (by decide)
    (at4 a b c 0)
theorem tel2 (a b : F) : -a + b + -b = -a :=
  E.eval_eq_of_norm (e := .add (.add (.neg (.atom (.main 0 0))) (.atom (.main 0 1))) (.neg (.atom (.main 0 1))))
    (e' := .neg (.atom (.main 0 0))) (by decide) (at4 a b 0 0)
theorem tel0 (b : F) : b + (-b) = 0 :=
  E.eval_eq_of_norm (e := .add (.atom (.main 0 0)) (.neg (.atom (.main 0 0)))) (e' := .const 0) (by decide)
    (at4 b 0 0 0)

-- ---------------------------------------------------------------------------
-- The rows' shapes
-- ---------------------------------------------------------------------------

section Shape
variable {A : List Cell} {key : Nat}

theorem bits_shape {m : Bool} : ∀ (n p lvl : Nat) (bw : Bool) (wc : Nat), ∀ d ∈ bitsRows A key m n p lvl bw wc,
    (d.kind = 3 ∨ d.kind = 4) ∧ d.m = m
  | 0, _, _, _, _ => by intro d hd; cases hd
  | n + 1, p, lvl, bw, wc => by
    intro d hd
    unfold bitsRows at hd
    split at hd
    · rw [List.mem_singleton] at hd; subst hd; exact ⟨.inr rfl, rfl⟩
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact ⟨.inl rfl, rfl⟩
        · split at hd
          · cases hd
          · exact bits_shape n _ _ _ _ d hd
      · cases hd

/-- A noun's rows: wrappers in its role or a tail's, chains in its mode or `1`. -/
theorem noun_shape : ∀ (n p ro : Nat), ∀ d ∈ nounRows A key n p ro,
    (d.kind = 1 ∨ d.kind = 2 → d.ro = ro ∨ d.ro = 2) ∧ (d.kind = 3 ∨ d.kind = 4 → d.m = (ro != 1) ∨ d.m = true) ∧
      1 ≤ d.kind ∧ d.kind ≤ 4
  | 0, _, _ => by intro d hd; cases hd
  | n + 1, p, ro => by
    intro d hd
    unfold nounRows at hd
    split at hd
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact ⟨fun _ => .inl rfl, fun h => by simp only [atomRow] at h; exact absurd h (by decide), by simp [atomRow], by simp [atomRow]⟩
      · obtain ⟨hk, hm⟩ := bits_shape _ _ _ _ _ d hd
        exact ⟨fun h => by omega, fun _ => .inl hm, by omega, by omega⟩
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact ⟨fun _ => .inl rfl, fun h => by simp only [cellRow] at h; exact absurd h (by decide), by simp [cellRow], by simp [cellRow]⟩
        · have : ∀ q, d ∈ nounRows A key n q 2 → _ := fun q h => noun_shape n q 2 d h
          rcases List.mem_append.1 hd with hd | hd <;>
          · obtain ⟨h1, h2, h3, h4⟩ := noun_shape n _ 2 d hd
            exact ⟨fun h => .inr ((h1 h).elim id id), fun h => .inr ((h2 h).elim (fun e => by rw [e]; rfl) id), h3, h4⟩
      · cases hd

end Shape

-- ---------------------------------------------------------------------------
-- decn: the nouns' needs
-- ---------------------------------------------------------------------------

section Chains
variable {A : List Cell} {key : Nat} {v : List F}

theorem S_bits_n {m : Bool} (n p lvl : Nat) (bw : Bool) (wc : Nat) :
    S A "decn" v (bitsRows A key m n p lvl bw wc) = 0 :=
  S_zero (fun d hd => n_bits (bits_shape n p lvl bw wc d hd).1)

theorem S_noun_n : ∀ (n p ro : Nat) {s : DecJet.Nn}, ro ≠ 0 → DecJet.readNn (A.take key) n p = some s →
    S A "decn" v (nounRows A key n p ro) = -ind ([ofN key, ofN p, ofN ro] = v)
  | 0, _, _, _, _, h => by cases h
  | n + 1, p, ro, s, hro, h => by
    unfold nounRows
    unfold DecJet.readNn at h
    cases ha : DecJet.readAtom (A.take key) p with
    | some sk =>
      simp only
      rw [S_cons, n_atom (d := atomRow key p ro) rfl, S_bits_n]
      exact add_zero' _
    | none =>
      rw [ha] at h
      simp only at h ⊢
      cases hc : DecJet.readCell (A.take key) p with
      | none => rw [hc] at h; cases h
      | some sk =>
        rw [hc] at h
        simp only at h ⊢
        cases hh : DecJet.readNn (A.take key) n sk.h with
        | none => rw [hh] at h; cases h
        | some hn =>
          cases ht : DecJet.readNn (A.take key) n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some tn =>
            obtain ⟨_, _, _, _, _, _, h21, h23⟩ := cellReads (d := cellRow key p ro false 0) rfl hc
            rw [S_cons, n_cell (d := cellRow key p ro false 0) rfl h21 h23, S_append,
              S_noun_n n sk.h 2 (by decide) hh, S_noun_n n sk.t 2 (by decide) ht]
            have : h0 (cellRow key p ro false 0) = 0 := bF_f (by simp [cellRow]; omega)
            rw [this, show (ofN 2 - 0 : F) = ofN 2 from rfl]
            exact tel3 _ _ _

-- ---------------------------------------------------------------------------
-- decb: the bits' chains
-- ---------------------------------------------------------------------------

theorem S_bits_b {m : Bool} : ∀ (n p lvl : Nat) (bw : Bool) (wc : Nat) {bs : List Bool} {sks : List DecJet.ConsSk},
    DecJet.readBits (A.take key) n p = some (bs, sks) →
    S A "decb" v (bitsRows A key m n p lvl bw wc) = -ind ([ofN key, ofN p, bF m, ofN lvl, bF bw, ofN wc] = v)
  | 0, _, _, _, _, _, _, h => by cases h
  | n + 1, p, lvl, bw, wc, bs, sks, h => by
    unfold bitsRows
    unfold DecJet.readBits at h
    by_cases hK : DecJet.isK (A.take key) p = true
    · rw [if_pos hK, S_cons, b_nil (d := nilRow key p m lvl bw wc) rfl, S_nil]; exact add_zero' _
    · rw [if_neg hK] at h ⊢
      cases hr : DecJet.readCons (A.take key) p with
      | none => rw [hr] at h; cases h
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hr] at h
        simp only at h ⊢
        cases hb : DecJet.readBits (A.take key) n sk.t with
        | none => rw [hb] at h; cases h
        | some q2 =>
          obtain ⟨bs', sks'⟩ := q2
          by_cases hl : DecJet.isK (A.take key) sk.t = true
          · rw [if_pos hl, S_cons, b_consL (d := consRow key p m lvl bw wc b (DecJet.isK (A.take key) sk.t)) rfl hl, S_nil]; exact add_zero' _
          · have hl' : DecJet.isK (A.take key) sk.t = false := by simpa using hl
            obtain ⟨_, _, _, h14⟩ := consReads (d := consRow key p m lvl bw wc b (DecJet.isK (A.take key) sk.t)) rfl hr
              rfl rfl (fun hK' => readBits_tail hb hK')
            rw [if_neg hl, S_cons, b_cons (d := consRow key p m lvl bw wc b (DecJet.isK (A.take key) sk.t)) rfl hl' h14,
              S_bits_b n sk.t (lvl + 1) _ _ hb]
            exact tel2 _ _

theorem S_noun_b : ∀ (n p ro : Nat) {s : DecJet.Nn}, DecJet.readNn (A.take key) n p = some s →
    S A "decb" v (nounRows A key n p ro) = 0
  | 0, _, _, _, h => by cases h
  | n + 1, p, ro, s, h => by
    unfold nounRows
    unfold DecJet.readNn at h
    cases ha : DecJet.readAtom (A.take key) p with
    | some sk =>
      rw [ha] at h
      simp only at h ⊢
      cases hb : DecJet.readBits (A.take key) (n + 1) sk.b with
      | none => rw [hb] at h; cases h
      | some q =>
        obtain ⟨_, _, _, _, _, h22⟩ := atomReads (d := atomRow key p ro) rfl ha
        rw [S_cons, b_atom (d := atomRow key p ro) rfl h22, S_bits_b _ _ _ _ _ hb]
        exact tel0 (ind ([ofN key, ofN sk.b, bF (ro != 1), ofN 0, bF (ro == 1), ofN 0] = v))
    | none =>
      rw [ha] at h
      simp only at h ⊢
      cases hc : DecJet.readCell (A.take key) p with
      | none => rw [hc] at h; cases h
      | some sk =>
        rw [hc] at h
        simp only at h ⊢
        cases hh : DecJet.readNn (A.take key) n sk.h with
        | none => rw [hh] at h; cases h
        | some hn =>
          cases ht : DecJet.readNn (A.take key) n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some tn =>
            rw [S_cons, b_cell (d := cellRow key p ro false 0) rfl, S_append, S_noun_b n sk.h 2 hh,
              S_noun_b n sk.t 2 ht]
            simp only [zero_add']

-- ---------------------------------------------------------------------------
-- decd: the head's verdict
-- ---------------------------------------------------------------------------

/-- The cells the head's rewritten bits take, from a borrow. -/
def wcAdd : Bool → List Bool → Nat
  | _, [] => 0
  | bw, b :: bs => (if bw && !(b && bs.isEmpty) then 6 else 0) + wcAdd (bw && !b) bs

theorem wcAdd_false : ∀ bs, wcAdd false bs = 0
  | [] => rfl
  | b :: bs => by simp [wcAdd, wcAdd_false bs]

theorem wcAdd_cells : ∀ (c : Nat) (bs : List Bool) (sks : List DecJet.ConsSk), sks.length = bs.length →
    wcAdd true bs = (DecJet.bitCells c bs sks).length
  | _, [], _, _ => rfl
  | _, _ :: _, [], h => absurd h (by rw [List.length_nil, List.length_cons]; exact Nat.noConfusion)
  | c, false :: bs, sk :: sks, h => by
    show 6 + wcAdd true bs = ([Cell.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 0,
      .app 0 (if DecJet.dropped bs then 0 else c + 6)] ++ DecJet.bitCells (c + 6) bs sks).length
    rw [List.length_append, wcAdd_cells (c + 6) bs sks (Nat.succ.inj h)]; rfl
  | c, true :: bs, sk :: sks, _ => by
    cases bs with
    | nil => rfl
    | cons b bs => show 6 + wcAdd false (b :: bs) = 6; rw [wcAdd_false]

theorem readBits_ne {H : List Cell} {n t : Nat} {bs : List Bool} {sks : List DecJet.ConsSk}
    (h : DecJet.readBits H n t = some (bs, sks)) (hK : DecJet.isK H t = false) : bs ≠ [] := by
  cases n with
  | zero => cases h
  | succ n =>
    unfold DecJet.readBits at h
    rw [hK, if_neg (by decide)] at h
    split at h
    · split at h
      · cases h; exact List.cons_ne_nil _ _
      · cases h
    · cases h

theorem S_bits_d : ∀ (n p lvl : Nat) (bw : Bool) (wc : Nat) {bs : List Bool} {sks : List DecJet.ConsSk},
    DecJet.readBits (A.take key) n p = some (bs, sks) →
    S A "decd" v (bitsRows A key false n p lvl bw wc) =
      if bs = [] then ind ([ofN key, ofN 1, ofN wc] = v) else ind ([ofN key, ofN 0, ofN (wc + wcAdd bw bs)] = v)
  | 0, _, _, _, _, _, _, h => by cases h
  | n + 1, p, lvl, bw, wc, bs, sks, h => by
    unfold bitsRows
    unfold DecJet.readBits at h
    by_cases hK : DecJet.isK (A.take key) p = true
    · rw [if_pos hK] at h ⊢
      cases h
      rw [S_cons, d_nil (d := nilRow key p false lvl bw wc) rfl rfl, S_nil, if_pos rfl]; exact add_zero' _
    · rw [if_neg hK] at h ⊢
      cases hr : DecJet.readCons (A.take key) p with
      | none => rw [hr] at h; cases h
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hr] at h
        simp only at h ⊢
        cases hb : DecJet.readBits (A.take key) n sk.t with
        | none => rw [hb] at h; cases h
        | some q2 =>
          obtain ⟨bs', sks'⟩ := q2
          rw [hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [if_neg (List.cons_ne_nil _ _)]
          by_cases hl : DecJet.isK (A.take key) sk.t = true
          · rw [if_pos hl, S_cons, d_consL (d := consRow key p false lvl bw wc b (DecJet.isK (A.take key) sk.t)) rfl rfl hl, S_nil, add_zero']
            rw [readBits_K hb hl]
            show ind ([ofN key, ofN 0, ofN (wc + (if bw && !b then 6 else 0))] = v) = _
            congr 4
            cases bw <;> cases b <;> rfl
          · have hl' : DecJet.isK (A.take key) sk.t = false := by simpa using hl
            have hne := readBits_ne hb hl'
            rw [if_neg hl, S_cons, d_cons (d := consRow key p false lvl bw wc b (DecJet.isK (A.take key) sk.t)) rfl hl', zero_add',
              S_bits_d n sk.t (lvl + 1) _ _ hb, if_neg hne]
            congr 4
            have : bs'.isEmpty = false := by cases bs' with | nil => exact absurd rfl hne | cons _ _ => rfl
            simp only [wcAdd, this, Bool.and_false, Bool.not_false, Bool.and_true]
            cases bw <;> simp [Nat.add_assoc]

theorem S_noun2_d : ∀ (n p : Nat), S A "decd" v (nounRows A key n p 2) = 0 := by
  intro n p
  apply S_zero
  intro d hd
  obtain ⟨h1, h2, h3, h4⟩ := noun_shape n p 2 d hd
  refine d_zero ⟨h3, h4⟩ (fun h => ?_) (fun h => ?_)
  · rcases h1 (.inl h) with e | e <;> rw [e] <;> decide
  · rcases h2 h with e | e <;> rw [e] <;> rfl

theorem S_noun_x : ∀ (n p ro : Nat), ro ≠ 0 → S A "decx" v (nounRows A key n p ro) = 0 := by
  intro n p ro hro
  apply S_zero
  intro d hd
  obtain ⟨h1, _, _, _⟩ := noun_shape n p ro d hd
  exact x_zero (fun h => by rcases h1 h with e | e <;> rw [e] <;> omega)

theorem S_bits_x {m : Bool} (n p lvl : Nat) (bw : Bool) (wc : Nat) :
    S A "decx" v (bitsRows A key m n p lvl bw wc) = 0 :=
  S_zero (fun d hd => x_zero (fun h => by have := (bits_shape n p lvl bw wc d hd).1; omega))

theorem S_bits_d1 (n p lvl : Nat) (bw : Bool) (wc : Nat) :
    S A "decd" v (bitsRows A key true n p lvl bw wc) = 0 :=
  S_zero (fun d hd => by
    obtain ⟨hk, hm⟩ := bits_shape n p lvl bw wc d hd
    have h14 : 1 ≤ d.kind ∧ d.kind ≤ 4 := ⟨by rcases hk with e | e <;> omega, by rcases hk with e | e <;> omega⟩
    exact d_zero h14 (fun h => absurd h (by rcases hk with e | e <;> omega)) (fun _ => hm))

theorem S_bits_b0 {m : Bool} (n p lvl : Nat) (bw : Bool) (wc : Nat) :
    S A "decn" v (bitsRows A key m n p lvl bw wc) = 0 := S_bits_n n p lvl bw wc

end Chains

end DecT

end Circuit
