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

/-- A chain's mode field: the mode, and `2` after a list's end. -/
abbrev mf (m term : Bool) : F := bF m + ofN 2 * bF term

theorem mf_false (m : Bool) : mf m false = bF m := by cases m <;> decide

-- decn

theorem n_cons (hk : d.kind = 3 ∨ d.kind = 4) : sendsT A d "decn" v = 0 := by
  rw [sendN]
  rw [kc, ka, ki, bF_f (by omega), bF_f (by omega), bF_f (P := d.kind = 5) (by omega)]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem n_indB (hk : d.kind = 5) (hb : d.ib = true) : sendsT A d "decn" v = 0 := by
  rw [sendN]
  rw [kc, ka, ki, bF_f (by omega), bF_f (by omega), bF_t hk, vIB, hb]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem n_bits (hk : d.kind = 3 ∨ d.kind = 4 ∨ (d.kind = 5 ∧ d.ib = true)) : sendsT A d "decn" v = 0 := by
  rcases hk with hk | hk | ⟨hk, hb⟩
  · exact n_cons (.inl hk)
  · exact n_cons (.inr hk)
  · exact n_indB hk hb

theorem n_ind (hk : d.kind = 5) (hb : d.ib = false) {R : Nat} (h1 : (sl A d 1).2.2.2 = R) :
    sendsT A d "decn" v = -ind ([ofN d.key, ofN d.p, ofN d.ro] = v) + ind ([ofN d.key, ofN R, ofN d.ro] = v) := by
  rw [sendN]
  rw [kc, ka, ki, bF_f (by omega), bF_f (by omega), bF_t hk, vIB, hb, h1]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem n_atom (hk : d.kind = 2) : sendsT A d "decn" v = -ind ([ofN d.key, ofN d.p, ofN d.ro] = v) := by
  rw [sendN]
  rw [kc, ka, ki, bF_f (by omega), bF_t hk, bF_f (by omega)]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem n_cell (hk : d.kind = 1) {hh tt : Nat} (h21 : (sl A d 21).2.2.2 = hh) (h26 : (sl A d 26).2.2.2 = tt) :
    sendsT A d "decn" v = -ind ([ofN d.key, ofN d.p, ofN d.ro] = v) +
      (ind ([ofN d.key, ofN hh, ofN 2 - h0 d] = v) + ind ([ofN d.key, ofN tt, ofN 2] = v)) := by
  rw [sendN]
  rw [kc, ka, ki, bF_t hk, bF_f (by omega), bF_f (by omega), h21, h26]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

-- decb

theorem b_nil (hk : d.kind = 4) :
    sendsT A d "decb" v = -ind ([ofN d.key, ofN d.p, mf d.m d.term, ofN d.lvl, bF d.bw, ofN d.wc] = v) := by
  rw [sendB]
  rw [ka, ks, kn, ki, bF_f (by omega), bF_f (by omega), bF_t hk, bF_f (by omega)]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem b_cons (hk : d.kind = 3) {t : Nat} (h14 : (sl A d 14).2.2.2 = t) :
    sendsT A d "decb" v = -ind ([ofN d.key, ofN d.p, bF d.m, ofN d.lvl, bF d.bw, ofN d.wc] = v) +
      ind ([ofN d.key, ofN t, mf d.m d.last, ofN (d.lvl + 1), bF (d.bw && !d.bit),
        ofN (d.wc + 6 * (if d.bw && !(d.bit && d.last) then 1 else 0))] = v) := by
  rw [sendB]
  rw [ka, ks, kn, ki, bF_f (by omega), bF_t hk, bF_f (by omega), bF_f (by omega), h14]
  have e1 : ofN (d.lvl + 1) = ofN d.lvl + 1 := by rw [ofN_add]; rfl
  have e2 : bF (d.bw && !d.bit) = vBW d * (1 - vBIT d) := by
    simp only [vBW, vBIT]; cases d.bw <;> cases d.bit <;> decide
  have e3 : ofN (d.wc + 6 * (if d.bw && !(d.bit && d.last) then 1 else 0)) = ofN d.wc + ofN 6 * vWR d := by
    simp only [vWR, vDROP, vBW, vBIT, vL, ofN_add, ofN_mul]
    cases d.bw <;> cases d.bit <;> cases d.last <;> rfl
  rw [e1, e2, e3]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem b_ind (hk : d.kind = 5) (hb : d.ib = true) {R : Nat} (h1 : (sl A d 1).2.2.2 = R) :
    sendsT A d "decb" v = -ind ([ofN d.key, ofN d.p, mf d.m d.term, ofN d.lvl, bF d.bw, ofN d.wc] = v) +
      ind ([ofN d.key, ofN R, mf d.m d.term, ofN d.lvl, bF d.bw, ofN d.wc] = v) := by
  rw [sendB]
  rw [ka, ks, kn, ki, bF_f (by omega), bF_f (by omega), bF_f (by omega), bF_t hk, vIB, hb, h1]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem b_indN (hk : d.kind = 5) (hb : d.ib = false) : sendsT A d "decb" v = 0 := by
  rw [sendB]
  rw [ka, ks, kn, ki, bF_f (by omega), bF_f (by omega), bF_f (by omega), bF_t hk, vIB, hb]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem b_atom (hk : d.kind = 2) {b : Nat} (h22 : (sl A d 22).2.2.2 = b) :
    sendsT A d "decb" v = ind ([ofN d.key, ofN b, bF (d.ro != 1), ofN 0, bF (d.ro == 1), ofN 0] = v) := by
  rw [sendB]
  rw [ka, ks, kn, ki, bF_t hk, bF_f (by omega), bF_f (by omega), bF_f (by omega), h22]
  have e1 : h1 d = bF (d.ro == 1) := by
    unfold h1
    by_cases h : d.ro = 1
    · rw [bF_t (P := (d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 1) ⟨.inr hk, h⟩, h]; rfl
    · rw [bF_f (P := (d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 1) (by omega), beq_false_of_ne h]; rfl
  have e2 : (1 : F) - bF (d.ro == 1) = bF (d.ro != 1) := by
    unfold bne; cases d.ro == 1 <;> decide
  rw [e1, e2]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem b_cell (hk : d.kind = 1) : sendsT A d "decb" v = 0 := by
  rw [sendB]
  rw [ka, ks, kn, ki, bF_f (by omega), bF_f (by omega), bF_f (by omega), bF_f (by omega)]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

-- decd

theorem d_zero (hk : 1 ≤ d.kind ∧ d.kind ≤ 5) (h1' : d.kind = 1 → d.ro ≠ 0 ∧ d.ro ≠ 1)
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
  have hd1 : kn d * (1 - vM d) * (1 - vT d) = 0 := by
    unfold kn
    by_cases h : d.kind = 4
    · rw [vM, h3 (.inr h)]; rw [show (1 - bF true : F) = 0 by decide, mul_zero', zero_mul']
    · rw [bF_f h, zero_mul', zero_mul']
  rw [hs, hc, hd0, hd1]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem d_nil (hk : d.kind = 4) (hm : d.m = false) (ht : d.term = false) :
    sendsT A d "decd" v = ind ([ofN d.key, ofN 1, ofN d.wc] = v) := by
  rw [sendD]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show kc d * h1 d = 0 by unfold kc; rw [bF_f (by omega), zero_mul'],
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], show kn d = 1 by unfold kn; rw [bF_t hk], vM, hm, vT, ht]
  rw [show (1 - bF false : F) = 1 by decide]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem d_nilT (hk : d.kind = 4) (ht : d.term = true) : sendsT A d "decd" v = 0 := by
  rw [sendD]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show kc d * h1 d = 0 by unfold kc; rw [bF_f (by omega), zero_mul'],
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], vT, ht]
  rw [show (1 - bF true : F) = 0 by decide]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem d_ind (hk : d.kind = 5) : sendsT A d "decd" v = 0 := by
  rw [sendD]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show kc d * h1 d = 0 by unfold kc; rw [bF_f (by omega), zero_mul'],
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], show kn d = 0 by unfold kn; rw [bF_f (by omega)]]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
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
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
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
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem d_cellH (hk : d.kind = 1) (hro : d.ro = 1) : sendsT A d "decd" v = ind ([ofN d.key, ofN 1, ofN 0] = v) := by
  rw [sendD]
  rw [show vSUB d = 0 by unfold vSUB h0; rw [bF_f (by omega), mul_zero'],
    show kc d * h1 d = 1 by unfold kc h1; rw [bF_t hk, bF_t ⟨.inl hk, hro⟩]; rfl,
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], show kn d = 0 by unfold kn; rw [bF_f (by omega)]]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
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
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
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
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem x_cell (hk : d.kind = 1) (hro : d.ro = 0) : sendsT A d "decx" v =
    ind ([ofN d.key, ofN d.key + ofN 12 * bF d.err, ofN d.key + ofN 12 + ofN d.wc + ofN 3 * bF d.err] = v) := by
  rw [sendX]
  rw [show vSUB d = 1 by unfold vSUB kc h0; rw [bF_t hk, bF_t ⟨.inl hk, hro⟩]; rfl,
    show ka d * h0 d = 0 by unfold ka; rw [bF_f (by omega), zero_mul']]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
  all_goals first | contradiction | decide |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; done) |
    (simp only [zero_mul', mul_zero', zero_add', add_zero', neg_zero_eq]; decide)

theorem x_atom (hk : d.kind = 2) (hro : d.ro = 0) : sendsT A d "decx" v =
    ind ([ofN d.key, ofN d.key, ofN d.key + ofN 3] = v) := by
  rw [sendX]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show ka d * h0 d = 1 by unfold ka h0; rw [bF_t hk, bF_t ⟨.inr hk, hro⟩]; rfl]
  (try unfold ind); repeat' split
  all_goals (try simp only [vIB, vT, ki, bF_true, bF_false])
  all_goals (try (generalize d.ib = x; cases x))
  all_goals (try (generalize d.term = x; cases x))
  all_goals (try (generalize decide (d.kind = 5) = x; cases x))
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

theorem bits_shape {m : Bool} : ∀ (n p lvl : Nat) (bw : Bool) (wc : Nat) (term : Bool),
    ∀ d ∈ bitsRows A key m n p lvl bw wc term,
    (d.kind = 3 ∨ d.kind = 4 ∨ (d.kind = 5 ∧ d.ib = true)) ∧ d.m = m
  | 0, _, _, _, _, _ => by intro d hd; cases hd
  | n + 1, p, lvl, bw, wc, term => by
    intro d hd
    unfold bitsRows at hd
    split at hd
    · rw [List.mem_singleton] at hd; subst hd; exact ⟨.inr (.inl rfl), rfl⟩
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact ⟨.inl rfl, rfl⟩
        · exact bits_shape n _ _ _ _ _ d hd
      · split at hd
        · rcases List.mem_cons.1 hd with rfl | hd
          · exact ⟨.inr (.inr ⟨rfl, rfl⟩), rfl⟩
          · exact bits_shape n _ _ _ _ _ d hd
        · cases hd

/-- A noun's rows: wrappers and needs in its role or a tail's, chains in its
    mode or `1`. -/
theorem noun_shape : ∀ (n p ro : Nat), ∀ d ∈ nounRows A key n p ro,
    (d.kind = 1 ∨ d.kind = 2 → d.ro = ro ∨ d.ro = 2) ∧ (d.kind = 3 ∨ d.kind = 4 → d.m = (ro != 1) ∨ d.m = true) ∧
      1 ≤ d.kind ∧ d.kind ≤ 5
  | 0, _, _ => by intro d hd; cases hd
  | n + 1, p, ro => by
    intro d hd
    unfold nounRows at hd
    split at hd
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact ⟨fun _ => .inl rfl, fun h => by simp only [atomRow] at h; exact absurd h (by decide), by simp [atomRow],
          by simp [atomRow]⟩
      · obtain ⟨hk, hm⟩ := bits_shape _ _ _ _ _ _ d hd
        exact ⟨fun h => by omega, fun _ => .inl hm, by omega, by omega⟩
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact ⟨fun _ => .inl rfl, fun h => by simp only [cellRow] at h; exact absurd h (by decide), by simp [cellRow],
            by simp [cellRow]⟩
        · rcases List.mem_append.1 hd with hd | hd <;>
          · obtain ⟨h1, h2, h3, h4⟩ := noun_shape n _ 2 d hd
            exact ⟨fun h => .inr ((h1 h).elim id id), fun h => .inr ((h2 h).elim (fun e => by rw [e]; rfl) id), h3, h4⟩
      · split at hd
        · rcases List.mem_cons.1 hd with rfl | hd
          · exact ⟨fun h => by simp only [indRow] at h; omega, fun h => by simp only [indRow] at h; omega,
              by simp [indRow], by simp [indRow]⟩
          · exact noun_shape n _ ro d hd
        · cases hd

end Shape

-- ---------------------------------------------------------------------------
-- decn: the nouns' needs
-- ---------------------------------------------------------------------------

section Chains
variable {A : List Cell} {key : Nat} {v : List F}

theorem S_bits_n {m : Bool} (n p lvl : Nat) (bw : Bool) (wc : Nat) (term : Bool) :
    S A "decn" v (bitsRows A key m n p lvl bw wc term) = 0 :=
  S_zero (fun d hd => n_bits (bits_shape n p lvl bw wc term d hd).1)

theorem S_noun_n : ∀ (n p ro : Nat) {s : DecJet.Nn}, ro ≠ 0 → DecJet.readNnI (A.take key) n p = some s →
    S A "decn" v (nounRows A key n p ro) = -ind ([ofN key, ofN p, ofN ro] = v)
  | 0, _, _, _, _, h => by cases h
  | n + 1, p, ro, s, hro, h => by
    rcases readNnI_cases h with ⟨sk, bs, sks, ha, hb, hc, rfl⟩ | ⟨sk, hh, tt, ha, hc, h1, h2, rfl⟩ |
      ⟨R, ha, hc, hi, hR⟩
    · rw [nounRows_atom ha, S_cons, n_atom (d := atomRow key p ro) rfl, S_bits_n]
      exact add_zero' _
    · obtain ⟨_, _, _, _, _, _, h21, h26⟩ := cellReads (d := cellRow key p ro false 0 (iktOf (A.take key) sk.kt)) rfl hc rfl
      rw [nounRows_cell ha hc, S_cons, n_cell (d := cellRow key p ro false 0 (iktOf (A.take key) sk.kt)) rfl h21 h26, S_append,
        S_noun_n n sk.h 2 (by decide) h1, S_noun_n n sk.t 2 (by decide) h2]
      have : h0 (cellRow key p ro false 0 (iktOf (A.take key) sk.kt)) = 0 := bF_f (by simp [cellRow]; omega)
      rw [this, show (ofN 2 - 0 : F) = ofN 2 from rfl]
      exact tel3 _ _ _
    · obtain ⟨_, h1⟩ := indReads (d := indRow key p ro false false 0 false 0 false) rfl hi
      rw [nounRows_ind ha hc hi, S_cons, n_ind (d := indRow key p ro false false 0 false 0 false) rfl rfl h1,
        S_noun_n n R ro hro hR]
      exact tel2 _ _

-- ---------------------------------------------------------------------------
-- decb: the bits' chains
-- ---------------------------------------------------------------------------

theorem S_bits_b {m : Bool} : ∀ (n p lvl : Nat) (bw : Bool) (wc : Nat) (term : Bool) {bs : List Bool}
    {sks : List DecJet.ConsSk},
    DecJet.readBitsI (A.take key) n p = some (bs, sks) → (term = true → bs = []) →
    S A "decb" v (bitsRows A key m n p lvl bw wc term) =
      -ind ([ofN key, ofN p, mf m term, ofN lvl, bF bw, ofN wc] = v)
  | 0, _, _, _, _, _, _, _, h, _ => by cases h
  | n + 1, p, lvl, bw, wc, term, bs, sks, h, ht => by
    rcases readBitsI_cases h with ⟨hK, rfl⟩ | ⟨b, sk, bs', sks', hK, hr, hb, rfl, rfl⟩ | ⟨R, hK, hr, hi, hb⟩
    · rw [bitsRows_K hK, S_cons, b_nil (d := nilRow key p m lvl bw wc term) rfl, S_nil]; exact add_zero' _
    · have hterm : term = false := by cases term; rfl; exact absurd (ht rfl) (List.cons_ne_nil _ _)
      subst hterm
      obtain ⟨_, _, _, h14⟩ := consReads (d := consRow key p m lvl bw wc b (restNil (A.take key) n sk.t)) rfl hr rfl
      rw [bitsRows_cons hK hr, S_cons, b_cons (d := consRow key p m lvl bw wc b (restNil (A.take key) n sk.t)) rfl h14,
        S_bits_b n sk.t (lvl + 1) _ _ _ hb (fun e => by rw [restNil_eq hb] at e; exact List.isEmpty_iff.1 e), mf_false]
      exact tel2 _ _
    · obtain ⟨_, h1⟩ := indReads (d := indRow key p 0 true m lvl bw wc term) rfl hi
      rw [bitsRows_ind hK hr hi, S_cons, b_ind (d := indRow key p 0 true m lvl bw wc term) rfl rfl h1,
        S_bits_b n R lvl bw wc term hb ht]
      exact tel2 _ _

theorem S_noun_b : ∀ (n p ro : Nat) {s : DecJet.Nn}, n ≤ (A.take key).length →
    DecJet.readNnI (A.take key) n p = some s → S A "decb" v (nounRows A key n p ro) = 0
  | 0, _, _, _, _, h => by cases h
  | n + 1, p, ro, s, hn, h => by
    rcases readNnI_cases h with ⟨sk, bs, sks, ha, hb, hc, rfl⟩ | ⟨sk, hh, tt, ha, hc, h1, h2, rfl⟩ |
      ⟨R, ha, hc, hi, hR⟩
    · obtain ⟨_, _, _, _, _, h22⟩ := atomReads (d := atomRow key p ro) rfl ha
      rw [nounRows_atom ha, S_cons, b_atom (d := atomRow key p ro) rfl h22,
        S_bits_b _ _ _ _ _ false (DecJet.readBitsI_mono hb hn) (fun h => absurd h (by decide)), mf_false]
      exact tel0 _
    · rw [nounRows_cell ha hc, S_cons, b_cell (d := cellRow key p ro false 0 _) rfl, S_append,
        S_noun_b n sk.h 2 (by omega) h1, S_noun_b n sk.t 2 (by omega) h2]
      simp only [zero_add']
    · rw [nounRows_ind ha hc hi, S_cons, b_indN (d := indRow key p ro false false 0 false 0 false) rfl rfl,
        S_noun_b n R ro (by omega) hR]
      exact zero_add' 0

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

theorem S_bits_d : ∀ (n p lvl : Nat) (bw : Bool) (wc : Nat) (term : Bool) {bs : List Bool}
    {sks : List DecJet.ConsSk},
    DecJet.readBitsI (A.take key) n p = some (bs, sks) → (term = true → bs = []) →
    S A "decd" v (bitsRows A key false n p lvl bw wc term) =
      if term then 0
      else if bs = [] then ind ([ofN key, ofN 1, ofN wc] = v) else ind ([ofN key, ofN 0, ofN (wc + wcAdd bw bs)] = v)
  | 0, _, _, _, _, _, _, _, h, _ => by cases h
  | n + 1, p, lvl, bw, wc, term, bs, sks, h, ht => by
    rcases readBitsI_cases h with ⟨hK, rfl⟩ | ⟨b, sk, bs', sks', hK, hr, hb, rfl, rfl⟩ | ⟨R, hK, hr, hi, hb⟩
    · rw [bitsRows_K hK, S_cons, S_nil, add_zero', if_pos rfl]
      cases term
      · exact d_nil (d := nilRow key p false lvl bw wc false) rfl rfl rfl
      · exact d_nilT (d := nilRow key p false lvl bw wc true) rfl rfl
    · have hterm : term = false := by cases term; rfl; exact absurd (ht rfl) (List.cons_ne_nil _ _)
      subst hterm
      rw [if_neg (by decide), if_neg (List.cons_ne_nil _ _), bitsRows_cons hK hr, restNil_eq hb, S_cons]
      cases hl : bs'.isEmpty
      · have hne : bs' ≠ [] := fun e => by rw [e] at hl; cases hl
        rw [d_cons (d := consRow key p false lvl bw wc b false) rfl rfl, zero_add',
          S_bits_d n sk.t (lvl + 1) _ _ false hb (fun h => absurd h (by decide)), if_neg (by decide), if_neg hne]
        congr 4
        simp only [wcAdd, hl, Bool.and_false, Bool.not_false, Bool.and_true]
        cases bw <;> simp [Nat.add_assoc]
      · have he : bs' = [] := List.isEmpty_iff.1 hl
        subst he
        rw [d_consL (d := consRow key p false lvl bw wc b true) rfl rfl rfl,
          S_bits_d n sk.t (lvl + 1) _ _ true hb (fun _ => rfl), if_pos rfl, add_zero']
        show ind ([ofN key, ofN 0, ofN (wc + (if bw && !b then 6 else 0))] = v) = _
        congr 4
        cases bw <;> cases b <;> rfl
    · rw [bitsRows_ind hK hr hi, S_cons, d_ind (d := indRow key p 0 true false lvl bw wc term) rfl, zero_add']
      exact S_bits_d n R lvl bw wc term hb ht

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

theorem S_bits_x {m : Bool} (n p lvl : Nat) (bw : Bool) (wc : Nat) (term : Bool) :
    S A "decx" v (bitsRows A key m n p lvl bw wc term) = 0 :=
  S_zero (fun d hd => x_zero (fun h => by have := (bits_shape n p lvl bw wc term d hd).1; omega))

theorem S_bits_d1 (n p lvl : Nat) (bw : Bool) (wc : Nat) (term : Bool) :
    S A "decd" v (bitsRows A key true n p lvl bw wc term) = 0 :=
  S_zero (fun d hd => by
    obtain ⟨hk, hm⟩ := bits_shape n p lvl bw wc term d hd
    have hk' : d.kind = 3 ∨ d.kind = 4 ∨ d.kind = 5 := by
      rcases hk with h | h | ⟨h, _⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    have h15 : 1 ≤ d.kind ∧ d.kind ≤ 5 := by
      rcases hk' with h | h | h <;> rw [h] <;> decide
    exact d_zero h15 (fun h => by rcases hk' with h' | h' | h' <;> rw [h'] at h <;> cases h) (fun _ => hm))

end Chains

end DecT

end Circuit
