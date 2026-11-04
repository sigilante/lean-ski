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
  unfold ind; split <;> grind

section Rows
variable {A : List Cell} {d : DR} {v : List F}

-- decn

theorem n_bits (hk : d.kind = 3 ∨ d.kind = 4) : sendsT A d "decn" v = 0 := by
  rw [sendN]; simp only [ite_ind]
  rw [kc, ka, bF_f (by omega), bF_f (by omega)]
  grind

theorem n_atom (hk : d.kind = 2) : sendsT A d "decn" v = -ind ([ofN d.key, ofN d.p, ofN d.ro] = v) := by
  rw [sendN]; simp only [ite_ind]
  rw [kc, ka, bF_f (by omega), bF_t hk]
  grind

theorem n_cell (hk : d.kind = 1) {hh tt : Nat} (h21 : (sl A d 21).2.2.2 = hh) (h23 : (sl A d 23).2.2.2 = tt) :
    sendsT A d "decn" v = -ind ([ofN d.key, ofN d.p, ofN d.ro] = v) +
      (ind ([ofN d.key, ofN hh, ofN 2 - h0 d] = v) + ind ([ofN d.key, ofN tt, ofN 2] = v)) := by
  rw [sendN]; simp only [ite_ind]
  rw [kc, ka, bF_t hk, bF_f (by omega), h21, h23]
  grind

-- decb

theorem b_nil (hk : d.kind = 4) :
    sendsT A d "decb" v = -ind ([ofN d.key, ofN d.p, bF d.m, ofN d.lvl, bF d.bw, ofN d.wc] = v) := by
  rw [sendB]; simp only [ite_ind]
  rw [ka, ks, kn, bF_f (by omega), bF_f (by omega), bF_t hk]
  ; grind

theorem b_consL (hk : d.kind = 3) (hl : d.last = true) :
    sendsT A d "decb" v = -ind ([ofN d.key, ofN d.p, bF d.m, ofN d.lvl, bF d.bw, ofN d.wc] = v) := by
  rw [sendB]; simp only [ite_ind]
  rw [ka, ks, kn, bF_f (by omega), bF_t hk, bF_f (by omega)]
  rw [vL, hl]
  rw [show (1 - bF true : F) = 0 by decide]; grind

theorem b_cons (hk : d.kind = 3) (hl : d.last = false) {t : Nat} (h14 : (sl A d 14).2.2.2 = t) :
    sendsT A d "decb" v = -ind ([ofN d.key, ofN d.p, bF d.m, ofN d.lvl, bF d.bw, ofN d.wc] = v) +
      ind ([ofN d.key, ofN t, bF d.m, ofN (d.lvl + 1), bF (d.bw && !d.bit),
        ofN (d.wc + 6 * (if d.bw then 1 else 0))] = v) := by
  rw [sendB]; simp only [ite_ind]
  rw [ka, ks, kn, bF_f (by omega), bF_t hk, bF_f (by omega), h14]
  have e1 : ofN (d.lvl + 1) = ofN d.lvl + 1 := by rw [ofN_add]; rfl
  have e2 : bF (d.bw && !d.bit) = vBW d * (1 - vBIT d) := by
    simp only [vBW, vBIT]; cases d.bw <;> cases d.bit <;> decide
  have e3 : ofN (d.wc + 6 * (if d.bw then 1 else 0)) = ofN d.wc + ofN 6 * vWR d := by
    simp only [vWR, vDROP, vBW, vBIT, vL, hl, ofN_add, ofN_mul]
    cases d.bw <;> cases d.bit <;> rfl
  rw [e1, e2, e3]
  rw [vL, hl]
  rw [show (1 - bF false : F) = 1 by decide]; grind

theorem b_atom (hk : d.kind = 2) {b : Nat} (h22 : (sl A d 22).2.2.2 = b) :
    sendsT A d "decb" v = ind ([ofN d.key, ofN b, bF (d.ro != 1), ofN 0, bF (d.ro == 1), ofN 0] = v) := by
  rw [sendB]; simp only [ite_ind]
  rw [ka, ks, kn, bF_t hk, bF_f (by omega), bF_f (by omega), h22]
  have e1 : h1 d = bF (d.ro == 1) := by
    unfold h1
    by_cases h : d.ro = 1
    · rw [bF_t (P := (d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 1) (by omega), h]; rfl
    · rw [bF_f (P := (d.kind = 1 ∨ d.kind = 2) ∧ d.ro = 1) (by omega), beq_false_of_ne h]; rfl
  have e2 : (1 : F) - bF (d.ro == 1) = bF (d.ro != 1) := by
    unfold bne; cases d.ro == 1 <;> decide
  rw [e1, e2]
  grind

theorem b_cell (hk : d.kind = 1) : sendsT A d "decb" v = 0 := by
  rw [sendB]; simp only [ite_ind]
  rw [ka, ks, kn, bF_f (by omega), bF_f (by omega), bF_f (by omega)]
  grind

-- decd

theorem d_zero (hk : 1 ≤ d.kind ∧ d.kind ≤ 4) (h1' : d.kind = 1 → d.ro ≠ 0 ∧ d.ro ≠ 1)
    (h3 : d.kind = 3 ∨ d.kind = 4 → d.m = true) : sendsT A d "decd" v = 0 := by
  rw [sendD]; simp only [ite_ind]
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
  grind

theorem d_nil (hk : d.kind = 4) (hm : d.m = false) : sendsT A d "decd" v = ind ([ofN d.key, ofN 1, ofN d.wc] = v) := by
  rw [sendD]; simp only [ite_ind]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show kc d * h1 d = 0 by unfold kc; rw [bF_f (by omega), zero_mul'],
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], show kn d = 1 by unfold kn; rw [bF_t hk], vM, hm]
  rw [show (1 - bF false : F) = 1 by decide]; grind

theorem d_consL (hk : d.kind = 3) (hm : d.m = false) (hl : d.last = true) :
    sendsT A d "decd" v = ind ([ofN d.key, ofN 0, ofN (d.wc + (if d.bw && !d.bit then 6 else 0))] = v) := by
  rw [sendD]; simp only [ite_ind]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show kc d * h1 d = 0 by unfold kc; rw [bF_f (by omega), zero_mul'],
    show ks d = 1 by unfold ks; rw [bF_t hk], show kn d = 0 by unfold kn; rw [bF_f (by omega)], vM, hm, vL, hl]
  have e3 : ofN (d.wc + (if d.bw && !d.bit then 6 else 0)) = ofN d.wc + ofN 6 * vWR d := by
    simp only [vWR, vDROP, vBW, vBIT, vL, hl, ofN_add]
    cases d.bw <;> cases d.bit <;> rfl
  rw [e3]
  rw [show (1 - bF false : F) = 1 by decide, show bF true = 1 from rfl]; grind

theorem d_cons (hk : d.kind = 3) (hl : d.last = false) : sendsT A d "decd" v = 0 := by
  rw [sendD]; simp only [ite_ind]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show kc d * h1 d = 0 by unfold kc; rw [bF_f (by omega), zero_mul'],
    show kn d = 0 by unfold kn; rw [bF_f (by omega)], vL, hl]
  rw [show bF false = 0 from rfl]; grind

theorem d_cellH (hk : d.kind = 1) (hro : d.ro = 1) : sendsT A d "decd" v = ind ([ofN d.key, ofN 1, ofN 0] = v) := by
  rw [sendD]; simp only [ite_ind]
  rw [show vSUB d = 0 by unfold vSUB h0; rw [bF_f (by omega), mul_zero'],
    show kc d * h1 d = 1 by unfold kc h1; rw [bF_t hk, bF_t (by omega)]; rfl,
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], show kn d = 0 by unfold kn; rw [bF_f (by omega)]]
  grind

theorem d_cellS (hk : d.kind = 1) (hro : d.ro = 0) :
    sendsT A d "decd" v = -ind ([ofN d.key, bF d.err, ofN d.wc] = v) := by
  rw [sendD]; simp only [ite_ind]
  rw [show vSUB d = 1 by unfold vSUB kc h0; rw [bF_t hk, bF_t (by omega)]; rfl,
    show kc d * h1 d = 0 by unfold h1; rw [bF_f (by omega), mul_zero'],
    show ks d = 0 by unfold ks; rw [bF_f (by omega)], show kn d = 0 by unfold kn; rw [bF_f (by omega)]]
  grind

-- decx

theorem x_zero (hk : d.kind = 1 ∨ d.kind = 2 → d.ro ≠ 0) : sendsT A d "decx" v = 0 := by
  rw [sendX]; simp only [ite_ind]
  have : h0 d = 0 := by
    unfold h0
    rw [bF_f]; intro ⟨h1, h2⟩; exact hk h1 h2
  rw [show vSUB d = 0 by unfold vSUB; rw [this, mul_zero'], this, mul_zero']
  simp only [zero_mul', add_zero']

theorem x_cell (hk : d.kind = 1) (hro : d.ro = 0) : sendsT A d "decx" v =
    ind ([ofN d.key, ofN d.key + ofN 12 * bF d.err, ofN d.key + ofN 12 + ofN d.wc + ofN 3 * bF d.err] = v) := by
  rw [sendX]; simp only [ite_ind]
  rw [show vSUB d = 1 by unfold vSUB kc h0; rw [bF_t hk, bF_t (by omega)]; rfl,
    show ka d * h0 d = 0 by unfold ka; rw [bF_f (by omega), zero_mul']]
  grind

theorem x_atom (hk : d.kind = 2) (hro : d.ro = 0) : sendsT A d "decx" v =
    ind ([ofN d.key, ofN d.key, ofN d.key + ofN 3] = v) := by
  rw [sendX]; simp only [ite_ind]
  rw [show vSUB d = 0 by unfold vSUB kc; rw [bF_f (by omega), zero_mul'],
    show ka d * h0 d = 1 by unfold ka h0; rw [bF_t hk, bF_t (by omega)]; rfl]
  grind

end Rows

end DecT

end Circuit
