import Ski.ZK.ROMMerkleOpen
import Ski.ZK.ROMFamily

/-!
# The oracle-commitment theorems' hypotheses, met

The kernel checks a theorem's proof, not that its hypotheses can hold
together; two hypotheses of this line of work once could not, and the
theorems over them said nothing.  Here each new hypothesis shape is met with
small parameters that give a real bound (`s = 1`, `k ≥ 1`, `L = 2`), the
positions reading the data and the statement index, and each set is fed to
the first lemma that consumes it: the single commitment (`posW`, into
`pfR_hidesA`, `s k / NSh = 1/8`), several hidden leaves (`psW`, into
`pfRL_hidesA`, `2/8`), a Merkle tree's leaves with one opened (`posM`, into
`pfM_hidesA`, the unopened leaf's data read), the query hash keeping the
first commitment's digit across statements (`φW`), and a family's
per-statement positions (`posF`).
-/

set_option autoImplicit false
namespace Circuit
open ZKF

/-- injective on the salt range ⇒ spread ≤ 1 -/
theorem inj_le_one (N : Nat) (g : Nat → Nat)
    (hg : ∀ x y, x < N → y < N → g x = g y → x = y) (v : Nat) :
    sumTo N (fun x => indB (decide (g x = v))) ≤ 1 := by
  by_cases h : ∃ x0, x0 < N ∧ g x0 = v
  · obtain ⟨x0, hx0, e0⟩ := h
    refine Nat.le_trans (sumTo_mono _ (fun x hx => ?_)) (sumTo_indEq x0 N).1
    by_cases e : g x = v
    · have hx : x = x0 := hg x x0 hx hx0 (e.trans e0.symm)
      have h1 : indB (decide (x = x0)) = 1 := by simp [hx, indB]
      rw [h1]; exact indB_le _
    · simp [e, indB]
  · have hz : sumTo N (fun x => indB (decide (g x = v))) = sumTo N (fun _ => 0) :=
      sumTo_congr _ (fun x hx => by
        have : g x ≠ v := fun e => h ⟨x, hx, e⟩
        simp [this, indB])
    rw [hz, sumTo_const]; simp

/-! ### W1: ROMHide/ROMRounds/ROMInst/ROMMulti shape (hpos, hs), pos depends on d.
    NSh = n = 8, s = 1, k = 1: error s k / NSh = 1/8. -/
def posW (d σo σh : Nat) : Nat := (d + σo + σh) % 8

theorem hposW : ∀ d σo σh, posW d σo σh < 8 := fun _ _ _ => Nat.mod_lt _ (by decide)
theorem hsW : ∀ d σo v, sumTo 8 (fun σh => indB (decide (posW d σo σh = v))) ≤ 1 :=
  fun d σo v => inj_le_one 8 _ (fun x y hx hy e => by simp only [posW] at e; omega) v

-- the hypotheses feed the theorems at those parameters
example : ComPfHidesA (8 * (1 * 2 ^ 8)) (1 * (2 ^ 8 * (2 * (1 * 1)))) (comR 2 8 1 posW)
    (pfR 2 8 1 1 posW (fun d : Nat => d) (fun o _ => o) (fun _ _ _ => 0)) (fun d : Nat => d) :=
  pfR_hidesA (K := 2) (n := 8) (NSh := 8) (NSo := 1) (s := 1) (k := 1) (by decide) posW hposW
    (fun d : Nat => d) (fun o _ => o) hsW (fun _ _ _ => 0)

/-! ### W2: ROMMerkle with L = 2 (romMerkle_sat covers only L = 1), d-dependent.
    NSh = 8, n = 16, s = 1: error L s k / NSh = 2/8 at k = 1. -/
def psW (d σo σh : Nat) : List Nat := [2 * ((d + σo + σh) % 8), 2 * ((d + σo + σh) % 8) + 1]

theorem hndW : ∀ d σo σh, (psW d σo σh).Nodup := fun d σo σh => by
  simp only [psW, List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
  omega
theorem hlenW : ∀ d σo σh, (psW d σo σh).length = 2 := fun _ _ _ => rfl
theorem hltW : ∀ d σo σh, ∀ p ∈ psW d σo σh, p < 16 := fun d σo σh p hp => by
  simp only [psW, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with e | e <;> subst e <;> omega
theorem hsLW : ∀ d σo l, l < 2 → ∀ v, sumTo 8 (fun σh => indB (decide ((psW d σo σh).getD l 0 = v))) ≤ 1 := by
  intro d σo l hl v
  rcases (show l = 0 ∨ l = 1 by omega) with e | e <;> subst e
  · exact inj_le_one 8 _ (fun x y hx hy e => by simp only [psW, List.getD_cons_zero] at e; omega) v
  · exact inj_le_one 8 _ (fun x y hx hy e => by simp only [psW, List.getD_cons_succ, List.getD_cons_zero] at e; omega) v

example := pfRL_hidesA (K := 2) (n := 16) (NSh := 8) (NSo := 1) (L := 2) (s := 1) (k := 1) (by decide) psW
  hndW hlenW hltW hsLW (fun d : Nat => d) (fun o _ => o) (fun _ _ _ => 0)

/-! ### W3: ROMMerkleOpen, the commitment depending on the unopened leaf's data.
    L = 2, leaf 0 opened, NSl = 8, n = 16, s = 1: error UL·2sk/NSl = 2/8 at k = 1.
    (merkleOpen_sat's pos ignores d.) -/
def posM (d : Nat × Nat) (l a : Nat) : Nat := l % 2 + 2 * ((a + (if l = 0 then d.1 else d.2)) % 8)
def isOM (l : Nat) : Bool := l == 0

theorem hdistM : ∀ d l l' a b, l < 2 → l' < 2 → l ≠ l' → posM d l a ≠ posM d l' b := by
  intro d l l' a b hl hl' hne e
  simp only [posM] at e; omega
theorem hltM : ∀ d l a, l < 2 → posM d l a < 16 := by
  intro d l a hl; simp only [posM]; omega
theorem hsM : ∀ d l v, sumTo 8 (fun x => indB (decide (posM d l x = v))) ≤ 1 :=
  fun d l v => inj_le_one 8 _ (fun x y hx hy e => by simp only [posM] at e; split at e <;> omega) v
theorem hposOM : ∀ d d' : Nat × Nat, d.1 = d'.1 → ∀ l a, isOM l = true → posM d l a = posM d' l a := by
  intro d d' h l a hO
  have : l = 0 := by simpa [isOM] using hO
  subst this; simp [posM, h]
-- the commitment really reads the unopened leaf's data
example : posM (0, 0) 1 0 ≠ posM (0, 1) 1 0 := by decide

example := pfM_hidesA (K := 2) (n := 16) (NSl := 8) (L := 2) (k := 1) (s := 1) (by decide) (by decide) posM
  hdistM hltM hsM isOM (fun d : Nat × Nat => d.1) hposOM (fun o _ => o) (fun _ _ _ => 0)

/-! ### W4: the query hash hypotheses hφ, hφs (families and fs_open4_two/pow), non-constant in w
    and in the statement index.  n1 = KQ = 8, T = 8, N4 = 64. -/
abbrev Wt := Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF)))
def wh (w : Wt) : Nat := (w.map (fun x => x.1.length + x.2.1.length)).getD 0
def φW (ix : Nat) (m : Nat) (w : Wt) : Nat := m % 8 + 8 * ((ix + m / 8 + wh w) % 8)

theorem hφW : ∀ ix : Nat, ∀ m w, φW ix m w < 64 := by
  intro ix m w; simp only [φW]; omega
theorem hφsW : ∀ i j m w m' w', φW i m w = φW j m' w' → m % 8 = m' % 8 := by
  intro i j m w m' w' e; simp only [φW] at e; omega
example : φW 0 0 none ≠ φW 1 0 none := by decide
example : φW 0 0 none ≠ φW 0 8 none := by decide

/-! ### W5: the families' per-statement ROM hypotheses (ROMFamily), index-dependent. -/
def posF (ix : Nat) (d : List (List (List F))) (σo σh : Nat) : Nat := (ix + d.length + σo + σh) % 8
theorem hposF : ∀ ix d σo σh, posF ix d σo σh < (fun _ => 8) ix := fun _ _ _ _ => Nat.mod_lt _ (by decide)
theorem hsF : ∀ ix d σo v, sumTo ((fun _ => 8) ix) (fun σh => indB (decide (posF ix d σo σh = v))) ≤ (fun _ => 1) ix :=
  fun ix d σo v => inj_le_one 8 _ (fun x y hx hy e => by simp only [posF] at e; omega) v

/-! ### W6: the pre-ROM family hypotheses (FSQueryAbs *_powD): hr1, hc1, hsp with δs = 1. -/
example : ∀ ix : Nat, ComHides (8 * (1 * 2 ^ 8) * 2) (comI 2 8 1 (fun (_ : List (List (List F))) σo σh => posF ix [] σo σh)) :=
  fun ix => comI_hides (K := 2) (n := 8) (by decide) _ (fun _ _ _ => hposF ix [] _ _)

end Circuit
