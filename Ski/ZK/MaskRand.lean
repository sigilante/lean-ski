import Ski.ZK.MaskChunk

/-!
# Openings of independent randomness

Plonky3's hiding PCS commits, beside the trace and the quotient chunks,
columns that hold nothing but randomness: the random codeword columns
appended to every committed matrix (`with_random_cols`), and the
randomization polynomial's columns (`get_opt_randomization_poly_commitment`).
The proof opens them at the opening points like any column, and stores
their values (`opened_values_rand`).  Those values are drawn
independently of everything else in the view, so adding them keeps the
simulation exact (`PCSCloseN.indep`): the simulator draws them itself.
`pcsRand` instantiates it with the openings of uniform polynomials over
`F` at the query points and at the out-of-domain points
(`pcsCloseN_rand`).

Scope.  This covers these columns' openings.  Their other role, masking
the polynomial FRI tests, is `Ski/ZK/MaskFri.lean`'s (`pcsCloseN_fri`,
`pcsCloseN_friR`).
-/

namespace Circuit

open ZKF

/-- A sum over `[0, B m)`, by the remainder and the quotient. -/
theorem sumTo_split (B : Nat) (f : Nat → Nat) : ∀ m, sumTo (B * m) f = sumTo m (fun q => sumTo B (fun r => f (r + B * q)))
  | 0 => by rw [Nat.mul_zero]; rfl
  | m + 1 => by
    rw [Nat.mul_succ, sumTo_app, sumTo_split B f m, sumTo_succ,
      sumTo_congr (f := fun r => f (B * m + r)) (g := fun r => f (r + B * m)) B
        (fun r _ => by show f (B * m + r) = f (r + B * m); rw [Nat.add_comm])]

section
variable {PV PW : Type} (pcs : (Nat → Tup) → EF → EF → Nat → PV) (psim : EF → EF → List EF → Nat → PV)
  (NR : Nat) (g : EF → EF → Nat → PW)

/-- The PCS's view with a second view `g` of independent randomness: the
    randomness `r` read as `r % NR` for the PCS and `r / NR` for `g`. -/
def pcsIndep (t : Nat → Tup) (α β : EF) (r : Nat) : PV × PW := (pcs t α β (r % NR), g α β (r / NR))

/-- Its simulator draws the second view itself. -/
def psimIndep (α β : EF) (v : List EF) (r : Nat) : PV × PW := (psim α β v (r % NR), g α β (r / NR))
end

/-- **Independent randomness keeps the simulation exact**: a PCS that
    meets `PCSCloseN` with `ε = 0`, with a second view drawn from `NR2`
    independent values beside it, meets it too. -/
theorem PCSCloseN.indep {PV PW : Type} {off : EF → String → EF} {NR NR2 : Nat}
    {tv : (String → EF) → EF → (Nat → Tup) → List EF} {pcs : (Nat → Tup) → EF → EF → Nat → PV}
    {psim : EF → EF → List EF → Nat → PV} (h : PCSCloseN off NR tv pcs psim 0) (g : EF → EF → Nat → PW) :
    PCSCloseN off (NR * NR2) tv (pcsIndep pcs NR g) (psimIndep psim NR g) 0 := by
  intro t α β Ev
  have hdiv : ∀ q r, r < NR → (r + NR * q) % NR = r ∧ (r + NR * q) / NR = q := fun q r hr => by
    have hpos : 0 < NR := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
    refine ⟨?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    · rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hr, Nat.zero_add]
  have key : sumTo (NR * NR2) (fun r => indB (Ev (pcsIndep pcs NR g t α β r))) =
      sumTo (NR * NR2) (fun r => indB (Ev (psimIndep psim NR g α β (tv (prefixOf α (off β)) β t) r))) := by
    rw [sumTo_split NR _ NR2, sumTo_split NR _ NR2]
    refine sumTo_congr NR2 (fun q _ => ?_)
    have e1 : sumTo NR (fun r => indB (Ev (pcsIndep pcs NR g t α β (r + NR * q)))) =
        sumTo NR (fun r => indB (Ev (pcs t α β r, g α β q))) :=
      sumTo_congr NR (fun r hr => by
        show indB (Ev (pcs t α β ((r + NR * q) % NR), g α β ((r + NR * q) / NR))) = _
        rw [(hdiv q r hr).1, (hdiv q r hr).2])
    have e2 : sumTo NR (fun r => indB (Ev (psimIndep psim NR g α β (tv (prefixOf α (off β)) β t) (r + NR * q)))) =
        sumTo NR (fun r => indB (Ev (psim α β (tv (prefixOf α (off β)) β t) r, g α β q))) :=
      sumTo_congr NR (fun r hr => by
        show indB (Ev (psim α β _ ((r + NR * q) % NR), g α β ((r + NR * q) / NR))) = _
        rw [(hdiv q r hr).1, (hdiv q r hr).2])
    rw [e1, e2]
    obtain ⟨h1, h2⟩ := h t α β (fun v => Ev (v, g α β q))
    exact Nat.le_antisymm (by simpa using h1) (by simpa using h2)
  rw [key]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- **The random columns' openings**: `k` uniform polynomials over `F` of
    `n` coefficients each, the randomness `r`'s digits, at the query points
    `S` and the out-of-domain points `Z`. -/
def randOpen (S : List F) (Z : List EF) (n : Nat) : Nat → List F → List (List F × List EF)
  | 0, _ => []
  | k + 1, rs => (S.map (fun s => fval s (rs.take n)), Z.map (fun z => fvalE z (rs.take n))) ::
      randOpen S Z n k (rs.drop n)

/-- The masked PCS with its quotients and their chunks, and the random
    columns' openings beside it. -/
def pcsRand (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF) (qs : List QGroup)
    (ks : List Nat) (cols : (Nat → Tup) → EF → EF → List (List (List F))) (csets : List CSet)
    (qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F)) (S : List F) (Z : List EF) (n k : Nat) :=
  pcsIndep (pcsChunk off tv qs ks cols csets qd) (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets))
    (fun _ _ r => randOpen S Z n k (digitsF (k * n) r))

def psimRand (qs : List QGroup) (ks : List Nat) (csets : List CSet) (S : List F) (Z : List EF) (n k : Nat) :=
  psimIndep (psimChunk qs ks csets) (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets))
    (fun _ _ r => randOpen S Z n k (digitsF (k * n) r))

/-- **The PCS with the random columns' openings hides exactly**: under
    `pcsCloseN_chunks`'s hypotheses, adding the openings of `k` uniform
    polynomials (the random codeword and randomization columns) keeps
    `PCSCloseN` with `ε = 0`. -/
theorem pcsCloseN_rand {qs : List QGroup} {ks : List Nat} {cols : (Nat → Tup) → EF → EF → List (List (List F))}
    {csets : List CSet} {qd : (Nat → Tup) → EF → EF → List F → List (List (List F) × List F)}
    (hok : ∀ q ∈ qs, q.OK) (hks : ks.length = qs.length)
    (hcols : ∀ t α β, Shaped (qs.map QGroup.ext) (cols t α β) ∧ (cols t α β).map List.length = ks)
    (hcs : ∀ c ∈ csets, c.OK) (off : EF → String → EF) (tv : (String → EF) → EF → (Nat → Tup) → List EF)
    (hrec : ∀ t α β ms, RecOK csets (qd t α β ms)
      (fun c => c.JS α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms))
      (fun c => c.Jζ α β (tv (prefixOf α (off β)) β t) (openMulti (qs.map QGroup.ext) (cols t α β) ms)))
    (S : List F) (Z : List EF) (n k : Nat) :
    PCSCloseN off (P ^ (mtotal (qs.map QGroup.ext) ks + ctot csets) * P ^ (k * n)) tv
      (pcsRand off tv qs ks cols csets qd S Z n k) (psimRand qs ks csets S Z n k) 0 :=
  (pcsCloseN_chunks hok hks hcols hcs off tv hrec).indep _

end Circuit
