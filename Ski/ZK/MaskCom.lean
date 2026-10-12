import Ski.ZK.MaskGen

/-!
# Commitments that hide

Plonky3's hiding PCS commits every matrix by a Merkle tree of salted
hashes (the hiding MMCS), and the proof carries the roots and the paths.
The view of `pcsCloseN_fri` leaves them out.  This file adds them, under
an explicit assumption: a commitment `Com d σ`, its salt `σ` drawn from
`NS` values, has one distribution whatever the data `d` it commits
(`ComHides`).  Then any PCS that hides exactly still hides exactly with
the commitments of whatever data it computes beside its view, the
simulator committing to fixed data (`PCSCloseN.commit`).

Scope.  `ComHides` is perfect hiding.  A salted hash hides only
computationally, or statistically in the random-oracle model; that step,
and Fiat–Shamir, stay assumptions outside this model.
-/

namespace Circuit

open ZKF

/-- **A commitment hides**: over its salt, the commitments of any two data
    have one distribution. -/
def ComHides {D C : Type} (NS : Nat) (Com : D → Nat → C) : Prop :=
  ∀ (d d' : D) (E : C → Bool), sumTo NS (fun σ => indB (E (Com d σ))) = sumTo NS (fun σ => indB (E (Com d' σ)))

/-- **Commitments beside an exactly hiding PCS keep it exact**: the PCS
    with the commitment of the data `Dat` it computes, the salt drawn
    beside its randomness, against the simulator with the commitment of
    fixed data `d0`. -/
theorem PCSCloseN.commit {PV D C : Type} {off : EF → String → EF} {NR NS : Nat}
    {tv : (String → EF) → EF → (Nat → Tup) → List EF} {pcs : (Nat → Tup) → EF → EF → Nat → PV}
    {psim : EF → EF → List EF → Nat → PV} (h : PCSCloseN off NR tv pcs psim 0) (Com : D → Nat → C)
    (hc : ComHides NS Com) (Dat : (Nat → Tup) → EF → EF → Nat → D) (d0 : D) :
    PCSCloseN off (NR * NS) tv (fun t α β r => (pcs t α β (r % NR), Com (Dat t α β (r % NR)) (r / NR)))
      (fun α β v r => (psim α β v (r % NR), Com d0 (r / NR))) 0 := by
  intro t α β Ev
  have hdiv : ∀ q r, r < NR → (r + NR * q) % NR = r ∧ (r + NR * q) / NR = q := fun q r hr => by
    have hpos : 0 < NR := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
    refine ⟨?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    · rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hr, Nat.zero_add]
  have split : ∀ g : PV → C → Nat, sumTo (NR * NS) (fun r => g (pcs t α β (r % NR)) (Com (Dat t α β (r % NR)) (r / NR))) =
      sumTo NS (fun σ => sumTo NR (fun r => g (pcs t α β r) (Com (Dat t α β r) σ))) := fun g => by
    rw [sumTo_split NR _ NS]
    exact sumTo_congr NS (fun q _ => sumTo_congr NR (fun r hr => by rw [(hdiv q r hr).1, (hdiv q r hr).2]))
  have splitS : ∀ g : PV → C → Nat, sumTo (NR * NS) (fun r => g (psim α β (tv (prefixOf α (off β)) β t) (r % NR))
      (Com d0 (r / NR))) = sumTo NS (fun σ => sumTo NR (fun r => g (psim α β (tv (prefixOf α (off β)) β t) r) (Com d0 σ))) :=
    fun g => by
    rw [sumTo_split NR _ NS]
    exact sumTo_congr NS (fun q _ => sumTo_congr NR (fun r hr => by rw [(hdiv q r hr).1, (hdiv q r hr).2]))
  have key : sumTo (NR * NS) (fun r => indB (Ev (pcs t α β (r % NR), Com (Dat t α β (r % NR)) (r / NR)))) =
      sumTo (NR * NS) (fun r => indB (Ev (psim α β (tv (prefixOf α (off β)) β t) (r % NR), Com d0 (r / NR)))) := by
    rw [split (fun v c => indB (Ev (v, c))), splitS (fun v c => indB (Ev (v, c)))]
    calc sumTo NS (fun σ => sumTo NR (fun r => indB (Ev (pcs t α β r, Com (Dat t α β r) σ))))
        = sumTo NR (fun r => sumTo NS (fun σ => indB (Ev (pcs t α β r, Com (Dat t α β r) σ)))) :=
          (sumTo_exch (fun σ r => indB (Ev (pcs t α β r, Com (Dat t α β r) σ))) NR NS)
      _ = sumTo NR (fun r => sumTo NS (fun σ => indB (Ev (pcs t α β r, Com d0 σ)))) :=
          sumTo_congr NR (fun r _ => hc (Dat t α β r) d0 (fun c => Ev (pcs t α β r, c)))
      _ = sumTo NS (fun σ => sumTo NR (fun r => indB (Ev (pcs t α β r, Com d0 σ)))) :=
          (sumTo_exch (fun r σ => indB (Ev (pcs t α β r, Com d0 σ))) NS NR)
      _ = _ := sumTo_congr NS (fun σ _ => by
          obtain ⟨h1, h2⟩ := h t α β (fun v => Ev (v, Com d0 σ))
          exact Nat.le_antisymm (by simpa using h1) (by simpa using h2))
  rw [key]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end Circuit
