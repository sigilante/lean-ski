import Ski.ZK.FriCommit
import Ski.ZK.FSMultiMixSud

/-!
# The Sudoku proofs with FRI in Plonky3's order as an opening

`FriCommit` builds a commit-phase strategy of FRI's shape in Plonky3's
order (`friCommitQCPf`).  Here it is the third opening of
`sud_interleaveD`'s Sudoku proofs, and the proofs' own FRI view is constant
(`sud_interleaveFRI`; `fri`, `Rb`, `Ro` constant, so that view component is
`((), ())`).  The opening reads the three earlier challenges (the
protocol's messages, by the layout of `m3` under `hr1`, `hr2`), then `k3`
layer reads at `φ3 M (Rᵢ, i)`, then its query seed; it takes no `c4`
argument.  The theorem holds for any `layer3`, `out3` and `φ3`: nothing
constrains them to fold, to stay below the table, or to avoid the proof's
own query point (a read landing there returns `c4`'s value).

Limits, beyond the instantiation:
- **Hiding.**  FRI's hiding moves from `sud_pcs`, which held for any `fri`,
  to the hypothesis `hp3`, which fixes the opening's data and asks the
  output's distribution over the salt alone to hide it.  Plonky3's FRI
  masks with codewords inside that data and publishes its final polynomial
  and query values, deterministic in the data; it appears not to meet
  `hp3`.  Worse, `hp3` must hold for every `c4` while the opening ignores
  `c4`: data agreeing at one challenge's points and data agreeing at
  another's are then linked, and by interpolation every two data of one
  shape are, so only an opening whose distribution does not depend on the
  data meets `hp3`.  Masks drawn from the opening's salt do not help, for
  the same reason; `MaskFri`'s shift keeps FRI's batched polynomial at the
  challenge `α`, not the masked datum.  A faithful version needs the
  opening to read `c4` (the rows FRI opens) or the PCS's hiding argument
  run across the proof.
- **Coverage.**  The opening sees slot 3's data only (the quotient table's
  chunks and codewords, through `pfPair`; the binder `d3` is unused); the
  trace polynomials and codewords of slots 1 and 2 and the matrices `Rb`
  carried are not FRI inputs, where Plonky3 batches them all.
- **Order.**  The opened trace and quotient rows (`S16 c4`, `S10 c4`,
  `SP c4`) still come from `c4`, drawn before the commit phase, while
  Plonky3 opens the rows FRI's queries pick.
- **Other.**  All three openings make `k3 + 4` reads; `αd`, `B4` and `NR2`
  remain in the error though they now feed nothing; and
  `sud_interleaveD` takes the full-transcript read-back (`hdg`), not
  `SudChallenger`'s weaker `hφsp`.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **The Sudoku proofs with a commit phase of FRI's shape, in Plonky3's
    order, as their third opening**: `sud_interleaveD` with the third opening reading the earlier
    challenges, `k3` layer reads, and the query seed last
    (`friCommitNxtC`, `friCommitQC_seed`), taking no `c4` argument, and the
    proof's own FRI view constant (`fri`, `Rb`, `Ro` trivial); its hiding is
    the hypothesis `hp3`. -/
theorem sud_interleaveFRI {P1 P2 P3 W1 W2 R3 : Type} {k3 kq : Nat} (φ1 : Nat → Nat → W1 → Nat) (nx1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → Nat × Nat × W1) (G1 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P1) (φ2 : Nat → Nat → W2 → Nat) (nx2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → Nat × Nat × W2) (G2 : Nat → Nat → Nat → List (List (List F)) → Nat → List Nat → P2) (φ3 : Nat → Nat → (Option R3 × Nat) → Nat) (layer3 : Nat → List Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → R3) (out3 : Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → List Nat → P3) (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) {n1 n2 n3 : Nat} {NS1 NS2 NS3 : ∀ ix : Nat, Nat} (Com1 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc1 : ∀ ix : Nat, ComHides (NS1 ix) (Com1 ix)) (hp1 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS1 ix) (Com1 ix) ((pfRd (Q4 * Q4) K2 Q4 K4 n1 (k3 + 4) (φ1 ix) (nx1 ix) (G1 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [0, 2, 4, 6])) (hr1 : ∀ ix : Nat, ∀ d σ, (Com1 ix) d σ < n1) (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS2 ix) (Com2 ix) ((pfRd (Q4 * Q4) K2 Q4 K4 n1 (k3 + 4) (φ2 ix) (nx2 ix) (G2 ix)) c4 T1 T2 T3 T4 M) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4 T1 T2 T3 T4 M, ComPfHides (NS3 ix) (Com3 ix) ((pfRd (Q4 * Q4) K2 Q4 K4 n1 (k3 + 4) (φ3 ix) ((fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) ix) ((fun ix => fun _ M d σ l => out3 ix M d σ l) ix)) c4 T1 T2 T3 T4 M) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F))) (dg : Nat → Nat) (hdg : ∀ ix m w, dg (φ ix m w) = m % n1) (δs : Nat → Nat) (hsp1 : ∀ ix d v, sumTo (NS1 ix) (fun σ => indB (decide (Com1 ix d σ = v))) ≤ δs ix) (isQ : Nat → Bool) (nxtQ : Nat → List Nat → Nat × Nat × Unit) :
    ∀ n, ZKBT (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n) (smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).sm 2) n)
      (scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n)
      (rvPowD (mixRv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ
        (fun i => read4T (Q4 * Q4) K2 Q4 K4 ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).m1 ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).m2 ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).m3 ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).q ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).out)) n)
      (pgPowD (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).pts) (fun _ c => c)) n)
      (svPowDT (pgRd (Q4 * Q4) K2 Q4 K4 (fun i => !isQ i) (fun i => ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).pts) (fun _ c => c))
        (mixSv (Q4 * Q4) K2 Q4 K4 kq isQ nxtQ (fun i => ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).sv)) n)
      (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun i => ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun i => cond (isQ i) 0 ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).ε)
        (fun n => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun i => ((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) i).sm 2) n
          (fun _ => rSum (fun i => cond (isQ i) kq (4 + 3 * (k3 + 4))) n *
            cond (isQ n) 0 (((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) n).NS * (((sudDD off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 (fun _ _ _ _ _ => ()) NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) NS1 NS2 NS3 n1 n2 n3 Com1 Com2 Com3 (k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l)) n).NR * (Q4 ^ 2 * δs n))))))) n) :=
  sud_interleaveD (V := Unit) (Wv := Unit) (W3 := Option R3 × Nat) (kr := k3 + 4) φ1 nx1 G1 φ2 nx2 G2 φ3 (fun ix => friCommitNxtC n1 n2 (fun _ => layer3 ix)) (fun ix => fun _ M d σ l => out3 ix M d σ l) off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ hS16 hS10 hSP hsz16 hsz hszP αd hB4 (fun _ _ _ _ _ => ()) hncw NR2 (fun _ _ _ _ _ => ([] : List (EF → EF))) (fun _ _ _ _ _ => ()) Com1 hc1 hp1 hr1 d1 Com2 hc2 hp2 hr2 d2 Com3 hc3 hp3 hr3 d3 dg hdg δs hsp1 isQ nxtQ

end

end Circuit
