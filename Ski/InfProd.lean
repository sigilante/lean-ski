import Ski.InfNF
import Ski.HnfCertFinal
open Term

/-!
# Which infinitary normal forms have an infinite left spine

With `HnfCert.q5` (S1.5): a node of `t^∞` with an infinite left spine exists exactly when the
39-state automaton puts `t` in the rejecting class 37.
-/

namespace InfNF
open HnfS HnfProd

/-- **S2, Cor. 10.**  No node of `t^∞` has an infinite left spine iff `cls t ≠ 37`. -/
theorem nodes_iff_cls {t : Term} (ht : PureS t) :
    (∀ u, Node t u → ¬ LeftInf u) ↔ cls t ≠ 37 :=
  (prod_iff_nodes ht).symm.trans (HnfCert.q5 ht)

end InfNF
