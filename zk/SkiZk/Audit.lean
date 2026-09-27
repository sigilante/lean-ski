import Lean
import SkiZk.Traversable
import SkiZk.Compute
import SkiZk.Memory
import SkiZk.Fingerprint

/-!
# The audit manifest of the zero-knowledge layer — build-enforced

This layer builds on Mathlib through Pure Nock, so its allow-list is Pure
Nock's: `{propext, Classical.choice, Quot.sound}` (`NockPure/AuditSpec.lean`).
The core keeps the narrower `{propext, Quot.sound}`; nothing here widens it.
A `sorry` (`sorryAx`) or a `native_decide` (`Lean.ofReduceBool`) fails the
build.
-/

open Lean Elab Command

namespace SkiZk.Audit

/-- Lean 4's three standard axioms, as in Pure Nock. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#audit_zk " ids:ident+ : command => do
  for id in ids do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let axs ← liftCoreM <| collectAxioms n
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
  throwError
  "AUDIT FAILURE for {n}\n \
  disallowed axioms: {bad.toList}\n \
  full footprint: {axs.toList}\n \
  allowed here: {allowed}"

end SkiZk.Audit

open SkiZk

-- Traversability (Pure Nock paper, Defs. RVT, traversable, state_data_separation)
#audit_zk traversable_of

-- SKI execution
#audit_zk head_ne_halt Fc_leaf Fc_node Fc_not_leaf rvt_node_single rvt_eval chain_rvt eval_rvt
  exec_unique execution_traversable execution_stateTraversable

-- SKI memory: terms as nouns
#audit_zk toNoun_injective toNoun_validates mtree_label Fm_leaf Fm_node rvt_state rvt_termNoun
  mtree_rvt termNoun_rvt mem_unique memory_traversable memory_stateTraversable

-- Fingerprints over BabyBear
#audit_zk leafList_toNoun_le cast_inj_le_two map_cast_inj dyckBits_inj toNoun_fieldNoun_ne
  term_collision_card_le babyBear_eq babyBear_prime two_ne_zero_of_charP
  babyBear_collision_card_le babyBear4_card babyBear4_collision_card_le
