import Lean
import Ski.S10Frame
import Ski.S10Closure

/-!
# Axiom gate for the S10 mechanization (stand-alone)

The same check as `#audit_clean` in `Ski/Audit.lean` (allow-list `{propext, Quot.sound}`), in a
module that imports only the S10 modules.  The root module `Ski` imports this module, so the
default `lake build` runs the gate (as for `S11Audit`).
-/

open Lean Elab Command

namespace S10.Audit

def allowed : List Name := [``propext, ``Quot.sound]

elab "#s10_audit_clean " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "AUDIT FAILURE for {n}\n disallowed axioms: {bad.toList}\n full footprint: {axs.toList}"

end S10.Audit

-- M0: S10Frame (frames, firing, locality, checked runs, the bridge to head reduction)
#s10_audit_clean
  S10.args S10.tw S10.F S10.fstep S10.frun S10.seat S10.FiresAt S10.Silent S10.Eternal
  S10.Quiet S10.psum S10.psum_const S10.fstep_append S10.frun_append S10.frun_add
  S10.fstep_len S10.frun_succ_len S10.seat_append S10.seat_len S10.frun_le S10.frun_lt_len
  S10.Quiet.of_nil S10.Quiet.nil S10.Quiet.refl S10.Quiet.trans S10.Quiet.fires
  S10.Quiet.silent_eternal S10.silent_eternal_append S10.FiresAt.not_silent
  S10.FiresAt.unique S10.FiresAt.append S10.isTw8 S10.isF S10.isF_F S10.ne_F_of_isF
  S10.qrun S10.qrun_sound S10.Quiet.of_qrun S10.Quiet.of_qrun_take S10.firesAt_of_qrun
  S10.QuietD S10.QuietD.trans S10.QuietD.fires S10.QuietD.cast S10.step?_foldl
  S10.step?_frame S10.fstep_pure S10.frun_pure S10.iter_foldl S10.iter_eq_frun
  S10.args_foldl S10.TFiresAt S10.TFiresAt.of_firesAt

-- M1: S10Closure (clocks; Seq, Iter, Loop, Cond, Reindex; clock_closure; the corollary)
#s10_audit_clean
  S10.Clock S10.Clock.fires_iff S10.Clock.firesAt_T S10.seq_fires S10.seq_quiet S10.Clock.seq
  S10.iter_fires S10.Clock.iter S10.loop_frames S10.loop_silent_eternal S10.Clock.cond
  S10.Clock.reindex S10.clock_closure

/-- info: 'S10.clock_closure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms S10.clock_closure
