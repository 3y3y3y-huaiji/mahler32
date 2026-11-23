module

public import Mahler32.Base6LightCone
public import Mahler32.SyracuseGates
public import Mahler32.ArnoldTongue5State
public import Mahler32.ArnoldTongue7State
public import Mahler32.DAGBoundedGap
public import Mahler32.TwoWorldPadeCriterion
public import Mahler32.Fib11Free
public import Mahler32.WalshZeroCorr
public import Mahler32.HInvariance
public import Mahler32.SyracuseBijection

/-!
# Zero-axiom core entry point (tasks 1–10)

This module imports the ten core task modules and nothing else.  It neither imports the
conditional task-11 module nor `Mahler32.Basic`'s advertised surface, so `#print axioms` on it
is a faithful audit of the zero-axiom claim.

The audit itself lives in `AuditAxioms.lean` and is run in CI.
-/
