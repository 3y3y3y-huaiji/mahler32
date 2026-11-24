module

public import Mahler32.Base6LightCone
public import Mahler32.SyracuseGates
public import Mahler32.QuiverMonotone
public import Mahler32.ArnoldTongue5State
public import Mahler32.ArnoldTongue7State
public import Mahler32.DAGBoundedGap
public import Mahler32.TwoWorldPadeCriterion
public import Mahler32.Fib11Free
public import Mahler32.WalshZeroCorr
public import Mahler32.HInvariance
public import Mahler32.SyracuseBijection
public import Mahler32.ZeroEntropyCages
public import Mahler32.DiscreteFluidCertificates
public import Mahler32.Model94Obstructions
public import Mahler32.Model94GlobalDecay
public import Mahler32.RationalBaseDefs
public import Mahler32.GeneralPQDecay
public import Mahler32.ZeroEntropyAutomaton

/-!
# Zero-axiom core entry point (tasks 1–17)

This module imports all zero-axiom core task modules (including general `(p, q)` Fourier decay
and signed rational zero-entropy automata) and nothing else.  It neither imports the
conditional task-11 module nor `Mahler32.Basic`'s advertised surface, so `#print axioms` on it
is a faithful audit of the zero-axiom claim.  (`Mahler32.Basic` is still pulled in transitively
by the task modules that restate its results.)

The audit itself lives in `AuditAxioms.lean` and is run in CI.
-/
