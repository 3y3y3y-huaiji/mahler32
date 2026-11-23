import Lake
open Lake DSL

package «mahler32» where
  -- Parity structure of the 3/2 Mahler recursion

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

/-- The zero-axiom core library: `Mahler32/Basic.lean` plus the eleven task modules
(ten of which live here; the conditional one is a separate library below).  The glob pulls in
every module under `Mahler32/`, so a newly added file cannot silently escape the build. -/
@[default_target]
lean_lib «Mahler32» where
  globs := #[.andSubmodules `Mahler32, .one `Mahler32Core]

/-- The advertised statement surface.  Its proofs are `sorry`, so it is deliberately not a
default target: `lake build` must stay warning-clean. -/
lean_lib «Challenge» where
  roots := #[`Challenge]

/-- The real proofs, imported from `Mahler32.Basic`.  Palomar builds this target by name
(`lake build Solution`), so it has to be a Lake target in its own right. -/
@[default_target]
lean_lib «Solution» where
  roots := #[`Solution]

/-- Conditional extension (task 11).  It is a *separate* library so that the one explicitly
declared axiom `schlickewei_subspace_Q3` can never leak into `Mahler32Core` or `Solution`.
CI verifies this library against the whitelist
`propext, Classical.choice, Quot.sound, schlickewei_subspace_Q3`. -/
lean_lib «Mahler32Conditional» where
  roots := #[`Mahler32Conditional.AlgebraicPairBranch]
