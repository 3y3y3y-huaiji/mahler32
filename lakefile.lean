import Lake
open Lake DSL

package «mahler32» where
  -- Parity structure of the 3/2 Mahler recursion

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

@[default_target]
lean_lib «Mahler32» where
  globs := #[.andSubmodules `Mahler32]

/-- The advertised statement surface.  Its proofs are `sorry`, so it is deliberately not a
default target: `lake build` must stay warning-clean. -/
lean_lib «Challenge» where
  roots := #[`Challenge]

/-- The real proofs, imported from `Mahler32.Basic`.  Palomar builds this target by name
(`lake build Solution`), so it has to be a Lake target in its own right. -/
@[default_target]
lean_lib «Solution» where
  roots := #[`Solution]
