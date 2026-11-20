import Lake
open Lake DSL

package «mahler32» where
  -- Parity structure of the 3/2 Mahler recursion

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

@[default_target]
lean_lib «Mahler32» where
  globs := #[.andSubmodules `Mahler32]
