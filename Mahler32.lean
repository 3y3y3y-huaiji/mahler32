module

public import Mahler32Core
public import Mahler32Conditional.AlgebraicPairBranch

/-!
# The Mahler `3/2` recursion

Complete entry point of the repository:

* `Mahler32Core` — the zero-axiom core (tasks 1–10) on top of `Mahler32.Basic`;
* `Mahler32Conditional.AlgebraicPairBranch` — task 11, which declares the single explicit
  axiom `schlickewei_subspace_Q3`.

The core is deliberately importable on its own (`import Mahler32Core`): the Palomar surface
(`Solution`) only depends on `Mahler32.Basic` and never sees the conditional axiom.
-/
