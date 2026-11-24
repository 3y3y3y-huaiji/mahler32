# Parity structure of the 3/2 Mahler recursion, in Lean 4

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/lean_build.yml)
[![Independent kernel (nanoda)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/independent-kernel.yml/badge.svg)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/independent-kernel.yml)
[![Papers (LaTeX)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/papers.yml/badge.svg)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/papers.yml)
[![Release](https://img.shields.io/github/v/release/3y3y3y-huaiji/mahler32?label=Release)](https://github.com/3y3y3y-huaiji/mahler32/releases/latest)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24491265.svg)](https://doi.org/10.5281/zenodo.24491265)
[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.36.0-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0008--2312--6913-A6CE39?logo=orcid&logoColor=white)](https://orcid.org/0009-0008-2312-6913)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)
[![LLM Assisted](https://img.shields.io/badge/Formalized_with-LLM_Assistance-blueviolet.svg)](#ai--llm-assistance-disclosure)

A Lean 4 / Mathlib formalization of the arithmetic structure behind the parity sequence of

```
a(1) = 1,   a(n+1) = a(n) + ⌈a(n)/2⌉ = ⌈3·a(n)/2⌉
```

i.e. [OEIS A061419](https://oeis.org/A061419), whose parity is
[OEIS A205083](https://oeis.org/A205083) (shifted by one index: `A205083(n) = a(n+1) mod 2`).
The recurrence is the `3/2`-dynamical system of Mahler (1968); `a(n) = ⌊K·(3/2)^n⌋` with
`K = 1.0815136685898…`, but `K(3)` is *not* a Mahler Z-number, so the parity sequence is not
governed by that theorem.

Everything below is machine-checked: **1046 lines (108 `#lint`-checked declarations), no `sorry`**,
and every core theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (some
3-adic window theorems use only `propext` and `Quot.sound`).

---

## What is proved

### 1. The one-step laws

| Theorem | Statement |
| :-- | :-- |
| `step_parity` | `step x % 2 = x / 2 % 2` — the next parity is the **second binary digit** of the current term |
| `step_mod_three` | `step x % 3 = 2 * (x % 2)` — hence `a n ≢ 1 (mod 3)` for `n ≥ 1` |
| `step_parity_hex` | the base-`6` two-digit local law `b₀' = (t₀ + b₁) % 2` |
| `a_mod_six` | `a (n+1) % 6 = 3·ε(n+1) + 2·ε(n)`: the last base-`6` digit is a **bijection** onto consecutive parity pairs, so it only takes `{0, 2, 3, 5}` |

`step_parity` is the reason base `6` is the right window and base `3` is not: `6 = 2·3` carries
one binary digit per digit, while in base `3` the parity is a global digit sum.

### 2. The information window (“the cliff”)

| Theorem | Statement |
| :-- | :-- |
| `step_shift` | `step (x + 2^(j+1)·t) = step x + 2^j·(3t)` |
| `step_pow_shift` | `step^[k] (x + 2^m·t) = step^[k] x + 2^(m-k)·(3^k·t)` for `k ≤ m` |
| `parity_window`, `parity_window_hex`, `a_parity_window` | `m` low binary (equivalently `m` low base-`6`) digits determine **exactly** the next `m` parities |
| `cliff_sharp` | the window is sharp: `0` and `6^m` agree modulo `6^m` yet differ in parity at step `m` |

Each iteration spends exactly one binary digit — so the last `m` base-`6` digits buy `m` steps
and not one more.

### 3. The base-3 two-state machine

Reading the base-`3` digits most significant first, appending `x % 2`, and dividing by `2` digit
by digit with a carry in `{0,1}` reproduces `⌈3x/2⌉`:

`run_spec : 2·val(quotient) + remainder = r·3^|L| + val L` (the long-division invariant, purely
algebraic — no bound on the digits is needed), and `ternary_machine` composes it with
`val (digits 3 x).reverse = x`.

### 4. The inverse branch and period doubling

| Theorem | Statement |
| :-- | :-- |
| `bstep` | `bstep y = (2y - 2y % 3)/3`, the base-`3` “undo one digit” rule |
| `step_bstep`, `bstep_step` | the branch and `step` are mutually inverse where defined |
| `bstep_pow_step`, `step_pow_bstep` | `k`-step round trip; the latter through the legality predicate `good k y` |
| `runRem_eq` | one-period state transition: `runRem B r = (r + ones B) % 2` |
| `runOut_two_blocks_odd/even` | odd count of odd digits flips the carry, even count returns it |
| `period_doubling` | odd count ⟹ `|B|` is **not** a period of the scan of `B ++ B` |
| `period_persists` | even count ⟹ `|B|` stays a period |

Note the primitivity caveat: the exact new period is `2p` for **primitive** blocks with an odd
number of `1`-digits (verified for every primitive block of length ≤ 4), while a non-primitive
block such as `111` (whose repeating value is `1/2`) behaves like its primitive root.

---

## The `2 ^ k` legal classes

| Theorem | Statement |
| :-- | :-- |
| `step_lt_succ`, `step_strictMono`, `step_pow_strictMono` | `step` and all its iterates are strictly monotone |
| `step_pow_two_pow` | `step^[k] (2^k) = 3^k` — the window boundary lands exactly on `3^k` |
| `good_step_pow` | every point of the `k`-th image is legal |
| `good_card` | **`\|{y < 3^k : good k y}\| = 2^k`** |

The count is proved by an explicit bijection rather than by a surjectivity argument on the digit
map: `x ↦ step^[k] x` maps `{x < 2^k}` onto `{y < 3^k : good k y}`. Membership uses
`step^[k] x < step^[k] (2^k) = 3^k`; injectivity is strict monotonicity; surjectivity sends a legal
`y` to `x = bstep^[k] y`, which satisfies `step^[k] x = y` by `step_pow_bstep` and `x < 2^k` by
monotonicity. `#eval` reproduces `1, 2, 4, 8, 16, 32` for `k = 0 … 5`.

---

## 5. Light-cone flip, 3-adic window, 11-free Fibonacci pruning, and Walsh zero correlation

| Group | Theorem | Statement |
| :-- | :-- | :-- |
| Light-cone & `F₂` split | `step_pow_add_six_pow` | `step^[k] (x + 6^k) = step^[k] x + 9^k` |
| | `light_cone_flip_hex` | `(step^[k] (x + 6^k)) % 2 ≠ (step^[k] x) % 2` |
| | `parity_linear_split` | `(step^[k] x) % 2 = ((step^[k] (x % 2^k)) % 2 + (x / 2^k) % 2) % 2` |
| 3-adic window | `bstep_mod_three_pow` | `bstep y % 3^j = bstep (y % 3^(j+1)) % 3^j` |
| | `good_mod_iff` | `good k y ↔ good k (y % 3^k)` |
| 11-free pruning | `good11Free_card` | `\|{y < 3^k : good11Free k y}\| = Nat.fib (k + 2)` |
| Walsh spectrum | `walsh_zero_of_bit_zero` | `u / 2^k % 2 = 0 → walsh k u = 0` |
| | `walsh_eq_two_mul_core` | `u / 2^k % 2 = 1 → walsh k u = 2 * walshCore k u` |

Because `parity_linear_split` separates bit `k` as a pure linear XOR summand, any linear mask
omitting bit `k` has Walsh correlation `0` (`50%` accuracy).  Adding the `11`-free condition
(forbidding consecutive odd backward steps) shrinks the legal residue classes modulo `3^k` from
`2^k` to `Nat.fib (k + 2)` (`#eval` checks `k = 0 … 5` give `[1, 2, 3, 5, 8, 13]`).

## Task modules and papers (2026-11)

The toolchain is pinned to the **latest release** pair, Lean `v4.36.0` / Mathlib `v4.36.0`
(`lean-toolchain`, `lakefile.lean`); no nightly or unreleased pins are used.

The following modules are built and audited (every path is checked for registration by
`scripts/verify_ssot.py`):

| Module | Machine-checked content |
| :-- | :-- |
| `Mahler32/Basic.lean` | the core parity development: one-step laws, information window and sharpness, base-3 transducer, inverse branch and period doubling, the `2^k` legal-class count, 11-free Fibonacci pruning and Walsh zero correlation |
| `Mahler32/Base6LightCone.lean` | task-sheet `step`/`iterStep`/`bstep`/`good`; light-cone flip and the 3-adic window (`light_cone_flip`, `good_mod_iff`) |
| `Mahler32/SyracuseGates.lean` | integer `3/2` step `zStep`; exact gates `g % 12 = 9`, `g % 256 = 9`, `g % 768 = 9` |
| `Mahler32/TwoWorldPadeCriterion.lean` | Archimedean–`2`-adic Padé discrepancy identity; uniqueness of agreement `two_world_iff`; integer engine `two_pow_dvd_eq_zero`; rational `√2` bounds; $\mathbb{R}\times\mathbb{Q}_2$ simultaneous evaluation (`two_world_ghost_bounds`, `no_eventually_periodic_94`, `repetition_exponent_bound`); mod-9 non-vanishing congruence criterion (`mod_nine_gate_rat`, `mod_nine_gate_b2`, `mod_nine_anti_misfire`) |
| `Mahler32/ArnoldTongue5State.lean` | the `5`-state count, **plus** exact windows where the real `T` branches stay in `[1/3, 11/15)` (`T_false_maps`, `T_true_maps`) |
| `Mahler32/ArnoldTongue7State.lean` | the `7`-state count, **plus** the exact `T` windows on `[7/24, 17/24)` |
| `Mahler32/DAGBoundedGap.lean` | bounded gap; exact hitting set `S7_iff_hits`; the `g + 128` carry branch (`zStepNat_add_128`); deterministic `Quiver.StrictMono` residue DAG |
| `Mahler32/Fib11Free.lean` | 11-free `3`-adic reverse pruning; `countBelow (good11Free k) (3^k) = fib (k+2)` |
| `Mahler32/WalshZeroCorr.lean` | Walsh coefficients on the real `k`-step orbit; top-bit-zero vanishing and top-bit doubling |
| `Mahler32/HInvariance.lean` | Hensel inverse, word residue `r_u`, affine offset `Δ(u,h,p3)`, and `h`-invariance of local Fourier norms |
| `Mahler32/SyracuseBijection.lean` | full-branch bijection of the accelerated Mahler–Syracuse map; forced `b ≥ 5` after the truncated `a = 1` branch |
| `Mahler32/ZeroEntropyCages.lean` | integer-vanishing criterion; the **deterministic** even-branch four-term obstruction `cage_two_sevenths`; the two-branch joint relation `Step`; genuine `Step`-orbits/cycles in `[2/7,5/7)` (`joint_orbit_two_sevenths`, `joint_cycle_two_fifths`, `joint_cycle_four_thirteenths`); the finite-state holed obstruction `[5/24,11/24) ∪ [13/24,19/24)` with survivor set `{4/15,2/5,3/5,11/15}` and `2`-cycle `2/5 ↔ 3/5` |
| `Mahler32/DiscreteFluidCertificates.lean` | cup map self-map; exact `4/19 → 6/19 → 9/19 → 4/19` three-cycle; `3/2` expansion; `2 : 1` mass split |
| `Mahler32/Model94Obstructions.lean` | `9/4` finite-roof arithmetic obstruction: mirror conservation, even-rung extinction, forbidden sums, odd-rung Klein-4, sum/difference shadow maps, carry-free base-9 conservation, finite-roof block bound |
| `Mahler32/Model94GlobalDecay.lean` | `9/4` global Fourier decay and midpoint $36^K$ Cantor intersection: `midpoint_double_cantor`, `inAK_scaled_interval`, `inAK_antipodal_exclusion`, exact `4`-contraction `norm_hatMu94_four_pow_mul`, cosine product `norm_hatMu94_cosine_product`, `global_odd_freq_decay`, `global_freq_decay_of_four_pow`, `DualPotentialCert`, `cert42_path_decay` |
| `Mahler32/RationalBaseDefs.lean` | pure exposed definitions (`@[expose] public def`) for general coprime `(p, q)` symbolic words, `TunnelModelPQ`, `RatInterval`, `StepPQ`, `hasBranchOverlap`, and `ZeroEntropyAutomaton` |
| `Mahler32/GeneralPQDecay.lean` | general coprime `(p, q)` (`2 ≤ q < p`) $\log_q p$ repetition-exponent exclusion (`repetition_exponent_bound_pq`), tunnel Fourier decay & quantitative Weyl equidistribution (`global_coprime_freq_decay_pq`, `weyl_decay_3_2`..`weyl_decay_8_3`), and Karp dual-potential cycle bound (`karp_cycle_bound`, `cert44_cycle_bound`) |
| `Mahler32/ZeroEntropyAutomaton.lean` | soundness of exact branch-overlap checking (`hasBranchOverlap_sound`), polynomial walk growth (`totalPaths_poly_bound`), zero-entropy SCC mother theorem (`zero_entropy_of_no_branching_scc`), and kernel `decide` certificates (`-5/3` `0.2880`, `-3/2` holed `0.5660 > 1/2`, `-3/2` centered `0.4284`, `+5/3` centered `0.3030`) |
| `Mahler32/QuiverMonotone.lean` | verbatim mirror of `Mathlib/Combinatorics/Quiver/Monotone.lean` from mathlib4#44885 (`Quiver.Monotone`, `Quiver.StrictMono`, `StrictMono.isPartialOrder_reachable`), pending the upstream merge |

The conditional branch is deliberately *outside* the zero-axiom core: `Mahler32Conditional/AlgebraicPairBranch.lean`
is the only module that may depend on the single extra axiom `schlickewei_subspace_Q3`, and it is a separate
Lake library so it cannot be imported by `Mahler32Core`, `Solution` or `SpecCheck`. Its own definition/statement
lock lives in `SpecCheckConditional.lean`.

Two companion papers (with Chinese reading editions) live in `papers/`:

- `papers/paper1_transcendence/` ([`main.tex`](papers/paper1_transcendence/main.tex), [中文阅读版](papers/paper1_transcendence/main_zh.md)) — *Simultaneous Archimedean and $q$-adic Padé Comparison for Rational Bases $p/q$ and the Algebraic–Pair Branch*
- `papers/paper2_zero_entropy_fluid/` ([`main.tex`](papers/paper2_zero_entropy_fluid/main.tex), [中文阅读版](papers/paper2_zero_entropy_fluid/main_zh.md)) — *Zero-Topological-Entropy Symbolic Obstructions, Discrete Fluid Transport, and Quantitative Weyl Decay for Rational Bases $p/q$*

Prebuilt PDFs and SHA-256 checksums for both companion papers are published as assets on the
[latest GitHub Release](https://github.com/3y3y3y-huaiji/mahler32/releases/latest); citation metadata
is provided in [`CITATION.cff`](CITATION.cff) and [`.zenodo.json`](.zenodo.json). The `v1.0.0`
snapshot is archived on Zenodo under DOI [10.5281/zenodo.24491265](https://doi.org/10.5281/zenodo.24491265).

Both carry a theorem-to-Lean traceability table.  Three honesty caveats are stated there rather
than hidden.  First, the general “all real `ξ` excluded” statement is a human-level proposition
whose only machine-checked ingredients are the integer engine and the concrete deterministic
`[2/7,5/7)` obstruction.  Second, the two-branch **joint** relation `Step x y ↔ y = T0 x ∨ y = T1 x` is
*not* emptied on `[2/7,5/7)` (an explicit six-term `Step`-orbit is proved in
`ZeroEntropyCages.joint_orbit_two_sevenths`), so the single-branch emptying depth `3` of the
deterministic map says nothing about the joint relation; `scripts/generate_certificates.py`
computes the exact joint survivor sets, the finite-depth Markov/SCC structure and the rational
cycles, and the holed obstruction `[5/24,11/24) ∪ [13/24,19/24)` is the finite-state core where the
survivor set is exactly `{4/15,2/5,3/5,11/15}`.  Third, the constant `δ* = 8/57` is the exact
preimage `T0⁻¹(4/19) = (2/3)(4/19)` of the cup cycle; under the cup map `F` (the branch-restricted
joint map on `[0,1/2)`) the left-hole family `[δ,1/2)` has the three exact regimes verified in the
script: `δ > 4/19` empties, `8/57 < δ ≤ 4/19` keeps a finite (zero-entropy) survivor set containing
the `3`-cycle, and `δ < 8/57` has positive entropy via the fold `T1 ∘ T0³` sending `[8/81,8/57)`
into `[0,4/19)`.  Nothing here claims Mahler's original conjecture, nor the `9/4` conjecture.

## Build

```bash
lake exe cache get      # prebuilt Mathlib oleans
lake build -KwarningAsError=true
```

## Layout

```
Mahler32.lean            # library root
Mahler32/Basic.lean      # core parity development
Mahler32/*.lean          # task modules (see the inventory table above)
Mahler32Core.lean        # zero-axiom entry point: imports every task module
Mahler32Conditional/     # task-11 branch; the only module with an extra axiom
AuditAxioms.lean         # kernel-axiom audit of the zero-axiom core
AuditAxiomsConditional.lean  # audit of the single conditional axiom
SpecCheck.lean           # definition / statement / numeric locks for the core
SpecCheckConditional.lean    # the same for the conditional branch
Challenge.lean           # advertised statements only (proofs are `sorry`)
Solution.lean            # imports Mahler32.Basic; the same names, proved
comparator.json          # names Comparator checks between Challenge and Solution
formalization.yaml       # self-report: classification, sources, automation, review status
docs/MAHLER32_REVIEW.md  # referee-style review: claim-by-claim verdicts, numerics, literature
docs/DECISIONS.md        # ADR log: the non-negotiable modelling decisions
papers/                  # two companion papers (LaTeX source + refs.bib)
scripts/verify_all.sh    # one-shot: build, audit, certificates, SSOT, secret guard, papers
scripts/verify_ssot.py   # toolchain / module-inventory / stale-claim / link gate
scripts/generate_certificates.py  # exact rational certificates for the papers
```

`Challenge.lean` and `Solution.lean` exist so the claims can be read in a few minutes without
reading the proofs.  They are separate Lake targets (`lake build Challenge`, `lake build
Solution`), matching the packaging expected by the [Palomar Registry](https://palomar-registry.org);

```
lake build Solution     # the real proofs
lake build Challenge    # the statement surface, with its expected `sorry` warnings
```

## AI / LLM assistance disclosure

This development was carried out with substantial LLM assistance. Every statement is checked by
Lean 4 and by CI (`lake build -KwarningAsError=true`, `#lint`, and a kernel-axiom audit that fails
on `sorryAx`).

## License

Dual-licensed, at your option, under either

- **Apache License 2.0** — see [`LICENSE`](LICENSE)
- **Mulan Permissive Software License v2 (MulanPSL-2.0)** — see [`LICENSE-MULAN`](LICENSE-MULAN)

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in
this work by you shall be dual-licensed as above, without any additional terms or conditions.
