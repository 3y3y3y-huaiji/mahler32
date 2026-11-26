# Parity structure of the 3/2 Mahler recursion, in Lean 4

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/lean_build.yml)
[![Independent kernel (nanoda)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/independent-kernel.yml/badge.svg)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/independent-kernel.yml)
[![Papers (LaTeX)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/papers.yml/badge.svg)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/papers.yml)
[![Release](https://img.shields.io/github/v/release/3y3y3y-huaiji/mahler32?label=Release)](https://github.com/3y3y3y-huaiji/mahler32/releases/latest)
[![aiXiv](https://img.shields.io/badge/aiXiv-2611.03037-B31B1B.svg)](https://aixiv.online/abs/2611.03037)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24491265.svg)](https://doi.org/10.5281/zenodo.24491265)
[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.36.0-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0008--2312--6913-A6CE39?logo=orcid&logoColor=white)](https://orcid.org/0009-0008-2312-6913)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![License: MulanPSL-2.0](https://img.shields.io/badge/License-MulanPSL_2.0-orange.svg)](LICENSE-MULAN)

A Lean 4 / Mathlib formalization of the symbolic, arithmetic and harmonic structure of the
parity sequence of the Mahler `3/2` recursion

```text
a(1) = 1,   a(n+1) = a(n) + ⌈a(n)/2⌉ = ⌈3·a(n)/2⌉
```

i.e. [OEIS A061419](https://oeis.org/A061419), whose parity is
[OEIS A205083](https://oeis.org/A205083) (shifted by one index: `A205083(n) = a(n+1) mod 2`).
The recurrence is the `3/2` dynamical system of Mahler (1968).

**Paper:** [PDF](papers/main/main.pdf) · [LaTeX source](papers/main/main.tex) · [中文版 PDF](papers/main-zh/main.pdf) · [中文 LaTeX 源](papers/main-zh/main.tex) · [aiXiv:2611.03037](https://aixiv.online/abs/2611.03037) · [Release PDFs](https://github.com/3y3y3y-huaiji/mahler32/releases/latest) · [Zenodo DOI](https://doi.org/10.5281/zenodo.24491265).

## Main results

| Result | Content | Status |
| :-- | :-- | :-- |
| General `(p,q)` repetition exponent | For coprime `2 ≤ q < p`, a symbolic orbit matching `U V^w` must satisfy `w < log_q p + (log_q p − 1)·|U|/|V| + log(g₀ + d_max/(p−q))/(|V| log q)`; no orbit matches `U V^w` for all `w`. | Unconditional, zero axioms |
| `(9,4)` congruence model | Mirror symmetry `g_k + g̃_k = 9^k 4^{N−k} − 1`; even-level extinction; four-point odd-level exclusion; CRT intersection modulo `36^K` of the `2`-adic and `3`-adic survivor sets, with antipodal diameter `≤ (9^K − 4^K)/5`; global odd-frequency decay `‖μ̂_K(u)‖ ≤ C K^{−c}`. | Unconditional, zero axioms |
| Quantitative Weyl equidistribution | The `9/4` Fourier decay extends to every coprime `p > q ≥ 2`: `‖μ̂_K(u)‖ ≤ C K^{−c}` whenever `q ∤ u`, explicit at `3/2, 4/3, 5/4, 5/3, 7/4, 8/3`. | Unconditional, zero axioms |
| Simultaneous Padé comparison | Archimedean and `2`-adic diagonal Padé approximants differ by `e c²/(1−c)` and coincide iff `c = 0`; with integer-vanishing this gives the repetition exponent above. | Unconditional, zero axioms |
| `3/2` deterministic vs joint symbolics | No rational `x` has four iterates of the deterministic map in `[2/7, 5/7)`; the joint two-branch relation admits explicit periodic orbits there; the holed barrier has survivor set `{4/15, 2/5, 3/5, 11/15}`. | Unconditional; holed exactness is paper-only (Lean certifies the four points and their transitions) |
| Zero-topological-entropy automata | An acyclic component ordering with no internal branching forces polynomial walk growth, hence zero entropy, for every signed rational base `±p/q`; exact rational certificates at four regions. | Unconditional, kernel `decide` |
| Algebraic-pair branch | For algebraic irrational `δ`, the violating index pairs with distinct gaps are finite. | Conditional on Schlickewei's subspace theorem |

The two unconditional `9/4` and `(p,q)` decay results, the repetition exponent and the
`3/2` symbolics are stated and proved as the main theorems of the paper
[`papers/main/main.tex`](papers/main/main.tex). The algebraic-pair finiteness is the only
statement that uses an extra axiom; it is physically isolated in
[`Mahler32Conditional/AlgebraicPairBranch.lean`](Mahler32Conditional/AlgebraicPairBranch.lean).

## Verification status

- **Toolchain.** Lean `v4.36.0` with Mathlib `v4.36.0`, pinned in `lean-toolchain` and `lakefile.lean`.
- **Zero-axiom core.** Every theorem in [`AuditAxioms.lean`](AuditAxioms.lean) depends only on
  `propext`, `Classical.choice` and `Quot.sound`. The core has no `sorry`, no `admit`, no
  `native_decide` and no local `axiom`.
- **Conditional branch.** [`Mahler32Conditional/AlgebraicPairBranch.lean`](Mahler32Conditional/AlgebraicPairBranch.lean)
  is a separate Lake library whose only extra axiom is `schlickewei_subspace_Q3`; it cannot be
  imported by `Mahler32Core`, `Solution` or `SpecCheck`.
- **Independent kernel.** [`AuditAxioms.lean`](AuditAxioms.lean) is replayed by `leanchecker`, and the
  exported core and conditional environments are re-type-checked by `nanoda`, a separate Rust
  implementation of the Lean kernel, in
  [`.github/workflows/independent-kernel.yml`](.github/workflows/independent-kernel.yml).
- **Exact certificates.** All finite rational constants and certificate sizes quoted above are
  regenerated and checked by `scripts/generate_certificates.py --verify`.

## Reproduce

```bash
lake exe cache get
lake build -KwarningAsError=true
./scripts/verify_all.sh
```

`scripts/verify_all.sh` mirrors the CI: build, axiom audit, SSOT gate, secret guard, certificate
reproducibility and the LaTeX build.

## Paper

The two former companion papers are merged into a single pure-mathematics paper,
[*Symbolic exclusion intervals, Fourier decay, and p-adic obstructions for rational-base orbits*](papers/main/main.tex)
([aiXiv:2611.03037](https://aixiv.online/abs/2611.03037)).
The CI-compiled [PDF](papers/main/main.pdf) is committed next to the source `main.tex` and
`refs.bib`, and is attached alongside `SHA256SUMS.txt` on every tagged
[GitHub Release](https://github.com/3y3y3y-huaiji/mahler32/releases/latest). A full Chinese
translation is maintained at [`papers/main-zh/main.tex`](papers/main-zh/main.tex) with its
compiled [PDF](papers/main-zh/main.pdf); it is built with XeLaTeX (`ctex` + Noto CJK) and attached
to the same release as `main-zh.pdf`. The text is organised as introduction and main results,
proofs, a short formal-verification section, and an AI-assistance statement. The `v1.0.0` snapshot
is archived on Zenodo under DOI [10.5281/zenodo.24491265](https://doi.org/10.5281/zenodo.24491265).
Citation metadata is in [`CITATION.cff`](CITATION.cff) and [`.zenodo.json`](.zenodo.json).

The formal engineering assets — [`AGENTS.md`](AGENTS.md), [`docs/`](docs/),
[`formalization.yaml`](formalization.yaml) and the full CI — are retained.

<details>
<summary><strong>Background: the <code>3/2</code> recursion and one-step laws</strong></summary>

The core module [`Mahler32/Basic.lean`](Mahler32/Basic.lean) (1046 lines) proves:

- **One-step laws.** `step x % 2 = x / 2 % 2`: the next parity is the second binary digit of the
  current term. Also `step x % 3 = 2 * (x % 2)`, and the base-`6` last digit is a bijection onto
  consecutive parity pairs, taking values in `{0, 2, 3, 5}`.
- **Sharp parity predictability.** `m` low binary (equivalently base-`6`) digits determine exactly the next
  `m` parities, and the window is sharp: `0` and `6^m` agree modulo `6^m` yet differ at step `m`.
- **Base-`3` transducer.** Long division with a carry in `{0,1}` reproduces `⌈3x/2⌉`; the invariant
  is purely algebraic.
- **Inverse branch and period doubling.** The branch `bstep y = (2y − 2y % 3)/3` is inverse to
  `step` where defined, and scanning a primitive block with an odd number of `1`-digits doubles
  the period.
- **`2^k` legal classes.** `|{y < 3^k : good k y}| = 2^k`, by an explicit bijection.
- **11-free pruning and Walsh structure.** Forbidding two consecutive odd backward steps reduces
  the count modulo `3^k` to `Nat.fib (k + 2)`; Walsh coefficients vanish whenever the mask omits
  bit `k`.
</details>

<details>
<summary><strong>Complete module inventory</strong></summary>

| Module | Machine-checked content |
| :-- | :-- |
| `Mahler32/Basic.lean` | one-step laws, sharp `m`-digit parity predictability, base-3 transducer, inverse branch and period doubling, the `2^k` legal-class count, 11-free Fibonacci pruning, Walsh zero correlation |
| `Mahler32/Base6LightCone.lean` | carry propagation under `6^(L−1)` shifts and the 3-adic window (`light_cone_flip`, `good_mod_iff`) |
| `Mahler32/SyracuseGates.lean` | integer `3/2` step; exact gates `g % 12 = 9`, `g % 256 = 9`, `g % 768 = 9` |
| `Mahler32/TwoWorldPadeCriterion.lean` | Padé discrepancy identity, agreement criterion, integer engine, rational `√2` bounds, `(9,4)` prefix repetition bounds, mod-9 non-vanishing criterion |
| `Mahler32/ArnoldTongue5State.lean` | the 5-state count and exact `T` windows on `[1/3, 11/15)` |
| `Mahler32/ArnoldTongue7State.lean` | the 7-state count and exact `T` windows on `[7/24, 17/24)` |
| `Mahler32/DAGBoundedGap.lean` | finite-state hitting-time bounds; exact hitting set; carry branch under `g + 128`; deterministic monotone residue graph |
| `Mahler32/Fib11Free.lean` | 11-free 3-adic reverse pruning; `countBelow (good11Free k) (3^k) = fib (k+2)` |
| `Mahler32/WalshZeroCorr.lean` | Walsh coefficients on the real `k`-step orbit; top-bit vanishing and doubling |
| `Mahler32/HInvariance.lean` | Hensel inverse, word residue, affine offset, `h`-invariance of local Fourier norms |
| `Mahler32/SyracuseBijection.lean` | full-branch bijection of the accelerated Mahler–Syracuse map |
| `Mahler32/ZeroEntropyCages.lean` | zero-entropy exclusion intervals; deterministic `[2/7,5/7)` exit; joint orbits and cycles; holed finite survivor core |
| `Mahler32/DiscreteFluidCertificates.lean` | transfer and expansion bounds, exact `4/19 → 6/19 → 9/19 → 4/19` cycle, `3/2` expansion, `2:1` length split (no invariant measure) |
| `Mahler32/Model94Obstructions.lean` | `(9,4)` mirror symmetry, even-level extinction, forbidden sums, four-point odd-level exclusion, sum/difference identities, carry-free base-9 conservation, finite-window bound |
| `Mahler32/Model94GlobalDecay.lean` | CRT intersection modulo `36^K` of the `2`-adic and `3`-adic survivor sets, antipodal exclusion, `4`-contraction, cosine product, global odd-frequency decay |
| `Mahler32/RationalBaseDefs.lean` | exposed definitions for general coprime `(p,q)` words, consecutive-digit model, rational intervals, zero-entropy finite-state model |
| `Mahler32/GeneralPQDecay.lean` | general `(p,q)` repetition-exponent exclusion, consecutive-digit Fourier decay, quantitative Weyl equidistribution, Karp cycle bound |
| `Mahler32/ZeroEntropyAutomaton.lean` | branch-overlap soundness, polynomial walk growth, zero-entropy finite-state theorem, exact kernel certificates |
| `Mahler32/QuiverMonotone.lean` | mirror of `Mathlib/Combinatorics/Quiver/Monotone.lean` from mathlib4#44885, pending upstream merge |
| `Mahler32Conditional/AlgebraicPairBranch.lean` | the conditional algebraic-pair finiteness theorem; the only module with the extra axiom |

</details>

## Layout

```text
Mahler32.lean                # library root
Mahler32/Basic.lean          # core parity development
Mahler32/*.lean              # task modules (see the inventory above)
Mahler32Core.lean            # zero-axiom entry point: imports every task module
Mahler32Conditional/         # the algebraic-pair branch; the only extra-axiom module
AuditAxioms.lean             # kernel-axiom audit of the zero-axiom core
AuditAxiomsConditional.lean  # audit of the single conditional axiom
SpecCheck.lean               # definition / statement / numeric locks for the core
SpecCheckConditional.lean    # the same for the conditional branch
Challenge.lean               # advertised statements only
Solution.lean                # the same names, proved
comparator.json              # names checked between Challenge and Solution
formalization.yaml           # self-report
docs/MAHLER32_REVIEW.md      # referee-style review
docs/DECISIONS.md            # ADR log
papers/main/                 # the unified paper (LaTeX source + refs.bib)
scripts/verify_all.sh        # one-shot: build, audit, certificates, SSOT, secret guard, papers
scripts/verify_ssot.py       # toolchain / module-inventory / stale-claim / unified-paper gate
scripts/generate_certificates.py  # exact rational certificates for the paper
```

`Challenge.lean` and `Solution.lean` are separate Lake targets (`lake build Challenge`,
`lake build Solution`), matching the packaging expected by the
[Palomar Registry](https://palomar-registry.org).

## AI / LLM assistance disclosure

This development was carried out with substantial LLM assistance. Every statement is checked by
Lean 4 and by CI (`lake build -KwarningAsError=true`, `#lint`, a kernel-axiom audit that fails on
`sorryAx`, and an independent `nanoda` kernel check).

## License

Dual-licensed, at your option, under either

- **Apache License 2.0** — see [`LICENSE`](LICENSE)
- **Mulan Permissive Software License v2 (MulanPSL-2.0)** — see [`LICENSE-MULAN`](LICENSE-MULAN)

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in
this work by you shall be dual-licensed as above, without any additional terms or conditions.
