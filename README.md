# Parity structure of the 3/2 Mahler recursion, in Lean 4

[![Lean 4 CI](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/lean_build.yml/badge.svg)](https://github.com/3y3y3y-huaiji/mahler32/actions/workflows/lean_build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue.svg)](https://lean-lang.org/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-v4.36.0-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0008--2312--6913-A6CE39?logo=orcid&logoColor=white)](https://orcid.org/0009-0008-2312-6913)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE-APACHE)
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

Everything below is machine-checked: **555 lines, no `sorry`**, and every core theorem depends
only on `propext`, `Classical.choice` and `Quot.sound`.

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

## Build

```bash
lake exe cache get      # prebuilt Mathlib oleans
lake build -KwarningAsError=true
```

## Layout

```
Mahler32.lean           # library root
Mahler32/Basic.lean     # all material
docs/MAHLER32_REVIEW.md # referee-style review: claim-by-claim verdicts, numerics, literature
```

## AI / LLM assistance disclosure

This development was carried out with substantial LLM assistance. Every statement is checked by
Lean 4 and by CI (`lake build -KwarningAsError=true`, `#lint`, and a kernel-axiom audit that fails
on `sorryAx`).

## License

Dual-licensed, at your option, under either

- **Apache License 2.0** — see [`LICENSE-APACHE`](LICENSE-APACHE)
- **Mulan Permissive Software License v2 (MulanPSL-2.0)** — see [`LICENSE-MULAN`](LICENSE-MULAN)

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in
this work by you shall be dual-licensed as above, without any additional terms or conditions.
