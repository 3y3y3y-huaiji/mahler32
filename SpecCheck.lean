module

public import Mahler32Core

/-!
# `SpecCheck` — the definition lock, statement lock and numeric anchors

This file is a *read-only* statement surface over the zero-axiom core (tasks 1–12).  It is not a
proof of anything new: it is a gate.  CI compiles it with `warningAsError`, and every declaration
below is chosen so that it **only typechecks if the implementation still matches the task sheet**:

* **Definition locks** (`example … := rfl`) — reuse the candidate's own definitions *by
  definitional equality* against the verbatim task-sheet body.  If a definition is weakened,
  generalised, made abstract, or given an extra hypothesis, the `rfl` no longer closes and the
  file fails to compile.
* **Statement locks** (`example … := Mahler32.…theorem …`) — restate the exact final theorem type
  and discharge it by `exact`.  If the candidate proves a weaker variant (extra hypothesis, a
  `∃` replaced by `∀`, a `≠` replaced by `→`, …), the `exact` fails.
* **Numeric anchors** (`example … := by decide`) — pin concrete arithmetic truth (the `k = 4`
  Fibonacci count `8`, the Syracuse anchors `0` and `1/16`, the Padé identity, …).  A hollow or
  abstract substitute definition cannot reproduce these values.

Nothing here imports or mentions `Mahler32Conditional`; the conditional axiom type is locked in
the sibling file `SpecCheckConditional.lean`.
-/

public section

/-! ## Task 1 — `Mahler32.Base6LightCone` -/

namespace SpecCheck.Base6LightCone

open Mahler32.Base6LightCone

/-- Lock: `step a = (3*a+1)/2`. -/
example (a : ℕ) : step a = (3 * a + 1) / 2 := rfl

/-- Lock: `iterStep` base case. -/
example (a : ℕ) : iterStep 0 a = a := rfl

/-- Lock: `iterStep` successor case (structural recursion on `k`). -/
example (k a : ℕ) : iterStep (k + 1) a = iterStep k (step a) := rfl

/-- Lock: `bstep y = (2*y)/3`. -/
example (y : ℕ) : bstep y = (2 * y) / 3 := rfl

/-- Lock: `good k y` is *exactly* the no-`≡ 1 (mod 3)` predicate. -/
example (k y : ℕ) : good k y ↔ (∀ j, j < k → (bstep^[j] y) % 3 ≠ 1) := Iff.rfl

/-- Statement lock: the light-cone flip. -/
example (k a : ℕ) : iterStep k (a + 6 ^ k) % 2 ≠ iterStep k a % 2 :=
  light_cone_flip k a

/-- Statement lock: the 3-adic window `good k y ↔ good k (y % 3^k)`. -/
example (k y : ℕ) : good k y ↔ good k (y % 3 ^ k) := good_mod_iff k y

/-- Statement lock: the next term is never `≡ 1 (mod 3)`. -/
example (a : ℕ) : step a % 3 ≠ 1 := step_mod_three_ne_one a

/-- Statement lock: the last base-`6` digit stays in `{0, 2, 3, 5}`. -/
example (a : ℕ) : step a % 6 = 0 ∨ step a % 6 = 2 ∨ step a % 6 = 3 ∨ step a % 6 = 5 :=
  step_mod_six_mem a

/-- Numeric anchor: `iterStep 1 7 = step 7 = 11`. -/
example : iterStep 1 7 = 11 := by decide

/-- Numeric anchor: the flip is real, not vacuous (`11 % 2 ≠ 2 % 2`). -/
example : iterStep 1 (1 + 6 ^ 1) % 2 ≠ iterStep 1 1 % 2 := by decide

end SpecCheck.Base6LightCone

/-! ## Task 2 — `Mahler32.SyracuseGates` -/

namespace SpecCheck.SyracuseGates

open Mahler32.SyracuseGates

/-- Lock: `zStep` is the integer `3/2` map. -/
example (g : ℕ) : zStep g = (if g % 2 = 0 then (3 * g) / 2 else (3 * g + 1) / 2) := rfl

/-- Statement lock: `g ≡ 9 (mod 12)` characterises an even successor among odd multiples of `3`. -/
example {g : ℕ} (hodd : g % 2 = 1) (hthree : g % 3 = 0) : zStep g % 2 = 0 ↔ g % 12 = 9 :=
  odd_step_mod_twelve hodd hthree

/-- Statement lock: `256 ∣ 27g+13 ↔ g % 256 = 9`. -/
example (g : ℕ) : 256 ∣ (27 * g + 13) ↔ g % 256 = 9 := short_jump_mod_256 g

/-- Statement lock: merging the `3`-adic and `2`-adic gates. -/
example {g : ℕ} (h3 : g % 3 = 0) (h256 : g % 256 = 9) : g % 768 = 9 :=
  mod_768_gate h3 h256

/-- Numeric anchor: `zStep 9 = 14` (and hence even). -/
example : zStep 9 = 14 := by decide

/-- Numeric anchor: `27 * 9 + 13 = 256`. -/
example : 27 * 9 + 13 = 256 := by decide

end SpecCheck.SyracuseGates

/-! ## Task 3 — `Mahler32.ArnoldTongue5State` -/

namespace SpecCheck.ArnoldTongue5State

open Mahler32.ArnoldTongue5State

/-- Lock: the translated Mahler map `T_t x = (3x - t)/2`. -/
example (t : Bool) (x : ℚ) : T t x = (3 * x - (if t then 1 else 0)) / 2 := rfl

/-- Lock: `countPaths` base case. -/
example (m : Fin 5) : countPaths m 0 = 1 := rfl

/-- Statement lock: the exact ten-slot transition table. -/
example :
    nextInterval 0 false = some 1 ∧ nextInterval 0 true = some 0 ∧
      nextInterval 1 false = none ∧ nextInterval 1 true = some 1 ∧
      nextInterval 2 false = some 3 ∧ nextInterval 2 true = some 4 ∧
      nextInterval 3 false = some 4 ∧ nextInterval 3 true = none ∧
      nextInterval 4 false = some 2 ∧ nextInterval 4 true = none :=
  nextInterval_exact

/-- Statement lock: `|L(k)| = k + 1` for `k ≥ 1`. -/
example (k : ℕ) (hk : 1 ≤ k) : countPaths 0 k = k + 1 := countPaths_zero k hk

/-- Statement lock: `24 * countPaths 0 k < 41 k - 72` for `k ≥ 8`. -/
example (k : ℕ) (hk : 8 ≤ k) : 24 * countPaths 0 k < 41 * k - 72 :=
  countPaths_zero_lt k hk

/-- Numeric anchor: `countPaths 0 3 = 4`. -/
example : countPaths 0 3 = 4 := by decide

end SpecCheck.ArnoldTongue5State

/-! ## Task 4 — `Mahler32.ArnoldTongue7State` -/

namespace SpecCheck.ArnoldTongue7State

open Mahler32.ArnoldTongue7State

/-- Lock: `countPaths7` base case. -/
example (m : Fin 7) : countPaths7 m 0 = 1 := rfl

/-- Statement lock: the exact fourteen-slot transition table. -/
example :
    nextInterval7 0 false = some 1 ∧ nextInterval7 0 true = some 0 ∧
      nextInterval7 1 false = some 3 ∧ nextInterval7 1 true = some 2 ∧
      nextInterval7 2 false = some 2 ∧ nextInterval7 2 true = none ∧
      nextInterval7 3 false = none ∧ nextInterval7 3 true = some 3 ∧
      nextInterval7 4 false = some 5 ∧ nextInterval7 4 true = some 6 ∧
      nextInterval7 5 false = some 4 ∧ nextInterval7 5 true = none ∧
      nextInterval7 6 false = none ∧ nextInterval7 6 true = some 5 :=
  nextInterval7_exact

/-- Statement lock: `|L(k)| = 2k` for `k ≥ 1`. -/
example (k : ℕ) (hk : 1 ≤ k) : countPaths7 0 k = 2 * k := countPaths7_zero k hk

/-- Numeric anchor: `countPaths7 0 5 = 10`. -/
example : countPaths7 0 5 = 10 := by decide

end SpecCheck.ArnoldTongue7State

/-! ## Task 5 — `Mahler32.DAGBoundedGap` -/

namespace SpecCheck.DAGBoundedGap

open Mahler32.DAGBoundedGap

/-- Lock: `embed128 n` has value `n % 128`. -/
example (n : ℕ) : (embed128 n).val = n % 128 := rfl

/-- Lock: `zStep g` has value `(3 g + g % 2)/2 % 128`. -/
example (g : Fin 128) : (zStep g).val = (3 * g.val + g.val % 2) / 2 % 128 := rfl

/-- Statement lock: `S7` has `27` elements. -/
example : S7.card = 27 := S7_card

/-- Statement lock: `R7` has `4` elements. -/
example : R7.card = 4 := R7_card

/-- Statement lock: bounded gap `≤ 11`. -/
example (g : Fin 128) (hg : g ∈ S7) : ∃ n ≤ 11, iterZ n g ∈ R7 :=
  dag_bounded_gap g hg

/-- Numeric anchor: `0` is already a collision residue, so its depth is `0`. -/
example : dagDepth ⟨0, by norm_num⟩ = 0 := by decide

/-- Statement lock: the deterministic residue potential is `Quiver.StrictMono`
(mathlib4#44885 `Quiver.StrictMono`). -/
example : Quiver.StrictMono gapPot := gapPot_strictMono

/-- Statement lock: the deterministic residue graph is acyclic, via
`Quiver.StrictMono.path_eq_nil`. -/
example {a : GapV} (p : Quiver.Path a a) : p = .nil := gap_acyclic p

/-- Statement lock: `Quiver.Reachable` is a partial order, via
`Quiver.StrictMono.isPartialOrder_reachable`. -/
example : IsPartialOrder GapV Quiver.Reachable := gap_reachable_isPartialOrder

/-- Statement lock: the naive two-branch carry relation has a self-loop at `127`, so it is *not*
a DAG. -/
example : CarryStep (embed128 127) (embed128 127) := carry_self_loop_127

/-- Statement lock: no uniform `≤ 11` bound holds on genuine `ℕ` orbits (counterexample `28`). -/
example : ¬ (∀ g : ℕ, ∃ n ≤ 11, iterZNat n g % 128 ∈ R7Nat) := nat_uniform_eleven_fails

end SpecCheck.DAGBoundedGap

/-! ## Task 6 — `Mahler32.TwoWorldPadeCriterion` -/

namespace SpecCheck.TwoWorldPadeCriterion

open Mahler32.TwoWorldPadeCriterion

/-- Lock: `[1/2]` Padé value `e/(1-c)`. -/
example (e c : ℚ) : pade12 e c = e / (1 - c) := rfl

/-- Lock: `[1/1]` Padé value `e(1+c)`. -/
example (e c : ℚ) : pade11 e c = e * (1 + c) := rfl

/-- Statement lock: the two-world identity. -/
example (e c : ℚ) (hc : c ≠ 1) : pade12 e c - pade11 e c = e * c ^ 2 / (1 - c) :=
  two_world_identity e c hc

/-- Statement lock: the integer-valued complementary factor. -/
example : (1 / 9 : ℚ) * 9 = 1 := integer_divisibility_bound

/-- Numeric anchor: at `c = 1/2`, `pade12 1 (1/2) = 2`. -/
example : pade12 1 (1 / 2) = 2 := by norm_num [pade12]

end SpecCheck.TwoWorldPadeCriterion

/-! ## Task 7 — `Mahler32.Fib11Free` -/

namespace SpecCheck.Fib11Free

open Mahler32.Fib11Free

/-- Lock: `bstep y = (2*y)/3` on the genuine `3`-adic reverse map. -/
example (y : ℕ) : bstep y = (2 * y) / 3 := rfl

/-- Lock: `good11FreeAux` base case. -/
example (prevOdd : Bool) (y : ℕ) : good11FreeAux 0 prevOdd y = true := rfl

/-- Lock: the full `good11FreeAux` successor body (nested `11`-free ban). -/
example (k : ℕ) (prevOdd : Bool) (y : ℕ) :
    good11FreeAux (k + 1) prevOdd y =
      (if y % 3 = 1 then false
       else if y % 3 = 2 then
         (if prevOdd then false else good11FreeAux k true (bstep y))
       else good11FreeAux k false (bstep y)) := rfl

/-- Lock: `good11Free k y = good11FreeAux k false y`. -/
example (k y : ℕ) : good11Free k y = good11FreeAux k false y := rfl

/-- Lock: `fib 0 = 0`. -/
example : fib 0 = 0 := rfl

/-- Lock: `fib 1 = 1`. -/
example : fib 1 = 1 := rfl

/-- Lock: `fib (n+2) = fib (n+1) + fib n`. -/
example (n : ℕ) : fib (n + 2) = fib (n + 1) + fib n := rfl

/-- Lock: `countBelow P N = (List.range N).countP P`. -/
example (P : ℕ → Bool) (N : ℕ) : countBelow P N = (List.range N).countP P := rfl

/-- Statement lock: `countBelow (good11Free k) (3^k) = fib (k+2)`. -/
example (k : ℕ) : countBelow (good11Free k) (3 ^ k) = fib (k + 2) := fib_count k

/-- Statement lock: the `k = 4` Fibonacci count `8`. -/
example : countBelow (good11Free 4) (3 ^ 4) = 8 := survivors_four

/-- Numeric anchor: `k = 4` over `3^4 = 81` really yields `8` survivors. -/
example : countBelow (good11Free 4) (3 ^ 4) = 8 := by decide

/-- Numeric anchor: `k = 3` yields `fib 5 = 5` survivors. -/
example : countBelow (good11Free 3) (3 ^ 3) = 5 := by decide

end SpecCheck.Fib11Free

/-! ## Task 8 — `Mahler32.WalshZeroCorr` -/

namespace SpecCheck.WalshZeroCorr

open Mahler32.WalshZeroCorr

/-- Lock: `fk` really binds to `Base6LightCone.iterStep`. -/
example (k x : ℕ) : fk k x = (Mahler32.Base6LightCone.iterStep k x) % 2 := rfl

/-- Lock: `bitDotAux` base case. -/
example (u x d : ℕ) : bitDotAux 0 u x d = 0 := rfl

/-- Lock: `signBit`. -/
example (b : ℕ) : signBit b = (if b % 2 = 0 then 1 else -1) := rfl

/-- Lock: `walshCoeff` on the `(k+1)`-bit cube. -/
example (k u : ℕ) :
    walshCoeff k u =
      ((List.range (2 ^ (k + 1))).map
        (fun x => signBit (fk k x + bitDotAux (k + 1) u x))).sum := rfl

/-- Statement lock: top-bit-zero frequencies vanish. -/
example (k u : ℕ) (hu : u < 2 ^ k) : walshCoeff k u = 0 := walsh_top_bit_zero k u hu

/-- Statement lock: top-bit frequencies double the lower coefficient. -/
example (k u : ℕ) (hu : u < 2 ^ k) :
    walshCoeff k (u + 2 ^ k) =
      2 * ((List.range (2 ^ k)).map (fun x => signBit (fk k x + bitDotAux k u x))).sum :=
  walsh_top_bit_double k u hu

/-- Numeric anchor: `walshCoeff 0 0 = 0`. -/
example : walshCoeff 0 0 = 0 := by decide

end SpecCheck.WalshZeroCorr

/-! ## Task 9 — `Mahler32.HInvariance` -/

namespace SpecCheck.HInvariance

open Mahler32.HInvariance

/-- Lock: `wordA [] = 0`. -/
example : wordA [] = 0 := rfl

/-- Lock: `wordA (b :: rest) = (if b then 1 else 0) * 3 ^ rest.length + 2 * wordA rest`. -/
example (b : Bool) (rest : List Bool) :
    wordA (b :: rest) = (if b then 1 else 0) * 3 ^ rest.length + 2 * wordA rest := rfl

/-- Lock: `henselInvAux` base case. -/
example (M a : ℕ) : henselInvAux M a 0 = 1 % M := rfl

/-- Lock: `invModPow2 s a = henselInvAux (2^s) a s`. -/
example (s a : ℕ) : invModPow2 s a = henselInvAux (2 ^ s) a s := rfl

/-- Lock: `wordResidue` body. -/
example (s : ℕ) (u : List Bool) :
    wordResidue s u =
      (let M := 2 ^ s
       let inv3s := invModPow2 s (3 ^ s)
       (inv3s * (M - wordA u % M)) % M) := rfl

/-- Lock: `affineDelta` body. -/
example (s : ℕ) (u : List Bool) (h p3 : ℕ) :
    affineDelta s u h p3 =
      (let M := 2 ^ s
       let r := wordResidue s u
       (invModPow2 s p3 * ((r + M - h % M) % M)) % M) := rfl

/-- Statement lock: Hensel inverse correctness. -/
example (s a : ℕ) (ha : a % 2 = 1) : (a * invModPow2 s a) % 2 ^ s = 1 % 2 ^ s :=
  henselInv_correct s a ha

/-- Statement lock: the residue equation `3^s r_u + A(u) ≡ 0 (mod 2^s)`. -/
example (s : ℕ) (u : List Bool) : (3 ^ s * wordResidue s u + wordA u) % 2 ^ s = 0 :=
  wordResidue_correct s u

/-- Statement lock: the affine equation `p3 Δ + h ≡ r_u (mod 2^s)`. -/
example (s : ℕ) (u : List Bool) (h p3 : ℕ) (hp3 : p3 % 2 = 1) :
    (p3 * affineDelta s u h p3 + h) % 2 ^ s = wordResidue s u % 2 ^ s :=
  affineDelta_equation s u h p3 hp3

/-- Statement lock: the `h`-shift identity. -/
example (s : ℕ) (u : List Bool) (h p3 : ℕ) (hp3 : p3 % 2 = 1) :
    (affineDelta s u h p3 + invModPow2 s p3 * h) % 2 ^ s
      = affineDelta s u 0 p3 % 2 ^ s :=
  affineDelta_shift s u h p3 hp3

/-- Statement lock: `p3`-scaling. -/
example (s : ℕ) (u : List Bool) (m p3 : ℕ) (hp3 : p3 % 2 = 1) :
    (m * affineDelta s u 0 p3) % 2 ^ s
      = ((m * invModPow2 s p3) * affineDelta s u 0 1) % 2 ^ s :=
  affineDelta_scale s u m p3 hp3

/-- Statement lock: the pairwise phase difference is `h`-invariant. -/
example (s : ℕ) (u v : List Bool) (m : ℤ) (h p3 : ℕ) (hp3 : p3 % 2 = 1) :
    ((m * (affineDelta s u h p3 : ℤ) - m * (affineDelta s v h p3 : ℤ)) % (2 ^ s : ℤ))
      = (((m * (invModPow2 s p3 : ℤ))
            * ((affineDelta s u 0 1 : ℤ) - (affineDelta s v 0 1 : ℤ))) % (2 ^ s : ℤ)) :=
  affine_phase_shift s u v m h p3 hp3

/-- Statement lock: `h`-invariance of the local Fourier norm. -/
example (s : ℕ) (W : List (List Bool)) (m h p3 : ℕ)
    (hp3 : p3 % 2 = 1) (χ : ZMod (2 ^ s) → ℂ)
    (hadd : ∀ a b, χ (a + b) = χ a * χ b) (hnorm : ∀ a, ‖χ a‖ = 1) :
    localFourierNormSq s W m h p3 χ
      = localFourierNormSq s W (m * invModPow2 s p3) 0 1 χ :=
  fourier_norm_invariant s W m h p3 hp3 χ hadd hnorm

/-- Numeric anchor: `A([1,0,1]) = 9 + 4 = 13`. -/
example : wordA [true, false, true] = 13 := by decide

/-- Numeric anchor: `invModPow2 3 3 = 3` (`3 * 3 ≡ 1 (mod 8)`). -/
example : invModPow2 3 3 = 3 := by decide

end SpecCheck.HInvariance

/-! ## Task 10 — `Mahler32.SyracuseBijection` -/

namespace SpecCheck.SyracuseBijection

open Mahler32.SyracuseBijection

/-- Lock: even step `T0 x = (3/2) x`. -/
example (x : ℚ) : T0 x = (3 / 2 : ℚ) * x := rfl

/-- Lock: odd step `T1 x = (3/2) x - 1/2`. -/
example (x : ℚ) : T1 x = (3 / 2 : ℚ) * x - (1 / 2 : ℚ) := rfl

/-- Lock: `iterT0` base case. -/
example (x : ℚ) : iterT0 0 x = x := rfl

/-- Lock: `iterT0` successor case. -/
example (a : ℕ) (x : ℚ) : iterT0 (a + 1) x = iterT0 a (T0 x) := rfl

/-- Lock: `loTile a = (1/3) (2/3)^a`. -/
example (a : ℕ) : loTile a = (1 / 3 : ℚ) * ((2 / 3 : ℚ) ^ a) := rfl

/-- Lock: `hiTile a = min (1/4) ((1/2) (2/3)^a)`. -/
example (a : ℕ) : hiTile a = min (1 / 4 : ℚ) ((1 / 2 : ℚ) * ((2 / 3 : ℚ) ^ a)) := rfl

/-- Lock: `syracuseMap a x = (3/2)^(a+1) x - 1/2`. -/
example (a : ℕ) (x : ℚ) : syracuseMap a x = ((3 / 2 : ℚ) ^ (a + 1)) * x - (1 / 2 : ℚ) := rfl

/-- Lock: `syracuseInv a y = (2/3)^(a+1) (y + 1/2)`. -/
example (a : ℕ) (y : ℚ) :
    syracuseInv a y = ((2 / 3 : ℚ) ^ (a + 1)) * (y + (1 / 2 : ℚ)) := rfl

/-- Statement lock: §4.4 full-branch bijection for `a ≥ 2`. -/
example {a : ℕ} (ha : 2 ≤ a) :
    (∀ x : ℚ, loTile a ≤ x → x < hiTile a →
        0 ≤ syracuseMap a x ∧ syracuseMap a x < 1 / 4) ∧
      (∀ y : ℚ, 0 ≤ y → y < 1 / 4 →
        loTile a ≤ syracuseInv a y ∧ syracuseInv a y < hiTile a) :=
  syracuse_bijective ha

/-- Statement lock: forced `b ≥ 5` after the truncated `a = 1` branch. -/
example {x : ℚ} (hlo : 2 / 9 ≤ x) (hhi : x < 1 / 4)
    {b : ℕ} (hb1 : 1 ≤ b) (hb4 : b ≤ 4) : syracuseMap 1 x < loTile b :=
  force_b_ge_five hlo hhi hb1 hb4

/-- Numeric anchor: `syracuseMap 1 (2/9) = 0`. -/
example : syracuseMap 1 (2 / 9) = 0 := by norm_num [syracuseMap]

/-- Numeric anchor: `syracuseMap 1 (1/4) = 1/16`. -/
example : syracuseMap 1 (1 / 4) = 1 / 16 := by norm_num [syracuseMap]

/-- Numeric anchor: `loTile 1 = 2/9`. -/
example : loTile 1 = 2 / 9 := by norm_num [loTile]

/-- Numeric anchor: `hiTile 1 = 1/4`. -/
example : hiTile 1 = 1 / 4 := by norm_num [hiTile]

/-- Numeric anchor: `1/16 < loTile 4 = 16/243`. -/
example : (1 / 16 : ℚ) < loTile 4 := by norm_num [loTile]

end SpecCheck.SyracuseBijection

/-! ### `ZeroEntropyCages` and `DiscreteFluidCertificates` -/

namespace SpecCheck.NewModules

open Mahler32.ZeroEntropyCages Mahler32.DiscreteFluidCertificates

/-- Statement lock: the integer-vanishing engine. -/
example {M : ℤ} {N : ℕ} (h1 : (2 : ℤ) ^ N ∣ M) (h2 : |M| < (2 : ℤ) ^ N) : M = 0 :=
  exclusion_integer h1 h2

/-- Statement lock: the exact four-term `[2/7, 5/7)` cage. -/
example (x : ℚ) (h0 : 2 / 7 ≤ x) (h1 : x < 5 / 7)
    (a1 : 2 / 7 ≤ Tq x) (b1 : Tq x < 5 / 7)
    (a2 : 2 / 7 ≤ Tq (Tq x)) (b2 : Tq (Tq x) < 5 / 7)
    (a3 : 2 / 7 ≤ Tq (Tq (Tq x))) (b3 : Tq (Tq (Tq x)) < 5 / 7) : False :=
  cage_two_sevenths x h0 h1 ⟨a1, b1, a2, b2, a3, b3⟩

/-- Numeric anchor: `Tcup (4/19) = 6/19`. -/
example : Tcup (4 / 19) = 6 / 19 := by
  unfold Tcup
  norm_num

/-- Numeric anchor: the exact three-cycle return. -/
example : Tcup (Tcup (Tcup (4 / 19))) = 4 / 19 := by
  unfold Tcup
  norm_num

end SpecCheck.NewModules

end
