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

/-! ## Core — `Mahler32.Basic` -/

namespace SpecCheck.Basic

open Mahler32

/-- Lock: `step x = x + (x+1)/2`. -/
example (x : ℕ) : step x = x + (x + 1) / 2 := rfl

/-- Statement lock: the next parity is the second binary digit. -/
example (x : ℕ) : step x % 2 = x / 2 % 2 := step_parity x

/-- Numeric anchor: `step 7 = 11`. -/
example : step 7 = 11 := by decide

end SpecCheck.Basic

/-! ## Core — `Mahler32.QuiverMonotone` (mathlib4#44885 mirror) -/

namespace SpecCheck.QuiverMonotone

universe u v

/-- Lock: `Quiver.Monotone f` is exactly arrowwise `≤`. -/
example {V : Type u} [Quiver V] {α : Type v} [Preorder α] (f : V → α) :
    Quiver.Monotone f ↔ ∀ ⦃a b : V⦄, (a ⟶ b) → f a ≤ f b := Iff.rfl

/-- Lock: `Quiver.StrictMono f` is exactly arrowwise `<`. -/
example {V : Type u} [Quiver V] {α : Type v} [Preorder α] (f : V → α) :
    Quiver.StrictMono f ↔ ∀ ⦃a b : V⦄, (a ⟶ b) → f a < f b := Iff.rfl

/-- Statement lock: strict monotonicity implies monotonicity. -/
example {V : Type u} [Quiver V] {α : Type v} [Preorder α] {f : V → α}
    (hf : Quiver.StrictMono f) : Quiver.Monotone f :=
  hf.monotone

/-- Statement lock: `Reachable` is a partial order under a strictly monotone potential. -/
example {V : Type u} [Quiver V] {α : Type v} [Preorder α] {f : V → α}
    (hf : Quiver.StrictMono f) : IsPartialOrder V Quiver.Reachable :=
  Quiver.StrictMono.isPartialOrder_reachable hf

end SpecCheck.QuiverMonotone

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

/-- Lock: `gapPot` is the order-dual depth `OrderDual.toDual (dagDepth ·)`. -/
example (v : GapV) : gapPot v = OrderDual.toDual (dagDepth v.1) := rfl

/-- Lock: `CarryStep g h` is membership in the two-branch carry successor set. -/
example (g h : Fin 128) : CarryStep g h ↔ h ∈ carrySucc g := Iff.rfl

/-- Lock: `carrySucc g = {zStep g, zStep g + 64}`. -/
example (g : Fin 128) : carrySucc g = {zStep g, embed128 ((zStep g).val + 64)} := rfl

end SpecCheck.DAGBoundedGap

/-! ## Task 6 — `Mahler32.TwoWorldPadeCriterion` (Archimedean–`2`-adic Padé Comparison) -/

namespace SpecCheck.TwoWorldPadeCriterion

open Mahler32.TwoWorldPadeCriterion

/-- Lock: `[1/2]` Padé value `e/(1-c)`. -/
example (e c : ℚ) : pade12 e c = e / (1 - c) := rfl

/-- Lock: `[1/1]` Padé value `e(1+c)`. -/
example (e c : ℚ) : pade11 e c = e * (1 + c) := rfl

/-- Statement lock: Padé discrepancy identity. -/
example (e c : ℚ) (hc : c ≠ 1) : pade12 e c - pade11 e c = e * c ^ 2 / (1 - c) :=
  two_world_identity e c hc

/-- Statement lock: the integer-valued complementary factor. -/
example : (1 / 9 : ℚ) * 9 = 1 := integer_divisibility_bound

/-- Numeric anchor: at `c = 1/2`, `pade12 1 (1/2) = 2`. -/
example : pade12 1 (1 / 2) = 2 := by norm_num [pade12]

/-- Statement lock: simultaneous Archimedean and `2`-adic (`ℝ × ℚ₂`) isolation bounds. -/
example (g0 : ℕ) (hg0 : 1 ≤ g0) {U V : List ℕ}
    (hU : validWord94 U) (hV : validWord94 V) (hs : 0 < V.length) (w : ℕ)
    (hmatch : matchesWord94 g0 (U ++ repeatWord V w)) :
    (4 : ℚ) ^ (U.length + w * V.length) ≤
        ((g0 : ℚ) - qStar U V) * (9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - (4 : ℚ) ^ V.length) ∧
      ((g0 : ℚ) - qStar U V) * (9 : ℚ) ^ U.length * ((9 : ℚ) ^ V.length - (4 : ℚ) ^ V.length) <
        ((g0 : ℚ) + 3 / 5) * (9 : ℚ) ^ (U.length + V.length) :=
  two_world_ghost_bounds hg0 hU hV hs w hmatch

/-- Statement lock: unconditional exclusion of all eventually periodic `9/4` orbits. -/
example (g0 : ℕ) (hg0 : 1 ≤ g0) {U V : List ℕ}
    (hU : validWord94 U) (hV : validWord94 V) (hs : 0 < V.length) :
    ¬ ∀ w : ℕ, matchesWord94 g0 (U ++ repeatWord V w) :=
  no_eventually_periodic_94 hg0 hU hV hs

/-- Statement lock: repetition exponent bound `w < 317/200 + (117/200)(r/s) + m/s`. -/
example (g0 m w : ℕ) (hg0 : 1 ≤ g0)
    (hm : (g0 : ℚ) + 3 / 5 ≤ (4 : ℚ) ^ m) {U V : List ℕ} (hU : validWord94 U)
    (hV : validWord94 V) (hs : 0 < V.length)
    (hmatch : matchesWord94 g0 (U ++ repeatWord V w)) :
    (w : ℚ) < (317 / 200 : ℚ) + (117 / 200 : ℚ) * ((U.length : ℚ) / (V.length : ℚ)) +
      (m : ℚ) / (V.length : ℚ) :=
  repetition_exponent_bound hg0 hm hU hV hs hmatch

/-- Statement lock: mod-9 non-vanishing congruence criterion for rational `q/b`. -/
example {r d : ℕ} {c : ℕ → ℕ → ℤ} {q b : ℤ}
    (hq : (9 : ℤ) ∣ q) (hb : ¬ ((3 : ℤ) ∣ b))
    (hL : polyTelescopeRat r d c q b (4 / 9 : ℚ) = 0) : (9 : ℤ) ∣ c 0 d :=
  mod_nine_gate_rat hq hb hL

/-- Statement lock: mod-9 criterion specialized at `B₂(4/9) = -9(5 g₀ + 2)/5`. -/
example {r d : ℕ} {c : ℕ → ℕ → ℤ} (g0 : ℕ)
    (hL : polyTelescopeRat r d c (-9 * (5 * (g0 : ℤ) + 2)) 5 (4 / 9 : ℚ) = 0) :
    (9 : ℤ) ∣ c 0 d :=
  mod_nine_gate_b2 g0 hL

/-- Statement lock: contrapositive mod-9 non-vanishing criterion (`9 ∤ c_{0,d}` implies `L(4/9) ≠ 0`). -/
example {r d : ℕ} {c : ℕ → ℕ → ℤ} {q : ℤ}
    (hq : (9 : ℤ) ∣ q) (hc : ¬ ((9 : ℤ) ∣ c 0 d)) :
    polyTelescope r d c q (4 / 9 : ℚ) ≠ 0 :=
  mod_nine_anti_misfire hq hc

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

/-! ### `ZeroEntropyCages` — the two-branch joint relation and its orbits -/

namespace SpecCheck.ZeroEntropyCages

open Mahler32.ZeroEntropyCages

/-- Lock: the joint relation is *exactly* `y = T0 x ∨ y = T1 x`. -/
example (x y : ℚ) : Step x y ↔ y = T0 x ∨ y = T1 x := Iff.rfl

/-- Lock: `Tq` is the single conditional subtraction `{3x/2}`. -/
example (x : ℚ) :
    Tq x = (if (3 * x) / 2 < 1 then (3 * x) / 2 else (3 * x) / 2 - 1) := rfl

/-- Lock: the `[2/7,5/7)` obstruction predicate. -/
example (x : ℚ) : cage27 x ↔ 2 / 7 ≤ x ∧ x < 5 / 7 := Iff.rfl

/-- Lock: the holed obstruction `[5/24,11/24) ∪ [13/24,19/24)`. -/
example (x : ℚ) :
    holedCage x ↔ (5 / 24 ≤ x ∧ x < 11 / 24) ∨ (13 / 24 ≤ x ∧ x < 19 / 24) := Iff.rfl

/-- Statement lock: the integer-vanishing engine. -/
example {M : ℤ} {N : ℕ} (h1 : (2 : ℤ) ^ N ∣ M) (h2 : |M| < (2 : ℤ) ^ N) : M = 0 :=
  exclusion_integer h1 h2

/-- Statement lock: the exact four-term deterministic `[2/7, 5/7)` obstruction. -/
example (x : ℚ) (h0 : 2 / 7 ≤ x) (h1 : x < 5 / 7)
    (a1 : 2 / 7 ≤ Tq x) (b1 : Tq x < 5 / 7)
    (a2 : 2 / 7 ≤ Tq (Tq x)) (b2 : Tq (Tq x) < 5 / 7)
    (a3 : 2 / 7 ≤ Tq (Tq (Tq x))) (b3 : Tq (Tq (Tq x)) < 5 / 7) : False :=
  cage_two_sevenths x h0 h1 ⟨a1, b1, a2, b2, a3, b3⟩

/-- Statement lock: the six-term joint `Step`-orbit inside `[2/7,5/7)`. -/
example :
    Step (3 / 7) (9 / 14) ∧ Step (9 / 14) (13 / 28) ∧
      Step (13 / 28) (39 / 56) ∧ Step (39 / 56) (61 / 112) ∧
      Step (61 / 112) (71 / 224) ∧
      cage27 (3 / 7) ∧ cage27 (9 / 14) ∧ cage27 (13 / 28) ∧
      cage27 (39 / 56) ∧ cage27 (61 / 112) ∧ cage27 (71 / 224) :=
  joint_orbit_two_sevenths

/-- Statement lock: the genuine joint `2`-cycle `2/5 ↔ 3/5`. -/
example :
    Step (2 / 5) (3 / 5) ∧ Step (3 / 5) (2 / 5) ∧
      cage27 (2 / 5) ∧ cage27 (3 / 5) :=
  joint_cycle_two_fifths

/-- Statement lock: the genuine joint `4`-cycle `4/13 ↦ 6/13 ↦ 9/13 ↦ 7/13 ↦ 4/13`. -/
example :
    Step (4 / 13) (6 / 13) ∧ Step (6 / 13) (9 / 13) ∧
      Step (9 / 13) (7 / 13) ∧ Step (7 / 13) (4 / 13) ∧
      cage27 (4 / 13) ∧ cage27 (6 / 13) ∧ cage27 (9 / 13) ∧ cage27 (7 / 13) :=
  joint_cycle_four_thirteenths

/-- Statement lock: the holed obstruction contains the `2/5 ↔ 3/5` joint cycle. -/
example :
    Step (2 / 5) (3 / 5) ∧ Step (3 / 5) (2 / 5) ∧
      holedCage (2 / 5) ∧ holedCage (3 / 5) :=
  holed_cage_two_cycle

/-- Statement lock: the two holed-obstruction transients `4/15 ↦ 2/5` and `11/15 ↦ 3/5`. -/
example :
    Step (4 / 15) (2 / 5) ∧ Step (11 / 15) (3 / 5) ∧
      holedCage (4 / 15) ∧ holedCage (11 / 15) :=
  holed_cage_transients

end SpecCheck.ZeroEntropyCages

/-! ### `DiscreteFluidCertificates` — the exact cup `3`-cycle -/

namespace SpecCheck.DiscreteFluidCertificates

open Mahler32.DiscreteFluidCertificates

/-- Numeric anchor: `Tcup (4/19) = 6/19`. -/
example : Tcup (4 / 19) = 6 / 19 := by
  unfold Tcup
  norm_num

/-- Numeric anchor: the exact three-cycle return. -/
example : Tcup (Tcup (Tcup (4 / 19))) = 4 / 19 := by
  unfold Tcup
  norm_num

end SpecCheck.DiscreteFluidCertificates

/-! ### `Model94Obstructions` — the `9/4` finite-roof model -/

namespace SpecCheck.Model94Obstructions

open Mahler32.Model94Obstructions

/-- Lock: `step94` is the explicit `9/4` branch rule on `g % 4 ∈ {1, 2}`. -/
example (g : ℕ) :
    step94 g =
      (match g % 4 with
        | 1 => some ((9 * g + 3) / 4)
        | 2 => some ((9 * g + 2) / 4)
        | _ => none) := rfl

/-- Lock: `iter94` base case. -/
example (g : ℕ) : iter94 0 g = some g := rfl

/-- Lock: `iter94` successor case. -/
example (k g : ℕ) : iter94 (k + 1) g = (step94 g).bind (iter94 k) := rfl

/-- Lock: `survives94 k g` is exactly `iter94 k g ≠ none`. -/
example (k g : ℕ) : survives94 k g ↔ iter94 k g ≠ none := Iff.rfl

/-- Statement lock: survival is periodic with period `4^k` in the input. -/
example (k t g : ℕ) : survives94 k (g + 4 ^ k * t) ↔ survives94 k g :=
  survives94_add_four_pow k t g

/-- Statement lock: at most three of every Klein-`4` quadruple survive, for **every odd**
`N ≥ 3`. -/
example {N g δ : ℕ} (hN : 3 ≤ N) (hodd : N % 2 = 1) (hg : g < 4 ^ (N - 1))
    (hδ1 : 1 ≤ δ) (hδ3 : δ ≤ 3) :
    ¬ (survives94 (N + 1) g ∧ survives94 (N + 1) (g + δ * 4 ^ (N - 1)) ∧
       survives94 (N + 1) (4 ^ N - 1 - g) ∧
       survives94 (N + 1) (4 ^ N - 1 - (g + δ * 4 ^ (N - 1)))) :=
  odd_rung_klein4_no_four hN hodd hg hδ1 hδ3

/-- Statement lock: the kernel-checked `N = 3` instance of the odd-rung Klein-`4` exclusion. -/
example :
    ((List.range 16).all (fun g =>
        ([1, 2, 3] : List ℕ).all (fun δ =>
          if g + δ * 16 < 64 then
            decide ((({g, g + δ * 16, 63 - g, 63 - (g + δ * 16)} : Finset ℕ).filter
              (fun x => survives94 4 x)).card ≤ 3)
          else true))) = true :=
  odd_rung_klein4_exclusion

end SpecCheck.Model94Obstructions

/-! ### `Model94GlobalDecay` — `9/4` global Fourier decay and midpoint `36^K` intersection -/

namespace SpecCheck.Model94GlobalDecay

open Mahler32.Model94GlobalDecay
open Mahler32.Model94Obstructions

/-- Statement lock: midpoint `g_K mod 36^K ∈ S_K ∩ A_K` for any `2K`-step survivor. -/
example (K g0 gK : ℕ) (h2K : survives94 (2 * K) g0) (hmid : iter94 K g0 = some gK) :
    gK % 36 ^ K < 36 ^ K ∧ inSK K (gK % 36 ^ K) ∧ inAK K (gK % 36 ^ K) :=
  midpoint_double_cantor h2K hmid

/-- Statement lock: `A_K` deterministic interval clamp `[2(9^K - 4^K)/5, 3(9^K - 4^K)/5]`. -/
example (K a : ℕ) (ha : inAK K a) :
    2 * (9 ^ K - 4 ^ K) / 5 ≤ (4 ^ K * a) % 9 ^ K ∧
      (4 ^ K * a) % 9 ^ K ≤ 3 * (9 ^ K - 4 ^ K) / 5 :=
  inAK_scaled_interval ha

/-- Statement lock: `A_K` antipodal exclusion (diameter `≤ (9^K - 4^K)/5` after `4^K` scaling). -/
example (K a₁ a₂ : ℕ) (h1 : inAK K a₁) (h2 : inAK K a₂) :
    |(((4 ^ K * a₁) % 9 ^ K : ℕ) : ℤ) - (((4 ^ K * a₂) % 9 ^ K : ℕ) : ℤ)| ≤
      ((9 ^ K - 4 ^ K) / 5 : ℕ) :=
  inAK_antipodal_exclusion h1 h2

/-- Statement lock: `|(survivorsSet94 K)| = 2^K`. -/
example (K : ℕ) : (survivorsSet94 K).card = 2 ^ K := card_survivorsSet94 K

/-- Statement lock: iterated exact `4`-contraction `‖μ̂_K(4^v u)‖ = ‖μ̂_{K-v}(u)‖`. -/
example (K v : ℕ) (hv : v ≤ K) (u : ℤ) :
    ‖hatMu94 K ((4 : ℤ) ^ v * u)‖ = ‖hatMu94 (K - v) u‖ :=
  norm_hatMu94_four_pow_mul hv u

/-- Statement lock: one-step `9`-multiplication cosine identity. -/
example (K : ℕ) (u : ℤ) :
    ‖hatMu94 (K + 1) (9 * u)‖ =
      |Real.cos (Real.pi * (u : ℝ) / (4 : ℝ) ^ (K + 1))| * ‖hatMu94 K u‖ :=
  norm_hatMu94_nine_mul K u

/-- Statement lock: global odd-frequency decay `∃ C c > 0, ‖μ̂_K(u)‖ ≤ C K^{-c}`. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (K : ℕ), 1 ≤ K → ∀ (u : ℤ), u % 2 = 1 → ‖hatMu94 K u‖ ≤ C * (K : ℝ) ^ (-c) :=
  global_odd_freq_decay

/-- Statement lock: combined `4`-contraction and odd-frequency decay `C (K - v)^{-c}`. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (K v : ℕ), v < K → ∀ (u : ℤ), u % 2 = 1 →
      ‖hatMu94 K ((4 : ℤ) ^ v * u)‖ ≤ C * ((K - v : ℕ) : ℝ) ^ (-c) :=
  global_freq_decay_of_four_pow

/-- Statement lock: path contraction instantiated at `cert42`. -/
example (u : Fin 42) (p : List (Fin 42)) :
    cert42.pathWeight u p ≤ (161 / 162 : ℚ) ^ p.length :=
  cert42_path_decay u p

end SpecCheck.Model94GlobalDecay

/-! ## Issue #17 — `Mahler32.RationalBaseDefs` -/

namespace SpecCheck.RationalBaseDefs

open Mahler32

/-- Definition lock: `wordWeightPQ 3 2 [1, 0] = 3`. -/
example : wordWeightPQ 3 2 [1, 0] = 3 := rfl

/-- Definition lock: `(mkCell 1 2 3 4).width = 1 / 4`. -/
example : (mkCell 1 2 3 4).width = 1 / 4 := by
  norm_num [RatInterval.width, RatInterval.lo, RatInterval.hi, mkCell]

end SpecCheck.RationalBaseDefs

/-! ## Issue #17 — `Mahler32.GeneralPQDecay` -/

namespace SpecCheck.GeneralPQDecay

open Mahler32
open Mahler32.GeneralPQDecay
open Mahler32.TwoWorldPadeCriterion
open Mahler32.Model94GlobalDecay

/-- Statement lock: critical `log_q p` repetition-exponent exclusion bound. -/
example {p q dmin dmax g0 w : ℕ} (hq : 2 ≤ q) (hpq : q < p) (hcop : Nat.Coprime p q)
    (hg0 : 1 ≤ g0) {U V : List ℕ} (hU : validWordPQ dmin dmax U)
    (hV : validWordPQ dmin dmax V) (hs : 0 < V.length)
    (hmatch : matchesWordPQ p q g0 (U ++ repeatWord V w)) :
    (w : ℝ) < Real.log p / Real.log q +
      (Real.log p / Real.log q - 1) * ((U.length : ℝ) / (V.length : ℝ)) +
      Real.log ((g0 : ℝ) + (dmax : ℝ) / ((p : ℝ) - q)) / ((V.length : ℝ) * Real.log q) :=
  repetition_exponent_bound_pq hq hpq hcop hg0 hU hV hs hmatch

/-- Statement lock: general `(p, q)` quantitative Weyl Fourier decay. -/
example (M : TunnelModelPQ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ K : ℕ, 1 ≤ K → ∀ u : ℤ, ¬ ((M.q : ℤ) ∣ u) →
        ‖M.hatMu K u‖ ≤ C * (K : ℝ) ^ (-c) :=
  global_coprime_freq_decay_pq M

/-- Statement lock: Weyl instantiations for `3/2, 4/3, 5/4, 5/3, 7/4, 8/3`. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ K : ℕ, 1 ≤ K → ∀ u : ℤ, ¬ ((3 : ℤ) ∣ u) →
    ‖(TunnelModelPQ.mkConsecutive 8 3 1 (by decide) (by decide) (by decide)).hatMu K u‖ ≤
      C * (K : ℝ) ^ (-c) :=
  weyl_decay_8_3

/-- Statement lock: Karp dual-potential cycle bound & 44-vertex baseline certificate. -/
example (u : Fin 44) (p : List (Fin 44)) (hcyc : DualPotentialCert.pathEnd u p = u) :
    cert44.pathWeight u p ≤ (249 / 250 : ℚ) ^ p.length :=
  cert44_cycle_bound u p hcyc

end SpecCheck.GeneralPQDecay

/-! ## Issue #17 — `Mahler32.ZeroEntropyAutomaton` -/

namespace SpecCheck.ZeroEntropyAutomaton

open Mahler32
open Mahler32.ZeroEntropyAutomaton

/-- Statement lock: soundness of exact overlap check `hasBranchOverlap`. -/
example {p q : ℕ} (hq : 1 ≤ q) (neg : Bool) {I J : RatInterval}
    (hI0 : 0 ≤ I.lo) (hI1 : I.hi ≤ 1) {x y : ℚ}
    (hx : I.mem x) (hy : J.mem y) (hstep : StepPQ p q neg x y) :
    hasBranchOverlap p q neg I J = true :=
  hasBranchOverlap_sound hq neg hI0 hI1 hx hy hstep

/-- Statement lock: zero topological entropy under topological SCC ordering + no internal branching. -/
example {p q N M : ℕ} {neg : Bool} (A : ZeroEntropyAutomaton p q neg N M) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ L : ℕ, (totalPaths (fun i j =>
        hasBranchOverlap p q neg (A.cells i) (A.cells j)) L : ℝ) ≤ C * (1 + ε) ^ L :=
  zero_entropy_of_no_branching_scc A

/-- Certificate lock: `-5/3`, `-3/2` holed (`0.5660 > 1/2`), `-3/2` centered (`0.4284`), `+5/3`. -/
example :
    (1 / 2 : ℚ) < unionWidth [mkCell 147 1000 43 100, mkCell 57 100 853 1000] :=
  cert_neg_3_2_holed_width_gt_half.2

end SpecCheck.ZeroEntropyAutomaton

end
