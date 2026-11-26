/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for `fano-sparse24-perm`

Pure-`Init` (zero Mathlib) definitions for:
1. Universal `k:m` structured Top-`k` EF21 contraction.
2. Joint `k:m + MXFP4` (E8M0 power-of-2, `M_eff = 3`, `B = 32`) and dense Ternary contraction.
3. Exact `2:4` column-permutation feasibility on `8` columns (`35` `(4,4)`-bipartitions),
   the Fano plane `PG(2, 2)` obstruction (`R_crit(2, 3) = 7`), and the 3-column sunflower
   obstruction (`R_crit(2, 4) = 4`).
4. Exact rational Uniform and Laplace `k:2k` order-statistic NMSE laws.
-/

namespace FanoSparse24Perm

/-! ## 1. Finite Sums and Structured Top-`k` EF21 Contraction -/

/-- Exact rational sum `∑_{i=0}^{n-1} f i`. -/
def sumRange : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

/-- A length-`m` block of nonnegative magnitudes sorted in non-increasing order
    `a 0 ≥ a 1 ≥ ... ≥ a (m - 1) ≥ 0`. -/
def NonIncreasingMags (m : Nat) (a : Nat → Rat) : Prop :=
  (∀ i : Nat, i < m → (0 : Rat) ≤ a i) ∧
  (∀ i j : Nat, i ≤ j → j < m → a j ≤ a i)

/-- Total squared energy `∑_{i=0}^{m-1} (a i)^2` of an `m`-block. -/
def blockEnergy (m : Nat) (a : Nat → Rat) : Rat :=
  sumRange m (fun i => a i * a i)

/-- Retained squared energy `∑_{i=0}^{k-1} (a i)^2` of the top-`k` entries. -/
def blockKeptEnergy (k : Nat) (a : Nat → Rat) : Rat :=
  sumRange k (fun i => a i * a i)

/-- Pruned squared error `∑_{j=0}^{m-k-1} (a (k + j))^2` of the bottom `m - k` entries. -/
def blockPrunedErr (k m : Nat) (a : Nat → Rat) : Rat :=
  sumRange (m - k) (fun j => a (k + j) * a (k + j))

/-- Universal structured Top-`k` EF21 contraction constant `α(k:m) = k / m`. -/
def ef21Alpha (k m : Nat) : Rat :=
  (k : Rat) / (m : Rat)

/-! ## 2. Joint `k:m + MXFP4` (`B = 32`) & Dense Ternary Quantization -/

/-- Exact nearest-level squared quantization error for E2M1 on `[0, 3]`
    (MXFP4 E8M0 worst-case aligned domain `M_eff = 3`, levels `{0, 1/2, 1, 3/2, 2, 3}`,
    midpoints `{1/4, 3/4, 5/4, 7/4, 5/2}`). -/
def e2m1ErrSq (y : Rat) : Rat :=
  if y ≤ 1 / 4 then y * y
  else if y ≤ 3 / 4 then (y - 1 / 2) * (y - 1 / 2)
  else if y ≤ 5 / 4 then (y - 1) * (y - 1)
  else if y ≤ 7 / 4 then (y - 3 / 2) * (y - 3 / 2)
  else if y ≤ 5 / 2 then (y - 2) * (y - 2)
  else (y - 3) * (y - 3)

/-- Joint `k:m + MXFP4` squared error of a single sorted `m`-group:
    top `k` entries quantized via `e2m1ErrSq`, bottom `m - k` entries pruned to `0`. -/
def groupMxfp4ErrSq (k m : Nat) (a : Nat → Rat) : Rat :=
  sumRange k (fun i => e2m1ErrSq (a i)) +
  sumRange (m - k) (fun j => a (k + j) * a (k + j))

/-- Total joint `k:m + MXFP4` squared error across `g` groups of size `m`. -/
def blockMxfp4ErrSq (g k m : Nat) (x : Nat → Nat → Rat) : Rat :=
  sumRange g (fun r => groupMxfp4ErrSq k m (x r))

/-- Total squared energy across `g` groups of size `m`. -/
def blockMxfp4Energy (g m : Nat) (x : Nat → Nat → Rat) : Rat :=
  sumRange g (fun r => blockEnergy m (x r))

/-- Valid MXFP4 `g`-group block of `m`-groups with block maximum `M_eff = 3`
    anchored in group `0` (`x 0 0 = 3`). -/
def ValidMxfp4Block (g m : Nat) (x : Nat → Nat → Rat) : Prop :=
  (∀ r : Nat, r < g → NonIncreasingMags m (x r)) ∧
  (∀ r i : Nat, r < g → i < m → x r i ≤ 3) ∧
  x 0 0 = 3

/-- Exact nearest-level squared quantization error for Ternary `{-1, 0, +1}` on `[0, 1]`. -/
def ternaryErrSq (y : Rat) : Rat :=
  if y ≤ 1 / 2 then y * y else (y - 1) * (y - 1)

/-- Closed-form dense max-abs Ternary EF21 contraction constant `4 / (B + 3)`. -/
def ternaryDenseAlpha (B : Nat) : Rat :=
  (4 : Rat) / ((B + 3 : Nat) : Rat)

/-! ## 3. Exact `2:4` Column-Permutation Feasibility, Fano Plane & Sunflower Obstructions -/

/-- Universal first-moment lower bound `⌈(4C - 1)(4C - 2) / 6⌉` for `R_crit(C, 3)`. -/
def rCritLowerBound3 (C : Nat) : Nat :=
  ((4 * C - 1) * (4 * C - 2) + 5) / 6

/-- Test bit `i` of natural number bitmask `m`. -/
def bitTest (m i : Nat) : Bool :=
  (m / 2 ^ i) % 2 == 1

/-- Hamming weight (number of set bits in `0..7`) of an 8-column bitmask. -/
def popcount8 (m : Nat) : Nat :=
  (if bitTest m 0 then 1 else 0) +
  (if bitTest m 1 then 1 else 0) +
  (if bitTest m 2 then 1 else 0) +
  (if bitTest m 3 then 1 else 0) +
  (if bitTest m 4 then 1 else 0) +
  (if bitTest m 5 then 1 else 0) +
  (if bitTest m 6 then 1 else 0) +
  (if bitTest m 7 then 1 else 0)

/-- Intersection cardinality `|a ∩ b|` of two 8-column bitmasks. -/
def interCount8 (a b : Nat) : Nat :=
  (if bitTest a 0 && bitTest b 0 then 1 else 0) +
  (if bitTest a 1 && bitTest b 1 then 1 else 0) +
  (if bitTest a 2 && bitTest b 2 then 1 else 0) +
  (if bitTest a 3 && bitTest b 3 then 1 else 0) +
  (if bitTest a 4 && bitTest b 4 then 1 else 0) +
  (if bitTest a 5 && bitTest b 5 then 1 else 0) +
  (if bitTest a 6 && bitTest b 6 then 1 else 0) +
  (if bitTest a 7 && bitTest b 7 then 1 else 0)

/-- Predicate that `p` is a canonical `(4, 4)`-bipartition of `Fin 8` (half containing column `0`). -/
def isBipartition8 (p : Nat) : Bool :=
  decide (p < 256) && bitTest p 0 && decide (popcount8 p = 4)

/-- Predicate that `(4, 4)`-bipartition `p` is `2:4`-feasible for row bitmask `r`:
    at most 2 entries of `r` lie in `p` and at most 2 lie in the complement of `p`. -/
def bipartitionFeasible (p r : Nat) : Bool :=
  let c := interCount8 p r
  decide (c ≤ 2 ∧ popcount8 r - c ≤ 2)

/-- Predicate that bipartition `p` is killed (infeasible) by row bitmask `r`. -/
def bipartitionKilled (p r : Nat) : Bool :=
  !(bipartitionFeasible p r)

/-- All `35` canonical `(4, 4)`-bipartitions of `8` columns. -/
def allBipartitions8 : List Nat :=
  (List.range 256).filter isBipartition8

/-- All `56` weight-3 row bitmasks on `8` columns. -/
def allTriples8 : List Nat :=
  (List.range 256).filter (fun r => decide (popcount8 r = 3))

/-- All `70` weight-4 row bitmasks on `8` columns. -/
def allQuads8 : List Nat :=
  (List.range 256).filter (fun r => decide (popcount8 r = 4))

/-- The `7` lines of the Fano plane `PG(2, 2)` on columns `{0, 1, 2, 3, 4, 5, 6}` of `8`. -/
def fanoLines8 : List Nat :=
  [ 2 ^ 0 + 2 ^ 1 + 2 ^ 3,
    2 ^ 1 + 2 ^ 2 + 2 ^ 4,
    2 ^ 2 + 2 ^ 3 + 2 ^ 5,
    2 ^ 3 + 2 ^ 4 + 2 ^ 6,
    2 ^ 4 + 2 ^ 5 + 2 ^ 0,
    2 ^ 5 + 2 ^ 6 + 2 ^ 1,
    2 ^ 6 + 2 ^ 0 + 2 ^ 2 ]

/-- The `4` weight-4 sunflower rows sharing 3-column core `{0, 1, 2}` with petals `3, 4, 5, 6`. -/
def sunflowerRows8 : List Nat :=
  [ 2 ^ 0 + 2 ^ 1 + 2 ^ 2 + 2 ^ 3,
    2 ^ 0 + 2 ^ 1 + 2 ^ 2 + 2 ^ 4,
    2 ^ 0 + 2 ^ 1 + 2 ^ 2 + 2 ^ 5,
    2 ^ 0 + 2 ^ 1 + 2 ^ 2 + 2 ^ 6 ]

/-- Existence of a `2:4`-feasible `(4, 4)`-bipartition for a list of row bitmasks. -/
def rowsFeasible8 (rows : List Nat) : Prop :=
  ∃ p : Nat, p ∈ allBipartitions8 ∧ ∀ r : Nat, r ∈ rows → bipartitionFeasible p r = true

/-! ## 4. Exact Rational Order-Statistic `k:2k` NMSE Laws -/

/-- Exact Uniform `[-1, 1]` order-statistic sum of the `k` smallest squared magnitudes
    out of `2k`: `∑_{i=1}^k i(i+1) / ((2k+1)(2k+2))`. -/
def unifOrderStatSum (k : Nat) : Rat :=
  sumRange k (fun i =>
    (((i + 1) * (i + 2) : Nat) : Rat) / (((2 * k + 1) * (2 * k + 2) : Nat) : Rat))

/-- Exact Uniform `k:2k` NMSE from order statistics divided by total variance `2k / 3`. -/
def unifNMSEFromOrderStats (k : Nat) : Rat :=
  unifOrderStatSum k / ((2 * k : Rat) / 3)

/-- Closed-form Uniform `k:2k` NMSE `(k + 2) / (4 (2k + 1))`. -/
def unifNMSE (k : Nat) : Rat :=
  ((k + 2 : Nat) : Rat) / ((4 * (2 * k + 1) : Nat) : Rat)

/-- Tail harmonic sum `H_1(m, i) = ∑_{j=0}^{i-1} 1 / (m - j)`. -/
def harmonicTail1 (m i : Nat) : Rat :=
  sumRange i (fun j => (1 : Rat) / ((m - j : Nat) : Rat))

/-- Tail squared harmonic sum `H_2(m, i) = ∑_{j=0}^{i-1} 1 / (m - j)^2`. -/
def harmonicTail2 (m i : Nat) : Rat :=
  sumRange i (fun j => (1 : Rat) / (((m - j) * (m - j) : Nat) : Rat))

/-- Exact Laplace `(0, 1)` `k:2k` NMSE via Rényi's exponential order-statistic representation:
    `(1 / (4k)) ∑_{i=1}^k (H_1(2k, i)^2 + H_2(2k, i))`. -/
def laplaceNMSE (k : Nat) : Rat :=
  (1 / ((4 * k : Nat) : Rat)) *
    sumRange k (fun i =>
      let h1 := harmonicTail1 (2 * k) (i + 1)
      h1 * h1 + harmonicTail2 (2 * k) (i + 1))

end FanoSparse24Perm
