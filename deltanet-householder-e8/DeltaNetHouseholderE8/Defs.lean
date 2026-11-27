/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Trusted Definitions (`deltanet-householder-e8`)

Pure-`Init` (zero Mathlib) definitions for:
1. Rational finite sums, inner products, Euclidean squared norm, and Householder rank-1 updates.
2. Binade-bottom round-up ratio `r_m`, the resulting squared-norm bound `S_max^(1)(m)` and the `1`-ULP / `2`-ULP ceilings (rational model; IEEE-754 rounding itself is not formalised).
3. Aligned-key WY triangular matrix `I + 2 * strictLower(1 1^T)` and its exact inverse `T`.
4. Pure-integer 8D `D_8` and scaled `2 * E_8` root lattices, reflections, and the non-Weyl
   `Hamming[8,4,4]` weight-4 witness.
-/

namespace DeltaNetHouseholderE8

/-! ### Rational Vector & Dyadic Primitives -/

/-- Recursive sum over `Fin k` in `Rat`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f =>
      finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Sum of `f : Fin n → Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

/-- Exact rational inner product `⟨u, v⟩ = ∑_i u_i v_i`. -/
def dotProd {d : Nat} (u v : Fin d → Rat) : Rat :=
  finSum (fun i => u i * v i)

/-- Exact rational squared Euclidean norm `‖u‖_2^2 = ∑_i u_i^2`. -/
def l2NormSq {d : Nat} (u : Fin d → Rat) : Rat :=
  dotProd u u

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

/-- Exact dyadic power `2^k` in `Rat`. -/
def pow2Rat (k : Nat) : Rat :=
  ((2 ^ k : Nat) : Rat)

/-- Exact inverse dyadic power `2^{-k} = 1 / 2^k` in `Rat`. -/
def invPow2Rat (k : Nat) : Rat :=
  1 / pow2Rat k

/-! ### Pillar 1: Householder Rank-1 Update & 2-ULP Ceiling -/

/-- Exact Householder / DeltaNet rank-1 state transition `(I - β k k^T) v`. -/
def householderApply {d : Nat} (β : Rat) (k v : Fin d → Rat) : Fin d → Rat :=
  fun i => v i - β * dotProd k v * k i

/-- Binade-bottom relative round-up ratio (the value of a tie-to-even round-up at the bottom of a binade; used as a hypothesised per-coordinate bound, not derived from IEEE-754)
    `(1 + 2^{-m}) / (1 + 2^{-(m+1)}) = (2^{m+1} + 2) / (2^{m+1} + 1)`. -/
def rneBinadeBottomRatio (m : Nat) : Rat :=
  (1 + invPow2Rat m) / (1 + invPow2Rat (m + 1))

/-- Squared-norm bound `S_max^(1)(m) = ((2^{m+1} + 2) / (2^{m+1} + 1))^2`
    (the square of `rneBinadeBottomRatio`; a bound under that hypothesis, not proved attained). -/
def sMax1 (m : Nat) : Rat :=
  let r := (pow2Rat (m + 1) + 2) / (pow2Rat (m + 1) + 1)
  r * r

/-- Explicit 8-dimensional vector on the `FP8-E4M3` grid (`m = 3`) with exact
    squared norm `287 / 256` (`1.12109375`). -/
def fp8WitnessVec : Fin 8 → Rat
  | ⟨0, _⟩ => 9 / 16
  | ⟨1, _⟩ => 9 / 16
  | ⟨2, _⟩ => 9 / 16
  | ⟨3, _⟩ => 9 / 32
  | ⟨4, _⟩ => 9 / 32
  | ⟨5, _⟩ => 3 / 32
  | ⟨6, _⟩ => 1 / 16
  | ⟨7, _⟩ => 1 / 32

/-- 1 ULP below `2` in `[1, 2)` for `m`-bit mantissa: `β_1(m) = 2 - 2^{-m}`. -/
def betaOneUlp (m : Nat) : Rat :=
  2 - invPow2Rat m

/-- 2 ULPs below `2` in `[1, 2)` for `m`-bit mantissa: `β_2(m) = 2 - 2^{1-m} = 2 - 2 * 2^{-m}`. -/
def betaTwoUlp (m : Nat) : Rat :=
  2 - 2 * invPow2Rat m

/-! ### Pillar 2: Chunkwise WY Triangular Inverse -/

/-- Exact rational matrix multiplication `(A * B)_{i, j} = ∑_l A_{i, l} B_{l, j}`. -/
def matMul {C : Nat} (A B : Fin C → Fin C → Rat) (i j : Fin C) : Rat :=
  finSum (fun l => A i l * B l j)

/-- Exact `C × C` identity matrix over `Rat`. -/
def identityMat (C : Nat) (i j : Fin C) : Rat :=
  if i = j then 1 else 0

/-- Aligned unit-key WY triangular matrix `A = I + 2 * strictLower(1 1^T)` at `β = 2`. -/
def wyAlignedMat (C : Nat) (i j : Fin C) : Rat :=
  if i.val = j.val then 1
  else if j.val < i.val then 2
  else 0

/-- Exact inverse `T = (I + 2 * strictLower(1 1^T))^{-1}` with alternating entries
    `T_{i, j} = (-1)^{i - j} * 2` for `i > j`. -/
def wyAlignedInv (C : Nat) (i j : Fin C) : Rat :=
  if i.val = j.val then 1
  else if j.val < i.val then (if (i.val - j.val) % 2 = 0 then 2 else -2)
  else 0

/-- Row `ℓ_1`-norm `∑_j |M_{i, j}|` of row `i` of a `C × C` rational matrix. -/
def rowL1Norm {C : Nat} (M : Fin C → Fin C → Rat) (i : Fin C) : Rat :=
  finSum (fun j => ratAbs (M i j))

/-! ### Pillar 3: Pure-Integer 8D `D_8`, `2 * E_8`, and `Hamming[8,4,4]` -/

/-- Exact pure-integer 8D dot product. -/
def intDot8 (u v : Fin 8 → Int) : Int :=
  u ⟨0, by decide⟩ * v ⟨0, by decide⟩ +
  u ⟨1, by decide⟩ * v ⟨1, by decide⟩ +
  u ⟨2, by decide⟩ * v ⟨2, by decide⟩ +
  u ⟨3, by decide⟩ * v ⟨3, by decide⟩ +
  u ⟨4, by decide⟩ * v ⟨4, by decide⟩ +
  u ⟨5, by decide⟩ * v ⟨5, by decide⟩ +
  u ⟨6, by decide⟩ * v ⟨6, by decide⟩ +
  u ⟨7, by decide⟩ * v ⟨7, by decide⟩

/-- Exact pure-integer 8D squared Euclidean norm. -/
def intNormSq8 (u : Fin 8 → Int) : Int :=
  intDot8 u u

/-- Exact pure-integer 8D coordinate sum. -/
def intSum8 (u : Fin 8 → Int) : Int :=
  u ⟨0, by decide⟩ + u ⟨1, by decide⟩ + u ⟨2, by decide⟩ + u ⟨3, by decide⟩ +
  u ⟨4, by decide⟩ + u ⟨5, by decide⟩ + u ⟨6, by decide⟩ + u ⟨7, by decide⟩

/-- The `D_8` integer lattice `{x ∈ ℤ^8 : ∑ x_i ≡ 0 (mod 2)}`. -/
def InD8Lattice (x : Fin 8 → Int) : Prop :=
  intSum8 x % 2 = 0

/-- A `D_8` root `v ∈ ℤ^8` with `‖v‖_2^2 = 2`. -/
def IsD8Root (v : Fin 8 → Int) : Prop :=
  intNormSq8 v = 2

/-- Exact integer `D_8` reflection `R_v(x) = x - ((2 ⟨v, x⟩) / 2) v = x - ⟨v, x⟩ v`. -/
def reflectD8 (v x : Fin 8 → Int) : Fin 8 → Int :=
  fun i => x i - intDot8 v x * v i

/-- The scaled `2 * E_8` root lattice
    `2 E_8 = {x ∈ ℤ^8 : x_0 ≡ x_1 ≡ ... ≡ x_7 (mod 2), ∑ x_i ≡ 0 (mod 4)}`. -/
def InTwoE8Lattice (x : Fin 8 → Int) : Prop :=
  (∀ i : Fin 8, x i % 2 = x ⟨0, by decide⟩ % 2) ∧ intSum8 x % 4 = 0

/-- A root of `2 * E_8`: `w ∈ 2 E_8` with `‖w‖_2^2 = 8` (all 240 roots: 112 integer + 128 half-integer). -/
def IsTwoE8Root (w : Fin 8 → Int) : Prop :=
  InTwoE8Lattice w ∧ intNormSq8 w = 8

/-- Integer-type `2 * E_8` root: all coordinates even (`(±2, ±2, 0^6)`), `‖w‖_2^2 = 8`. -/
def IsTwoE8IntRoot (w : Fin 8 → Int) : Prop :=
  (∀ i : Fin 8, w i % 2 = 0) ∧ intNormSq8 w = 8

/-- Half-integer-type `2 * E_8` root: all coordinates `±1` with an even number of `-1`s (`∑ w_i ≡ 0 (mod 4)`). -/
def IsTwoE8HalfIntRoot (w : Fin 8 → Int) : Prop :=
  (∀ i : Fin 8, w i = 1 ∨ w i = -1) ∧ intSum8 w % 4 = 0

/-- Exact integer `2 * E_8` reflection `R_w(x) = x - ((2 ⟨w, x⟩) / 8) w` (exact bit-shift `>>> 2` on `⟨w, x⟩`). -/
def reflectTwoE8 (w x : Fin 8 → Int) : Fin 8 → Int :=
  fun i => x i - ((2 * intDot8 w x) / 8) * w i

/-- Non-Weyl `Hamming[8,4,4]` weight-4 vector `v = (1, 1, 1, 1, 0, 0, 0, 0)`. -/
def hammingV : Fin 8 → Int :=
  fun i => if i.val < 4 then 1 else 0

/-- Standard basis integer witness `e_0 = (1, 0, 0, 0, 0, 0, 0, 0)`. -/
def hammingX : Fin 8 → Int :=
  fun i => if i.val = 0 then 1 else 0

/-- Even-sum `D_8`-lattice integer witness `(1, 0, 0, 0, 1, 0, 0, 0)`. -/
def hammingXEven : Fin 8 → Int :=
  fun i => if i.val = 0 ∨ i.val = 4 then 1 else 0

/-- Cast an 8D integer vector into `Fin 8 → Rat`. -/
def ratOfIntVec8 (u : Fin 8 → Int) : Fin 8 → Rat :=
  fun i => (u i : Rat)

end DeltaNetHouseholderE8
