/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Shared Pure-`Init` Definitions (`deltanet-wy-stability`)

All definitions required to state the five headline theorems of
`DeltanetWyStabilityChallenge` using Lean 4 `Init` only (zero Mathlib).
-/

namespace DeltanetWyStability

/-- Structural finite sum over `Fin n` with values in `Rat`. -/
def sumFin : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | _ + 1, f => sumFin (fun i => f i.castSucc) + f ⟨_, Nat.lt_succ_self _⟩

/-- Inner product of two `d`-dimensional rational vectors. -/
def dot {d : Nat} (u v : Fin d → Rat) : Rat :=
  sumFin (fun i => u i * v i)

/-- Squared Euclidean norm of a `d`-dimensional rational vector. -/
def normSq {d : Nat} (v : Fin d → Rat) : Rat :=
  dot v v

/-- Absolute value on `Rat`. -/
def ratAbs (x : Rat) : Rat :=
  if 0 ≤ x then x else -x

/-- Natural-number power on `Rat`. -/
def ratPow (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => ratPow x n * x

/-- `m × n` rational matrix. -/
abbrev RatMat (m n : Nat) := Fin m → Fin n → Rat

/-- `n × n` identity matrix over `Rat`. -/
def idMat (n : Nat) : RatMat n n :=
  fun i j => if i = j then 1 else 0

/-- Matrix addition. -/
def matAdd {m n : Nat} (A B : RatMat m n) : RatMat m n :=
  fun i j => A i j + B i j

/-- Matrix negation. -/
def matNeg {m n : Nat} (A : RatMat m n) : RatMat m n :=
  fun i j => -(A i j)

/-- Matrix multiplication. -/
def matMul {m p n : Nat} (A : RatMat m p) (B : RatMat p n) : RatMat m n :=
  fun i j => sumFin (fun k => A i k * B k j)

/-- Natural-number matrix power. -/
def matPow {n : Nat} (A : RatMat n n) : Nat → RatMat n n
  | 0 => idMat n
  | k + 1 => matMul (matPow A k) A

/-- Standard binomial coefficient `C(n, k)` via Pascal's recurrence. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Gated DeltaNet rank-1 state transition operator `T(v) = α (v - β ⟨k, v⟩ k)`. -/
def deltaNetStep {d : Nat} (α β : Rat) (k v : Fin d → Rat) : Fin d → Rat :=
  fun i => α * (v i - β * dot k v * k i)

/-- Non-negative OCP MXFP4 (`E2M1`) round-to-nearest-up quantizer on grid
    `{0, 1/2, 1, 3/2, 2, 3, 4, 6}` with midpoints `{1/4, 3/4, 5/4, 7/4, 5/2, 7/2, 5}`. -/
def e2m1QuantNonneg (x : Rat) : Rat :=
  if x < 1 / 4 then 0
  else if x < 3 / 4 then 1 / 2
  else if x < 5 / 4 then 1
  else if x < 7 / 4 then 3 / 2
  else if x < 5 / 2 then 2
  else if x < 7 / 2 then 3
  else if x < 5 then 4
  else 6

/-- Signed OCP MXFP4 (`E2M1`) quantizer. -/
def e2m1Quant (x : Rat) : Rat :=
  if 0 ≤ x then e2m1QuantNonneg x else -(e2m1QuantNonneg (-x))

/-- Exact extremal witness for OCP MXFP4 (`B = 32`, OCP v1.0 scale `max |y| ≥ 4`):
    `y_0 = 5 → 6`, `y_{1..31} = 1/4 → 1/2`, attaining squared-norm blowup `700 / 431`. -/
def e2m1OcpWitness : Fin 32 → Rat :=
  fun i => if i.val = 0 then 5 else 1 / 4

/-- Exact extremal witness for MXFP4 (`B = 32`, max-fit scale `max |y| > 3`):
    `y_0 = 7/2 → 4`, `y_{1..31} = 1/4 → 1/2`, attaining squared-norm blowup `380 / 227`. -/
def e2m1MaxFitWitness : Fin 32 → Rat :=
  fun i => if i.val = 0 then 7 / 2 else 1 / 4

/-- Exact normal-range squared-norm blowup `((2^(m+1) + 2) / (2^(m+1) + 1))^2`
    for an `m`-bit mantissa floating-point format. -/
def normalMaxRatioSq (m : Nat) : Rat :=
  let p : Rat := ((2 ^ (m + 1) : Nat) : Rat)
  ((p + 2) / (p + 1)) * ((p + 2) / (p + 1))

/-- Lower rounding midpoint `2^m + 1/2` of the worst-case normal bin `[2^m, 2^m + 1]`. -/
def normalBinMid (m : Nat) : Rat :=
  ((2 ^ m : Nat) : Rat) + 1 / 2

/-- Upper endpoint `2^m + 1` of the worst-case normal bin `[2^m, 2^m + 1]`. -/
def normalBinUpper (m : Nat) : Rat :=
  ((2 ^ m : Nat) : Rat) + 1

/-- Safe step-size ceiling `β_safe(α = 1) = 2 / R_max` at decay gate `α = 1`. -/
def betaSafe (R : Rat) : Rat := 2 / R

/-- Single Householder reflection/contraction step `v ↦ v - β ⟨k, v⟩ k`. -/
def hhStep {d : Nat} (β : Rat) (k v : Fin d → Rat) : Fin d → Rat :=
  fun a => v a - β * dot k v * k a

/-- Sequential application of Householder factors `∏_{m = start}^{start + len - 1} (I - β_m k_m k_m^T)`
    to an initial vector `v`. -/
def hhChain {C d : Nat} (betas : Fin C → Rat) (keys : Fin C → Fin d → Rat)
    (start : Nat) : Nat → (Fin d → Rat) → (Fin d → Rat)
  | 0, v => v
  | n + 1, v =>
    let prev := hhChain betas keys start n v
    if h : start + n < C then
      hhStep (betas ⟨start + n, h⟩) (keys ⟨start + n, h⟩) prev
    else
      prev

/-- Strictly lower-triangular chunkwise WY matrix
    `L_{i, j} = β_i α^{i - j} ⟨k_i, k_j⟩` for `i > j` and `0` otherwise. -/
def wyL (C d : Nat) (α : Rat) (betas : Fin C → Rat) (keys : Fin C → Fin d → Rat) : RatMat C C :=
  fun i j =>
    if j.val < i.val then
      betas i * ratPow α (i.val - j.val) * dot (keys i) (keys j)
    else
      0

/-- Closed-form chunkwise WY inverse matrix `T = (I + L)^{-1}`:
    `T_{i, i} = 1`, `T_{i, j} = -β_i α^{i - j} ⟨k_i, (∏_{m=j+1}^{i-1} (I - β_m k_m k_m^T)) k_j⟩`
    for `i > j`, and `0` for `i < j`. -/
def wyT (C d : Nat) (α : Rat) (betas : Fin C → Rat) (keys : Fin C → Fin d → Rat) : RatMat C C :=
  fun i j =>
    if i = j then 1
    else if j.val < i.val then
      -(betas i * ratPow α (i.val - j.val) *
        dot (keys i) (hhChain betas keys (j.val + 1) (i.val - j.val - 1) (keys j)))
    else
      0

/-- Aligned strictly lower-triangular matrix `(L_C)_{i, j} = β` for `i > j`, else `0`. -/
def alignedL (C : Nat) (β : Rat) : RatMat C C :=
  fun i j => if j.val < i.val then β else 0

/-- Block lower-triangular `(n + m) × (n + m)` matrix `[[A, 0], [C, D]]`. -/
def blockLower {n m : Nat} (A : RatMat n n) (C : RatMat m n) (D : RatMat m m) :
    RatMat (n + m) (n + m) :=
  fun i j =>
    if hi : i.val < n then
      if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else
      if hj : j.val < n then
        C ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩ ⟨j.val, hj⟩
      else
        D ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩
          ⟨j.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hj) j.isLt⟩

/-- Recursive 2×2 Block-Schur inverse `[[A_inv, 0], [-D_inv * C * A_inv, D_inv]]`. -/
def blockSchurInv {n m : Nat} (A_inv : RatMat n n) (C : RatMat m n) (D_inv : RatMat m m) :
    RatMat (n + m) (n + m) :=
  blockLower A_inv (matNeg (matMul (matMul D_inv C) A_inv)) D_inv

end DeltanetWyStability
