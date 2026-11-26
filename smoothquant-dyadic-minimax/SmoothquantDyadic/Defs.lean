/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`smoothquant-dyadic-minimax`)

Pure-`Init` (zero Mathlib) exact rational definitions for:
1. Bilinear quantization error `E(A, B, s) = A s^2 + B s^{-2}`, asymmetric-bitwidth SmoothQuant
   interior channel error, classical `SQ(0.5)` suboptimality ratio `(q_X^2 + q_W^2) / (2 q_W q_X)`,
   critical clamping threshold `M_crit = q_X / q_W`, and bulk/total channel objectives.
2. Zero-FLOP dyadic power-of-2 SmoothQuant per-channel `L_2^2` (`5/4`) and squared `L_1` (`9/8`)
   penalty ratios, plus per-tensor coupled `Δ_W(s), Δ_X(s)` penalty ratios (naive `5/2` vs
   global phase-shifted `3/2`).
3. Exact `2 × 2` Walsh-Hadamard matrix `H_2`, matrix multiplication, Frobenius squared norm,
   max-abs entry norm, and parametric `(W(M), X(M))` families for `SQ -> Hadamard` vs
   `Pure Hadamard` and `Hadamard -> SQ` non-commutation separation.
-/

namespace SmoothquantDyadic

/-! ### 1. Bilinear Quantization Error & Asymmetric-Bitwidth SmoothQuant -/

/-- Bilinear quantization error `E(A, B, s) = A s^2 + B / s^2` for diagonal scale `s > 0`. -/
def bilinearErr (A B s : Rat) : Rat :=
  A * (s * s) + B / (s * s)

/-- Interior-channel bilinear error in squared relative scale `u = (s / s_{1/2})^2 > 0`
    for symmetric quantizer levels `(q_W, q_X)`: `E_ch(q_W, q_X, u) = 1 / (q_W^2 u) + u / q_X^2`. -/
def interiorChannelErr (qW qX u : Rat) : Rat :=
  1 / (qW * qW * u) + u / (qX * qX)

/-- Exact rational penalty ratio of classical SmoothQuant (`α = 1/2`, `u = 1`) over optimal
    asymmetric-bitwidth scaling (`u* = q_X / q_W`): `(q_X^2 + q_W^2) / (2 q_W q_X)`. -/
def sqHalfPenaltyRatio (qW qX : Rat) : Rat :=
  (qX * qX + qW * qW) / (2 * qW * qX)

/-- Exact critical outlier threshold `M_crit = q_X / q_W` below which optimal SmoothQuant
    migration clamps to `α* = 0` (`u = 1`). -/
def criticalClampThreshold (qW qX : Rat) : Rat :=
  qX / qW

/-- Bulk-channel first-order Frobenius squared error under SmoothQuant scaling `u = M^{2α} ≥ 1`
    with activation outlier ratio `M ≥ 1`: `E_bulk(q_W, q_X, M, u) = u / (M^2 q_W^2) + 1 / (q_X^2 u)`. -/
def bulkChannelErr (qW qX M u : Rat) : Rat :=
  u / (M * M * qW * qW) + 1 / (qX * qX * u)

/-- Outlier-channel first-order Frobenius squared error (`ρ = 1`, invariant to `α`):
    `E_out(q_W, q_X) = 1 / q_W^2 + 1 / q_X^2`. -/
def outlierChannelErr (qW qX : Rat) : Rat :=
  1 / (qW * qW) + 1 / (qX * qX)

/-- Total first-order Frobenius squared error for `k` outlier channels (`ρ = 1`) and
    `b` bulk channels (`ρ = 1/M`) under SmoothQuant scaling `u = M^{2α}`. -/
def totalCoupledErr (qW qX M u : Rat) (k b : Nat) : Rat :=
  (k : Rat) * outlierChannelErr qW qX + (b : Rat) * bulkChannelErr qW qX M u

/-! ### 2. Dyadic Power-of-2 SmoothQuant Penalty Functions -/

/-- Per-channel `L_2^2` dyadic rounding penalty `(u + 1/u) / 2` where `u = (s_dyad / s*)^2`. -/
def dyadicL2SqPenalty (u : Rat) : Rat :=
  (u + 1 / u) / 2

/-- Per-channel `L_1` bilinear error `A s + B / s`. -/
def bilinearL1Err (A B s : Rat) : Rat :=
  A * s + B / s

/-- Per-channel squared `L_1` dyadic rounding penalty `(u + 2 + 1/u) / 4 = ((r + 1/r)/2)^2`
    where `u = r^2 = (s_dyad / s*)^2`. -/
def dyadicL1SqPenalty (u : Rat) : Rat :=
  (u + 2 + 1 / u) / 4

/-- Per-tensor coupled channel penalty `(M_W^2 / u + M_X^2 * u) / 2` given global squared
    step-size inflations `M_W^2 = max_k u_k` and `M_X^2 = max_k u_k^{-1}`. -/
def perTensorCoupledChannelPenalty (mwSq mxSq u : Rat) : Rat :=
  (mwSq / u + mxSq * u) / 2

/-- Rational maximum of two rationals. -/
def ratMax (a b : Rat) : Rat :=
  if a ≤ b then b else a

/-- Exact `d = 2` per-tensor coupled average penalty for squared rounding ratios `u_1, u_2 > 0`. -/
def perTensorCoupledD2Penalty (u1 u2 : Rat) : Rat :=
  let mwSq := ratMax u1 u2
  let mxSq := ratMax (1 / u1) (1 / u2)
  (perTensorCoupledChannelPenalty mwSq mxSq u1 +
   perTensorCoupledChannelPenalty mwSq mxSq u2) / 2

/-- Exact rational integer power of two `2^e` for `e : Int`. -/
def pow2IntRat (e : Int) : Rat :=
  match e with
  | Int.ofNat n => ((2 ^ n : Nat) : Rat)
  | Int.negSucc n => 1 / ((2 ^ (n + 1) : Nat) : Rat)

/-! ### 3. `2 × 2` Matrices, Walsh-Hadamard Transform, and `SQ <-> Hadamard` Non-Commutation -/

/-- Exact `2 × 2` rational matrix. -/
structure Mat2 where
  a00 : Rat
  a01 : Rat
  a10 : Rat
  a11 : Rat
deriving DecidableEq

/-- Exact `2 × 2` matrix multiplication. -/
def mat2Mul (A B : Mat2) : Mat2 :=
  { a00 := A.a00 * B.a00 + A.a01 * B.a10
    a01 := A.a00 * B.a01 + A.a01 * B.a11
    a10 := A.a10 * B.a00 + A.a11 * B.a10
    a11 := A.a10 * B.a01 + A.a11 * B.a11 }

/-- Scalar multiplication of a `2 × 2` matrix. -/
def mat2Scale (c : Rat) (A : Mat2) : Mat2 :=
  { a00 := c * A.a00, a01 := c * A.a01, a10 := c * A.a10, a11 := c * A.a11 }

/-- Exact `2 × 2` diagonal matrix `diag(d0, d1)`. -/
def mat2Diag (d0 d1 : Rat) : Mat2 :=
  { a00 := d0, a01 := 0, a10 := 0, a11 := d1 }

/-- Exact `2 × 2` Walsh-Hadamard matrix `H_2` (`H_2^T = H_2`, `H_2^2 = 2 I_2`). -/
def hadamard2 : Mat2 :=
  { a00 := 1, a01 := 1, a10 := 1, a11 := -1 }

/-- Exact Frobenius squared norm `‖A‖_F^2` of a `2 × 2` matrix. -/
def mat2FrobSq (A : Mat2) : Rat :=
  A.a00 * A.a00 + A.a01 * A.a01 + A.a10 * A.a10 + A.a11 * A.a11

/-- Squared max-abs entry norm `(max_{i,j} |A_{ij}|)^2 = max_{i,j} A_{ij}^2` of a `2 × 2` matrix. -/
def mat2MaxSq (A : Mat2) : Rat :=
  ratMax (ratMax (A.a00 * A.a00) (A.a01 * A.a01))
         (ratMax (A.a10 * A.a10) (A.a11 * A.a11))

/-- First-order per-tensor bilinear quantization error proxy for factorized product
    `(1/d) W' X'`: `(1/d^2) (max|W'|^2 / q_W^2 * ‖X'‖_F^2 + max|X'|^2 / q_X^2 * ‖W'‖_F^2)`. -/
def mat2QuantErrProxy (qW qX d : Rat) (W' X' : Mat2) : Rat :=
  (mat2MaxSq W' / (qW * qW) * mat2FrobSq X' +
   mat2MaxSq X' / (qX * qX) * mat2FrobSq W') / (d * d)

/-- Parametric anti-correlated outlier weight matrix `W(M)` with `w_0 = 1/M, w_1 = 1`. -/
def antiOutlierW (M : Rat) : Mat2 :=
  { a00 := 1 / M, a01 := 1, a10 := 1 / M, a11 := -1 }

/-- Parametric anti-correlated outlier activation matrix `X(M)` with `x_0 = M, x_1 = 1`. -/
def antiOutlierX (M : Rat) : Mat2 :=
  { a00 := M, a01 := M, a10 := 1, a11 := -1 }

end SmoothquantDyadic
