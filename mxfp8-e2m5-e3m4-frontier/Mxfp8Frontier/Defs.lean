/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`mxfp8-e2m5-e3m4-frontier`)

Pure-`Init` (zero Mathlib) exact rational and natural-number definitions for:
1. 8-bit IEEE/FN floating-point magnitude grids `E_a M_b` (`a + b = 7`) in integer units
   of the smallest positive subnormal `u_min = 1`, and normalized rational grids in `[0, 1]`.
2. Universal all-`B` EF21 contraction functions `alpha(B) = 1 - delta(B)` for the five
   distinct 8-bit microscaling formats (`INT8`, `E2M5_FN`, `E3M4_FN`, `E4M3_OCP`, `E5M2_IEEE`)
   under both OCP `E8M0` power-of-2 scaling and continuous `DeepSeek-V3 FP32` max-abs scaling,
   plus the exact candidate contraction function `ef21AlphaCand ay ae my me B`.
3. Delayed-scaling spike-clipping relative MSE `delayedClipDelta`, wide-format normal relative
   MSE `wideNormalDelta`, and exact rational spike-factor crossover `spikeCrossover M m`.
4. Block-scaled vector quantization squared error `sqErrList`, relative error, and delayed-scaling
   headroom margin underflow capacity `underflowCap`.
-/

namespace Mxfp8Frontier

/-! ### 0. Exact Dyadic Powers of Two -/

/-- Exact rational power of two `2^k`. -/
def pow2Rat (k : Nat) : Rat := ((2 ^ k : Nat) : Rat)

/-- Exact rational inverse power of two `2^{-k}`. -/
def invPow2Rat (k : Nat) : Rat := 1 / pow2Rat k

/-! ### 1. Exact 7-Bit Magnitude Grid Decoding for `E_a M_b` (`a + b = 7`) -/

/-- Exact nonnegative magnitude of 7-bit unsigned code `c` in an `(e_bits, m_bits)`
    IEEE-subnormal floating-point format, measured in integer units of `u_min = 1`.
    For `e_bits = 0` (`INT8` / `E0M7`), code `c` decodes to `c`.
    For `e_bits ≥ 1`, `e = c / 2^m_bits` and `m = c % 2^m_bits`:
    subnormals (`e = 0`) decode to `m`, normals (`e ≥ 1`) decode to `(2^m_bits + m) * 2^(e - 1)`. -/
def fp8MagInt (e_bits m_bits c : Nat) : Nat :=
  if e_bits = 0 then c
  else
    let e := c / 2 ^ m_bits
    let m := c % 2 ^ m_bits
    if e = 0 then m else (2 ^ m_bits + m) * 2 ^ (e - 1)

/-- Normalized rational grid point `fp8MagInt e_bits m_bits c / M_max` in `[0, 1]`. -/
def fp8NormRat (e_bits m_bits M_max c : Nat) : Rat :=
  (fp8MagInt e_bits m_bits c : Rat) / (M_max : Rat)

/-! ### 2. Exact Candidate & Universal All-`B` EF21 Contraction Functions -/

/-- Exact EF21 contraction constant `1 - delta(B)` for an anchor coordinate `(ay, ae)`
    and `B - 1` copies of a midpoint coordinate `(my, me)` (all in half-units of `u_min`):
    `1 - (ae^2 + (B - 1) * me^2) / (ay^2 + (B - 1) * my^2)`. -/
def ef21AlphaCand (ay ae my me B : Nat) : Rat :=
  1 - (((ae * ae + (B - 1) * (me * me) : Nat) : Rat) /
       ((ay * ay + (B - 1) * (my * my) : Nat) : Rat))

/-- Exact linear-fractional rational function `(n1 * B + n0) / (d1 * B + d0)`. -/
def linFrac (n1 n0 d1 d0 B : Nat) : Rat :=
  ((n1 * B + n0 : Nat) : Rat) / ((d1 * B + d0 : Nat) : Rat)

/-- Exact all-`B` EF21 contraction constant for `E0M7` (`INT8`) ≡ `E1M6_FN` under `E8M0` scaling. -/
def alphaE8M0_INT8 (B : Nat) : Rat :=
  linFrac 0 16128 1 16128 B

/-- Exact all-`B` EF21 contraction constant for `E2M5_FN` under `E8M0` scaling (3 exact regimes). -/
def alphaE8M0_E2M5 (B : Nat) : Rat :=
  if B ≤ 249 then
    linFrac 0 67584 1 67599 B
  else if B ≤ 253 then
    linFrac 0 64512 1 64515 B
  else
    linFrac 0 63504 1 63503 B

/-- Exact all-`B` EF21 contraction constant for `E3M4_FN` under `E8M0` scaling (3 exact regimes). -/
def alphaE8M0_E3M4 (B : Nat) : Rat :=
  if B ≤ 30721 then
    linFrac 0 4456448 1 4460543 B
  else if B ≤ 31745 then
    linFrac 0 4063232 1 4064255 B
  else
    linFrac 0 3936256 1 3936255 B

/-- Exact all-`B` EF21 contraction constant for `E4M3_OCP` under `E8M0` scaling (3 exact regimes). -/
def alphaE8M0_E4M3 (B : Nat) : Rat :=
  if B ≤ 474924269 then
    linFrac 0 77309411328 1 77577846783 B
  else if B ≤ 939524097 then
    linFrac 0 56371445760 1 56438554623 B
  else
    linFrac 0 52613349376 1 52613349375 B

/-- Exact all-`B` EF21 contraction constant for `E5M2_IEEE` under `E8M0` scaling (3 exact regimes). -/
def alphaE8M0_E5M2 (B : Nat) : Rat :=
  if B ≤ 432345564227567617 then
    linFrac 0 23058430092136939520 1 23346660468288651263 B
  else if B ≤ 504403158265495553 then
    linFrac 0 16140901064495857664 1 16212958658533785599 B
  else
    linFrac 0 14123288431433875456 1 14123288431433875455 B

/-- Exact all-`B` EF21 contraction constant for `E0M7` (`INT8`) ≡ `E1M6_FN` under continuous FP32 scaling. -/
def alphaCont_INT8 (B : Nat) : Rat :=
  linFrac 0 64516 1 64515 B

/-- Exact all-`B` EF21 contraction constant for `E2M5_FN` under continuous FP32 scaling (2 exact regimes). -/
def alphaCont_E2M5 (B : Nat) : Rat :=
  if B ≤ 57 then
    linFrac 4224 11652 4225 11651 B
  else
    linFrac 0 254016 1 254015 B

/-- Exact all-`B` EF21 contraction constant for `E3M4_FN` under continuous FP32 scaling (2 exact regimes). -/
def alphaCont_E3M4 (B : Nat) : Rat :=
  if B ≤ 14468 then
    linFrac 1088 2756 1089 2755 B
  else
    linFrac 0 15745024 1 15745023 B

/-- Exact all-`B` EF21 contraction constant for `E4M3_OCP` under continuous FP32 scaling (2 exact regimes). -/
def alphaCont_E4M3 (B : Nat) : Rat :=
  if B ≤ 730740961 then
    linFrac 288 496 289 495 B
  else
    linFrac 0 210453397504 1 210453397503 B

/-- Exact all-`B` EF21 contraction constant for `E5M2_IEEE` under continuous FP32 scaling (2 exact regimes). -/
def alphaCont_E5M2 (B : Nat) : Rat :=
  if B ≤ 706164421571693771 then
    linFrac 80 116 81 115 B
  else
    linFrac 0 56493153725735501824 1 56493153725735501823 B

/-! ### 3. Delayed-Scaling Spike-Clipping Crossover -/

/-- Exact relative squared clipping error `(1 - 2^M / ρ)^2` when a coordinate spikes
    by factor `ρ > 2^M` above the delayed-scaling headroom margin `M` bits. -/
def delayedClipDelta (ρ : Rat) (M : Nat) : Rat :=
  (1 - pow2Rat M / ρ) * (1 - pow2Rat M / ρ)

/-- Exact worst-case normal relative squared error `1 / (2^{m+1} + 1)^2` for an unclipped
    floating-point format with `m` mantissa bits (e.g. `1/81` for `E5M2`, `m = 2`). -/
def wideNormalDelta (m : Nat) : Rat :=
  1 / (((2 ^ (m + 1) + 1 : Nat) : Rat) * ((2 ^ (m + 1) + 1 : Nat) : Rat))

/-- Exact spike-factor crossover `ρ*(M, m) = ((2^{m+1} + 1) / 2^{m+1}) * 2^M` where
    delayed-scaling clipping error equals wide-format normal quantization error. -/
def spikeCrossover (M m : Nat) : Rat :=
  (((2 ^ (m + 1) + 1 : Nat) : Rat) / pow2Rat (m + 1)) * pow2Rat M

/-! ### 4. Block-Scaled Exponent-Bias Invariance & Delayed-Scaling Margin Tax -/

/-- Exact squared quantization error `∑ (s * q_i - x_i)^2` for a block with shared scale `s`,
    input coordinates `xs`, and quantized grid coordinates `qs`. -/
def sqErrList (s : Rat) : List Rat → List Rat → Rat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, q :: qs => (s * q - x) * (s * q - x) + sqErrList s xs qs

/-- Exact squared Euclidean norm `∑ x_i^2` of a coordinate list `xs`. -/
def normSqList : List Rat → Rat
  | [] => 0
  | x :: xs => x * x + normSqList xs

/-- Effective delayed-scaling anchor magnitude `Y / 2^M` under headroom margin `M` bits. -/
def effAnchor (Y : Rat) (M : Nat) : Rat :=
  Y / pow2Rat M

/-- Delayed-scaling underflow capacity `(Y / 2^M)^2` under headroom margin `M` bits. -/
def underflowCap (Y : Rat) (M : Nat) : Rat :=
  effAnchor Y M * effAnchor Y M

end Mxfp8Frontier
