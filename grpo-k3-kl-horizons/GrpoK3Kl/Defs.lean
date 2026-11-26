/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Shared Definitions for GRPO / RLHF Schulman `k3` KL & Advantage Stability Laws

Pure `Init` (zero Mathlib) exact rational and IEEE-754 RNE definitions for:
1. Exact Schulman `k3` KL estimator Taylor/Padé envelopes and stabilized polynomial.
2. Exact IEEE-754 Round-to-Nearest-Even (RNE) predicates and bit-exact `BF16` / `FP16`
   decoders for Order A `(fl(exp d) - d) - 1` and Order B `(fl(exp d) - 1) - d`.
3. Binade-ULP discretization `ulp(k, m) = 2^{k - m}`, PPO/GRPO clip window `[4/5, 6/5]`,
   and direct logit-difference `log p_new - log p_old = (z_new - z_old) - (LSE_new - LSE_old)`.
4. Exact binary-reward GRPO group mean, variance, normalized advantage squared magnitudes,
   `Dr.GRPO` mean-only advantages, BF16 one-pass variance, and `FP8-E4M3` mean-saturation stall.
-/

namespace GrpoK3Kl

/-- Exact power of two as a rational number: `2^k : Rat`. -/
def pow2Rat (k : Nat) : Rat := ((2 ^ k : Nat) : Rat)

/-- Exact reciprocal power of two as a rational number: `2^{-k} : Rat`. -/
def invPow2Rat (k : Nat) : Rat := (1 : Rat) / pow2Rat k

/-- Exact absolute value on `Rat`. -/
def ratAbs (x : Rat) : Rat := if (0 : Rat) ≤ x then x else -x

/-- Exact binade ULP spacing `ulp(k, m) = 2^k / 2^m` on `[2^k, 2^{k+1})` for an `m`-bit mantissa. -/
def binadeUlp (k m : Nat) : Rat := pow2Rat k * invPow2Rat m

/-- Recursive finite sum over `Fin k → Rat`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f =>
    finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{j : Fin n} f j` over `Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat := finSumAux n f

/-! ## Schulman `k3` KL Estimator Taylor & Padé Envelopes -/

/-- Exact degree-3 Taylor partial sum of `exp(d)`: `1 + d + d^2/2 + d^3/6`. -/
def expTaylor3 (d : Rat) : Rat :=
  1 + d + d * d / 2 + d * d * d / 6

/-- Exact degree-4 Taylor partial sum of `exp(d)`: `1 + d + d^2/2 + d^3/6 + d^4/24`. -/
def expTaylor4 (d : Rat) : Rat :=
  expTaylor3 d + d * d * d * d / 24

/-- Exact quadratic-cubic lower envelope for `k3(d) = exp(d) - 1 - d`: `(d^2/2)(1 + d/3)`. -/
def k3QuadLower (d : Rat) : Rat :=
  (d * d / 2) * (1 + d / 3)

/-- Stabilized degree-4 Taylor estimator for `k3(d)`: `(d^2/2)(1 + d/3 + d^2/12)`. -/
def k3Stab (d : Rat) : Rat :=
  (d * d / 2) * (1 + d / 3 + d * d / 12)

/-- Exact quadratic-quartic upper envelope on `[0, 1]`: `(d^2/2)(1 + d/3 + d^2/6)`. -/
def k3QuadUpper (d : Rat) : Rat :=
  (d * d / 2) * (1 + d / 3 + d * d / 6)

/-- Numerator of the `[2/2]` Padé approximant of `exp(d)`: `1 + d/2 + d^2/12`. -/
def pade22Num (d : Rat) : Rat :=
  1 + d / 2 + d * d / 12

/-- Denominator of the `[2/2]` Padé approximant of `exp(d)`: `1 - d/2 + d^2/12`. -/
def pade22Den (d : Rat) : Rat :=
  1 - d / 2 + d * d / 12

/-- Exact `[2/2]` Padé approximant of `exp(d)`. -/
def pade22 (d : Rat) : Rat :=
  pade22Num d / pade22Den d

/-! ## Exact IEEE-754 RNE Predicates & Bit-Exact `BF16` / `FP16` Decoders -/

/-- IEEE-754 RNE rounding to `1` from above on `[1, 1 + 2^{-m}]`:
    `1` has even significand `2^m` and `1 + 2^{-m}` has odd significand `2^m + 1`,
    so `fl_m(x) = 1` iff `1 ≤ x` and `x - 1 ≤ (1 + 2^{-m}) - x`. -/
def rneRoundsToOneAbove (m : Nat) (x : Rat) : Prop :=
  1 ≤ x ∧ x - 1 ≤ (1 + invPow2Rat m) - x

/-- IEEE-754 RNE rounding strictly down to `1 - 2^{-(m+1)}` on `[1 - 2^{-(m+1)}, 1]`:
    `1 - 2^{-(m+1)}` has odd significand `2^{m+1} - 1` and `1` has even significand `2^m`,
    so `fl_m(x) = 1 - 2^{-(m+1)}` iff `x` is strictly closer to `1 - 2^{-(m+1)}` than to `1`. -/
def rneRoundsToPredOfOne (m : Nat) (x : Rat) : Prop :=
  1 - invPow2Rat (m + 1) ≤ x ∧ x ≤ 1 ∧ x - (1 - invPow2Rat (m + 1)) < 1 - x

/-- IEEE-754 RNE snapping to `1` from below on `[1 - 2^{-(m+1)}, 1]`:
    `1` has even significand `2^m`, so `fl_m(x) = 1` iff `1 - x ≤ x - (1 - 2^{-(m+1)})`. -/
def rneSnapsToOneBelow (m : Nat) (x : Rat) : Prop :=
  (1 - invPow2Rat (m + 1) ≤ x ∧ x ≤ 1) ∧
  1 - x ≤ x - (1 - invPow2Rat (m + 1))

/-- IEEE-754 RNE rounding (or tie-to-even) to an even-significand lower neighbor `s`
    with binade ULP `u`: `s ≤ x` and `x - s ≤ (s + u) - x`. -/
def rneRoundsToLowerEven (s u x : Rat) : Prop :=
  s ≤ x ∧ x - s ≤ (s + u) - x

/-- IEEE-754 RNE rounding (or tie-to-even) to an even-significand upper neighbor `s + u`
    from an odd-significand lower neighbor `s` with binade ULP `u`. -/
def rneRoundsToUpperEven (s u x : Rat) : Prop :=
  s ≤ x ∧ x ≤ s + u ∧ (s + u) - x ≤ x - s

/-- IEEE-754 RNE rounding strictly to lower neighbor `s` (closer to `s` than to `s + u`,
    independent of significand parity). -/
def rneRoundsStrictlyLower (s u x : Rat) : Prop :=
  s ≤ x ∧ x - s < (s + u) - x

/-- Exact rational decoder for positive normal `BF16` bit patterns (`0x0080 ≤ bits ≤ 0x7f7f`):
    `E = (bits / 128) % 256`, `M = bits % 128`, value `(128 + M) * 2^{E - 134}`. -/
def bf16DecodePosNormal (bits : Nat) : Rat :=
  let E := (bits / 128) % 256
  let M := bits % 128
  if E < 134 then
    ((128 + M : Nat) : Rat) * invPow2Rat (134 - E)
  else
    ((128 + M : Nat) : Rat) * pow2Rat (E - 134)

/-- Exact rational decoder for positive normal `FP16` bit patterns (`0x0400 ≤ bits ≤ 0x7bff`):
    `E = (bits / 1024) % 32`, `M = bits % 1024`, value `(1024 + M) * 2^{E - 25}`. -/
def fp16DecodePosNormal (bits : Nat) : Rat :=
  let E := (bits / 1024) % 32
  let M := bits % 1024
  if E < 25 then
    ((1024 + M : Nat) : Rat) * invPow2Rat (25 - E)
  else
    ((1024 + M : Nat) : Rat) * pow2Rat (E - 25)

/-! ## Log-Prob Cancellation, Clip Window, and Direct Logit-Difference -/

/-- Exact token log-probability `log p(y) = z_y - LSE`. -/
def logProb (z lse : Rat) : Rat := z - lse

/-- Direct logit-difference formula `(z_new - z_old) - (LSE_new - LSE_old)`. -/
def directLogitDiff (zNew zOld lseNew lseOld : Rat) : Rat :=
  (zNew - zOld) - (lseNew - lseOld)

/-- Standard PPO/GRPO unclipped ratio interior `[0.8, 1.2] = [4/5, 6/5]`. -/
def inClipWindow (r : Rat) : Prop :=
  (4 / 5 : Rat) ≤ r ∧ r ≤ (6 / 5 : Rat)

/-! ## GRPO Binary-Reward & Group Advantage Definitions -/

/-- Group mean `μ = k / G` for binary rewards `r ∈ {0, 1}^G` with `k` successes. -/
def binMean (k G : Nat) : Rat :=
  (k : Rat) / (G : Rat)

/-- Group variance `σ^2 = k(G - k) / G^2` for binary rewards with `k` successes out of `G`. -/
def binVar (k G : Nat) : Rat :=
  ((k : Rat) * ((G : Rat) - (k : Rat))) / ((G : Rat) * (G : Rat))

/-- Exact squared positive advantage `A_+^2 = (1 - μ)^2 / σ^2`. -/
def binAdvPosSq (k G : Nat) : Rat :=
  ((1 : Rat) - binMean k G) * ((1 : Rat) - binMean k G) / binVar k G

/-- Exact squared negative advantage `A_-^2 = (0 - μ)^2 / σ^2`. -/
def binAdvNegSq (k G : Nat) : Rat :=
  (binMean k G * binMean k G) / binVar k G

/-- Exact squared L1 advantage sum `(|A_+| + |A_-|)^2 = A_+^2 + A_-^2 + 2` (since `|A_+ A_-| = 1`). -/
def binL1SumSq (k G : Nat) : Rat :=
  binAdvPosSq k G + binAdvNegSq k G + 2

/-- Mean-only `Dr.GRPO` advantage `A_i^{Dr} = r_i - μ`. -/
def drGrpoAdv (r μ : Rat) : Rat := r - μ

/-- Exact `FP8-E4M3` RNE step `fl_E4M3(acc + 4)` on the trajectory of summing `4.0`:
    on `[0, 64)`, multiples of `4` are exact in `FP8-E4M3`; at `64`, `ulp_E4M3(64) = 8`
    and `64` has even significand `8`, so `64 + 4 = 68` ties-to-even back to `64`. -/
def fp8E4M3AddFour (acc : Rat) : Rat :=
  if acc < 64 then acc + 4 else 64

/-- Sequential `FP8-E4M3` sum of `n` copies of `4.0` starting from `0`. -/
def fp8E4M3SeqSumFour : Nat → Rat
  | 0 => 0
  | n + 1 => fp8E4M3AddFour (fp8E4M3SeqSumFour n)

end GrpoK3Kl
