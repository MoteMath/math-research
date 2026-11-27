/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import XorVdcFp4Dither.Defs

/-!
# Trusted Challenge Statements (`xor-vdc-fp4-dither`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Exact discrete unbiasedness and closed-form pairwise covariance for 1-PRNG zero-carry XOR-VDC SR.
2. Exact Walsh–Hadamard spectral diagonalization, `popcount ≥ 2` variance halving, universal trace
   conservation, exact `14/16` (`B = 16`) & `29/32` (`B = 32`) mode counts, and the values `61/96` &
   `359/576` of the function `e2m1XorMseRatio` (defined in `Defs.lean`, not derived from the spectrum).
3. Universal harmonic-mean worst-case relative SR variance law `(r - l)^2 / (4 l r)` and exact
   bounds on all 6 positive OCP E2M1 intervals (`1/8`, `1/24`, `1/48`).
4. Universal antithetic paired SR variance halving (`≤ 1/4` vs independent `1/2`) and exact zero
   variance at every midpoint.
5. Double-quantized GEMM `max |bias| = 1/4` obstruction for `same`, `antithetic`, and `msb_1bit_xor`
   couplings vs 0-extra-bit `bitrev_10` Hammersley (`max |bias| = 3527 / 1048576`, `> 74x` lower).
6. Exact zero-bias 32-bit split-word XOR-VDC double GEMM with preserved negative intra-block
   cross-lane covariance (`64x` PRNG reduction at `B = 32`).
-/

namespace XorVdcFp4DitherChallenge

open XorVdcFp4Dither

/-- Theorem 1 (Zero-Carry XOR-VDC Unbiasedness and Exact Closed-Form Pairwise Covariance):
    For all `b ≤ m`, zero-carry XOR-VDC (`u_i = u_0 ^^^ (bitrev_b(i) << (m - b))`) is strictly
    unbiased on every coordinate `i`, and its exact discrete average pairwise covariance over
    uniform `m`-bit `u_0` and `p1, p2` equals `xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j)`. -/
theorem xor_vdc_sr_unbiased_and_covariance_exact (m b : Nat) (hbm : b ≤ m) :
    (∀ (i : Nat) (l r : Rat) (p : Nat), p ≤ 2 ^ m →
      discreteMean (2 ^ m) (fun u0 => srVal l r p (xorVdcLane m b i u0)) =
      l + (r - l) * ((p : Rat) / ((2 ^ m : Nat) : Rat))) ∧
    (∀ (i j : Nat),
      avgDiscreteSrCov m (xorVdcLane m b i) (xorVdcLane m b j) =
      xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j)) := by
  sorry

/-- Theorem 2 (Exact Walsh–Hadamard Spectrum, Trace Conservation, and OCP E2M1 Ratios):
    For all `b`, `xorCovMatrix b` and `xorVdcCovMatrix b` are exactly diagonalized by the
    Walsh–Hadamard basis, every `popcount ≥ 2` mode achieves exact eigenvalue `1/12 < 1/6`,
    universal trace conservation `∑_k λ_k = B * (1/6)` holds, exact mode counts beating
    independent SR are `14/16` (`B = 16`) and `29/32` (`B = 32`), and the function
    `e2m1XorMseRatio` (defined in `Defs.lean`, not derived from the spectrum) takes the values
    `61/96` (`B = 16`) and `359/576` (`B = 32`). -/
theorem xor_vdc_walsh_spectrum_and_trace_conservation :
    (∀ (b k i : Nat), k < 2 ^ b → i < 2 ^ b →
      matVec (2 ^ b) (xorCovMatrix b) (walshSign b k) i = xorWalshEig b k * walshSign b k i ∧
      matVec (2 ^ b) (xorVdcCovMatrix b) (walshSign b k) i = xorVdcWalshEig b k * walshSign b k i) ∧
    (∀ (b k : Nat), 2 ≤ popcountBits b k →
      xorWalshEig b k = 1 / 12 ∧ xorVdcWalshEig b k = 1 / 12 ∧ (1 / 12 : Rat) < 1 / 6) ∧
    (∀ (b : Nat),
      sumRange (2 ^ b) (fun k => xorWalshEig b k) = ((2 ^ b : Nat) : Rat) * (1 / 6) ∧
      sumRange (2 ^ b) (fun k => xorVdcWalshEig b k) = ((2 ^ b : Nat) : Rat) * (1 / 6)) ∧
    (countRange 16 (fun k => decide (xorVdcWalshEig 4 k < 1 / 6)) = 14 ∧
     countRange 32 (fun k => decide (xorVdcWalshEig 5 k < 1 / 6)) = 29) ∧
    (e2m1XorMseRatio 16 = 61 / 96 ∧ e2m1XorMseRatio 32 = 359 / 576) := by
  sorry

/-- Theorem 3 (OCP E2M1 Harmonic-Mean Worst-Case Relative SR Variance):
    For all `0 < l < r`, `(x - l)(r - x) / x^2 ≤ (r - l)^2 / (4 l r)` on `[l, r]` with exact
    attainment at the harmonic mean `x* = 2 l r / (l + r) ∈ [l, r]`, giving exact maxima
    `1/8` on `[1/2, 1]`, `1/24` on `[1, 3/2], [2, 3], [4, 6]`, and `1/48` on `[3/2, 2], [3, 4]`. -/
theorem e2m1_harmonic_mean_worst_case_sr_variance :
    (∀ (l r : Rat), (0 : Rat) < l → l < r →
      (l ≤ harmonicMean l r ∧ harmonicMean l r ≤ r) ∧
      (∀ x : Rat, l ≤ x → x ≤ r → relSrVar l r x ≤ maxRelSrVar l r) ∧
      relSrVar l r (harmonicMean l r) = maxRelSrVar l r) ∧
    (harmonicMean (1 / 2) 1 = 2 / 3 ∧ maxRelSrVar (1 / 2) 1 = 1 / 8) ∧
    (harmonicMean 1 (3 / 2) = 6 / 5 ∧ maxRelSrVar 1 (3 / 2) = 1 / 24) ∧
    (harmonicMean (3 / 2) 2 = 12 / 7 ∧ maxRelSrVar (3 / 2) 2 = 1 / 48) ∧
    (harmonicMean 2 3 = 12 / 5 ∧ maxRelSrVar 2 3 = 1 / 24) ∧
    (harmonicMean 3 4 = 24 / 7 ∧ maxRelSrVar 3 4 = 1 / 48) ∧
    (harmonicMean 4 6 = 24 / 5 ∧ maxRelSrVar 4 6 = 1 / 24) := by
  sorry

/-- Theorem 4 (Universal Antithetic Paired SR Variance Halving and Midpoint Cancellation):
    Antithetic pairing `(u, 1 - u)` has universally non-positive covariance on `[0, 1]^2`,
    strictly halves worst-case pair variance (`≤ 1/4` attained at `(1/4, 1/4)` vs independent
    `1/2` attained at `(1/2, 1/2)`), and achieves exact zero variance (`0`) on every complementary
    pair `p1 + p2 = 1` (including every midpoint `p1 = p2 = 1/2`). -/
theorem antithetic_pair_sr_variance_halving :
    (∀ p1 p2 : Rat, (0 : Rat) ≤ p1 → p1 ≤ 1 → (0 : Rat) ≤ p2 → p2 ≤ 1 →
      antiCov p1 p2 ≤ 0 ∧ antiPairVar p1 p2 ≤ 1 / 4 ∧ indPairVar p1 p2 ≤ 1 / 2) ∧
    (antiPairVar (1 / 4) (1 / 4) = 1 / 4 ∧ indPairVar (1 / 2) (1 / 2) = 1 / 2) ∧
    (∀ p1 p2 : Rat, p1 + p2 = 1 → antiPairVar p1 p2 = 0) ∧
    antiPairVar (1 / 2) (1 / 2) = 0 := by
  sorry

/-- Theorem 5 (Double-Quantized GEMM Bias Obstruction and `bitrev_10` Hammersley Bound):
    For all `k ≥ 1`, `samePerm`, `antiPerm k`, and `msbXorPerm k` all suffer exact worst-case
    `max |bias| = 1/4` (attained at `A = B = 2^(k-1)`), whereas 0-extra-bit `bitrev_10` Hammersley
    coupling (`k = 10`, `M = 1024`) cuts `max |bias|` by `> 74x` to exact `3527 / 1048576`
    (attained at `A = B = 341`). -/
theorem double_quant_gemm_bias_obstruction_and_hammersley :
    (∀ k, 1 ≤ k →
      (∀ A B, A ≤ 2 ^ k → B ≤ 2 ^ k → absRat (doubleQuantBias k samePerm A B) ≤ 1 / 4) ∧
      absRat (doubleQuantBias k samePerm (2 ^ (k - 1)) (2 ^ (k - 1))) = 1 / 4) ∧
    (∀ k, 1 ≤ k →
      (∀ A B, A ≤ 2 ^ k → B ≤ 2 ^ k → absRat (doubleQuantBias k (antiPerm k) A B) ≤ 1 / 4) ∧
      absRat (doubleQuantBias k (antiPerm k) (2 ^ (k - 1)) (2 ^ (k - 1))) = 1 / 4) ∧
    (∀ k, 1 ≤ k →
      (∀ A B, A ≤ 2 ^ k → B ≤ 2 ^ k → absRat (doubleQuantBias k (msbXorPerm k) A B) ≤ 1 / 4) ∧
      absRat (doubleQuantBias k (msbXorPerm k) (2 ^ (k - 1)) (2 ^ (k - 1))) = 1 / 4) ∧
    (∀ A B, A ≤ 1024 → B ≤ 1024 →
      absRat (doubleQuantBias 10 (hammersleyPerm 10) A B) ≤ 3527 / 1048576) ∧
    absRat (doubleQuantBias 10 (hammersleyPerm 10) 341 341) = 3527 / 1048576 ∧
    (3527 / 1048576 : Rat) * 74 < 1 / 4 := by
  sorry

/-- Theorem 6 (Split 32-Bit Word XOR-VDC Zero-Bias Double GEMM):
    Splitting a single `2m`-bit uniform word into independent `m`-bit halves `(w % 2^m, w / 2^m)`
    combined with XOR-VDC guarantees exact zero bias `E[Q(a; u0_a ^ d_i) Q(b; u0_b ^ d_j)] = a * b`
    for all `b ≤ m` and strictly preserves the exact intra-block XOR-VDC pairwise covariance on
    both halves (including strictly negative adjacent-lane covariance for 32-bit MXFP4 `m = 16, b = 5`). -/
theorem split_32bit_word_xor_vdc_zero_bias_double_gemm :
    (∀ (m b : Nat), b ≤ m →
      (∀ (i j : Nat) (la ra lb rb : Rat) (pa pb : Nat), pa ≤ 2 ^ m → pb ≤ 2 ^ m →
        splitWordXorVdcProdMean m b i j la ra lb rb pa pb =
        (la + (ra - la) * ((pa : Rat) / ((2 ^ m : Nat) : Rat))) *
        (lb + (rb - lb) * ((pb : Rat) / ((2 ^ m : Nat) : Rat)))) ∧
      (∀ (i j : Nat),
        splitWordLowSrAvgCov m b i j = xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j) ∧
        splitWordHighSrAvgCov m b i j = xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j))) ∧
    (splitWordLowSrAvgCov 16 5 0 1 < 0 ∧ splitWordHighSrAvgCov 16 5 0 1 < 0) := by
  sorry

end XorVdcFp4DitherChallenge
