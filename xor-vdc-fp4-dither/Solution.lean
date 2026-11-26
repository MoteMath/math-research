/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import XorVdcFp4Dither

/-!
# Verified Solutions (`xor-vdc-fp4-dither`)
-/

namespace XorVdcFp4DitherChallenge

open XorVdcFp4Dither

theorem xor_vdc_sr_unbiased_and_covariance_exact (m b : Nat) (hbm : b ≤ m) :
    (∀ (i : Nat) (l r : Rat) (p : Nat), p ≤ 2 ^ m →
      discreteMean (2 ^ m) (fun u0 => srVal l r p (xorVdcLane m b i u0)) =
      l + (r - l) * ((p : Rat) / ((2 ^ m : Nat) : Rat))) ∧
    (∀ (i j : Nat),
      avgDiscreteSrCov m (xorVdcLane m b i) (xorVdcLane m b j) =
      xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j)) :=
  XorVdcFp4Dither.xor_vdc_sr_unbiased_and_covariance_exact m b hbm

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
    (e2m1XorMseRatio 16 = 61 / 96 ∧ e2m1XorMseRatio 32 = 359 / 576) :=
  XorVdcFp4Dither.xor_vdc_walsh_spectrum_and_trace_conservation

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
    (harmonicMean 4 6 = 24 / 5 ∧ maxRelSrVar 4 6 = 1 / 24) :=
  XorVdcFp4Dither.e2m1_harmonic_mean_worst_case_sr_variance

theorem antithetic_pair_sr_variance_halving :
    (∀ p1 p2 : Rat, (0 : Rat) ≤ p1 → p1 ≤ 1 → (0 : Rat) ≤ p2 → p2 ≤ 1 →
      antiCov p1 p2 ≤ 0 ∧ antiPairVar p1 p2 ≤ 1 / 4 ∧ indPairVar p1 p2 ≤ 1 / 2) ∧
    (antiPairVar (1 / 4) (1 / 4) = 1 / 4 ∧ indPairVar (1 / 2) (1 / 2) = 1 / 2) ∧
    (∀ p1 p2 : Rat, p1 + p2 = 1 → antiPairVar p1 p2 = 0) ∧
    antiPairVar (1 / 2) (1 / 2) = 0 :=
  XorVdcFp4Dither.antithetic_pair_sr_variance_halving

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
    (3527 / 1048576 : Rat) * 74 < 1 / 4 :=
  XorVdcFp4Dither.double_quant_gemm_bias_obstruction_and_hammersley

theorem split_32bit_word_xor_vdc_zero_bias_double_gemm :
    (∀ (m b : Nat), b ≤ m →
      (∀ (i j : Nat) (la ra lb rb : Rat) (pa pb : Nat), pa ≤ 2 ^ m → pb ≤ 2 ^ m →
        splitWordXorVdcProdMean m b i j la ra lb rb pa pb =
        (la + (ra - la) * ((pa : Rat) / ((2 ^ m : Nat) : Rat))) *
        (lb + (rb - lb) * ((pb : Rat) / ((2 ^ m : Nat) : Rat)))) ∧
      (∀ (i j : Nat),
        splitWordLowSrAvgCov m b i j = xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j) ∧
        splitWordHighSrAvgCov m b i j = xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j))) ∧
    (splitWordLowSrAvgCov 16 5 0 1 < 0 ∧ splitWordHighSrAvgCov 16 5 0 1 < 0) :=
  XorVdcFp4Dither.split_32bit_word_xor_vdc_zero_bias_double_gemm

end XorVdcFp4DitherChallenge
