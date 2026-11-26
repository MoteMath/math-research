/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AllReduceXorVdc

/-!
# Verified Solutions (`allreduce-topology-xorvdc`)
-/

namespace AllReduceXorVdcChallenge

open AllReduceXorVdc

theorem allreduce_subulp_drift_ring_vs_tree_exact :
    (∀ (p tp : Nat), 1 ≤ p → 2 ≤ tp →
      ringSubUlpErr p tp = ((tp - 1 : Nat) : Rat) * (dyadicUlp p / 2) ∧
      directSubUlpErr p tp ≤ dyadicUlp p / 2) ∧
    (∀ (p k : Nat), 1 ≤ p → 1 ≤ k →
      treeSubUlpErr p k = dyadicUlp p / 2 ∧
      directSubUlpErr p (2 ^ k) = dyadicUlp p / 2 ∧
      ringSubUlpErr p (2 ^ k) = ((2 ^ k - 1 : Nat) : Rat) * treeSubUlpErr p k ∧
      ringSubUlpErr p (2 ^ k) = ((2 ^ k - 1 : Nat) : Rat) * directSubUlpErr p (2 ^ k)) ∧
    (∀ (p : Nat), 1 ≤ p →
      ringSubUlpErr p 64 = 63 * treeSubUlpErr p 6 ∧
      ringSubUlpErr p 64 = 63 * directSubUlpErr p 64) :=
  AllReduceXorVdc.allreduce_subulp_drift_ring_vs_tree_exact

theorem allreduce_cancel_wipeout_ring_vs_tree_exact :
    (∀ (M bound δ : Rat) (tp i j : Nat),
      (0 : Rat) < M → (0 : Rat) < δ → 2 ≤ tp → i < tp → j < tp → i ≠ j →
      ((tp : Rat) * δ) ≤ bound → bound < M →
      (ringCancelOut M bound δ tp i j = 0 ↔ (i = tp - 1 ∨ j = tp - 1)) ∧
      directCancelOut M δ tp i j = ((tp - 2 : Nat) : Rat) * δ) ∧
    (∀ (M bound δ : Rat) (k i j : Nat),
      (0 : Rat) < M → (0 : Rat) < δ → i < 2 ^ (k + 1) → j < 2 ^ (k + 1) → i ≠ j →
      ((2 ^ (k + 1) : Nat) : Rat) * δ ≤ bound → bound < M →
      (treeCancelOut M bound δ (k + 1) i j = 0 ↔
        ((i < 2 ^ k ∧ 2 ^ k ≤ j) ∨ (j < 2 ^ k ∧ 2 ^ k ≤ i)))) ∧
    (∀ (h : Nat), 2 ≤ h →
      ringWipeoutCount (2 * h) = 2 * (2 * h - 1) ∧
      treeWipeoutCount h = 2 * h * h ∧
      directWipeoutCount (2 * h) = 0 ∧
      ringWipeoutProb (2 * h) = 2 / ((2 * h : Nat) : Rat) ∧
      treeWipeoutProb h = ((2 * h : Nat) : Rat) / (2 * ((2 * h - 1 : Nat) : Rat)) ∧
      directWipeoutProb (2 * h) = 0 ∧
      (1 : Rat) / 2 < treeWipeoutProb h ∧
      ringWipeoutProb (2 * h) < treeWipeoutProb h) ∧
    (ringWipeoutProb 64 = 1 / 32 ∧
     treeWipeoutProb 32 = 32 / 63 ∧
     treeWipeoutProb 32 / ringWipeoutProb 64 = 1024 / 63 ∧
     (16 : Rat) < treeWipeoutProb 32 / ringWipeoutProb 64) :=
  AllReduceXorVdc.allreduce_cancel_wipeout_ring_vs_tree_exact

theorem cross_rank_xor_vdc_bijection_and_exact_mse :
    (∀ (M K u0 : Nat), K ≤ M → u0 < 2 ^ M →
      (∀ r : Fin (2 ^ K), topBits M K (xorVdcThreshold M K r.val u0) < 2 ^ K) ∧
      (∀ r₁ r₂ : Fin (2 ^ K),
        topBits M K (xorVdcThreshold M K r₁.val u0) = topBits M K (xorVdcThreshold M K r₂.val u0) →
        r₁ = r₂) ∧
      (∀ y : Fin (2 ^ K), ∃ r : Fin (2 ^ K),
        topBits M K (xorVdcThreshold M K r.val u0) = y.val)) ∧
    (∀ (M K f : Nat), K ≤ M → f < 2 ^ M →
      xorVdcBias M K f = 0 ∧
      (∀ u0, u0 < 2 ^ M →
        absRat (xorVdcRankSum M K f u0 - ((2 ^ K * f : Nat) : Rat) / ((2 ^ M : Nat) : Rat)) < 1)) ∧
    (∀ (M K : Nat), K ≤ M →
      xorVdcDiscreteMse M K =
        ((((2 ^ (M - K) : Nat) : Rat) * ((2 ^ (M - K) : Nat) : Rat)) - 1) /
          (6 * (((2 ^ (M - K) : Nat) : Rat) * ((2 ^ (M - K) : Nat) : Rat))) ∧
      xorVdcDiscreteMse M K < 1 / 6 ∧
      indSrDiscreteMse M K =
        ((2 ^ K : Nat) : Rat) *
          ((((2 ^ M : Nat) : Rat) * ((2 ^ M : Nat) : Rat) - 1) /
            (6 * (((2 ^ M : Nat) : Rat) * ((2 ^ M : Nat) : Rat))))) ∧
    (∀ (tp : Nat), 1 ≤ tp →
      mseIndSr tp / mseXorVdc = (tp : Rat) ∧
      mseRne tp / mseXorVdc = ((tp : Rat) * (tp : Rat)) / 2 ∧
      mseAntithetic tp / mseXorVdc = (tp : Rat) / 2) ∧
    (mseIndSr 64 / mseXorVdc = 64 ∧
     mseRne 64 / mseXorVdc = 2048 ∧
     mseAntithetic 64 / mseXorVdc = 32) :=
  AllReduceXorVdc.cross_rank_xor_vdc_bijection_and_exact_mse

theorem bf16_residual_stream_freeze_depth_exact :
    (∀ (p L : Nat), p ≤ 7 →
      (2 ^ (16 - 2 * p) < 2 * L ↔ bf16FreezeDepth p < L) ∧
      (2 ^ (16 - 2 * p) = 2 * L ↔ L = bf16FreezeDepth p)) ∧
    (bf16FreezeDepth 5 = 32 ∧ bf16FreezeDepth 4 = 128 ∧ bf16FreezeDepth 3 = 512) ∧
    (∀ (m : Int) (δ : Rat) (L : Nat), (0 : Rat) ≤ δ → δ < bf16HalfUlp →
      bf16ResidualAccum ((m : Rat) * bf16Ulp) δ L = (m : Rat) * bf16Ulp ∧
      absRat (bf16ResidualAccum ((m : Rat) * bf16Ulp) δ L -
        ((m : Rat) * bf16Ulp + (L : Rat) * δ)) = (L : Rat) * δ) ∧
    (∀ (m : Int) (L : Nat), m % 2 = 0 →
      bf16ResidualAccum ((m : Rat) * bf16Ulp) bf16HalfUlp L = (m : Rat) * bf16Ulp) ∧
    (∀ (m : Int) (L : Nat), m % 2 ≠ 0 → 1 ≤ L →
      bf16ResidualAccum ((m : Rat) * bf16Ulp) bf16HalfUlp L = ((m + 1 : Int) : Rat) * bf16Ulp) :=
  AllReduceXorVdc.bf16_residual_stream_freeze_depth_exact

theorem kahan_compensated_residual_exact_recovery :
    (∀ (u s0 : Rat) (xs : List Rat), (0 : Rat) < u →
      let res := kahanAccum u s0 xs
      res.1 + res.2 = s0 + sumListRat xs ∧
      absRat res.2 ≤ u / 2 ∧
      absRat (res.1 - (s0 + sumListRat xs)) ≤ u / 2) ∧
    (∀ (m : Int) (δ : Rat) (L : Nat),
      let res := kahanAccum bf16Ulp ((m : Rat) * bf16Ulp) (List.replicate L δ)
      res.1 + res.2 = (m : Rat) * bf16Ulp + (L : Rat) * δ ∧
      absRat (res.1 - ((m : Rat) * bf16Ulp + (L : Rat) * δ)) ≤ bf16HalfUlp) :=
  AllReduceXorVdc.kahan_compensated_residual_exact_recovery

theorem fixed_scale_ternary_saturation_barrier :
    (∀ (S : Rat) (k : Nat), (0 : Rat) < S → 1 ≤ k →
      let exactS := sumRange (2 ^ k) (ternaryDriftInput S)
      let rOut := ringReduceFn (ternaryAdd S) (2 ^ k) (ternaryDriftInput S)
      let tOut := treeReduce (ternaryAdd S) k (ternaryDriftInput S)
      let dOut := directReduce (ternaryQuant S) (2 ^ k) (ternaryDriftInput S)
      rOut = S ∧ tOut = S ∧ dOut = S ∧
      absRat (rOut - exactS) = ((2 ^ k - 1 : Nat) : Rat) * (S / 2) ∧
      absRat (tOut - exactS) = ((2 ^ k - 1 : Nat) : Rat) * (S / 2) ∧
      absRat (dOut - exactS) = ((2 ^ k - 1 : Nat) : Rat) * (S / 2) ∧
      absRat (rOut - exactS) / absRat (tOut - exactS) = 1 ∧
      absRat (rOut - exactS) / absRat (dOut - exactS) = 1) ∧
    (∀ (S x : Rat), (0 : Rat) < S → S < absRat x →
      absRat x - S ≤ absRat (ternaryQuant S x - x) ∧ (0 : Rat) < absRat x - S) :=
  AllReduceXorVdc.fixed_scale_ternary_saturation_barrier

end AllReduceXorVdcChallenge
