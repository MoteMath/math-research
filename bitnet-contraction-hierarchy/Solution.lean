/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitnetContraction

/-!
# Verified Solutions (`bitnet-contraction-hierarchy`)
-/

namespace BitnetContractionChallenge

open BitnetContraction

theorem ternary_nearest_nonneg_contraction (d : Nat) (γ : Rat) (hγ : 0 ≤ γ) (x : Fin d → Rat) :
    ternErrSq γ x ≤ normSq x ∧ ternErrSqStrict γ x ≤ normSq x :=
  BitnetContraction.ternary_nearest_nonneg_contraction d γ hγ x

theorem bitnet_absmean_contraction_exact (d : Nat) (hd : 1 ≤ d) :
    (∀ x : Fin d → Rat, 0 < normSq x →
      let γ := l1Norm x / (d : Rat)
      ternErrSq γ x ≤ (1 - (2 * (d : Rat) - 1) / ((d : Rat) * (d : Rat))) * normSq x) ∧
    (0 < normSq (unitE0 d) ∧
      let γ := l1Norm (unitE0 d) / (d : Rat)
      ternErrSq γ (unitE0 d) =
        (1 - (2 * (d : Rat) - 1) / ((d : Rat) * (d : Rat))) * normSq (unitE0 d)) :=
  BitnetContraction.bitnet_absmean_contraction_exact d hd

theorem bitnet_absmax_and_half_contraction_exact (d : Nat) (hd : 1 ≤ d) :
    (∀ (M : Rat), 0 < M → ∀ (x : Fin d → Rat),
      (∀ i, (x i).abs ≤ M) → (∃ i, (x i).abs = M) →
      ternErrSq M x ≤ (1 - 4 / ((d : Rat) + 3)) * normSq x) ∧
    ((∀ i, (absMaxWitness d i).abs ≤ 1) ∧ (∃ i, (absMaxWitness d i).abs = 1) ∧
      ternErrSq 1 (absMaxWitness d) = (1 - 4 / ((d : Rat) + 3)) * normSq (absMaxWitness d)) ∧
    (∀ (M : Rat), 0 < M → ∀ (x : Fin d → Rat),
      (∀ i, (x i).abs ≤ M) → (∃ i, (x i).abs = M) →
      ternErrSq (M / 2) x ≤ (1 - 12 / ((d : Rat) + 15)) * normSq x) ∧
    ((∀ i, (absMaxHalfWitness d i).abs ≤ 1) ∧ (∃ i, (absMaxHalfWitness d i).abs = 1) ∧
      ternErrSq ((1 : Rat) / 2) (absMaxHalfWitness d) =
        (1 - 12 / ((d : Rat) + 15)) * normSq (absMaxHalfWitness d)) :=
  BitnetContraction.bitnet_absmax_and_half_contraction_exact d hd

theorem bitnet_rms_contraction_exact_algebraic (d : Nat) (hd : 1 ≤ d) :
    (∀ (x : Fin d → Rat) (γ : Rat), 0 < γ → (d : Rat) * (γ * γ) = normSq x →
      let α := ternAlpha γ x
      3 * (d : Rat) + 1 ≤ ((d : Rat) * α + 1) * ((d : Rat) * α + 1)) ∧
    ((8 : Rat) * ((1 : Rat) * 1) = normSq (rmsWitness 8 5) ∧
      ternAlpha 1 (rmsWitness 8 5) = (1 : Rat) / 2) ∧
    ((16 : Rat) * ((1 : Rat) * 1) = normSq (rmsWitness 16 7) ∧
      ternAlpha 1 (rmsWitness 16 7) = (3 : Rat) / 8) :=
  BitnetContraction.bitnet_rms_contraction_exact_algebraic d hd

theorem multilevel_shifted_sqrt_dcrit_exact (M : Nat) (hM : 2 ≤ M) :
    ((4 * M * M + 1) * (4 * M * M + 1) < 16 * M * M * (M * M + 1) ∧
     16 * M * M * (M * M + 1) < (4 * M * M + 2) * (4 * M * M + 2)) ∧
    (∀ d : Nat,
      (4 * M * M + 2 < d ∧
        16 * M * M * (M * M + 1) < (d - (4 * M * M + 2)) * (d - (4 * M * M + 2))) ↔
      dCrit M ≤ d) ∧
    (dCrit 2 = 36 ∧ dCrit 3 = 76 ∧ dCrit 7 = 396) ∧
    (harmonicConst [1] = 1 ∧
     harmonicConst [1, 2] = (4 : Rat) / 3 ∧
     harmonicConst [1, 3] = (3 : Rat) / 2 ∧
     harmonicConst [1, 2, 3] = (23 : Rat) / 15 ∧
     harmonicConst [1, 2, 3, 4, 5, 6, 7] = (88069 : Rat) / 45045) :=
  BitnetContraction.multilevel_shifted_sqrt_dcrit_exact M hM

theorem two_stage_ternary_greedy_vs_disjoint_crossover :
    (jointDisjointTwoStageAlpha witnessD3Disjoint = (46898841 : Rat) / 49188010 ∧
     greedyTwoStageAlpha witnessD3Disjoint = (49056967 : Rat) / 49188010 ∧
     jointDisjointTwoStageAlpha witnessD3Disjoint < greedyTwoStageAlpha witnessD3Disjoint ∧
     greedyTwoStageAlpha witnessD3Greedy = (20774823 : Rat) / 21352229 ∧
     jointDisjointTwoStageAlpha witnessD3Disjoint < greedyTwoStageAlpha witnessD3Greedy) ∧
    (greedyTwoStageAlpha witnessD4Greedy = (83898881 : Rat) / 89674484 ∧
     jointDisjointTwoStageAlpha witnessD4Greedy = (67117057 : Rat) / 67255863 ∧
     greedyTwoStageAlpha witnessD4Greedy < jointDisjointTwoStageAlpha witnessD4Greedy ∧
     jointDisjointTwoStageAlpha witnessD4Disjoint = (22370441 : Rat) / 23894386 ∧
     greedyTwoStageAlpha witnessD4Greedy < jointDisjointTwoStageAlpha witnessD4Disjoint) :=
  BitnetContraction.two_stage_ternary_greedy_vs_disjoint_crossover

end BitnetContractionChallenge
