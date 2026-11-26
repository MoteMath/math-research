/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KroneckerCyclicFrustration

/-!
# Verified Solutions (`kronecker-cyclic-frustration`)
-/

namespace KroneckerCyclicFrustrationChallenge

open KroneckerCyclicFrustration

theorem sum_of_two_kronecker_optimal_cond_exact :
    (∀ {n m : Nat} (α : Fin n → Rat) (β : Fin m → Rat),
      (∀ i, (0 : Rat) < α i) → (∀ j, (0 : Rat) < β j) →
      ∀ (i_max i_min : Fin n) (j_max j_min : Fin m)
        (ℓ : Fin n → Rat) (r : Fin m → Rat),
      (∀ i, (0 : Rat) < ℓ i) → (∀ j, (0 : Rat) < r j) →
      ∀ (lam_min lam_max : Rat), (0 : Rat) < lam_min →
      (∀ i j, lam_min ≤ (1 + α i * β j) / (ℓ i * r j) ∧
              (1 + α i * β j) / (ℓ i * r j) ≤ lam_max) →
      cornerOptKappaSq (α i_max) (α i_min) (β j_max) (β j_min) ≤
        (lam_max / lam_min) * (lam_max / lam_min)) ∧
    (∀ α α_max α_min β β_max β_min : Rat,
      (1 + α * β_max) * (1 + α_min * β) - (1 + α * β) * (1 + α_min * β_max) =
        (α - α_min) * (β_max - β) ∧
      (1 + α * β_min) * (1 + α_max * β) - (1 + α * β) * (1 + α_max * β_min) =
        (α_max - α) * (β - β_min) ∧
      (1 + α * β) * (1 + α_max * β_max) - (1 + α * β_max) * (1 + α_max * β) =
        (α_max - α) * (β_max - β) ∧
      (1 + α * β) * (1 + α_min * β_min) - (1 + α * β_min) * (1 + α_min * β) =
        (α - α_min) * (β - β_min)) ∧
    (∀ α_min α_max β_min β_max : Rat,
      (0 : Rat) < α_min → α_min ≤ α_max → (0 : Rat) < β_min → β_min ≤ β_max →
      (∀ α β : Rat, α_min ≤ α → α ≤ α_max → β_min ≤ β → β ≤ β_max →
        1 / ((1 + α_max * β_max) * (1 + α_min * β_min)) ≤
          cornerPrecondEigSq α β α_max α_min β_max β_min ∧
        cornerPrecondEigSq α β α_max α_min β_max β_min ≤
          1 / ((1 + α_max * β_min) * (1 + α_min * β_max))) ∧
      cornerPrecondEigSq α_max β_max α_max α_min β_max β_min =
        1 / ((1 + α_max * β_min) * (1 + α_min * β_max)) ∧
      cornerPrecondEigSq α_min β_min α_max α_min β_max β_min =
        1 / ((1 + α_max * β_min) * (1 + α_min * β_max)) ∧
      cornerPrecondEigSq α_max β_min α_max α_min β_max β_min =
        1 / ((1 + α_max * β_max) * (1 + α_min * β_min)) ∧
      cornerPrecondEigSq α_min β_max α_max α_min β_max β_min =
        1 / ((1 + α_max * β_max) * (1 + α_min * β_min)) ∧
      (1 / ((1 + α_max * β_min) * (1 + α_min * β_max))) /
        (1 / ((1 + α_max * β_max) * (1 + α_min * β_min))) =
        cornerOptKappaSq α_max α_min β_max β_min) :=
  KroneckerCyclicFrustration.sum_of_two_kronecker_optimal_cond_exact

theorem multihead_two_head_zero_frustration_and_kfac_gap :
    (∀ {d : Nat} (b1 b2 : Fin d → Rat),
      (∀ j, (0 : Rat) < b1 j) → (∀ j, (0 : Rat) < b2 j) →
      ∀ (j_max j_min : Fin d) (ℓ1 ℓ2 : Rat) (r : Fin d → Rat),
      (0 : Rat) < ℓ1 → (0 : Rat) < ℓ2 → (∀ j, (0 : Rat) < r j) →
      ∀ (lam_min lam_max : Rat), (0 : Rat) < lam_min →
      (∀ j, lam_min ≤ b1 j / (ℓ1 * r j) ∧ b1 j / (ℓ1 * r j) ≤ lam_max ∧
            lam_min ≤ b2 j / (ℓ2 * r j) ∧ b2 j / (ℓ2 * r j) ≤ lam_max) →
      twoHeadOptKappaSq (b1 j_max) (b2 j_max) (b1 j_min) (b2 j_min) ≤
        (lam_max / lam_min) * (lam_max / lam_min)) ∧
    (∀ {d : Nat} (b1 b2 : Fin d → Rat),
      (∀ j, (0 : Rat) < b1 j) → (∀ j, (0 : Rat) < b2 j) →
      ∀ (j_max j_min : Fin d),
      let M_max := b1 j_max / b2 j_max
      let M_min := b1 j_min / b2 j_min
      (∀ j, M_min ≤ b1 j / b2 j ∧ b1 j / b2 j ≤ M_max) →
      let ℓ1Sq : Rat := 1
      let ℓ2Sq : Rat := 1 / (M_max * M_min)
      let rSq : Fin d → Rat := fun j => b1 j * b2 j
      (∀ j,
        M_min ≤ (b1 j * b1 j) / (ℓ1Sq * rSq j) ∧ (b1 j * b1 j) / (ℓ1Sq * rSq j) ≤ M_max ∧
        M_min ≤ (b2 j * b2 j) / (ℓ2Sq * rSq j) ∧ (b2 j * b2 j) / (ℓ2Sq * rSq j) ≤ M_max) ∧
      (b1 j_max * b1 j_max) / (ℓ1Sq * rSq j_max) = M_max ∧
      (b1 j_min * b1 j_min) / (ℓ1Sq * rSq j_min) = M_min ∧
      M_max / M_min = twoHeadOptKappaSq (b1 j_max) (b2 j_max) (b1 j_min) (b2 j_min)) ∧
    (∀ M : Rat, (1 : Rat) ≤ M →
      twoHeadOptKappaSq M 1 1 1 = M ∧
      (∀ h j : Fin 2, 1 / (1 + M) ≤ twoHeadKfacEig M h j ∧ twoHeadKfacEig M h j ≤ 1 / 2) ∧
      twoHeadKfacEig M ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 / 2 ∧
      twoHeadKfacEig M ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 / (1 + M) ∧
      (1 / 2 : Rat) / (1 / (1 + M)) = (1 + M) / 2 ∧
      (((1 + M) / 2) * ((1 + M) / 2)) / M = ((1 + M) * (1 + M)) / (4 * M)) ∧
    ((((1 + 4 : Rat) * (1 + 4)) / (4 * 4) = 25 / 16) ∧
     (((1 + 16 : Rat) * (1 + 16)) / (4 * 16) = 289 / 64) ∧
     (((1 + 64 : Rat) * (1 + 64)) / (4 * 64) = 4225 / 256) ∧
     (((1 + 256 : Rat) * (1 + 256)) / (4 * 256) = 66049 / 1024) ∧
     (((1 + 1024 : Rat) * (1 + 1024)) / (4 * 1024) = 1050625 / 4096)) :=
  KroneckerCyclicFrustration.multihead_two_head_zero_frustration_and_kfac_gap

theorem multihead_cyclic_frustration_karp_cycle_bound :
    (∀ {H d L : Nat} (hL : 0 < L)
      (b : Fin H → Fin d → Rat) (ℓ : Fin H → Rat) (r : Fin d → Rat),
      (∀ h j, (0 : Rat) < b h j) → (∀ h, (0 : Rat) < ℓ h) → (∀ j, (0 : Rat) < r j) →
      ∀ (head : Fin L → Fin H) (feat : Fin L → Fin d),
      karpScaledCycleProduct hL b ℓ r head feat = karpCycleProduct hL b head feat ∧
      (∀ (lam_min lam_max : Rat), (0 : Rat) < lam_min →
        (∀ h j, lam_min ≤ b h j / (ℓ h * r j) ∧ b h j / (ℓ h * r j) ≤ lam_max) →
        karpCycleProduct hL b head feat ≤ ratPow (lam_max / lam_min) L)) ∧
    (∀ (H : Nat), 2 ≤ H → ∀ (M : Rat), (1 : Rat) ≤ M →
      (∀ h1 h2 j1 j2 : Fin H,
        twoHeadOptKappaSq (cyclicWitness H M h1 j1) (cyclicWitness H M h2 j1)
                          (cyclicWitness H M h1 j2) (cyclicWitness H M h2 j2) ≤
          ratPow M H) ∧
      (∀ (ℓ r : Fin H → Rat), (∀ h, (0 : Rat) < ℓ h) → (∀ j, (0 : Rat) < r j) →
        ∀ (lam_min lam_max : Rat), (0 : Rat) < lam_min →
        (∀ h j, lam_min ≤ cyclicWitness H M h j / (ℓ h * r j) ∧
                cyclicWitness H M h j / (ℓ h * r j) ≤ lam_max) →
        ratPow M (H * (H - 1)) ≤ ratPow (lam_max / lam_min) H) ∧
      (∀ h j : Fin H,
        (1 : Rat) ≤ cyclicWitness H M h j ∧ cyclicWitness H M h j ≤ ratPow M (H - 1))) ∧
    (cyclicFrustrationRatio 2 = 1 ∧
     cyclicFrustrationRatio 3 = 4 / 3 ∧
     cyclicFrustrationRatio 4 = 3 / 2 ∧
     cyclicFrustrationRatio 8 = 7 / 4) :=
  KroneckerCyclicFrustration.multihead_cyclic_frustration_karp_cycle_bound

theorem monarch_coherence_factorization_and_lower_bound :
    (∀ {n1 n2 : Nat} (A : Fin n2 → Fin n2 → Int) (B : Fin n1 → Fin n1 → Int)
      (a1 a2 : Fin n2) (b1 b2 : Fin n1),
      finSumInt (fun b' : Fin n1 =>
        finSumInt (fun a' : Fin n2 =>
          monarchEntry A B (b', a') (a1, b1) * monarchEntry A B (b', a') (a2, b2))) =
      matColDot A a1 a2 * matColDot B b1 b2) ∧
    (∀ {n1 n2 : Nat} (A : Fin n2 → Fin n2 → Int) (B : Fin n1 → Fin n1 → Int) (S_A S_B : Int),
      IsScaledOrtho A S_A → IsScaledOrtho B S_B →
      ∀ (a1 a2 : Fin n2) (b1 b2 : Fin n1),
        finSumInt (fun b' : Fin n1 =>
          finSumInt (fun a' : Fin n2 =>
            monarchEntry A B (b', a') (a1, b1) * monarchEntry A B (b', a') (a2, b2))) =
        if a1 = a2 ∧ b1 = b2 then S_A * S_B else 0) ∧
    (∀ {n1 n2 : Nat} (A : Fin n2 → Fin n2 → Int) (B : Fin n1 → Fin n1 → Int)
      (maxSqA maxSqB S_A S_B : Int),
      (0 : Int) ≤ maxSqA → (0 : Int) ≤ maxSqB →
      (∀ a' a, A a' a * A a' a ≤ maxSqA) →
      (∀ b' b, B b' b * B b' b ≤ maxSqB) →
      (∀ (a' : Fin n2) (a : Fin n2) (b' : Fin n1) (b : Fin n1),
        monarchEntry A B (b', a') (a, b) * monarchEntry A B (b', a') (a, b) ≤ maxSqA * maxSqB) ∧
      (∀ (a'0 a0 : Fin n2) (b'0 b0 : Fin n1),
        A a'0 a0 * A a'0 a0 = maxSqA → B b'0 b0 * B b'0 b0 = maxSqB →
        monarchEntry A B (b'0, a'0) (a0, b0) * monarchEntry A B (b'0, a'0) (a0, b0) =
          maxSqA * maxSqB) ∧
      ((0 : Int) < S_A → (0 : Int) < S_B →
        (((maxSqA * maxSqB : Int) : Rat) / ((S_A * S_B : Int) : Rat)) =
        ((maxSqA : Rat) / (S_A : Rat)) * ((maxSqB : Rat) / (S_B : Rat)))) ∧
    (∀ {n : Nat} (v : Fin n → Int) (M : Int),
      (0 : Int) ≤ M → (∀ j : Fin n, v j * v j ≤ M) →
      vecNormSq v ≤ (vecNnz v : Int) * M ∧
      ((0 : Int) < vecNormSq v → 0 < vecNnz v →
        (1 : Rat) / ((vecNnz v : Int) : Rat) ≤ (M : Rat) / (vecNormSq v : Rat))) :=
  KroneckerCyclicFrustration.monarch_coherence_factorization_and_lower_bound

theorem octonion_sparse_e2m1_monarch_blocks_exact :
    (∀ a b c d : Int, IsScaledOrtho (quat4 a b c d) (a * a + b * b + c * c + d * d)) ∧
    (∀ c0 c1 c2 c3 c4 c5 c6 c7 : Int,
      IsScaledOrtho (oct8 c0 c1 c2 c3 c4 c5 c6 c7)
        (c0 * c0 + c1 * c1 + c2 * c2 + c3 * c3 + c4 * c4 + c5 * c5 + c6 * c6 + c7 * c7)) ∧
    (∀ s : Nat, 1 ≤ s → s ≤ 4 → IsOptimalSparseE2M1Block (sparseQuat4 s) s) ∧
    (∀ s : Nat, 1 ≤ s → s ≤ 8 → IsOptimalSparseE2M1Block (sparseOct8 s) s) ∧
    (IsOptimalSparseE2M1Block (sparseQuat4 3) 3 ∧
     IsOptimalSparseE2M1Block (sparseOct8 4) 4 ∧
     IsOptimalSparseE2M1Block (sparseOct8 7) 7 ∧
     ((4 + 4 : Nat) = 8 ∧ (8 : Rat) / 16 = 1 / 2) ∧
     ((7 + 4 : Nat) = 11 ∧ (16 - 11 : Rat) / 16 = 5 / 16) ∧
     (((1 : Rat) / 4) * ((1 : Rat) / 4) = 1 / 16) ∧
     (((1 : Rat) / 7) * ((1 : Rat) / 4) = 1 / 28)) :=
  KroneckerCyclicFrustration.octonion_sparse_e2m1_monarch_blocks_exact

theorem kfac_cross_scale_suboptimality_witness :
    (∀ K : Rat, (0 : Rat) < K →
      let sumK := K + 1 / K
      let kfacRatio :=
        kfacPrecondEig 2 (1 / K) (1 / K) sumK sumK /
        kfacPrecondEig 2 (1 / K) K sumK sumK
      cornerOptKappaSq K (1 / K) K (1 / K) =
        ((K * K + 1) * (K * K + 1)) / (4 * K * K) ∧
      kfacRatio = ((K * K + 1) * (K * K + 3)) / (2 * (3 * K * K + 1)) ∧
      (kfacRatio * kfacRatio) / cornerOptKappaSq K (1 / K) K (1 / K) =
        (K * K * (K * K + 3) * (K * K + 3)) / ((3 * K * K + 1) * (3 * K * K + 1)) ∧
      (K * K) / 9 < (kfacRatio * kfacRatio) / cornerOptKappaSq K (1 / K) K (1 / K)) ∧
    (∀ C : Rat, ∃ K : Rat, (0 : Rat) < K ∧
      let sumK := K + 1 / K
      let kfacRatio :=
        kfacPrecondEig 2 (1 / K) (1 / K) sumK sumK /
        kfacPrecondEig 2 (1 / K) K sumK sumK
      C * cornerOptKappaSq K (1 / K) K (1 / K) < kfacRatio * kfacRatio) ∧
    (let K : Rat := 128
     let sumK := K + 1 / K
     let kfacRatio :=
       kfacPrecondEig 2 (1 / K) (1 / K) sumK sumK /
       kfacPrecondEig 2 (1 / K) K sumK sumK
     cornerOptKappaSq K (1 / K) K (1 / K) = (268468225 : Rat) / 65536 ∧
     1000 * cornerOptKappaSq K (1 / K) K (1 / K) < kfacRatio * kfacRatio ∧
     1800 * cornerOptKappaSq K (1 / K) K (1 / K) < kfacRatio * kfacRatio) :=
  KroneckerCyclicFrustration.kfac_cross_scale_suboptimality_witness

end KroneckerCyclicFrustrationChallenge
