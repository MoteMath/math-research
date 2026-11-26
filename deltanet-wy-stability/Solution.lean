/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltanetWyStability

/-!
# Verified Solutions (`deltanet-wy-stability`)
-/

namespace DeltanetWyStabilityChallenge

open DeltanetWyStability

theorem deltanet_spectral_stability_iff (d : Nat) (α β : Rat)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β)
    (k : Fin d → Rat) (hk : 0 < normSq k) :
    (∀ v : Fin d → Rat, normSq (deltaNetStep α β k v) ≤ normSq v) ↔
    β * normSq k ≤ (1 + α) / α :=
  DeltanetWyStability.deltanet_spectral_stability_iff d α β hα0 hα1 hβ0 k hk

theorem mxfp4_mxfp6_fp8_bf16_norm_blowup_and_beta_safe :
    (∀ y : Fin 32 → Rat, (∃ i0, 4 ≤ ratAbs (y i0)) →
      normSq (fun i => e2m1Quant (y i)) ≤ (700 / 431) * normSq y) ∧
    ((∃ i0, 4 ≤ ratAbs (e2m1OcpWitness i0)) ∧
      normSq (fun i => e2m1Quant (e2m1OcpWitness i)) = (700 / 431) * normSq e2m1OcpWitness) ∧
    (36 / 25 : Rat) < 700 / 431 ∧
    betaSafe (700 / 431) = 431 / 350 ∧
    (∀ y : Fin 32 → Rat, (∃ i0, 3 ≤ ratAbs (y i0)) →
      normSq (fun i => e2m1Quant (y i)) ≤ (380 / 227) * normSq y) ∧
    ((∃ i0, 3 < ratAbs (e2m1MaxFitWitness i0)) ∧
      normSq (fun i => e2m1Quant (e2m1MaxFitWitness i)) = (380 / 227) * normSq e2m1MaxFitWitness) ∧
    betaSafe (380 / 227) = 227 / 190 ∧
    (∀ m : Nat, ∀ t : Rat, normalBinMid m ≤ t →
      (normalBinUpper m / t) * (normalBinUpper m / t) ≤ normalMaxRatioSq m) ∧
    (∀ m : Nat, (normalBinUpper m / normalBinMid m) * (normalBinUpper m / normalBinMid m) =
      normalMaxRatioSq m) ∧
    (normalMaxRatioSq 1 = 36 / 25 ∧ betaSafe (normalMaxRatioSq 1) = 25 / 18) ∧
    (normalMaxRatioSq 2 = 100 / 81 ∧ betaSafe (normalMaxRatioSq 2) = 81 / 50) ∧
    (normalMaxRatioSq 3 = 324 / 289 ∧ betaSafe (normalMaxRatioSq 3) = 289 / 162) ∧
    (normalMaxRatioSq 7 = 66564 / 66049 ∧ betaSafe (normalMaxRatioSq 7) = 66049 / 33282) :=
  DeltanetWyStability.mxfp4_mxfp6_fp8_bf16_norm_blowup_and_beta_safe

theorem wy_inverse_closed_form_and_aligned_contraction :
    (∀ (C d : Nat) (α : Rat) (betas : Fin C → Rat) (keys : Fin C → Fin d → Rat),
      matMul (matAdd (idMat C) (wyL C d α betas keys)) (wyT C d α betas keys) = idMat C) ∧
    (∀ (C d : Nat) (α β : Rat) (k : Fin d → Rat) (i j : Fin C), j.val < i.val →
      wyT C d α (fun _ => β) (fun _ => k) i j =
        -(β * normSq k * ratPow α (i.val - j.val) * ratPow (1 - β * normSq k) (i.val - j.val - 1))) ∧
    (∀ (C d : Nat) (α β : Rat) (k : Fin d → Rat),
      0 < α → α ≤ 1 → 0 ≤ β → β * normSq k ≤ 2 →
      (∀ i j : Fin C, j.val < i.val →
        ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j) ≤ β * normSq k) ∧
      (∀ i : Fin C,
        sumFin (fun j : Fin C => ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j)) ≤
          1 + ((C - 1 : Nat) : Rat) * (β * normSq k) ∧
        sumFin (fun j : Fin C => ratAbs (wyT C d α (fun _ => β) (fun _ => k) i j)) ≤
          2 * (C : Rat) - 1)) ∧
    (∀ (C d : Nat) (hC : 2 ≤ C) (k : Fin d → Rat), 1 < normSq k →
      ratAbs (wyT C d 1 (fun _ => 2) (fun _ => k) ⟨C - 1, by omega⟩ ⟨0, by omega⟩) =
        2 * normSq k * ratPow (2 * normSq k - 1) (C - 2)) :=
  DeltanetWyStability.wy_inverse_closed_form_and_aligned_contraction

theorem euler_product_binomial_peak_explosion :
    (∀ (C : Nat) (β : Rat) (k : Nat), 1 ≤ k → ∀ (i j : Fin C), j.val + k ≤ i.val →
      matPow (alignedL C β) k i j =
        ratPow β k * ((choose (i.val - j.val - 1) (k - 1) : Nat) : Rat)) ∧
    matPow (alignedL 16 1) 8 ⟨15, by decide⟩ ⟨0, by decide⟩ = 3432 ∧
    matPow (alignedL 64 1) 32 ⟨63, by decide⟩ ⟨0, by decide⟩ = 465428353255261088 ∧
    matPow (alignedL 64 2) 32 ⟨63, by decide⟩ ⟨0, by decide⟩ =
      ratPow 2 32 * 465428353255261088 ∧
    (1000000000000000000000000000 : Rat) <
      matPow (alignedL 64 2) 32 ⟨63, by decide⟩ ⟨0, by decide⟩ :=
  DeltanetWyStability.euler_product_binomial_peak_explosion

theorem block_schur_wy_exact_inverse (n m : Nat)
    (A A_inv : RatMat n n) (C : RatMat m n) (D D_inv : RatMat m m)
    (hAL : matMul A_inv A = idMat n) (hAR : matMul A A_inv = idMat n)
    (hDL : matMul D_inv D = idMat m) (hDR : matMul D D_inv = idMat m) :
    matMul (blockLower A C D) (blockSchurInv A_inv C D_inv) = idMat (n + m) ∧
    matMul (blockSchurInv A_inv C D_inv) (blockLower A C D) = idMat (n + m) :=
  DeltanetWyStability.block_schur_wy_exact_inverse n m A A_inv C D D_inv hAL hAR hDL hDR

end DeltanetWyStabilityChallenge
