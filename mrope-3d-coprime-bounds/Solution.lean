/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mrope3dCoprime

/-!
# Verified Solutions (`mrope-3d-coprime-bounds`)
-/

namespace Mrope3dCoprimeChallenge

open Mrope3dCoprime

theorem separable_3d_mrope_axis_floor_theorem :
    (∀ (PT PH PW : Nat)
      (cT : Fin PT → Int → Rat) (cH : Fin PH → Int → Rat) (cW : Fin PW → Int → Rat),
      (∀ k, cT k 0 = 1) → (∀ k, cH k 0 = 1) → (∀ k, cW k 0 = 1) →
      (∀ dT : Int, sep3DKernel PT PH PW cT cH cW dT 0 0 =
        (((PH + PW : Nat) : Rat) + sepAxisSum PT cT dT) / ((PT + PH + PW : Nat) : Rat)) ∧
      (∀ dH : Int, sep3DKernel PT PH PW cT cH cW 0 dH 0 =
        (((PT + PW : Nat) : Rat) + sepAxisSum PH cH dH) / ((PT + PH + PW : Nat) : Rat)) ∧
      (∀ dW : Int, sep3DKernel PT PH PW cT cH cW 0 0 dW =
        (((PT + PH : Nat) : Rat) + sepAxisSum PW cW dW) / ((PT + PH + PW : Nat) : Rat))) ∧
    (∀ (PT PH PW : Nat), 0 < PT + PH + PW →
      ∀ (cT : Fin PT → Int → Rat) (cH : Fin PH → Int → Rat) (cW : Fin PW → Int → Rat)
      (dT dH dW : Int) (M Mmin : Rat),
      (∀ k, cT k 0 = 1) → (∀ k, cH k 0 = 1) → (∀ k, cW k 0 = 1) →
      Mmin ≤ sepAxisSum PT cT dT →
      Mmin ≤ sepAxisSum PH cH dH →
      Mmin ≤ sepAxisSum PW cW dW →
      ratAbs (sep3DKernel PT PH PW cT cH cW dT 0 0) ≤ M →
      ratAbs (sep3DKernel PT PH PW cT cH cW 0 dH 0) ≤ M →
      ratAbs (sep3DKernel PT PH PW cT cH cW 0 0 dW) ≤ M →
      ((((PT + PH + PW) - min3 PT PH PW : Nat) : Rat) + Mmin) /
        ((PT + PH + PW : Nat) : Rat) ≤ M) ∧
    (∀ (cT : Fin 16 → Int → Rat) (cH : Fin 24 → Int → Rat) (cW : Fin 24 → Int → Rat),
      (∀ k, cH k 0 = 1) → (∀ k, cW k 0 = 1) →
      (∀ dT : Int, (0 : Rat) ≤ sepAxisSum 16 cT dT →
        (3 / 4 : Rat) ≤ sep3DKernel 16 24 24 cT cH cW dT 0 0 ∧
        (3 / 4 : Rat) ≤ ratAbs (sep3DKernel 16 24 24 cT cH cW dT 0 0)) ∧
      (∀ (L : Nat), 0 < L →
        (0 : Rat) ≤ finSum (fun j : Fin L => sepAxisSum 16 cT (j.val + 1)) →
        ∃ j : Fin L, (0 : Rat) ≤ sepAxisSum 16 cT (j.val + 1) ∧
          (3 / 4 : Rat) ≤ ratAbs (sep3DKernel 16 24 24 cT cH cW (j.val + 1) 0 0)) ∧
      (∀ (N d : Nat) (v : Fin N → Fin d → Rat), 2 ≤ N →
        (∀ t : Fin N, l2NormSq (v t) = 16) →
        (∀ t s : Fin N, sepAxisSum 16 cT ((t.val : Int) - (s.val : Int)) = dotProd (v t) (v s)) →
        ∃ t s : Fin N, t ≠ s ∧
          (3 / 4 : Rat) - (1 : Rat) / (4 * ((N - 1 : Nat) : Rat)) ≤
            sep3DKernel 16 24 24 cT cH cW ((t.val : Int) - (s.val : Int)) 0 0)) :=
  Mrope3dCoprime.separable_3d_mrope_axis_floor_theorem

theorem coupled_3d_mrope_shatters_separable_floor :
    (∀ (P : Nat), 0 < P → ∀ (c : Fin P → Int → Int → Int → Rat) (dT : Int) (B : Rat),
      (0 : Rat) ≤ B →
      (∀ k : Fin P, ratAbs (c k dT 0 0) ≤ B) →
      ratAbs (coupled3DGeneral P c dT 0 0) ≤ B) ∧
    (coupled3DKernelQ4 64 ωT64 ωH64 ωW64 0 0 0 = 1 ∧
      (∀ dT dH dW : Int, ¬ (dT % 4 = 0 ∧ dH % 4 = 0 ∧ dW % 4 = 0) →
        coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT dH dW = 0 ∧
        ratAbs (coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT dH dW) < (1 / 2 : Rat) ∧
        ratAbs (coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT dH dW) < (3 / 4 : Rat)) ∧
      (∀ ε : Rat, (0 : Rat) < ε → ∀ dT : Int, dT % 4 ≠ 0 →
        ratAbs (coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT 0 0) < ε)) ∧
    ((∀ k : Fin 27, ωT27 k ≠ 0 ∧ ωH27 k ≠ 0 ∧ ωW27 k ≠ 0) ∧
      coupled3DKernelQ4 27 ωT27 ωH27 ωW27 0 0 0 = 1 ∧
      (∀ dT dH dW : Int, ¬ (dT % 4 = 0 ∧ dH % 4 = 0 ∧ dW % 4 = 0) →
        ratAbs (coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW) ≤ (1 / 3 : Rat) ∧
        ratAbs (coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW) < (1 / 2 : Rat) ∧
        ratAbs (coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW) < (3 / 4 : Rat) ∧
        coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW *
          coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW ≤ (1 / 9 : Rat))) :=
  Mrope3dCoprime.coupled_3d_mrope_shatters_separable_floor

theorem contiguous_mrope_bf16_width_freeze_exact :
    (ratPow (pow2Rat 12) 64 < ratPow (1000000 : Rat) 40) ∧
    (∀ (k : Nat) (θ : Rat), 40 ≤ k → k ≤ 63 → (0 : Rat) ≤ θ →
      ratPow θ 64 * ratPow (1000000 : Rat) k ≤ 1 →
      θ < invPow2Rat 12) ∧
    (∀ (dW : Nat) (θ : Rat), 1 ≤ dW → dW ≤ 63 → (0 : Rat) ≤ θ → θ ≤ invPow2Rat 12 →
      (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) < invPow2Rat 13 ∧
      (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) < invPow2Rat 9 ∧
      1 - invPow2Rat 9 < 1 - (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ)) ∧
    (∀ (k dW : Nat) (θ c : Rat),
      40 ≤ k → k ≤ 63 → 1 ≤ dW → dW ≤ 63 →
      (0 : Rat) ≤ θ → ratPow θ 64 * ratPow (1000000 : Rat) k ≤ 1 →
      1 - (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) ≤ c → c ≤ 1 →
      bf16SnapsToOne c) :=
  Mrope3dCoprime.contiguous_mrope_bf16_width_freeze_exact

theorem interleaved_vs_contiguous_mrope_resolution_gap :
    (∀ (θ0sq q : Rat),
      geomResContigW θ0sq q * (1 - q) =
        (1 / 2 : Rat) * θ0sq * ratPow q 40 * (1 - ratPow q 24) ∧
      geomResInterleavedStride3 θ0sq q * (1 - ratPow q 3) =
        (1 / 2 : Rat) * θ0sq * ratPow q 2 * (1 - ratPow q 72)) ∧
    (∀ (θ0sq q : Rat), (0 : Rat) < θ0sq → (0 : Rat) < q → q < 1 →
      (θ0sq * ratPow q 2) / (θ0sq * ratPow q 40) = 1 / ratPow q 38 ∧
      geomResInterleavedStride3 θ0sq q / geomResContigW θ0sq q =
        (1 / ratPow q 38) * ((1 + ratPow q 24 + ratPow q 48) / (1 + q + q * q))) ∧
    (∀ (q b : Rat), (0 : Rat) < q → (0 : Rat) < b → ratPow q 32 * b = 1 →
      ratPow (1 / ratPow q 38) 16 = ratPow b 19) ∧
    (∀ (θ0sq q : Rat), (0 : Rat) < θ0sq → (0 : Rat) < q → q < 1 →
      ratPow q 32 * (1000000 : Rat) = 1 →
      (10000000 : Rat) < 1 / ratPow q 38 ∧
      (1000000 : Rat) < geomResInterleavedStride3 θ0sq q / geomResContigW θ0sq q ∧
      (1000000 : Rat) < geomResQwen3InterleavedW θ0sq q / geomResContigW θ0sq q) :=
  Mrope3dCoprime.interleaved_vs_contiguous_mrope_resolution_gap

theorem q32_3d_modular_phase_exact_relative_invariance :
    (∀ ωT ωH ωW T1 H1 W1 T2 H2 W2 : Int,
      q32PhaseDiff (q32Phase ωT ωH ωW T2 H2 W2) (q32Phase ωT ωH ωW T1 H1 W1) =
        q32Phase ωT ωH ωW (T2 - T1) (H2 - H1) (W2 - W1)) ∧
    (∀ ωT ωH ωW m T H W : Int,
      q32PhaseDiff (q32Phase ωT ωH ωW T H W) (q32Phase ωT ωH ωW m m m) =
        q32Phase ωT ωH ωW (T - m) (H - m) (W - m)) ∧
    (∀ ωT ωH ωW T1 H1 W1 T2 H2 W2 sT sH sW : Int,
      q32PhaseDiff (q32Phase ωT ωH ωW (T2 + sT) (H2 + sH) (W2 + sW))
                   (q32Phase ωT ωH ωW (T1 + sT) (H1 + sH) (W1 + sW)) =
        q32PhaseDiff (q32Phase ωT ωH ωW T2 H2 W2) (q32Phase ωT ωH ωW T1 H1 W1)) ∧
    (∀ ωT ωH ωW T H W : Int,
      q32Phase ωT ωH ωW (T + Q32_MOD) H W = q32Phase ωT ωH ωW T H W ∧
      q32Phase ωT ωH ωW T (H + Q32_MOD) W = q32Phase ωT ωH ωW T H W ∧
      q32Phase ωT ωH ωW T H (W + Q32_MOD) = q32Phase ωT ωH ωW T H W) ∧
    (∀ ω Δ : Int, ω % 2 = 1 → ((Δ * ω) % Q32_MOD = 0 ↔ Δ % Q32_MOD = 0)) ∧
    (∀ ωT ωH ωW T H W Δ : Int, 0 < Δ → Δ < Q32_MOD →
      (ωT % 2 = 1 → q32Phase ωT ωH ωW (T + Δ) H W ≠ q32Phase ωT ωH ωW T H W) ∧
      (ωH % 2 = 1 → q32Phase ωT ωH ωW T (H + Δ) W ≠ q32Phase ωT ωH ωW T H W) ∧
      (ωW % 2 = 1 → q32Phase ωT ωH ωW T H (W + Δ) ≠ q32Phase ωT ωH ωW T H W)) :=
  Mrope3dCoprime.q32_3d_modular_phase_exact_relative_invariance

theorem cross_modal_fp_phase_drift_vs_q32_exact :
    (pow2Rat 17 = 131072 ∧
      fpUlpAtPow2 7 17 = 1024 ∧
      fpUlpAtPow2 7 16 = 512 ∧
      FP16_MAX = (2 - invPow2Rat 10) * pow2Rat 15 ∧
      fp16Overflows (pow2Rat 17)) ∧
    (∀ T H W : Nat, T ≤ 255 → H ≤ 63 → W ≤ 63 →
      rneSnapsToPow2 7 17 (pow2Rat 17 - (T : Rat)) ∧
      rneSnapsToPow2 7 17 (pow2Rat 17 - (H : Rat)) ∧
      rneSnapsToPow2 7 17 (pow2Rat 17 - (W : Rat)) ∧
      rneSnapsToPow2 7 17 (pow2Rat 17 + (T : Rat)) ∧
      fp16Overflows (pow2Rat 17 - (T : Rat))) ∧
    (∀ ωT ωH ωW : Int, ∀ T H W : Nat,
      q32PhaseDiff (q32Phase ωT ωH ωW T H W) (q32Phase ωT ωH ωW 131072 131072 131072) =
        q32Phase ωT ωH ωW ((T : Int) - 131072) ((H : Int) - 131072) ((W : Int) - 131072)) ∧
    (∀ ωT ωH ωW : Int, ωT % 2 = 1 → ωH % 2 = 1 → ωW % 2 = 1 →
      (∀ T1 T2 H W : Nat, T1 ≤ 255 → T2 ≤ 255 → T1 ≠ T2 →
        q32PhaseDiff (q32Phase ωT ωH ωW T1 H W) (q32Phase ωT ωH ωW 131072 131072 131072) ≠
        q32PhaseDiff (q32Phase ωT ωH ωW T2 H W) (q32Phase ωT ωH ωW 131072 131072 131072)) ∧
      (∀ T H1 H2 W : Nat, H1 ≤ 63 → H2 ≤ 63 → H1 ≠ H2 →
        q32PhaseDiff (q32Phase ωT ωH ωW T H1 W) (q32Phase ωT ωH ωW 131072 131072 131072) ≠
        q32PhaseDiff (q32Phase ωT ωH ωW T H2 W) (q32Phase ωT ωH ωW 131072 131072 131072)) ∧
      (∀ T H W1 W2 : Nat, W1 ≤ 63 → W2 ≤ 63 → W1 ≠ W2 →
        q32PhaseDiff (q32Phase ωT ωH ωW T H W1) (q32Phase ωT ωH ωW 131072 131072 131072) ≠
        q32PhaseDiff (q32Phase ωT ωH ωW T H W2) (q32Phase ωT ωH ωW 131072 131072 131072))) :=
  Mrope3dCoprime.cross_modal_fp_phase_drift_vs_q32_exact

end Mrope3dCoprimeChallenge
