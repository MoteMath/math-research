/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp8Frontier

/-!
# Verified Solutions (`mxfp8-e2m5-e3m4-frontier`)
-/

namespace Mxfp8FrontierChallenge

open Mxfp8Frontier

theorem fp8_e1m6_collapse_to_int8_exact :
    (∀ m_bits c : Nat, c < 2 ^ (m_bits + 1) →
      fp8MagInt 1 m_bits c = fp8MagInt 0 (m_bits + 1) c ∧
      fp8MagInt 1 m_bits c = c) ∧
    (∀ c : Nat, c < 128 →
      fp8MagInt 1 6 c = fp8MagInt 0 7 c ∧
      fp8NormRat 1 6 127 c = fp8NormRat 0 7 127 c) ∧
    (fp8MagInt 0 7 127 = 127 ∧
     fp8MagInt 1 6 127 = 127 ∧
     fp8MagInt 2 5 127 = 252 ∧
     fp8MagInt 3 4 127 = 1984 ∧
     fp8MagInt 4 3 126 = 229376 ∧
     fp8MagInt 5 2 123 = 3758096384) ∧
    (127 < 252 ∧ 252 < 1984 ∧ 1984 < 229376 ∧ 229376 < 3758096384) :=
  Mxfp8Frontier.fp8_e1m6_collapse_to_int8_exact

theorem mxfp8_e4m3_vs_e5m2_all_b_crossover_exact :
    (∀ B : Nat, 1 ≤ B →
      (alphaE8M0_E4M3 B ≤ ef21AlphaCand 278528 16384 1 1 B ∧
       alphaE8M0_E4M3 B ≤ ef21AlphaCand 237568 8192 1 1 B ∧
       alphaE8M0_E4M3 B ≤ ef21AlphaCand 229376 0 1 1 B) ∧
      (alphaCont_E4M3 B ≤ ef21AlphaCand 458752 0 278528 16384 B ∧
       alphaCont_E4M3 B ≤ ef21AlphaCand 458752 0 1 1 B) ∧
      (alphaE8M0_E5M2 B ≤ ef21AlphaCand 4831838208 536870912 1 1 B ∧
       alphaE8M0_E5M2 B ≤ ef21AlphaCand 4026531840 268435456 1 1 B ∧
       alphaE8M0_E5M2 B ≤ ef21AlphaCand 3758096384 0 1 1 B) ∧
      (alphaCont_E5M2 B ≤ ef21AlphaCand 7516192768 0 4831838208 536870912 B ∧
       alphaCont_E5M2 B ≤ ef21AlphaCand 7516192768 0 1 1 B)) ∧
    ((∀ B : Nat, 1 ≤ B → B ≤ 637534210 → alphaE8M0_E5M2 B < alphaE8M0_E4M3 B) ∧
     (∀ B : Nat, 637534211 ≤ B → alphaE8M0_E4M3 B < alphaE8M0_E5M2 B)) ∧
    ((alphaCont_E4M3 1 = 1 ∧ alphaCont_E5M2 1 = 1) ∧
     (∀ B : Nat, 2 ≤ B → B ≤ 2630667467 → alphaCont_E5M2 B < alphaCont_E4M3 B) ∧
     (∀ B : Nat, 2630667468 ≤ B → alphaCont_E4M3 B < alphaCont_E5M2 B)) ∧
    (((1 - alphaE8M0_E4M3 128) * (356 / 100 : Rat) < 1 - alphaE8M0_E5M2 128) ∧
     ((1 - alphaE8M0_E4M3 16384) * (356 / 100 : Rat) < 1 - alphaE8M0_E5M2 16384) ∧
     ((1 - alphaCont_E4M3 128) * (357 / 100 : Rat) < 1 - alphaCont_E5M2 128) ∧
     ((1 - alphaCont_E4M3 16384) * (356 / 100 : Rat) < 1 - alphaCont_E5M2 16384)) :=
  Mxfp8Frontier.mxfp8_e4m3_vs_e5m2_all_b_crossover_exact

theorem mxfp8_e8m0_complete_five_regime_frontier :
    (∀ B : Nat, 1 ≤ B → B ≤ 4 →
      alphaE8M0_E2M5 B < alphaE8M0_INT8 B ∧
      alphaE8M0_E3M4 B < alphaE8M0_INT8 B ∧
      alphaE8M0_E4M3 B < alphaE8M0_INT8 B ∧
      alphaE8M0_E5M2 B < alphaE8M0_INT8 B) ∧
    (∀ B : Nat, 5 ≤ B → B ≤ 47 →
      alphaE8M0_INT8 B < alphaE8M0_E2M5 B ∧
      alphaE8M0_E3M4 B < alphaE8M0_E2M5 B ∧
      alphaE8M0_E4M3 B < alphaE8M0_E2M5 B ∧
      alphaE8M0_E5M2 B < alphaE8M0_E2M5 B) ∧
    (∀ B : Nat, 48 ≤ B → B ≤ 11379 →
      alphaE8M0_INT8 B < alphaE8M0_E3M4 B ∧
      alphaE8M0_E2M5 B < alphaE8M0_E3M4 B ∧
      alphaE8M0_E4M3 B < alphaE8M0_E3M4 B ∧
      alphaE8M0_E5M2 B < alphaE8M0_E3M4 B) ∧
    (∀ B : Nat, 11380 ≤ B → B ≤ 637534210 →
      alphaE8M0_INT8 B < alphaE8M0_E4M3 B ∧
      alphaE8M0_E2M5 B < alphaE8M0_E4M3 B ∧
      alphaE8M0_E3M4 B < alphaE8M0_E4M3 B ∧
      alphaE8M0_E5M2 B < alphaE8M0_E4M3 B) ∧
    (∀ B : Nat, 637534211 ≤ B →
      alphaE8M0_INT8 B < alphaE8M0_E5M2 B ∧
      alphaE8M0_E2M5 B < alphaE8M0_E5M2 B ∧
      alphaE8M0_E3M4 B < alphaE8M0_E5M2 B ∧
      alphaE8M0_E4M3 B < alphaE8M0_E5M2 B) ∧
    ((1 - alphaE8M0_E3M4 128) * (365 / 100 : Rat) < 1 - alphaE8M0_E4M3 128) :=
  Mxfp8Frontier.mxfp8_e8m0_complete_five_regime_frontier

theorem deepseek_fp32_scale_complete_five_regime_frontier :
    (alphaCont_INT8 1 = 1 ∧ alphaCont_E2M5 1 = 1 ∧ alphaCont_E3M4 1 = 1 ∧
     alphaCont_E4M3 1 = 1 ∧ alphaCont_E5M2 1 = 1) ∧
    (∀ B : Nat, 2 ≤ B → B ≤ 12 →
      alphaCont_E2M5 B < alphaCont_INT8 B ∧
      alphaCont_E3M4 B < alphaCont_INT8 B ∧
      alphaCont_E4M3 B < alphaCont_INT8 B ∧
      alphaCont_E5M2 B < alphaCont_INT8 B) ∧
    (∀ B : Nat, 13 ≤ B → B ≤ 230 →
      alphaCont_INT8 B < alphaCont_E2M5 B ∧
      alphaCont_E3M4 B < alphaCont_E2M5 B ∧
      alphaCont_E4M3 B < alphaCont_E2M5 B ∧
      alphaCont_E5M2 B < alphaCont_E2M5 B) ∧
    (∀ B : Nat, 231 ≤ B → B ≤ 54668 →
      alphaCont_INT8 B < alphaCont_E3M4 B ∧
      alphaCont_E2M5 B < alphaCont_E3M4 B ∧
      alphaCont_E4M3 B < alphaCont_E3M4 B ∧
      alphaCont_E5M2 B < alphaCont_E3M4 B) ∧
    (∀ B : Nat, 54669 ≤ B → B ≤ 2630667467 →
      alphaCont_INT8 B < alphaCont_E4M3 B ∧
      alphaCont_E2M5 B < alphaCont_E4M3 B ∧
      alphaCont_E3M4 B < alphaCont_E4M3 B ∧
      alphaCont_E5M2 B < alphaCont_E4M3 B) ∧
    (∀ B : Nat, 2630667468 ≤ B →
      alphaCont_INT8 B < alphaCont_E5M2 B ∧
      alphaCont_E2M5 B < alphaCont_E5M2 B ∧
      alphaCont_E3M4 B < alphaCont_E5M2 B ∧
      alphaCont_E4M3 B < alphaCont_E5M2 B) ∧
    (((1 - alphaCont_E2M5 128) * (677 / 100 : Rat) < 1 - alphaCont_E4M3 128) ∧
     ((1 - alphaCont_E3M4 16384) * (332 / 100 : Rat) < 1 - alphaCont_E4M3 16384)) :=
  Mxfp8Frontier.deepseek_fp32_scale_complete_five_regime_frontier

theorem delayed_scaling_spike_clipping_crossover_exact :
    (∀ (M m : Nat), delayedClipDelta (spikeCrossover M m) M = wideNormalDelta m) ∧
    (∀ (M m : Nat) (ρ : Rat), pow2Rat M < ρ →
      (wideNormalDelta m < delayedClipDelta ρ M ↔ spikeCrossover M m < ρ) ∧
      (delayedClipDelta ρ M < wideNormalDelta m ↔ ρ < spikeCrossover M m)) ∧
    (wideNormalDelta 2 = 1 / 81 ∧
     (∀ M : Nat, spikeCrossover M 2 = (9 / 8 : Rat) * pow2Rat M) ∧
     (spikeCrossover 0 2 = 9 / 8 ∧ spikeCrossover 1 2 = 9 / 4 ∧
      spikeCrossover 2 2 = 9 / 2 ∧ spikeCrossover 3 2 = 9 ∧
      spikeCrossover 4 2 = 18)) ∧
    (∀ (M : Nat) (k_norm ns_norm e_ns e_e5m2 : Rat),
      0 < k_norm → 0 ≤ ns_norm → 0 < e_ns →
      e_e5m2 ≤ (1 / 81 : Rat) * k_norm →
      e_e5m2 / (k_norm + ns_norm) <
        (delayedClipDelta (spikeCrossover M 2) M * k_norm + e_ns) / (k_norm + ns_norm)) :=
  Mxfp8Frontier.delayed_scaling_spike_clipping_crossover_exact

theorem fp8_block_scaling_bias_invariance_exact :
    (∀ (s c : Rat) (xs qs : List Rat), c ≠ 0 →
      sqErrList (s / c) xs (qs.map (c * ·)) = sqErrList s xs qs ∧
      1 - sqErrList (s / c) xs (qs.map (c * ·)) / normSqList xs =
        1 - sqErrList s xs qs / normSqList xs) ∧
    (∀ (s : Rat) (b₁ b₂ : Nat) (xs qs : List Rat),
      let c := pow2Rat b₁ / pow2Rat b₂
      sqErrList (s / c) xs (qs.map (c * ·)) = sqErrList s xs qs) ∧
    (∀ (Y : Rat) (M : Nat),
      underflowCap Y M = 4 * underflowCap Y (M + 1) ∧
      underflowCap Y M = (Y * Y) / ((4 ^ M : Nat) : Rat)) ∧
    (underflowCap 458752 0 = 210453397504 ∧
     underflowCap 458752 1 = 52613349376 ∧
     underflowCap 458752 2 = 13153337344) :=
  Mxfp8Frontier.fp8_block_scaling_bias_invariance_exact

end Mxfp8FrontierChallenge
