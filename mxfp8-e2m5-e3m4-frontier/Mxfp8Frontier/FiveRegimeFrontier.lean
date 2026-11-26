/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp8Frontier.E4M3vsE5M2

/-!
# Theorems 3 & 4: Complete Five-Regime `E_a M_b` Microscaling Frontiers (E8M0 & Continuous FP32)

Proves the exact global all-`B` (`∀ B ≥ 1`) optimality phase diagrams across all five distinct
8-bit microscaling formats (`INT8`, `E2M5_FN`, `E3M4_FN`, `E4M3_OCP`, `E5M2_IEEE`):
- **Theorem 3 (`mxfp8_e8m0_complete_five_regime_frontier`):**
  `INT8` (`1..4`) → `E2M5` (`5..47`, covering OCP `B = 32`) → `E3M4` (`48..11,379`, covering
  `B = 64..1024`) → `E4M3_OCP` (`11,380..637,534,210`) → `E5M2_IEEE` (`≥ 637,534,211`).
- **Theorem 4 (`deepseek_fp32_scale_complete_five_regime_frontier`):**
  Tie at `B = 1` → `INT8` (`2..12`) → `E2M5` (`13..230`, covering DeepSeek-V3 `1×128` tile with
  `> 6.77x` lower worst-case MSE than `E4M3_OCP`) → `E3M4` (`231..54,668`, covering DeepSeek-V3
  `128×128 = 16,384` block with `> 3.32x` lower worst-case MSE than `E4M3_OCP`) →
  `E4M3_OCP` (`54,669..2,630,667,467`) → `E5M2_IEEE` (`≥ 2,630,667,468`).
-/

namespace Mxfp8Frontier

/-! ### Part A: Adjacent Pairwise Crossovers under OCP `E8M0` Block Scaling -/

theorem int8_beats_e2m5_e8m0 (B : Nat) (h1 : 1 ≤ B) (h2 : B ≤ 4) :
    alphaE8M0_E2M5 B < alphaE8M0_INT8 B := by
  unfold alphaE8M0_E2M5 alphaE8M0_INT8
  have h249 : B ≤ 249 := by omega
  simp only [h249, ↓reduceIte]
  exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

theorem e2m5_beats_int8_e8m0 (B : Nat) (h1 : 5 ≤ B) :
    alphaE8M0_INT8 B < alphaE8M0_E2M5 B := by
  unfold alphaE8M0_INT8 alphaE8M0_E2M5
  split
  · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
  · split
    · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
    · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

theorem e2m5_beats_e3m4_e8m0 (B : Nat) (h1 : 1 ≤ B) (h2 : B ≤ 47) :
    alphaE8M0_E3M4 B < alphaE8M0_E2M5 B := by
  unfold alphaE8M0_E3M4 alphaE8M0_E2M5
  have h249 : B ≤ 249 := by omega
  have h30721 : B ≤ 30721 := by omega
  simp only [h249, h30721, ↓reduceIte]
  exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

theorem e3m4_beats_e2m5_e8m0 (B : Nat) (h1 : 48 ≤ B) :
    alphaE8M0_E2M5 B < alphaE8M0_E3M4 B := by
  unfold alphaE8M0_E2M5 alphaE8M0_E3M4
  split
  · have h30721 : B ≤ 30721 := by omega
    simp only [h30721, ↓reduceIte]
    exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
  · split
    · have h30721 : B ≤ 30721 := by omega
      simp only [h30721, ↓reduceIte]
      exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
    · split
      · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
      · split
        · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
        · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

theorem e3m4_beats_e4m3_e8m0 (B : Nat) (h1 : 1 ≤ B) (h2 : B ≤ 11379) :
    alphaE8M0_E4M3 B < alphaE8M0_E3M4 B := by
  unfold alphaE8M0_E4M3 alphaE8M0_E3M4
  have h4 : B ≤ 474924269 := by omega
  have h3 : B ≤ 30721 := by omega
  simp only [h4, h3, ↓reduceIte]
  exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

theorem e4m3_beats_e3m4_e8m0 (B : Nat) (h1 : 11380 ≤ B) :
    alphaE8M0_E3M4 B < alphaE8M0_E4M3 B := by
  unfold alphaE8M0_E3M4 alphaE8M0_E4M3
  split
  · have h4 : B ≤ 474924269 := by omega
    simp only [h4, ↓reduceIte]
    exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
  · split
    · have h4 : B ≤ 474924269 := by omega
      simp only [h4, ↓reduceIte]
      exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
    · split
      · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
      · split
        · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
        · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

/-- Headline Theorem 3 (`mxfp8_e8m0_complete_five_regime_frontier`). -/
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
    ((1 - alphaE8M0_E3M4 128) * (365 / 100 : Rat) < 1 - alphaE8M0_E4M3 128) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B h1 h2
    have h01 := int8_beats_e2m5_e8m0 B h1 h2
    have h12 := e2m5_beats_e3m4_e8m0 B h1 (by omega)
    have h23 := e3m4_beats_e4m3_e8m0 B h1 (by omega)
    have h34 := e4m3_beats_e5m2_e8m0 B h1 (by omega)
    exact ⟨h01, rat_lt_trans h12 h01,
           rat_lt_trans h23 (rat_lt_trans h12 h01),
           rat_lt_trans h34 (rat_lt_trans h23 (rat_lt_trans h12 h01))⟩
  · intro B h1 h2
    have h10 := e2m5_beats_int8_e8m0 B h1
    have h12 := e2m5_beats_e3m4_e8m0 B (by omega) h2
    have h23 := e3m4_beats_e4m3_e8m0 B (by omega) (by omega)
    have h34 := e4m3_beats_e5m2_e8m0 B (by omega) (by omega)
    exact ⟨h10, h12, rat_lt_trans h23 h12, rat_lt_trans h34 (rat_lt_trans h23 h12)⟩
  · intro B h1 h2
    have h10 := e2m5_beats_int8_e8m0 B (by omega)
    have h21 := e3m4_beats_e2m5_e8m0 B h1
    have h23 := e3m4_beats_e4m3_e8m0 B (by omega) h2
    have h34 := e4m3_beats_e5m2_e8m0 B (by omega) (by omega)
    exact ⟨rat_lt_trans h10 h21, h21, h23, rat_lt_trans h34 h23⟩
  · intro B h1 h2
    have h10 := e2m5_beats_int8_e8m0 B (by omega)
    have h21 := e3m4_beats_e2m5_e8m0 B (by omega)
    have h32 := e4m3_beats_e3m4_e8m0 B h1
    have h34 := e4m3_beats_e5m2_e8m0 B (by omega) h2
    exact ⟨rat_lt_trans h10 (rat_lt_trans h21 h32),
           rat_lt_trans h21 h32, h32, h34⟩
  · intro B h1
    have h10 := e2m5_beats_int8_e8m0 B (by omega)
    have h21 := e3m4_beats_e2m5_e8m0 B (by omega)
    have h32 := e4m3_beats_e3m4_e8m0 B (by omega)
    have h43 := e5m2_beats_e4m3_e8m0 B h1
    exact ⟨rat_lt_trans h10 (rat_lt_trans h21 (rat_lt_trans h32 h43)),
           rat_lt_trans h21 (rat_lt_trans h32 h43),
           rat_lt_trans h32 h43, h43⟩
  · unfold alphaE8M0_E3M4 alphaE8M0_E4M3
    simp only [Nat.reduceLeDiff, ↓reduceIte]
    exact one_sub_linFrac_mul_lt (p := 365) (q := 100) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### Part B: Adjacent Pairwise Crossovers under Continuous FP32 (`DeepSeek-V3`) Scaling -/

theorem int8_beats_e2m5_cont (B : Nat) (h1 : 2 ≤ B) (h2 : B ≤ 12) :
    alphaCont_E2M5 B < alphaCont_INT8 B := by
  unfold alphaCont_E2M5 alphaCont_INT8
  have h57 : B ≤ 57 := by omega
  simp only [h57, ↓reduceIte]
  apply linFrac_lt_of_nat (by omega) (by omega)
  have hL : (4224 * B + 11652) * (1 * B + 64515) =
      4224 * (B * B) + 272523012 * B + 751728780 := by grind
  have hR : (0 * B + 64516) * (4225 * B + 11651) =
      0 * (B * B) + 272580100 * B + 751675916 := by grind
  rw [hL, hR]
  exact nat_quad_lt_of_secant (lo := 2) (hi := 12) h1 h2 (by omega) (by omega)

theorem e2m5_beats_int8_cont (B : Nat) (h1 : 13 ≤ B) :
    alphaCont_INT8 B < alphaCont_E2M5 B := by
  unfold alphaCont_INT8 alphaCont_E2M5
  split
  · apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (0 * B + 64516) * (4225 * B + 11651) =
        0 * (B * B) + 272580100 * B + 751675916 := by grind
    have hR : (4224 * B + 11652) * (1 * B + 64515) =
        4224 * (B * B) + 272523012 * B + 751728780 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_tangent (lo := 13) h1 (by omega) (by omega)
  · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

theorem e2m5_beats_e3m4_cont (B : Nat) (h1 : 2 ≤ B) (h2 : B ≤ 230) :
    alphaCont_E3M4 B < alphaCont_E2M5 B := by
  unfold alphaCont_E3M4 alphaCont_E2M5
  have h3 : B ≤ 14468 := by omega
  simp only [h3, ↓reduceIte]
  split
  · -- 2 ≤ B ≤ 57
    apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (1088 * B + 2756) * (4225 * B + 11651) =
        4596800 * (B * B) + 24320388 * B + 32110156 := by grind
    have hR : (4224 * B + 11652) * (1089 * B + 2755) =
        4599936 * (B * B) + 24326148 * B + 32101260 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_tangent (lo := 2) h1 (by omega) (by omega)
  · -- 58 ≤ B ≤ 230
    rename_i hgt
    have hlo : 58 ≤ B := by omega
    apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (1088 * B + 2756) * (1 * B + 254015) =
        1088 * (B * B) + 276371076 * B + 700065340 := by grind
    have hR : (0 * B + 254016) * (1089 * B + 2755) =
        0 * (B * B) + 276623424 * B + 699814080 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_secant (lo := 58) (hi := 230) hlo h2 (by omega) (by omega)

theorem e3m4_beats_e2m5_cont (B : Nat) (h1 : 231 ≤ B) :
    alphaCont_E2M5 B < alphaCont_E3M4 B := by
  unfold alphaCont_E2M5 alphaCont_E3M4
  have h2 : ¬ B ≤ 57 := by omega
  simp only [h2, ↓reduceIte]
  split
  · -- 231 ≤ B ≤ 14468
    apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (0 * B + 254016) * (1089 * B + 2755) =
        0 * (B * B) + 276623424 * B + 699814080 := by grind
    have hR : (1088 * B + 2756) * (1 * B + 254015) =
        1088 * (B * B) + 276371076 * B + 700065340 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_tangent (lo := 231) h1 (by omega) (by omega)
  · -- B ≥ 14469
    exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

theorem e3m4_beats_e4m3_cont (B : Nat) (h1 : 2 ≤ B) (h2 : B ≤ 54668) :
    alphaCont_E4M3 B < alphaCont_E3M4 B := by
  unfold alphaCont_E4M3 alphaCont_E3M4
  have h4 : B ≤ 730740961 := by omega
  simp only [h4, ↓reduceIte]
  split
  · -- 2 ≤ B ≤ 14468
    apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (288 * B + 496) * (1089 * B + 2755) =
        313632 * (B * B) + 1333584 * B + 1366480 := by grind
    have hR : (1088 * B + 2756) * (289 * B + 495) =
        314432 * (B * B) + 1335044 * B + 1364220 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_tangent (lo := 2) h1 (by omega) (by omega)
  · -- 14469 ≤ B ≤ 54668
    rename_i hgt
    have hlo : 14469 ≤ B := by omega
    apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (288 * B + 496) * (1 * B + 15745023) =
        288 * (B * B) + 4534567120 * B + 7809531408 := by grind
    have hR : (0 * B + 15745024) * (289 * B + 495) =
        0 * (B * B) + 4550311936 * B + 7793786880 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_secant (lo := 14469) (hi := 54668) hlo h2 (by omega) (by omega)

theorem e4m3_beats_e3m4_cont (B : Nat) (h1 : 54669 ≤ B) :
    alphaCont_E3M4 B < alphaCont_E4M3 B := by
  unfold alphaCont_E3M4 alphaCont_E4M3
  have h3 : ¬ B ≤ 14468 := by omega
  simp only [h3, ↓reduceIte]
  split
  · -- 54669 ≤ B ≤ 730740961
    apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (0 * B + 15745024) * (289 * B + 495) =
        0 * (B * B) + 4550311936 * B + 7793786880 := by grind
    have hR : (288 * B + 496) * (1 * B + 15745023) =
        288 * (B * B) + 4534567120 * B + 7809531408 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_tangent (lo := 54669) h1 (by omega) (by omega)
  · -- B ≥ 730740962
    exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

/-- Headline Theorem 4 (`deepseek_fp32_scale_complete_five_regime_frontier`). -/
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
     ((1 - alphaCont_E3M4 16384) * (332 / 100 : Rat) < 1 - alphaCont_E4M3 16384)) := by
  refine ⟨⟨by unfold alphaCont_INT8; exact linFrac_eq_one (by decide) (by decide),
           by unfold alphaCont_E2M5; simp only [Nat.reduceLeDiff, ↓reduceIte]; exact linFrac_eq_one (by decide) (by decide),
           by unfold alphaCont_E3M4; simp only [Nat.reduceLeDiff, ↓reduceIte]; exact linFrac_eq_one (by decide) (by decide),
           by unfold alphaCont_E4M3; simp only [Nat.reduceLeDiff, ↓reduceIte]; exact linFrac_eq_one (by decide) (by decide),
           by unfold alphaCont_E5M2; simp only [Nat.reduceLeDiff, ↓reduceIte]; exact linFrac_eq_one (by decide) (by decide)⟩,
          ?_, ?_, ?_, ?_, ?_,
          ⟨by unfold alphaCont_E2M5 alphaCont_E4M3; simp only [Nat.reduceLeDiff, ↓reduceIte]; exact one_sub_linFrac_mul_lt (p := 677) (q := 100) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
           by unfold alphaCont_E3M4 alphaCont_E4M3; simp only [Nat.reduceLeDiff, ↓reduceIte]; exact one_sub_linFrac_mul_lt (p := 332) (q := 100) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩⟩
  · intro B h1 h2
    have h01 := int8_beats_e2m5_cont B h1 h2
    have h12 := e2m5_beats_e3m4_cont B h1 (by omega)
    have h23 := e3m4_beats_e4m3_cont B h1 (by omega)
    have h34 := e4m3_beats_e5m2_cont B h1 (by omega)
    exact ⟨h01, rat_lt_trans h12 h01,
           rat_lt_trans h23 (rat_lt_trans h12 h01),
           rat_lt_trans h34 (rat_lt_trans h23 (rat_lt_trans h12 h01))⟩
  · intro B h1 h2
    have h10 := e2m5_beats_int8_cont B h1
    have h12 := e2m5_beats_e3m4_cont B (by omega) h2
    have h23 := e3m4_beats_e4m3_cont B (by omega) (by omega)
    have h34 := e4m3_beats_e5m2_cont B (by omega) (by omega)
    exact ⟨h10, h12, rat_lt_trans h23 h12, rat_lt_trans h34 (rat_lt_trans h23 h12)⟩
  · intro B h1 h2
    have h10 := e2m5_beats_int8_cont B (by omega)
    have h21 := e3m4_beats_e2m5_cont B h1
    have h23 := e3m4_beats_e4m3_cont B (by omega) h2
    have h34 := e4m3_beats_e5m2_cont B (by omega) (by omega)
    exact ⟨rat_lt_trans h10 h21, h21, h23, rat_lt_trans h34 h23⟩
  · intro B h1 h2
    have h10 := e2m5_beats_int8_cont B (by omega)
    have h21 := e3m4_beats_e2m5_cont B (by omega)
    have h32 := e4m3_beats_e3m4_cont B h1
    have h34 := e4m3_beats_e5m2_cont B (by omega) h2
    exact ⟨rat_lt_trans h10 (rat_lt_trans h21 h32),
           rat_lt_trans h21 h32, h32, h34⟩
  · intro B h1
    have h10 := e2m5_beats_int8_cont B (by omega)
    have h21 := e3m4_beats_e2m5_cont B (by omega)
    have h32 := e4m3_beats_e3m4_cont B (by omega)
    have h43 := e5m2_beats_e4m3_cont B h1
    exact ⟨rat_lt_trans h10 (rat_lt_trans h21 (rat_lt_trans h32 h43)),
           rat_lt_trans h21 (rat_lt_trans h32 h43),
           rat_lt_trans h32 h43, h43⟩

end Mxfp8Frontier
