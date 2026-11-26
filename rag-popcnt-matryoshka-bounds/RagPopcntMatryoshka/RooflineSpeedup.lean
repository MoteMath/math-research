/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RagPopcntMatryoshka.RatOrder

/-!
# Theorem 6: Exact RAG Memory-Footprint & Bandwidth-Roofline Speedup Laws

Proves:
1. Universal exact VRAM compression ratios for all `N > 0, D > 0`:
   `16×` (`1-Bit`) and `8×` (`2-Bit`) vs `FP16`; `32×` (`1-Bit`) and `16×` (`2-Bit`) vs `FP32`.
2. Exact concrete `1M × 1536` (`N = 2^20 = 1,048,576, D = 1536`) MiB footprints:
   `192 MiB` (`1-Bit`), `384 MiB` (`2-Bit`), `768 MiB` (`INT4`), `1536 MiB` (`INT8`),
   `3072 MiB` (`FP16`), `6144 MiB` (`FP32`).
3. Universal exact 2-stage byte-transfer ratios:
   `(N·(D/8) + MK·(D/2)) / (2·N·D) = 1/16 + MK/(4N)` (`1-Bit + INT4`) and
   `(N·(D/4) + MK·(D/2)) / (2·N·D) = 1/8 + MK/(4N)` (`2-Bit + INT4`).
4. Exact bandwidth-roofline speedup certification `> 12×` whenever `12 · MK < N`
   (and concrete `> 15.9× > 12×` at `MK = 160, N = 1,000,000` and `N = 1,048,576`).
-/

namespace RagPopcntMatryoshka

theorem vram_compression_ratios {N D : Rat} (hN : (0 : Rat) < N) (hD : (0 : Rat) < D) :
    bytesFP16 N D / bytes1Bit N D = 16 ∧
    bytesFP16 N D / bytes2Bit N D = 8 ∧
    bytesFP32 N D / bytes1Bit N D = 32 ∧
    bytesFP32 N D / bytes2Bit N D = 16 := by
  have hND : (0 : Rat) < N * D := rat_mul_pos hN hD
  have hNDne : N * D ≠ 0 := Rat.ne_of_gt hND
  have h1ne : N * D / 8 ≠ 0 := Rat.ne_of_gt (rat_div_pos hND (by decide : (0 : Rat) < 8))
  have h2ne : N * D / 4 ≠ 0 := Rat.ne_of_gt (rat_div_pos hND (by decide : (0 : Rat) < 4))
  unfold bytesFP16 bytesFP32 bytes1Bit bytes2Bit
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply rat_mul_right_cancel (c := N * D / 8) h1ne
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ h1ne, Rat.mul_one]
    rw [Rat.div_def]; grind
  · apply rat_mul_right_cancel (c := N * D / 4) h2ne
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ h2ne, Rat.mul_one]
    rw [Rat.div_def]; grind
  · apply rat_mul_right_cancel (c := N * D / 8) h1ne
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ h1ne, Rat.mul_one]
    rw [Rat.div_def]; grind
  · apply rat_mul_right_cancel (c := N * D / 4) h2ne
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ h2ne, Rat.mul_one]
    rw [Rat.div_def]; grind

theorem twoStage1Bit_transfer_ratio {N D MK : Rat} (hN : (0 : Rat) < N) (hD : (0 : Rat) < D) :
    twoStage1BitBytes N D MK / bytesFP16 N D = 1 / 16 + MK / (4 * N) := by
  have hND : (0 : Rat) < 2 * N * D :=
    rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 2) hN) hD
  have hNDne : 2 * N * D ≠ 0 := Rat.ne_of_gt hND
  have h4Nne : 4 * N ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide : (0 : Rat) < 4) hN)
  unfold twoStage1BitBytes bytesFP16
  apply rat_mul_right_cancel (c := 2 * N * D) hNDne
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hNDne, Rat.mul_one]
  rw [Rat.add_mul, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hcancel : (4 * N)⁻¹ * (2 * N * D) = D * ((4 * N)⁻¹ * (4 * N)) * (2 : Rat)⁻¹ := by
    have h4 : (2 : Rat) * N * D = D * (4 * N) * (2 : Rat)⁻¹ := by grind
    rw [h4]; grind
  have hinv : (4 * N)⁻¹ * (4 * N) = 1 := Rat.inv_mul_cancel _ h4Nne
  have hterm : MK * (4 * N)⁻¹ * (2 * N * D) = MK * (D * (2 : Rat)⁻¹) := by
    have eq1 : MK * (4 * N)⁻¹ * (2 * N * D) = MK * ((4 * N)⁻¹ * (2 * N * D)) := by grind
    rw [eq1, hcancel, hinv, Rat.mul_one]
  rw [hterm]
  grind

theorem twoStage2Bit_transfer_ratio {N D MK : Rat} (hN : (0 : Rat) < N) (hD : (0 : Rat) < D) :
    twoStage2BitBytes N D MK / bytesFP16 N D = 1 / 8 + MK / (4 * N) := by
  have hND : (0 : Rat) < 2 * N * D :=
    rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 2) hN) hD
  have hNDne : 2 * N * D ≠ 0 := Rat.ne_of_gt hND
  have h4Nne : 4 * N ≠ 0 := Rat.ne_of_gt (rat_mul_pos (by decide : (0 : Rat) < 4) hN)
  unfold twoStage2BitBytes bytesFP16
  apply rat_mul_right_cancel (c := 2 * N * D) hNDne
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hNDne, Rat.mul_one]
  rw [Rat.add_mul, Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hcancel : (4 * N)⁻¹ * (2 * N * D) = D * ((4 * N)⁻¹ * (4 * N)) * (2 : Rat)⁻¹ := by
    have h4 : (2 : Rat) * N * D = D * (4 * N) * (2 : Rat)⁻¹ := by grind
    rw [h4]; grind
  have hinv : (4 * N)⁻¹ * (4 * N) = 1 := Rat.inv_mul_cancel _ h4Nne
  have hterm : MK * (4 * N)⁻¹ * (2 * N * D) = MK * (D * (2 : Rat)⁻¹) := by
    have eq1 : MK * (4 * N)⁻¹ * (2 * N * D) = MK * ((4 * N)⁻¹ * (2 * N * D)) := by grind
    rw [eq1, hcancel, hinv, Rat.mul_one]
  rw [hterm]
  grind

theorem roofline_speedup_gt_twelve {N D MK : Rat}
    (hN : (0 : Rat) < N) (hD : (0 : Rat) < D) (hMK : (0 : Rat) ≤ MK)
    (hbound : 12 * MK < N) :
    (12 : Rat) < bytesFP16 N D / twoStage1BitBytes N D MK := by
  have htsPos : (0 : Rat) < twoStage1BitBytes N D MK := by
    unfold twoStage1BitBytes
    have h1 : (0 : Rat) < N * (D / 8) := rat_mul_pos hN (rat_div_pos hD (by decide : (0 : Rat) < 8))
    have h2 : (0 : Rat) ≤ MK * (D / 2) :=
      Rat.mul_nonneg hMK (Rat.le_of_lt (rat_div_pos hD (by decide : (0 : Rat) < 2)))
    exact rat_add_pos_of_pos_of_nonneg h1 h2
  rw [rat_lt_div_iff htsPos]
  unfold twoStage1BitBytes bytesFP16
  apply rat_lt_of_sub_pos
  have eq : 2 * N * D - 12 * (N * (D / 8) + MK * (D / 2)) = (N - 12 * MK) * (D / 2) := by
    rw [Rat.div_def, Rat.div_def]; grind
  rw [eq]
  exact rat_mul_pos (rat_sub_pos hbound) (rat_div_pos hD (by decide : (0 : Rat) < 2))

/-- Headline Theorem 6 (`rag_memory_and_bandwidth_speedup_roofline_exact`). -/
theorem rag_memory_and_bandwidth_speedup_roofline_exact :
    (∀ N D : Rat, (0 : Rat) < N → (0 : Rat) < D →
      bytesFP16 N D / bytes1Bit N D = 16 ∧
      bytesFP16 N D / bytes2Bit N D = 8 ∧
      bytesFP32 N D / bytes1Bit N D = 32 ∧
      bytesFP32 N D / bytes2Bit N D = 16) ∧
    (bytes1Bit (1048576 : Rat) 1536 / 1048576 = 192 ∧
     bytes2Bit (1048576 : Rat) 1536 / 1048576 = 384 ∧
     bytesInt4 (1048576 : Rat) 1536 / 1048576 = 768 ∧
     bytesInt8 (1048576 : Rat) 1536 / 1048576 = 1536 ∧
     bytesFP16 (1048576 : Rat) 1536 / 1048576 = 3072 ∧
     bytesFP32 (1048576 : Rat) 1536 / 1048576 = 6144) ∧
    (∀ N D MK : Rat, (0 : Rat) < N → (0 : Rat) < D →
      twoStage1BitBytes N D MK / bytesFP16 N D = 1 / 16 + MK / (4 * N) ∧
      twoStage2BitBytes N D MK / bytesFP16 N D = 1 / 8 + MK / (4 * N)) ∧
    (∀ N D MK : Rat, (0 : Rat) < N → (0 : Rat) < D → (0 : Rat) ≤ MK → 12 * MK < N →
      (12 : Rat) < bytesFP16 N D / twoStage1BitBytes N D MK) ∧
    ((12 : Rat) < bytesFP16 (1000000 : Rat) 1536 / twoStage1BitBytes 1000000 1536 160 ∧
     (159 / 10 : Rat) < bytesFP16 (1000000 : Rat) 1536 / twoStage1BitBytes 1000000 1536 160 ∧
     (12 : Rat) < bytesFP16 (1048576 : Rat) 1536 / twoStage1BitBytes 1048576 1536 160) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N D hN hD; exact vram_compression_ratios hN hD
  · unfold bytes1Bit bytes2Bit bytesInt4 bytesInt8 bytesFP16 bytesFP32
    grind
  · intro N D MK hN hD
    exact ⟨twoStage1Bit_transfer_ratio hN hD, twoStage2Bit_transfer_ratio hN hD⟩
  · intro N D MK hN hD hMK hbound
    exact roofline_speedup_gt_twelve hN hD hMK hbound
  · refine ⟨roofline_speedup_gt_twelve (by grind) (by grind) (by grind) (by grind), ?_,
      roofline_speedup_gt_twelve (by grind) (by grind) (by grind) (by grind)⟩
    rw [rat_lt_div_iff (by unfold twoStage1BitBytes; grind)]
    unfold bytesFP16 twoStage1BitBytes
    grind

end RagPopcntMatryoshka
