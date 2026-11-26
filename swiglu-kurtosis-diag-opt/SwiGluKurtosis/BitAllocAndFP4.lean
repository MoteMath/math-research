/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SwiGluKurtosis.RatOrder

/-!
# Theorems 5 & 6: Asymmetric Bit Allocation Dominance & MXFP4-vs-NVFP4 Underflow Gap

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
5. `gated_ffn_asymmetric_bit_allocation_dominance`
6. `mxfp4_block32_vs_nvfp4_block16_kurtosis_underflow_gap`
-/

namespace SwiGluKurtosis

/-! ### Theorem 5: Asymmetric Gate-Up-Down Bit Allocation Dominance -/

theorem amgm3_cube_sos (x y z : Rat) (hx : (0 : Rat) ≤ x) (hy : (0 : Rat) ≤ y) (hz : (0 : Rat) ≤ z) :
    27 * x * y * z ≤ (x + y + z) * (x + y + z) * (x + y + z) := by
  apply rat_le_of_sub_nonneg
  have hid : (x + y + z) * (x + y + z) * (x + y + z) - 27 * x * y * z =
      (1 / 2 : Rat) * (x + y + z) * (sq (x - y) + sq (y - z) + sq (z - x)) +
      3 * (x * sq (y - z) + y * sq (z - x) + z * sq (x - y)) := by
    unfold sq; grind
  rw [hid]
  have hsum_nn : (0 : Rat) ≤ x + y + z := rat_add_nonneg (rat_add_nonneg hx hy) hz
  have ht1 : (0 : Rat) ≤ (1 / 2 : Rat) * (x + y + z) * (sq (x - y) + sq (y - z) + sq (z - x)) :=
    Rat.mul_nonneg (Rat.mul_nonneg (rat_div_nonneg (by decide) (by decide)) hsum_nn)
      (rat_add_nonneg (rat_add_nonneg (rat_sq_nonneg _) (rat_sq_nonneg _)) (rat_sq_nonneg _))
  have ht2 : (0 : Rat) ≤ 3 * (x * sq (y - z) + y * sq (z - x) + z * sq (x - y)) :=
    Rat.mul_nonneg (by decide)
      (rat_add_nonneg
        (rat_add_nonneg (Rat.mul_nonneg hx (rat_sq_nonneg _)) (Rat.mul_nonneg hy (rat_sq_nonneg _)))
        (Rat.mul_nonneg hz (rat_sq_nonneg _)))
  exact rat_add_nonneg ht1 ht2

theorem bitAllocMSE_amgm3_lower_bound (Sg Su Sd : Rat) (bg bu bd : Nat)
    (hSg : (0 : Rat) ≤ Sg) (hSu : (0 : Rat) ≤ Su) (hSd : (0 : Rat) ≤ Sd) :
    27 * Sg * Su * Sd * invPow2Rat (2 * (bg + bu + bd)) ≤
      bitAllocMSE Sg Su Sd bg bu bd * bitAllocMSE Sg Su Sd bg bu bd * bitAllocMSE Sg Su Sd bg bu bd := by
  unfold bitAllocMSE
  have h1 := amgm3_cube_sos
    (Sg * invPow2Rat (2 * bg))
    (Su * invPow2Rat (2 * bu))
    (Sd * invPow2Rat (2 * bd))
    (Rat.mul_nonneg hSg (Rat.le_of_lt (invPow2Rat_pos _)))
    (Rat.mul_nonneg hSu (Rat.le_of_lt (invPow2Rat_pos _)))
    (Rat.mul_nonneg hSd (Rat.le_of_lt (invPow2Rat_pos _)))
  have hpow : invPow2Rat (2 * (bg + bu + bd)) =
      invPow2Rat (2 * bg) * invPow2Rat (2 * bu) * invPow2Rat (2 * bd) := by
    have hnat : 2 * (bg + bu + bd) = 2 * bg + 2 * bu + 2 * bd := by omega
    rw [hnat, invPow2Rat_add, invPow2Rat_add]
  have heq : 27 * (Sg * invPow2Rat (2 * bg)) * (Su * invPow2Rat (2 * bu)) * (Sd * invPow2Rat (2 * bd)) =
      27 * Sg * Su * Sd * invPow2Rat (2 * (bg + bu + bd)) := by
    rw [hpow]; grind
  rw [heq] at h1
  exact h1

theorem invPow2Rat_step2 (b : Nat) :
    invPow2Rat (2 * b) = 4 * invPow2Rat (2 * (b + 1)) := by
  have hnat : 2 * (b + 1) = 2 * b + 2 := by omega
  rw [hnat, invPow2Rat_add]
  have h2 : invPow2Rat 2 = 1 / 4 := by simp [invPow2Rat, pow2Rat]
  rw [h2]; grind

theorem bitAllocMSE_up_bump_diff (Sg Su Sd : Rat) (b : Nat) (hb : 1 ≤ b) :
    bitAllocMSE Sg Su Sd b b b - bitAllocMSE Sg Su Sd b (b + 1) (b - 1) =
      3 * invPow2Rat (2 * (b + 1)) * (Su - 4 * Sd) := by
  unfold bitAllocMSE
  have hb_eq : b = (b - 1) + 1 := by omega
  have h_b : invPow2Rat (2 * b) = 4 * invPow2Rat (2 * (b + 1)) := invPow2Rat_step2 b
  have h_bm1 : invPow2Rat (2 * (b - 1)) = 16 * invPow2Rat (2 * (b + 1)) := by
    have h1 : invPow2Rat (2 * (b - 1)) = 4 * invPow2Rat (2 * ((b - 1) + 1)) :=
      invPow2Rat_step2 (b - 1)
    rw [← hb_eq] at h1
    rw [h1, h_b]
    grind
  rw [h_b, h_bm1]
  grind

theorem bitAllocMSE_gate_bump_diff (Sg Su Sd : Rat) (b : Nat) (hb : 1 ≤ b) :
    bitAllocMSE Sg Su Sd b b b - bitAllocMSE Sg Su Sd (b + 1) b (b - 1) =
      3 * invPow2Rat (2 * (b + 1)) * (Sg - 4 * Sd) := by
  unfold bitAllocMSE
  have hb_eq : b = (b - 1) + 1 := by omega
  have h_b : invPow2Rat (2 * b) = 4 * invPow2Rat (2 * (b + 1)) := invPow2Rat_step2 b
  have h_bm1 : invPow2Rat (2 * (b - 1)) = 16 * invPow2Rat (2 * (b + 1)) := by
    have h1 : invPow2Rat (2 * (b - 1)) = 4 * invPow2Rat (2 * ((b - 1) + 1)) :=
      invPow2Rat_step2 (b - 1)
    rw [← hb_eq] at h1
    rw [h1, h_b]
    grind
  rw [h_b, h_bm1]
  grind

theorem bitAllocMSE_gate_vs_up_swap_diff (Sg Su Sd : Rat) (b : Nat) (hb : 1 ≤ b) :
    bitAllocMSE Sg Su Sd (b - 1) (b + 1) b - bitAllocMSE Sg Su Sd (b + 1) (b - 1) b =
      15 * invPow2Rat (2 * (b + 1)) * (Sg - Su) := by
  unfold bitAllocMSE
  have hb_eq : b = (b - 1) + 1 := by omega
  have h_b : invPow2Rat (2 * b) = 4 * invPow2Rat (2 * (b + 1)) := invPow2Rat_step2 b
  have h_bm1 : invPow2Rat (2 * (b - 1)) = 16 * invPow2Rat (2 * (b + 1)) := by
    have h1 : invPow2Rat (2 * (b - 1)) = 4 * invPow2Rat (2 * ((b - 1) + 1)) :=
      invPow2Rat_step2 (b - 1)
    rw [← hb_eq] at h1
    rw [h1, h_b]
    grind
  rw [h_b, h_bm1]
  grind

theorem bitAllocMSE_up_bump_iff (Sg Su Sd : Rat) (b : Nat) (hb : 1 ≤ b) :
    bitAllocMSE Sg Su Sd b (b + 1) (b - 1) < bitAllocMSE Sg Su Sd b b b ↔ 4 * Sd < Su := by
  have hc : (0 : Rat) < 3 * invPow2Rat (2 * (b + 1)) :=
    rat_mul_pos (by decide) (invPow2Rat_pos _)
  constructor
  · intro hlt
    have hpos := rat_sub_pos hlt
    rw [bitAllocMSE_up_bump_diff Sg Su Sd b hb] at hpos
    apply rat_lt_of_sub_pos
    apply rat_lt_of_mul_pos_right hc
    have h0 : (0 : Rat) * (3 * invPow2Rat (2 * (b + 1))) = 0 := by grind
    rw [h0, Rat.mul_comm]
    exact hpos
  · intro hgt
    apply rat_lt_of_sub_pos
    rw [bitAllocMSE_up_bump_diff Sg Su Sd b hb]
    exact rat_mul_pos hc (rat_sub_pos hgt)

theorem bitAllocMSE_gate_bump_iff (Sg Su Sd : Rat) (b : Nat) (hb : 1 ≤ b) :
    bitAllocMSE Sg Su Sd (b + 1) b (b - 1) < bitAllocMSE Sg Su Sd b b b ↔ 4 * Sd < Sg := by
  have hc : (0 : Rat) < 3 * invPow2Rat (2 * (b + 1)) :=
    rat_mul_pos (by decide) (invPow2Rat_pos _)
  constructor
  · intro hlt
    have hpos := rat_sub_pos hlt
    rw [bitAllocMSE_gate_bump_diff Sg Su Sd b hb] at hpos
    apply rat_lt_of_sub_pos
    apply rat_lt_of_mul_pos_right hc
    have h0 : (0 : Rat) * (3 * invPow2Rat (2 * (b + 1))) = 0 := by grind
    rw [h0, Rat.mul_comm]
    exact hpos
  · intro hgt
    apply rat_lt_of_sub_pos
    rw [bitAllocMSE_gate_bump_diff Sg Su Sd b hb]
    exact rat_mul_pos hc (rat_sub_pos hgt)

theorem bitAllocMSE_gate_vs_up_swap_iff (Sg Su Sd : Rat) (b : Nat) (hb : 1 ≤ b) :
    bitAllocMSE Sg Su Sd (b + 1) (b - 1) b < bitAllocMSE Sg Su Sd (b - 1) (b + 1) b ↔ Su < Sg := by
  have hc : (0 : Rat) < 15 * invPow2Rat (2 * (b + 1)) :=
    rat_mul_pos (by decide) (invPow2Rat_pos _)
  constructor
  · intro hlt
    have hpos := rat_sub_pos hlt
    rw [bitAllocMSE_gate_vs_up_swap_diff Sg Su Sd b hb] at hpos
    apply rat_lt_of_sub_pos
    apply rat_lt_of_mul_pos_right hc
    have h0 : (0 : Rat) * (15 * invPow2Rat (2 * (b + 1))) = 0 := by grind
    rw [h0, Rat.mul_comm]
    exact hpos
  · intro hgt
    apply rat_lt_of_sub_pos
    rw [bitAllocMSE_gate_vs_up_swap_diff Sg Su Sd b hb]
    exact rat_mul_pos hc (rat_sub_pos hgt)

/-- Headline Theorem 5 (`gated_ffn_asymmetric_bit_allocation_dominance`). -/
theorem gated_ffn_asymmetric_bit_allocation_dominance :
    (∀ (Sg Su Sd : Rat) (bg bu bd : Nat), (0 : Rat) ≤ Sg → (0 : Rat) ≤ Su → (0 : Rat) ≤ Sd →
      27 * Sg * Su * Sd * invPow2Rat (2 * (bg + bu + bd)) ≤
        bitAllocMSE Sg Su Sd bg bu bd * bitAllocMSE Sg Su Sd bg bu bd * bitAllocMSE Sg Su Sd bg bu bd) ∧
    (∀ (Sg Su Sd : Rat) (b : Nat), 1 ≤ b →
      (bitAllocMSE Sg Su Sd b (b + 1) (b - 1) < bitAllocMSE Sg Su Sd b b b ↔ 4 * Sd < Su) ∧
      (bitAllocMSE Sg Su Sd (b + 1) b (b - 1) < bitAllocMSE Sg Su Sd b b b ↔ 4 * Sd < Sg) ∧
      (bitAllocMSE Sg Su Sd (b + 1) (b - 1) b < bitAllocMSE Sg Su Sd (b - 1) (b + 1) b ↔ Su < Sg)) ∧
    (∀ (Sg Su Sd : Rat),
      (bitAllocMSE Sg Su Sd 4 5 3 < bitAllocMSE Sg Su Sd 4 4 4 ↔ 4 * Sd < Su) ∧
      (bitAllocMSE Sg Su Sd 5 4 3 < bitAllocMSE Sg Su Sd 4 4 4 ↔ 4 * Sd < Sg) ∧
      (bitAllocMSE Sg Su Sd 5 3 4 < bitAllocMSE Sg Su Sd 3 5 4 ↔ Su < Sg)) ∧
    (bitAllocMSE 3 1 1 5 3 4 < bitAllocMSE 3 1 1 3 5 4 ∧
     bitAllocMSE 1 5 1 4 5 3 < bitAllocMSE 1 5 1 4 4 4 ∧
     bitAllocMSE 5 1 1 5 4 3 < bitAllocMSE 5 1 1 4 4 4) := by
  refine ⟨bitAllocMSE_amgm3_lower_bound, ?_, ?_, ?_⟩
  · intro Sg Su Sd b hb
    exact ⟨bitAllocMSE_up_bump_iff Sg Su Sd b hb,
           bitAllocMSE_gate_bump_iff Sg Su Sd b hb,
           bitAllocMSE_gate_vs_up_swap_iff Sg Su Sd b hb⟩
  · intro Sg Su Sd
    exact ⟨bitAllocMSE_up_bump_iff Sg Su Sd 4 (by decide),
           bitAllocMSE_gate_bump_iff Sg Su Sd 4 (by decide),
           bitAllocMSE_gate_vs_up_swap_iff Sg Su Sd 4 (by decide)⟩
  · have h415 : (4 : Rat) * 1 < 5 := by
      apply rat_lt_of_sub_pos
      have h : (5 : Rat) - 4 * 1 = 1 := by grind
      rw [h]; decide
    refine ⟨(bitAllocMSE_gate_vs_up_swap_iff 3 1 1 4 (by decide)).mpr (by decide),
            (bitAllocMSE_up_bump_iff 1 5 1 4 (by decide)).mpr h415,
            (bitAllocMSE_gate_bump_iff 5 1 1 4 (by decide)).mpr h415⟩

/-! ### Theorem 6: MXFP4 (`B=32`) vs NVFP4 (`B=16`) Outlier Underflow Gap -/

theorem mxfp4_underflow_below_M_div_24 {s M x : Rat}
    (hvalid : validE2M1Scale s M) (hx : ratAbs x < M / 24) :
    fp4Underflows s x := by
  unfold validE2M1Scale maxE2M1 at hvalid
  unfold fp4Underflows underflowMidE2M1
  have hs_ge : M / 24 ≤ s * (1 / 4) := by
    have h1 := rat_mul_le_mul_of_nonneg_right hvalid.2 (rat_div_nonneg (by decide) (by decide) : (0 : Rat) ≤ 1 / 24)
    have hr : s * 6 * (1 / 24) = s * (1 / 4) := by grind
    have hl2 : M * (1 / 24 : Rat) = M / 24 := by
      apply Eq.symm
      apply (rat_div_eq_iff (by decide : (24 : Rat) ≠ 0)).mpr
      grind
    rw [hl2, hr] at h1
    exact h1
  exact rat_lt_of_lt_of_le hx hs_ge

theorem cleanHalf16_excludes_idx (v : Fin 32 → Rat) (idx : Fin 32) (k : Fin 16) :
    ∃ j : Fin 32, j ≠ idx ∧ cleanHalf16 v idx k = v j := by
  unfold cleanHalf16
  split
  · rename_i hlt
    refine ⟨⟨k.val + 16, Nat.add_lt_add_right k.isLt 16⟩, ?_, rfl⟩
    intro heq
    have hval : k.val + 16 = idx.val := congrArg Fin.val heq
    omega
  · rename_i hge
    refine ⟨⟨k.val, Nat.lt_trans k.isLt (by decide)⟩, ?_, rfl⟩
    intro heq
    have hval : k.val = idx.val := congrArg Fin.val heq
    omega

/-- Headline Theorem 6 (`mxfp4_block32_vs_nvfp4_block16_kurtosis_underflow_gap`). -/
theorem mxfp4_block32_vs_nvfp4_block16_kurtosis_underflow_gap :
    (maxE2M1 = 6 ∧ minSubE2M1 = 1 / 2 ∧ underflowMidE2M1 = 1 / 4 ∧
     maxE2M1 / underflowMidE2M1 = 24) ∧
    (∀ (v : Fin 32 → Rat) (idx : Fin 32) (M m s32 : Rat),
      (0 : Rat) < M → (0 : Rat) < m → m < M / 24 →
      ratAbs (v idx) = M →
      (∀ j : Fin 32, j ≠ idx → m / 12 ≤ ratAbs (v j) ∧ ratAbs (v j) ≤ m) →
      validE2M1Scale s32 M →
      (∀ j : Fin 32, j ≠ idx → fp4Underflows s32 (v j)) ∧
      (let sClean := m / 6
       validE2M1Scale sClean m ∧
       (∀ k : Fin 16, ratAbs (cleanHalf16 v idx k) ≤ m) ∧
       (∀ k : Fin 16, fp4PreservedNonzero sClean (cleanHalf16 v idx k)) ∧
       (∀ k : Fin 16, ¬ fp4Underflows sClean (cleanHalf16 v idx k)))) ∧
    (∀ (M : Rat), (0 : Rat) < M →
      (31 : Nat) + 1 = 32 ∧ (16 : Nat) + 16 = 32 ∧ (15 : Nat) + 16 = 31 ∧
      (16 : Rat) / 32 = 1 / 2) := by
  refine ⟨⟨rfl, rfl, rfl, by simp [maxE2M1, underflowMidE2M1]; grind⟩, ?_, ?_⟩
  · intro v idx M m s32 hM hm hm_lt hidx hbg hs32
    refine ⟨?_, ?_⟩
    · intro j hj
      have hj_le : ratAbs (v j) ≤ m := (hbg j hj).2
      have hj_lt : ratAbs (v j) < M / 24 := rat_lt_of_le_of_lt hj_le hm_lt
      exact mxfp4_underflow_below_M_div_24 hs32 hj_lt
    · dsimp only
      have hsClean_pos : (0 : Rat) < m / 6 := rat_div_pos hm (by decide)
      have hsClean_valid : validE2M1Scale (m / 6) m := by
        refine ⟨hsClean_pos, ?_⟩
        unfold maxE2M1
        rw [rat_div_mul_cancel (by decide : (6 : Rat) ≠ 0)]
        exact Rat.le_refl
      refine ⟨hsClean_valid, ?_, ?_, ?_⟩
      · intro k
        rcases cleanHalf16_excludes_idx v idx k with ⟨j, hj, hjk⟩
        rw [hjk]
        exact (hbg j hj).2
      · intro k
        rcases cleanHalf16_excludes_idx v idx k with ⟨j, hj, hjk⟩
        rw [hjk]
        unfold fp4PreservedNonzero underflowMidE2M1
        have hlo : m / 12 ≤ ratAbs (v j) := (hbg j hj).1
        have h24_le_12 : (m / 6) * (1 / 4 : Rat) ≤ m / 12 := by
          apply rat_le_of_sub_nonneg
          have hsub : m / 12 - (m / 6) * (1 / 4 : Rat) = m / 24 := by
            have h1 : m / 12 = m * (1 / 12) := by
              apply (rat_div_eq_iff (by decide : (12 : Rat) ≠ 0)).mpr; grind
            have h2 : m / 6 = m * (1 / 6) := by
              apply (rat_div_eq_iff (by decide : (6 : Rat) ≠ 0)).mpr; grind
            have h3 : m / 24 = m * (1 / 24) := by
              apply (rat_div_eq_iff (by decide : (24 : Rat) ≠ 0)).mpr; grind
            rw [h1, h2, h3]; grind
          rw [hsub]
          exact Rat.le_of_lt (rat_div_pos hm (by decide))
        exact Rat.le_trans h24_le_12 hlo
      · intro k
        rcases cleanHalf16_excludes_idx v idx k with ⟨j, hj, hjk⟩
        rw [hjk]
        unfold fp4Underflows underflowMidE2M1
        have hlo : m / 12 ≤ ratAbs (v j) := (hbg j hj).1
        have h24_le_12 : (m / 6) * (1 / 4 : Rat) ≤ m / 12 := by
          apply rat_le_of_sub_nonneg
          have hsub : m / 12 - (m / 6) * (1 / 4 : Rat) = m / 24 := by
            have h1 : m / 12 = m * (1 / 12) := by
              apply (rat_div_eq_iff (by decide : (12 : Rat) ≠ 0)).mpr; grind
            have h2 : m / 6 = m * (1 / 6) := by
              apply (rat_div_eq_iff (by decide : (6 : Rat) ≠ 0)).mpr; grind
            have h3 : m / 24 = m * (1 / 24) := by
              apply (rat_div_eq_iff (by decide : (24 : Rat) ≠ 0)).mpr; grind
            rw [h1, h2, h3]; grind
          rw [hsub]
          exact Rat.le_of_lt (rat_div_pos hm (by decide))
        exact Rat.not_lt.mpr (Rat.le_trans h24_le_12 hlo)
  · intro _ _
    exact ⟨rfl, rfl, rfl, by grind⟩

end SwiGluKurtosis
