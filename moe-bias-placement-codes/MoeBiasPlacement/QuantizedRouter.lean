/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MoeBiasPlacement.RatHelpers

/-!
# Frontier 3 Proofs: Exact Quantized-Router Zero-Flip Margin Thresholds

Proves Theorem 6: `quantized_router_zero_flip_thresholds`.
-/

namespace MoeBiasPlacement

private theorem rat_two_mul (x : Rat) : (2 : Rat) * x = x + x := by
  have h2 : (2 : Rat) = 1 + 1 := by exact Rat.natCast_add 1 1
  rw [h2, Rat.add_mul, Rat.one_mul]

private theorem rat_ratio_eq_nat (n : Nat) (hn : 1 < n) (p q : Nat)
    (hp : n + 1 = p) (hq : n - 1 = q) :
    ((n : Rat) + 1) / ((n : Rat) - 1) = (p : Rat) / (q : Rat) := by
  have hnum : (n : Rat) + 1 = (p : Rat) := by
    rw [← hp, rat_natCast_add]; simp
  have hden : (n : Rat) - 1 = (q : Rat) := by
    have hq1 : q + 1 = n := by omega
    have h1 : (n : Rat) = (q : Rat) + 1 := by
      rw [← hq1, rat_natCast_add]; simp
    rw [h1, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
  rw [hnum, hden]

theorem quantized_router_zero_flip_thresholds :
    (∀ z_k z_j z'_k z'_j ε : Rat,
      (z'_k - z_k).abs ≤ ε → (z'_j - z_j).abs ≤ ε → z_k - z_j > 2 * ε → z'_k > z'_j) ∧
    (∀ z_k z_j ε : Rat,
      0 ≤ ε → z_k - z_j = 2 * ε →
      ∃ z'_k z'_j : Rat, (z'_k - z_k).abs ≤ ε ∧ (z'_j - z_j).abs ≤ ε ∧ z'_k = z'_j) ∧
    (∀ (m : Nat) (z_k z_j z'_k z'_j : Rat),
      let u : Rat := 1 / ((2 ^ (m + 1) : Nat) : Rat)
      0 < z_j → z_j < z_k →
      (z'_k - z_k).abs ≤ u * z_k.abs →
      (z'_j - z_j).abs ≤ u * z_j.abs →
      z_k * (((2 ^ (m + 1) : Nat) : Rat) - 1) > z_j * (((2 ^ (m + 1) : Nat) : Rat) + 1) →
      z'_k > z'_j) ∧
    (∀ (m : Nat) (z_k z_j : Rat),
      let u : Rat := 1 / ((2 ^ (m + 1) : Nat) : Rat)
      0 < z_j →
      z_k * (((2 ^ (m + 1) : Nat) : Rat) - 1) = z_j * (((2 ^ (m + 1) : Nat) : Rat) + 1) →
      ∃ z'_k z'_j : Rat,
        (z'_k - z_k).abs ≤ u * z_k.abs ∧
        (z'_j - z_j).abs ≤ u * z_j.abs ∧
        z'_k = z'_j) ∧
    ((((2 ^ (1 + 1) : Nat) : Rat) + 1) / (((2 ^ (1 + 1) : Nat) : Rat) - 1) = 5 / 3 ∧
     (((2 ^ (2 + 1) : Nat) : Rat) + 1) / (((2 ^ (2 + 1) : Nat) : Rat) - 1) = 9 / 7 ∧
     (((2 ^ (3 + 1) : Nat) : Rat) + 1) / (((2 ^ (3 + 1) : Nat) : Rat) - 1) = 17 / 15 ∧
     (((2 ^ (7 + 1) : Nat) : Rat) + 1) / (((2 ^ (7 + 1) : Nat) : Rat) - 1) = 257 / 255 ∧
     (((2 ^ (10 + 1) : Nat) : Rat) + 1) / (((2 ^ (10 + 1) : Nat) : Rat) - 1) = 2049 / 2047) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Part 1: Uniform quantization sufficiency
    intro z_k z_j z'_k z'_j ε hk hj hgap
    have hk1 : z_k - ε ≤ z'_k := by
      have h := ((rat_abs_le_iff (z'_k - z_k) ε).mp hk).1
      have h1 := (Rat.add_le_add_right (c := z_k)).mpr h
      simpa [Rat.sub_eq_add_neg, Rat.add_comm (-ε) z_k, Rat.add_assoc,
             Rat.neg_add_cancel, Rat.add_zero] using h1
    have hj1 : z'_j ≤ z_j + ε := by
      have h := ((rat_abs_le_iff (z'_j - z_j) ε).mp hj).2
      have h1 := (Rat.add_le_add_right (c := z_j)).mpr h
      simpa [Rat.sub_eq_add_neg, Rat.add_comm ε z_j, Rat.add_assoc,
             Rat.neg_add_cancel, Rat.add_zero] using h1
    have hmid : z_j + ε < z_k - ε := by
      have h1 := (Rat.add_lt_add_right (c := z_j - ε)).mpr hgap
      have hl : 2 * ε + (z_j - ε) = z_j + ε := by
        rw [rat_two_mul, Rat.sub_eq_add_neg, Rat.add_comm (ε + ε) (z_j + -ε),
            Rat.add_assoc z_j (-ε), ← Rat.add_assoc (-ε) ε ε,
            Rat.neg_add_cancel, Rat.zero_add]
      have hr : (z_k - z_j) + (z_j - ε) = z_k - ε := by
        simp only [Rat.sub_eq_add_neg, Rat.add_assoc]
        rw [← Rat.add_assoc (-z_j) z_j, Rat.neg_add_cancel, Rat.zero_add]
      rw [hl, hr] at h1
      exact h1
    exact rat_lt_of_lt_of_le (rat_lt_of_le_of_lt hj1 hmid) hk1
  · -- Part 2: Uniform quantization tightness
    intro z_k z_j ε hε heq
    refine ⟨z_k - ε, z_j + ε, ?_, ?_, ?_⟩
    · have h1 : (z_k - ε) - z_k = -ε := by
        rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.add_comm z_k (-ε),
            Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
      rw [h1, rat_abs_neg, rat_abs_of_nonneg hε]
      exact rat_le_refl ε
    · have h1 : (z_j + ε) - z_j = ε := by
        rw [Rat.sub_eq_add_neg, Rat.add_comm z_j ε, Rat.add_assoc,
            Rat.add_neg_cancel, Rat.add_zero]
      rw [h1, rat_abs_of_nonneg hε]
      exact rat_le_refl ε
    · have h1 : z_k = z_j + 2 * ε := by
        have := congrArg (· + z_j) heq
        simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero,
               Rat.add_comm (2 * ε) z_j] using this
      rw [h1, rat_two_mul, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_assoc,
          Rat.add_neg_cancel, Rat.add_zero]
  · -- Part 3: Floating-point relative quantization sufficiency
    intro m z_k z_j z'_k z'_j u hjpos hjk hk hj hratio
    let P : Rat := ((2 ^ (m + 1) : Nat) : Rat)
    have hPpos : 0 < P := rat_natCast_pos (Nat.pow_pos (by decide))
    have hPne : P ≠ 0 := rat_natCast_ne_zero (Nat.pow_pos (by decide))
    have hu : u = P⁻¹ := by
      show 1 / P = P⁻¹
      rw [Rat.div_def, Rat.one_mul]
    have hzk_pos : 0 < z_k := rat_lt_of_lt_of_le hjpos (Rat.le_of_lt hjk)
    rw [rat_abs_of_nonneg (Rat.le_of_lt hzk_pos)] at hk
    rw [rat_abs_of_nonneg (Rat.le_of_lt hjpos)] at hj
    have hk1 : z_k * (1 - u) ≤ z'_k := by
      have h := ((rat_abs_le_iff (z'_k - z_k) (u * z_k)).mp hk).1
      have h1 := (Rat.add_le_add_right (c := z_k)).mpr h
      have hlhs : -(u * z_k) + z_k = z_k * (1 - u) := by
        rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_one, Rat.mul_neg,
            Rat.add_comm, Rat.mul_comm u z_k]
      have hrhs : (z'_k - z_k) + z_k = z'_k := by
        rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero]
      rw [hlhs, hrhs] at h1
      exact h1
    have hj1 : z'_j ≤ z_j * (1 + u) := by
      have h := ((rat_abs_le_iff (z'_j - z_j) (u * z_j)).mp hj).2
      have h1 := (Rat.add_le_add_right (c := z_j)).mpr h
      have hlhs : (z'_j - z_j) + z_j = z'_j := by
        rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero]
      have hrhs : u * z_j + z_j = z_j * (1 + u) := by
        rw [Rat.mul_add, Rat.mul_one, Rat.add_comm, Rat.mul_comm u z_j]
      rw [hlhs, hrhs] at h1
      exact h1
    have hmid : z_j * (1 + u) < z_k * (1 - u) := by
      have h1 := rat_mul_lt_mul_of_pos_right hratio (rat_inv_pos hPpos)
      have hl : z_j * (P + 1) * P⁻¹ = z_j * (1 + u) := by
        rw [Rat.mul_assoc, Rat.add_mul, Rat.mul_inv_cancel _ hPne, Rat.one_mul, hu]
      have hr : z_k * (P - 1) * P⁻¹ = z_k * (1 - u) := by
        rw [Rat.mul_assoc, Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul,
            Rat.mul_inv_cancel _ hPne, Rat.one_mul, hu, ← Rat.sub_eq_add_neg]
      change z_j * (P + 1) * P⁻¹ < z_k * (P - 1) * P⁻¹ at h1
      rw [hl, hr] at h1
      exact h1
    exact rat_lt_of_lt_of_le (rat_lt_of_le_of_lt hj1 hmid) hk1
  · -- Part 4: Floating-point relative quantization tightness
    intro m z_k z_j u hjpos heq
    let P : Rat := ((2 ^ (m + 1) : Nat) : Rat)
    have hPpos : 0 < P := rat_natCast_pos (Nat.pow_pos (by decide))
    have hPne : P ≠ 0 := rat_natCast_ne_zero (Nat.pow_pos (by decide))
    have hu : u = P⁻¹ := by
      show 1 / P = P⁻¹
      rw [Rat.div_def, Rat.one_mul]
    have hupos : 0 < u := by rw [hu]; exact rat_inv_pos hPpos
    have hPm1_pos : 0 < P - 1 := by
      rw [rat_sub_pos_iff]
      have h2m : 1 < 2 ^ (m + 1) := by
        have : 2 ≤ 2 ^ (m + 1) := by
          calc 2 = 2 ^ 1 := by decide
            _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have : (1 : Rat) = ((1 : Nat) : Rat) := by simp
      rw [this]; exact rat_natCast_lt h2m
    have hPp1_pos : 0 < P + 1 := by
      have h01 : (0 : Rat) ≤ 1 := by decide
      have h1 := rat_add_lt_add_of_lt_of_le hPpos h01
      simpa [Rat.zero_add] using h1
    have hzk_pos : 0 < z_k := by
      have hrhs : 0 < z_j * (P + 1) := rat_mul_pos hjpos hPp1_pos
      have heqP : z_k * (P - 1) = z_j * (P + 1) := heq
      rw [← heqP] at hrhs
      by_cases h : 0 < z_k
      · exact h
      · exfalso
        have hle : z_k ≤ 0 := rat_le_of_not_lt h
        have hneg : 0 ≤ -z_k := rat_neg_nonneg_of_nonpos hle
        have hprod : 0 ≤ (-z_k) * (P - 1) := rat_mul_nonneg hneg (Rat.le_of_lt hPm1_pos)
        rw [Rat.neg_mul] at hprod
        have hle0 : z_k * (P - 1) ≤ 0 := (rat_neg_le_neg_iff 0 _).mp (by simpa using hprod)
        exact Rat.lt_irrefl (rat_lt_of_lt_of_le hrhs hle0)
    refine ⟨z_k * (1 - u), z_j * (1 + u), ?_, ?_, ?_⟩
    · have h1 : z_k * (1 - u) - z_k = -(u * z_k) := by
        rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_one, Rat.mul_neg,
            Rat.add_comm z_k, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.mul_comm z_k u]
      rw [h1, rat_abs_neg, rat_abs_of_nonneg (Rat.le_of_lt hzk_pos),
          rat_abs_of_nonneg (rat_mul_nonneg (Rat.le_of_lt hupos) (Rat.le_of_lt hzk_pos))]
      exact rat_le_refl _
    · have h1 : z_j * (1 + u) - z_j = u * z_j := by
        rw [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_one, Rat.add_comm z_j,
            Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.mul_comm z_j u]
      rw [h1, rat_abs_of_nonneg (Rat.le_of_lt hjpos),
          rat_abs_of_nonneg (rat_mul_nonneg (Rat.le_of_lt hupos) (Rat.le_of_lt hjpos))]
      exact rat_le_refl _
    · have h1 := congrArg (· * P⁻¹) heq
      have hl : z_k * (P - 1) * P⁻¹ = z_k * (1 - u) := by
        rw [Rat.mul_assoc, Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul,
            Rat.mul_inv_cancel _ hPne, Rat.one_mul, hu, ← Rat.sub_eq_add_neg]
      have hr : z_j * (P + 1) * P⁻¹ = z_j * (1 + u) := by
        rw [Rat.mul_assoc, Rat.add_mul, Rat.mul_inv_cancel _ hPne, Rat.one_mul, hu]
      change z_k * (P - 1) * P⁻¹ = z_j * (P + 1) * P⁻¹ at h1
      rw [hl, hr] at h1
      exact h1
  · -- Part 5: Exact hardware ratio thresholds (E2M1, E3M2, E2M3/FP8, BF16, FP16)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact rat_ratio_eq_nat (2 ^ (1 + 1)) (by decide) 5 3 (by decide) (by decide)
    · exact rat_ratio_eq_nat (2 ^ (2 + 1)) (by decide) 9 7 (by decide) (by decide)
    · exact rat_ratio_eq_nat (2 ^ (3 + 1)) (by decide) 17 15 (by decide) (by decide)
    · exact rat_ratio_eq_nat (2 ^ (7 + 1)) (by decide) 257 255 (by decide) (by decide)
    · exact rat_ratio_eq_nat (2 ^ (10 + 1)) (by decide) 2049 2047 (by decide) (by decide)

end MoeBiasPlacement
