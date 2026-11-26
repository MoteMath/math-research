/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EF21Ternary.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Symmetric 2-Bit Zero-Omission Collapse & Mantissa Stochastic Rounding Law

Proves:
- `symmetric_2bit_no_zero_collapse`: omitting `0` from symmetric 2-bit `{±μ, ±3μ}` forces
  worst-case EF21 contraction `≤ 9 / (d + 8)` on the 1-sparse unit vector, with exact attainment.
- `mantissa_sr_variance_law`: exact worst-case relative variance `1 / (4 · 2^m · (2^m + 1))`
  for `m`-bit mantissa stochastic rounding, with exact attainment at `t = 2^m / (2 · 2^m + 1)`.
-/

namespace EF21Ternary

open scoped BigOperators

/-- Theorem 4 (`I086`): Exact zero-omission EF21 collapse for symmetric 2-bit `{±1, ±3}`
on the 1-sparse unit vector `e_0` in dimension `d ≥ 1`, with exact attainment at
`γ = 3 / (d + 8)`. -/
theorem symmetric_2bit_no_zero_collapse (d : ℕ) (hd : 0 < d) :
    let e0 : Fin d → ℝ := fun i => if i.1 = 0 then 1 else 0
    (∀ (γ : ℝ) (q : Fin d → ℤ),
      (∀ i, q i = -3 ∨ q i = -1 ∨ q i = 1 ∨ q i = 3) →
      (1 - 9 / ((d : ℝ) + 8)) * (∑ i : Fin d, (e0 i) ^ 2) ≤
        ∑ i : Fin d, (e0 i - γ * (q i : ℝ)) ^ 2) ∧
    (∃ q : Fin d → ℤ,
      (∀ i, q i = -3 ∨ q i = -1 ∨ q i = 1 ∨ q i = 3) ∧
      ∑ i : Fin d, (e0 i - (3 / ((d : ℝ) + 8)) * (q i : ℝ)) ^ 2 =
        (1 - 9 / ((d : ℝ) + 8)) * (∑ i : Fin d, (e0 i) ^ 2)) := by
  intro e0
  let i0 : Fin d := ⟨0, hd⟩
  have hsum_e0 : ∑ i : Fin d, (e0 i) ^ 2 = 1 := by
    rw [Finset.sum_eq_single i0]
    · simp [e0, i0]
    · intro i _ hi
      have hne : i.1 ≠ 0 := by
        intro h0
        exact hi (Fin.ext h0)
      simp [e0, hne]
    · simp
  have hd_pos : (0 : ℝ) < (d : ℝ) + 8 := by positivity
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  constructor
  · intro γ q hq
    rw [hsum_e0, mul_one]
    have hq_sq_ge : ∀ i : Fin d, (1 : ℝ) ≤ ((q i : ℝ)) ^ 2 := by
      intro i
      rcases hq i with h | h | h | h <;> rw [h] <;> norm_num
    have hq0_sq_le : ((q i0 : ℝ)) ^ 2 ≤ 9 := by
      rcases hq i0 with h | h | h | h <;> rw [h] <;> norm_num
    let S : ℝ := ∑ i : Fin d, ((q i : ℝ)) ^ 2
    have hS_split : S = ((q i0 : ℝ)) ^ 2 + ∑ i ∈ Finset.univ.erase i0, ((q i : ℝ)) ^ 2 :=
      (Finset.add_sum_erase Finset.univ (fun i : Fin d => ((q i : ℝ)) ^ 2)
        (Finset.mem_univ i0)).symm
    have herase_card : (Finset.univ.erase i0).card = d - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_fin]
    have herase_ge : ((d : ℝ) - 1) ≤ ∑ i ∈ Finset.univ.erase i0, ((q i : ℝ)) ^ 2 := by
      have h1 : ∑ _i ∈ Finset.univ.erase i0, (1 : ℝ) ≤
          ∑ i ∈ Finset.univ.erase i0, ((q i : ℝ)) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hq_sq_ge i)
      rw [Finset.sum_const, herase_card, nsmul_eq_mul, mul_one] at h1
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub hd, Nat.cast_one]
      linarith
    have hS_ge : ((q i0 : ℝ)) ^ 2 + ((d : ℝ) - 1) ≤ S := by linarith
    have hS_pos : 0 < S := by
      have hq0_ge := hq_sq_ge i0
      linarith
    have hexpand : ∑ i : Fin d, (e0 i - γ * (q i : ℝ)) ^ 2 =
        1 - 2 * γ * (q i0 : ℝ) + γ ^ 2 * S := by
      have hterm : ∀ i : Fin d, (e0 i - γ * (q i : ℝ)) ^ 2 =
          (e0 i) ^ 2 - 2 * γ * (e0 i * (q i : ℝ)) + γ ^ 2 * ((q i : ℝ)) ^ 2 := by
        intro i; ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hsum_e0]
      have hcross : ∑ i : Fin d, e0 i * (q i : ℝ) = (q i0 : ℝ) := by
        rw [Finset.sum_eq_single i0]
        · simp [e0, i0]
        · intro i _ hi
          have hne : i.1 ≠ 0 := fun h0 => hi (Fin.ext h0)
          simp [e0, hne]
        · simp
      rw [hcross]
    rw [hexpand]
    have hcs : 1 - ((q i0 : ℝ)) ^ 2 / S ≤ 1 - 2 * γ * (q i0 : ℝ) + γ ^ 2 * S := by
      have hsq : 0 ≤ S * (γ - (q i0 : ℝ) / S) ^ 2 := mul_nonneg hS_pos.le (sq_nonneg _)
      have hident : 1 - 2 * γ * (q i0 : ℝ) + γ ^ 2 * S - (1 - ((q i0 : ℝ)) ^ 2 / S) =
          S * (γ - (q i0 : ℝ) / S) ^ 2 := by
        field_simp
        ring
      linarith
    have hfrac : ((q i0 : ℝ)) ^ 2 / S ≤ 9 / ((d : ℝ) + 8) := by
      rw [div_le_div_iff₀ hS_pos hd_pos]
      nlinarith
    linarith
  · refine ⟨fun i => if i.1 = 0 then 3 else 1, ?_, ?_⟩
    · intro i
      by_cases h : i.1 = 0 <;> simp [h]
    · rw [hsum_e0, mul_one]
      have hsplit := (Finset.add_sum_erase Finset.univ
        (fun i : Fin d => (e0 i - 3 / ((d : ℝ) + 8) *
          ((if i.1 = 0 then (3 : ℤ) else 1 : ℤ) : ℝ)) ^ 2)
        (Finset.mem_univ i0)).symm
      rw [hsplit]
      have h0 : (e0 i0 - 3 / ((d : ℝ) + 8) *
          ((if i0.1 = 0 then (3 : ℤ) else 1 : ℤ) : ℝ)) ^ 2 =
          (1 - 9 / ((d : ℝ) + 8)) ^ 2 := by
        simp [e0, i0]
        ring
      have hrest : ∑ i ∈ Finset.univ.erase i0,
          (e0 i - 3 / ((d : ℝ) + 8) *
            ((if i.1 = 0 then (3 : ℤ) else 1 : ℤ) : ℝ)) ^ 2 =
          ((d : ℝ) - 1) * (3 / ((d : ℝ) + 8)) ^ 2 := by
        have hcongr : ∀ i ∈ Finset.univ.erase i0,
            (e0 i - 3 / ((d : ℝ) + 8) *
              ((if i.1 = 0 then (3 : ℤ) else 1 : ℤ) : ℝ)) ^ 2 =
            (3 / ((d : ℝ) + 8)) ^ 2 := by
          intro i hi
          have hne : i.1 ≠ 0 := by
            intro h0
            exact (Finset.mem_erase.mp hi).1 (Fin.ext h0)
          simp [e0, hne]
        rw [Finset.sum_congr rfl hcongr, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_fin, nsmul_eq_mul]
        have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
          rw [Nat.cast_sub hd, Nat.cast_one]
        rw [hcast]
      rw [h0, hrest]
      field_simp
      ring

/-- Theorem 5 (`I087`): Exact worst-case relative variance law for `m`-bit mantissa
floating-point stochastic rounding, with exact attainment at `t = 2^m / (2 · 2^m + 1)`. -/
theorem mantissa_sr_variance_law (m : ℕ) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * (1 - t) / ((2 : ℝ) ^ m + t) ^ 2 ≤
        1 / (4 * (2 : ℝ) ^ m * ((2 : ℝ) ^ m + 1))) ∧
    (let tStar : ℝ := (2 : ℝ) ^ m / (2 * (2 : ℝ) ^ m + 1)
     0 ≤ tStar ∧ tStar ≤ 1 ∧
     tStar * (1 - tStar) / ((2 : ℝ) ^ m + tStar) ^ 2 =
       1 / (4 * (2 : ℝ) ^ m * ((2 : ℝ) ^ m + 1))) := by
  have hM : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hM1 : (0 : ℝ) < (2 : ℝ) ^ m + 1 := by positivity
  have h2M1 : (0 : ℝ) < 2 * (2 : ℝ) ^ m + 1 := by positivity
  constructor
  · intro t ht0 _ht1
    have hden1 : (0 : ℝ) < ((2 : ℝ) ^ m + t) ^ 2 := by positivity
    have hden2 : (0 : ℝ) < 4 * (2 : ℝ) ^ m * ((2 : ℝ) ^ m + 1) := by positivity
    rw [div_le_div_iff₀ hden1 hden2]
    have hsos : 0 ≤ ((2 * (2 : ℝ) ^ m + 1) * t - (2 : ℝ) ^ m) ^ 2 := sq_nonneg _
    nlinarith
  · dsimp only
    refine ⟨by positivity, ?_, ?_⟩
    · rw [div_le_one h2M1]
      linarith
    · field_simp
      ring

end EF21Ternary
