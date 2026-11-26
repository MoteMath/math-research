/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UnsignedFp4SoftmaxV.RatOrder

/-!
# Theorems 1 & 2: IEEE `U-E1M3 == UINT4` Collapse and All-`B` Unsigned 4-Bit EF21 Classification

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. `unsigned_fp4_e1m3_collapse_to_uint4`: Bit-level proof that IEEE-subnormal `U-E1M3`
   decodes to `{0, ..., 15}`, identically equal to `U-E0M4` (`UINT4`).
2. `unsigned_fp4_all_b_ef21_regime_classification`: Universal per-coordinate and vector-level
   proof of the exact EF21 contraction formula `1 - α(U, B) = max_k ((B-1) h_k^2)/(1 + (B-1) m_k^2)`,
   complete all-`B ≥ 2` unsigned 4-bit regime classification
   (`U-E0M4` `[2..9]` → `U-E2M2` `[10..130]` → `U-E3M1` `[131..18431]` → `U-E4M0` `[≥ 18432]`),
   and exact improvement ratios over signed `S-E2M1` at `B ∈ {64, 256, 1024}`.
-/

namespace UnsignedFp4SoftmaxV

/-! ### Theorem 1: IEEE `U-E1M3 == UINT4` Collapse -/

theorem decode_u_e1m3_eq_uint4 (c : Nat) (hc : c < 16) :
    decodeUnsignedIEEE 1 3 c = decodeUnsignedIEEE 0 4 c ∧
    decodeUnsignedIEEE 1 3 c = c := by
  unfold decodeUnsignedIEEE
  simp only [Nat.one_ne_zero, ↓reduceIte]
  split
  · rename_i he
    have hlt : c < 8 := by omega
    have hmod : c % 8 = c := Nat.mod_eq_of_lt hlt
    exact ⟨hmod, hmod⟩
  · rename_i he
    have hge : 8 ≤ c := by omega
    have he1 : c / 8 = 1 := by omega
    have hval : (8 + c % 8) * 2 ^ (c / 8 - 1) = c := by
      rw [he1]
      omega
    exact ⟨hval, hval⟩

theorem unsigned_fp4_e1m3_collapse_to_uint4 :
    (∀ c : Nat, c < 16 →
      decodeUnsignedIEEE 1 3 c = decodeUnsignedIEEE 0 4 c ∧
      decodeUnsignedIEEE 1 3 c = c) ∧
    unsignedFp4IntLevels 1 3 = unsignedFp4IntLevels 0 4 ∧
    unsignedFp4IntLevels 1 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] ∧
    uE1M3Levels = uE0M4Levels ∧
    (∀ B : Nat, ef21OneMinusAlpha uE1M3Levels B = ef21OneMinusAlpha uE0M4Levels B) ∧
    (∀ N : Nat, simplexRtnDrift uE1M3Levels N = simplexRtnDrift uE0M4Levels N) ∧
    unsignedFp4IntLevels 2 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28] ∧
    unsignedFp4IntLevels 3 1 = [0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192] ∧
    unsignedFp4IntLevels 4 0 =
      [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384] := by
  have hInt : unsignedFp4IntLevels 1 3 = unsignedFp4IntLevels 0 4 := rfl
  have hRat : uE1M3Levels = uE0M4Levels := rfl
  refine ⟨decode_u_e1m3_eq_uint4, hInt, rfl, hRat, ?_, ?_, rfl, rfl, rfl⟩
  · intro B; rw [hRat]
  · intro N; rw [hRat]

/-! ### Theorem 2: Universal EF21 Contraction Formula & All-`B` Regime Classification -/

/-- Per-coordinate exact EF21 midpoint optimality inside any nonnegative bin `[u0, u1]`:
    for any `c > 0` and `0 ≤ u0 ≤ x ≤ u1`, `rtnDist(u0, u1, x)^2 ≤ (h^2 / (c + m^2)) * (c + x^2)`. -/
theorem ef21_coord_bound {u0 u1 x c : Rat}
    (hu0 : (0 : Rat) ≤ u0) (hx0 : u0 ≤ x) (hx1 : x ≤ u1) (hc : (0 : Rat) < c) :
    let h := (u1 - u0) / 2
    let m := (u0 + u1) / 2
    rtnDist u0 u1 x * rtnDist u0 u1 x ≤ (h * h / (c + m * m)) * (c + x * x) := by
  intro h m
  have hden_pos : (0 : Rat) < c + m * m := rat_add_pos_of_pos_of_nonneg hc (rat_sq_nonneg m)
  have hden_ne : c + m * m ≠ 0 := Rat.ne_of_gt hden_pos
  have hgoal :
      rtnDist u0 u1 x * rtnDist u0 u1 x * (c + m * m) ≤ h * h * (c + x * x) →
      rtnDist u0 u1 x * rtnDist u0 u1 x ≤ (h * h / (c + m * m)) * (c + x * x) := by
    intro hcross
    apply rat_le_of_mul_pos_right hden_pos
    have eq1 : (h * h / (c + m * m)) * (c + x * x) * (c + m * m) = h * h * (c + x * x) := by
      rw [Rat.mul_comm ((h * h / (c + m * m))) (c + x * x), Rat.mul_assoc,
          rat_div_mul_cancel hden_ne, Rat.mul_comm]
    rw [eq1]
    exact hcross
  apply hgoal
  unfold rtnDist
  split
  · rename_i hxm
    have hmx_nonneg : (0 : Rat) ≤ m - x := rat_sub_nonneg hxm
    have hxu0_nonneg : (0 : Rat) ≤ x - u0 := rat_sub_nonneg hx0
    have hmu0_nonneg : (0 : Rat) ≤ m - u0 := rat_sub_nonneg (Rat.le_trans hx0 hxm)
    have hx_nonneg : (0 : Rat) ≤ x := Rat.le_trans hu0 hx0
    have hm_nonneg : (0 : Rat) ≤ m := Rat.le_trans hx_nonneg hxm
    have hterm1 : (0 : Rat) ≤ c * ((m - u0) + (x - u0)) :=
      Rat.mul_nonneg (Rat.le_of_lt hc) (rat_add_nonneg hmu0_nonneg hxu0_nonneg)
    have hterm2 : (0 : Rat) ≤ u0 * (m * (x - u0) + x * (m - u0)) :=
      Rat.mul_nonneg hu0 (rat_add_nonneg (Rat.mul_nonneg hm_nonneg hxu0_nonneg)
                                         (Rat.mul_nonneg hx_nonneg hmu0_nonneg))
    have hdiff_nonneg :
        (0 : Rat) ≤ (m - x) * (c * ((m - u0) + (x - u0)) + u0 * (m * (x - u0) + x * (m - u0))) :=
      Rat.mul_nonneg hmx_nonneg (rat_add_nonneg hterm1 hterm2)
    apply rat_le_of_sub_nonneg
    have hid :
        h * h * (c + x * x) - (x - u0) * (x - u0) * (c + m * m) =
        (m - x) * (c * ((m - u0) + (x - u0)) + u0 * (m * (x - u0) + x * (m - u0))) := by
      dsimp only [h, m]; grind
    rw [hid]
    exact hdiff_nonneg
  · rename_i hnot
    have hmx : m < x := Rat.not_le.mp hnot
    have hxm_nonneg : (0 : Rat) ≤ x - m := rat_sub_nonneg (Rat.le_of_lt hmx)
    have hu1x_nonneg : (0 : Rat) ≤ u1 - x := rat_sub_nonneg hx1
    have hu1x_le_h : u1 - x ≤ h := by
      apply rat_le_of_sub_nonneg
      have eq : h - (u1 - x) = x - m := by dsimp only [h, m]; grind
      rw [eq]; exact hxm_nonneg
    have hsq_le : (u1 - x) * (u1 - x) ≤ h * h :=
      Rat.le_trans (rat_mul_le_mul_of_nonneg_left hu1x_le_h hu1x_nonneg)
                   (rat_mul_le_mul_of_nonneg_right hu1x_le_h (Rat.le_trans hu1x_nonneg hu1x_le_h))
    have hm_nonneg : (0 : Rat) ≤ m := by
      have hu1_nonneg : (0 : Rat) ≤ u1 := Rat.le_trans hu0 (Rat.le_trans hx0 hx1)
      exact rat_div_nonneg (rat_add_nonneg hu0 hu1_nonneg) (by decide)
    have hmx_sq : m * m ≤ x * x :=
      Rat.le_trans (rat_mul_le_mul_of_nonneg_left (Rat.le_of_lt hmx) hm_nonneg)
                   (rat_mul_le_mul_of_nonneg_right (Rat.le_of_lt hmx)
                     (Rat.le_trans hm_nonneg (Rat.le_of_lt hmx)))
    have hden_le : c + m * m ≤ c + x * x := rat_add_le_add Rat.le_refl hmx_sq
    exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hsq_le (Rat.le_of_lt hden_pos))
                       (rat_mul_le_mul_of_nonneg_left hden_le (rat_sq_nonneg h))

/-- Vector-level EF21 contraction upper bound for any block size `B ≥ 2` and peak `x_0 = 1`. -/
theorem ef21_vector_upper_bound {B : Nat} (hB : 2 ≤ B) {C : Rat}
    (x e : Fin (B - 1) → Rat)
    (hcoord : ∀ j : Fin (B - 1), ∃ u0 u1 : Rat,
      (0 : Rat) ≤ u0 ∧ u0 ≤ x j ∧ x j ≤ u1 ∧
      e j = rtnDist u0 u1 (x j) ∧ ef21Bin u0 u1 B ≤ C) :
    sumFin (fun j => e j * e j) / (1 + sumFin (fun j => x j * x j)) ≤ C := by
  have hb1_nat : 0 < B - 1 := by omega
  have hb1_pos : (0 : Rat) < ((B - 1 : Nat) : Rat) := rat_natCast_pos hb1_nat
  have hb1_ne : ((B - 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hb1_pos
  let c : Rat := 1 / ((B - 1 : Nat) : Rat)
  have hc_pos : (0 : Rat) < c := rat_div_pos (by decide) hb1_pos
  have hsum_sq_nonneg : (0 : Rat) ≤ sumFin (fun j : Fin (B - 1) => x j * x j) := by
    have h0 : sumFin (fun _ : Fin (B - 1) => (0 : Rat)) = 0 := by
      rw [sumFin_const, Rat.mul_zero]
    rw [← h0]
    exact sumFin_le_sumFin (fun j => rat_sq_nonneg (x j))
  have hnorm_pos : (0 : Rat) < 1 + sumFin (fun j : Fin (B - 1) => x j * x j) :=
    rat_add_pos_of_pos_of_nonneg (by decide) hsum_sq_nonneg
  apply rat_div_le_of_mul_le hnorm_pos
  have hterm : ∀ j : Fin (B - 1), e j * e j ≤ C * (c + x j * x j) := by
    intro j
    rcases hcoord j with ⟨u0, u1, hu0, hx0, hx1, heq, hbin⟩
    rw [heq]
    have h1 := ef21_coord_bound hu0 hx0 hx1 hc_pos
    let h := (u1 - u0) / 2
    let m := (u0 + u1) / 2
    have hfrac_eq : h * h / (c + m * m) = ef21Bin u0 u1 B := by
      unfold ef21Bin
      dsimp only [h, m, c]
      have hd1 : 1 / ((B - 1 : Nat) : Rat) + ((u0 + u1) / 2) * ((u0 + u1) / 2) ≠ 0 :=
        Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg hc_pos (rat_sq_nonneg _))
      have hd2 : 1 + ((B - 1 : Nat) : Rat) * (((u0 + u1) / 2) * ((u0 + u1) / 2)) ≠ 0 :=
        Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (by decide)
          (Rat.mul_nonneg (Rat.le_of_lt hb1_pos) (rat_sq_nonneg _)))
      apply rat_div_eq_of_cross hd1 hd2
      have hmul : (1 / ((B - 1 : Nat) : Rat)) * ((B - 1 : Nat) : Rat) = 1 :=
        rat_div_mul_cancel hb1_ne
      grind
    change rtnDist u0 u1 (x j) * rtnDist u0 u1 (x j) ≤ (h * h / (c + m * m)) * (c + x j * x j) at h1
    rw [hfrac_eq] at h1
    have hcx_nonneg : (0 : Rat) ≤ c + x j * x j :=
      Rat.le_of_lt (rat_add_pos_of_pos_of_nonneg hc_pos (rat_sq_nonneg (x j)))
    exact Rat.le_trans h1 (rat_mul_le_mul_of_nonneg_right hbin hcx_nonneg)
  have hsum_le := sumFin_le_sumFin hterm
  rw [sumFin_mul_left, sumFin_add, sumFin_const] at hsum_le
  have hbc : ((B - 1 : Nat) : Rat) * c = 1 := by
    dsimp only [c]
    exact rat_mul_div_cancel hb1_ne
  rw [hbc] at hsum_le
  exact hsum_le

/-- Exact attainment of `ef21Bin u0 u1 B` at the uniform midpoint vector `(1, m, ..., m)`. -/
theorem ef21_midpoint_attainment {B : Nat} (u0 u1 : Rat) :
    let h := (u1 - u0) / 2
    let m := (u0 + u1) / 2
    sumFin (fun _ : Fin (B - 1) => h * h) / (1 + sumFin (fun _ : Fin (B - 1) => m * m)) =
      ef21Bin u0 u1 B := by
  intro h m
  rw [sumFin_const, sumFin_const]
  rfl

/-! ### Exact Closed-Form EF21 Formulas for Unsigned 4-Bit & `S-E2M1` Codebooks (`∀ B ≥ 2`) -/

private theorem ef21Bin_int_form (a b M : Rat) (hM : M ≠ 0) (B : Nat) :
    ef21Bin (a / M) (b / M) B =
      ((B - 1 : Nat) : Rat) * ((b - a) * (b - a)) /
        (4 * (M * M) + ((B - 1 : Nat) : Rat) * ((a + b) * (a + b))) := by
  unfold ef21Bin
  have hM2 : (0 : Rat) < M * M := by
    have hle := rat_sq_nonneg M
    have hne : M * M ≠ 0 := by
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact hM h
      | inr h => exact hM h
    exact Rat.lt_of_le_of_ne hle (Ne.symm hne)
  have hd1 : (0 : Rat) < 1 + ((B - 1 : Nat) : Rat) *
      (((a / M + b / M) / 2) * ((a / M + b / M) / 2)) :=
    rat_add_pos_of_pos_of_nonneg (by decide)
      (Rat.mul_nonneg (rat_natCast_nonneg (B - 1)) (rat_sq_nonneg _))
  have hd2 : (0 : Rat) < 4 * (M * M) + ((B - 1 : Nat) : Rat) * ((a + b) * (a + b)) :=
    rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) hM2)
      (Rat.mul_nonneg (rat_natCast_nonneg (B - 1)) (rat_sq_nonneg _))
  apply rat_div_eq_of_cross (Rat.ne_of_gt hd1) (Rat.ne_of_gt hd2)
  have ha : (a / M) * M = a := rat_div_mul_cancel hM
  have hb : (b / M) * M = b := rat_div_mul_cancel hM
  grind

private theorem ef21Bin_scaled (a b M A C : Rat) (B : Nat)
    (hM : M ≠ 0) (hd : (b - a) * (b - a) ≠ 0)
    (hA : 4 * (M * M) = A * ((b - a) * (b - a)))
    (hC : (a + b) * (a + b) = C * ((b - a) * (b - a)))
    (hApos : (0 : Rat) < A) (hCnonneg : (0 : Rat) ≤ C) :
    ef21Bin (a / M) (b / M) B =
      ((B - 1 : Nat) : Rat) / (A + C * ((B - 1 : Nat) : Rat)) := by
  rw [ef21Bin_int_form a b M hM B]
  have hb1_nonneg : (0 : Rat) ≤ ((B - 1 : Nat) : Rat) := rat_natCast_nonneg (B - 1)
  have hden2_pos : (0 : Rat) < A + C * ((B - 1 : Nat) : Rat) :=
    rat_add_pos_of_pos_of_nonneg hApos (Rat.mul_nonneg hCnonneg hb1_nonneg)
  have hden1_pos : (0 : Rat) < 4 * (M * M) + ((B - 1 : Nat) : Rat) * ((a + b) * (a + b)) := by
    rw [hA, hC]
    have hsq_pos : (0 : Rat) < (b - a) * (b - a) :=
      Rat.lt_of_le_of_ne (rat_sq_nonneg (b - a)) (Ne.symm hd)
    have eq : A * ((b - a) * (b - a)) + ((B - 1 : Nat) : Rat) * (C * ((b - a) * (b - a))) =
        (A + C * ((B - 1 : Nat) : Rat)) * ((b - a) * (b - a)) := by grind
    rw [eq]
    exact rat_mul_pos hden2_pos hsq_pos
  apply rat_div_eq_of_cross (Rat.ne_of_gt hden1_pos) (Rat.ne_of_gt hden2_pos)
  rw [hA, hC]; grind

private theorem ef21_frac_lt_of_denom_lt {b1 D1 D2 : Rat}
    (hb1 : (0 : Rat) < b1) (hD1 : (0 : Rat) < D1) (hD2 : (0 : Rat) < D2) (h : D2 < D1) :
    b1 / D1 < b1 / D2 := by
  apply rat_div_lt_div_of_cross hD1 hD2
  exact rat_mul_lt_mul_of_pos_left h hb1

private theorem ef21_frac_le_of_denom_le {b1 D1 D2 : Rat}
    (hb1 : (0 : Rat) ≤ b1) (hD1 : (0 : Rat) < D1) (hD2 : (0 : Rat) < D2) (h : D2 ≤ D1) :
    b1 / D1 ≤ b1 / D2 := by
  apply rat_div_le_div_of_cross hD1 hD2
  exact rat_mul_le_mul_of_nonneg_left h hb1

private theorem ef21_bin_le_frac (a b M A2 C2 : Nat) (B : Nat)
    (hM : 0 < M) (hA2 : 0 < A2)
    (hA : A2 * ((b - a) * (b - a)) ≤ 4 * (M * M))
    (hC : C2 * ((b - a) * (b - a)) ≤ (a + b) * (a + b))
    (hab : a ≤ b) :
    ef21Bin ((a : Rat) / (M : Rat)) ((b : Rat) / (M : Rat)) B ≤
      ((B - 1 : Nat) : Rat) / ((A2 : Rat) + (C2 : Rat) * ((B - 1 : Nat) : Rat)) := by
  have hMpos : (0 : Rat) < (M : Rat) := rat_natCast_pos hM
  have hMne : (M : Rat) ≠ 0 := Rat.ne_of_gt hMpos
  rw [ef21Bin_int_form (a : Rat) (b : Rat) (M : Rat) hMne B]
  have hb1 : (0 : Rat) ≤ ((B - 1 : Nat) : Rat) := rat_natCast_nonneg (B - 1)
  have hM2 : (0 : Rat) < (M : Rat) * (M : Rat) := rat_mul_pos hMpos hMpos
  have hd1 : (0 : Rat) < 4 * ((M : Rat) * (M : Rat)) +
      ((B - 1 : Nat) : Rat) * (((a : Rat) + (b : Rat)) * ((a : Rat) + (b : Rat))) :=
    rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) hM2)
      (Rat.mul_nonneg hb1 (rat_sq_nonneg _))
  have hd2 : (0 : Rat) < (A2 : Rat) + (C2 : Rat) * ((B - 1 : Nat) : Rat) :=
    rat_add_pos_of_pos_of_nonneg (rat_natCast_pos hA2) (Rat.mul_nonneg (rat_natCast_nonneg C2) hb1)
  apply rat_div_le_div_of_cross hd1 hd2
  have hsub_cast : ((b - a : Nat) : Rat) = (b : Rat) - (a : Rat) := by
    have hk : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
    have hc : (b : Rat) = (a : Rat) + ((b - a : Nat) : Rat) := by
      conv => lhs; rw [hk]
      rw [Rat.natCast_add]
    grind
  have hA_rat : (A2 : Rat) * (((b : Rat) - (a : Rat)) * ((b : Rat) - (a : Rat))) ≤
      4 * ((M : Rat) * (M : Rat)) := by
    have := rat_natCast_le hA
    simp only [Rat.natCast_mul] at this
    rw [hsub_cast] at this
    exact this
  have hC_rat : (C2 : Rat) * (((b : Rat) - (a : Rat)) * ((b : Rat) - (a : Rat))) ≤
      ((a : Rat) + (b : Rat)) * ((a : Rat) + (b : Rat)) := by
    have := rat_natCast_le hC
    simp only [Rat.natCast_mul, Rat.natCast_add] at this
    rw [hsub_cast] at this
    exact this
  have hsum : ((A2 : Rat) + (C2 : Rat) * ((B - 1 : Nat) : Rat)) *
      (((b : Rat) - (a : Rat)) * ((b : Rat) - (a : Rat))) ≤
      4 * ((M : Rat) * (M : Rat)) +
        ((B - 1 : Nat) : Rat) * (((a : Rat) + (b : Rat)) * ((a : Rat) + (b : Rat))) := by
    have h1 := rat_add_le_add hA_rat (rat_mul_le_mul_of_nonneg_left hC_rat hb1)
    have eq : ((A2 : Rat) + (C2 : Rat) * ((B - 1 : Nat) : Rat)) *
        (((b : Rat) - (a : Rat)) * ((b : Rat) - (a : Rat))) =
        (A2 : Rat) * (((b : Rat) - (a : Rat)) * ((b : Rat) - (a : Rat))) +
        ((B - 1 : Nat) : Rat) * ((C2 : Rat) * (((b : Rat) - (a : Rat)) * ((b : Rat) - (a : Rat)))) := by
      grind
    rw [eq]; exact h1
  have h2 := rat_mul_le_mul_of_nonneg_left hsum hb1
  have eqL : ((B - 1 : Nat) : Rat) * (((b : Rat) - (a : Rat)) * ((b : Rat) - (a : Rat))) *
      ((A2 : Rat) + (C2 : Rat) * ((B - 1 : Nat) : Rat)) =
      ((B - 1 : Nat) : Rat) * (((A2 : Rat) + (C2 : Rat) * ((B - 1 : Nat) : Rat)) *
        (((b : Rat) - (a : Rat)) * ((b : Rat) - (a : Rat)))) := by grind
  rw [eqL]
  exact h2

/-- Exact closed form of `ef21OneMinusAlpha uE0M4Levels B` for ALL `B : Nat`. -/
theorem ef21_uE0M4_exact (B : Nat) :
    ef21OneMinusAlpha uE0M4Levels B =
      ((B - 1 : Nat) : Rat) / (900 + ((B - 1 : Nat) : Rat)) := by
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  let f0 : Rat := b1 / (900 + b1)
  have hf0_nonneg : (0 : Rat) ≤ f0 :=
    rat_div_nonneg (rat_natCast_nonneg (B - 1))
      (rat_add_pos_of_pos_of_nonneg (by decide) (rat_natCast_nonneg (B - 1)))
  have h0 : ef21Bin (((0 : Nat) : Rat) / ((15 : Nat) : Rat)) (((1 : Nat) : Rat) / ((15 : Nat) : Rat)) B =
      ((B - 1 : Nat) : Rat) / (900 + ((B - 1 : Nat) : Rat)) := by
    have := ef21Bin_scaled 0 1 15 900 1 B (by decide) (by grind) (by grind) (by grind) (by decide) (by decide)
    simpa [Rat.one_mul] using this
  have hdom : ∀ a b : Nat, a ≤ b →
      900 * ((b - a) * (b - a)) ≤ 4 * (15 * 15) →
      1 * ((b - a) * (b - a)) ≤ (a + b) * (a + b) →
      ef21Bin ((a : Rat) / (15 : Rat)) ((b : Rat) / (15 : Rat)) B ≤ f0 := by
    intro a b hab hA hC
    have := ef21_bin_le_frac a b 15 900 1 B (by omega) (by omega) hA hC hab
    simpa [f0, b1, Rat.one_mul] using this
  have hL : unsignedFp4IntLevels 0 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl
  unfold ef21OneMinusAlpha uE0M4Levels normalizeLevels
  rw [hL]
  simp only [List.map, maxAdjacentBins]
  apply Rat.le_antisymm
  · repeat (first | apply rat_max_le | exact hf0_nonneg | (apply hdom <;> omega))
  · rw [← h0]; exact rat_le_max_left _ _

/-- Exact closed form of `ef21OneMinusAlpha uE2M2Levels B` for ALL `B : Nat`. -/
theorem ef21_uE2M2_exact (B : Nat) :
    ef21OneMinusAlpha uE2M2Levels B =
      max (((B - 1 : Nat) : Rat) / (3136 + ((B - 1 : Nat) : Rat)))
          (((B - 1 : Nat) : Rat) / (196 + 81 * ((B - 1 : Nat) : Rat))) := by
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  let f0 : Rat := b1 / (3136 + b1)
  let f12 : Rat := b1 / (196 + 81 * b1)
  let M := max f0 f12
  have hf0_nonneg : (0 : Rat) ≤ f0 :=
    rat_div_nonneg (rat_natCast_nonneg (B - 1))
      (rat_add_pos_of_pos_of_nonneg (by decide) (rat_natCast_nonneg (B - 1)))
  have hM_nonneg : (0 : Rat) ≤ M := Rat.le_trans hf0_nonneg (rat_le_max_left f0 f12)
  have h0 : ef21Bin (((0 : Nat) : Rat) / ((28 : Nat) : Rat)) (((1 : Nat) : Rat) / ((28 : Nat) : Rat)) B =
      ((B - 1 : Nat) : Rat) / (3136 + ((B - 1 : Nat) : Rat)) := by
    have := ef21Bin_scaled 0 1 28 3136 1 B (by decide) (by grind) (by grind) (by grind) (by decide) (by decide)
    simpa [Rat.one_mul] using this
  have h12 : ef21Bin (((16 : Nat) : Rat) / ((28 : Nat) : Rat)) (((20 : Nat) : Rat) / ((28 : Nat) : Rat)) B =
      ((B - 1 : Nat) : Rat) / (196 + 81 * ((B - 1 : Nat) : Rat)) := by
    have := ef21Bin_scaled 16 20 28 196 81 B (by decide) (by grind) (by grind) (by grind) (by decide) (by decide)
    simpa using this
  have hdom0 : ∀ a b : Nat, a ≤ b →
      3136 * ((b - a) * (b - a)) ≤ 4 * (28 * 28) →
      1 * ((b - a) * (b - a)) ≤ (a + b) * (a + b) →
      ef21Bin ((a : Rat) / (28 : Rat)) ((b : Rat) / (28 : Rat)) B ≤ M := by
    intro a b hab hA hC
    have hle := ef21_bin_le_frac a b 28 3136 1 B (by omega) (by omega) hA hC hab
    have hle' : ef21Bin ((a : Rat) / (28 : Rat)) ((b : Rat) / (28 : Rat)) B ≤ f0 := by
      simpa [f0, b1, Rat.one_mul] using hle
    exact Rat.le_trans hle' (rat_le_max_left f0 f12)
  have hdom12 : ∀ a b : Nat, a ≤ b →
      196 * ((b - a) * (b - a)) ≤ 4 * (28 * 28) →
      81 * ((b - a) * (b - a)) ≤ (a + b) * (a + b) →
      ef21Bin ((a : Rat) / (28 : Rat)) ((b : Rat) / (28 : Rat)) B ≤ M := by
    intro a b hab hA hC
    have hle := ef21_bin_le_frac a b 28 196 81 B (by omega) (by omega) hA hC hab
    have hle' : ef21Bin ((a : Rat) / (28 : Rat)) ((b : Rat) / (28 : Rat)) B ≤ f12 := by
      simpa [f12, b1] using hle
    exact Rat.le_trans hle' (rat_le_max_right f0 f12)
  have hL : unsignedFp4IntLevels 2 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28] := rfl
  unfold ef21OneMinusAlpha uE2M2Levels normalizeLevels
  rw [hL]
  simp only [List.map, maxAdjacentBins]
  apply Rat.le_antisymm
  · repeat (first | apply rat_max_le | exact hM_nonneg
                  | (apply hdom0 <;> omega) | (apply hdom12 <;> omega))
  · apply rat_max_le
    · rw [← h0]; exact rat_le_max_left _ _
    · rw [← h12]
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      exact rat_le_max_left _ _

/-- Exact closed form of `ef21OneMinusAlpha uE3M1Levels B` for ALL `B : Nat`. -/
theorem ef21_uE3M1_exact (B : Nat) :
    ef21OneMinusAlpha uE3M1Levels B =
      max (((B - 1 : Nat) : Rat) / (147456 + ((B - 1 : Nat) : Rat)))
          (((B - 1 : Nat) : Rat) / (36 + 25 * ((B - 1 : Nat) : Rat))) := by
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  let f0 : Rat := b1 / (147456 + b1)
  let f14 : Rat := b1 / (36 + 25 * b1)
  let M := max f0 f14
  have hf0_nonneg : (0 : Rat) ≤ f0 :=
    rat_div_nonneg (rat_natCast_nonneg (B - 1))
      (rat_add_pos_of_pos_of_nonneg (by decide) (rat_natCast_nonneg (B - 1)))
  have hM_nonneg : (0 : Rat) ≤ M := Rat.le_trans hf0_nonneg (rat_le_max_left f0 f14)
  have h0 : ef21Bin (((0 : Nat) : Rat) / ((192 : Nat) : Rat)) (((1 : Nat) : Rat) / ((192 : Nat) : Rat)) B =
      ((B - 1 : Nat) : Rat) / (147456 + ((B - 1 : Nat) : Rat)) := by
    have := ef21Bin_scaled 0 1 192 147456 1 B (by decide) (by grind) (by grind) (by grind) (by decide) (by decide)
    simpa [Rat.one_mul] using this
  have h14 : ef21Bin (((128 : Nat) : Rat) / ((192 : Nat) : Rat)) (((192 : Nat) : Rat) / ((192 : Nat) : Rat)) B =
      ((B - 1 : Nat) : Rat) / (36 + 25 * ((B - 1 : Nat) : Rat)) := by
    have := ef21Bin_scaled 128 192 192 36 25 B (by decide) (by grind) (by grind) (by grind) (by decide) (by decide)
    simpa using this
  have hdom0 : ∀ a b : Nat, a ≤ b →
      147456 * ((b - a) * (b - a)) ≤ 4 * (192 * 192) →
      1 * ((b - a) * (b - a)) ≤ (a + b) * (a + b) →
      ef21Bin ((a : Rat) / (192 : Rat)) ((b : Rat) / (192 : Rat)) B ≤ M := by
    intro a b hab hA hC
    have hle := ef21_bin_le_frac a b 192 147456 1 B (by omega) (by omega) hA hC hab
    have hle' : ef21Bin ((a : Rat) / (192 : Rat)) ((b : Rat) / (192 : Rat)) B ≤ f0 := by
      simpa [f0, b1, Rat.one_mul] using hle
    exact Rat.le_trans hle' (rat_le_max_left f0 f14)
  have hdom14 : ∀ a b : Nat, a ≤ b →
      36 * ((b - a) * (b - a)) ≤ 4 * (192 * 192) →
      25 * ((b - a) * (b - a)) ≤ (a + b) * (a + b) →
      ef21Bin ((a : Rat) / (192 : Rat)) ((b : Rat) / (192 : Rat)) B ≤ M := by
    intro a b hab hA hC
    have hle := ef21_bin_le_frac a b 192 36 25 B (by omega) (by omega) hA hC hab
    have hle' : ef21Bin ((a : Rat) / (192 : Rat)) ((b : Rat) / (192 : Rat)) B ≤ f14 := by
      simpa [f14, b1] using hle
    exact Rat.le_trans hle' (rat_le_max_right f0 f14)
  have hL : unsignedFp4IntLevels 3 1 = [0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192] := rfl
  unfold ef21OneMinusAlpha uE3M1Levels normalizeLevels
  rw [hL]
  simp only [List.map, maxAdjacentBins]
  apply Rat.le_antisymm
  · repeat (first | apply rat_max_le | exact hM_nonneg
                  | (apply hdom0 <;> omega) | (apply hdom14 <;> omega))
  · apply rat_max_le
    · rw [← h0]; exact rat_le_max_left _ _
    · rw [← h14]
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      exact rat_le_max_left _ _

/-- Exact closed form of `ef21OneMinusAlpha uE4M0Levels B` for ALL `B : Nat`. -/
theorem ef21_uE4M0_exact (B : Nat) :
    ef21OneMinusAlpha uE4M0Levels B =
      max (((B - 1 : Nat) : Rat) / (1073741824 + ((B - 1 : Nat) : Rat)))
          (((B - 1 : Nat) : Rat) / (16 + 9 * ((B - 1 : Nat) : Rat))) := by
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  let f0 : Rat := b1 / (1073741824 + b1)
  let f14 : Rat := b1 / (16 + 9 * b1)
  let M := max f0 f14
  have hf0_nonneg : (0 : Rat) ≤ f0 :=
    rat_div_nonneg (rat_natCast_nonneg (B - 1))
      (rat_add_pos_of_pos_of_nonneg (by decide) (rat_natCast_nonneg (B - 1)))
  have hM_nonneg : (0 : Rat) ≤ M := Rat.le_trans hf0_nonneg (rat_le_max_left f0 f14)
  have h0 : ef21Bin (((0 : Nat) : Rat) / ((16384 : Nat) : Rat)) (((1 : Nat) : Rat) / ((16384 : Nat) : Rat)) B =
      ((B - 1 : Nat) : Rat) / (1073741824 + ((B - 1 : Nat) : Rat)) := by
    have := ef21Bin_scaled 0 1 16384 1073741824 1 B (by decide) (by grind) (by grind) (by grind) (by decide) (by decide)
    simpa [Rat.one_mul] using this
  have h14 : ef21Bin (((8192 : Nat) : Rat) / ((16384 : Nat) : Rat)) (((16384 : Nat) : Rat) / ((16384 : Nat) : Rat)) B =
      ((B - 1 : Nat) : Rat) / (16 + 9 * ((B - 1 : Nat) : Rat)) := by
    have := ef21Bin_scaled 8192 16384 16384 16 9 B (by decide) (by grind) (by grind) (by grind) (by decide) (by decide)
    simpa using this
  have hdom0 : ∀ a b : Nat, a ≤ b →
      1073741824 * ((b - a) * (b - a)) ≤ 4 * (16384 * 16384) →
      1 * ((b - a) * (b - a)) ≤ (a + b) * (a + b) →
      ef21Bin ((a : Rat) / (16384 : Rat)) ((b : Rat) / (16384 : Rat)) B ≤ M := by
    intro a b hab hA hC
    have hle := ef21_bin_le_frac a b 16384 1073741824 1 B (by omega) (by omega) hA hC hab
    have hle' : ef21Bin ((a : Rat) / (16384 : Rat)) ((b : Rat) / (16384 : Rat)) B ≤ f0 := by
      simpa [f0, b1, Rat.one_mul] using hle
    exact Rat.le_trans hle' (rat_le_max_left f0 f14)
  have hdom14 : ∀ a b : Nat, a ≤ b →
      16 * ((b - a) * (b - a)) ≤ 4 * (16384 * 16384) →
      9 * ((b - a) * (b - a)) ≤ (a + b) * (a + b) →
      ef21Bin ((a : Rat) / (16384 : Rat)) ((b : Rat) / (16384 : Rat)) B ≤ M := by
    intro a b hab hA hC
    have hle := ef21_bin_le_frac a b 16384 16 9 B (by omega) (by omega) hA hC hab
    have hle' : ef21Bin ((a : Rat) / (16384 : Rat)) ((b : Rat) / (16384 : Rat)) B ≤ f14 := by
      simpa [f14, b1] using hle
    exact Rat.le_trans hle' (rat_le_max_right f0 f14)
  have hL : unsignedFp4IntLevels 4 0 =
      [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384] := rfl
  unfold ef21OneMinusAlpha uE4M0Levels normalizeLevels
  rw [hL]
  simp only [List.map, maxAdjacentBins]
  apply Rat.le_antisymm
  · repeat (first | apply rat_max_le | exact hM_nonneg
                  | (apply hdom0 <;> omega) | (apply hdom14 <;> omega))
  · apply rat_max_le
    · rw [← h0]; exact rat_le_max_left _ _
    · rw [← h14]
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      exact rat_le_max_left _ _

/-- Exact closed form of `ef21OneMinusAlpha sE2M1Levels B` for ALL `B : Nat`. -/
theorem ef21_sE2M1_exact (B : Nat) :
    ef21OneMinusAlpha sE2M1Levels B =
      max (((B - 1 : Nat) : Rat) / (576 + ((B - 1 : Nat) : Rat)))
          (((B - 1 : Nat) : Rat) / (36 + 25 * ((B - 1 : Nat) : Rat))) := by
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  let f0 : Rat := b1 / (576 + b1)
  let f6 : Rat := b1 / (36 + 25 * b1)
  let M := max f0 f6
  have hf0_nonneg : (0 : Rat) ≤ f0 :=
    rat_div_nonneg (rat_natCast_nonneg (B - 1))
      (rat_add_pos_of_pos_of_nonneg (by decide) (rat_natCast_nonneg (B - 1)))
  have hM_nonneg : (0 : Rat) ≤ M := Rat.le_trans hf0_nonneg (rat_le_max_left f0 f6)
  have h0 : ef21Bin (((0 : Nat) : Rat) / ((12 : Nat) : Rat)) (((1 : Nat) : Rat) / ((12 : Nat) : Rat)) B =
      ((B - 1 : Nat) : Rat) / (576 + ((B - 1 : Nat) : Rat)) := by
    have := ef21Bin_scaled 0 1 12 576 1 B (by decide) (by grind) (by grind) (by grind) (by decide) (by decide)
    simpa [Rat.one_mul] using this
  have h6 : ef21Bin (((8 : Nat) : Rat) / ((12 : Nat) : Rat)) (((12 : Nat) : Rat) / ((12 : Nat) : Rat)) B =
      ((B - 1 : Nat) : Rat) / (36 + 25 * ((B - 1 : Nat) : Rat)) := by
    have := ef21Bin_scaled 8 12 12 36 25 B (by decide) (by grind) (by grind) (by grind) (by decide) (by decide)
    simpa using this
  have hdom0 : ∀ a b : Nat, a ≤ b →
      576 * ((b - a) * (b - a)) ≤ 4 * (12 * 12) →
      1 * ((b - a) * (b - a)) ≤ (a + b) * (a + b) →
      ef21Bin ((a : Rat) / (12 : Rat)) ((b : Rat) / (12 : Rat)) B ≤ M := by
    intro a b hab hA hC
    have hle := ef21_bin_le_frac a b 12 576 1 B (by omega) (by omega) hA hC hab
    have hle' : ef21Bin ((a : Rat) / (12 : Rat)) ((b : Rat) / (12 : Rat)) B ≤ f0 := by
      simpa [f0, b1, Rat.one_mul] using hle
    exact Rat.le_trans hle' (rat_le_max_left f0 f6)
  have hdom6 : ∀ a b : Nat, a ≤ b →
      36 * ((b - a) * (b - a)) ≤ 4 * (12 * 12) →
      25 * ((b - a) * (b - a)) ≤ (a + b) * (a + b) →
      ef21Bin ((a : Rat) / (12 : Rat)) ((b : Rat) / (12 : Rat)) B ≤ M := by
    intro a b hab hA hC
    have hle := ef21_bin_le_frac a b 12 36 25 B (by omega) (by omega) hA hC hab
    have hle' : ef21Bin ((a : Rat) / (12 : Rat)) ((b : Rat) / (12 : Rat)) B ≤ f6 := by
      simpa [f6, b1] using hle
    exact Rat.le_trans hle' (rat_le_max_right f0 f6)
  unfold ef21OneMinusAlpha sE2M1Levels normalizeLevels
  simp only [List.map, maxAdjacentBins]
  apply Rat.le_antisymm
  · repeat (first | apply rat_max_le | exact hM_nonneg
                  | (apply hdom0 <;> omega) | (apply hdom6 <;> omega))
  · apply rat_max_le
    · rw [← h0]; exact rat_le_max_left _ _
    · rw [← h6]
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      refine Rat.le_trans ?_ (rat_le_max_right _ _)
      exact rat_le_max_left _ _

/-! ### Complete All-`B` (`∀ B ≥ 2`) Regime Classification -/

private theorem regime_uE0M4 (B : Nat) (h1 : 2 ≤ B) (h2 : B ≤ 9) :
    ef21OneMinusAlpha uE0M4Levels B < ef21OneMinusAlpha uE2M2Levels B ∧
    ef21OneMinusAlpha uE0M4Levels B < ef21OneMinusAlpha uE3M1Levels B ∧
    ef21OneMinusAlpha uE0M4Levels B < ef21OneMinusAlpha uE4M0Levels B := by
  rw [ef21_uE0M4_exact, ef21_uE2M2_exact, ef21_uE3M1_exact, ef21_uE4M0_exact]
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  have hb1_pos : (0 : Rat) < b1 := rat_natCast_pos (by omega)
  have hb1_le8 : b1 ≤ ((8 : Nat) : Rat) := rat_natCast_le (by omega)
  have hD0 : (0 : Rat) < 900 + b1 := rat_add_pos (by decide) hb1_pos
  have hD2 : (0 : Rat) < 196 + 81 * b1 := rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  have hD3 : (0 : Rat) < 36 + 25 * b1 := rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  have hD4 : (0 : Rat) < 16 + 9 * b1 := rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  refine ⟨?_, ?_, ?_⟩
  · refine rat_lt_of_lt_of_le (ef21_frac_lt_of_denom_lt hb1_pos hD0 hD2 ?_) (rat_le_max_right _ _)
    have hmul : 80 * b1 ≤ 640 := by
      have := rat_mul_le_mul_of_nonneg_left hb1_le8 (by decide : (0 : Rat) ≤ 80)
      have eq : (80 : Rat) * ((8 : Nat) : Rat) = 640 := by grind
      rwa [eq] at this
    have hlt : 80 * b1 < 704 := rat_lt_of_le_of_lt hmul (by decide)
    apply rat_lt_of_sub_pos
    have eq : (900 + b1) - (196 + 81 * b1) = 704 - 80 * b1 := by grind
    rw [eq]; exact rat_sub_pos hlt
  · refine rat_lt_of_lt_of_le (ef21_frac_lt_of_denom_lt hb1_pos hD0 hD3 ?_) (rat_le_max_right _ _)
    have hmul : 24 * b1 ≤ 192 := by
      have := rat_mul_le_mul_of_nonneg_left hb1_le8 (by decide : (0 : Rat) ≤ 24)
      have eq : (24 : Rat) * ((8 : Nat) : Rat) = 192 := by grind
      rwa [eq] at this
    have hlt : 24 * b1 < 864 := rat_lt_of_le_of_lt hmul (by decide)
    apply rat_lt_of_sub_pos
    have eq : (900 + b1) - (36 + 25 * b1) = 864 - 24 * b1 := by grind
    rw [eq]; exact rat_sub_pos hlt
  · refine rat_lt_of_lt_of_le (ef21_frac_lt_of_denom_lt hb1_pos hD0 hD4 ?_) (rat_le_max_right _ _)
    have hmul : 8 * b1 ≤ 64 := by
      have := rat_mul_le_mul_of_nonneg_left hb1_le8 (by decide : (0 : Rat) ≤ 8)
      have eq : (8 : Rat) * ((8 : Nat) : Rat) = 64 := by grind
      rwa [eq] at this
    have hlt : 8 * b1 < 884 := rat_lt_of_le_of_lt hmul (by decide)
    apply rat_lt_of_sub_pos
    have eq : (900 + b1) - (16 + 9 * b1) = 884 - 8 * b1 := by grind
    rw [eq]; exact rat_sub_pos hlt

private theorem regime_uE2M2 (B : Nat) (h1 : 10 ≤ B) (h2 : B ≤ 130) :
    ef21OneMinusAlpha uE2M2Levels B < ef21OneMinusAlpha uE0M4Levels B ∧
    ef21OneMinusAlpha uE2M2Levels B < ef21OneMinusAlpha uE3M1Levels B ∧
    ef21OneMinusAlpha uE2M2Levels B < ef21OneMinusAlpha uE4M0Levels B := by
  rw [ef21_uE0M4_exact, ef21_uE2M2_exact, ef21_uE3M1_exact, ef21_uE4M0_exact]
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  have hb1_pos : (0 : Rat) < b1 := rat_natCast_pos (by omega)
  have hb1_ge9 : ((9 : Nat) : Rat) ≤ b1 := rat_natCast_le (by omega)
  have hb1_le129 : b1 ≤ ((129 : Nat) : Rat) := rat_natCast_le (by omega)
  have hD0 : (0 : Rat) < 900 + b1 := rat_add_pos (by decide) hb1_pos
  have hD2a : (0 : Rat) < 3136 + b1 := rat_add_pos (by decide) hb1_pos
  have hD2b : (0 : Rat) < 196 + 81 * b1 := rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  have hD3b : (0 : Rat) < 36 + 25 * b1 := rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  have hD4b : (0 : Rat) < 16 + 9 * b1 := rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  have hmax_lt : ∀ x y z : Rat, x < z → y < z → max x y < z := by
    intro x y z hx hy
    cases Rat.le_total (a := x) (b := y) with
    | inl h => rw [rat_max_eq_right h]; exact hy
    | inr h => rw [rat_max_eq_left h]; exact hx
  refine ⟨?_, ?_, ?_⟩
  · apply hmax_lt
    · apply ef21_frac_lt_of_denom_lt hb1_pos hD2a hD0
      apply rat_lt_of_sub_pos
      have eq : (3136 + b1) - (900 + b1) = 2236 := by grind
      rw [eq]; decide
    · apply ef21_frac_lt_of_denom_lt hb1_pos hD2b hD0
      have hmul : (720 : Rat) ≤ 80 * b1 := by
        have := rat_mul_le_mul_of_nonneg_left hb1_ge9 (by decide : (0 : Rat) ≤ 80)
        have eq : (80 : Rat) * ((9 : Nat) : Rat) = 720 := by grind
        rwa [eq] at this
      have hlt : (704 : Rat) < 80 * b1 := rat_lt_of_lt_of_le (by decide) hmul
      apply rat_lt_of_sub_pos
      have eq : (196 + 81 * b1) - (900 + b1) = 80 * b1 - 704 := by grind
      rw [eq]; exact rat_sub_pos hlt
  · apply hmax_lt
    · refine rat_lt_of_lt_of_le (ef21_frac_lt_of_denom_lt hb1_pos hD2a hD3b ?_) (rat_le_max_right _ _)
      have hmul : 24 * b1 ≤ 3096 := by
        have := rat_mul_le_mul_of_nonneg_left hb1_le129 (by decide : (0 : Rat) ≤ 24)
        have eq : (24 : Rat) * ((129 : Nat) : Rat) = 3096 := by grind
        rwa [eq] at this
      have hlt : 24 * b1 < 3100 := rat_lt_of_le_of_lt hmul (by decide)
      apply rat_lt_of_sub_pos
      have eq : (3136 + b1) - (36 + 25 * b1) = 3100 - 24 * b1 := by grind
      rw [eq]; exact rat_sub_pos hlt
    · refine rat_lt_of_lt_of_le (ef21_frac_lt_of_denom_lt hb1_pos hD2b hD3b ?_) (rat_le_max_right _ _)
      apply rat_lt_of_sub_pos
      have eq : (196 + 81 * b1) - (36 + 25 * b1) = 160 + 56 * b1 := by grind
      rw [eq]; exact rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  · apply hmax_lt
    · refine rat_lt_of_lt_of_le (ef21_frac_lt_of_denom_lt hb1_pos hD2a hD4b ?_) (rat_le_max_right _ _)
      have hmul : 8 * b1 ≤ 1032 := by
        have := rat_mul_le_mul_of_nonneg_left hb1_le129 (by decide : (0 : Rat) ≤ 8)
        have eq : (8 : Rat) * ((129 : Nat) : Rat) = 1032 := by grind
        rwa [eq] at this
      have hlt : 8 * b1 < 3120 := rat_lt_of_le_of_lt hmul (by decide)
      apply rat_lt_of_sub_pos
      have eq : (3136 + b1) - (16 + 9 * b1) = 3120 - 8 * b1 := by grind
      rw [eq]; exact rat_sub_pos hlt
    · refine rat_lt_of_lt_of_le (ef21_frac_lt_of_denom_lt hb1_pos hD2b hD4b ?_) (rat_le_max_right _ _)
      apply rat_lt_of_sub_pos
      have eq : (196 + 81 * b1) - (16 + 9 * b1) = 180 + 72 * b1 := by grind
      rw [eq]; exact rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)

private theorem regime_uE3M1 (B : Nat) (h1 : 131 ≤ B) (h2 : B ≤ 18431) :
    ef21OneMinusAlpha uE3M1Levels B < ef21OneMinusAlpha uE0M4Levels B ∧
    ef21OneMinusAlpha uE3M1Levels B < ef21OneMinusAlpha uE2M2Levels B ∧
    ef21OneMinusAlpha uE3M1Levels B ≤ ef21OneMinusAlpha uE4M0Levels B := by
  rw [ef21_uE0M4_exact, ef21_uE2M2_exact, ef21_uE3M1_exact, ef21_uE4M0_exact]
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  have hb1_pos : (0 : Rat) < b1 := rat_natCast_pos (by omega)
  have hb1_ge130 : ((130 : Nat) : Rat) ≤ b1 := rat_natCast_le (by omega)
  have hb1_le18430 : b1 ≤ ((18430 : Nat) : Rat) := rat_natCast_le (by omega)
  have hD0 : (0 : Rat) < 900 + b1 := rat_add_pos (by decide) hb1_pos
  have hD2a : (0 : Rat) < 3136 + b1 := rat_add_pos (by decide) hb1_pos
  have hD3a : (0 : Rat) < 147456 + b1 := rat_add_pos (by decide) hb1_pos
  have hD3b : (0 : Rat) < 36 + 25 * b1 := rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  have hD4b : (0 : Rat) < 16 + 9 * b1 := rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  have hmax_lt : ∀ x y z : Rat, x < z → y < z → max x y < z := by
    intro x y z hx hy
    cases Rat.le_total (a := x) (b := y) with
    | inl h => rw [rat_max_eq_right h]; exact hy
    | inr h => rw [rat_max_eq_left h]; exact hx
  refine ⟨?_, ?_, ?_⟩
  · apply hmax_lt
    · apply ef21_frac_lt_of_denom_lt hb1_pos hD3a hD0
      apply rat_lt_of_sub_pos
      have eq : (147456 + b1) - (900 + b1) = 146556 := by grind
      rw [eq]; decide
    · apply ef21_frac_lt_of_denom_lt hb1_pos hD3b hD0
      have hmul : (3120 : Rat) ≤ 24 * b1 := by
        have := rat_mul_le_mul_of_nonneg_left hb1_ge130 (by decide : (0 : Rat) ≤ 24)
        have eq : (24 : Rat) * ((130 : Nat) : Rat) = 3120 := by grind
        rwa [eq] at this
      have hlt : (864 : Rat) < 24 * b1 := rat_lt_of_lt_of_le (by decide) hmul
      apply rat_lt_of_sub_pos
      have eq : (36 + 25 * b1) - (900 + b1) = 24 * b1 - 864 := by grind
      rw [eq]; exact rat_sub_pos hlt
  · apply hmax_lt
    · refine rat_lt_of_lt_of_le (ef21_frac_lt_of_denom_lt hb1_pos hD3a hD2a ?_) (rat_le_max_left _ _)
      apply rat_lt_of_sub_pos
      have eq : (147456 + b1) - (3136 + b1) = 144320 := by grind
      rw [eq]; decide
    · refine rat_lt_of_lt_of_le (ef21_frac_lt_of_denom_lt hb1_pos hD3b hD2a ?_) (rat_le_max_left _ _)
      have hmul : (3120 : Rat) ≤ 24 * b1 := by
        have := rat_mul_le_mul_of_nonneg_left hb1_ge130 (by decide : (0 : Rat) ≤ 24)
        have eq : (24 : Rat) * ((130 : Nat) : Rat) = 3120 := by grind
        rwa [eq] at this
      have hlt : (3100 : Rat) < 24 * b1 := rat_lt_of_lt_of_le (by decide) hmul
      apply rat_lt_of_sub_pos
      have eq : (36 + 25 * b1) - (3136 + b1) = 24 * b1 - 3100 := by grind
      rw [eq]; exact rat_sub_pos hlt
  · apply rat_max_le
    · refine Rat.le_trans (ef21_frac_le_of_denom_le (Rat.le_of_lt hb1_pos) hD3a hD4b ?_) (rat_le_max_right _ _)
      have hmul : 8 * b1 ≤ 147440 := by
        have := rat_mul_le_mul_of_nonneg_left hb1_le18430 (by decide : (0 : Rat) ≤ 8)
        have eq : (8 : Rat) * ((18430 : Nat) : Rat) = 147440 := by grind
        rwa [eq] at this
      apply rat_le_of_sub_nonneg
      have eq : (147456 + b1) - (16 + 9 * b1) = 147440 - 8 * b1 := by grind
      rw [eq]; exact rat_sub_nonneg hmul
    · refine Rat.le_trans (ef21_frac_le_of_denom_le (Rat.le_of_lt hb1_pos) hD3b hD4b ?_) (rat_le_max_right _ _)
      apply rat_le_of_sub_nonneg
      have eq : (36 + 25 * b1) - (16 + 9 * b1) = 20 + 16 * b1 := by grind
      rw [eq]; exact Rat.le_of_lt (rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos))

private theorem regime_uE4M0 (B : Nat) (h1 : 18432 ≤ B) :
    ef21OneMinusAlpha uE4M0Levels B < ef21OneMinusAlpha uE0M4Levels B ∧
    ef21OneMinusAlpha uE4M0Levels B < ef21OneMinusAlpha uE2M2Levels B ∧
    ef21OneMinusAlpha uE4M0Levels B < ef21OneMinusAlpha uE3M1Levels B := by
  rw [ef21_uE0M4_exact, ef21_uE2M2_exact, ef21_uE3M1_exact, ef21_uE4M0_exact]
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  have hb1_pos : (0 : Rat) < b1 := rat_natCast_pos (by omega)
  have hb1_ge : ((18431 : Nat) : Rat) ≤ b1 := rat_natCast_le (by omega)
  have hD0 : (0 : Rat) < 900 + b1 := rat_add_pos (by decide) hb1_pos
  have hD2a : (0 : Rat) < 3136 + b1 := rat_add_pos (by decide) hb1_pos
  have hD3a : (0 : Rat) < 147456 + b1 := rat_add_pos (by decide) hb1_pos
  have hD4a : (0 : Rat) < 1073741824 + b1 := rat_add_pos (by decide) hb1_pos
  have hD4b : (0 : Rat) < 16 + 9 * b1 := rat_add_pos (by decide) (rat_mul_pos (by decide) hb1_pos)
  have hmax_lt : ∀ x y z : Rat, x < z → y < z → max x y < z := by
    intro x y z hx hy
    cases Rat.le_total (a := x) (b := y) with
    | inl h => rw [rat_max_eq_right h]; exact hy
    | inr h => rw [rat_max_eq_left h]; exact hx
  have hlt3a : max (b1 / (1073741824 + b1)) (b1 / (16 + 9 * b1)) < b1 / (147456 + b1) := by
    apply hmax_lt
    · apply ef21_frac_lt_of_denom_lt hb1_pos hD4a hD3a
      apply rat_lt_of_sub_pos
      have eq : (1073741824 + b1) - (147456 + b1) = 1073594368 := by grind
      rw [eq]; decide
    · apply ef21_frac_lt_of_denom_lt hb1_pos hD4b hD3a
      have hmul : (147448 : Rat) ≤ 8 * b1 := by
        have := rat_mul_le_mul_of_nonneg_left hb1_ge (by decide : (0 : Rat) ≤ 8)
        have eq : (8 : Rat) * ((18431 : Nat) : Rat) = 147448 := by grind
        rwa [eq] at this
      have hlt : (147440 : Rat) < 8 * b1 := rat_lt_of_lt_of_le (by decide) hmul
      apply rat_lt_of_sub_pos
      have eq : (16 + 9 * b1) - (147456 + b1) = 8 * b1 - 147440 := by grind
      rw [eq]; exact rat_sub_pos hlt
  have h3a_lt_2a : b1 / (147456 + b1) < b1 / (3136 + b1) := by
    apply ef21_frac_lt_of_denom_lt hb1_pos hD3a hD2a
    apply rat_lt_of_sub_pos
    have eq : (147456 + b1) - (3136 + b1) = 144320 := by grind
    rw [eq]; decide
  have h2a_lt_0 : b1 / (3136 + b1) < b1 / (900 + b1) := by
    apply ef21_frac_lt_of_denom_lt hb1_pos hD2a hD0
    apply rat_lt_of_sub_pos
    have eq : (3136 + b1) - (900 + b1) = 2236 := by grind
    rw [eq]; decide
  refine ⟨?_, ?_, ?_⟩
  · exact rat_lt_of_lt_of_le (rat_lt_of_lt_of_le hlt3a (Rat.le_of_lt h3a_lt_2a)) (Rat.le_of_lt h2a_lt_0)
  · exact rat_lt_of_lt_of_le (rat_lt_of_lt_of_le hlt3a (Rat.le_of_lt h3a_lt_2a)) (rat_le_max_left _ _)
  · exact rat_lt_of_lt_of_le hlt3a (rat_le_max_left _ _)

private theorem rat_lt_of_nat_mul_lt {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d < c * b) : ((a : Rat) / (b : Rat)) < ((c : Rat) / (d : Rat)) := by
  apply rat_div_lt_div_of_cross (rat_natCast_pos hb) (rat_natCast_pos hd)
  have h1 := rat_natCast_lt h
  simpa only [Rat.natCast_mul] using h1

private theorem rat_le_of_nat_mul_le {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : ((a : Rat) / (b : Rat)) ≤ ((c : Rat) / (d : Rat)) := by
  apply rat_div_le_div_of_cross (rat_natCast_pos hb) (rat_natCast_pos hd)
  have h1 := rat_natCast_le h
  simpa only [Rat.natCast_mul] using h1

/-- Headline Theorem 2: Universal EF21 contraction law, complete all-`B ≥ 2` unsigned 4-bit
    regime classification, exact boundary tie at `B = 18431`, and exact improvement ratios over
    signed `S-E2M1` at `B ∈ {64, 256, 1024}`. -/
theorem unsigned_fp4_all_b_ef21_regime_classification :
    (∀ (B : Nat) (_ : 2 ≤ B) (C : Rat) (x e : Fin (B - 1) → Rat),
      (∀ j : Fin (B - 1), ∃ u0 u1 : Rat,
        (0 : Rat) ≤ u0 ∧ u0 ≤ x j ∧ x j ≤ u1 ∧
        e j = rtnDist u0 u1 (x j) ∧ ef21Bin u0 u1 B ≤ C) →
      sumFin (fun j => e j * e j) / (1 + sumFin (fun j => x j * x j)) ≤ C) ∧
    (∀ (B : Nat) (u0 u1 : Rat),
      let h := (u1 - u0) / 2
      let m := (u0 + u1) / 2
      sumFin (fun _ : Fin (B - 1) => h * h) / (1 + sumFin (fun _ : Fin (B - 1) => m * m)) =
        ef21Bin u0 u1 B) ∧
    (∀ B : Nat, 2 ≤ B → B ≤ 9 →
      ef21OneMinusAlpha uE0M4Levels B < ef21OneMinusAlpha uE2M2Levels B ∧
      ef21OneMinusAlpha uE0M4Levels B < ef21OneMinusAlpha uE3M1Levels B ∧
      ef21OneMinusAlpha uE0M4Levels B < ef21OneMinusAlpha uE4M0Levels B) ∧
    (∀ B : Nat, 10 ≤ B → B ≤ 130 →
      ef21OneMinusAlpha uE2M2Levels B < ef21OneMinusAlpha uE0M4Levels B ∧
      ef21OneMinusAlpha uE2M2Levels B < ef21OneMinusAlpha uE3M1Levels B ∧
      ef21OneMinusAlpha uE2M2Levels B < ef21OneMinusAlpha uE4M0Levels B) ∧
    (∀ B : Nat, 131 ≤ B → B ≤ 18431 →
      ef21OneMinusAlpha uE3M1Levels B < ef21OneMinusAlpha uE0M4Levels B ∧
      ef21OneMinusAlpha uE3M1Levels B < ef21OneMinusAlpha uE2M2Levels B ∧
      ef21OneMinusAlpha uE3M1Levels B ≤ ef21OneMinusAlpha uE4M0Levels B) ∧
    (ef21OneMinusAlpha uE3M1Levels 18431 = ef21OneMinusAlpha uE4M0Levels 18431) ∧
    (∀ B : Nat, 18432 ≤ B →
      ef21OneMinusAlpha uE4M0Levels B < ef21OneMinusAlpha uE0M4Levels B ∧
      ef21OneMinusAlpha uE4M0Levels B < ef21OneMinusAlpha uE2M2Levels B ∧
      ef21OneMinusAlpha uE4M0Levels B < ef21OneMinusAlpha uE3M1Levels B) ∧
    ((ef21OneMinusAlpha sE2M1Levels 64 = 7 / 71 ∧
      ef21OneMinusAlpha uE2M2Levels 64 = 9 / 457 ∧
      (5 : Rat) < ef21OneMinusAlpha sE2M1Levels 64 / ef21OneMinusAlpha uE2M2Levels 64) ∧
     (ef21OneMinusAlpha sE2M1Levels 256 = 85 / 277 ∧
      ef21OneMinusAlpha uE3M1Levels 256 = 85 / 2137 ∧
      (77 / 10 : Rat) < ef21OneMinusAlpha sE2M1Levels 256 / ef21OneMinusAlpha uE3M1Levels 256) ∧
     (ef21OneMinusAlpha sE2M1Levels 1024 = 341 / 533 ∧
      ef21OneMinusAlpha uE3M1Levels 1024 = 341 / 8537 ∧
      (16 : Rat) < ef21OneMinusAlpha sE2M1Levels 1024 / ef21OneMinusAlpha uE3M1Levels 1024)) := by
  refine ⟨fun B hB C x e hc => ef21_vector_upper_bound hB x e hc,
          fun B u0 u1 => ef21_midpoint_attainment u0 u1,
          regime_uE0M4, regime_uE2M2, regime_uE3M1, ?_, regime_uE4M0, ?_⟩
  · rw [ef21_uE3M1_exact, ef21_uE4M0_exact]
    have hL : ((18431 - 1 : Nat) : Rat) / (36 + 25 * ((18431 - 1 : Nat) : Rat)) ≤
              ((18431 - 1 : Nat) : Rat) / (147456 + ((18431 - 1 : Nat) : Rat)) := by
      have eq1 : (36 : Rat) + 25 * ((18431 - 1 : Nat) : Rat) = (460786 : Nat) := by grind
      have eq2 : (147456 : Rat) + ((18431 - 1 : Nat) : Rat) = (165886 : Nat) := by grind
      rw [eq1, eq2]; exact rat_le_of_nat_mul_le (by omega) (by omega) (by omega)
    have hR : ((18431 - 1 : Nat) : Rat) / (1073741824 + ((18431 - 1 : Nat) : Rat)) ≤
              ((18431 - 1 : Nat) : Rat) / (16 + 9 * ((18431 - 1 : Nat) : Rat)) := by
      have eq1 : (1073741824 : Rat) + ((18431 - 1 : Nat) : Rat) = (1073760254 : Nat) := by grind
      have eq2 : (16 : Rat) + 9 * ((18431 - 1 : Nat) : Rat) = (165886 : Nat) := by grind
      rw [eq1, eq2]; exact rat_le_of_nat_mul_le (by omega) (by omega) (by omega)
    rw [rat_max_eq_left hL, rat_max_eq_right hR]
    grind
  · refine ⟨?_, ?_, ?_⟩
    · have hs : ef21OneMinusAlpha sE2M1Levels 64 = 7 / 71 := by
        rw [ef21_sE2M1_exact]
        have hle : ((64 - 1 : Nat) : Rat) / (36 + 25 * ((64 - 1 : Nat) : Rat)) ≤
                   ((64 - 1 : Nat) : Rat) / (576 + ((64 - 1 : Nat) : Rat)) := by
          have eq1 : (36 : Rat) + 25 * ((64 - 1 : Nat) : Rat) = (1611 : Nat) := by grind
          have eq2 : (576 : Rat) + ((64 - 1 : Nat) : Rat) = (639 : Nat) := by grind
          rw [eq1, eq2]; exact rat_le_of_nat_mul_le (by omega) (by omega) (by omega)
        rw [rat_max_eq_left hle]; grind
      have hu : ef21OneMinusAlpha uE2M2Levels 64 = 9 / 457 := by
        rw [ef21_uE2M2_exact]
        have hle : ((64 - 1 : Nat) : Rat) / (196 + 81 * ((64 - 1 : Nat) : Rat)) ≤
                   ((64 - 1 : Nat) : Rat) / (3136 + ((64 - 1 : Nat) : Rat)) := by
          have eq1 : (196 : Rat) + 81 * ((64 - 1 : Nat) : Rat) = (5299 : Nat) := by grind
          have eq2 : (3136 : Rat) + ((64 - 1 : Nat) : Rat) = (3199 : Nat) := by grind
          rw [eq1, eq2]; exact rat_le_of_nat_mul_le (by omega) (by omega) (by omega)
        rw [rat_max_eq_left hle]; grind
      refine ⟨hs, hu, ?_⟩
      rw [hs, hu]
      have eq : (7 / 71 : Rat) / (9 / 457) = (3199 : Nat) / (639 : Nat) := by grind
      have eq5 : (5 : Rat) = (5 : Nat) / (1 : Nat) := by grind
      rw [eq, eq5]
      exact rat_lt_of_nat_mul_lt (by omega) (by omega) (by omega)
    · have hs : ef21OneMinusAlpha sE2M1Levels 256 = 85 / 277 := by
        rw [ef21_sE2M1_exact]
        have hle : ((256 - 1 : Nat) : Rat) / (36 + 25 * ((256 - 1 : Nat) : Rat)) ≤
                   ((256 - 1 : Nat) : Rat) / (576 + ((256 - 1 : Nat) : Rat)) := by
          have eq1 : (36 : Rat) + 25 * ((256 - 1 : Nat) : Rat) = (6411 : Nat) := by grind
          have eq2 : (576 : Rat) + ((256 - 1 : Nat) : Rat) = (831 : Nat) := by grind
          rw [eq1, eq2]; exact rat_le_of_nat_mul_le (by omega) (by omega) (by omega)
        rw [rat_max_eq_left hle]; grind
      have hu : ef21OneMinusAlpha uE3M1Levels 256 = 85 / 2137 := by
        rw [ef21_uE3M1_exact]
        have hle : ((256 - 1 : Nat) : Rat) / (147456 + ((256 - 1 : Nat) : Rat)) ≤
                   ((256 - 1 : Nat) : Rat) / (36 + 25 * ((256 - 1 : Nat) : Rat)) := by
          have eq1 : (147456 : Rat) + ((256 - 1 : Nat) : Rat) = (147711 : Nat) := by grind
          have eq2 : (36 : Rat) + 25 * ((256 - 1 : Nat) : Rat) = (6411 : Nat) := by grind
          rw [eq1, eq2]; exact rat_le_of_nat_mul_le (by omega) (by omega) (by omega)
        rw [rat_max_eq_right hle]; grind
      refine ⟨hs, hu, ?_⟩
      rw [hs, hu]
      have eq : (85 / 277 : Rat) / (85 / 2137) = (2137 : Nat) / (277 : Nat) := by grind
      have eq77 : (77 / 10 : Rat) = (77 : Nat) / (10 : Nat) := by grind
      rw [eq, eq77]
      exact rat_lt_of_nat_mul_lt (by omega) (by omega) (by omega)
    · have hs : ef21OneMinusAlpha sE2M1Levels 1024 = 341 / 533 := by
        rw [ef21_sE2M1_exact]
        have hle : ((1024 - 1 : Nat) : Rat) / (36 + 25 * ((1024 - 1 : Nat) : Rat)) ≤
                   ((1024 - 1 : Nat) : Rat) / (576 + ((1024 - 1 : Nat) : Rat)) := by
          have eq1 : (36 : Rat) + 25 * ((1024 - 1 : Nat) : Rat) = (25611 : Nat) := by grind
          have eq2 : (576 : Rat) + ((1024 - 1 : Nat) : Rat) = (1599 : Nat) := by grind
          rw [eq1, eq2]; exact rat_le_of_nat_mul_le (by omega) (by omega) (by omega)
        rw [rat_max_eq_left hle]; grind
      have hu : ef21OneMinusAlpha uE3M1Levels 1024 = 341 / 8537 := by
        rw [ef21_uE3M1_exact]
        have hle : ((1024 - 1 : Nat) : Rat) / (147456 + ((1024 - 1 : Nat) : Rat)) ≤
                   ((1024 - 1 : Nat) : Rat) / (36 + 25 * ((1024 - 1 : Nat) : Rat)) := by
          have eq1 : (147456 : Rat) + ((1024 - 1 : Nat) : Rat) = (148479 : Nat) := by grind
          have eq2 : (36 : Rat) + 25 * ((1024 - 1 : Nat) : Rat) = (25611 : Nat) := by grind
          rw [eq1, eq2]; exact rat_le_of_nat_mul_le (by omega) (by omega) (by omega)
        rw [rat_max_eq_right hle]; grind
      refine ⟨hs, hu, ?_⟩
      rw [hs, hu]
      have eq : (341 / 533 : Rat) / (341 / 8537) = (8537 : Nat) / (533 : Nat) := by grind
      have eq16 : (16 : Rat) = (16 : Nat) / (1 : Nat) := by grind
      rw [eq, eq16]
      exact rat_lt_of_nat_mul_lt (by omega) (by omega) (by omega)

end UnsignedFp4SoftmaxV
