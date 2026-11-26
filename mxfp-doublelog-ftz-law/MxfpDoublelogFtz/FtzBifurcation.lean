/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxfpDoublelogFtz.Ef21Envelopes

/-!
# Theorems 5 & 6: Exact `FTZ` `4^b` Underflow Penalty & Hardware Bifurcation (`E4M3` vs `E2M_b`)

Proves:
- **Theorem 5 (`mxfp_ftz_four_to_the_b_underflow_penalty`):**
  Flushing subnormals to zero (`FTZ`) jumps the smallest positive representable grid value
  from `1` to `2^b`, multiplying worst-case underflow squared error by exact factor `4^b`
  (`4×, 16×, 64×, 256×, 1024×` for `b = 1, 2, 3, 4, 5`). Proves the exact closed-form
  EF21 underflow ratio `R_cont(M, b, B) = 4^b * (4*M^2 + k) / (4*M^2 + 4^b * k)` and
  its exact gap identity `4^b - R_cont(M, b, B) = 4^b * (4^b - 1) * k / (4*M^2 + 4^b * k)`,
  showing `R_cont` approaches `4^b` arbitrarily closely in the large-dynamic-range regime.

- **Theorem 6 (`mxfp_ftz_hardware_bifurcation_e4m3_vs_e2mb`):**
  Proves `W8_E4M3_OCP` (`a = 4, b = 3`, `M = 229376`) suffers **EXACT ZERO** worst-case
  continuous-scale EF21 penalty from `FTZ` for ALL `1 ≤ B ≤ 11,417,825` (with exact first
  penalty at `B = 11,417,826`), whereas every optimal `a = 2` microscaling format
  (`E2M1, E2M2, E2M3, E2M4, E2M5`) hits `> 2×` worst-case MSE penalty already at `B ≤ 12`
  (and `B ≤ 5` under OCP E8M0).
-/

namespace MxfpDoublelogFtz

/-! ## Theorem 5: Exact `4^b` Underflow Penalty -/

theorem pow2_sq_eq_pow4 (b : Nat) : 2 ^ b * 2 ^ b = 4 ^ b := by
  induction b with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    have h4 : 4 = 2 * 2 := by decide
    have : 2 ^ n * 2 * (2 ^ n * 2) = (2 ^ n * 2 ^ n) * 4 := by grind
    rw [this, ih]

theorem ftzContUfRatio_closed_form {M b B : Nat} (hM : 0 < M) (hB : 2 ≤ B) :
    ftzContUfRatio M b B =
      ((4 ^ b : Nat) : Rat) * (4 * ((M * M : Nat) : Rat) + ((B - 1 : Nat) : Rat)) /
        (4 * ((M * M : Nat) : Rat) + ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat)) := by
  unfold ftzContUfRatio deltaContUf
  have hsq : ((2 ^ b * 2 ^ b : Nat) : Rat) = ((4 ^ b : Nat) : Rat) := by
    rw [pow2_sq_eq_pow4]
  have h1sq : ((1 * 1 : Nat) : Rat) = 1 := by decide
  rw [hsq, h1sq]
  have hk_pos : (0 : Rat) < ((B - 1 : Nat) : Rat) := natCast_pos (by omega)
  have hm2_pos : (0 : Rat) < ((M * M : Nat) : Rat) := natCast_pos (Nat.mul_pos hM hM)
  have h4b_pos : (0 : Rat) < ((4 ^ b : Nat) : Rat) := natCast_pos (Nat.pow_pos (by decide : 0 < 4))
  have hd_ftz : (0 : Rat) < 4 * ((M * M : Nat) : Rat) + ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat) :=
    rat_add_pos (rat_mul_pos (by decide : (0 : Rat) < 4) hm2_pos) (rat_mul_pos h4b_pos hk_pos)
  have hd_gu : (0 : Rat) < 4 * ((M * M : Nat) : Rat) + 1 * ((B - 1 : Nat) : Rat) :=
    rat_add_pos (rat_mul_pos (by decide : (0 : Rat) < 4) hm2_pos) (rat_mul_pos (by decide : (0 : Rat) < 1) hk_pos)
  have hgu_pos : (0 : Rat) < (1 * ((B - 1 : Nat) : Rat)) / (4 * ((M * M : Nat) : Rat) + 1 * ((B - 1 : Nat) : Rat)) :=
    rat_div_pos (rat_mul_pos (by decide : (0 : Rat) < 1) hk_pos) hd_gu
  rw [rat_div_eq_div_iff (Rat.ne_of_gt hgu_pos) (Rat.ne_of_gt hd_ftz)]
  have hinv_ftz := Rat.mul_inv_cancel _ (Rat.ne_of_gt hd_ftz)
  have hinv_gu := Rat.mul_inv_cancel _ (Rat.ne_of_gt hd_gu)
  rw [Rat.div_def, Rat.div_def]
  grind

theorem ftzContUfRatio_gap_identity {M b B : Nat} (hM : 0 < M) (hB : 2 ≤ B) :
    ((4 ^ b : Nat) : Rat) - ftzContUfRatio M b B =
      ((4 ^ b : Nat) : Rat) * (((4 ^ b : Nat) : Rat) - 1) * ((B - 1 : Nat) : Rat) /
        (4 * ((M * M : Nat) : Rat) + ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat)) := by
  rw [ftzContUfRatio_closed_form hM hB]
  have hk_pos : (0 : Rat) < ((B - 1 : Nat) : Rat) := natCast_pos (by omega)
  have hm2_pos : (0 : Rat) < ((M * M : Nat) : Rat) := natCast_pos (Nat.mul_pos hM hM)
  have h4b_pos : (0 : Rat) < ((4 ^ b : Nat) : Rat) := natCast_pos (Nat.pow_pos (by decide : 0 < 4))
  have hd_ftz : (0 : Rat) < 4 * ((M * M : Nat) : Rat) + ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat) :=
    rat_add_pos (rat_mul_pos (by decide : (0 : Rat) < 4) hm2_pos) (rat_mul_pos h4b_pos hk_pos)
  have hinv := Rat.mul_inv_cancel _ (Rat.ne_of_gt hd_ftz)
  rw [Rat.div_def, Rat.div_def]
  grind

theorem ftzContUfRatio_bounds {M b B : Nat} (hM : 0 < M) (hB : 2 ≤ B) :
    ftzContUfRatio M b B ≤ ((4 ^ b : Nat) : Rat) ∧
    (∀ ε : Rat, (0 : Rat) < ε →
      ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat) < ε * (4 * ((M * M : Nat) : Rat)) →
      ((4 ^ b : Nat) : Rat) * (1 - ε) < ftzContUfRatio M b B) := by
  have hk_pos : (0 : Rat) < ((B - 1 : Nat) : Rat) := natCast_pos (by omega)
  have hm2_pos : (0 : Rat) < ((M * M : Nat) : Rat) := natCast_pos (Nat.mul_pos hM hM)
  have h4b_pos : (0 : Rat) < ((4 ^ b : Nat) : Rat) := natCast_pos (Nat.pow_pos (by decide : 0 < 4))
  have h4b_ge1 : (1 : Rat) ≤ ((4 ^ b : Nat) : Rat) :=
    (natCast_le_iff 1 (4 ^ b)).mpr (Nat.pow_pos (by decide : 0 < 4))
  have hd_ftz : (0 : Rat) < 4 * ((M * M : Nat) : Rat) + ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat) :=
    rat_add_pos (rat_mul_pos (by decide : (0 : Rat) < 4) hm2_pos) (rat_mul_pos h4b_pos hk_pos)
  constructor
  · apply rat_le_of_sub_nonneg
    rw [ftzContUfRatio_gap_identity hM hB]
    exact rat_div_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt h4b_pos) (rat_sub_nonneg h4b_ge1)) (Rat.le_of_lt hk_pos))
      hd_ftz
  · intro ε _hε hsmall
    rw [ftzContUfRatio_closed_form hM hB]
    have h1 : ((4 ^ b : Nat) : Rat) * (1 - ε) = (((4 ^ b : Nat) : Rat) * (1 - ε)) / 1 := by grind
    rw [h1, rat_div_lt_div_iff (by decide : (0 : Rat) < 1) hd_ftz]
    apply rat_lt_of_sub_pos
    have hident : ((4 ^ b : Nat) : Rat) * (4 * ((M * M : Nat) : Rat) + ((B - 1 : Nat) : Rat)) * 1 -
        ((4 ^ b : Nat) : Rat) * (1 - ε) *
          (4 * ((M * M : Nat) : Rat) + ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat)) =
        ((4 ^ b : Nat) : Rat) *
          ((ε * (4 * ((M * M : Nat) : Rat)) - ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat)) +
            ((B - 1 : Nat) : Rat) + ε * (((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat))) := by
      grind
    rw [hident]
    have hpos1 : (0 : Rat) < ε * (4 * ((M * M : Nat) : Rat)) - ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat) :=
      rat_sub_pos hsmall
    have hpos2 : (0 : Rat) ≤ ε * (((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat)) :=
      Rat.mul_nonneg (Rat.le_of_lt _hε) (Rat.mul_nonneg (Rat.le_of_lt h4b_pos) (Rat.le_of_lt hk_pos))
    exact rat_mul_pos h4b_pos (rat_add_pos_of_pos_of_nonneg (rat_add_pos hpos1 hk_pos) hpos2)

/-- **Headline Theorem 5:** Exact `4^b` underflow squared-error penalty of `FTZ` vs gradual underflow. -/
theorem mxfp_ftz_four_to_the_b_underflow_penalty :
    (∀ a b : Nat, 1 ≤ a →
      mxfpMinPosInt a b false = 1 ∧
      mxfpMinPosInt a b true = 2 ^ b ∧
      mxfpMinPosInt a b true * mxfpMinPosInt a b true =
        4 ^ b * (mxfpMinPosInt a b false * mxfpMinPosInt a b false)) ∧
    (∀ M b B : Nat, 0 < M → 2 ≤ B →
      ftzContUfRatio M b B =
        ((4 ^ b : Nat) : Rat) * (4 * ((M * M : Nat) : Rat) + ((B - 1 : Nat) : Rat)) /
          (4 * ((M * M : Nat) : Rat) + ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat)) ∧
      ((4 ^ b : Nat) : Rat) - ftzContUfRatio M b B =
        ((4 ^ b : Nat) : Rat) * (((4 ^ b : Nat) : Rat) - 1) * ((B - 1 : Nat) : Rat) /
          (4 * ((M * M : Nat) : Rat) + ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat)) ∧
      ftzContUfRatio M b B ≤ ((4 ^ b : Nat) : Rat) ∧
      (∀ ε : Rat, (0 : Rat) < ε →
        ((4 ^ b : Nat) : Rat) * ((B - 1 : Nat) : Rat) < ε * (4 * ((M * M : Nat) : Rat)) →
        ((4 ^ b : Nat) : Rat) * (1 - ε) < ftzContUfRatio M b B)) ∧
    (4 ^ 1 = 4 ∧ 4 ^ 2 = 16 ∧ 4 ^ 3 = 64 ∧ 4 ^ 4 = 256 ∧ 4 ^ 5 = 1024) := by
  refine ⟨?_, ?_, by decide⟩
  · intro a b ha
    have hne : a ≠ 0 := by omega
    unfold mxfpMinPosInt
    simp only [hne, Bool.not_false, Bool.not_true]
    refine ⟨rfl, rfl, ?_⟩
    simpa [Nat.mul_one] using pow2_sq_eq_pow4 b
  · intro M b B hM hB
    have hb := ftzContUfRatio_bounds (b := b) hM hB
    exact ⟨ftzContUfRatio_closed_form hM hB, ftzContUfRatio_gap_identity hM hB, hb.1, hb.2⟩

/-! ## Theorem 6: Exact `FTZ` Hardware Bifurcation (`W8_E4M3_OCP` vs `E2M1..E2M5`) -/

/-- Exact ZERO worst-case Continuous-scale EF21 penalty of `FTZ` on `W8_E4M3_OCP`
for ALL `1 ≤ B ≤ 11,417,825`. -/
theorem ocpE4m3_ftz_exact_zero_penalty (B : Nat) (hB1 : 1 ≤ B) (hBmax : B ≤ 11417825) :
    deltaContOcpE4m3 true B = deltaContOcpE4m3 false B := by
  unfold deltaContOcpE4m3
  simp only [↓reduceIte, Bool.false_eq_true]
  by_cases h1 : B = 1
  · subst h1
    unfold deltaContNormOcpE4m3 deltaContUf ocpE4m3MaxInt
    have h0 : ((1 - 1 : Nat) : Rat) = 0 := by decide
    rw [h0]
    have hnorm : (0 : Rat) / (4 * 14 * 14 + 0 * 17 * 17) = 0 := by grind
    have huf8 : (((8 * 8 : Nat) : Rat) * 0) /
        (4 * (((14 * 2 ^ 14) * (14 * 2 ^ 14) : Nat) : Rat) + ((8 * 8 : Nat) : Rat) * 0) = 0 := by
      grind
    have huf1 : (((1 * 1 : Nat) : Rat) * 0) /
        (4 * (((14 * 2 ^ 14) * (14 * 2 ^ 14) : Nat) : Rat) + ((1 * 1 : Nat) : Rat) * 0) = 0 := by
      grind
    rw [hnorm, huf8, huf1]
  · have hB2 : 2 ≤ B := by omega
    have h784 : (0 : Rat) < 4 * 14 * 14 :=
      rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 4) (by decide : (0 : Rat) < 14))
        (by decide : (0 : Rat) < 14)
    have hden_norm : (0 : Rat) < 4 * 14 * 14 + ((B - 1 : Nat) : Rat) * 17 * 17 :=
      rat_add_pos_of_pos_of_nonneg h784
        (Rat.mul_nonneg (Rat.mul_nonneg (natCast_nonneg _) (by decide : (0 : Rat) ≤ 17))
          (by decide : (0 : Rat) ≤ 17))
    have hM : 0 < ocpE4m3MaxInt := by unfold ocpE4m3MaxInt; decide
    have hden_ftz := deltaContUf_den_pos hM 8 B
    have hden_gu := deltaContUf_den_pos hM 1 B
    have hle_ftz : deltaContUf ocpE4m3MaxInt 8 B ≤ deltaContNormOcpE4m3 B := by
      unfold deltaContUf deltaContNormOcpE4m3
      rw [rat_div_le_div_iff hden_ftz hden_norm]
      apply rat_le_of_sub_nonneg
      have hMval : ((ocpE4m3MaxInt * ocpE4m3MaxInt : Nat) : Rat) = (52613349376 : Rat) := by
        unfold ocpE4m3MaxInt; grind
      rw [hMval]
      have h88 : ((8 * 8 : Nat) : Rat) = 64 := by grind
      rw [h88]
      have hk_nn : (0 : Rat) ≤ ((B - 1 : Nat) : Rat) := natCast_nonneg _
      have hk_le : ((B - 1 : Nat) : Rat) ≤ (11417824 : Rat) :=
        (natCast_le_iff (B - 1) 11417824).mpr (by omega)
      have hident : ((B - 1 : Nat) : Rat) * (4 * 52613349376 + 64 * ((B - 1 : Nat) : Rat)) -
          64 * ((B - 1 : Nat) : Rat) * (4 * 14 * 14 + ((B - 1 : Nat) : Rat) * 17 * 17) =
          ((B - 1 : Nat) : Rat) * (15360 + 18432 * (11417824 - ((B - 1 : Nat) : Rat))) := by grind
      rw [hident]
      exact Rat.mul_nonneg hk_nn
        (rat_add_nonneg (by decide : (0 : Rat) ≤ 15360)
          (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 18432) (rat_sub_nonneg hk_le)))
    have hle_gu : deltaContUf ocpE4m3MaxInt 1 B ≤ deltaContNormOcpE4m3 B := by
      unfold deltaContUf deltaContNormOcpE4m3
      rw [rat_div_le_div_iff hden_gu hden_norm]
      apply rat_le_of_sub_nonneg
      have hMval : ((ocpE4m3MaxInt * ocpE4m3MaxInt : Nat) : Rat) = (52613349376 : Rat) := by
        unfold ocpE4m3MaxInt; grind
      rw [hMval]
      have h11 : ((1 * 1 : Nat) : Rat) = 1 := by grind
      rw [h11]
      have hk_nn : (0 : Rat) ≤ ((B - 1 : Nat) : Rat) := natCast_nonneg _
      have hk_le : ((B - 1 : Nat) : Rat) ≤ (11417824 : Rat) :=
        (natCast_le_iff (B - 1) 11417824).mpr (by omega)
      have hident : ((B - 1 : Nat) : Rat) * (4 * 52613349376 + 1 * ((B - 1 : Nat) : Rat)) -
          1 * ((B - 1 : Nat) : Rat) * (4 * 14 * 14 + ((B - 1 : Nat) : Rat) * 17 * 17) =
          ((B - 1 : Nat) : Rat) * (207165063408 + 288 * (11417824 - ((B - 1 : Nat) : Rat))) := by grind
      rw [hident]
      exact Rat.mul_nonneg hk_nn
        (rat_add_nonneg (by decide : (0 : Rat) ≤ 207165063408)
          (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 288) (rat_sub_nonneg hk_le)))
    rw [rat_max_eq_left_of_le hle_ftz, rat_max_eq_left_of_le hle_gu]

/-- Exact first block size `B = 11,417,826` where `FTZ` incurs a strictly positive penalty on `W8_E4M3_OCP`. -/
theorem ocpE4m3_ftz_first_penalty :
    deltaContOcpE4m3 false 11417826 < deltaContOcpE4m3 true 11417826 := by
  unfold deltaContOcpE4m3
  simp only [↓reduceIte, Bool.false_eq_true]
  have hnorm_eq : deltaContNormOcpE4m3 11417826 = ((11417825 : Nat) : Rat) / ((3299752209 : Nat) : Rat) := by
    unfold deltaContNormOcpE4m3; congr 1 <;> grind
  have hgu_eq : deltaContUf ocpE4m3MaxInt 1 11417826 =
      ((deltaContUfNat ocpE4m3MaxInt 1 11417826).1 : Rat) / ((deltaContUfNat ocpE4m3MaxInt 1 11417826).2 : Rat) :=
    deltaContUf_eq_nat _ _ _
  have hftz_eq : deltaContUf ocpE4m3MaxInt 8 11417826 =
      ((deltaContUfNat ocpE4m3MaxInt 8 11417826).1 : Rat) / ((deltaContUfNat ocpE4m3MaxInt 8 11417826).2 : Rat) :=
    deltaContUf_eq_nat _ _ _
  rw [hnorm_eq, hgu_eq, hftz_eq]
  have hgu_le : ((deltaContUfNat ocpE4m3MaxInt 1 11417826).1 : Rat) / ((deltaContUfNat ocpE4m3MaxInt 1 11417826).2 : Rat) ≤
      ((11417825 : Nat) : Rat) / ((3299752209 : Nat) : Rat) :=
    rat_div_le_div_of_nat (by decide) (by decide) (by decide)
  have hftz_gt : ((11417825 : Nat) : Rat) / ((3299752209 : Nat) : Rat) <
      ((deltaContUfNat ocpE4m3MaxInt 8 11417826).1 : Rat) / ((deltaContUfNat ocpE4m3MaxInt 8 11417826).2 : Rat) :=
    rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
  rw [rat_max_eq_left_of_le hgu_le, rat_max_eq_right_of_le (Rat.le_of_lt hftz_gt)]
  exact hftz_gt

/-- Helper to prove `2 * (a / b) < c / d` via pure-`Nat` cross-multiplication. -/
theorem two_mul_div_lt_div_of_nat {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : 2 * a * d < c * b) :
    2 * ((a : Rat) / (b : Rat)) < (c : Rat) / (d : Rat) := by
  have heq : 2 * ((a : Rat) / (b : Rat)) = ((2 * a : Nat) : Rat) / (b : Rat) := by grind
  rw [heq]
  exact rat_div_lt_div_of_nat hb hd h

/-- **Headline Theorem 6:** Exact `FTZ` Hardware Bifurcation — `W8_E4M3_OCP` has exact ZERO
continuous-scale penalty for ALL `1 ≤ B ≤ 11,417,825`, whereas every optimal `a = 2`
microscaling format (`E2M1, E2M2, E2M3, E2M4, E2M5`) hits `> 2×` worst-case MSE already at `B ≤ 12`
(and `B ≤ 5` under OCP E8M0). -/
theorem mxfp_ftz_hardware_bifurcation_e4m3_vs_e2mb :
    (∀ B : Nat, 1 ≤ B → B ≤ 11417825 →
      deltaContOcpE4m3 true B = deltaContOcpE4m3 false B) ∧
    deltaContOcpE4m3 false 11417826 < deltaContOcpE4m3 true 11417826 ∧
    -- Continuous mode: every E2M_b (b = 1..5) hits > 2x MSE penalty at B <= 12
    (2 * deltaCont 2 1 false 12 < deltaCont 2 1 true 12 ∧
     2 * deltaCont 2 2 false 4 < deltaCont 2 2 true 4 ∧
     2 * deltaCont 2 3 false 2 < deltaCont 2 3 true 2 ∧
     2 * deltaCont 2 4 false 2 < deltaCont 2 4 true 2 ∧
     2 * deltaCont 2 5 false 2 < deltaCont 2 5 true 2) ∧
    -- OCP E8M0 mode: every E2M_b (b = 1..5) hits > 2x MSE penalty at B <= 5
    (2 * deltaE8m0 2 1 false 5 < deltaE8m0 2 1 true 5 ∧
     2 * deltaE8m0 2 2 false 3 < deltaE8m0 2 2 true 3 ∧
     2 * deltaE8m0 2 3 false 2 < deltaE8m0 2 3 true 2 ∧
     2 * deltaE8m0 2 4 false 2 < deltaE8m0 2 4 true 2 ∧
     2 * deltaE8m0 2 5 false 2 < deltaE8m0 2 5 true 2) := by
  refine ⟨ocpE4m3_ftz_exact_zero_penalty, ocpE4m3_ftz_first_penalty, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [deltaCont_eq_nat false 12 (by decide) (by decide),
          deltaCont_eq_nat true 12 (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 4 (by decide) (by decide),
          deltaCont_eq_nat true 4 (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 2 (by decide) (by decide),
          deltaCont_eq_nat true 2 (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 2 (by decide) (by decide),
          deltaCont_eq_nat true 2 (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 2 (by decide) (by decide),
          deltaCont_eq_nat true 2 (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [deltaE8m0_eq_nat false 5 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat true 5 (by decide) (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 3 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat true 3 (by decide) (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 2 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat true 2 (by decide) (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 2 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat true 2 (by decide) (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 2 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat true 2 (by decide) (by decide) (by decide)]
      exact two_mul_div_lt_div_of_nat (by decide) (by decide) (by decide)

end MxfpDoublelogFtz
