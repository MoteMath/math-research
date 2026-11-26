/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import XorVdcFp4Dither.WalshSpectrum

/-!
# Double-Quantized GEMM Bias Obstructions, `bitrev_10` Hammersley, and Split-Word XOR-VDC (Theorems 5 & 6)

Proves:
- **Theorem 5 (`double_quant_gemm_bias_obstruction_and_hammersley`)**:
  1. For all `k ≥ 1`, `samePerm`, `antiPerm k`, and `msbXorPerm k` all satisfy
     `max |bias| = 1/4` (both upper bound `≤ 1/4` for all `A, B ≤ 2^k` and exact attainment
     `= 1/4` at `A = B = 2^(k-1)`).
  2. For 0-extra-bit `bitrev_10` Hammersley coupling (`k = 10`, `M = 1024`),
     `∀ A B ≤ 1024, |bias| ≤ 3527 / 1048576` with exact attainment `= 3527 / 1048576` at `(341, 341)`
     (a `> 74x` reduction in worst-case bias with zero extra random bits).
- **Theorem 6 (`split_32bit_word_xor_vdc_zero_bias_double_gemm`)**:
  Splitting a single `2m`-bit uniform word (`m = 16` for 32-bit words) into independent halves
  `(w % 2^m, w / 2^m)` combined with XOR-VDC guarantees exact zero bias
  `E[Q(a; u0_a ^ d_i) * Q(b; u0_b ^ d_j)] = a * b` AND strictly preserves the exact intra-block
  XOR-VDC pairwise covariance on both halves (`64x` PRNG reduction at `B = 32` with strictly
  negative cross-lane covariance).
-/

namespace XorVdcFp4Dither

/-! ### 1. `countRange` Helpers -/

theorem countRange_append (a b : Nat) (p : Nat → Bool) :
    countRange (a + b) p = countRange a p + countRange b (fun j => p (a + j)) := by
  induction b with
  | zero => simp [countRange]
  | succ b ih =>
    rw [Nat.add_succ]
    simp only [countRange, ih]
    omega

theorem countRange_lt (M C : Nat) :
    countRange M (fun u => decide (u < C)) = min M C := by
  induction M with
  | zero => simp [countRange]
  | succ M ih =>
    simp only [countRange, ih]
    by_cases h : M < C <;> simp [h] <;> omega

theorem countRange_ge_and_lt (M L R : Nat) (hR : R ≤ M) :
    countRange M (fun u => decide (L ≤ u ∧ u < R)) = R - L := by
  induction M generalizing L R with
  | zero =>
    have hR0 : R = 0 := by omega
    subst hR0; simp [countRange]
  | succ M ih =>
    simp only [countRange]
    by_cases hRM : R ≤ M
    · rw [ih L R hRM]
      have hnot : ¬ (L ≤ M ∧ M < R) := by omega
      simp [hnot]
    · have hReq : R = M + 1 := by omega
      subst hReq
      have hcongr :
          countRange M (fun u => decide (L ≤ u ∧ u < M + 1)) =
          countRange M (fun u => decide (L ≤ u ∧ u < M)) := by
        apply countRange_congr
        intro u hu
        simp only [decide_eq_decide]
        omega
      rw [hcongr, ih L M (Nat.le_refl M)]
      by_cases hLM : L ≤ M
      · have htrue : L ≤ M ∧ M < M + 1 := by omega
        simp [htrue]; omega
      · have hfalse : ¬ (L ≤ M ∧ M < M + 1) := by omega
        simp only [hfalse, decide_false, Bool.false_eq_true, ↓reduceIte]
        omega

/-! ### 2. Exact `jointCount` & `max |bias| = 1/4` for `same`, `antithetic`, `msb_1bit_xor` -/

theorem jointCount_same (k A B : Nat) (hA : A ≤ 2 ^ k) (hB : B ≤ 2 ^ k) :
    jointCount k samePerm A B = min A B := by
  unfold jointCount samePerm
  have hcongr :
      countRange (2 ^ k) (fun u => decide (u < A ∧ u < B)) =
      countRange (2 ^ k) (fun u => decide (u < min A B)) := by
    apply countRange_congr
    intro u _
    simp only [decide_eq_decide]
    omega
  rw [hcongr, countRange_lt]
  omega

theorem jointCount_anti (k A B : Nat) (hA : A ≤ 2 ^ k) (hB : B ≤ 2 ^ k) :
    jointCount k (antiPerm k) A B = A + B - 2 ^ k := by
  unfold jointCount antiPerm
  have hcongr :
      countRange (2 ^ k) (fun u => decide (u < A ∧ 2 ^ k - 1 - u < B)) =
      countRange (2 ^ k) (fun u => decide (2 ^ k - B ≤ u ∧ u < A)) := by
    apply countRange_congr
    intro u hu
    simp only [decide_eq_decide]
    omega
  rw [hcongr, countRange_ge_and_lt (2 ^ k) (2 ^ k - B) A hA]
  omega

private theorem two_pow_eq_double_pred {k : Nat} (hk : 1 ≤ k) :
    2 ^ k = 2 * 2 ^ (k - 1) := by
  have hk1 : k = (k - 1) + 1 := by omega
  calc 2 ^ k = 2 ^ ((k - 1) + 1) := by rw [← hk1]
    _ = 2 ^ (k - 1) * 2 := Nat.pow_succ 2 (k - 1)
    _ = 2 * 2 ^ (k - 1) := Nat.mul_comm _ _

theorem jointCount_msbXor (k A B : Nat) (hk : 1 ≤ k) (_hA : A ≤ 2 ^ k) (_hB : B ≤ 2 ^ k) :
    jointCount k (msbXorPerm k) A B =
    min (min A (B - 2 ^ (k - 1))) (2 ^ (k - 1)) +
    min (min (A - 2 ^ (k - 1)) B) (2 ^ (k - 1)) := by
  unfold jointCount msbXorPerm
  let H := 2 ^ (k - 1)
  have hpow : 2 ^ k = H + H := by
    have := two_pow_eq_double_pred hk; omega
  rw [hpow, countRange_append]
  have hleft :
      countRange H (fun u => decide (u < A ∧ u ^^^ H < B)) =
      min (min A (B - H)) H := by
    have hcongr :
        countRange H (fun u => decide (u < A ∧ u ^^^ H < B)) =
        countRange H (fun u => decide (u < min A (B - H))) := by
      apply countRange_congr
      intro u hu
      have hxor : u ^^^ H = H + u := by
        have h0 : (0 : Nat) < H := Nat.two_pow_pos (k - 1)
        have := nat_xor_add_two_pow_right hu h0
        simpa using this
      rw [hxor]
      simp only [decide_eq_decide]
      omega
    rw [hcongr, countRange_lt]
    omega
  have hright :
      countRange H (fun v => decide (H + v < A ∧ (H + v) ^^^ H < B)) =
      min (min (A - H) B) H := by
    have hcongr :
        countRange H (fun v => decide (H + v < A ∧ (H + v) ^^^ H < B)) =
        countRange H (fun v => decide (v < min (A - H) B)) := by
      apply countRange_congr
      intro v hv
      have hxor : (H + v) ^^^ H = v := by
        have h0 : (0 : Nat) < H := Nat.two_pow_pos (k - 1)
        have := nat_xor_add_two_pow_both hv h0
        simpa using this
      rw [hxor]
      simp only [decide_eq_decide]
      omega
    rw [hcongr, countRange_lt]
    omega
  rw [hleft, hright]

private theorem doubleQuantBias_eq_int_div (k : Nat) (pi : Nat → Nat) (A B : Nat) :
    doubleQuantBias k pi A B =
    ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat) /
      (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat)) := by
  unfold doubleQuantBias
  have hMne : ((2 ^ k : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero k
  have hcast :
      ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat) =
      ((2 ^ k : Nat) : Rat) * (jointCount k pi A B : Rat) - ((A * B : Nat) : Rat) := by
    rw [Rat.intCast_sub, Rat.intCast_natCast, Rat.intCast_natCast, rat_natCast_mul]
  rw [hcast]
  grind

private theorem absRat_bias_le_of_int_bound {k : Nat} {pi : Nat → Nat} {A B C : Nat}
    (h1 : ((A * B : Nat) : Int) - (C : Int) ≤ ((2 ^ k * jointCount k pi A B : Nat) : Int))
    (h2 : ((2 ^ k * jointCount k pi A B : Nat) : Int) ≤ ((A * B : Nat) : Int) + (C : Int)) :
    absRat (doubleQuantBias k pi A B) ≤ (C : Rat) / (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat)) := by
  rw [doubleQuantBias_eq_int_div, absRat_le_iff]
  have hM2pos : (0 : Rat) < ((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat) :=
    rat_mul_pos (rat_pow2_pos k) (rat_pow2_pos k)
  have hlow_int : (-(C : Int)) ≤ ((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) := by
    omega
  have hhi_int : ((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) ≤ (C : Int) := by
    omega
  have hlow_rat : (-(C : Rat)) ≤
      ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat) := by
    have h := Rat.intCast_le_intCast.mpr hlow_int
    rw [Rat.intCast_neg, Rat.intCast_natCast] at h
    exact h
  have hhi_rat :
      ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat) ≤ (C : Rat) := by
    have h := Rat.intCast_le_intCast.mpr hhi_int
    rw [Rat.intCast_natCast] at h
    exact h
  constructor
  · have hneg : -((C : Rat) / (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat))) =
        (-(C : Rat)) / (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat)) := by grind
    rw [hneg]
    exact rat_div_le_div_of_pos_right hlow_rat hM2pos
  · exact rat_div_le_div_of_pos_right hhi_rat hM2pos

private theorem prod_le_quarter_sum_sq (a b M : Int) (hsum : a + b ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    4 * (a * b) ≤ M * M := by
  have h1 : 4 * (a * b) ≤ (a + b) * (a + b) := by
    have hdiff : (a + b) * (a + b) - 4 * (a * b) = (a - b) * (a - b) := by grind
    have hsq : 0 ≤ (a - b) * (a - b) := by
      by_cases h : 0 ≤ a - b
      · exact Int.mul_nonneg h h
      · have hrew : (a - b) * (a - b) = (b - a) * (b - a) := by grind
        rw [hrew]; exact Int.mul_nonneg (by omega) (by omega)
    omega
  have h2 : (a + b) * (a + b) ≤ M * M := by
    have hdiff : M * M - (a + b) * (a + b) = (M - (a + b)) * (M + (a + b)) := by grind
    have hpos : 0 ≤ (M - (a + b)) * (M + (a + b)) := Int.mul_nonneg (by omega) (by omega)
    omega
  omega

theorem bias_le_quarter_of_int_bound {k : Nat} {pi : Nat → Nat} {A B : Nat}
    (h1 : 4 * (((2 ^ k : Nat) : Int) * (jointCount k pi A B : Int) - (A : Int) * (B : Int)) ≤
          ((2 ^ k : Nat) : Int) * ((2 ^ k : Nat) : Int))
    (h2 : -(((2 ^ k : Nat) : Int) * ((2 ^ k : Nat) : Int)) ≤
          4 * (((2 ^ k : Nat) : Int) * (jointCount k pi A B : Int) - (A : Int) * (B : Int))) :
    absRat (doubleQuantBias k pi A B) ≤ 1 / 4 := by
  rw [doubleQuantBias_eq_int_div, absRat_le_iff]
  have hM2pos : (0 : Rat) < ((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat) :=
    rat_mul_pos (rat_pow2_pos k) (rat_pow2_pos k)
  have hM2ne : ((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hM2pos
  have h4M2pos : (0 : Rat) < 4 * (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat)) :=
    rat_mul_pos (by grind) hM2pos
  have hnum_eq :
      ((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) =
      ((2 ^ k : Nat) : Int) * (jointCount k pi A B : Int) - (A : Int) * (B : Int) := by
    rw [Int.natCast_mul, Int.natCast_mul]
  have hlow_rat : -((((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat))) ≤
      4 * ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat) := by
    rw [hnum_eq]
    have h := Rat.intCast_le_intCast.mpr h2
    rw [Rat.intCast_neg, Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_natCast] at h
    exact h
  have hhi_rat :
      4 * ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat) ≤
      (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat)) := by
    rw [hnum_eq]
    have h := Rat.intCast_le_intCast.mpr h1
    rw [Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_natCast] at h
    exact h
  constructor
  · have hstep := rat_div_le_div_of_pos_right hlow_rat h4M2pos
    have hl : -((((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat))) /
        (4 * (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat))) = -((1 : Rat) / 4) := by grind
    have hr : (4 * ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat)) /
        (4 * (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat))) =
        ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat) /
        (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat)) := by grind
    rw [hl, hr] at hstep
    exact hstep
  · have hstep := rat_div_le_div_of_pos_right hhi_rat h4M2pos
    have hl : (4 * ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat)) /
        (4 * (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat))) =
        ((((2 ^ k * jointCount k pi A B : Nat) : Int) - ((A * B : Nat) : Int) : Int) : Rat) /
        (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat)) := by grind
    have hr : (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat)) /
        (4 * (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat))) = (1 : Rat) / 4 := by grind
    rw [hl, hr] at hstep
    exact hstep

theorem samePerm_bias_obstruction (k : Nat) (hk : 1 ≤ k) :
    (∀ A B, A ≤ 2 ^ k → B ≤ 2 ^ k → absRat (doubleQuantBias k samePerm A B) ≤ 1 / 4) ∧
    absRat (doubleQuantBias k samePerm (2 ^ (k - 1)) (2 ^ (k - 1))) = 1 / 4 := by
  constructor
  · intro A B hA hB
    apply bias_le_quarter_of_int_bound
    · rw [jointCount_same k A B hA hB]
      by_cases hab : A ≤ B
      · have hmin : min A B = A := Nat.min_eq_left hab
        rw [hmin]
        have hrew : ((2 ^ k : Nat) : Int) * (A : Int) - (A : Int) * (B : Int) =
            (A : Int) * (((2 ^ k : Nat) : Int) - (B : Int)) := by grind
        rw [hrew]
        exact prod_le_quarter_sum_sq (A : Int) (((2 ^ k : Nat) : Int) - (B : Int))
          ((2 ^ k : Nat) : Int) (by omega) (by omega) (by omega)
      · have hmin : min A B = B := Nat.min_eq_right (by omega)
        rw [hmin]
        have hrew : ((2 ^ k : Nat) : Int) * (B : Int) - (A : Int) * (B : Int) =
            (B : Int) * (((2 ^ k : Nat) : Int) - (A : Int)) := by grind
        rw [hrew]
        exact prod_le_quarter_sum_sq (B : Int) (((2 ^ k : Nat) : Int) - (A : Int))
          ((2 ^ k : Nat) : Int) (by omega) (by omega) (by omega)
    · rw [jointCount_same k A B hA hB]
      have hge : (A : Int) * (B : Int) ≤ ((2 ^ k : Nat) : Int) * ((min A B : Nat) : Int) := by
        by_cases hab : A ≤ B
        · rw [Nat.min_eq_left hab]
          have : A * B ≤ 2 ^ k * A := by
            have := Nat.mul_le_mul_left A hB; rw [Nat.mul_comm A (2 ^ k)] at this; exact this
          have := Int.ofNat_le.mpr this
          rw [Int.natCast_mul, Int.natCast_mul] at this
          exact this
        · rw [Nat.min_eq_right (by omega)]
          have : A * B ≤ 2 ^ k * B := Nat.mul_le_mul_right B hA
          have := Int.ofNat_le.mpr this
          rw [Int.natCast_mul, Int.natCast_mul] at this
          exact this
      have hM2 : (0 : Int) ≤ ((2 ^ k : Nat) : Int) * ((2 ^ k : Nat) : Int) :=
        Int.mul_nonneg (by omega) (by omega)
      omega
  · have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := two_pow_eq_double_pred hk
    have hHle : 2 ^ (k - 1) ≤ 2 ^ k := by omega
    rw [doubleQuantBias_eq_int_div, jointCount_same k _ _ hHle hHle]
    have hmin : min (2 ^ (k - 1)) (2 ^ (k - 1)) = 2 ^ (k - 1) := Nat.min_self _
    rw [hmin, hpow]
    have hHne : ((2 ^ (k - 1) : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero (k - 1)
    have hval :
        ((((2 * 2 ^ (k - 1) * 2 ^ (k - 1) : Nat) : Int) - ((2 ^ (k - 1) * 2 ^ (k - 1) : Nat) : Int) : Int) : Rat) /
        (((2 * 2 ^ (k - 1) : Nat) : Rat) * ((2 * 2 ^ (k - 1) : Nat) : Rat)) = 1 / 4 := by
      rw [Rat.intCast_sub, Rat.intCast_natCast, Rat.intCast_natCast,
          rat_natCast_mul, rat_natCast_mul, rat_natCast_mul]
      have h2 : ((2 : Nat) : Rat) = 2 := rfl
      rw [h2]
      grind
    rw [hval, absRat_of_nonneg (by grind)]

theorem antiPerm_bias_obstruction (k : Nat) (hk : 1 ≤ k) :
    (∀ A B, A ≤ 2 ^ k → B ≤ 2 ^ k → absRat (doubleQuantBias k (antiPerm k) A B) ≤ 1 / 4) ∧
    absRat (doubleQuantBias k (antiPerm k) (2 ^ (k - 1)) (2 ^ (k - 1))) = 1 / 4 := by
  constructor
  · intro A B hA hB
    apply bias_le_quarter_of_int_bound
    · rw [jointCount_anti k A B hA hB]
      have hle : ((2 ^ k : Nat) : Int) * ((A + B - 2 ^ k : Nat) : Int) ≤ (A : Int) * (B : Int) := by
        by_cases hsum : A + B ≤ 2 ^ k
        · have h0 : A + B - 2 ^ k = 0 := by omega
          rw [h0]
          have : (0 : Int) ≤ (A : Int) * (B : Int) := Int.mul_nonneg (by omega) (by omega)
          omega
        · have hsub : ((A + B - 2 ^ k : Nat) : Int) = (A : Int) + (B : Int) - ((2 ^ k : Nat) : Int) := by omega
          rw [hsub]
          have hdiff : (A : Int) * (B : Int) - ((2 ^ k : Nat) : Int) * ((A : Int) + (B : Int) - ((2 ^ k : Nat) : Int)) =
              (((2 ^ k : Nat) : Int) - (A : Int)) * (((2 ^ k : Nat) : Int) - (B : Int)) := by grind
          have hnn : 0 ≤ (((2 ^ k : Nat) : Int) - (A : Int)) * (((2 ^ k : Nat) : Int) - (B : Int)) :=
            Int.mul_nonneg (by omega) (by omega)
          omega
      have hM2 : (0 : Int) ≤ ((2 ^ k : Nat) : Int) * ((2 ^ k : Nat) : Int) :=
        Int.mul_nonneg (by omega) (by omega)
      omega
    · rw [jointCount_anti k A B hA hB]
      by_cases hsum : A + B ≤ 2 ^ k
      · have h0 : A + B - 2 ^ k = 0 := by omega
        rw [h0]
        have hle := prod_le_quarter_sum_sq (A : Int) (B : Int) ((2 ^ k : Nat) : Int)
          (by omega) (by omega) (by omega)
        omega
      · have hsub : ((A + B - 2 ^ k : Nat) : Int) = (A : Int) + (B : Int) - ((2 ^ k : Nat) : Int) := by omega
        rw [hsub]
        have hdiff : (A : Int) * (B : Int) - ((2 ^ k : Nat) : Int) * ((A : Int) + (B : Int) - ((2 ^ k : Nat) : Int)) =
            (((2 ^ k : Nat) : Int) - (A : Int)) * (((2 ^ k : Nat) : Int) - (B : Int)) := by grind
        have hle := prod_le_quarter_sum_sq (((2 ^ k : Nat) : Int) - (A : Int))
          (((2 ^ k : Nat) : Int) - (B : Int)) ((2 ^ k : Nat) : Int)
          (by omega) (by omega) (by omega)
        omega
  · have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := two_pow_eq_double_pred hk
    have hHle : 2 ^ (k - 1) ≤ 2 ^ k := by omega
    rw [doubleQuantBias_eq_int_div, jointCount_anti k _ _ hHle hHle]
    have h0 : 2 ^ (k - 1) + 2 ^ (k - 1) - 2 ^ k = 0 := by omega
    rw [h0, hpow]
    have hHne : ((2 ^ (k - 1) : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero (k - 1)
    have hval :
        ((((2 * 2 ^ (k - 1) * 0 : Nat) : Int) - ((2 ^ (k - 1) * 2 ^ (k - 1) : Nat) : Int) : Int) : Rat) /
        (((2 * 2 ^ (k - 1) : Nat) : Rat) * ((2 * 2 ^ (k - 1) : Nat) : Rat)) = -(1 / 4) := by
      rw [Rat.intCast_sub, Rat.intCast_natCast, Rat.intCast_natCast,
          rat_natCast_mul, rat_natCast_mul, rat_natCast_mul]
      have h2 : ((2 : Nat) : Rat) = 2 := rfl
      have h0r : ((0 : Nat) : Rat) = 0 := rfl
      rw [h2, h0r]
      grind
    rw [hval, absRat_of_nonpos (by grind)]
    grind

theorem msbXorPerm_bias_obstruction (k : Nat) (hk : 1 ≤ k) :
    (∀ A B, A ≤ 2 ^ k → B ≤ 2 ^ k → absRat (doubleQuantBias k (msbXorPerm k) A B) ≤ 1 / 4) ∧
    absRat (doubleQuantBias k (msbXorPerm k) (2 ^ (k - 1)) (2 ^ (k - 1))) = 1 / 4 := by
  let H := 2 ^ (k - 1)
  have hpow : 2 ^ k = 2 * H := two_pow_eq_double_pred hk
  have hpowI : ((2 ^ k : Nat) : Int) = 2 * (H : Int) := by
    rw [hpow, Int.natCast_mul]; rfl
  have h4H2 : 2 * (H : Int) * (2 * (H : Int)) = 4 * ((H : Int) * (H : Int)) := by grind
  constructor
  · intro A B hA hB
    apply bias_le_quarter_of_int_bound
    · rw [jointCount_msbXor k A B hk hA hB, hpowI]
      by_cases hAH : A ≤ H <;> by_cases hBH : B ≤ H
      · have hc : min (min A (B - H)) H + min (min (A - H) B) H = 0 := by omega
        rw [hc]
        have hAB : (0 : Int) ≤ (A : Int) * (B : Int) := Int.mul_nonneg (by omega) (by omega)
        have hH2 : (0 : Int) ≤ (H : Int) * (H : Int) := Int.mul_nonneg (by omega) (by omega)
        omega
      · have hc : min (min A (B - H)) H + min (min (A - H) B) H = min A (B - H) := by omega
        rw [hc]
        by_cases hmin : A ≤ B - H
        · rw [Nat.min_eq_left hmin]
          have hrew : 2 * (H : Int) * (A : Int) - (A : Int) * (B : Int) =
              (A : Int) * (2 * (H : Int) - (B : Int)) := by grind
          have hdiff : (H : Int) * (H : Int) - (A : Int) * (2 * (H : Int) - (B : Int)) =
              ((H : Int) - (A : Int)) * (H : Int) + (A : Int) * ((B : Int) - (H : Int)) := by grind
          have hnn1 : 0 ≤ ((H : Int) - (A : Int)) * (H : Int) := Int.mul_nonneg (by omega) (by omega)
          have hnn2 : 0 ≤ (A : Int) * ((B : Int) - (H : Int)) := Int.mul_nonneg (by omega) (by omega)
          omega
        · rw [Nat.min_eq_right (by omega)]
          have hsub : ((B - H : Nat) : Int) = (B : Int) - (H : Int) := by omega
          rw [hsub]
          have hAB : ((B : Int) - (H : Int)) * (B : Int) ≤ (A : Int) * (B : Int) :=
            Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
          have hq : 4 * (((B : Int) - (H : Int)) * (2 * (H : Int) - (B : Int))) ≤ (H : Int) * (H : Int) :=
            prod_le_quarter_sum_sq ((B : Int) - (H : Int)) (2 * (H : Int) - (B : Int)) (H : Int)
              (by omega) (by omega) (by omega)
          have hH2 : (0 : Int) ≤ (H : Int) * (H : Int) := Int.mul_nonneg (by omega) (by omega)
          have hrew : 2 * (H : Int) * ((B : Int) - (H : Int)) - ((B : Int) - (H : Int)) * (B : Int) =
              ((B : Int) - (H : Int)) * (2 * (H : Int) - (B : Int)) := by grind
          omega
      · have hc : min (min A (B - H)) H + min (min (A - H) B) H = min (A - H) B := by omega
        rw [hc]
        by_cases hmin : A - H ≤ B
        · rw [Nat.min_eq_left hmin]
          have hsub : ((A - H : Nat) : Int) = (A : Int) - (H : Int) := by omega
          rw [hsub]
          have hAB : (A : Int) * ((A : Int) - (H : Int)) ≤ (A : Int) * (B : Int) :=
            Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
          have hq : 4 * (((A : Int) - (H : Int)) * (2 * (H : Int) - (A : Int))) ≤ (H : Int) * (H : Int) :=
            prod_le_quarter_sum_sq ((A : Int) - (H : Int)) (2 * (H : Int) - (A : Int)) (H : Int)
              (by omega) (by omega) (by omega)
          have hH2 : (0 : Int) ≤ (H : Int) * (H : Int) := Int.mul_nonneg (by omega) (by omega)
          have hrew : 2 * (H : Int) * ((A : Int) - (H : Int)) - (A : Int) * ((A : Int) - (H : Int)) =
              ((A : Int) - (H : Int)) * (2 * (H : Int) - (A : Int)) := by grind
          omega
        · rw [Nat.min_eq_right (by omega)]
          have hrew : 2 * (H : Int) * (B : Int) - (A : Int) * (B : Int) =
              (B : Int) * (2 * (H : Int) - (A : Int)) := by grind
          have hdiff : (H : Int) * (H : Int) - (B : Int) * (2 * (H : Int) - (A : Int)) =
              ((H : Int) - (B : Int)) * (H : Int) + (B : Int) * ((A : Int) - (H : Int)) := by grind
          have hnn1 : 0 ≤ ((H : Int) - (B : Int)) * (H : Int) := Int.mul_nonneg (by omega) (by omega)
          have hnn2 : 0 ≤ (B : Int) * ((A : Int) - (H : Int)) := Int.mul_nonneg (by omega) (by omega)
          omega
      · have hc : min (min A (B - H)) H + min (min (A - H) B) H = (A - H) + (B - H) := by omega
        rw [hc]
        have hsub : (((A - H) + (B - H) : Nat) : Int) = (A : Int) + (B : Int) - 2 * (H : Int) := by omega
        rw [hsub]
        have hdiff : (A : Int) * (B : Int) - 2 * (H : Int) * ((A : Int) + (B : Int) - 2 * (H : Int)) =
            (2 * (H : Int) - (A : Int)) * (2 * (H : Int) - (B : Int)) := by grind
        have hnn : 0 ≤ (2 * (H : Int) - (A : Int)) * (2 * (H : Int) - (B : Int)) :=
          Int.mul_nonneg (by omega) (by omega)
        have hH2 : (0 : Int) ≤ (H : Int) * (H : Int) := Int.mul_nonneg (by omega) (by omega)
        omega
    · rw [jointCount_msbXor k A B hk hA hB, hpowI]
      by_cases hAH : A ≤ H <;> by_cases hBH : B ≤ H
      · have hc : min (min A (B - H)) H + min (min (A - H) B) H = 0 := by omega
        rw [hc]
        have hAB : (A : Int) * (B : Int) ≤ (H : Int) * (H : Int) := by
          have h1 : (A : Int) * (B : Int) ≤ (H : Int) * (B : Int) :=
            Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
          have h2 : (H : Int) * (B : Int) ≤ (H : Int) * (H : Int) :=
            Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
          omega
        omega
      · have hc : min (min A (B - H)) H + min (min (A - H) B) H = min A (B - H) := by omega
        rw [hc]
        by_cases hmin : A ≤ B - H
        · rw [Nat.min_eq_left hmin]
          have hle : (A : Int) * (B : Int) ≤ 2 * (H : Int) * (A : Int) := by
            have : A * B ≤ 2 * H * A := by
              have := Nat.mul_le_mul_left A (show B ≤ 2 * H by omega)
              rw [Nat.mul_comm A (2 * H)] at this; exact this
            have hI := Int.ofNat_le.mpr this
            rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul] at hI
            exact hI
          have hH2 : (0 : Int) ≤ (H : Int) * (H : Int) := Int.mul_nonneg (by omega) (by omega)
          omega
        · rw [Nat.min_eq_right (by omega)]
          have hsub : ((B - H : Nat) : Int) = (B : Int) - (H : Int) := by omega
          rw [hsub]
          have hAB : (A : Int) * (B : Int) ≤ (H : Int) * (B : Int) :=
            Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
          have hdiff : (H : Int) * (H : Int) - ((H : Int) * (B : Int) - 2 * (H : Int) * ((B : Int) - (H : Int))) =
              (H : Int) * ((B : Int) - (H : Int)) := by grind
          have hnn : 0 ≤ (H : Int) * ((B : Int) - (H : Int)) := Int.mul_nonneg (by omega) (by omega)
          omega
      · have hc : min (min A (B - H)) H + min (min (A - H) B) H = min (A - H) B := by omega
        rw [hc]
        by_cases hmin : A - H ≤ B
        · rw [Nat.min_eq_left hmin]
          have hsub : ((A - H : Nat) : Int) = (A : Int) - (H : Int) := by omega
          rw [hsub]
          have hAB : (A : Int) * (B : Int) ≤ (A : Int) * (H : Int) :=
            Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
          have hdiff : (H : Int) * (H : Int) - ((A : Int) * (H : Int) - 2 * (H : Int) * ((A : Int) - (H : Int))) =
              (H : Int) * ((A : Int) - (H : Int)) := by grind
          have hnn : 0 ≤ (H : Int) * ((A : Int) - (H : Int)) := Int.mul_nonneg (by omega) (by omega)
          omega
        · rw [Nat.min_eq_right (by omega)]
          have hle : (A : Int) * (B : Int) ≤ 2 * (H : Int) * (B : Int) := by
            have : A * B ≤ 2 * H * B := Nat.mul_le_mul_right B (by omega)
            have hI := Int.ofNat_le.mpr this
            rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul] at hI
            exact hI
          have hH2 : (0 : Int) ≤ (H : Int) * (H : Int) := Int.mul_nonneg (by omega) (by omega)
          omega
      · have hc : min (min A (B - H)) H + min (min (A - H) B) H = (A - H) + (B - H) := by omega
        rw [hc]
        have hsub : (((A - H) + (B - H) : Nat) : Int) = (A : Int) + (B : Int) - 2 * (H : Int) := by omega
        rw [hsub]
        have hdiff : (A : Int) * (B : Int) - 2 * (H : Int) * ((A : Int) + (B : Int) - 2 * (H : Int)) =
            (2 * (H : Int) - (A : Int)) * (2 * (H : Int) - (B : Int)) := by grind
        have h1 : (2 * (H : Int) - (A : Int)) * (2 * (H : Int) - (B : Int)) ≤
            (H : Int) * (2 * (H : Int) - (B : Int)) :=
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        have h2 : (H : Int) * (2 * (H : Int) - (B : Int)) ≤ (H : Int) * (H : Int) :=
          Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
  · have hHle : H ≤ 2 ^ k := by omega
    rw [doubleQuantBias_eq_int_div, jointCount_msbXor k H H hk hHle hHle]
    have h0 : min (min H (H - H)) H + min (min (H - H) H) H = 0 := by omega
    rw [h0, hpow]
    have hHne : ((2 ^ (k - 1) : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero (k - 1)
    have hval :
        ((((2 * H * 0 : Nat) : Int) - ((H * H : Nat) : Int) : Int) : Rat) /
        (((2 * H : Nat) : Rat) * ((2 * H : Nat) : Rat)) = -(1 / 4) := by
      rw [Rat.intCast_sub, Rat.intCast_natCast, Rat.intCast_natCast,
          rat_natCast_mul, rat_natCast_mul, rat_natCast_mul]
      have h2 : ((2 : Nat) : Rat) = 2 := rfl
      have h0r : ((0 : Nat) : Rat) = 0 := rfl
      rw [h2, h0r]
      grind
    rw [hval, absRat_of_nonpos (by grind)]
    grind

/-! ### 3. Exact Dyadic Recurrence and `3527 / 1048576` Bound for `bitrev_10` Hammersley -/

/-- Exact fast `O(k)` evaluator of `jointCount k (hammersleyPerm k) A B`. -/
def hammersleyCountFast : Nat → Nat → Nat → Nat
  | 0, A, B => if 0 < A ∧ 0 < B then 1 else 0
  | k + 1, A, B =>
    if A ≤ 2 ^ k then
      hammersleyCountFast k A ((B + 1) / 2)
    else
      (B + 1) / 2 + hammersleyCountFast k (A - 2 ^ k) (B / 2)

/-- Exact 1D upper bound `F(k, A) = max_{B ≤ 2^k} (2^k * count(k, A, B) - A * B)`. -/
def hammersleyBound : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, A =>
    if A ≤ 2 ^ k then
      2 * hammersleyBound k A + A
    else
      2 * hammersleyBound k (A - 2 ^ k) + (2 ^ (k + 1) - A)

theorem countRange_bitrev_lt (k C : Nat) (hC : C ≤ 2 ^ k) :
    countRange (2 ^ k) (fun u => decide (bitrev k u < C)) = C := by
  induction k generalizing C with
  | zero =>
    have hC' : C = 0 ∨ C = 1 := by omega
    rcases hC' with h0 | h1
    · subst h0; decide
    · subst h1; decide
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hpow, countRange_append]
    have hleft :
        countRange (2 ^ k) (fun u => decide (bitrev (k + 1) u < C)) = (C + 1) / 2 := by
      have hcongr :
          countRange (2 ^ k) (fun u => decide (bitrev (k + 1) u < C)) =
          countRange (2 ^ k) (fun u => decide (bitrev k u < (C + 1) / 2)) := by
        apply countRange_congr
        intro u hu
        rw [bitrev_succ_half hu]
        simp only [decide_eq_decide]
        omega
      rw [hcongr]
      exact ih ((C + 1) / 2) (by omega)
    have hright :
        countRange (2 ^ k) (fun v => decide (bitrev (k + 1) (2 ^ k + v) < C)) = C / 2 := by
      have hcongr :
          countRange (2 ^ k) (fun v => decide (bitrev (k + 1) (2 ^ k + v) < C)) =
          countRange (2 ^ k) (fun v => decide (bitrev k v < C / 2)) := by
        apply countRange_congr
        intro v hv
        rw [bitrev_succ_add_pow hv]
        simp only [decide_eq_decide]
        omega
      rw [hcongr]
      exact ih (C / 2) (by omega)
    rw [hleft, hright]
    omega

theorem jointCount_hammersley_eq_fast (k A B : Nat) (hA : A ≤ 2 ^ k) (hB : B ≤ 2 ^ k) :
    jointCount k (hammersleyPerm k) A B = hammersleyCountFast k A B := by
  induction k generalizing A B with
  | zero =>
    unfold jointCount hammersleyPerm hammersleyCountFast countRange bitrev
    simp [countRange]
  | succ k ih =>
    unfold jointCount hammersleyPerm hammersleyCountFast
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hpow, countRange_append]
    by_cases hAle : A ≤ 2 ^ k
    · simp only [hAle, ↓reduceIte]
      have hleft :
          countRange (2 ^ k) (fun u => decide (u < A ∧ bitrev (k + 1) u < B)) =
          jointCount k (hammersleyPerm k) A ((B + 1) / 2) := by
        unfold jointCount hammersleyPerm
        apply countRange_congr
        intro u hu
        rw [bitrev_succ_half hu]
        simp only [decide_eq_decide]
        omega
      have hright :
          countRange (2 ^ k) (fun v => decide (2 ^ k + v < A ∧ bitrev (k + 1) (2 ^ k + v) < B)) = 0 := by
        have hcongr :
            countRange (2 ^ k) (fun v => decide (2 ^ k + v < A ∧ bitrev (k + 1) (2 ^ k + v) < B)) =
            countRange (2 ^ k) (fun _ => false) := by
          apply countRange_congr
          intro v _
          have hfalse : ¬ (2 ^ k + v < A ∧ bitrev (k + 1) (2 ^ k + v) < B) := by omega
          simp [hfalse]
        rw [hcongr]
        have h0 : ∀ n, countRange n (fun _ => false) = 0 := by
          intro n; induction n with | zero => rfl | succ n ihn => simp [countRange, ihn]
        exact h0 (2 ^ k)
      rw [hleft, hright, Nat.add_zero]
      exact ih A ((B + 1) / 2) hAle (by omega)
    · simp only [hAle, ↓reduceIte]
      have hleft :
          countRange (2 ^ k) (fun u => decide (u < A ∧ bitrev (k + 1) u < B)) = (B + 1) / 2 := by
        have hcongr :
            countRange (2 ^ k) (fun u => decide (u < A ∧ bitrev (k + 1) u < B)) =
            countRange (2 ^ k) (fun u => decide (bitrev k u < (B + 1) / 2)) := by
          apply countRange_congr
          intro u hu
          rw [bitrev_succ_half hu]
          simp only [decide_eq_decide]
          omega
        rw [hcongr]
        exact countRange_bitrev_lt k ((B + 1) / 2) (by omega)
      have hright :
          countRange (2 ^ k) (fun v => decide (2 ^ k + v < A ∧ bitrev (k + 1) (2 ^ k + v) < B)) =
          jointCount k (hammersleyPerm k) (A - 2 ^ k) (B / 2) := by
        unfold jointCount hammersleyPerm
        apply countRange_congr
        intro v hv
        rw [bitrev_succ_add_pow hv]
        simp only [decide_eq_decide]
        omega
      rw [hleft, hright, ih (A - 2 ^ k) (B / 2) (by omega) (by omega)]

/-- Universal discrepancy bounds for `bitrev_k` Hammersley for ALL `k` and ALL `A, B ≤ 2^k`:
    `0 ≤ 2^k * count(k, A, B) - A * B ≤ hammersleyBound k A`. -/
theorem hammersleyCountFast_bounds (k A B : Nat) (hA : A ≤ 2 ^ k) (hB : B ≤ 2 ^ k) :
    A * B ≤ 2 ^ k * hammersleyCountFast k A B ∧
    2 ^ k * hammersleyCountFast k A B ≤ A * B + hammersleyBound k A := by
  induction k generalizing A B with
  | zero =>
    unfold hammersleyCountFast hammersleyBound
    have hA' : A = 0 ∨ A = 1 := by omega
    have hB' : B = 0 ∨ B = 1 := by omega
    rcases hA' with rfl | rfl <;> rcases hB' with rfl | rfl <;> decide
  | succ k ih =>
    unfold hammersleyCountFast hammersleyBound
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hAle : A ≤ 2 ^ k
    · simp only [hAle, ↓reduceIte]
      have ⟨hl, hr⟩ := ih A ((B + 1) / 2) hAle (by omega)
      have hmod : B % 2 = 0 ∨ B % 2 = 1 := by omega
      rcases hmod with heven | hodd
      · have hB2 : 2 * ((B + 1) / 2) = B := by omega
        constructor
        · have : A * (2 * ((B + 1) / 2)) ≤ 2 * (2 ^ k * hammersleyCountFast k A ((B + 1) / 2)) := by
            have := Nat.mul_le_mul_left 2 hl
            have hmul : A * (2 * ((B + 1) / 2)) = 2 * (A * ((B + 1) / 2)) := by
              rw [Nat.mul_left_comm]
            omega
          rw [hB2] at this
          rw [hpow, Nat.mul_assoc]
          exact this
        · have h2r := Nat.mul_le_mul_left 2 hr
          have hmul : A * (2 * ((B + 1) / 2)) = 2 * (A * ((B + 1) / 2)) := by
            rw [Nat.mul_left_comm]
          rw [hB2] at hmul
          rw [hpow, Nat.mul_assoc]
          omega
      · have hB2 : 2 * ((B + 1) / 2) = B + 1 := by omega
        have hmul : A * (B + 1) = 2 * (A * ((B + 1) / 2)) := by
          calc A * (B + 1) = A * (2 * ((B + 1) / 2)) := by rw [hB2]
            _ = 2 * (A * ((B + 1) / 2)) := Nat.mul_left_comm A 2 ((B + 1) / 2)
        have h2l := Nat.mul_le_mul_left 2 hl
        have h2r := Nat.mul_le_mul_left 2 hr
        rw [hpow, Nat.mul_assoc]
        have hAB1 : A * (B + 1) = A * B + A := Nat.mul_succ A B
        omega
    · simp only [hAle, ↓reduceIte]
      have ha : A - 2 ^ k ≤ 2 ^ k := by omega
      have hAeq : A = 2 ^ k + (A - 2 ^ k) := by omega
      have ⟨hl, hr⟩ := ih (A - 2 ^ k) (B / 2) ha (by omega)
      have h2l := Nat.mul_le_mul_left 2 hl
      have h2r := Nat.mul_le_mul_left 2 hr
      have hmod : B % 2 = 0 ∨ B % 2 = 1 := by omega
      have hdist : 2 ^ (k + 1) * ((B + 1) / 2 + hammersleyCountFast k (A - 2 ^ k) (B / 2)) =
          2 ^ (k + 1) * ((B + 1) / 2) + 2 * (2 ^ k * hammersleyCountFast k (A - 2 ^ k) (B / 2)) := by
        calc 2 ^ (k + 1) * ((B + 1) / 2 + hammersleyCountFast k (A - 2 ^ k) (B / 2))
          _ = 2 ^ (k + 1) * ((B + 1) / 2) + 2 ^ (k + 1) * hammersleyCountFast k (A - 2 ^ k) (B / 2) :=
              Nat.mul_add _ _ _
          _ = 2 ^ (k + 1) * ((B + 1) / 2) + (2 * 2 ^ k) * hammersleyCountFast k (A - 2 ^ k) (B / 2) := by
              rw [hpow]
          _ = 2 ^ (k + 1) * ((B + 1) / 2) + 2 * (2 ^ k * hammersleyCountFast k (A - 2 ^ k) (B / 2)) := by
              rw [Nat.mul_assoc]
      rw [hdist]
      rcases hmod with heven | hodd
      · have hB1 : 2 * ((B + 1) / 2) = B := by omega
        have hB2 : 2 * (B / 2) = B := by omega
        have hAB : A * B = 2 ^ k * B + 2 * ((A - 2 ^ k) * (B / 2)) := by
          calc A * B = (2 ^ k + (A - 2 ^ k)) * B := by rw [← hAeq]
            _ = 2 ^ k * B + (A - 2 ^ k) * B := Nat.add_mul _ _ _
            _ = 2 ^ k * B + (A - 2 ^ k) * (2 * (B / 2)) := by rw [hB2]
            _ = 2 ^ k * B + 2 * ((A - 2 ^ k) * (B / 2)) := by rw [Nat.mul_left_comm (A - 2 ^ k) 2 (B / 2)]
        have hterm1 : 2 ^ (k + 1) * ((B + 1) / 2) = 2 ^ k * B := by
          calc 2 ^ (k + 1) * ((B + 1) / 2) = (2 * 2 ^ k) * ((B + 1) / 2) := by rw [hpow]
            _ = (2 ^ k * 2) * ((B + 1) / 2) := by rw [Nat.mul_comm 2 (2 ^ k)]
            _ = 2 ^ k * (2 * ((B + 1) / 2)) := Nat.mul_assoc _ _ _
            _ = 2 ^ k * B := by rw [hB1]
        rw [hAB, hterm1]
        omega
      · have hB1 : 2 * ((B + 1) / 2) = B + 1 := by omega
        have hB2 : 2 * (B / 2) + 1 = B := by omega
        have hAB : A * B = 2 ^ k * B + 2 * ((A - 2 ^ k) * (B / 2)) + (A - 2 ^ k) := by
          calc A * B = (2 ^ k + (A - 2 ^ k)) * B := by rw [← hAeq]
            _ = 2 ^ k * B + (A - 2 ^ k) * B := Nat.add_mul _ _ _
            _ = 2 ^ k * B + (A - 2 ^ k) * (2 * (B / 2) + 1) := by rw [hB2]
            _ = 2 ^ k * B + ((A - 2 ^ k) * (2 * (B / 2)) + (A - 2 ^ k) * 1) := by rw [Nat.mul_add]
            _ = 2 ^ k * B + (2 * ((A - 2 ^ k) * (B / 2)) + (A - 2 ^ k)) := by
                rw [Nat.mul_one, Nat.mul_left_comm (A - 2 ^ k) 2 (B / 2)]
            _ = 2 ^ k * B + 2 * ((A - 2 ^ k) * (B / 2)) + (A - 2 ^ k) := by rw [Nat.add_assoc]
        have hterm1 : 2 ^ (k + 1) * ((B + 1) / 2) = 2 ^ k * B + 2 ^ k := by
          calc 2 ^ (k + 1) * ((B + 1) / 2) = (2 * 2 ^ k) * ((B + 1) / 2) := by rw [hpow]
            _ = (2 ^ k * 2) * ((B + 1) / 2) := by rw [Nat.mul_comm 2 (2 ^ k)]
            _ = 2 ^ k * (2 * ((B + 1) / 2)) := Nat.mul_assoc _ _ _
            _ = 2 ^ k * (B + 1) := by rw [hB1]
            _ = 2 ^ k * B + 2 ^ k := Nat.mul_succ _ _
        have hsubA : 2 ^ (k + 1) - A = 2 ^ k - (A - 2 ^ k) := by omega
        rw [hAB, hterm1, hsubA]
        omega

/-- Binary-tree bounded universal check over `[lo, lo + 2^d)` (depth `d`, zero recursion limit issues). -/
def allBelowPow2 : Nat → Nat → (Nat → Bool) → Bool
  | 0, lo, p => p lo
  | d + 1, lo, p => allBelowPow2 d lo p && allBelowPow2 d (lo + 2 ^ d) p

theorem allBelowPow2_true {d lo : Nat} {p : Nat → Bool} (h : allBelowPow2 d lo p = true) :
    ∀ i, lo ≤ i → i < lo + 2 ^ d → p i = true := by
  induction d generalizing lo with
  | zero =>
    intro i hlo hhi
    have heq : i = lo := by omega
    subst heq
    exact h
  | succ d ih =>
    simp only [allBelowPow2, Bool.and_eq_true] at h
    intro i hlo hhi
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    by_cases hmid : i < lo + 2 ^ d
    · exact ih h.1 i hlo hmid
    · exact ih h.2 i (by omega) (by omega)

theorem hammersleyBound_10_le : ∀ A, A ≤ 1024 → hammersleyBound 10 A ≤ 3527 := by
  have hall : allBelowPow2 10 0 (fun A => decide (hammersleyBound 10 A ≤ 3527)) = true := by
    decide
  have h1024 : hammersleyBound 10 1024 ≤ 3527 := by decide
  intro A hA
  by_cases hlt : A < 1024
  · exact of_decide_eq_true (allBelowPow2_true hall A (by omega) hlt)
  · have hEq : A = 1024 := by omega
    subst hEq
    exact h1024

theorem hammersley10_bias_exact :
    (∀ A B, A ≤ 1024 → B ≤ 1024 →
      absRat (doubleQuantBias 10 (hammersleyPerm 10) A B) ≤ 3527 / 1048576) ∧
    absRat (doubleQuantBias 10 (hammersleyPerm 10) 341 341) = 3527 / 1048576 ∧
    (3527 / 1048576 : Rat) * 74 < 1 / 4 := by
  refine ⟨?_, ?_, by grind⟩
  · intro A B hA hB
    have hA' : A ≤ 2 ^ 10 := hA
    have hB' : B ≤ 2 ^ 10 := hB
    have ⟨hl, hr⟩ := hammersleyCountFast_bounds 10 A B hA' hB'
    have hF : hammersleyBound 10 A ≤ 3527 := hammersleyBound_10_le A hA
    rw [← jointCount_hammersley_eq_fast 10 A B hA' hB'] at hl hr
    have hstep := absRat_bias_le_of_int_bound (k := 10) (pi := hammersleyPerm 10)
      (A := A) (B := B) (C := 3527) (by omega) (by omega)
    have hden : ((3527 : Nat) : Rat) / (((2 ^ 10 : Nat) : Rat) * ((2 ^ 10 : Nat) : Rat)) =
        3527 / 1048576 := by grind
    rw [hden] at hstep
    exact hstep
  · rw [doubleQuantBias_eq_int_div, jointCount_hammersley_eq_fast 10 341 341 (by omega) (by omega)]
    have hfast : hammersleyCountFast 10 341 341 = 117 := rfl
    rw [hfast]
    have hval :
        ((((2 ^ 10 * 117 : Nat) : Int) - ((341 * 341 : Nat) : Int) : Int) : Rat) /
        (((2 ^ 10 : Nat) : Rat) * ((2 ^ 10 : Nat) : Rat)) = 3527 / 1048576 := by grind
    rw [hval, absRat_of_nonneg (by grind)]

/-! ### 4. Headline Theorem 5 -/

theorem double_quant_gemm_bias_obstruction_and_hammersley :
    (∀ k, 1 ≤ k →
      (∀ A B, A ≤ 2 ^ k → B ≤ 2 ^ k → absRat (doubleQuantBias k samePerm A B) ≤ 1 / 4) ∧
      absRat (doubleQuantBias k samePerm (2 ^ (k - 1)) (2 ^ (k - 1))) = 1 / 4) ∧
    (∀ k, 1 ≤ k →
      (∀ A B, A ≤ 2 ^ k → B ≤ 2 ^ k → absRat (doubleQuantBias k (antiPerm k) A B) ≤ 1 / 4) ∧
      absRat (doubleQuantBias k (antiPerm k) (2 ^ (k - 1)) (2 ^ (k - 1))) = 1 / 4) ∧
    (∀ k, 1 ≤ k →
      (∀ A B, A ≤ 2 ^ k → B ≤ 2 ^ k → absRat (doubleQuantBias k (msbXorPerm k) A B) ≤ 1 / 4) ∧
      absRat (doubleQuantBias k (msbXorPerm k) (2 ^ (k - 1)) (2 ^ (k - 1))) = 1 / 4) ∧
    (∀ A B, A ≤ 1024 → B ≤ 1024 →
      absRat (doubleQuantBias 10 (hammersleyPerm 10) A B) ≤ 3527 / 1048576) ∧
    absRat (doubleQuantBias 10 (hammersleyPerm 10) 341 341) = 3527 / 1048576 ∧
    (3527 / 1048576 : Rat) * 74 < 1 / 4 :=
  ⟨samePerm_bias_obstruction, antiPerm_bias_obstruction, msbXorPerm_bias_obstruction,
   hammersley10_bias_exact.1, hammersley10_bias_exact.2.1, hammersley10_bias_exact.2.2⟩

/-! ### 5. Theorem 6: Split `2m`-Bit (32-Bit) Word XOR-VDC Zero-Bias Double GEMM -/

theorem discreteMean_split_factor (m : Nat) (f g : Nat → Rat) :
    discreteMean (2 ^ (2 * m)) (fun w => f (splitLow m w) * g (splitHigh m w)) =
    discreteMean (2 ^ m) f * discreteMean (2 ^ m) g := by
  unfold discreteMean splitLow splitHigh
  have hpow : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by
    rw [Nat.two_mul, Nat.pow_add]
  rw [hpow, sumRange_mul_split (2 ^ m) (2 ^ m) (Nat.two_pow_pos m) (fun hi lo => f lo * g hi)]
  have hinner :
      sumRange (2 ^ m) (fun hi => sumRange (2 ^ m) (fun lo => f lo * g hi)) =
      sumRange (2 ^ m) (fun hi => sumRange (2 ^ m) f * g hi) := by
    apply sumRange_congr
    intro hi _
    exact sumRange_mul_right (2 ^ m) f (g hi)
  rw [hinner, sumRange_mul_left, rat_natCast_mul]
  have hMne : ((2 ^ m : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero m
  grind

theorem discreteMean_splitLow (m : Nat) (f : Nat → Rat) :
    discreteMean (2 ^ (2 * m)) (fun w => f (splitLow m w)) = discreteMean (2 ^ m) f := by
  have h := discreteMean_split_factor m f (fun _ => (1 : Rat))
  have h1 : discreteMean (2 ^ m) (fun _ => (1 : Rat)) = 1 := by
    unfold discreteMean
    rw [sumRange_const]
    have hMne : ((2 ^ m : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero m
    grind
  have hcongr :
      discreteMean (2 ^ (2 * m)) (fun w => f (splitLow m w) * (1 : Rat)) =
      discreteMean (2 ^ (2 * m)) (fun w => f (splitLow m w)) := by
    unfold discreteMean
    congr 1
    apply sumRange_congr
    intro w _; grind
  rw [hcongr, h1, Rat.mul_one] at h
  exact h

theorem discreteMean_splitHigh (m : Nat) (g : Nat → Rat) :
    discreteMean (2 ^ (2 * m)) (fun w => g (splitHigh m w)) = discreteMean (2 ^ m) g := by
  have h := discreteMean_split_factor m (fun _ => (1 : Rat)) g
  have h1 : discreteMean (2 ^ m) (fun _ => (1 : Rat)) = 1 := by
    unfold discreteMean
    rw [sumRange_const]
    have hMne : ((2 ^ m : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero m
    grind
  have hcongr :
      discreteMean (2 ^ (2 * m)) (fun w => (1 : Rat) * g (splitHigh m w)) =
      discreteMean (2 ^ (2 * m)) (fun w => g (splitHigh m w)) := by
    unfold discreteMean
    congr 1
    apply sumRange_congr
    intro w _; grind
  rw [hcongr, h1, Rat.one_mul] at h
  exact h

theorem splitWordXorVdc_zero_bias (m b i j : Nat) (hbm : b ≤ m)
    (la ra lb rb : Rat) (pa pb : Nat) (hpa : pa ≤ 2 ^ m) (hpb : pb ≤ 2 ^ m) :
    splitWordXorVdcProdMean m b i j la ra lb rb pa pb =
    (la + (ra - la) * ((pa : Rat) / ((2 ^ m : Nat) : Rat))) *
    (lb + (rb - lb) * ((pb : Rat) / ((2 ^ m : Nat) : Rat))) := by
  unfold splitWordXorVdcProdMean
  rw [discreteMean_split_factor m
    (fun u => srVal la ra pa (xorVdcLane m b i u))
    (fun u => srVal lb rb pb (xorVdcLane m b j u))]
  rw [xorVdcLane_unbiased m b i hbm la ra pa hpa,
      xorVdcLane_unbiased m b j hbm lb rb pb hpb]

theorem splitWordLowSrAvgCov_eq (m b i j : Nat) (hbm : b ≤ m) :
    splitWordLowSrAvgCov m b i j = xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j) := by
  have hrew : splitWordLowSrAvgCov m b i j =
      avgDiscreteSrCov m (xorVdcLane m b i) (xorVdcLane m b j) := by
    unfold splitWordLowSrAvgCov avgDiscreteSrCov discreteCov
    unfold discreteMean
    congr 1
    apply sumRange_congr
    intro p1 _
    congr 1
    apply sumRange_congr
    intro p2 _
    have hm1 := discreteMean_splitLow m (fun u => srErr p1 (2 ^ m) (xorVdcLane m b i u))
    have hm2 := discreteMean_splitLow m (fun u => srErr p2 (2 ^ m) (xorVdcLane m b j u))
    have hprod := discreteMean_splitLow m (fun u =>
      (srErr p1 (2 ^ m) (xorVdcLane m b i u) -
        discreteMean (2 ^ m) (fun u => srErr p1 (2 ^ m) (xorVdcLane m b i u))) *
      (srErr p2 (2 ^ m) (xorVdcLane m b j u) -
        discreteMean (2 ^ m) (fun u => srErr p2 (2 ^ m) (xorVdcLane m b j u))))
    unfold discreteMean at hm1 hm2 hprod
    rw [hm1, hm2]
    exact hprod
  rw [hrew]
  exact (xor_vdc_sr_unbiased_and_covariance_exact m b hbm).2 i j

theorem splitWordHighSrAvgCov_eq (m b i j : Nat) (hbm : b ≤ m) :
    splitWordHighSrAvgCov m b i j = xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j) := by
  have hrew : splitWordHighSrAvgCov m b i j =
      avgDiscreteSrCov m (xorVdcLane m b i) (xorVdcLane m b j) := by
    unfold splitWordHighSrAvgCov avgDiscreteSrCov discreteCov
    unfold discreteMean
    congr 1
    apply sumRange_congr
    intro p1 _
    congr 1
    apply sumRange_congr
    intro p2 _
    have hm1 := discreteMean_splitHigh m (fun u => srErr p1 (2 ^ m) (xorVdcLane m b i u))
    have hm2 := discreteMean_splitHigh m (fun u => srErr p2 (2 ^ m) (xorVdcLane m b j u))
    have hprod := discreteMean_splitHigh m (fun u =>
      (srErr p1 (2 ^ m) (xorVdcLane m b i u) -
        discreteMean (2 ^ m) (fun u => srErr p1 (2 ^ m) (xorVdcLane m b i u))) *
      (srErr p2 (2 ^ m) (xorVdcLane m b j u) -
        discreteMean (2 ^ m) (fun u => srErr p2 (2 ^ m) (xorVdcLane m b j u))))
    unfold discreteMean at hm1 hm2 hprod
    rw [hm1, hm2]
    exact hprod
  rw [hrew]
  exact (xor_vdc_sr_unbiased_and_covariance_exact m b hbm).2 i j

/-- Concrete 32-bit MXFP4 (`m = 16, b = 5`, `B = 32`) adjacent-lane negative covariance witness. -/
theorem mxfp4_32bit_adjacent_cov_neg :
    xorDiscreteAvgCovFormula 16 5 (bitrev 5 0) (bitrev 5 1) < 0 := by
  have hval : xorDiscreteAvgCovFormula 16 5 (bitrev 5 0) (bitrev 5 1) =
      -((1 : Rat) / 24) - (1 : Rat) / (12 * (65536 : Rat) * 65536) := by
    simp only [xorDiscreteAvgCovFormula, xorRankCov, bitrev, sumRange, bitSign, bitAt]
    grind
  rw [hval]
  grind

/-! ### 6. Headline Theorem 6 -/

theorem split_32bit_word_xor_vdc_zero_bias_double_gemm :
    (∀ (m b : Nat), b ≤ m →
      (∀ (i j : Nat) (la ra lb rb : Rat) (pa pb : Nat), pa ≤ 2 ^ m → pb ≤ 2 ^ m →
        splitWordXorVdcProdMean m b i j la ra lb rb pa pb =
        (la + (ra - la) * ((pa : Rat) / ((2 ^ m : Nat) : Rat))) *
        (lb + (rb - lb) * ((pb : Rat) / ((2 ^ m : Nat) : Rat)))) ∧
      (∀ (i j : Nat),
        splitWordLowSrAvgCov m b i j = xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j) ∧
        splitWordHighSrAvgCov m b i j = xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j))) ∧
    (splitWordLowSrAvgCov 16 5 0 1 < 0 ∧ splitWordHighSrAvgCov 16 5 0 1 < 0) := by
  refine ⟨?_, ?_⟩
  · intro m b hbm
    refine ⟨?_, ?_⟩
    · intro i j la ra lb rb pa pb hpa hpb
      exact splitWordXorVdc_zero_bias m b i j hbm la ra lb rb pa pb hpa hpb
    · intro i j
      exact ⟨splitWordLowSrAvgCov_eq m b i j hbm, splitWordHighSrAvgCov_eq m b i j hbm⟩
  · rw [splitWordLowSrAvgCov_eq 16 5 0 1 (by omega), splitWordHighSrAvgCov_eq 16 5 0 1 (by omega)]
    exact ⟨mxfp4_32bit_adjacent_cov_neg, mxfp4_32bit_adjacent_cov_neg⟩

end XorVdcFp4Dither
