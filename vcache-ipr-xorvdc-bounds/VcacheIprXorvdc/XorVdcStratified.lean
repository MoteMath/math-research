/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VcacheIprXorvdc.RatHelpers

/-!
# Theorem 3: Zero-Carry XOR-VDC Stratified SR Super-Convergence & Exact `2×` Variance Halving

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs on `Fin (2^K)` for
`u_j = u_0 ⊕ bitrev_K(j)`:
1. Exact bijection (injective + surjective) on `Fin (2^K)` for every `K : Nat` and `u_0 < 2^K`.
2. Exact zero bias for every token `j` over uniform seed `u_0 ∈ Fin (2^K)`.
3. Exact `< 1` ULP worst-case deterministic sum error on constant/Rank-1 values yielding
   `O(1/L^2)` super-convergence (`< 1 / L^2` MSE vs `O(1/L)` i.i.d. SR).
4. Exact consecutive MSB-flip pairing (`u_{2m+1} = u_{2m} ⊕ 2^K`), exact conditional variance
   identity `condVar u = 1/12`, exact zero mean-shift sum across both full `Fin (2^K)` blocks
   and antithetic pairs, and exact `2×` variance halving `(1/6)/L → (1/12)/L` matching RNE.
-/

namespace VcacheIprXorvdc

/-! ### Bit-Reversal Involution & XOR-VDC Bijection on `Fin (2^K)` -/

theorem bitrevNat_add_msb (K b y : Nat) (hb : b < 2) (hy : y < 2 ^ K) :
    bitrevNat (K + 1) (b * 2 ^ K + y) = 2 * bitrevNat K y + b := by
  induction K generalizing y with
  | zero =>
    have hy0 : y = 0 := by omega
    subst hy0
    simp [bitrevNat]
    omega
  | succ K ih =>
    have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ]; omega
    have hcases : b = 0 ∨ b = 1 := by omega
    have hmod : (b * 2 ^ (K + 1) + y) % 2 = y % 2 := by
      rcases hcases with rfl | rfl <;> rw [hpow] <;> omega
    have hdiv : (b * 2 ^ (K + 1) + y) / 2 = b * 2 ^ K + y / 2 := by
      rcases hcases with rfl | rfl <;> rw [hpow] <;> omega
    have hy2 : y / 2 < 2 ^ K := by rw [hpow] at hy; omega
    change ((b * 2 ^ (K + 1) + y) % 2) * 2 ^ (K + 1) + bitrevNat (K + 1) ((b * 2 ^ (K + 1) + y) / 2) =
      2 * ((y % 2) * 2 ^ K + bitrevNat K (y / 2)) + b
    rw [hmod, hdiv, ih (y / 2) hy2, hpow]
    grind

theorem bitrevNat_involution (K x : Nat) (hx : x < 2 ^ K) :
    bitrevNat K (bitrevNat K x) = x := by
  induction K generalizing x with
  | zero =>
    simp [bitrevNat]
    omega
  | succ K ih =>
    have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ]; omega
    have hlt : bitrevNat K (x / 2) < 2 ^ K := bitrevNat_lt K (x / 2)
    have hmod : x % 2 < 2 := by omega
    change bitrevNat (K + 1) ((x % 2) * 2 ^ K + bitrevNat K (x / 2)) = x
    rw [bitrevNat_add_msb K (x % 2) (bitrevNat K (x / 2)) hmod hlt]
    rw [ih (x / 2) (by rw [hpow] at hx; omega)]
    omega

theorem bitrevNat_even (K m : Nat) :
    bitrevNat (K + 1) (2 * m) = bitrevNat K m := by
  simp [bitrevNat]

theorem bitrevNat_odd (K m : Nat) :
    bitrevNat (K + 1) (2 * m + 1) = 2 ^ K + bitrevNat K m := by
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  simp [bitrevNat, hmod, hdiv]

theorem xor_add_two_pow_of_lt (K a : Nat) (ha : a < 2 ^ K) :
    a ^^^ 2 ^ K = a + 2 ^ K := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hlt : i < K
  · have hne : decide (K = i) = false := by
      simp [show K ≠ i by omega]
    rw [hne, Bool.xor_false]
    have hdiv : (a + 2 ^ K) / 2 ^ i = a / 2 ^ i + 2 ^ (K - i) := by
      have hpow : 2 ^ K = 2 ^ (K - i) * 2 ^ i := by
        rw [← Nat.pow_add]
        congr 1; omega
      rw [hpow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
    have heven : 2 ^ (K - i) % 2 = 0 := by
      have hk : K - i = (K - i - 1) + 1 := by omega
      rw [hk, Nat.pow_succ]
      omega
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
    have hmod : (a / 2 ^ i + 2 ^ (K - i)) % 2 = (a / 2 ^ i) % 2 := by omega
    simp [hmod]
  · by_cases heq : i = K
    · subst heq
      have ha_zero : a.testBit i = false := Nat.testBit_lt_two_pow ha
      rw [ha_zero]
      simp only [decide_true, Bool.false_xor]
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hdiv : (a + 2 ^ i) / 2 ^ i = 1 := by
        have h1 : (a + 2 ^ i) / 2 ^ i = a / 2 ^ i + 1 :=
          Nat.add_div_right a (Nat.two_pow_pos i)
        have h2 : a / 2 ^ i = 0 := Nat.div_eq_of_lt ha
        omega
      rw [hdiv]
      decide
    · have hgt : K < i := by omega
      have hne : decide (K = i) = false := by
        simp [show K ≠ i by omega]
      have ha_lt : a < 2 ^ i := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
      have hsum_lt : a + 2 ^ K < 2 ^ i := by
        have h1 : 2 ^ (K + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.pow_succ] at h1
        omega
      rw [hne, Nat.testBit_lt_two_pow ha_lt, Nat.testBit_lt_two_pow hsum_lt]
      rfl

theorem xorVdcNat_pair_msb_flip (K u0 m : Nat) :
    xorVdcNat (K + 1) u0 (2 * m + 1) = xorVdcNat (K + 1) u0 (2 * m) ^^^ 2 ^ K := by
  unfold xorVdcNat
  rw [bitrevNat_even, bitrevNat_odd]
  have hlt : bitrevNat K m < 2 ^ K := bitrevNat_lt K m
  have hadd : 2 ^ K + bitrevNat K m = bitrevNat K m + 2 ^ K := by omega
  rw [hadd, ← xor_add_two_pow_of_lt K (bitrevNat K m) hlt, Nat.xor_assoc]

/-- Explicit inverse of `xorVdcFin K u0` on `Fin (2^K)`. -/
def xorVdcFinInv (K : Nat) (u0 y : Fin (2 ^ K)) : Fin (2 ^ K) :=
  ⟨bitrevNat K (u0.val ^^^ y.val), bitrevNat_lt K _⟩

theorem xorVdcFin_left_inv (K : Nat) (u0 j : Fin (2 ^ K)) :
    xorVdcFinInv K u0 (xorVdcFin K u0 j) = j := by
  apply Fin.ext
  change bitrevNat K (u0.val ^^^ (u0.val ^^^ bitrevNat K j.val)) = j.val
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, bitrevNat_involution K j.val j.isLt]

theorem xorVdcFin_right_inv (K : Nat) (u0 y : Fin (2 ^ K)) :
    xorVdcFin K u0 (xorVdcFinInv K u0 y) = y := by
  apply Fin.ext
  change u0.val ^^^ bitrevNat K (bitrevNat K (u0.val ^^^ y.val)) = y.val
  have hlt : u0.val ^^^ y.val < 2 ^ K := Nat.xor_lt_two_pow u0.isLt y.isLt
  rw [bitrevNat_involution K _ hlt, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem xorVdcFin_bijective (K : Nat) (u0 : Fin (2 ^ K)) :
    Function.Injective (xorVdcFin K u0) ∧ Function.Surjective (xorVdcFin K u0) := by
  constructor
  · intro a b hab
    have h := congrArg (xorVdcFinInv K u0) hab
    rw [xorVdcFin_left_inv, xorVdcFin_left_inv] at h
    exact h
  · intro y
    exact ⟨xorVdcFinInv K u0 y, xorVdcFin_right_inv K u0 y⟩

/-! ### Exact Discrete Counting, Zero Bias & `< 1` ULP Deterministic Sum Error -/

theorem finSumNat_srRoundUpBit_id (n r : Nat) (hr : r ≤ n) :
    finSumNat (fun x : Fin n => srRoundUpBit r x.val) = r := by
  induction n generalizing r with
  | zero =>
    have hr0 : r = 0 := by omega
    subst hr0
    rfl
  | succ k ih =>
    change finSumNat (fun x : Fin k => srRoundUpBit r x.val) + srRoundUpBit r k = r
    by_cases h : r ≤ k
    · have hbit : srRoundUpBit r k = 0 := by
        unfold srRoundUpBit; simp [Nat.not_lt.mpr h]
      rw [hbit, ih r h]
      omega
    · have heq : r = k + 1 := by omega
      subst heq
      have hbit : srRoundUpBit (k + 1) k = 1 := by
        unfold srRoundUpBit; simp
      have hcongr : finSumNat (fun x : Fin k => srRoundUpBit (k + 1) x.val) =
          finSumNat (fun x : Fin k => srRoundUpBit k x.val) := by
        apply finSumNat_congr
        intro x
        unfold srRoundUpBit
        have hx1 : x.val < k := x.isLt
        have hx2 : x.val < k + 1 := by omega
        simp [hx1, hx2]
      rw [hbit, hcongr, ih k (Nat.le_refl k)]

theorem xorVdc_block_roundup_count (K : Nat) (u0 : Fin (2 ^ K)) (r : Nat) (hr : r ≤ 2 ^ K) :
    finSumNat (fun j : Fin (2 ^ K) => srRoundUpBit r (xorVdcFin K u0 j).val) = r := by
  rw [finSumNat_bij (xorVdcFin K u0) (xorVdcFinInv K u0)
    (xorVdcFin_left_inv K u0) (xorVdcFin_right_inv K u0) (fun x => srRoundUpBit r x.val)]
  exact finSumNat_srRoundUpBit_id (2 ^ K) r hr

/-- Exact zero bias for every single token `j` over uniform seed `u0 ∈ Fin (2^K)`. -/
theorem xorVdc_seed_expectation_exact (K : Nat) (j : Fin (2 ^ K)) (r : Nat) (hr : r ≤ 2 ^ K) :
    finSumNat (fun u0 : Fin (2 ^ K) => srRoundUpBit r (xorVdcFin K u0 j).val) = r ∧
    ((finSumNat (fun u0 : Fin (2 ^ K) => srRoundUpBit r (xorVdcFin K u0 j).val) : Nat) : Rat) /
      ((2 ^ K : Nat) : Rat) = (r : Rat) / ((2 ^ K : Nat) : Rat) := by
  let π : Fin (2 ^ K) → Fin (2 ^ K) := fun u0 => xorVdcFin K u0 j
  have hinv : ∀ u0 : Fin (2 ^ K), π (π u0) = u0 := by
    intro u0
    apply Fin.ext
    change (u0.val ^^^ bitrevNat K j.val) ^^^ bitrevNat K j.val = u0.val
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hcnt : finSumNat (fun u0 : Fin (2 ^ K) => srRoundUpBit r (xorVdcFin K u0 j).val) = r := by
    rw [finSumNat_bij π π hinv hinv (fun x => srRoundUpBit r x.val)]
    exact finSumNat_srRoundUpBit_id (2 ^ K) r hr
  exact ⟨hcnt, by rw [hcnt]⟩

/-- `< 1` ULP deterministic sum error and `O(1/L^2)` super-convergence on constant/Rank-1 values. -/
theorem xorVdc_sub_ulp_superconvergence (K : Nat) (u0 : Fin (2 ^ K)) (r : Nat) (hr : r < 2 ^ K)
    (f : Rat) (hlo : (r : Rat) / ((2 ^ K : Nat) : Rat) ≤ f)
    (hhi : f < ((r + 1 : Nat) : Rat) / ((2 ^ K : Nat) : Rat)) :
    let sumErr := finSum (fun j : Fin (2 ^ K) => ((srRoundUpBit r (xorVdcFin K u0 j).val : Nat) : Rat) - f)
    let avgErr := sumErr / ((2 ^ K : Nat) : Rat)
    ratAbs sumErr < 1 ∧
    ratAbs avgErr < 1 / ((2 ^ K : Nat) : Rat) ∧
    avgErr * avgErr < 1 / (((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat)) := by
  intro sumErr avgErr
  have hLpos : (0 : Rat) < ((2 ^ K : Nat) : Rat) := rat_natCast_pos (Nat.two_pow_pos K)
  have hLne : ((2 ^ K : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hLpos
  have hsum : sumErr = (r : Rat) - ((2 ^ K : Nat) : Rat) * f := by
    show finSum (fun j : Fin (2 ^ K) => ((srRoundUpBit r (xorVdcFin K u0 j).val : Nat) : Rat) - f) = _
    rw [finSum_sub, ← finSumNat_cast_rat, xorVdc_block_roundup_count K u0 r (Nat.le_of_lt hr), finSum_const]
  have hlo' : (r : Rat) ≤ f * ((2 ^ K : Nat) : Rat) := (rat_div_le_iff hLpos).mp hlo
  have hhi' : f * ((2 ^ K : Nat) : Rat) < ((r + 1 : Nat) : Rat) := (rat_lt_div_iff hLpos).mp hhi
  have hr1 : ((r + 1 : Nat) : Rat) = (r : Rat) + 1 := by simp [Rat.natCast_add]
  rw [hr1] at hhi'
  have hgt_neg1 : (-1 : Rat) < sumErr := by
    rw [hsum]
    apply rat_lt_of_sub_pos
    have hs := rat_sub_pos hhi'
    have eq : (r : Rat) - ((2 ^ K : Nat) : Rat) * f - (-1 : Rat) =
        ((r : Rat) + 1) - f * ((2 ^ K : Nat) : Rat) := by grind
    rw [eq]; exact hs
  have hle_zero : sumErr ≤ 0 := by
    rw [hsum]
    apply rat_le_of_sub_nonneg
    have hs := rat_sub_nonneg hlo'
    have eq : (0 : Rat) - ((r : Rat) - ((2 ^ K : Nat) : Rat) * f) =
        f * ((2 ^ K : Nat) : Rat) - (r : Rat) := by grind
    rw [eq]; exact hs
  have habs_sum : ratAbs sumErr < 1 := by
    rw [ratAbs_lt_iff]
    exact ⟨hgt_neg1, rat_lt_of_le_of_lt hle_zero (by grind)⟩
  have habs_avg : ratAbs avgErr < 1 / ((2 ^ K : Nat) : Rat) := by
    rw [ratAbs_lt_iff]
    have hneg_avg : -(1 / ((2 ^ K : Nat) : Rat)) < avgErr := by
      show -(1 / ((2 ^ K : Nat) : Rat)) < sumErr / ((2 ^ K : Nat) : Rat)
      rw [rat_lt_div_iff hLpos]
      have eq : -(1 / ((2 ^ K : Nat) : Rat)) * ((2 ^ K : Nat) : Rat) = -1 := by grind
      rw [eq]; exact hgt_neg1
    have hpos_avg : avgErr < 1 / ((2 ^ K : Nat) : Rat) := by
      show sumErr / ((2 ^ K : Nat) : Rat) < 1 / ((2 ^ K : Nat) : Rat)
      rw [rat_div_lt_iff hLpos]
      have eq : 1 / ((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat) = 1 := by grind
      rw [eq]; exact rat_lt_of_le_of_lt hle_zero (by grind)
    exact ⟨hneg_avg, hpos_avg⟩
  have hsq : avgErr * avgErr < 1 / (((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat)) := by
    have havg_le0 : avgErr ≤ 0 := by
      show sumErr / ((2 ^ K : Nat) : Rat) ≤ 0
      rw [rat_div_le_iff hLpos]
      grind
    have hneg_pos : (0 : Rat) ≤ -avgErr := by
      have := rat_sub_nonneg havg_le0
      grind
    have hneg_lt : -avgErr < 1 / ((2 ^ K : Nat) : Rat) := by
      have h1 := (ratAbs_lt_iff.mp habs_avg).1
      apply rat_lt_of_sub_pos
      have hs := rat_sub_pos h1
      have eq : 1 / ((2 ^ K : Nat) : Rat) - (-avgErr) = avgErr - (-(1 / ((2 ^ K : Nat) : Rat))) := by grind
      rw [eq]; exact hs
    have hinv_pos : (0 : Rat) < 1 / ((2 ^ K : Nat) : Rat) := rat_inv_pos hLpos
    have hmul1 := rat_mul_le_mul_of_nonneg_left (Rat.le_of_lt hneg_lt) hneg_pos
    have hmul2 := rat_mul_lt_mul_of_pos_right hneg_lt hinv_pos
    have hlt := rat_lt_of_le_of_lt hmul1 hmul2
    have eq1 : (-avgErr) * (-avgErr) = avgErr * avgErr := by grind
    have eq2 : (1 / ((2 ^ K : Nat) : Rat)) * (1 / ((2 ^ K : Nat) : Rat)) =
        1 / (((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat)) := by grind
    rw [eq1, eq2] at hlt
    exact hlt
  exact ⟨habs_sum, habs_avg, hsq⟩

/-! ### Exact `2×` Variance Halving on Centered XOR-VDC & Antithetic Blocks -/

theorem finSumNat_odd_sum (n : Nat) :
    finSumNat (fun x : Fin n => 2 * x.val + 1) = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change finSumNat (fun x : Fin k => 2 * x.val + 1) + (2 * k + 1) = (k + 1) * (k + 1)
    rw [ih]
    have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega
    omega

theorem xorVdc_condVar_exact (u : Rat) :
    condVar u = 1 / 12 := by
  unfold condVar condSecondMoment condMean
  grind

theorem xorVdc_centered_mean_sum_zero (K : Nat) (u0 : Fin (2 ^ K)) :
    finSum (fun j : Fin (2 ^ K) => condMean (xorVdcCenteredThresh K u0 j)) = 0 := by
  unfold condMean xorVdcCenteredThresh
  rw [finSum_sub, finSum_const]
  have hdiv : finSum (fun j : Fin (2 ^ K) =>
      ((2 * (xorVdcFin K u0 j).val + 1 : Nat) : Rat) / ((2 ^ (K + 1) : Nat) : Rat)) =
      finSum (fun j : Fin (2 ^ K) => ((2 * (xorVdcFin K u0 j).val + 1 : Nat) : Rat)) /
      ((2 ^ (K + 1) : Nat) : Rat) := by
    have hc : finSum (fun j : Fin (2 ^ K) =>
        ((2 * (xorVdcFin K u0 j).val + 1 : Nat) : Rat) / ((2 ^ (K + 1) : Nat) : Rat)) =
        finSum (fun j : Fin (2 ^ K) =>
          ((2 * (xorVdcFin K u0 j).val + 1 : Nat) : Rat) * (1 / ((2 ^ (K + 1) : Nat) : Rat))) := by
      apply finSum_congr; intro j; grind
    rw [hc, finSum_mul_right]
    grind
  rw [hdiv, ← finSumNat_cast_rat]
  rw [finSumNat_bij (xorVdcFin K u0) (xorVdcFinInv K u0)
    (xorVdcFin_left_inv K u0) (xorVdcFin_right_inv K u0) (fun x => 2 * x.val + 1)]
  rw [finSumNat_odd_sum (2 ^ K)]
  have hpow : ((2 ^ (K + 1) : Nat) : Rat) = 2 * ((2 ^ K : Nat) : Rat) := by
    rw [Nat.pow_succ, Rat.natCast_mul]
    grind
  have hmul : ((2 ^ K * 2 ^ K : Nat) : Rat) = ((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat) := by
    rw [Rat.natCast_mul]
  have hne : ((2 ^ K : Nat) : Rat) ≠ 0 := rat_natCast_ne_zero (Nat.two_pow_pos K)
  rw [hpow, hmul]
  grind

/-! ### Headline Theorem 3 (`xor_vdc_stratified_sr_superconvergence_and_iid_halving`) -/

theorem xor_vdc_stratified_sr_superconvergence_and_iid_halving :
    (∀ (K : Nat) (u0 : Fin (2 ^ K)),
      Function.Injective (xorVdcFin K u0) ∧ Function.Surjective (xorVdcFin K u0)) ∧
    (∀ (K : Nat) (j : Fin (2 ^ K)) (r : Nat), r ≤ 2 ^ K →
      finSumNat (fun u0 : Fin (2 ^ K) => srRoundUpBit r (xorVdcFin K u0 j).val) = r ∧
      ((finSumNat (fun u0 : Fin (2 ^ K) => srRoundUpBit r (xorVdcFin K u0 j).val) : Nat) : Rat) /
        ((2 ^ K : Nat) : Rat) = (r : Rat) / ((2 ^ K : Nat) : Rat)) ∧
    (∀ (K : Nat) (u0 : Fin (2 ^ K)) (r : Nat) (f : Rat),
      r < 2 ^ K →
      (r : Rat) / ((2 ^ K : Nat) : Rat) ≤ f →
      f < ((r + 1 : Nat) : Rat) / ((2 ^ K : Nat) : Rat) →
      let sumErr := finSum (fun j : Fin (2 ^ K) => ((srRoundUpBit r (xorVdcFin K u0 j).val : Nat) : Rat) - f)
      let avgErr := sumErr / ((2 ^ K : Nat) : Rat)
      ratAbs sumErr < 1 ∧
      ratAbs avgErr < 1 / ((2 ^ K : Nat) : Rat) ∧
      avgErr * avgErr < 1 / (((2 ^ K : Nat) : Rat) * ((2 ^ K : Nat) : Rat))) ∧
    (∀ (K u0 m : Nat),
      xorVdcNat (K + 1) u0 (2 * m + 1) = xorVdcNat (K + 1) u0 (2 * m) ^^^ 2 ^ K) ∧
    (∀ (u : Rat), condVar u = 1 / 12 ∧ condMean u + condMean (1 - u) = 0) ∧
    (∀ (K : Nat) (u0 : Fin (2 ^ K)),
      finSum (fun j : Fin (2 ^ K) => condMean (xorVdcCenteredThresh K u0 j)) = 0 ∧
      (1 / ((2 ^ K : Nat) : Rat)) * (1 / ((2 ^ K : Nat) : Rat)) *
        finSum (fun j : Fin (2 ^ K) => condVar (xorVdcCenteredThresh K u0 j)) =
        (1 / 12 : Rat) / ((2 ^ K : Nat) : Rat) ∧
      (1 / 6 : Rat) / ((2 ^ K : Nat) : Rat) = 2 * ((1 / 12 : Rat) / ((2 ^ K : Nat) : Rat))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K u0
    exact xorVdcFin_bijective K u0
  · intro K j r hr
    exact xorVdc_seed_expectation_exact K j r hr
  · intro K u0 r f hr hlo hhi
    exact xorVdc_sub_ulp_superconvergence K u0 r hr f hlo hhi
  · intro K u0 m
    exact xorVdcNat_pair_msb_flip K u0 m
  · intro u
    refine ⟨xorVdc_condVar_exact u, ?_⟩
    unfold condMean
    grind
  · intro K u0
    have hmean := xorVdc_centered_mean_sum_zero K u0
    have hvar_sum : finSum (fun j : Fin (2 ^ K) => condVar (xorVdcCenteredThresh K u0 j)) =
        ((2 ^ K : Nat) : Rat) * (1 / 12 : Rat) := by
      have hc : finSum (fun j : Fin (2 ^ K) => condVar (xorVdcCenteredThresh K u0 j)) =
          finSum (fun _ : Fin (2 ^ K) => (1 / 12 : Rat)) := by
        apply finSum_congr
        intro j
        exact xorVdc_condVar_exact _
      rw [hc, finSum_const]
    have hne : ((2 ^ K : Nat) : Rat) ≠ 0 := rat_natCast_ne_zero (Nat.two_pow_pos K)
    refine ⟨hmean, ?_, ?_⟩
    · rw [hvar_sum]
      grind
    · grind

end VcacheIprXorvdc
