/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlibiBitsplitKulisch.RatOrder

/-!
# Pillar 1: Exact `ALiBi` Content-Swamping Horizon, Binade Asymmetry & Dyadic Slope Optimality

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. Universal IEEE-754 RNE content-swamping threshold `B ≥ 2^{p+1} |x| → rneSwampsAtNegB p e M x`.
2. Exact power-of-2 binade asymmetry between `-x` (outward) and `+x` (inward) at `B = 2^e`.
3. Concrete `BF16`, `FP8-E4M3` (`d = 19..23` swamping & `d = 465` overflow), and `FP16`
   (`d = 65520 < 131072` overflow) horizons.
4. Exact zero multiplication rounding error for dyadic slopes `m = 2^{-k}`.
-/

namespace AlibiBitsplitKulisch

/-- Exact bias value at the power-of-2 binade boundary `M = 2^{p-1}` is `2^e`. -/
theorem alibiBias_pow2_boundary (p : Nat) (e : Int) :
    alibiBias p e (2 ^ (p - 1)) = zpow2Rat e := by
  unfold alibiBias
  have hcast : ((2 ^ (p - 1) : Nat) : Rat) = zpow2Rat ((p - 1 : Nat) : Int) := by
    rw [zpow2Rat_ofNat]; rfl
  rw [hcast, ← zpow2Rat_add]
  have he : ((p - 1 : Nat) : Int) + (e - ((p - 1 : Nat) : Int)) = e := by omega
  rw [he]

/-- For `2 ≤ p`, `2^{p-1}` is even (`(2^{p-1}) % 2 = 0`). -/
theorem pow2_pred_even {p : Nat} (hp : 2 ≤ p) : (2 ^ (p - 1)) % 2 = 0 := by
  have hk : p - 1 = (p - 2) + 1 := by omega
  rw [hk, Nat.pow_succ]
  omega

/-- Strict upper bound on `alibiBias` in binade `[2^e, 2^{e+1})`: `alibiBias p e M < 2^{e+1}`. -/
theorem alibiBias_lt_binade_top {p : Nat} (hp : 2 ≤ p) (e : Int) {M : Nat} (hM : M < 2 ^ p) :
    alibiBias p e M < zpow2Rat (e + 1) := by
  unfold alibiBias
  have hMrat : (M : Rat) < pow2Rat p := rat_natCast_lt hM
  have hmul : (M : Rat) * zpow2Rat (e - ((p - 1 : Nat) : Int)) <
      pow2Rat p * zpow2Rat (e - ((p - 1 : Nat) : Int)) :=
    rat_mul_lt_mul_of_pos_right hMrat (zpow2Rat_pos _)
  have htop : pow2Rat p * zpow2Rat (e - ((p - 1 : Nat) : Int)) = zpow2Rat (e + 1) := by
    rw [← zpow2Rat_ofNat p, ← zpow2Rat_add]
    have he : (p : Int) + (e - ((p - 1 : Nat) : Int)) = e + 1 := by omega
    rw [he]
  rw [htop] at hmul
  exact hmul

/-- Universal IEEE-754 RNE ALiBi content-swamping theorem:
    whenever `B = M * 2^{e - (p - 1)} ≥ 2^{p+1} * |x|`, `fl_p(x - B) = -B` erases 100% of `x`,
    covering both `+x` and `-x` and every normal significand `M ∈ [2^{p-1}, 2^p - 1]`. -/
theorem rneSwampsAtNegB_of_ge_two_pow_succ_mul_abs {p : Nat} (hp : 2 ≤ p) (e : Int) {M : Nat}
    (hMlo : 2 ^ (p - 1) ≤ M) (hMhi : M < 2 ^ p) {x : Rat}
    (hge : pow2Rat (p + 1) * ratAbs x ≤ alibiBias p e M) :
    rneSwampsAtNegB p e M x := by
  have hB_lt : alibiBias p e M < zpow2Rat (e + 1) := alibiBias_lt_binade_top hp e hMhi
  have hlt_top : pow2Rat (p + 1) * ratAbs x < zpow2Rat (e + 1) :=
    rat_lt_of_le_of_lt hge hB_lt
  have hpow_pos : (0 : Rat) < pow2Rat (p + 1) := pow2Rat_pos (p + 1)
  have habs_lt_out : ratAbs x < alibiHalfUlpOut p e := by
    unfold alibiHalfUlpOut
    have hmul : ratAbs x * pow2Rat (p + 1) < zpow2Rat (e - (p : Int)) * pow2Rat (p + 1) := by
      have hrhs : zpow2Rat (e - (p : Int)) * pow2Rat (p + 1) = zpow2Rat (e + 1) := by
        rw [← zpow2Rat_ofNat (p + 1), ← zpow2Rat_add]
        have he : e - (p : Int) + ((p + 1 : Nat) : Int) = e + 1 := by omega
        rw [he]
      rw [hrhs, Rat.mul_comm]
      exact hlt_top
    exact rat_lt_of_mul_pos_right hpow_pos hmul
  unfold rneSwampsAtNegB
  split
  · rename_i hxle
    have habs : ratAbs x = -x := ratAbs_of_nonpos hxle
    rw [habs] at habs_lt_out
    split
    · exact Rat.le_of_lt habs_lt_out
    · exact habs_lt_out
  · rename_i hxnotle
    have hxpos : (0 : Rat) < x := Rat.not_le.mp hxnotle
    have habs : ratAbs x = x := ratAbs_of_nonneg (Rat.le_of_lt hxpos)
    rw [habs] at habs_lt_out hge
    unfold alibiHalfUlpIn
    by_cases hbdry : M = 2 ^ (p - 1)
    · subst hbdry
      have heven : (2 ^ (p - 1)) % 2 = 0 := pow2_pred_even hp
      simp only [heven, ite_true]
      rw [alibiBias_pow2_boundary] at hge
      have hmul : x * pow2Rat (p + 1) ≤ zpow2Rat (e - (p : Int) - 1) * pow2Rat (p + 1) := by
        have hrhs : zpow2Rat (e - (p : Int) - 1) * pow2Rat (p + 1) = zpow2Rat e := by
          rw [← zpow2Rat_ofNat (p + 1), ← zpow2Rat_add]
          have he : e - (p : Int) - 1 + ((p + 1 : Nat) : Int) = e := by omega
          rw [he]
        rw [hrhs, Rat.mul_comm]
        exact hge
      exact rat_le_of_mul_pos_right hpow_pos hmul
    · simp only [hbdry, ite_false]
      split
      · exact Rat.le_of_lt habs_lt_out
      · exact habs_lt_out

/-- Exact power-of-2 binade asymmetry: at `B = 2^e` (`M = 2^{p-1}`),
    for `x = 2^{e-p}`, outward `-x` IS swamped while inward `+x` is NOT swamped. -/
theorem binade_asymmetry_exact {p : Nat} (hp : 2 ≤ p) (e : Int) :
    let x := zpow2Rat (e - (p : Int))
    rneSwampsAtNegB p e (2 ^ (p - 1)) (-x) ∧
    ¬ rneSwampsAtNegB p e (2 ^ (p - 1)) x := by
  intro x
  have hxpos : (0 : Rat) < x := zpow2Rat_pos (e - (p : Int))
  have hneg_le : -x ≤ 0 := by
    have := rat_sub_nonneg (Rat.le_of_lt hxpos)
    grind
  have heven : (2 ^ (p - 1)) % 2 = 0 := pow2_pred_even hp
  constructor
  · unfold rneSwampsAtNegB alibiHalfUlpOut
    simp only [hneg_le, heven, ite_true]
    have hnn : - -x = x := by grind
    rw [hnn]
    exact Rat.le_refl
  · unfold rneSwampsAtNegB alibiHalfUlpIn
    have hnotle : ¬ (x ≤ 0) := Rat.not_le.mpr hxpos
    simp only [hnotle, heven, ite_true, ite_false]
    -- Show `zpow2Rat (e - p - 1) < zpow2Rat (e - p)`
    have hdouble : zpow2Rat (e - (p : Int)) = 2 * zpow2Rat (e - (p : Int) - 1) := by
      have h2 : (2 : Rat) = zpow2Rat 1 := by unfold zpow2Rat pow2Rat; decide
      rw [h2, ← zpow2Rat_add]
      have he : (1 : Int) + (e - (p : Int) - 1) = e - (p : Int) := by omega
      rw [he]
    have hlt : zpow2Rat (e - (p : Int) - 1) < x := by
      change zpow2Rat (e - (p : Int) - 1) < zpow2Rat (e - (p : Int))
      rw [hdouble]
      have hp1 : (0 : Rat) < zpow2Rat (e - (p : Int) - 1) := zpow2Rat_pos _
      apply rat_lt_of_sub_pos
      have : 2 * zpow2Rat (e - (p : Int) - 1) - zpow2Rat (e - (p : Int) - 1) =
          zpow2Rat (e - (p : Int) - 1) := by grind
      rw [this]; exact hp1
    exact Rat.not_le.mpr hlt

/-- Exact dyadic slope closure: multiplying any exact `p`-bit normal float (or `0`)
    by `2^{-k}` produces an exact `p`-bit float with zero multiplication rounding error. -/
theorem dyadic_slope_zero_mul_error (p : Nat) (v : Rat) (k : Nat)
    (hv : isExactPBitFloat p v) :
    isExactPBitFloat p (v * invPow2Rat k) := by
  cases hv with
  | inl hv0 =>
    left
    rw [hv0, Rat.zero_mul]
  | inr h =>
    rcases h with ⟨e, M, hlo, hhi, habs⟩
    right
    refine ⟨e - (k : Int), M, hlo, hhi, ?_⟩
    rw [ratAbs_mul, habs, ratAbs_of_nonneg (Rat.le_of_lt (invPow2Rat_pos k))]
    unfold alibiBias
    rw [Rat.mul_assoc, ← zpow2Rat_neg_ofNat k, ← zpow2Rat_add]
    have he : e - ((p - 1 : Nat) : Int) + -(k : Int) = (e - (k : Int)) - ((p - 1 : Nat) : Int) := by
      omega
    rw [he]

/-- Every positive integer `n < 2^p` can be normalized into `[2^{p-1}, 2^p - 1]` by a power of 2. -/
theorem nat_lt_pow2_exact_pbit {p : Nat} (hp : 2 ≤ p) :
    ∀ (d : Nat), d ≤ 2 ^ p → isExactPBitFloat p (d : Rat) := by
  intro d hd
  by_cases hd0 : d = 0
  · left; subst hd0; rfl
  · by_cases hdeq : d = 2 ^ p
    · right
      refine ⟨(p : Int), 2 ^ (p - 1), Nat.le_refl _, ?_, ?_⟩
      · exact Nat.pow_lt_pow_right (by decide) (by omega)
      · rw [hdeq, ratAbs_of_nonneg (rat_natCast_nonneg _), alibiBias_pow2_boundary,
            zpow2Rat_ofNat]
        rfl
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hdlt : d < 2 ^ p := Nat.lt_of_le_of_ne hd hdeq
      -- Let `e = Nat.log2 d`, so `2^e ≤ d < 2^{e+1}` and `e ≤ p - 1`.
      let e : Nat := Nat.log2 d
      have hlo_e : 2 ^ e ≤ d := Nat.log2_self_le hd0
      have hhi_e : d < 2 ^ (e + 1) := Nat.lt_log2_self
      have he_le : e ≤ p - 1 := by
        by_cases hle : e ≤ p - 1
        · exact hle
        · have hge : p ≤ e := by omega
          have hpow : 2 ^ p ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) hge
          omega
      let shift : Nat := (p - 1) - e
      let M : Nat := d * 2 ^ shift
      have hMlo : 2 ^ (p - 1) ≤ M := by
        have h1 : 2 ^ e * 2 ^ shift = 2 ^ (p - 1) := by
          rw [← Nat.pow_add]
          have : e + shift = p - 1 := by omega
          rw [this]
        rw [← h1]
        exact Nat.mul_le_mul_right (2 ^ shift) hlo_e
      have hMhi : M < 2 ^ p := by
        have h1 : 2 ^ (e + 1) * 2 ^ shift = 2 ^ p := by
          rw [← Nat.pow_add]
          have : e + 1 + shift = p := by omega
          rw [this]
        rw [← h1]
        exact Nat.mul_lt_mul_of_pos_right hhi_e (Nat.pow_pos (by decide))
      right
      refine ⟨(e : Int), M, hMlo, hMhi, ?_⟩
      rw [ratAbs_of_nonneg (rat_natCast_nonneg _)]
      unfold alibiBias
      have hesub : (e : Int) - ((p - 1 : Nat) : Int) = -(shift : Int) := by omega
      rw [hesub, zpow2Rat_neg_ofNat]
      show (d : Rat) = ((d * 2 ^ shift : Nat) : Rat) * invPow2Rat shift
      rw [Rat.natCast_mul]
      change (d : Rat) = (d : Rat) * pow2Rat shift * invPow2Rat shift
      rw [Rat.mul_assoc, pow2Rat_mul_invPow2Rat, Rat.mul_one]

/-- Every even integer `d ≤ 2^{p+1}` is also an exact `p`-bit float. -/
theorem even_nat_le_pow2_succ_exact_pbit {p : Nat} (hp : 2 ≤ p) (d : Nat)
    (heven : d % 2 = 0) (hd : d ≤ 2 ^ (p + 1)) :
    isExactPBitFloat p (d : Rat) := by
  have hhalf_le : d / 2 ≤ 2 ^ p := by
    have hpow : 2 ^ (p + 1) = 2 ^ p * 2 := Nat.pow_succ 2 p
    omega
  have hhalf_exact : isExactPBitFloat p ((d / 2 : Nat) : Rat) :=
    nat_lt_pow2_exact_pbit hp (d / 2) hhalf_le
  have hd_eq : (d : Rat) = ((d / 2 : Nat) : Rat) * (2 : Rat) := by
    have hnat : d = (d / 2) * 2 := by omega
    have hcast : ((d : Nat) : Rat) = (((d / 2) * 2 : Nat) : Rat) := congrArg Nat.cast hnat
    rw [hcast, Rat.natCast_mul]
    rfl
  cases hhalf_exact with
  | inl h0 =>
    left
    rw [hd_eq, h0, Rat.zero_mul]
  | inr h =>
    rcases h with ⟨e, M, hlo, hhi, habs⟩
    right
    refine ⟨e + 1, M, hlo, hhi, ?_⟩
    rw [hd_eq, ratAbs_mul, habs, ratAbs_of_nonneg (by decide)]
    unfold alibiBias
    have h2 : (2 : Rat) = zpow2Rat 1 := by unfold zpow2Rat pow2Rat; decide
    rw [h2, Rat.mul_assoc, ← zpow2Rat_add]
    have he : e - ((p - 1 : Nat) : Int) + 1 = (e + 1) - ((p - 1 : Nat) : Int) := by omega
    rw [he]

/-- Headline Theorem 1 (`alibi_content_swamping_and_dyadic_slope_exact`):
    Proves the universal IEEE-754 RNE ALiBi content-swamping threshold `B ≥ 2^{p+1} |x|`,
    the exact power-of-2 binade asymmetry for `+x` vs `-x`, concrete `BF16` / `FP8-E4M3` / `FP16`
    swamping and overflow horizons (`d = 465` for FP8-E4M3, `d = 65520 < 131072` for FP16),
    and exact zero multiplication rounding error for dyadic slopes `m = 2^{-k}`. -/
theorem alibi_content_swamping_and_dyadic_slope_exact :
    (∀ (p : Nat) (e : Int) (M : Nat) (x : Rat),
      2 ≤ p → 2 ^ (p - 1) ≤ M → M < 2 ^ p →
      pow2Rat (p + 1) * ratAbs x ≤ alibiBias p e M →
      rneSwampsAtNegB p e M x) ∧
    (∀ (p : Nat) (e : Int), 2 ≤ p →
      let x := zpow2Rat (e - (p : Int))
      alibiBias p e (2 ^ (p - 1)) = zpow2Rat e ∧
      rneSwampsAtNegB p e (2 ^ (p - 1)) (-x) ∧
      ¬ rneSwampsAtNegB p e (2 ^ (p - 1)) x) ∧
    (alibiBias 8 8 128 = 256 ∧
      rneSwampsAtNegB 8 8 128 (-1) ∧
      ¬ rneSwampsAtNegB 8 8 128 1 ∧
      alibiBias 8 8 130 = 260 ∧
      rneSwampsAtNegB 8 8 130 1) ∧
    (alibiBias 4 4 8 = 16 ∧
      rneSwampsAtNegB 4 4 8 (-1) ∧
      ¬ rneSwampsAtNegB 4 4 8 1 ∧
      alibiBias 4 4 10 = 20 ∧
      rneSwampsAtNegB 4 4 10 1 ∧
      fp8E4M3Overflows 465 ∧
      ¬ fp8E4M3Overflows 464) ∧
    (fp16Overflows 65520 ∧
      (65520 : Nat) < 131072 ∧
      ¬ fp16Overflows 65519) ∧
    (∀ (p : Nat) (v : Rat) (k : Nat),
      isExactPBitFloat p v → isExactPBitFloat p (v * invPow2Rat k)) ∧
    (∀ (p d k : Nat), 2 ≤ p → d ≤ 2 ^ p →
      isExactPBitFloat p (d : Rat) ∧ isExactPBitFloat p ((d : Rat) * invPow2Rat k)) ∧
    (∀ (p d k : Nat), 2 ≤ p → d % 2 = 0 → d ≤ 2 ^ (p + 1) →
      isExactPBitFloat p (d : Rat) ∧ isExactPBitFloat p ((d : Rat) * invPow2Rat k)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p e M x hp hlo hhi hge
    exact rneSwampsAtNegB_of_ge_two_pow_succ_mul_abs hp e hlo hhi hge
  · intro p e hp
    exact ⟨alibiBias_pow2_boundary p e, binade_asymmetry_exact hp e⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold alibiBias
      have he : (8 : Int) - ((8 - 1 : Nat) : Int) = ((1 : Nat) : Int) := rfl
      rw [he, zpow2Rat_ofNat]; unfold pow2Rat; grind
    · unfold rneSwampsAtNegB alibiHalfUlpOut
      have h1 : (-1 : Rat) ≤ 0 := by decide
      have h2 : (128 : Nat) % 2 = 0 := rfl
      have he : (8 : Int) - ((8 : Nat) : Int) = ((0 : Nat) : Int) := rfl
      simp only [h1, h2, ite_true]
      rw [he, zpow2Rat_ofNat]
      unfold pow2Rat
      have h0 : ((2 ^ 0 : Nat) : Rat) = 1 := rfl
      have hm : -(-1 : Rat) = 1 := by grind
      rw [h0, hm]; exact Rat.le_refl
    · unfold rneSwampsAtNegB alibiHalfUlpIn
      have h1 : ¬ ((1 : Rat) ≤ 0) := by decide
      have h2 : (128 : Nat) % 2 = 0 := rfl
      have h3 : (128 : Nat) = 2 ^ (8 - 1) := rfl
      have he : (8 : Int) - ((8 : Nat) : Int) - 1 = -((1 : Nat) : Int) := rfl
      simp only [h1, h2, h3, ite_true, ite_false]
      rw [he, zpow2Rat_neg_ofNat]
      unfold invPow2Rat pow2Rat
      apply Rat.not_le.mpr
      have h2r : ((2 ^ 1 : Nat) : Rat) = 2 := rfl
      rw [h2r]
      apply rat_div_lt_of_mul_lt (by decide : (0 : Rat) < 2)
      rw [Rat.one_mul]; decide
    · unfold alibiBias
      have he : (8 : Int) - ((8 - 1 : Nat) : Int) = ((1 : Nat) : Int) := rfl
      rw [he, zpow2Rat_ofNat]; unfold pow2Rat; grind
    · unfold rneSwampsAtNegB alibiHalfUlpIn
      have h1 : ¬ ((1 : Rat) ≤ 0) := by decide
      have h2 : (130 : Nat) % 2 = 0 := rfl
      have h3 : ¬ ((130 : Nat) = 2 ^ (8 - 1)) := by decide
      have he : (8 : Int) - ((8 : Nat) : Int) = ((0 : Nat) : Int) := rfl
      simp only [h1, h2, h3, ite_true, ite_false]
      rw [he, zpow2Rat_ofNat]
      unfold pow2Rat
      have h0 : ((2 ^ 0 : Nat) : Rat) = 1 := rfl
      rw [h0]; exact Rat.le_refl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold alibiBias
      have he : (4 : Int) - ((4 - 1 : Nat) : Int) = ((1 : Nat) : Int) := rfl
      rw [he, zpow2Rat_ofNat]; unfold pow2Rat; grind
    · unfold rneSwampsAtNegB alibiHalfUlpOut
      have h1 : (-1 : Rat) ≤ 0 := by decide
      have h2 : (8 : Nat) % 2 = 0 := rfl
      have he : (4 : Int) - ((4 : Nat) : Int) = ((0 : Nat) : Int) := rfl
      simp only [h1, h2, ite_true]
      rw [he, zpow2Rat_ofNat]
      unfold pow2Rat
      have h0 : ((2 ^ 0 : Nat) : Rat) = 1 := rfl
      have hm : -(-1 : Rat) = 1 := by grind
      rw [h0, hm]; exact Rat.le_refl
    · unfold rneSwampsAtNegB alibiHalfUlpIn
      have h1 : ¬ ((1 : Rat) ≤ 0) := by decide
      have h2 : (8 : Nat) % 2 = 0 := rfl
      have h3 : (8 : Nat) = 2 ^ (4 - 1) := rfl
      have he : (4 : Int) - ((4 : Nat) : Int) - 1 = -((1 : Nat) : Int) := rfl
      simp only [h1, h2, h3, ite_true, ite_false]
      rw [he, zpow2Rat_neg_ofNat]
      unfold invPow2Rat pow2Rat
      apply Rat.not_le.mpr
      have h2r : ((2 ^ 1 : Nat) : Rat) = 2 := rfl
      rw [h2r]
      apply rat_div_lt_of_mul_lt (by decide : (0 : Rat) < 2)
      rw [Rat.one_mul]; decide
    · unfold alibiBias
      have he : (4 : Int) - ((4 - 1 : Nat) : Int) = ((1 : Nat) : Int) := rfl
      rw [he, zpow2Rat_ofNat]; unfold pow2Rat; grind
    · unfold rneSwampsAtNegB alibiHalfUlpIn
      have h1 : ¬ ((1 : Rat) ≤ 0) := by decide
      have h2 : (10 : Nat) % 2 = 0 := rfl
      have h3 : ¬ ((10 : Nat) = 2 ^ (4 - 1)) := by decide
      have he : (4 : Int) - ((4 : Nat) : Int) = ((0 : Nat) : Int) := rfl
      simp only [h1, h2, h3, ite_true, ite_false]
      rw [he, zpow2Rat_ofNat]
      unfold pow2Rat
      have h0 : ((2 ^ 0 : Nat) : Rat) = 1 := rfl
      rw [h0]; exact Rat.le_refl
    · unfold fp8E4M3Overflows; decide
    · unfold fp8E4M3Overflows; decide
  · refine ⟨?_, ?_, ?_⟩
    · unfold fp16Overflows; decide
    · decide
    · unfold fp16Overflows; decide
  · intro p v k hv
    exact dyadic_slope_zero_mul_error p v k hv
  · intro p d k hp hd
    have h1 := nat_lt_pow2_exact_pbit hp d hd
    exact ⟨h1, dyadic_slope_zero_mul_error p (d : Rat) k h1⟩
  · intro p d k hp heven hd
    have h1 := even_nat_le_pow2_succ_exact_pbit hp d heven hd
    exact ⟨h1, dyadic_slope_zero_mul_error p (d : Rat) k h1⟩

end AlibiBitsplitKulisch
