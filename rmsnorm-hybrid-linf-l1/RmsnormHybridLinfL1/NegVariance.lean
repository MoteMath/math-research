/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RmsnormHybridLinfL1.Swamping

/-!
# Exact 1-Pass LayerNorm Negative-Variance Witnesses & Universal 2-Pass Non-Negativity (Theorems 5 & 6)

Proves:
1. Theorem 5: Bit-exact IEEE-754 RNE 1-pass LayerNorm negative-variance (`NaN`) and zero-collapse
   witnesses for BF16 (`0x4173` = `243/16`, `Var = -1`), FP16 (`0x5417` = `1047/16`, `Var = -4`),
   FP8-E4M3 (`0x55` = `13`, `Var = -16`), and FP8-E5M2 (`0x48` = `8`, `Var = -8`).
2. Theorem 6: Unconditional non-negativity of 2-pass shifted-mean variance in exact rational
   arithmetic (with exact parallel-axis and 1-pass/2-pass identities) and in EVERY monotonic
   non-negative rounding arithmetic.
-/

namespace RmsnormHybridLinfL1

/-! ## Theorem 5: Bit-Exact 1-Pass LayerNorm Negative-Variance Witnesses -/

/-- Headline Theorem 5: Bit-exact IEEE-754 RNE verification of minimal unit-std 1-pass LayerNorm
    negative-variance (`Var < 0 => NaN`) and zero-collapse witnesses across BF16, FP16, FP8-E4M3,
    and FP8-E5M2. -/
theorem bf16_fp16_onepass_layernorm_negative_variance_exact :
    (fmtBF16.decode 0x4173 = FloatVal.finite (243 / 16) ∧
     (let r := fmtBF16.onePassVarPairBits 0x4173
      fmtBF16.decode r.1 = FloatVal.finite 232 ∧
      fmtBF16.decode r.2.1 = FloatVal.finite 233 ∧
      fmtBF16.decode r.2.2 = FloatVal.finite (-1)) ∧
     fmtBF16.decode 0x413d = FloatVal.finite (189 / 16) ∧
     (let r := fmtBF16.onePassVarPairBits 0x413d
      fmtBF16.decode r.1 = FloatVal.finite 140 ∧
      fmtBF16.decode r.2.1 = FloatVal.finite 140 ∧
      fmtBF16.decode r.2.2 = FloatVal.finite 0)) ∧
    (fmtFP16.decode 0x5417 = FloatVal.finite (1047 / 16) ∧
     (let r := fmtFP16.onePassVarPairBits 0x5417
      fmtFP16.decode r.1 = FloatVal.finite 4280 ∧
      fmtFP16.decode r.2.1 = FloatVal.finite 4284 ∧
      fmtFP16.decode r.2.2 = FloatVal.finite (-4)) ∧
     fmtFP16.decode 0x4fc7 = FloatVal.finite (1991 / 64) ∧
     (let r := fmtFP16.onePassVarPairBits 0x4fc7
      fmtFP16.decode r.1 = FloatVal.finite 969 ∧
      fmtFP16.decode r.2.1 = FloatVal.finite 969 ∧
      fmtFP16.decode r.2.2 = FloatVal.finite 0)) ∧
    (fmtFP8E4M3.decode 0x55 = FloatVal.finite 13 ∧
     (let r := fmtFP8E4M3.onePassVarPairBits 0x55
      fmtFP8E4M3.decode r.1 = FloatVal.finite 160 ∧
      fmtFP8E4M3.decode r.2.1 = FloatVal.finite 176 ∧
      fmtFP8E4M3.decode r.2.2 = FloatVal.finite (-16))) ∧
    (fmtFP8E5M2.decode 0x48 = FloatVal.finite 8 ∧
     (let r := fmtFP8E5M2.onePassVarPairBits 0x48
      fmtFP8E5M2.decode r.1 = FloatVal.finite 56 ∧
      fmtFP8E5M2.decode r.2.1 = FloatVal.finite 64 ∧
      fmtFP8E5M2.decode r.2.2 = FloatVal.finite (-8))) := by
  refine ⟨⟨?_, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩⟩,
          ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩⟩,
          ⟨?_, ⟨?_, ?_, ?_⟩⟩,
          ⟨?_, ⟨?_, ?_, ?_⟩⟩⟩
  -- BF16 0x4173 (243/16 -> m2=232, mu2=233, var=-1)
  · exact decode_eq_finite_of_dyadic fmtBF16 0x4173 243 (-4) (243 / 16) (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtBF16 _ 232 0 232 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtBF16 _ 233 0 233 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtBF16 _ (-128) (-7) (-1) (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  -- BF16 0x413d (189/16 -> m2=140, mu2=140, var=0)
  · exact decode_eq_finite_of_dyadic fmtBF16 0x413d 189 (-4) (189 / 16) (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtBF16 _ 140 0 140 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtBF16 _ 140 0 140 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtBF16 _ 0 (-133) 0 (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  -- FP16 0x5417 (1047/16 -> m2=4280, mu2=4284, var=-4)
  · exact decode_eq_finite_of_dyadic fmtFP16 0x5417 1047 (-4) (1047 / 16) (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP16 _ 1070 2 4280 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP16 _ 1071 2 4284 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP16 _ (-1024) (-8) (-4) (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  -- FP16 0x4fc7 (1991/64 -> m2=969, mu2=969, var=0)
  · exact decode_eq_finite_of_dyadic fmtFP16 0x4fc7 1991 (-6) (1991 / 64) (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP16 _ 1938 (-1) 969 (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP16 _ 1938 (-1) 969 (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP16 _ 0 (-24) 0 (by decide)
      (by unfold pow2Int invPow2Rat pow2Rat; grind)
  -- FP8-E4M3 0x55 (13 -> m2=160, mu2=176, var=-16)
  · exact decode_eq_finite_of_dyadic fmtFP8E4M3 0x55 13 0 13 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP8E4M3 _ 10 4 160 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP8E4M3 _ 11 4 176 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP8E4M3 _ (-8) 1 (-16) (by decide)
      (by unfold pow2Int pow2Rat; grind)
  -- FP8-E5M2 0x48 (8 -> m2=56, mu2=64, var=-8)
  · exact decode_eq_finite_of_dyadic fmtFP8E5M2 0x48 4 1 8 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP8E5M2 _ 7 3 56 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP8E5M2 _ 4 4 64 (by decide)
      (by unfold pow2Int pow2Rat; grind)
  · exact decode_eq_finite_of_dyadic fmtFP8E5M2 _ (-4) 1 (-8) (by decide)
      (by unfold pow2Int pow2Rat; grind)

/-! ## Theorem 6: Universal 2-Pass Shifted-Mean Variance Non-Negativity -/

/-- Exact rational 2-pass shifted-mean variance is unconditionally `≥ 0` for any shift `μ`. -/
theorem twoPassVar_nonneg {d : Nat} (hd : 1 ≤ d) (x : Fin d → Rat) (μ : Rat) :
    (0 : Rat) ≤ twoPassVar x μ := by
  unfold twoPassVar
  have hdpos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hsum : (0 : Rat) ≤ finSum d (fun i => (x i - μ) * (x i - μ)) :=
    finSum_nonneg (fun i => rat_sq_nonneg (x i - μ))
  exact rat_div_nonneg hsum hdpos

/-- Exact parallel-axis identity:
    `twoPassVar x μ = twoPassVar x (vecMean x) + (vecMean x - μ)^2`. -/
theorem twoPassVar_parallel_axis {d : Nat} (hd : 1 ≤ d) (x : Fin d → Rat) (μ : Rat) :
    twoPassVar x μ = twoPassVar x (vecMean x) + (vecMean x - μ) * (vecMean x - μ) := by
  have hdpos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hdne : (d : Rat) ≠ 0 := Rat.ne_of_gt hdpos
  let m := vecMean x
  have hm : (d : Rat) * m = finSum d x := by
    simp only [m, vecMean]
    exact rat_mul_div_cancel hdne
  have hzero : finSum d (fun i => x i - m) = 0 := by
    rw [finSum_sub, finSum_const, hm]
    grind
  have hexpand :
      finSum d (fun i => (x i - μ) * (x i - μ)) =
      finSum d (fun i => (x i - m) * (x i - m)) + (d : Rat) * ((m - μ) * (m - μ)) := by
    have hcongr :
        finSum d (fun i => (x i - μ) * (x i - μ)) =
        finSum d (fun i => ((x i - m) * (x i - m) + (2 * (m - μ)) * (x i - m)) + (m - μ) * (m - μ)) := by
      apply finSum_congr; intro i; grind
    rw [hcongr, finSum_add, finSum_add, finSum_mul_left, hzero, finSum_const]
    grind
  unfold twoPassVar
  rw [hexpand]
  have hmul :
      ((finSum d (fun i => (x i - m) * (x i - m)) + (d : Rat) * ((m - μ) * (m - μ))) / (d : Rat) -
        (finSum d (fun i => (x i - m) * (x i - m)) / (d : Rat) + (m - μ) * (m - μ))) * (d : Rat) = 0 := by
    have h1 := rat_div_mul_cancel (a := finSum d (fun i => (x i - m) * (x i - m)) +
      (d : Rat) * ((m - μ) * (m - μ))) hdne
    have h2 := rat_div_mul_cancel (a := finSum d (fun i => (x i - m) * (x i - m))) hdne
    grind
  cases Rat.mul_eq_zero.mp hmul with
  | inl h0 => grind
  | inr h0 => exact False.elim (hdne h0)

/-- Exact rational equivalence of 2-pass and 1-pass variance:
    `twoPassVar x (vecMean x) = meanSq x - (vecMean x)^2`. -/
theorem twoPassVar_eq_meanSq_sub_mean_sq {d : Nat} (hd : 1 ≤ d) (x : Fin d → Rat) :
    twoPassVar x (vecMean x) = meanSq x - vecMean x * vecMean x := by
  have hpa := twoPassVar_parallel_axis hd x 0
  have h0 : twoPassVar x 0 = meanSq x := by
    unfold twoPassVar meanSq sumSq
    have hcongr : finSum d (fun i => (x i - 0) * (x i - 0)) = finSum d (fun i => x i * x i) := by
      apply finSum_congr; intro i; grind
    rw [hcongr]
  rw [h0] at hpa
  grind

/-- Sequential rounded sum preserves non-negativity for any non-negativity-preserving rounding `fl`. -/
theorem flSeqSum_nonneg (fl : Rat → Rat) (hfl : ∀ q : Rat, (0 : Rat) ≤ q → (0 : Rat) ≤ fl q) :
    ∀ (d : Nat) (f : Fin d → Rat), (∀ i, (0 : Rat) ≤ f i) → (0 : Rat) ≤ flSeqSum fl d f := by
  intro d
  induction d with
  | zero =>
    intro f _
    exact hfl 0 Rat.le_refl
  | succ n ih =>
    intro f hf
    simp only [flSeqSum]
    apply hfl
    exact rat_add_nonneg (ih (fun i => f i.castSucc) (fun i => hf i.castSucc))
      (hf ⟨n, Nat.lt_succ_self n⟩)

/-- Universal rounded 2-pass shifted-mean variance non-negativity under ANY non-negativity-preserving
    rounding `fl` (in particular any monotonic `fl` with `fl 0 = 0`). -/
theorem twoPassVarRounded_nonneg (fl : Rat → Rat)
    (hfl : ∀ q : Rat, (0 : Rat) ≤ q → (0 : Rat) ≤ fl q)
    {d : Nat} (hd : 1 ≤ d) (x : Fin d → Rat) (μHat : Rat) :
    (0 : Rat) ≤ twoPassVarRounded fl x μHat := by
  unfold twoPassVarRounded
  apply hfl
  have hdpos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  apply rat_div_nonneg _ hdpos
  apply flSeqSum_nonneg fl hfl
  intro i
  exact hfl _ (rat_sq_nonneg _)

/-- Every monotonic rounding operator with `fl 0 = 0` preserves non-negativity. -/
theorem nonneg_of_mono_zero (fl : Rat → Rat)
    (h0 : fl 0 = 0) (hmono : ∀ a b : Rat, a ≤ b → fl a ≤ fl b) :
    ∀ q : Rat, (0 : Rat) ≤ q → (0 : Rat) ≤ fl q := by
  intro q hq
  rw [← h0]
  exact hmono 0 q hq

/-- Headline Theorem 6: Unconditional Non-Negativity of 2-Pass Shifted-Mean LayerNorm Variance
    in Exact Rational Arithmetic and Every Monotonic Non-Negative Rounding Arithmetic. -/
theorem twopass_shifted_mean_variance_nonneg_universal :
    (∀ (d : Nat) (x : Fin d → Rat) (μ : Rat), 1 ≤ d →
      (0 : Rat) ≤ twoPassVar x μ ∧
      twoPassVar x μ = twoPassVar x (vecMean x) + (vecMean x - μ) * (vecMean x - μ) ∧
      twoPassVar x (vecMean x) ≤ twoPassVar x μ) ∧
    (∀ (d : Nat) (x : Fin d → Rat), 1 ≤ d →
      twoPassVar x (vecMean x) = meanSq x - vecMean x * vecMean x) ∧
    (∀ (fl : Rat → Rat), fl 0 = 0 → (∀ a b : Rat, a ≤ b → fl a ≤ fl b) →
      ∀ (d : Nat) (x : Fin d → Rat) (μHat : Rat), 1 ≤ d →
        (0 : Rat) ≤ twoPassVarRounded fl x μHat) ∧
    (∀ (fl : Rat → Rat), (∀ q : Rat, (0 : Rat) ≤ q → (0 : Rat) ≤ fl q) →
      ∀ (d : Nat) (x : Fin d → Rat) (μHat : Rat), 1 ≤ d →
        (0 : Rat) ≤ twoPassVarRounded fl x μHat) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d x μ hd
    have hnn := twoPassVar_nonneg hd x μ
    have hpa := twoPassVar_parallel_axis hd x μ
    have hmin : twoPassVar x (vecMean x) ≤ twoPassVar x μ := by
      rw [hpa]
      apply rat_le_of_sub_nonneg
      have heq : twoPassVar x (vecMean x) + (vecMean x - μ) * (vecMean x - μ) -
          twoPassVar x (vecMean x) = (vecMean x - μ) * (vecMean x - μ) := by grind
      rw [heq]
      exact rat_sq_nonneg _
    exact ⟨hnn, hpa, hmin⟩
  · intro d x hd
    exact twoPassVar_eq_meanSq_sub_mean_sq hd x
  · intro fl h0 hmono d x μHat hd
    exact twoPassVarRounded_nonneg fl (nonneg_of_mono_zero fl h0 hmono) hd x μHat
  · intro fl hfl d x μHat hd
    exact twoPassVarRounded_nonneg fl hfl hd x μHat

end RmsnormHybridLinfL1
