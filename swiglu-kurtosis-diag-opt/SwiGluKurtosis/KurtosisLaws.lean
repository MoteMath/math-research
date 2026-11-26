/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SwiGluKurtosis.RatOrder

/-!
# Theorems 1 & 2: Exact Gated-Bilinear `2x` Kurtosis Law & Correlated Amplification

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. `reglu_exact_two_x_kurtosis_multiplication_law`
2. `correlated_bilinear_kurtosis_amplification_exact`
-/

namespace SwiGluKurtosis

/-! ### Expectation Algebra for Symmetric Distributions -/

theorem relu_of_pos {x : Rat} (hx : (0 : Rat) < x) : relu x = x := by
  unfold relu
  have h : (0 : Rat) ≤ x := Rat.le_of_lt hx
  simp [h]

theorem relu_of_neg_pos {x : Rat} (hx : (0 : Rat) < x) : relu (-x) = 0 := by
  unfold relu
  have hneg : -x < 0 := rat_neg_of_pos hx
  have hnot : ¬ ((0 : Rat) ≤ -x) := Rat.not_le.mpr hneg
  simp [hnot]

theorem symExpect_add {n : Nat} (D : SymHalfDist n) (f g : Rat → Rat) :
    symExpect D (fun x => f x + g x) = symExpect D f + symExpect D g := by
  unfold symExpect
  have h : ∀ i : Fin n,
      D.prob i * (f (D.val i) + g (D.val i)) + D.prob i * (f (-D.val i) + g (-D.val i)) =
      (D.prob i * f (D.val i) + D.prob i * f (-D.val i)) +
      (D.prob i * g (D.val i) + D.prob i * g (-D.val i)) := by
    intro i; grind
  rw [finSum_congr h, finSum_add]

theorem symExpect_mul_left {n : Nat} (D : SymHalfDist n) (c : Rat) (f : Rat → Rat) :
    symExpect D (fun x => c * f x) = c * symExpect D f := by
  unfold symExpect
  have h : ∀ i : Fin n,
      D.prob i * (c * f (D.val i)) + D.prob i * (c * f (-D.val i)) =
      c * (D.prob i * f (D.val i) + D.prob i * f (-D.val i)) := by
    intro i; grind
  rw [finSum_congr h, finSum_mul_left]

theorem symExpect_mul_right {n : Nat} (D : SymHalfDist n) (f : Rat → Rat) (c : Rat) :
    symExpect D (fun x => f x * c) = symExpect D f * c := by
  unfold symExpect
  have h : ∀ i : Fin n,
      D.prob i * (f (D.val i) * c) + D.prob i * (f (-D.val i) * c) =
      (D.prob i * f (D.val i) + D.prob i * f (-D.val i)) * c := by
    intro i; grind
  rw [finSum_congr h, finSum_mul_right]

theorem symExpect_odd_zero {n : Nat} (D : SymHalfDist n) (f : Rat → Rat)
    (hodd : ∀ x, f (-x) = -f x) : symExpect D f = 0 := by
  unfold symExpect
  have h : ∀ i : Fin n,
      D.prob i * f (D.val i) + D.prob i * f (-D.val i) = 0 := by
    intro i
    rw [hodd (D.val i)]
    grind
  rw [finSum_congr h, finSum_zero]

theorem symExpect_even_eq_two_mul_half {n : Nat} (D : SymHalfDist n) (f : Rat → Rat)
    (heven : ∀ x, f (-x) = f x) :
    symExpect D f = 2 * finSum (fun i => D.prob i * f (D.val i)) := by
  unfold symExpect
  have h : ∀ i : Fin n,
      D.prob i * f (D.val i) + D.prob i * f (-D.val i) =
      2 * (D.prob i * f (D.val i)) := by
    intro i
    rw [heven (D.val i)]
    grind
  rw [finSum_congr h, finSum_mul_left]

theorem symExpect_relu_even {n : Nat} (D : SymHalfDist n) (f : Rat → Rat)
    (hf0 : f 0 = 0) (heven : ∀ x, f (-x) = f x) :
    symExpect D (fun x => f (relu x)) = (1 / 2) * symExpect D f := by
  rw [symExpect_even_eq_two_mul_half D f heven]
  unfold symExpect
  have h : ∀ i : Fin n,
      D.prob i * f (relu (D.val i)) + D.prob i * f (relu (-D.val i)) =
      D.prob i * f (D.val i) := by
    intro i
    rw [relu_of_pos (D.val_pos i), relu_of_neg_pos (D.val_pos i), hf0]
    grind
  rw [finSum_congr h]
  grind

theorem prodSymExpect_mul {n m : Nat} (G : SymHalfDist n) (U : SymHalfDist m)
    (f g : Rat → Rat) :
    prodSymExpect G U (fun x y => f x * g y) = symExpect G f * symExpect U g := by
  unfold prodSymExpect
  have h1 : (fun x => symExpect U (fun y => f x * g y)) =
      (fun x => f x * symExpect U g) := by
    funext x
    exact symExpect_mul_left U (f x) g
  rw [h1, symExpect_mul_right]

theorem symMoment2_pos {n : Nat} (D : SymHalfDist n) : (0 : Rat) < symMoment2 D := by
  unfold symMoment2
  rw [symExpect_even_eq_two_mul_half D sq (fun x => by unfold sq; grind)]
  apply rat_mul_pos (by decide)
  apply finSum_mul_pos_of_sum_pos D.prob_nonneg
  · rw [D.sum_prob]; exact rat_div_pos (by decide) (by decide)
  · intro i
    unfold sq
    exact rat_mul_pos (D.val_pos i) (D.val_pos i)

theorem symMoment4_pos {n : Nat} (D : SymHalfDist n) : (0 : Rat) < symMoment4 D := by
  unfold symMoment4
  rw [symExpect_even_eq_two_mul_half D pow4 (fun x => by unfold pow4 sq; grind)]
  apply rat_mul_pos (by decide)
  apply finSum_mul_pos_of_sum_pos D.prob_nonneg
  · rw [D.sum_prob]; exact rat_div_pos (by decide) (by decide)
  · intro i
    unfold pow4 sq
    have h2 := rat_mul_pos (D.val_pos i) (D.val_pos i)
    exact rat_mul_pos h2 h2

theorem symMoment2_ne_zero {n : Nat} (D : SymHalfDist n) : symMoment2 D ≠ 0 :=
  Rat.ne_of_gt (symMoment2_pos D)

theorem symMoment4_ne_zero {n : Nat} (D : SymHalfDist n) : symMoment4 D ≠ 0 :=
  Rat.ne_of_gt (symMoment4_pos D)

/-! ### Theorem 1: Exact `2x` ReGLU Kurtosis Multiplication Law -/

theorem reglu_indep_mean_zero {n m : Nat} (G : SymHalfDist n) (U : SymHalfDist m) :
    prodSymExpect G U (fun g u => relu g * u) = 0 := by
  rw [prodSymExpect_mul G U relu (fun u => u)]
  rw [symExpect_odd_zero U (fun u => u) (fun x => rfl)]
  grind

theorem bilinear_kurt_eq_mul {n m : Nat} (G : SymHalfDist n) (U : SymHalfDist m) :
    bilinearRawKurt G U = symKurtosis G * symKurtosis U := by
  unfold bilinearRawKurt symKurtosis rawKurtosis
  have h2 : prodSymExpect G U (fun g u => sq (g * u)) = symMoment2 G * symMoment2 U := by
    have heq : (fun g u => sq (g * u)) = (fun g u => sq g * sq u) := by
      funext g u; unfold sq; grind
    rw [heq, prodSymExpect_mul]
    rfl
  have h4 : prodSymExpect G U (fun g u => pow4 (g * u)) = symMoment4 G * symMoment4 U := by
    have heq : (fun g u => pow4 (g * u)) = (fun g u => pow4 g * pow4 u) := by
      funext g u; unfold pow4 sq; grind
    rw [heq, prodSymExpect_mul]
    rfl
  rw [h2, h4]
  have hg2 : sq (symMoment2 G) ≠ 0 := Rat.ne_of_gt (rat_sq_pos_of_ne_zero (symMoment2_ne_zero G))
  have hu2 : sq (symMoment2 U) ≠ 0 := Rat.ne_of_gt (rat_sq_pos_of_ne_zero (symMoment2_ne_zero U))
  have hgu2 : sq (symMoment2 G * symMoment2 U) ≠ 0 := by
    have hmul : sq (symMoment2 G * symMoment2 U) = sq (symMoment2 G) * sq (symMoment2 U) := by
      unfold sq; grind
    rw [hmul]
    exact Rat.ne_of_gt (rat_mul_pos (rat_sq_pos_of_ne_zero (symMoment2_ne_zero G))
      (rat_sq_pos_of_ne_zero (symMoment2_ne_zero U)))
  apply (rat_div_eq_iff hgu2).mpr
  have hmul : sq (symMoment2 G * symMoment2 U) = sq (symMoment2 G) * sq (symMoment2 U) := by
    unfold sq; grind
  rw [hmul]
  have hre : (symMoment4 G / sq (symMoment2 G)) * (symMoment4 U / sq (symMoment2 U)) *
      (sq (symMoment2 G) * sq (symMoment2 U)) =
      ((symMoment4 G / sq (symMoment2 G)) * sq (symMoment2 G)) *
      ((symMoment4 U / sq (symMoment2 U)) * sq (symMoment2 U)) := by grind
  rw [hre, rat_div_mul_cancel hg2, rat_div_mul_cancel hu2]

theorem reglu_indep_kurt_eq_two_mul {n m : Nat} (G : SymHalfDist n) (U : SymHalfDist m) :
    regluIndepRawKurt G U = 2 * symKurtosis G * symKurtosis U := by
  unfold regluIndepRawKurt symKurtosis rawKurtosis
  have h2 : prodSymExpect G U (fun g u => sq (relu g * u)) =
      (1 / 2) * symMoment2 G * symMoment2 U := by
    have heq : (fun g u => sq (relu g * u)) = (fun g u => sq (relu g) * sq u) := by
      funext g u; unfold sq; grind
    rw [heq, prodSymExpect_mul]
    rw [symExpect_relu_even G sq (by unfold sq; grind) (fun x => by unfold sq; grind)]
    rfl
  have h4 : prodSymExpect G U (fun g u => pow4 (relu g * u)) =
      (1 / 2) * symMoment4 G * symMoment4 U := by
    have heq : (fun g u => pow4 (relu g * u)) = (fun g u => pow4 (relu g) * pow4 u) := by
      funext g u; unfold pow4 sq; grind
    rw [heq, prodSymExpect_mul]
    rw [symExpect_relu_even G pow4 (by unfold pow4 sq; grind) (fun x => by unfold pow4 sq; grind)]
    rfl
  rw [h2, h4]
  have hg2 : sq (symMoment2 G) ≠ 0 := Rat.ne_of_gt (rat_sq_pos_of_ne_zero (symMoment2_ne_zero G))
  have hu2 : sq (symMoment2 U) ≠ 0 := Rat.ne_of_gt (rat_sq_pos_of_ne_zero (symMoment2_ne_zero U))
  have hdenom_pos : (0 : Rat) < sq ((1 / 2 : Rat) * symMoment2 G * symMoment2 U) := by
    apply rat_sq_pos_of_ne_zero
    have hpos := rat_mul_pos (rat_mul_pos (rat_div_pos (by decide) (by decide) : (0 : Rat) < 1 / 2) (symMoment2_pos G))
      (symMoment2_pos U)
    exact Rat.ne_of_gt hpos
  apply (rat_div_eq_iff (Rat.ne_of_gt hdenom_pos)).mpr
  have hsq : sq ((1 / 2 : Rat) * symMoment2 G * symMoment2 U) =
      (1 / 4 : Rat) * sq (symMoment2 G) * sq (symMoment2 U) := by
    unfold sq; grind
  rw [hsq]
  have hre : 2 * (symMoment4 G / sq (symMoment2 G)) * (symMoment4 U / sq (symMoment2 U)) *
      ((1 / 4 : Rat) * sq (symMoment2 G) * sq (symMoment2 U)) =
      (1 / 2 : Rat) * ((symMoment4 G / sq (symMoment2 G)) * sq (symMoment2 G)) *
      ((symMoment4 U / sq (symMoment2 U)) * sq (symMoment2 U)) := by grind
  rw [hre, rat_div_mul_cancel hg2, rat_div_mul_cancel hu2]

/-- Headline Theorem 1 (`reglu_exact_two_x_kurtosis_multiplication_law`). -/
theorem reglu_exact_two_x_kurtosis_multiplication_law :
    (∀ (n m : Nat) (G : SymHalfDist n) (U : SymHalfDist m),
      prodSymExpect G U (fun g u => relu g * u) = 0 ∧
      bilinearRawKurt G U = symKurtosis G * symKurtosis U ∧
      regluIndepRawKurt G U = 2 * symKurtosis G * symKurtosis U ∧
      regluIndepRawKurt G U = 2 * bilinearRawKurt G U) ∧
    (symKurtosis gaussMoment3Dist = 3 ∧
     regluIndepRawKurt gaussMoment3Dist gaussMoment3Dist = 18) ∧
    (symKurtosis laplaceMoment3Dist = 6 ∧
     regluIndepRawKurt laplaceMoment3Dist laplaceMoment3Dist = 72) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n m G U
    have hmean := reglu_indep_mean_zero G U
    have hbil := bilinear_kurt_eq_mul G U
    have hreg := reglu_indep_kurt_eq_two_mul G U
    refine ⟨hmean, hbil, hreg, ?_⟩
    rw [hreg, hbil]; grind
  · have hk : symKurtosis gaussMoment3Dist = 3 := by
      simp [symKurtosis, rawKurtosis, symMoment2, symMoment4, symExpect,
            finSum, finSumAux, gaussMoment3Dist, sq, pow4]
      grind
    refine ⟨hk, ?_⟩
    rw [reglu_indep_kurt_eq_two_mul, hk]
    grind
  · have hk : symKurtosis laplaceMoment3Dist = 6 := by
      simp [symKurtosis, rawKurtosis, symMoment2, symMoment4, symExpect,
            finSum, finSumAux, laplaceMoment3Dist, sq, pow4]
      grind
    refine ⟨hk, ?_⟩
    rw [reglu_indep_kurt_eq_two_mul, hk]
    grind

/-! ### Theorem 2: Correlated Bilinear Kurtosis Amplification Law -/

theorem reglu_self_kurt_eq {n : Nat} (G : SymHalfDist n) :
    regluSelfRawKurt G = 2 * symMoment8 G / sq (symMoment4 G) := by
  unfold regluSelfRawKurt rawKurtosis
  have h2 : symExpect G (fun g => sq (relu g * g)) = (1 / 2) * symMoment4 G := by
    have heq : symExpect G (fun g => sq (relu g * g)) = symExpect G (fun g => pow4 (relu g)) := by
      unfold symExpect
      apply finSum_congr
      intro i
      dsimp only
      rw [relu_of_pos (G.val_pos i), relu_of_neg_pos (G.val_pos i)]
      unfold pow4 sq; grind
    rw [heq, symExpect_relu_even G pow4 (by unfold pow4 sq; grind) (fun x => by unfold pow4 sq; grind)]
    rfl
  have h4 : symExpect G (fun g => pow4 (relu g * g)) = (1 / 2) * symMoment8 G := by
    have heq : symExpect G (fun g => pow4 (relu g * g)) = symExpect G (fun g => pow8 (relu g)) := by
      unfold symExpect
      apply finSum_congr
      intro i
      dsimp only
      rw [relu_of_pos (G.val_pos i), relu_of_neg_pos (G.val_pos i)]
      unfold pow8 pow4 sq; grind
    rw [heq, symExpect_relu_even G pow8 (by unfold pow8 pow4 sq; grind) (fun x => by unfold pow8 pow4 sq; grind)]
    rfl
  rw [h2, h4]
  have hm4 : sq (symMoment4 G) ≠ 0 := Rat.ne_of_gt (rat_sq_pos_of_ne_zero (symMoment4_ne_zero G))
  have hd : sq ((1 / 2 : Rat) * symMoment4 G) ≠ 0 := by
    have hsq : sq ((1 / 2 : Rat) * symMoment4 G) = (1 / 4 : Rat) * sq (symMoment4 G) := by
      unfold sq; grind
    rw [hsq]
    exact Rat.ne_of_gt (rat_mul_pos (rat_div_pos (by decide) (by decide)) (rat_sq_pos_of_ne_zero (symMoment4_ne_zero G)))
  apply (rat_div_eq_iff hd).mpr
  have hsq : sq ((1 / 2 : Rat) * symMoment4 G) = (1 / 4 : Rat) * sq (symMoment4 G) := by
    unfold sq; grind
  rw [hsq]
  have hre : (2 * symMoment8 G / sq (symMoment4 G)) * ((1 / 4 : Rat) * sq (symMoment4 G)) =
      (1 / 4 : Rat) * ((2 * symMoment8 G / sq (symMoment4 G)) * sq (symMoment4 G)) := by grind
  rw [hre, rat_div_mul_cancel hm4]
  grind

theorem reglu_self_gt_indep_of_moment_ineq {n : Nat} (G : SymHalfDist n)
    (hineq : pow4 (symMoment4 G) < symMoment8 G * pow4 (symMoment2 G)) :
    regluIndepRawKurt G G < regluSelfRawKurt G := by
  rw [reglu_indep_kurt_eq_two_mul, reglu_self_kurt_eq]
  unfold symKurtosis rawKurtosis
  have hm2_pos : (0 : Rat) < sq (symMoment2 G) := rat_sq_pos_of_ne_zero (symMoment2_ne_zero G)
  have hm2_4_pos : (0 : Rat) < pow4 (symMoment2 G) := rat_mul_pos hm2_pos hm2_pos
  have hm4_2_pos : (0 : Rat) < sq (symMoment4 G) := rat_sq_pos_of_ne_zero (symMoment4_ne_zero G)
  have hlhs : 2 * (symMoment4 G / sq (symMoment2 G)) * (symMoment4 G / sq (symMoment2 G)) =
      (2 * sq (symMoment4 G)) / pow4 (symMoment2 G) := by
    apply Eq.symm
    apply (rat_div_eq_iff (Rat.ne_of_gt hm2_4_pos)).mpr
    have hp4 : pow4 (symMoment2 G) = sq (symMoment2 G) * sq (symMoment2 G) := rfl
    rw [hp4]
    have hre : 2 * (symMoment4 G / sq (symMoment2 G)) * (symMoment4 G / sq (symMoment2 G)) *
        (sq (symMoment2 G) * sq (symMoment2 G)) =
        2 * ((symMoment4 G / sq (symMoment2 G)) * sq (symMoment2 G)) *
        ((symMoment4 G / sq (symMoment2 G)) * sq (symMoment2 G)) := by grind
    rw [hre, rat_div_mul_cancel (Rat.ne_of_gt hm2_pos)]
    unfold sq; grind
  rw [hlhs]
  rw [rat_div_lt_div_iff hm2_4_pos hm4_2_pos]
  have h1 : 2 * sq (symMoment4 G) * sq (symMoment4 G) = 2 * pow4 (symMoment4 G) := by
    unfold pow4 sq; grind
  have h2 : 2 * symMoment8 G * pow4 (symMoment2 G) = 2 * (symMoment8 G * pow4 (symMoment2 G)) := by
    grind
  rw [h1, h2]
  exact rat_mul_lt_mul_of_pos_left hineq (by decide)

theorem reglu_corr_mix_moments {n : Nat} (D : SymHalfDist n) (a b : Rat) :
    prodSymExpect D D (fun g z => sq (relu g * (a * g + b * z))) =
      (1 / 2) * (sq a * symMoment4 D + sq b * sq (symMoment2 D)) ∧
    prodSymExpect D D (fun g z => pow4 (relu g * (a * g + b * z))) =
      (1 / 2) * (pow4 a * symMoment8 D + 6 * sq a * sq b * symMoment6 D * symMoment2 D +
        pow4 b * sq (symMoment4 D)) := by
  have h2 : prodSymExpect D D (fun g z => sq (relu g * (a * g + b * z))) =
      (1 / 2) * (sq a * symMoment4 D + sq b * sq (symMoment2 D)) := by
    have hinner : ∀ g : Rat,
        symExpect D (fun z => sq (relu g * (a * g + b * z))) =
        sq a * sq (relu g * g) + sq b * sq (relu g) * symMoment2 D := by
      intro g
      have hexp : (fun z => sq (relu g * (a * g + b * z))) =
          (fun z => (sq a * sq (relu g * g) + (2 * a * b * sq (relu g) * g) * z) +
            (sq b * sq (relu g)) * sq z) := by
        funext z; unfold sq; grind
      rw [hexp, symExpect_add, symExpect_add]
      have hc : symExpect D (fun _ => sq a * sq (relu g * g)) = sq a * sq (relu g * g) := by
        unfold symExpect
        have hconst : ∀ i : Fin n,
            D.prob i * (sq a * sq (relu g * g)) + D.prob i * (sq a * sq (relu g * g)) =
            D.prob i * (2 * (sq a * sq (relu g * g))) := by
          intro i; grind
        rw [finSum_congr hconst, finSum_mul_right, D.sum_prob]
        grind
      have hodd : symExpect D (fun z => (2 * a * b * sq (relu g) * g) * z) = 0 := by
        rw [symExpect_mul_left]
        rw [symExpect_odd_zero D (fun z => z) (fun x => rfl)]
        grind
      rw [hc, hodd, symExpect_mul_left]
      unfold symMoment2; grind
    unfold prodSymExpect
    have hfun : (fun g => symExpect D (fun z => sq (relu g * (a * g + b * z)))) =
        (fun g => sq a * sq (relu g * g) + sq b * sq (relu g) * symMoment2 D) := funext hinner
    rw [hfun, symExpect_add, symExpect_mul_left]
    have hterm1 : symExpect D (fun g => sq (relu g * g)) = (1 / 2) * symMoment4 D := by
      have heq : symExpect D (fun g => sq (relu g * g)) = symExpect D (fun g => pow4 (relu g)) := by
        unfold symExpect
        apply finSum_congr; intro i; dsimp only
        rw [relu_of_pos (D.val_pos i), relu_of_neg_pos (D.val_pos i)]
        unfold pow4 sq; grind
      rw [heq, symExpect_relu_even D pow4 (by unfold pow4 sq; grind) (fun x => by unfold pow4 sq; grind)]
      rfl
    have hterm2 : symExpect D (fun g => sq b * sq (relu g) * symMoment2 D) =
        (1 / 2) * (sq b * sq (symMoment2 D)) := by
      have heq : (fun g => sq b * sq (relu g) * symMoment2 D) =
          (fun g => (sq b * symMoment2 D) * sq (relu g)) := by funext g; grind
      rw [heq, symExpect_mul_left,
          symExpect_relu_even D sq (by unfold sq; grind) (fun x => by unfold sq; grind)]
      unfold symMoment2 sq; grind
    rw [hterm1, hterm2]
    grind
  have h4 : prodSymExpect D D (fun g z => pow4 (relu g * (a * g + b * z))) =
      (1 / 2) * (pow4 a * symMoment8 D + 6 * sq a * sq b * symMoment6 D * symMoment2 D +
        pow4 b * sq (symMoment4 D)) := by
    have hinner : ∀ g : Rat,
        symExpect D (fun z => pow4 (relu g * (a * g + b * z))) =
        pow4 a * pow4 (relu g * g) +
        6 * sq a * sq b * (pow4 (relu g) * sq g) * symMoment2 D +
        pow4 b * pow4 (relu g) * symMoment4 D := by
      intro g
      have hexp : (fun z => pow4 (relu g * (a * g + b * z))) =
          (fun z =>
            (((pow4 a * pow4 (relu g * g) +
              (4 * a * a * a * b * pow4 (relu g) * (g * g * g)) * z) +
              (6 * sq a * sq b * (pow4 (relu g) * sq g)) * sq z) +
              (4 * a * b * b * b * pow4 (relu g) * g) * (z * z * z)) +
              (pow4 b * pow4 (relu g)) * pow4 z) := by
        funext z; unfold pow4 sq; grind
      rw [hexp, symExpect_add, symExpect_add, symExpect_add, symExpect_add]
      have hc : symExpect D (fun _ => pow4 a * pow4 (relu g * g)) = pow4 a * pow4 (relu g * g) := by
        unfold symExpect
        have hconst : ∀ i : Fin n,
            D.prob i * (pow4 a * pow4 (relu g * g)) + D.prob i * (pow4 a * pow4 (relu g * g)) =
            D.prob i * (2 * (pow4 a * pow4 (relu g * g))) := by intro i; grind
        rw [finSum_congr hconst, finSum_mul_right, D.sum_prob]; grind
      have hodd1 : symExpect D (fun z => (4 * a * a * a * b * pow4 (relu g) * (g * g * g)) * z) = 0 := by
        rw [symExpect_mul_left, symExpect_odd_zero D (fun z => z) (fun x => rfl)]; grind
      have hodd3 : symExpect D (fun z => (4 * a * b * b * b * pow4 (relu g) * g) * (z * z * z)) = 0 := by
        rw [symExpect_mul_left, symExpect_odd_zero D (fun z => z * z * z) (fun x => by grind)]; grind
      rw [hc, hodd1, hodd3, symExpect_mul_left, symExpect_mul_left]
      unfold symMoment2 symMoment4; grind
    unfold prodSymExpect
    have hfun : (fun g => symExpect D (fun z => pow4 (relu g * (a * g + b * z)))) =
        (fun g =>
          pow4 a * pow4 (relu g * g) +
          6 * sq a * sq b * (pow4 (relu g) * sq g) * symMoment2 D +
          pow4 b * pow4 (relu g) * symMoment4 D) := funext hinner
    rw [hfun, symExpect_add, symExpect_add, symExpect_mul_left]
    have ht1 : symExpect D (fun g => pow4 (relu g * g)) = (1 / 2) * symMoment8 D := by
      have heq : symExpect D (fun g => pow4 (relu g * g)) = symExpect D (fun g => pow8 (relu g)) := by
        unfold symExpect
        apply finSum_congr; intro i; dsimp only
        rw [relu_of_pos (D.val_pos i), relu_of_neg_pos (D.val_pos i)]
        unfold pow8 pow4 sq; grind
      rw [heq, symExpect_relu_even D pow8 (by unfold pow8 pow4 sq; grind) (fun x => by unfold pow8 pow4 sq; grind)]
      rfl
    have ht2 : symExpect D (fun g => 6 * sq a * sq b * (pow4 (relu g) * sq g) * symMoment2 D) =
        (1 / 2) * (6 * sq a * sq b * symMoment6 D * symMoment2 D) := by
      have heq1 : (fun g => 6 * sq a * sq b * (pow4 (relu g) * sq g) * symMoment2 D) =
          (fun g => (6 * sq a * sq b * symMoment2 D) * (pow4 (relu g) * sq g)) := by
        funext g; grind
      rw [heq1, symExpect_mul_left]
      have heq2 : symExpect D (fun g => pow4 (relu g) * sq g) = symExpect D (fun g => pow6 (relu g)) := by
        unfold symExpect
        apply finSum_congr; intro i; dsimp only
        rw [relu_of_pos (D.val_pos i), relu_of_neg_pos (D.val_pos i)]
        unfold pow6 pow4 sq; grind
      rw [heq2, symExpect_relu_even D pow6 (by unfold pow6 pow4 sq; grind) (fun x => by unfold pow6 pow4 sq; grind)]
      unfold symMoment6; grind
    have ht3 : symExpect D (fun g => pow4 b * pow4 (relu g) * symMoment4 D) =
        (1 / 2) * (pow4 b * sq (symMoment4 D)) := by
      have heq1 : (fun g => pow4 b * pow4 (relu g) * symMoment4 D) =
          (fun g => (pow4 b * symMoment4 D) * pow4 (relu g)) := by
        funext g; grind
      rw [heq1, symExpect_mul_left,
          symExpect_relu_even D pow4 (by unfold pow4 sq; grind) (fun x => by unfold pow4 sq; grind)]
      unfold symMoment4 sq; grind
    rw [ht1, ht2, ht3]
    grind
  exact ⟨h2, h4⟩

theorem gauss_corr_reglu_kurt_law (t : Rat) (ht0 : (0 : Rat) < t) (ht1 : t ≤ 1) :
    gaussCorrReGLUKurt t = 18 + (24 * t * (3 - t)) / sq (2 * t + 1) ∧
    (18 : Rat) < gaussCorrReGLUKurt t := by
  have hden_pos : (0 : Rat) < sq (2 * t + 1) := by
    apply rat_sq_pos_of_ne_zero
    have h2t : (0 : Rat) < 2 * t + 1 := rat_add_pos (rat_mul_pos (by decide) ht0) (by decide)
    exact Rat.ne_of_gt h2t
  have hid : gaussCorrReGLUKurt t = 18 + (24 * t * (3 - t)) / sq (2 * t + 1) := by
    unfold gaussCorrReGLUKurt
    have hden_eq : sq (3 * t + (1 - t)) = sq (2 * t + 1) := by unfold sq; grind
    rw [hden_eq]
    apply (rat_div_eq_iff (Rat.ne_of_gt hden_pos)).mpr
    have hre : (18 + 24 * t * (3 - t) / sq (2 * t + 1)) * sq (2 * t + 1) =
        18 * sq (2 * t + 1) + (24 * t * (3 - t) / sq (2 * t + 1)) * sq (2 * t + 1) := by grind
    rw [hre, rat_div_mul_cancel (Rat.ne_of_gt hden_pos)]
    unfold sq; grind
  refine ⟨hid, ?_⟩
  rw [hid]
  have h3t : (0 : Rat) < 3 - t := by
    apply rat_sub_pos
    exact rat_lt_of_le_of_lt ht1 (by decide)
  have hnum_pos : (0 : Rat) < 24 * t * (3 - t) :=
    rat_mul_pos (rat_mul_pos (by decide) ht0) h3t
  have hfrac_pos : (0 : Rat) < 24 * t * (3 - t) / sq (2 * t + 1) :=
    rat_div_pos hnum_pos hden_pos
  apply rat_lt_of_sub_pos
  have hsub : 18 + 24 * t * (3 - t) / sq (2 * t + 1) - 18 = 24 * t * (3 - t) / sq (2 * t + 1) := by
    grind
  rw [hsub]
  exact hfrac_pos

/-- Headline Theorem 2 (`correlated_bilinear_kurtosis_amplification_exact`). -/
theorem correlated_bilinear_kurtosis_amplification_exact :
    (∀ (n : Nat) (G : SymHalfDist n),
      regluSelfRawKurt G = 2 * symMoment8 G / sq (symMoment4 G)) ∧
    (∀ (n : Nat) (G : SymHalfDist n),
      pow4 (symMoment4 G) < symMoment8 G * pow4 (symMoment2 G) →
      regluIndepRawKurt G G < regluSelfRawKurt G) ∧
    (∀ (n : Nat) (D : SymHalfDist n) (a b : Rat),
      prodSymExpect D D (fun g z => sq (relu g * (a * g + b * z))) =
        (1 / 2) * (sq a * symMoment4 D + sq b * sq (symMoment2 D)) ∧
      prodSymExpect D D (fun g z => pow4 (relu g * (a * g + b * z))) =
        (1 / 2) * (pow4 a * symMoment8 D + 6 * sq a * sq b * symMoment6 D * symMoment2 D +
          pow4 b * sq (symMoment4 D))) ∧
    (∀ t : Rat, (0 : Rat) < t → t ≤ 1 →
      gaussCorrReGLUKurt t = 18 + (24 * t * (3 - t)) / sq (2 * t + 1) ∧
      (18 : Rat) < gaussCorrReGLUKurt t) ∧
    (gaussCorrReGLUKurt 0 = 18 ∧
     gaussCorrReGLUKurt (1 / 4) = 76 / 3 ∧
     gaussCorrReGLUKurt 1 = 70 / 3 ∧
     (18 : Rat) < 70 / 3 ∧
     (70 / 3 : Rat) < 76 / 3) ∧
    (regluIndepRawKurt heavyTail3Dist heavyTail3Dist < regluSelfRawKurt heavyTail3Dist) := by
  refine ⟨fun _ G => reglu_self_kurt_eq G,
          fun _ G h => reglu_self_gt_indep_of_moment_ineq G h,
          fun _ D a b => reglu_corr_mix_moments D a b,
          fun t h0 h1 => gauss_corr_reglu_kurt_law t h0 h1,
          ?_, ?_⟩
  · refine ⟨by simp [gaussCorrReGLUKurt, sq]; grind,
            by simp [gaussCorrReGLUKurt, sq]; grind,
            by simp [gaussCorrReGLUKurt, sq]; grind,
            ?_, ?_⟩
    · apply rat_lt_of_sub_pos
      have h : (70 / 3 : Rat) - 18 = 16 / 3 := by grind
      rw [h]; exact rat_div_pos (by decide) (by decide)
    · apply rat_lt_of_sub_pos
      have h : (76 / 3 : Rat) - 70 / 3 = 2 := by grind
      rw [h]; decide
  · apply reglu_self_gt_indep_of_moment_ineq heavyTail3Dist
    have hm2 : symMoment2 heavyTail3Dist = 23 / 8 := by
      simp [symMoment2, symExpect, finSum, finSumAux, heavyTail3Dist, sq]; grind
    have hm4 : symMoment4 heavyTail3Dist = 173 / 8 := by
      simp [symMoment4, symExpect, finSum, finSumAux, heavyTail3Dist, pow4, sq]; grind
    have hm8 : symMoment8 heavyTail3Dist = 33413 / 8 := by
      simp [symMoment8, symExpect, finSum, finSumAux, heavyTail3Dist, pow8, pow4, sq]; grind
    rw [hm2, hm4, hm8]
    apply rat_lt_of_sub_pos
    have hdiff : (33413 / 8 : Rat) * pow4 (23 / 8) - pow4 (173 / 8) = 2184367005 / 32768 := by
      unfold pow4 sq; grind
    rw [hdiff]
    exact rat_div_pos (by decide) (by decide)

end SwiGluKurtosis
