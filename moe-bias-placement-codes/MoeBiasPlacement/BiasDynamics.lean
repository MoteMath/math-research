/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MoeBiasPlacement.RatHelpers

/-!
# Frontier 1 Proofs: DeepSeek-V3 Aux-Loss-Free Bias Drift & Dead-Zone Phase Transition

Proves:
- Theorem 1: `aux_loss_free_mean_bias_drift_exact`
- Theorem 2: `dead_zone_fixed_point_threshold_exact`
-/

namespace MoeBiasPlacement

/-! ## Theorem 1: DeepSeek-V3 Aux-Loss-Free Mean-Bias Drift & Mean-Centered Invariance -/

private theorem signBiasDelta_le_gamma {E : Nat} (γ : Rat) (hγ : 0 < γ)
    (L : Fin E → Rat) (i : Fin E) : signBiasDelta γ L i ≤ γ := by
  unfold signBiasDelta
  dsimp only
  split
  · exact rat_le_refl γ
  · split
    · exact Rat.le_trans (rat_neg_nonpos_of_nonneg (Rat.le_of_lt hγ)) (Rat.le_of_lt hγ)
    · exact Rat.le_of_lt hγ

private theorem neg_gamma_le_signBiasDelta {E : Nat} (γ : Rat) (hγ : 0 < γ)
    (L : Fin E → Rat) (i : Fin E) : -γ ≤ signBiasDelta γ L i := by
  unfold signBiasDelta
  dsimp only
  split
  · exact Rat.le_trans (rat_neg_nonpos_of_nonneg (Rat.le_of_lt hγ)) (Rat.le_of_lt hγ)
  · split
    · exact rat_le_refl (-γ)
    · exact rat_neg_nonpos_of_nonneg (Rat.le_of_lt hγ)

private theorem sumFinRat_signBiasDelta_bound
    (E : Nat) (hE : 2 ≤ E) (γ : Rat) (hγ : 0 < γ) (L : Fin E → Rat) :
    (sumFinRat (signBiasDelta γ L) / (E : Rat)).abs ≤ (((E : Rat) - 2) / (E : Rat)) * γ := by
  have hEpos : (0 : Rat) < (E : Rat) := rat_natCast_pos (by omega)
  have hEne : (E : Rat) ≠ 0 := rat_natCast_ne_zero (by omega)
  have hE2nonneg : (0 : Rat) ≤ (E : Rat) - 2 := by
    rw [rat_sub_nonneg_iff]
    exact rat_natCast_le hE
  have hbound_eq : (((E : Rat) - 2) / (E : Rat)) * γ = (((E : Rat) - 2) * γ) / (E : Rat) := by
    rw [Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.mul_comm ((E : Rat)⁻¹) γ, ← Rat.mul_assoc]
  rw [hbound_eq, rat_abs_le_iff]
  have hneg_div : -((((E : Rat) - 2) * γ) / (E : Rat)) = (-(((E : Rat) - 2) * γ)) / (E : Rat) := by
    rw [Rat.div_def, Rat.div_def, Rat.neg_mul]
  rw [hneg_div, rat_div_le_iff hEpos, rat_le_div_iff hEpos]
  have hdiv_cancel : sumFinRat (signBiasDelta γ L) / (E : Rat) * (E : Rat) = sumFinRat (signBiasDelta γ L) := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hEne, Rat.mul_one]
  rw [hdiv_cancel]
  -- Now prove: -((E - 2) * γ) ≤ sumFinRat (signBiasDelta γ L) ≤ (E - 2) * γ
  by_cases hlt : ∃ i : Fin E, L i < meanLoad L
  · -- Case 1: some expert is strictly underloaded -> some expert must be strictly overloaded!
    have hgt : ∃ j : Fin E, meanLoad L < L j := by
      by_cases h : ∃ j : Fin E, meanLoad L < L j
      · exact h
      · exfalso
        have hle : ∀ j : Fin E, L j ≤ meanLoad L := fun j =>
          rat_le_of_not_lt (fun hlt' => h ⟨j, hlt'⟩)
        have hsum_lt : sumFinRat L < sumFinRat (fun _ : Fin E => meanLoad L) :=
          sumFinRat_lt_of_le_of_exists_lt hle hlt
        rw [sumFinRat_const] at hsum_lt
        have hmean : (E : Rat) * meanLoad L = sumFinRat L := by
          unfold meanLoad
          rw [Rat.div_def, Rat.mul_comm (sumFinRat L), ← Rat.mul_assoc,
              Rat.mul_inv_cancel _ hEne, Rat.one_mul]
        rw [hmean] at hsum_lt
        exact Rat.lt_irrefl hsum_lt
    rcases hlt with ⟨i, hi⟩
    rcases hgt with ⟨j, hj⟩
    have hdi : signBiasDelta γ L i = γ := by
      unfold signBiasDelta; simp [hi]
    have hdj : signBiasDelta γ L j = -γ := by
      unfold signBiasDelta
      have hnot : ¬ (L j < meanLoad L) := rat_not_lt_of_le (Rat.le_of_lt hj)
      simp [hnot, hj]
    constructor
    · -- Lower bound: -((E - 2) * γ) ≤ sum
      have hge := sumFinRat_ge_with_one_large (f := signBiasDelta γ L) (l := -γ) (v := γ)
        (neg_gamma_le_signBiasDelta γ hγ L) ⟨i, by rw [hdi]; exact rat_le_refl γ⟩
      -- hge : E * (-γ) + γ ≤ sum + (-γ)
      have h1 := (Rat.add_le_add_right (c := γ)).mpr hge
      have hlhs : ((E : Rat) * (-γ) + γ) + γ = -(((E : Rat) - 2) * γ) := by
        rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, Rat.neg_add, Rat.neg_neg,
            Rat.mul_neg, Rat.add_assoc]
        have h2γ : (2 : Rat) * γ = γ + γ := by
          have : (2 : Rat) = 1 + 1 := by exact Rat.natCast_add 1 1
          rw [this, Rat.add_mul, Rat.one_mul]
        rw [h2γ]
      have hrhs : (sumFinRat (signBiasDelta γ L) + -γ) + γ = sumFinRat (signBiasDelta γ L) := by
        rw [Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero]
      rw [hlhs, hrhs] at h1
      exact h1
    · -- Upper bound: sum ≤ (E - 2) * γ
      have hle := sumFinRat_le_with_one_small (f := signBiasDelta γ L) (u := γ) (v := -γ)
        (signBiasDelta_le_gamma γ hγ L) ⟨j, by rw [hdj]; exact rat_le_refl (-γ)⟩
      -- hle : sum + γ ≤ E * γ + (-γ)
      have h1 := (Rat.add_le_add_right (c := -γ)).mpr hle
      have hlhs : (sumFinRat (signBiasDelta γ L) + γ) + -γ = sumFinRat (signBiasDelta γ L) := by
        rw [Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
      have hrhs : ((E : Rat) * γ + -γ) + -γ = ((E : Rat) - 2) * γ := by
        rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, Rat.add_assoc]
        have h2γ : -((2 : Rat) * γ) = -γ + -γ := by
          have : (2 : Rat) = 1 + 1 := by exact Rat.natCast_add 1 1
          rw [this, Rat.add_mul, Rat.one_mul, Rat.neg_add]
        rw [h2γ]
      rw [hlhs, hrhs] at h1
      exact h1
  · -- Case 2: no expert is strictly underloaded -> all experts equal meanLoad -> sum = 0!
    have hge_mean : ∀ i : Fin E, meanLoad L ≤ L i := fun i =>
      rat_le_of_not_lt (fun hlt' => hlt ⟨i, hlt'⟩)
    have hnot_gt : ∀ i : Fin E, ¬ (meanLoad L < L i) := by
      intro i hi
      have hsum_gt : sumFinRat (fun _ : Fin E => meanLoad L) < sumFinRat L :=
        sumFinRat_lt_of_le_of_exists_lt hge_mean ⟨i, hi⟩
      rw [sumFinRat_const] at hsum_gt
      have hmean : (E : Rat) * meanLoad L = sumFinRat L := by
        unfold meanLoad
        rw [Rat.div_def, Rat.mul_comm (sumFinRat L), ← Rat.mul_assoc,
            Rat.mul_inv_cancel _ hEne, Rat.one_mul]
      rw [hmean] at hsum_gt
      exact Rat.lt_irrefl hsum_gt
    have hzero : signBiasDelta γ L = fun _ => 0 := by
      funext i
      unfold signBiasDelta
      have h1 : ¬ (L i < meanLoad L) := fun h => hlt ⟨i, h⟩
      have h2 : ¬ (meanLoad L < L i) := hnot_gt i
      simp [h1, h2]
    rw [hzero, sumFinRat_const, Rat.mul_zero]
    have hnonneg : 0 ≤ ((E : Rat) - 2) * γ := rat_mul_nonneg hE2nonneg (Rat.le_of_lt hγ)
    exact ⟨rat_neg_nonpos_of_nonneg hnonneg, hnonneg⟩

private theorem sumFinRat_ite_zero {n : Nat} (a b : Rat) (hn : 0 < n) :
    sumFinRat (fun i : Fin n => if i.val = 0 then a else b) = a + ((n - 1 : Nat) : Rat) * b := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp [sumFinRat, Rat.zero_add, Rat.zero_mul, Rat.add_zero]
    | succ m =>
      have hih := ih (by omega)
      change sumFinRat (fun i : Fin (m + 1) => if i.val = 0 then a else b) +
        (if m + 1 = 0 then a else b) = a + ((m + 1 + 1 - 1 : Nat) : Rat) * b
      have hne : m + 1 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      rw [hih]
      have hm1 : m + 1 + 1 - 1 = (m + 1 - 1) + 1 := by omega
      rw [hm1, rat_natCast_add, Rat.add_mul]
      have h1b : ((1 : Nat) : Rat) * b = b := by simp
      rw [h1b, Rat.add_assoc]

theorem aux_loss_free_mean_bias_drift_exact
    (E : Nat) (hE : 2 ≤ E) (γ : Rat) (hγ : 0 < γ) :
    (∀ L : Fin E → Rat,
      (sumFinRat (signBiasDelta γ L) / (E : Rat)).abs ≤ (((E : Rat) - 2) / (E : Rat)) * γ) ∧
    (∃ L : Fin E → Rat,
      sumFinRat (signBiasDelta γ L) / (E : Rat) = (((E : Rat) - 2) / (E : Rat)) * γ) ∧
    (∀ L b : Fin E → Rat,
      sumFinRat (meanCenteredDelta γ L) = 0 ∧
      ∀ i j : Fin E,
        (b i + meanCenteredDelta γ L i) - (b j + meanCenteredDelta γ L j) =
        (b i + signBiasDelta γ L i) - (b j + signBiasDelta γ L j)) := by
  have hEpos : (0 : Rat) < (E : Rat) := rat_natCast_pos (by omega)
  have hEne : (E : Rat) ≠ 0 := rat_natCast_ne_zero (by omega)
  refine ⟨sumFinRat_signBiasDelta_bound E hE γ hγ, ?_, ?_⟩
  · -- Attainment witness: L 0 = E, L i = 0 for i > 0
    refine ⟨fun i => if i.val = 0 then (E : Rat) else 0, ?_⟩
    have hsumL : sumFinRat (fun i : Fin E => if i.val = 0 then (E : Rat) else 0) = (E : Rat) := by
      rw [sumFinRat_ite_zero (E : Rat) 0 (by omega), Rat.mul_zero, Rat.add_zero]
    have hmean : meanLoad (fun i : Fin E => if i.val = 0 then (E : Rat) else 0) = 1 := by
      unfold meanLoad
      rw [hsumL, Rat.div_def, Rat.mul_inv_cancel _ hEne]
    have hdelta : signBiasDelta γ (fun i : Fin E => if i.val = 0 then (E : Rat) else 0) =
        fun i : Fin E => if i.val = 0 then -γ else γ := by
      funext i
      unfold signBiasDelta
      rw [hmean]
      by_cases hi : i.val = 0
      · have hgt : (1 : Rat) < (E : Rat) := by
          have : (1 : Rat) = ((1 : Nat) : Rat) := by simp
          rw [this]; exact rat_natCast_lt (by omega)
        have hnot : ¬ ((E : Rat) < 1) := rat_not_lt_of_le (Rat.le_of_lt hgt)
        simp [hi, hnot, hgt]
      · have hlt : (0 : Rat) < 1 := by decide
        simp [hi, hlt]
    rw [hdelta, sumFinRat_ite_zero (-γ) γ (by omega)]
    have hcast : ((E - 1 : Nat) : Rat) = (E : Rat) - 1 := by
      have h1 : E = (E - 1) + 1 := by omega
      have h2 : (E : Rat) = ((E - 1 : Nat) : Rat) + 1 := by
        have h3 : ((E - 1 + 1 : Nat) : Rat) = ((E - 1 : Nat) : Rat) + ((1 : Nat) : Rat) :=
          rat_natCast_add (E - 1) 1
        rw [← h1] at h3
        simpa using h3
      rw [h2, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
    rw [hcast]
    have hnum : -γ + ((E : Rat) - 1) * γ = ((E : Rat) - 2) * γ := by
      rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, Rat.one_mul,
          Rat.add_comm (-γ), Rat.add_assoc]
      rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul]
      have h2γ : -((2 : Rat) * γ) = -γ + -γ := by
        have : (2 : Rat) = 1 + 1 := by exact Rat.natCast_add 1 1
        rw [this, Rat.add_mul, Rat.one_mul, Rat.neg_add]
      rw [h2γ]
    rw [hnum, Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.mul_comm γ ((E : Rat)⁻¹), ← Rat.mul_assoc]
  · -- Mean-centered sign update
    intro L b
    constructor
    · unfold meanCenteredDelta
      rw [sumFinRat_sub, sumFinRat_const]
      have hmul : (E : Rat) * (sumFinRat (signBiasDelta γ L) / (E : Rat)) =
          sumFinRat (signBiasDelta γ L) := by
        rw [Rat.div_def, Rat.mul_comm (sumFinRat _), ← Rat.mul_assoc,
            Rat.mul_inv_cancel _ hEne, Rat.one_mul]
      rw [hmul, Rat.sub_eq_add_neg, Rat.add_neg_cancel]
    · intro i j
      unfold meanCenteredDelta
      let c := sumFinRat (signBiasDelta γ L) / (E : Rat)
      change (b i + (signBiasDelta γ L i - c)) - (b j + (signBiasDelta γ L j - c)) =
        (b i + signBiasDelta γ L i) - (b j + signBiasDelta γ L j)
      simp only [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]
      rw [← Rat.add_assoc (b i), Rat.add_assoc (b i + signBiasDelta γ L i) (-c),
          ← Rat.add_assoc (-c) (-b j), Rat.add_comm (-c) (-b j),
          Rat.add_assoc (-b j) (-c), ← Rat.add_assoc (-c) (-signBiasDelta γ L j),
          Rat.add_comm (-c) (-signBiasDelta γ L j), Rat.add_assoc (-signBiasDelta γ L j) (-c),
          Rat.neg_add_cancel, Rat.add_zero, ← Rat.add_assoc (b i + signBiasDelta γ L i)]

/-! ## Theorem 2: Sharp Dead-Zone Fixed-Point Phase Transition -/

theorem dead_zone_fixed_point_threshold_exact
    (E B K : Nat) (hE : 0 < E) (hr : 0 < (B * K) % E) :
    let r := (B * K) % E
    let Lbar : Rat := ((B * K : Nat) : Rat) / (E : Rat)
    let τ_min : Rat := ((max r (E - r) : Nat) : Rat) / (E : Rat)
    (∀ L : Fin E → Nat, sumFinNat L = B * K →
      ∃ i : Fin E, τ_min ≤ ((L i : Rat) - Lbar).abs) ∧
    (∀ τ : Rat, τ < τ_min → ∀ L : Fin E → Nat, sumFinNat L = B * K →
      ¬ (∀ i : Fin E, ((L i : Rat) - Lbar).abs ≤ τ)) ∧
    (∃ L : Fin E → Nat, sumFinNat L = B * K ∧
      ∀ i : Fin E, ((L i : Rat) - Lbar).abs ≤ τ_min) := by
  intro r Lbar τ_min
  have hEpos : (0 : Rat) < (E : Rat) := rat_natCast_pos hE
  have hEne : (E : Rat) ≠ 0 := rat_natCast_ne_zero hE
  let q := (B * K) / E
  have hdiv : B * K = q * E + r := by
    have := Nat.div_add_mod (B * K) E
    rw [Nat.mul_comm] at this
    exact this.symm
  have hrlt : r < E := Nat.mod_lt (B * K) hE
  have hmain : ∀ L : Fin E → Nat, sumFinNat L = B * K →
      ∃ i : Fin E, τ_min ≤ ((L i : Rat) - Lbar).abs := by
    intro L hsum
    -- Step 1: exists i with L i ≤ q
    have hex_le : ∃ i : Fin E, L i ≤ q := by
      by_cases h : ∃ i : Fin E, L i ≤ q
      · exact h
      · exfalso
        have hge : ∀ i : Fin E, q + 1 ≤ L i := fun i => by
          have : ¬ (L i ≤ q) := fun hle => h ⟨i, hle⟩
          omega
        have hsum_ge : E * (q + 1) ≤ sumFinNat L := by
          rw [← sumFinNat_const E (q + 1)]
          exact sumFinNat_le hge
        rw [hsum, hdiv, Nat.mul_add, Nat.mul_one, Nat.mul_comm E q] at hsum_ge
        omega
    -- Step 2: exists j with q + 1 ≤ L j
    have hex_ge : ∃ j : Fin E, q + 1 ≤ L j := by
      by_cases h : ∃ j : Fin E, q + 1 ≤ L j
      · exact h
      · exfalso
        have hle : ∀ j : Fin E, L j ≤ q := fun j => by
          have : ¬ (q + 1 ≤ L j) := fun hge => h ⟨j, hge⟩
          omega
        have hsum_le : sumFinNat L ≤ E * q := by
          rw [← sumFinNat_const E q]
          exact sumFinNat_le hle
        rw [hsum, hdiv, Nat.mul_comm E q] at hsum_le
        omega
    by_cases hcmp : E - r ≤ r
    · -- max r (E - r) = r; pick i with L i ≤ q
      rcases hex_le with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hmax : max r (E - r) = r := by omega
      have hτ : τ_min = (r : Rat) / (E : Rat) := by
        show ((max r (E - r) : Nat) : Rat) / (E : Rat) = (r : Rat) / (E : Rat)
        rw [hmax]
      rw [hτ]
      have hle_neg : (r : Rat) / (E : Rat) ≤ -((L i : Rat) - Lbar) := by
        have hneg : -((L i : Rat) - Lbar) = Lbar - (L i : Rat) := by
          rw [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg, Rat.add_comm, ← Rat.sub_eq_add_neg]
        rw [hneg]
        have hdiff : Lbar - (L i : Rat) = (((B * K : Nat) : Rat) - (L i : Rat) * (E : Rat)) / (E : Rat) := by
          show ((B * K : Nat) : Rat) / (E : Rat) - (L i : Rat) = _
          rw [Rat.div_def, Rat.div_def, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg,
              Rat.add_mul, Rat.neg_mul, Rat.mul_assoc, Rat.mul_inv_cancel _ hEne, Rat.mul_one]
        rw [hdiff]
        apply rat_div_le_div_of_nonneg_right _ hEpos
        have hnat : L i * E + r ≤ B * K := by
          have : L i * E ≤ q * E := Nat.mul_le_mul_right E hi
          omega
        have hrat : ((L i * E + r : Nat) : Rat) ≤ ((B * K : Nat) : Rat) := rat_natCast_le hnat
        rw [rat_natCast_add, rat_natCast_mul] at hrat
        have h1 := (Rat.add_le_add_right (c := -((L i : Rat) * (E : Rat)))).mpr hrat
        simpa [Rat.sub_eq_add_neg, Rat.add_comm ((L i : Rat) * (E : Rat)) (r : Rat),
               Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero] using h1
      exact Rat.le_trans hle_neg (rat_neg_le_abs_self _)
    · -- max r (E - r) = E - r; pick j with q + 1 ≤ L j
      rcases hex_ge with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hmax : max r (E - r) = E - r := by omega
      have hτ : τ_min = ((E - r : Nat) : Rat) / (E : Rat) := by
        show ((max r (E - r) : Nat) : Rat) / (E : Rat) = ((E - r : Nat) : Rat) / (E : Rat)
        rw [hmax]
      rw [hτ]
      have hle_pos : ((E - r : Nat) : Rat) / (E : Rat) ≤ (L j : Rat) - Lbar := by
        have hdiff : (L j : Rat) - Lbar = ((L j : Rat) * (E : Rat) - ((B * K : Nat) : Rat)) / (E : Rat) := by
          show (L j : Rat) - ((B * K : Nat) : Rat) / (E : Rat) = _
          rw [Rat.div_def, Rat.div_def, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg,
              Rat.add_mul, Rat.neg_mul, Rat.mul_assoc, Rat.mul_inv_cancel _ hEne, Rat.mul_one]
        rw [hdiff]
        apply rat_div_le_div_of_nonneg_right _ hEpos
        have hnat : B * K + (E - r) ≤ L j * E := by
          have : (q + 1) * E ≤ L j * E := Nat.mul_le_mul_right E hj
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        have hrat : ((B * K + (E - r) : Nat) : Rat) ≤ ((L j * E : Nat) : Rat) := rat_natCast_le hnat
        rw [rat_natCast_add] at hrat
        have h1 := (Rat.add_le_add_right (c := -((B * K : Nat) : Rat))).mpr hrat
        rw [Rat.add_comm ((B * K : Nat) : Rat) ((E - r : Nat) : Rat),
            Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, rat_natCast_mul] at h1
        rw [Rat.sub_eq_add_neg]
        exact h1
      exact Rat.le_trans hle_pos (rat_le_abs_self _)
  refine ⟨hmain, ?_, ?_⟩
  · -- Impossibility for all τ < τ_min
    intro τ hτ L hsum hall
    rcases hmain L hsum with ⟨i, hi⟩
    exact Rat.lt_irrefl (rat_lt_of_le_of_lt (Rat.le_trans hi (hall i)) hτ)
  · -- Attainment witness: r experts with q + 1, E - r experts with q
    refine ⟨fun i => if i.val < r then q + 1 else q, ?_, ?_⟩
    · rw [sumFinNat_ite_lt E r (q + 1) q (Nat.le_of_lt hrlt)]
      rw [Nat.mul_add, Nat.mul_one]
      have h1 : (E - r) * q + r * q = E * q := by
        rw [← Nat.add_mul]
        have : E - r + r = E := by omega
        rw [this]
      rw [Nat.mul_comm E q] at h1
      omega
    · intro i
      by_cases hi : i.val < r
      · simp only [hi, ↓reduceIte]
        have hdiff : (((q + 1 : Nat) : Rat) - Lbar) = ((E - r : Nat) : Rat) / (E : Rat) := by
          show ((q + 1 : Nat) : Rat) - ((B * K : Nat) : Rat) / (E : Rat) = _
          rw [Rat.div_def, Rat.div_def, Rat.sub_eq_add_neg]
          have h1 : ((q + 1 : Nat) : Rat) = (((q + 1) * E : Nat) : Rat) * (E : Rat)⁻¹ := by
            rw [rat_natCast_mul, Rat.mul_assoc, Rat.mul_inv_cancel _ hEne, Rat.mul_one]
          rw [h1, ← Rat.neg_mul, ← Rat.add_mul]
          congr 1
          have hnat : (q + 1) * E = B * K + (E - r) := by
            rw [Nat.add_mul, Nat.one_mul]; omega
          rw [hnat, rat_natCast_add, Rat.add_comm ((B * K : Nat) : Rat),
              Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
        rw [hdiff, rat_abs_of_nonneg]
        · exact rat_div_le_div_of_nonneg_right (rat_natCast_le (Nat.le_max_right r (E - r))) hEpos
        · rw [Rat.div_def]
          exact rat_mul_nonneg (rat_natCast_nonneg _) (Rat.le_of_lt (rat_inv_pos hEpos))
      · simp only [hi, ↓reduceIte]
        have hdiff : ((q : Rat) - Lbar) = -((r : Rat) / (E : Rat)) := by
          show (q : Rat) - ((B * K : Nat) : Rat) / (E : Rat) = _
          rw [Rat.div_def, Rat.div_def, Rat.sub_eq_add_neg, ← Rat.neg_mul]
          have h1 : (q : Rat) = ((q * E : Nat) : Rat) * (E : Rat)⁻¹ := by
            rw [rat_natCast_mul, Rat.mul_assoc, Rat.mul_inv_cancel _ hEne, Rat.mul_one]
          rw [h1, ← Rat.neg_mul, ← Rat.add_mul]
          congr 1
          rw [hdiv, rat_natCast_add, Rat.neg_add, ← Rat.add_assoc,
              Rat.add_neg_cancel, Rat.zero_add]
        rw [hdiff, rat_abs_neg, rat_abs_of_nonneg]
        · exact rat_div_le_div_of_nonneg_right (rat_natCast_le (Nat.le_max_left r (E - r))) hEpos
        · rw [Rat.div_def]
          exact rat_mul_nonneg (rat_natCast_nonneg _) (Rat.le_of_lt (rat_inv_pos hEpos))

end MoeBiasPlacement
