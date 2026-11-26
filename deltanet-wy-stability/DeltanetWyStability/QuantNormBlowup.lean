/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltanetWyStability.RatAlg

/-!
# Theorem 2: Exact Quantized-Key Squared-Norm Blowup & Safe Step-Size Ceilings
-/

namespace DeltanetWyStability

theorem rat_sq_ge_of_ge {x c : Rat} (hc : 0 ≤ c) (h : c ≤ x) : c * c ≤ x * x :=
  rat_mul_le_mul_nonneg hc hc h h

theorem e2m1Quant_sq_eq (x : Rat) :
    e2m1Quant x * e2m1Quant x = e2m1QuantNonneg (ratAbs x) * e2m1QuantNonneg (ratAbs x) := by
  unfold e2m1Quant ratAbs
  split
  · rfl
  · grind

theorem ratAbs_sq_eq (x : Rat) : ratAbs x * ratAbs x = x * x := by
  unfold ratAbs
  split <;> grind

/-- Per-coordinate upper bound for OCP v1.0 MXFP4 (`R = 700 / 431`):
    for every `x : Rat`, `Q(x)^2 - (700/431) x^2 ≤ 64 / 431`. -/
theorem e2m1_coord_ocp (x : Rat) :
    e2m1QuantNonneg x * e2m1QuantNonneg x - (700 / 431) * (x * x) ≤ 64 / 431 := by
  unfold e2m1QuantNonneg
  split
  · have h := rat_sq_nonneg x; grind
  · split
    · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 1 / 4) (by grind : (1 / 4 : Rat) ≤ x); grind
    · split
      · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 3 / 4) (by grind : (3 / 4 : Rat) ≤ x); grind
      · split
        · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 5 / 4) (by grind : (5 / 4 : Rat) ≤ x); grind
        · split
          · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 7 / 4) (by grind : (7 / 4 : Rat) ≤ x); grind
          · split
            · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 5 / 2) (by grind : (5 / 2 : Rat) ≤ x); grind
            · split
              · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 7 / 2) (by grind : (7 / 2 : Rat) ≤ x); grind
              · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 5) (by grind : (5 : Rat) ≤ x); grind

/-- Anchor coordinate upper bound for OCP v1.0 MXFP4 (`x ≥ 4`, `R = 700 / 431`):
    `Q(x)^2 - (700/431) x^2 ≤ -1984 / 431 = -31 * (64 / 431)`. -/
theorem e2m1_anchor_ocp (x : Rat) (hx : 4 ≤ x) :
    e2m1QuantNonneg x * e2m1QuantNonneg x - (700 / 431) * (x * x) ≤ -(1984 / 431) := by
  unfold e2m1QuantNonneg
  have h1 : ¬ x < 1 / 4 := by grind
  have h2 : ¬ x < 3 / 4 := by grind
  have h3 : ¬ x < 5 / 4 := by grind
  have h4 : ¬ x < 7 / 4 := by grind
  have h5 : ¬ x < 5 / 2 := by grind
  have h6 : ¬ x < 7 / 2 := by grind
  simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte]
  split
  · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 4) hx; grind
  · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 5) (by grind : (5 : Rat) ≤ x); grind

/-- Per-coordinate upper bound for max-fit MXFP4 (`R = 380 / 227`):
    for every `x : Rat`, `Q(x)^2 - (380/227) x^2 ≤ 33 / 227`. -/
theorem e2m1_coord_maxfit (x : Rat) :
    e2m1QuantNonneg x * e2m1QuantNonneg x - (380 / 227) * (x * x) ≤ 33 / 227 := by
  unfold e2m1QuantNonneg
  split
  · have h := rat_sq_nonneg x; grind
  · split
    · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 1 / 4) (by grind : (1 / 4 : Rat) ≤ x); grind
    · split
      · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 3 / 4) (by grind : (3 / 4 : Rat) ≤ x); grind
      · split
        · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 5 / 4) (by grind : (5 / 4 : Rat) ≤ x); grind
        · split
          · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 7 / 4) (by grind : (7 / 4 : Rat) ≤ x); grind
          · split
            · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 5 / 2) (by grind : (5 / 2 : Rat) ≤ x); grind
            · split
              · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 7 / 2) (by grind : (7 / 2 : Rat) ≤ x); grind
              · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 5) (by grind : (5 : Rat) ≤ x); grind

/-- Anchor coordinate upper bound for max-fit MXFP4 (`x ≥ 3`, `R = 380 / 227`):
    `Q(x)^2 - (380/227) x^2 ≤ -1023 / 227 = -31 * (33 / 227)`. -/
theorem e2m1_anchor_maxfit (x : Rat) (hx : 3 ≤ x) :
    e2m1QuantNonneg x * e2m1QuantNonneg x - (380 / 227) * (x * x) ≤ -(1023 / 227) := by
  unfold e2m1QuantNonneg
  have h1 : ¬ x < 1 / 4 := by grind
  have h2 : ¬ x < 3 / 4 := by grind
  have h3 : ¬ x < 5 / 4 := by grind
  have h4 : ¬ x < 7 / 4 := by grind
  have h5 : ¬ x < 5 / 2 := by grind
  simp only [h1, h2, h3, h4, h5, ↓reduceIte]
  split
  · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 3) hx; grind
  · split
    · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 7 / 2) (by grind : (7 / 2 : Rat) ≤ x); grind
    · have h := rat_sq_ge_of_ge (by grind : (0 : Rat) ≤ 5) (by grind : (5 : Rat) ≤ x); grind

theorem sumFin_const_except {n : Nat} (i0 : Fin n) (c : Rat) :
    sumFin (fun i : Fin n => if i = i0 then (0 : Rat) else c) = ((n : Rat) - 1) * c := by
  have h := sumFin_split_at i0 (fun _ : Fin n => c)
  rw [sumFin_const] at h
  grind

/-- Universal OCP v1.0 MXFP4 (`B = 32`) squared-norm blowup upper bound `700 / 431`. -/
theorem e2m1_ocp_block_bound (y : Fin 32 → Rat) (hanchor : ∃ i0, 4 ≤ ratAbs (y i0)) :
    normSq (fun i => e2m1Quant (y i)) ≤ (700 / 431) * normSq y := by
  rcases hanchor with ⟨i0, hi0⟩
  have hdiff : normSq (fun i => e2m1Quant (y i)) - (700 / 431) * normSq y =
      sumFin (fun i => e2m1Quant (y i) * e2m1Quant (y i) - (700 / 431) * (y i * y i)) := by
    unfold normSq dot
    rw [← sumFin_mul_left, ← sumFin_sub_fn]
  have hsplit := sumFin_split_at i0 (fun i => e2m1Quant (y i) * e2m1Quant (y i) - (700 / 431) * (y i * y i))
  have ha : e2m1Quant (y i0) * e2m1Quant (y i0) - (700 / 431) * (y i0 * y i0) ≤ -(1984 / 431) := by
    rw [e2m1Quant_sq_eq, ← ratAbs_sq_eq (y i0)]
    exact e2m1_anchor_ocp (ratAbs (y i0)) hi0
  have hrest : sumFin (fun i => if i = i0 then (0 : Rat) else
        e2m1Quant (y i) * e2m1Quant (y i) - (700 / 431) * (y i * y i)) ≤
      sumFin (fun i => if i = i0 then (0 : Rat) else (64 / 431 : Rat)) := by
    apply sumFin_le_sumFin
    intro i
    by_cases h : i = i0
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [e2m1Quant_sq_eq, ← ratAbs_sq_eq (y i)]
      exact e2m1_coord_ocp (ratAbs (y i))
  rw [sumFin_const_except] at hrest
  grind

/-- Universal max-fit MXFP4 (`B = 32`) squared-norm blowup upper bound `380 / 227`. -/
theorem e2m1_maxfit_block_bound (y : Fin 32 → Rat) (hanchor : ∃ i0, 3 ≤ ratAbs (y i0)) :
    normSq (fun i => e2m1Quant (y i)) ≤ (380 / 227) * normSq y := by
  rcases hanchor with ⟨i0, hi0⟩
  have hdiff : normSq (fun i => e2m1Quant (y i)) - (380 / 227) * normSq y =
      sumFin (fun i => e2m1Quant (y i) * e2m1Quant (y i) - (380 / 227) * (y i * y i)) := by
    unfold normSq dot
    rw [← sumFin_mul_left, ← sumFin_sub_fn]
  have hsplit := sumFin_split_at i0 (fun i => e2m1Quant (y i) * e2m1Quant (y i) - (380 / 227) * (y i * y i))
  have ha : e2m1Quant (y i0) * e2m1Quant (y i0) - (380 / 227) * (y i0 * y i0) ≤ -(1023 / 227) := by
    rw [e2m1Quant_sq_eq, ← ratAbs_sq_eq (y i0)]
    exact e2m1_anchor_maxfit (ratAbs (y i0)) hi0
  have hrest : sumFin (fun i => if i = i0 then (0 : Rat) else
        e2m1Quant (y i) * e2m1Quant (y i) - (380 / 227) * (y i * y i)) ≤
      sumFin (fun i => if i = i0 then (0 : Rat) else (33 / 227 : Rat)) := by
    apply sumFin_le_sumFin
    intro i
    by_cases h : i = i0
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [e2m1Quant_sq_eq, ← ratAbs_sq_eq (y i)]
      exact e2m1_coord_maxfit (ratAbs (y i))
  rw [sumFin_const_except] at hrest
  grind

theorem e2m1_ocp_witness_attains :
    (∃ i0, 4 ≤ ratAbs (e2m1OcpWitness i0)) ∧
    normSq (fun i => e2m1Quant (e2m1OcpWitness i)) = (700 / 431) * normSq e2m1OcpWitness := by
  let z0 : Fin 32 := ⟨0, by decide⟩
  constructor
  · refine ⟨z0, ?_⟩
    simp only [z0, e2m1OcpWitness, ratAbs, ↓reduceIte]
    grind
  · have hnum : normSq (fun i => e2m1Quant (e2m1OcpWitness i)) = 175 / 4 := by
      unfold normSq dot
      rw [sumFin_split_at z0]
      dsimp only
      have h0 : e2m1Quant (e2m1OcpWitness z0) = 6 := by
        simp only [z0, e2m1OcpWitness, e2m1Quant, e2m1QuantNonneg, ↓reduceIte]
        grind
      have hrest : sumFin (fun i : Fin 32 => if i = z0 then (0 : Rat) else
          e2m1Quant (e2m1OcpWitness i) * e2m1Quant (e2m1OcpWitness i)) =
          sumFin (fun i : Fin 32 => if i = z0 then (0 : Rat) else (1 / 4 : Rat)) := by
        apply sumFin_congr
        intro i
        by_cases h : i = z0
        · simp [h]
        · have hv : i.val ≠ 0 := fun hv => h (Fin.ext hv)
          simp only [h, ↓reduceIte, e2m1OcpWitness, hv, e2m1Quant, e2m1QuantNonneg]
          grind
      rw [h0, hrest, sumFin_const_except]
      grind
    have hden : normSq e2m1OcpWitness = 431 / 16 := by
      unfold normSq dot
      rw [sumFin_split_at z0]
      have h0 : e2m1OcpWitness z0 = 5 := by simp [z0, e2m1OcpWitness]
      have hrest : sumFin (fun i : Fin 32 => if i = z0 then (0 : Rat) else
          e2m1OcpWitness i * e2m1OcpWitness i) =
          sumFin (fun i : Fin 32 => if i = z0 then (0 : Rat) else (1 / 16 : Rat)) := by
        apply sumFin_congr
        intro i
        by_cases h : i = z0
        · simp [h]
        · have hv : i.val ≠ 0 := fun hv => h (Fin.ext hv)
          simp only [h, ↓reduceIte, e2m1OcpWitness, hv]
          grind
      rw [h0, hrest, sumFin_const_except]
      grind
    rw [hnum, hden]
    grind

theorem e2m1_maxfit_witness_attains :
    (∃ i0, 3 < ratAbs (e2m1MaxFitWitness i0)) ∧
    normSq (fun i => e2m1Quant (e2m1MaxFitWitness i)) = (380 / 227) * normSq e2m1MaxFitWitness := by
  let z0 : Fin 32 := ⟨0, by decide⟩
  constructor
  · refine ⟨z0, ?_⟩
    simp only [z0, e2m1MaxFitWitness, ratAbs, ↓reduceIte]
    grind
  · have hnum : normSq (fun i => e2m1Quant (e2m1MaxFitWitness i)) = 95 / 4 := by
      unfold normSq dot
      rw [sumFin_split_at z0]
      dsimp only
      have h0 : e2m1Quant (e2m1MaxFitWitness z0) = 4 := by
        simp only [z0, e2m1MaxFitWitness, e2m1Quant, e2m1QuantNonneg, ↓reduceIte]
        grind
      have hrest : sumFin (fun i : Fin 32 => if i = z0 then (0 : Rat) else
          e2m1Quant (e2m1MaxFitWitness i) * e2m1Quant (e2m1MaxFitWitness i)) =
          sumFin (fun i : Fin 32 => if i = z0 then (0 : Rat) else (1 / 4 : Rat)) := by
        apply sumFin_congr
        intro i
        by_cases h : i = z0
        · simp [h]
        · have hv : i.val ≠ 0 := fun hv => h (Fin.ext hv)
          simp only [h, ↓reduceIte, e2m1MaxFitWitness, hv, e2m1Quant, e2m1QuantNonneg]
          grind
      rw [h0, hrest, sumFin_const_except]
      grind
    have hden : normSq e2m1MaxFitWitness = 227 / 16 := by
      unfold normSq dot
      rw [sumFin_split_at z0]
      have h0 : e2m1MaxFitWitness z0 = 7 / 2 := by simp [z0, e2m1MaxFitWitness]
      have hrest : sumFin (fun i : Fin 32 => if i = z0 then (0 : Rat) else
          e2m1MaxFitWitness i * e2m1MaxFitWitness i) =
          sumFin (fun i : Fin 32 => if i = z0 then (0 : Rat) else (1 / 16 : Rat)) := by
        apply sumFin_congr
        intro i
        by_cases h : i = z0
        · simp [h]
        · have hv : i.val ≠ 0 := fun hv => h (Fin.ext hv)
          simp only [h, ↓reduceIte, e2m1MaxFitWitness, hv]
          grind
      rw [h0, hrest, sumFin_const_except]
      grind
    rw [hnum, hden]
    grind

theorem two_pow_pos_rat (m : Nat) : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have h2 : (1 : Rat) ≤ ((2 ^ m : Nat) : Rat) := by exact_mod_cast h1
  grind

/-- Universal `m`-bit normal-range rounding midpoint identity. -/
theorem normalBin_midpoint_eq (m : Nat) :
    (normalBinUpper m / normalBinMid m) * (normalBinUpper m / normalBinMid m) =
      normalMaxRatioSq m := by
  unfold normalBinUpper normalBinMid normalMaxRatioSq
  have hpow : ((2 ^ (m + 1) : Nat) : Rat) = 2 * ((2 ^ m : Nat) : Rat) := by
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Rat.natCast_mul 2 (2 ^ m)
  rw [hpow]
  let p : Rat := ((2 ^ m : Nat) : Rat)
  change ((p + 1) / (p + 1 / 2)) * ((p + 1) / (p + 1 / 2)) =
    ((2 * p + 2) / (2 * p + 1)) * ((2 * p + 2) / (2 * p + 1))
  have hp : 0 < p := two_pow_pos_rat m
  have hden1 : p + 1 / 2 ≠ 0 := by grind
  have hden2 : 2 * p + 1 ≠ 0 := by grind
  have hratio : (p + 1) / (p + 1 / 2) = (2 * p + 2) / (2 * p + 1) := by
    rw [Rat.div_def, Rat.div_def]
    have h2 : (p + 1) * (2 * p + 1) = (2 * p + 2) * (p + 1 / 2) := by grind
    have h3 : ((p + 1) * (p + 1 / 2)⁻¹) * (p + 1 / 2) * (2 * p + 1) =
        ((2 * p + 2) * (2 * p + 1)⁻¹) * (p + 1 / 2) * (2 * p + 1) := by
      have ha : ((p + 1) * (p + 1 / 2)⁻¹) * (p + 1 / 2) = p + 1 := by
        rw [Rat.mul_assoc, Rat.inv_mul_cancel _ hden1]; grind
      have hb : ((2 * p + 2) * (2 * p + 1)⁻¹) * (p + 1 / 2) * (2 * p + 1) =
          (2 * p + 2) * (p + 1 / 2) := by
        have hswap : ((2 * p + 2) * (2 * p + 1)⁻¹) * (p + 1 / 2) * (2 * p + 1) =
            (2 * p + 2) * (p + 1 / 2) * ((2 * p + 1)⁻¹ * (2 * p + 1)) := by grind
        rw [hswap, Rat.inv_mul_cancel _ hden2]; grind
      rw [ha, hb, h2]
    have hmul_ne : (p + 1 / 2) * (2 * p + 1) ≠ 0 := by
      intro h0
      rcases Rat.mul_eq_zero.mp h0 with h | h
      · exact hden1 h
      · exact hden2 h
    have h4 : ((p + 1) * (p + 1 / 2)⁻¹ - (2 * p + 2) * (2 * p + 1)⁻¹) * ((p + 1 / 2) * (2 * p + 1)) = 0 := by
      grind
    rcases Rat.mul_eq_zero.mp h4 with h | h
    · grind
    · exact absurd h hmul_ne
  rw [hratio]

/-- Universal `m`-bit normal-range rounding upper bound for all `t ≥ 2^m + 1/2`. -/
theorem normalBin_round_up_bound (m : Nat) (t : Rat) (ht : normalBinMid m ≤ t) :
    (normalBinUpper m / t) * (normalBinUpper m / t) ≤ normalMaxRatioSq m := by
  rw [← normalBin_midpoint_eq m]
  have hp : 0 < ((2 ^ m : Nat) : Rat) := two_pow_pos_rat m
  have hmid : 0 < normalBinMid m := by unfold normalBinMid; grind
  have hup : 0 ≤ normalBinUpper m := by unfold normalBinUpper; grind
  have htpos : 0 < t := by grind
  have hratio : normalBinUpper m / t ≤ normalBinUpper m / normalBinMid m :=
    rat_div_le_div_of_le_left hup hmid ht
  have hnonneg : 0 ≤ normalBinUpper m / t := by
    rw [Rat.div_def]
    exact rat_mul_nonneg hup (by have := rat_inv_pos htpos; grind)
  exact rat_mul_le_mul_nonneg hnonneg hnonneg hratio hratio

/-- Headline Theorem 2: Exact MXFP4 (OCP v1.0 & max-fit), MXFP6, FP8, and BF16
    quantized-key squared-norm blowup bounds, witnesses, and safe step-size ceilings. -/
theorem mxfp4_mxfp6_fp8_bf16_norm_blowup_and_beta_safe :
    (∀ y : Fin 32 → Rat, (∃ i0, 4 ≤ ratAbs (y i0)) →
      normSq (fun i => e2m1Quant (y i)) ≤ (700 / 431) * normSq y) ∧
    ((∃ i0, 4 ≤ ratAbs (e2m1OcpWitness i0)) ∧
      normSq (fun i => e2m1Quant (e2m1OcpWitness i)) = (700 / 431) * normSq e2m1OcpWitness) ∧
    (36 / 25 : Rat) < 700 / 431 ∧
    betaSafe (700 / 431) = 431 / 350 ∧
    (∀ y : Fin 32 → Rat, (∃ i0, 3 ≤ ratAbs (y i0)) →
      normSq (fun i => e2m1Quant (y i)) ≤ (380 / 227) * normSq y) ∧
    ((∃ i0, 3 < ratAbs (e2m1MaxFitWitness i0)) ∧
      normSq (fun i => e2m1Quant (e2m1MaxFitWitness i)) = (380 / 227) * normSq e2m1MaxFitWitness) ∧
    betaSafe (380 / 227) = 227 / 190 ∧
    (∀ m : Nat, ∀ t : Rat, normalBinMid m ≤ t →
      (normalBinUpper m / t) * (normalBinUpper m / t) ≤ normalMaxRatioSq m) ∧
    (∀ m : Nat, (normalBinUpper m / normalBinMid m) * (normalBinUpper m / normalBinMid m) =
      normalMaxRatioSq m) ∧
    (normalMaxRatioSq 1 = 36 / 25 ∧ betaSafe (normalMaxRatioSq 1) = 25 / 18) ∧
    (normalMaxRatioSq 2 = 100 / 81 ∧ betaSafe (normalMaxRatioSq 2) = 81 / 50) ∧
    (normalMaxRatioSq 3 = 324 / 289 ∧ betaSafe (normalMaxRatioSq 3) = 289 / 162) ∧
    (normalMaxRatioSq 7 = 66564 / 66049 ∧ betaSafe (normalMaxRatioSq 7) = 66049 / 33282) := by
  refine ⟨e2m1_ocp_block_bound, e2m1_ocp_witness_attains, ?_, ?_,
    e2m1_maxfit_block_bound, e2m1_maxfit_witness_attains, ?_,
    normalBin_round_up_bound, normalBin_midpoint_eq, ?_, ?_, ?_, ?_⟩
  · grind
  · simp only [betaSafe]; grind
  · simp only [betaSafe]; grind
  · constructor <;> (simp only [normalMaxRatioSq, betaSafe]; grind)
  · constructor <;> (simp only [normalMaxRatioSq, betaSafe]; grind)
  · constructor <;> (simp only [normalMaxRatioSq, betaSafe]; grind)
  · constructor <;> (simp only [normalMaxRatioSq, betaSafe]; grind)

end DeltanetWyStability
