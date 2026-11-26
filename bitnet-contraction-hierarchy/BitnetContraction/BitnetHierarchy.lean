/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitnetContraction.TernaryNonneg

/-!
# Theorems 2, 3, and 4: Exact Three-Tier BitNet Heuristic Contraction Hierarchy

Pure-`Init` Lean 4 proofs over `Rat` (zero Mathlib, zero calculus):
- **Theorem 2 (`bitnet_absmean_contraction_exact`):**
  Universal bound `ternErrSq γ x ≤ (1 - (2d - 1) / d^2) * normSq x` for `γ = l1Norm x / d`,
  with exact attainment on `unitE0 d = (1, 0, ..., 0)`.
- **Theorem 3 (`bitnet_absmax_and_half_contraction_exact`):**
  Universal bounds `4 / (d + 3)` for `AbsMax` (`γ = M`) and `12 / (d + 15)` for `AbsMax/2`
  (`γ = M / 2`), with exact attainment on `absMaxWitness d` and `absMaxHalfWitness d`.
- **Theorem 4 (`bitnet_rms_contraction_exact_algebraic`):**
  Universal algebraic squared-form bound `((d : Rat) * α + 1)^2 ≥ 3 * d + 1` whenever
  `d * γ^2 = normSq x` (`γ > 0`), with exact rational attainment for all `s^2 = 3d + 1`
  and concrete witnesses at `d = 8` (`α = 1/2`) and `d = 16` (`α = 3/8`).
-/

namespace BitnetContraction

/-! ## Concrete Rational Inequality Constants (avoiding `decide` on `Rat.div`) -/

private theorem rat_half_nonneg : (0 : Rat) ≤ (1 : Rat) / 2 :=
  rat_div_nonneg (by decide : (0 : Rat) ≤ 1) (by decide : (0 : Rat) < 2)

private theorem rat_half_le_one : (1 : Rat) / 2 ≤ 1 := by
  have h := rat_div_le_div_of_nonneg (by decide : (1 : Rat) ≤ 2) (by decide : (0 : Rat) < 2)
  have e : (2 : Rat) / 2 = 1 := by grind
  rw [e] at h
  exact h

private theorem rat_quarter_nonneg : (0 : Rat) ≤ (1 : Rat) / 4 :=
  rat_div_nonneg (by decide : (0 : Rat) ≤ 1) (by decide : (0 : Rat) < 4)

private theorem rat_quarter_le_one : (1 : Rat) / 4 ≤ 1 := by
  have h := rat_div_le_div_of_nonneg (by decide : (1 : Rat) ≤ 4) (by decide : (0 : Rat) < 4)
  have e : (4 : Rat) / 4 = 1 := by grind
  rw [e] at h
  exact h

private theorem rat_quarter_le_half : (1 : Rat) / 4 ≤ (1 : Rat) / 2 := by
  have h := rat_div_le_div_of_nonneg (by decide : (1 : Rat) ≤ 2) (by decide : (0 : Rat) < 4)
  have e : (2 : Rat) / 4 = (1 : Rat) / 2 := by grind
  rw [e] at h
  exact h

/-- At the tie boundary `|x| = γ / 2`, both `±γ` and `0` have the exact same squared error `γ^2 / 4`,
    so `ternErrSq γ x = ternErrSqStrict γ x` identically for all `0 ≤ γ`. -/
theorem ternErrSq_eq_strict {d : Nat} {γ : Rat} (hγ : 0 ≤ γ) (x : Fin d → Rat) :
    ternErrSq γ x = ternErrSqStrict γ x := by
  have hgain : normSq x - ternErrSq γ x = normSq x - ternErrSqStrict γ x := by
    rw [ternErrSq_gain_eq hγ x, ternErrSqStrict_gain_eq hγ x]
    apply sumRat_congr
    intro i
    by_cases hgt : γ / 2 < (x i).abs
    · have hle : γ / 2 ≤ (x i).abs := Rat.le_of_lt hgt
      simp only [hgt, hle, ite_true]
    · simp only [hgt, ite_false]
      by_cases hge : γ / 2 ≤ (x i).abs
      · have heq : (x i).abs = γ / 2 := Rat.le_antisymm (Rat.not_lt.mp hgt) hge
        simp only [heq]
        grind
      · simp only [hge, ite_false]
  grind

/-! ## Shared Rescaling & Positive-Norm Helpers -/

private theorem exists_nonzero_of_normSq_pos {d : Nat} {x : Fin d → Rat} (hpos : 0 < normSq x) :
    ∃ i : Fin d, x i ≠ 0 := by
  induction d with
  | zero =>
    unfold normSq sumRat at hpos
    exact absurd hpos (by decide)
  | succ k ih =>
    unfold normSq at hpos
    simp only [sumRat] at hpos
    by_cases hlast : x ⟨k, Nat.lt_succ_self k⟩ = 0
    · rw [hlast] at hpos
      have h0 : (0 : Rat) * 0 = 0 := by grind
      have hadd : sumRat (fun i : Fin k => x i.castSucc * x i.castSucc) + 0 =
          sumRat (fun i : Fin k => x i.castSucc * x i.castSucc) := by grind
      rw [h0, hadd] at hpos
      obtain ⟨i, hi⟩ := ih (x := fun i : Fin k => x i.castSucc) hpos
      exact ⟨i.castSucc, hi⟩
    · exact ⟨⟨k, Nat.lt_succ_self k⟩, hlast⟩

private theorem l1Norm_pos_of_normSq_pos {d : Nat} {x : Fin d → Rat} (hpos : 0 < normSq x) :
    0 < l1Norm x := by
  obtain ⟨i0, hi0⟩ := exists_nonzero_of_normSq_pos hpos
  have habs_ne : (x i0).abs ≠ 0 := fun h => hi0 ((rat_abs_eq_zero_iff (x i0)).mp h)
  have habs_pos : 0 < (x i0).abs :=
    Rat.lt_iff_le_and_ne.mpr ⟨rat_abs_nonneg (x i0), habs_ne.symm⟩
  have hlt := sumRat_lt_sumRat_of_le_of_lt
    (f := fun _ : Fin d => (0 : Rat))
    (g := fun i : Fin d => (x i).abs)
    (fun i => rat_abs_nonneg (x i))
    ⟨i0, habs_pos⟩
  rw [sumRat_zero] at hlt
  exact hlt

/-- Rescaled gain identity: for `γ > 0` and `z i = |x i| / γ`,
    `normSq x - ternErrSq γ x = γ^2 * ∑_i (if 1/2 ≤ z i then 2 * z i - 1 else 0)`. -/
private theorem gain_rescaled {d : Nat} {γ : Rat} (hγ : 0 < γ) (x : Fin d → Rat) :
    normSq x - ternErrSq γ x =
      (γ * γ) * sumRat (fun i =>
        let z := (x i).abs / γ
        if (1 : Rat) / 2 ≤ z then 2 * z - 1 else 0) := by
  have hγnn : 0 ≤ γ := Rat.le_of_lt hγ
  have hγ0 : γ ≠ 0 := (Rat.lt_iff_le_and_ne.mp hγ).2.symm
  rw [ternErrSq_gain_eq hγnn x, ← sumRat_mul_left]
  apply sumRat_congr
  intro i
  have hiff : (γ / 2 ≤ (x i).abs) ↔ ((1 : Rat) / 2 ≤ (x i).abs / γ) := by
    constructor
    · intro h
      have h1 := rat_div_le_div_of_nonneg h hγ
      have h2 : (γ / 2) / γ = (1 : Rat) / 2 := by grind
      rw [h2] at h1
      exact h1
    · intro h
      have h1 := Rat.mul_le_mul_of_nonneg_left h hγnn
      have h2 : γ * ((1 : Rat) / 2) = γ / 2 := by grind
      have h3 : γ * ((x i).abs / γ) = (x i).abs := by grind
      rw [h2, h3] at h1
      exact h1
  by_cases hc : (1 : Rat) / 2 ≤ (x i).abs / γ
  · have hl : γ / 2 ≤ (x i).abs := hiff.mpr hc
    simp only [hl, hc, ite_true]
    grind
  · have hl : ¬ (γ / 2 ≤ (x i).abs) := fun h => hc (hiff.mp h)
    simp only [hl, hc, ite_false]
    grind

private theorem normSq_rescaled {d : Nat} {γ : Rat} (hγ : 0 < γ) (x : Fin d → Rat) :
    normSq x = (γ * γ) * sumRat (fun i => ((x i).abs / γ) * ((x i).abs / γ)) := by
  have hγ0 : γ ≠ 0 := (Rat.lt_iff_le_and_ne.mp hγ).2.symm
  unfold normSq
  rw [← sumRat_mul_left]
  apply sumRat_congr
  intro i
  have hsq := rat_abs_sq (x i)
  have heq : γ * γ * ((x i).abs / γ * ((x i).abs / γ)) = (x i).abs * (x i).abs := by grind
  rw [heq, hsq]

/-! ## Theorem 2: Exact BitNet b1.58 `AbsMean` Contraction Law -/

/-- Core normalized `AbsMean` inequality: for `d ≥ 1`, `z : Fin d → Rat` with `z i ≥ 0` and
    `∑_i z_i = d`, we have `(2d - 1) * ∑_i z_i^2 ≤ d^2 * ∑_{z_i ≥ 1/2} (2 z_i - 1)`. -/
private theorem absmean_normalized {d : Nat} (hd : 1 ≤ d) (z : Fin d → Rat)
    (hz : ∀ i, 0 ≤ z i) (hsum : sumRat z = (d : Rat)) :
    (2 * (d : Rat) - 1) * sumRat (fun i => z i * z i) ≤
      ((d : Rat) * (d : Rat)) * sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0) := by
  have hd_pos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  by_cases hd1 : d = 1
  · subst hd1
    have h0 : z ⟨0, by decide⟩ = 1 := by
      unfold sumRat at hsum
      have h1 : (0 : Rat) + z ⟨0, by decide⟩ = z ⟨0, by decide⟩ := by grind
      have h2 : ((1 : Nat) : Rat) = 1 := by grind
      rw [sumRat, h1, h2] at hsum
      exact hsum
    unfold sumRat
    simp only [sumRat, h0, rat_half_le_one, ite_true]
    have heq : (2 * ((1 : Nat) : Rat) - 1) * (0 + 1 * 1) =
        ((1 : Nat) : Rat) * ((1 : Nat) : Rat) * (0 + (2 * 1 - 1)) := by grind
    rw [heq]
    exact Rat.le_refl
  · have hd2 : 2 ≤ d := by omega
    have hd2_rat : (2 : Rat) ≤ (d : Rat) := rat_natCast_le hd2
    let k : Rat := sumRat (fun i => if (1 : Rat) / 2 ≤ z i then (1 : Rat) else 0)
    let SQ : Rat := sumRat (fun i => if (1 : Rat) / 2 ≤ z i then z i else 0)
    let u : Rat := SQ - k / 2
    -- 1. Gain equals 2 * u
    have hgain_u : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0) = 2 * u := by
      have h1 : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0) =
          sumRat (fun i => (if (1 : Rat) / 2 ≤ z i then 2 * z i else 0) -
            (if (1 : Rat) / 2 ≤ z i then (1 : Rat) else 0)) := by
        apply sumRat_congr
        intro i
        by_cases h : (1 : Rat) / 2 ≤ z i
        · simp only [h, ite_true]
        · simp only [h, ite_false]; grind
      rw [h1, sumRat_sub]
      have h2 : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i else 0) = 2 * SQ := by
        dsimp [SQ]
        rw [← sumRat_mul_left]
        apply sumRat_congr
        intro i
        by_cases h : (1 : Rat) / 2 ≤ z i
        · simp only [h, ite_true]
        · simp only [h, ite_false]; grind
      rw [h2]
      change 2 * SQ - k = 2 * u
      dsimp [u]
      grind
    -- 2. Split sum of z into Q and Q^c
    let SnotQ : Rat := sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 0 else z i)
    have hsplit_z : SQ + SnotQ = (d : Rat) := by
      dsimp [SQ, SnotQ]
      rw [← sumRat_add]
      have h1 : sumRat (fun i => (if (1 : Rat) / 2 ≤ z i then z i else 0) +
          (if (1 : Rat) / 2 ≤ z i then 0 else z i)) = sumRat z := by
        apply sumRat_congr
        intro i
        by_cases h : (1 : Rat) / 2 ≤ z i
        · simp only [h, ite_true]; grind
        · simp only [h, ite_false]; grind
      rw [h1, hsum]
    -- 3. SnotQ ≤ (d - k) / 2, hence u ≥ d / 2
    have hSnotQ_le : SnotQ ≤ ((d : Rat) - k) / 2 := by
      have h1 : SnotQ ≤ sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 0 else (1 : Rat) / 2) := by
        dsimp [SnotQ]
        apply sumRat_le_sumRat
        intro i
        by_cases h : (1 : Rat) / 2 ≤ z i
        · simp only [h, ite_true]; exact Rat.le_refl
        · simp only [h, ite_false]
          exact Rat.le_of_lt (Rat.not_le.mp h)
      have h2 : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 0 else (1 : Rat) / 2) =
          ((d : Rat) - k) / 2 := by
        have ha : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 0 else (1 : Rat) / 2) =
            sumRat (fun i => ((1 : Rat) / 2) - (if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 2 else 0)) := by
          apply sumRat_congr
          intro i
          by_cases h : (1 : Rat) / 2 ≤ z i
          · simp only [h, ite_true]; grind
          · simp only [h, ite_false]; grind
        rw [ha, sumRat_sub, sumRat_const]
        have hb : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 2 else 0) =
            k * ((1 : Rat) / 2) := by
          dsimp [k]
          rw [← sumRat_mul_right]
          apply sumRat_congr
          intro i
          by_cases h : (1 : Rat) / 2 ≤ z i
          · simp only [h, ite_true]; grind
          · simp only [h, ite_false]; grind
        rw [hb]
        grind
      rw [h2] at h1
      exact h1
    have hu_ge : (d : Rat) / 2 ≤ u := by
      have h1 := rat_sub_nonneg_of_le hSnotQ_le
      apply rat_le_of_sub_nonneg
      have heq : u - (d : Rat) / 2 = ((d : Rat) - k) / 2 - SnotQ := by dsimp [u]; grind
      rw [heq]
      exact h1
    -- 4. k ≥ 1 (otherwise every z_i < 1/2 so ∑ z_i < d/2 < d)
    have hex_Q : ∃ i : Fin d, (1 : Rat) / 2 ≤ z i := by
      by_cases hex : ∃ i : Fin d, (1 : Rat) / 2 ≤ z i
      · exact hex
      · exfalso
        have hall : ∀ i : Fin d, z i < (1 : Rat) / 2 := by
          intro i
          exact Rat.not_le.mp (fun h => hex ⟨i, h⟩)
        have hlt : sumRat z < sumRat (fun _ : Fin d => (1 : Rat) / 2) :=
          sumRat_lt_sumRat_of_le_of_lt (fun i => Rat.le_of_lt (hall i))
            ⟨⟨0, hd⟩, hall ⟨0, hd⟩⟩
        rw [hsum, sumRat_const] at hlt
        have hbad : (0 : Rat) < (d : Rat) * ((1 : Rat) / 2) - (d : Rat) := by
          have h1 := Rat.add_lt_add_right (c := -(d : Rat)).mpr hlt
          have e1 : (d : Rat) + -(d : Rat) = 0 := by grind
          have e2 : (d : Rat) * ((1 : Rat) / 2) + -(d : Rat) =
              (d : Rat) * ((1 : Rat) / 2) - (d : Rat) := by grind
          rw [e1, e2] at h1
          exact h1
        have hneg : (d : Rat) * ((1 : Rat) / 2) - (d : Rat) ≤ 0 := by
          have h1 := rat_mul_nonneg (Rat.le_of_lt hd_pos) rat_half_nonneg
          have h2 := rat_neg_le_neg h1
          have e1 : -((d : Rat) * ((1 : Rat) / 2)) = (d : Rat) * ((1 : Rat) / 2) - (d : Rat) := by grind
          have e2 : -(0 : Rat) = 0 := by grind
          rw [e1, e2] at h2
          exact h2
        exact (Rat.not_le.mpr hbad) hneg
    have hk_ge1 : (1 : Rat) ≤ k := by
      obtain ⟨i0, hi0⟩ := hex_Q
      have hge := sumRat_ge_of_point_and_rest
        (fun i => if (1 : Rat) / 2 ≤ z i then (1 : Rat) else 0) i0 1 0
        (by simp only [hi0, ite_true]; exact Rat.le_refl)
        (fun i _ => by
          by_cases h : (1 : Rat) / 2 ≤ z i
          · simp only [h, ite_true]; decide
          · simp only [h, ite_false]; exact Rat.le_refl)
      have heq : (1 : Rat) + ((d : Rat) - 1) * 0 = 1 := by grind
      rw [heq] at hge
      exact hge
    -- 5. SnotQ ≥ 0, hence SQ ≤ d, hence u ≤ d - 1/2
    have hSnotQ_nn : 0 ≤ SnotQ :=
      sumRat_nonneg (fun i => by
        by_cases h : (1 : Rat) / 2 ≤ z i
        · simp only [h, ite_true]; exact Rat.le_refl
        · simp only [h, ite_false]; exact hz i)
    have hu_le : u ≤ (d : Rat) - (1 : Rat) / 2 := by
      apply rat_le_of_sub_nonneg
      have h1 := rat_sub_nonneg_of_le hk_ge1
      have h2 := rat_mul_nonneg rat_half_nonneg h1
      have h3 := rat_add_le_add hSnotQ_nn h2
      have heq : (d : Rat) - (1 : Rat) / 2 - u = SnotQ + ((1 : Rat) / 2) * (k - 1) := by dsimp [u]; grind
      rw [heq]
      have h0 : (0 : Rat) + 0 = 0 := by grind
      rw [h0] at h3
      exact h3
    -- 6. Norm-squared upper bound: ∑ z_i^2 ≤ u^2 + u/2 + d/2
    let y : Fin d → Rat := fun i => if (1 : Rat) / 2 ≤ z i then z i - (1 : Rat) / 2 else 0
    have hy_nn : ∀ i, 0 ≤ y i := fun i => by
      dsimp [y]
      by_cases h : (1 : Rat) / 2 ≤ z i
      · simp only [h, ite_true]; exact rat_sub_nonneg_of_le h
      · simp only [h, ite_false]; exact Rat.le_refl
    have hy_sum : sumRat y = u := by
      have h1 : sumRat y = SQ - sumRat (fun i => if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 2 else 0) := by
        dsimp [y, SQ]
        rw [← sumRat_sub]
        apply sumRat_congr
        intro i
        by_cases h : (1 : Rat) / 2 ≤ z i
        · simp only [h, ite_true]
        · simp only [h, ite_false]; grind
      have h2 : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 2 else 0) = k / 2 := by
        dsimp [k]
        rw [← sumRat_div_right]
        apply sumRat_congr
        intro i
        by_cases h : (1 : Rat) / 2 ≤ z i
        · simp only [h, ite_true]
        · simp only [h, ite_false]; grind
      rw [h1, h2]
    have hnorm_le : sumRat (fun i => z i * z i) ≤ u * u + u / 2 + (d : Rat) / 2 := by
      have hcoord : ∀ i : Fin d,
          z i * z i ≤ y i * y i + y i +
            (if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 4 else ((1 : Rat) / 2) * z i) := by
        intro i
        dsimp [y]
        by_cases h : (1 : Rat) / 2 ≤ z i
        · simp only [h, ite_true]
          have heq : (z i - (1 : Rat) / 2) * (z i - (1 : Rat) / 2) + (z i - (1 : Rat) / 2) +
              (1 : Rat) / 4 = z i * z i := by grind
          rw [heq]
          exact Rat.le_refl
        · simp only [h, ite_false]
          have hlt : z i ≤ (1 : Rat) / 2 := Rat.le_of_lt (Rat.not_le.mp h)
          have hmul := Rat.mul_le_mul_of_nonneg_right hlt (hz i)
          have heq : (0 : Rat) * 0 + 0 + ((1 : Rat) / 2) * z i = ((1 : Rat) / 2) * z i := by grind
          rw [heq]
          exact hmul
      have hsum_le := sumRat_le_sumRat hcoord
      have hsplit_rhs : sumRat (fun i => y i * y i + y i +
          (if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 4 else ((1 : Rat) / 2) * z i)) =
          sumRat (fun i => y i * y i) + sumRat y +
            sumRat (fun i => if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 4 else ((1 : Rat) / 2) * z i) := by
        rw [sumRat_add, sumRat_add]
      rw [hsplit_rhs] at hsum_le
      have hysq : sumRat (fun i => y i * y i) ≤ u * u := by
        rw [← hy_sum]
        exact sumRat_sq_le_sq_sumRat y hy_nn
      have htail : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 4 else ((1 : Rat) / 2) * z i) =
          k / 4 + SnotQ / 2 := by
        have h1 : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 4 else ((1 : Rat) / 2) * z i) =
            sumRat (fun i => (if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 4 else 0) +
              (if (1 : Rat) / 2 ≤ z i then 0 else ((1 : Rat) / 2) * z i)) := by
          apply sumRat_congr
          intro i
          by_cases h : (1 : Rat) / 2 ≤ z i
          · simp only [h, ite_true]; grind
          · simp only [h, ite_false]; grind
        rw [h1, sumRat_add]
        have ha : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then (1 : Rat) / 4 else 0) = k / 4 := by
          dsimp [k]
          rw [← sumRat_div_right]
          apply sumRat_congr
          intro i
          by_cases h : (1 : Rat) / 2 ≤ z i
          · simp only [h, ite_true]
          · simp only [h, ite_false]; grind
        have hb : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 0 else ((1 : Rat) / 2) * z i) = SnotQ / 2 := by
          dsimp [SnotQ]
          rw [← sumRat_div_right]
          apply sumRat_congr
          intro i
          by_cases h : (1 : Rat) / 2 ≤ z i
          · simp only [h, ite_true]; grind
          · simp only [h, ite_false]; grind
        rw [ha, hb]
      rw [hy_sum, htail] at hsum_le
      have hstep : sumRat (fun i => y i * y i) + u + (k / 4 + SnotQ / 2) ≤
          u * u + u + (k / 4 + SnotQ / 2) :=
        Rat.add_le_add_right.mpr (Rat.add_le_add_right.mpr hysq)
      have hcomb := Rat.le_trans hsum_le hstep
      have hcancel : u * u + u + (k / 4 + SnotQ / 2) = u * u + u / 2 + (d : Rat) / 2 := by
        dsimp [u]; grind
      rw [hcancel] at hcomb
      exact hcomb
    -- 7. Final quadratic identity:
    --    2 d^2 u - (2d - 1)(u^2 + u/2 + d/2) = (d - 1/2 - u) * ((2d - 1) * u - d) ≥ 0
    have h2dm1_nn : 0 ≤ 2 * (d : Rat) - 1 := by
      have h1 := rat_sub_nonneg_of_le hd2_rat
      have h2 := rat_mul_nonneg (by decide : (0 : Rat) ≤ 2) h1
      have h3 := rat_add_le_add h2 (by decide : (0 : Rat) ≤ 3)
      have e1 : (0 : Rat) + 0 = 0 := by grind
      have e2 : 2 * ((d : Rat) - 2) + 3 = 2 * (d : Rat) - 1 := by grind
      rw [e1, e2] at h3
      exact h3
    have hmul_norm := Rat.mul_le_mul_of_nonneg_left hnorm_le h2dm1_nn
    have hf1 : 0 ≤ (d : Rat) - (1 : Rat) / 2 - u := rat_sub_nonneg_of_le hu_le
    have hf2 : 0 ≤ (2 * (d : Rat) - 1) * u - (d : Rat) := by
      have h1 := Rat.mul_le_mul_of_nonneg_left hu_ge h2dm1_nn
      have h2 : (d : Rat) ≤ (2 * (d : Rat) - 1) * ((d : Rat) / 2) := by
        apply rat_le_of_sub_nonneg
        have h3 : 0 ≤ 2 * (d : Rat) - 3 := by
          have ha := rat_sub_nonneg_of_le hd2_rat
          have hb := rat_mul_nonneg (by decide : (0 : Rat) ≤ 2) ha
          have hc := rat_add_le_add hb (by decide : (0 : Rat) ≤ 1)
          have e1 : (0 : Rat) + 0 = 0 := by grind
          have e2 : 2 * ((d : Rat) - 2) + 1 = 2 * (d : Rat) - 3 := by grind
          rw [e1, e2] at hc
          exact hc
        have h4 := rat_mul_nonneg (rat_div_nonneg (Rat.le_of_lt hd_pos) (by decide : (0 : Rat) < 2)) h3
        have heq : (2 * (d : Rat) - 1) * ((d : Rat) / 2) - (d : Rat) =
            ((d : Rat) / 2) * (2 * (d : Rat) - 3) := by grind
        rw [heq]
        exact h4
      exact rat_sub_nonneg_of_le (Rat.le_trans h2 h1)
    have hP_nn : 0 ≤ ((d : Rat) - (1 : Rat) / 2 - u) * ((2 * (d : Rat) - 1) * u - (d : Rat)) :=
      rat_mul_nonneg hf1 hf2
    have hP_le : (2 * (d : Rat) - 1) * (u * u + u / 2 + (d : Rat) / 2) ≤
        ((d : Rat) * (d : Rat)) * (2 * u) := by
      apply rat_le_of_sub_nonneg
      have heq : ((d : Rat) * (d : Rat)) * (2 * u) -
          (2 * (d : Rat) - 1) * (u * u + u / 2 + (d : Rat) / 2) =
          ((d : Rat) - (1 : Rat) / 2 - u) * ((2 * (d : Rat) - 1) * u - (d : Rat)) := by grind
      rw [heq]
      exact hP_nn
    rw [hgain_u]
    exact Rat.le_trans hmul_norm hP_le

/-- **Theorem 2 (Exact BitNet b1.58 `AbsMean` Contraction Law):**
    For ALL `d ≥ 1` and EVERY `x : Fin d → Rat` with `normSq x > 0`, letting
    `γ := l1Norm x / (d : Rat)`:
    `ternErrSq γ x ≤ (1 - (2 * d - 1) / (d * d)) * normSq x`,
    with exact attainment on the 1-sparse unit vector `unitE0 d = (1, 0, ..., 0)`. -/
theorem bitnet_absmean_contraction_exact (d : Nat) (hd : 1 ≤ d) :
    (∀ x : Fin d → Rat, 0 < normSq x →
      let γ := l1Norm x / (d : Rat)
      ternErrSq γ x ≤ (1 - (2 * (d : Rat) - 1) / ((d : Rat) * (d : Rat))) * normSq x) ∧
    (0 < normSq (unitE0 d) ∧
      let γ := l1Norm (unitE0 d) / (d : Rat)
      ternErrSq γ (unitE0 d) =
        (1 - (2 * (d : Rat) - 1) / ((d : Rat) * (d : Rat))) * normSq (unitE0 d)) := by
  have hd_pos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hd_ne : (d : Rat) ≠ 0 := (Rat.lt_iff_le_and_ne.mp hd_pos).2.symm
  constructor
  · intro x hpos
    dsimp only
    let γ : Rat := l1Norm x / (d : Rat)
    have hl1_pos : 0 < l1Norm x := l1Norm_pos_of_normSq_pos hpos
    have hγ_pos : 0 < γ := rat_div_pos hl1_pos hd_pos
    have hγ_ne : γ ≠ 0 := (Rat.lt_iff_le_and_ne.mp hγ_pos).2.symm
    let z : Fin d → Rat := fun i => (x i).abs / γ
    have hz_nn : ∀ i, 0 ≤ z i := fun i => rat_div_nonneg (rat_abs_nonneg (x i)) hγ_pos
    have hz_sum : sumRat z = (d : Rat) := by
      dsimp [z]
      rw [sumRat_div_right]
      change l1Norm x / γ = (d : Rat)
      have hl1_ne : l1Norm x ≠ 0 := (Rat.lt_iff_le_and_ne.mp hl1_pos).2.symm
      dsimp [γ]
      grind
    have hcore := absmean_normalized hd z hz_nn hz_sum
    have hγ2_nn : 0 ≤ γ * γ := rat_sq_nonneg γ
    have hscaled := Rat.mul_le_mul_of_nonneg_left hcore hγ2_nn
    have hnorm := normSq_rescaled hγ_pos x
    have hgain := gain_rescaled hγ_pos x
    have h1 : (2 * (d : Rat) - 1) * normSq x ≤
        ((d : Rat) * (d : Rat)) * (normSq x - ternErrSq γ x) := by
      rw [hgain, hnorm]
      have e1 : (2 * (d : Rat) - 1) * (γ * γ * sumRat (fun i => z i * z i)) =
          γ * γ * ((2 * (d : Rat) - 1) * sumRat (fun i => z i * z i)) := by grind
      have e2 : (d : Rat) * (d : Rat) *
          (γ * γ * sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0)) =
          γ * γ * ((d : Rat) * (d : Rat) *
            sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0)) := by grind
      change (2 * (d : Rat) - 1) * (γ * γ * sumRat (fun i => z i * z i)) ≤
        (d : Rat) * (d : Rat) *
          (γ * γ * sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0))
      rw [e1, e2]
      exact hscaled
    have hd2_pos : (0 : Rat) < (d : Rat) * (d : Rat) := rat_mul_pos hd_pos hd_pos
    have hdiv := rat_div_le_div_of_nonneg h1 hd2_pos
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg_of_le hdiv
    have heq : (1 - (2 * (d : Rat) - 1) / ((d : Rat) * (d : Rat))) * normSq x - ternErrSq γ x =
        ((d : Rat) * (d : Rat) * (normSq x - ternErrSq γ x)) / ((d : Rat) * (d : Rat)) -
          ((2 * (d : Rat) - 1) * normSq x) / ((d : Rat) * (d : Rat)) := by grind
    rw [heq]
    exact hsub
  · -- Attainment on unitE0 d = (1, 0, ..., 0)
    have hnorm_e0 : normSq (unitE0 d) = 1 := by
      unfold normSq unitE0
      have h1 : sumRat (fun i : Fin d => (if i.val = 0 then (1 : Rat) else 0) *
          (if i.val = 0 then (1 : Rat) else 0)) =
          sumRat (fun i : Fin d => if i.val = 0 then (1 : Rat) else 0) := by
        apply sumRat_congr
        intro i
        by_cases h : i.val = 0
        · simp only [h, ite_true]; grind
        · simp only [h, ite_false]; grind
      rw [h1, sumRat_zero_override hd 1 0]
      grind
    have hl1_e0 : l1Norm (unitE0 d) = 1 := by
      unfold l1Norm unitE0
      have h1 : sumRat (fun i : Fin d => (if i.val = 0 then (1 : Rat) else 0).abs) =
          sumRat (fun i : Fin d => if i.val = 0 then (1 : Rat) else 0) := by
        apply sumRat_congr
        intro i
        by_cases h : i.val = 0
        · simp only [h, ite_true]; decide
        · simp only [h, ite_false]; decide
      rw [h1, sumRat_zero_override hd 1 0]
      grind
    refine ⟨by rw [hnorm_e0]; decide, ?_⟩
    dsimp only
    rw [hl1_e0, hnorm_e0]
    let γ : Rat := (1 : Rat) / (d : Rat)
    have hγ_pos : 0 < γ := rat_div_pos (by decide : (0 : Rat) < 1) hd_pos
    have hhalf_pos : 0 < γ / 2 := rat_div_pos hγ_pos (by decide : (0 : Rat) < 2)
    have hhalf_le1 : γ / 2 ≤ 1 := by
      have hd1 : (1 : Rat) ≤ (d : Rat) := rat_natCast_le hd
      have h2d : (1 : Rat) ≤ 2 * (d : Rat) := by
        have h1 := rat_mul_nonneg (by decide : (0 : Rat) ≤ 2) (rat_sub_nonneg_of_le hd1)
        apply rat_le_of_sub_nonneg
        have h2 := rat_add_le_add h1 (by decide : (0 : Rat) ≤ 1)
        have e1 : (0 : Rat) + 0 = 0 := by grind
        have e2 : 2 * ((d : Rat) - 1) + 1 = 2 * (d : Rat) - 1 := by grind
        rw [e1, e2] at h2
        exact h2
      have h2d_pos : (0 : Rat) < 2 * (d : Rat) := rat_mul_pos (by decide) hd_pos
      have hdiv := rat_div_le_div_of_nonneg h2d h2d_pos
      have e1 : (1 : Rat) / (2 * (d : Rat)) = γ / 2 := by dsimp [γ]; grind
      have e2 : (2 * (d : Rat)) / (2 * (d : Rat)) = 1 := by grind
      rw [e1, e2] at hdiv
      exact hdiv
    have hnot_le0 : ¬ (γ / 2 ≤ 0) := Rat.not_le.mpr hhalf_pos
    have hnot_ge0 : ¬ ((0 : Rat) ≤ -(γ / 2)) := by
      apply Rat.not_le.mpr
      have h1 := Rat.add_lt_add_right (c := -(γ / 2)).mpr hhalf_pos
      have e1 : (0 : Rat) + -(γ / 2) = -(γ / 2) := by grind
      have e2 : γ / 2 + -(γ / 2) = 0 := by grind
      rw [e1, e2] at h1
      exact h1
    have herr_e0 : ternErrSq γ (unitE0 d) = (1 - γ) * (1 - γ) := by
      unfold ternErrSq unitE0
      have h1 : sumRat (fun i : Fin d =>
          ((if i.val = 0 then (1 : Rat) else 0) -
            ternRound γ (if i.val = 0 then (1 : Rat) else 0)) *
          ((if i.val = 0 then (1 : Rat) else 0) -
            ternRound γ (if i.val = 0 then (1 : Rat) else 0))) =
          sumRat (fun i : Fin d => if i.val = 0 then (1 - γ) * (1 - γ) else 0) := by
        apply sumRat_congr
        intro i
        by_cases h : i.val = 0
        · simp only [h, ite_true, ternRound, hhalf_le1]
        · simp only [h, ite_false, ternRound, hnot_le0, hnot_ge0]
          grind
      rw [h1, sumRat_zero_override hd ((1 - γ) * (1 - γ)) 0]
      grind
    change ternErrSq γ (unitE0 d) = (1 - (2 * (d : Rat) - 1) / ((d : Rat) * (d : Rat))) * 1
    rw [herr_e0]
    dsimp [γ]
    grind

/-! ## Theorem 3: Exact `AbsMax` (`4/(d+3)`) and `AbsMax/2` (`12/(d+15)`) Contraction Laws -/

/-- **Theorem 3 (Exact `AbsMax` and `AbsMax/2` Contraction Laws):**
    For ALL `d ≥ 1`, `M > 0`, and EVERY `x : Fin d → Rat` with `max_i |x_i| = M`:
    1. `AbsMax` (`γ = M`): `ternErrSq M x ≤ (1 - 4 / (d + 3)) * normSq x`,
       attained with exact equality at `absMaxWitness d = (1, 1/2, ..., 1/2)` (`M = 1`).
    2. `AbsMax/2` (`γ = M / 2`): `ternErrSq (M / 2) x ≤ (1 - 12 / (d + 15)) * normSq x`,
       attained with exact equality at `absMaxHalfWitness d = (1, 1/4, ..., 1/4)` (`M = 1`). -/
theorem bitnet_absmax_and_half_contraction_exact (d : Nat) (hd : 1 ≤ d) :
    (∀ (M : Rat), 0 < M → ∀ (x : Fin d → Rat),
      (∀ i, (x i).abs ≤ M) → (∃ i, (x i).abs = M) →
      ternErrSq M x ≤ (1 - 4 / ((d : Rat) + 3)) * normSq x) ∧
    ((∀ i, (absMaxWitness d i).abs ≤ 1) ∧ (∃ i, (absMaxWitness d i).abs = 1) ∧
      ternErrSq 1 (absMaxWitness d) = (1 - 4 / ((d : Rat) + 3)) * normSq (absMaxWitness d)) ∧
    (∀ (M : Rat), 0 < M → ∀ (x : Fin d → Rat),
      (∀ i, (x i).abs ≤ M) → (∃ i, (x i).abs = M) →
      ternErrSq (M / 2) x ≤ (1 - 12 / ((d : Rat) + 15)) * normSq x) ∧
    ((∀ i, (absMaxHalfWitness d i).abs ≤ 1) ∧ (∃ i, (absMaxHalfWitness d i).abs = 1) ∧
      ternErrSq ((1 : Rat) / 2) (absMaxHalfWitness d) =
        (1 - 12 / ((d : Rat) + 15)) * normSq (absMaxHalfWitness d)) := by
  have hd_pos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hd3_pos : (0 : Rat) < (d : Rat) + 3 := by
    have h := rat_add_lt_add_of_lt_of_le hd_pos (by decide : (0 : Rat) ≤ 3)
    have e : (0 : Rat) + 0 = 0 := by grind
    rw [e] at h; exact h
  have hd15_pos : (0 : Rat) < (d : Rat) + 15 := by
    have h := rat_add_lt_add_of_lt_of_le hd_pos (by decide : (0 : Rat) ≤ 15)
    have e : (0 : Rat) + 0 = 0 := by grind
    rw [e] at h; exact h
  have hd3_ne : (d : Rat) + 3 ≠ 0 := (Rat.lt_iff_le_and_ne.mp hd3_pos).2.symm
  have hd15_ne : (d : Rat) + 15 ≠ 0 := (Rat.lt_iff_le_and_ne.mp hd15_pos).2.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part 1: Universal AbsMax bound
    intro M hM x hle ⟨i0, hi0⟩
    have hM_ne : M ≠ 0 := (Rat.lt_iff_le_and_ne.mp hM).2.symm
    let z : Fin d → Rat := fun i => (x i).abs / M
    have hz_nn : ∀ i, 0 ≤ z i := fun i => rat_div_nonneg (rat_abs_nonneg (x i)) hM
    have hz_le1 : ∀ i, z i ≤ 1 := fun i => by
      have h1 := rat_div_le_div_of_nonneg (hle i) hM
      have h2 : M / M = 1 := by grind
      rw [h2] at h1
      exact h1
    have hz_i0 : z i0 = 1 := by dsimp [z]; rw [hi0]; grind
    let g : Fin d → Rat := fun i =>
      ((d : Rat) + 3) * (if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0) - 4 * (z i * z i)
    have hg_i0 : (d : Rat) - 1 ≤ g i0 := by
      dsimp [g]
      rw [hz_i0]
      simp only [rat_half_le_one, ite_true]
      have heq : ((d : Rat) + 3) * (2 * 1 - 1) - 4 * (1 * 1) = (d : Rat) - 1 := by grind
      rw [heq]
      exact Rat.le_refl
    have hg_rest : ∀ i, i ≠ i0 → (-1 : Rat) ≤ g i := by
      intro i _
      dsimp [g]
      apply rat_le_of_sub_nonneg
      by_cases h : (1 : Rat) / 2 ≤ z i
      · simp only [h, ite_true]
        have hf1 : 0 ≤ 2 * z i - 1 := by
          have h1 := rat_mul_nonneg (by decide : (0 : Rat) ≤ 2) (rat_sub_nonneg_of_le h)
          have heq : 2 * (z i - (1 : Rat) / 2) = 2 * z i - 1 := by grind
          rw [heq] at h1
          exact h1
        have hf2 : 0 ≤ (d : Rat) + 2 - 2 * z i := by
          have h1 := rat_sub_nonneg_of_le (hz_le1 i)
          have h2 := rat_mul_nonneg (by decide : (0 : Rat) ≤ 2) h1
          have h3 := rat_add_le_add (Rat.le_of_lt hd_pos) h2
          have e1 : (0 : Rat) + 0 = 0 := by grind
          have e2 : (d : Rat) + 2 * (1 - z i) = (d : Rat) + 2 - 2 * z i := by grind
          rw [e1, e2] at h3
          exact h3
        have hmul := rat_mul_nonneg hf1 hf2
        have heq : ((d : Rat) + 3) * (2 * z i - 1) - 4 * (z i * z i) - (-1) =
            (2 * z i - 1) * ((d : Rat) + 2 - 2 * z i) := by grind
        rw [heq]
        exact hmul
      · simp only [h, ite_false]
        have hlt : z i ≤ (1 : Rat) / 2 := Rat.le_of_lt (Rat.not_le.mp h)
        have hsq := rat_mul_le_mul_of_nonneg (hz_nn i) (hz_nn i) hlt hlt
        have h4 := Rat.mul_le_mul_of_nonneg_left hsq (by decide : (0 : Rat) ≤ 4)
        have hsub := rat_sub_nonneg_of_le h4
        have heq : ((d : Rat) + 3) * 0 - 4 * (z i * z i) - (-1) =
            4 * (((1 : Rat) / 2) * ((1 : Rat) / 2)) - 4 * (z i * z i) := by grind
        rw [heq]
        exact hsub
    have hsum_g := sumRat_ge_of_point_and_rest g i0 ((d : Rat) - 1) (-1) hg_i0 hg_rest
    have hzero : ((d : Rat) - 1) + ((d : Rat) - 1) * (-1) = 0 := by grind
    rw [hzero] at hsum_g
    have hsum_eq : sumRat g =
        ((d : Rat) + 3) * sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0) -
          4 * sumRat (fun i => z i * z i) := by
      dsimp [g]
      rw [sumRat_sub, sumRat_mul_left, sumRat_mul_left]
    rw [hsum_eq] at hsum_g
    have hcore := rat_le_of_sub_nonneg hsum_g
    have hscaled := Rat.mul_le_mul_of_nonneg_left hcore (rat_sq_nonneg M)
    have hnorm := normSq_rescaled hM x
    have hgain := gain_rescaled hM x
    have h1 : 4 * normSq x ≤ ((d : Rat) + 3) * (normSq x - ternErrSq M x) := by
      rw [hgain, hnorm]
      have e1 : 4 * (M * M * sumRat (fun i => z i * z i)) =
          M * M * (4 * sumRat (fun i => z i * z i)) := by grind
      have e2 : ((d : Rat) + 3) *
          (M * M * sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0)) =
          M * M * (((d : Rat) + 3) *
            sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0)) := by grind
      change 4 * (M * M * sumRat (fun i => z i * z i)) ≤
        ((d : Rat) + 3) * (M * M * sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0))
      rw [e1, e2]
      exact hscaled
    have hdiv := rat_div_le_div_of_nonneg h1 hd3_pos
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg_of_le hdiv
    have heq : (1 - 4 / ((d : Rat) + 3)) * normSq x - ternErrSq M x =
        (((d : Rat) + 3) * (normSq x - ternErrSq M x)) / ((d : Rat) + 3) -
          (4 * normSq x) / ((d : Rat) + 3) := by grind
    rw [heq]
    exact hsub
  · -- Part 2: Exact AbsMax attainment on absMaxWitness d = (1, 1/2, ..., 1/2)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      unfold absMaxWitness
      by_cases h : i.val = 0
      · simp only [h, ite_true]
        rw [rat_abs_eq_of_nonneg (by decide : (0 : Rat) ≤ 1)]
        exact Rat.le_refl
      · simp only [h, ite_false]
        rw [rat_abs_eq_of_nonneg rat_half_nonneg]
        exact rat_half_le_one
    · refine ⟨⟨0, hd⟩, ?_⟩
      unfold absMaxWitness
      simp only [ite_true]
      exact rat_abs_eq_of_nonneg (by decide : (0 : Rat) ≤ 1)
    · have hnorm_w : normSq (absMaxWitness d) = ((d : Rat) + 3) / 4 := by
        unfold normSq absMaxWitness
        have h1 : sumRat (fun i : Fin d =>
            (if i.val = 0 then (1 : Rat) else (1 : Rat) / 2) *
            (if i.val = 0 then (1 : Rat) else (1 : Rat) / 2)) =
            sumRat (fun i : Fin d => if i.val = 0 then (1 : Rat) else (1 : Rat) / 4) := by
          apply sumRat_congr
          intro i
          by_cases h : i.val = 0
          · simp only [h, ite_true]; grind
          · simp only [h, ite_false]; grind
        rw [h1, sumRat_zero_override hd 1 ((1 : Rat) / 4)]
        grind
      have herr_w : ternErrSq 1 (absMaxWitness d) = ((d : Rat) - 1) / 4 := by
        unfold ternErrSq absMaxWitness
        have h1 : sumRat (fun i : Fin d =>
            ((if i.val = 0 then (1 : Rat) else (1 : Rat) / 2) -
              ternRound 1 (if i.val = 0 then (1 : Rat) else (1 : Rat) / 2)) *
            ((if i.val = 0 then (1 : Rat) else (1 : Rat) / 2) -
              ternRound 1 (if i.val = 0 then (1 : Rat) else (1 : Rat) / 2))) =
            sumRat (fun i : Fin d => if i.val = 0 then (0 : Rat) else (1 : Rat) / 4) := by
          apply sumRat_congr
          intro i
          by_cases h : i.val = 0
          · simp only [h, ite_true, ternRound, rat_half_le_one]; grind
          · have hr : (1 : Rat) / 2 ≤ (1 : Rat) / 2 := Rat.le_refl
            simp only [h, ite_false, ternRound, hr, ite_true]; grind
        rw [h1, sumRat_zero_override hd 0 ((1 : Rat) / 4)]
        grind
      rw [hnorm_w, herr_w]
      grind
  · -- Part 3: Universal AbsMax/2 bound
    intro M hM x hle ⟨i0, hi0⟩
    have hM_ne : M ≠ 0 := (Rat.lt_iff_le_and_ne.mp hM).2.symm
    have hM2_pos : 0 < M / 2 := rat_div_pos hM (by decide : (0 : Rat) < 2)
    let z : Fin d → Rat := fun i => (x i).abs / M
    have hz_nn : ∀ i, 0 ≤ z i := fun i => rat_div_nonneg (rat_abs_nonneg (x i)) hM
    have hz_le1 : ∀ i, z i ≤ 1 := fun i => by
      have h1 := rat_div_le_div_of_nonneg (hle i) hM
      have h2 : M / M = 1 := by grind
      rw [h2] at h1
      exact h1
    have hz_i0 : z i0 = 1 := by dsimp [z]; rw [hi0]; grind
    let hfun : Fin d → Rat := fun i =>
      ((d : Rat) + 15) * (if (1 : Rat) / 4 ≤ z i then 4 * z i - 1 else 0) - 48 * (z i * z i)
    have hh_i0 : 3 * ((d : Rat) - 1) ≤ hfun i0 := by
      dsimp [hfun]
      rw [hz_i0]
      simp only [rat_quarter_le_one, ite_true]
      have heq : ((d : Rat) + 15) * (4 * 1 - 1) - 48 * (1 * 1) = 3 * ((d : Rat) - 1) := by grind
      rw [heq]
      exact Rat.le_refl
    have hh_rest : ∀ i, i ≠ i0 → (-3 : Rat) ≤ hfun i := by
      intro i _
      dsimp [hfun]
      apply rat_le_of_sub_nonneg
      by_cases h : (1 : Rat) / 4 ≤ z i
      · simp only [h, ite_true]
        have hf1 : 0 ≤ 4 * z i - 1 := by
          have h1 := rat_mul_nonneg (by decide : (0 : Rat) ≤ 4) (rat_sub_nonneg_of_le h)
          have heq : 4 * (z i - (1 : Rat) / 4) = 4 * z i - 1 := by grind
          rw [heq] at h1
          exact h1
        have hf2 : 0 ≤ (d : Rat) + 12 - 12 * z i := by
          have h1 := rat_sub_nonneg_of_le (hz_le1 i)
          have h2 := rat_mul_nonneg (by decide : (0 : Rat) ≤ 12) h1
          have h3 := rat_add_le_add (Rat.le_of_lt hd_pos) h2
          have e1 : (0 : Rat) + 0 = 0 := by grind
          have e2 : (d : Rat) + 12 * (1 - z i) = (d : Rat) + 12 - 12 * z i := by grind
          rw [e1, e2] at h3
          exact h3
        have hmul := rat_mul_nonneg hf1 hf2
        have heq : ((d : Rat) + 15) * (4 * z i - 1) - 48 * (z i * z i) - (-3) =
            (4 * z i - 1) * ((d : Rat) + 12 - 12 * z i) := by grind
        rw [heq]
        exact hmul
      · simp only [h, ite_false]
        have hlt : z i ≤ (1 : Rat) / 4 := Rat.le_of_lt (Rat.not_le.mp h)
        have hsq := rat_mul_le_mul_of_nonneg (hz_nn i) (hz_nn i) hlt hlt
        have h48 := Rat.mul_le_mul_of_nonneg_left hsq (by decide : (0 : Rat) ≤ 48)
        have hsub := rat_sub_nonneg_of_le h48
        have heq : ((d : Rat) + 15) * 0 - 48 * (z i * z i) - (-3) =
            48 * (((1 : Rat) / 4) * ((1 : Rat) / 4)) - 48 * (z i * z i) := by grind
        rw [heq]
        exact hsub
    have hsum_h := sumRat_ge_of_point_and_rest hfun i0 (3 * ((d : Rat) - 1)) (-3) hh_i0 hh_rest
    have hzero : 3 * ((d : Rat) - 1) + ((d : Rat) - 1) * (-3) = 0 := by grind
    rw [hzero] at hsum_h
    have hsum_eq : sumRat hfun =
        ((d : Rat) + 15) * sumRat (fun i => if (1 : Rat) / 4 ≤ z i then 4 * z i - 1 else 0) -
          48 * sumRat (fun i => z i * z i) := by
      dsimp [hfun]
      rw [sumRat_sub, sumRat_mul_left, sumRat_mul_left]
    rw [hsum_eq] at hsum_h
    have hcore := rat_le_of_sub_nonneg hsum_h
    have hgain_m2 : normSq x - ternErrSq (M / 2) x =
        (M * M / 4) * sumRat (fun i => if (1 : Rat) / 4 ≤ z i then 4 * z i - 1 else 0) := by
      rw [gain_rescaled hM2_pos x]
      have h1 : sumRat (fun i =>
          if (1 : Rat) / 2 ≤ (x i).abs / (M / 2) then 2 * ((x i).abs / (M / 2)) - 1 else 0) =
          sumRat (fun i => if (1 : Rat) / 4 ≤ z i then 4 * z i - 1 else 0) := by
        apply sumRat_congr
        intro i
        have h2z : (x i).abs / (M / 2) = 2 * z i := by dsimp [z]; grind
        rw [h2z]
        have hiff : ((1 : Rat) / 2 ≤ 2 * z i) ↔ ((1 : Rat) / 4 ≤ z i) := by
          constructor
          · intro h
            have h1 := rat_div_le_div_of_nonneg h (by decide : (0 : Rat) < 2)
            have e1 : ((1 : Rat) / 2) / 2 = (1 : Rat) / 4 := by grind
            have e2 : (2 * z i) / 2 = z i := by grind
            rw [e1, e2] at h1
            exact h1
          · intro h
            have h1 := Rat.mul_le_mul_of_nonneg_left h (by decide : (0 : Rat) ≤ 2)
            have e1 : (2 : Rat) * ((1 : Rat) / 4) = (1 : Rat) / 2 := by grind
            rw [e1] at h1
            exact h1
        by_cases hc : (1 : Rat) / 4 ≤ z i
        · have hl : (1 : Rat) / 2 ≤ 2 * z i := hiff.mpr hc
          simp only [hl, hc, ite_true]; grind
        · have hl : ¬ ((1 : Rat) / 2 ≤ 2 * z i) := fun h => hc (hiff.mp h)
          simp only [hl, hc, ite_false]
      rw [h1]
      grind
    have hscaled := Rat.mul_le_mul_of_nonneg_left hcore
      (rat_div_nonneg (rat_sq_nonneg M) (by decide : (0 : Rat) < 4))
    have hnorm := normSq_rescaled hM x
    have h1 : 12 * normSq x ≤ ((d : Rat) + 15) * (normSq x - ternErrSq (M / 2) x) := by
      rw [hgain_m2, hnorm]
      have e1 : 12 * (M * M * sumRat (fun i => z i * z i)) =
          (M * M / 4) * (48 * sumRat (fun i => z i * z i)) := by grind
      have e2 : ((d : Rat) + 15) *
          ((M * M / 4) * sumRat (fun i => if (1 : Rat) / 4 ≤ z i then 4 * z i - 1 else 0)) =
          (M * M / 4) * (((d : Rat) + 15) *
            sumRat (fun i => if (1 : Rat) / 4 ≤ z i then 4 * z i - 1 else 0)) := by grind
      change 12 * (M * M * sumRat (fun i => z i * z i)) ≤
        ((d : Rat) + 15) * ((M * M / 4) * sumRat (fun i => if (1 : Rat) / 4 ≤ z i then 4 * z i - 1 else 0))
      rw [e1, e2]
      exact hscaled
    have hdiv := rat_div_le_div_of_nonneg h1 hd15_pos
    apply rat_le_of_sub_nonneg
    have hsub := rat_sub_nonneg_of_le hdiv
    have heq : (1 - 12 / ((d : Rat) + 15)) * normSq x - ternErrSq (M / 2) x =
        (((d : Rat) + 15) * (normSq x - ternErrSq (M / 2) x)) / ((d : Rat) + 15) -
          (12 * normSq x) / ((d : Rat) + 15) := by grind
    rw [heq]
    exact hsub
  · -- Part 4: Exact AbsMax/2 attainment on absMaxHalfWitness d = (1, 1/4, ..., 1/4)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      unfold absMaxHalfWitness
      by_cases h : i.val = 0
      · simp only [h, ite_true]
        rw [rat_abs_eq_of_nonneg (by decide : (0 : Rat) ≤ 1)]
        exact Rat.le_refl
      · simp only [h, ite_false]
        rw [rat_abs_eq_of_nonneg rat_quarter_nonneg]
        exact rat_quarter_le_one
    · refine ⟨⟨0, hd⟩, ?_⟩
      unfold absMaxHalfWitness
      simp only [ite_true]
      exact rat_abs_eq_of_nonneg (by decide : (0 : Rat) ≤ 1)
    · have hnorm_w : normSq (absMaxHalfWitness d) = ((d : Rat) + 15) / 16 := by
        unfold normSq absMaxHalfWitness
        have h1 : sumRat (fun i : Fin d =>
            (if i.val = 0 then (1 : Rat) else (1 : Rat) / 4) *
            (if i.val = 0 then (1 : Rat) else (1 : Rat) / 4)) =
            sumRat (fun i : Fin d => if i.val = 0 then (1 : Rat) else (1 : Rat) / 16) := by
          apply sumRat_congr
          intro i
          by_cases h : i.val = 0
          · simp only [h, ite_true]; grind
          · simp only [h, ite_false]; grind
        rw [h1, sumRat_zero_override hd 1 ((1 : Rat) / 16)]
        grind
      have herr_w : ternErrSq ((1 : Rat) / 2) (absMaxHalfWitness d) = ((d : Rat) + 3) / 16 := by
        unfold ternErrSq absMaxHalfWitness
        have hq_eq : ((1 : Rat) / 2) / 2 = (1 : Rat) / 4 := by grind
        have h1 : sumRat (fun i : Fin d =>
            ((if i.val = 0 then (1 : Rat) else (1 : Rat) / 4) -
              ternRound ((1 : Rat) / 2) (if i.val = 0 then (1 : Rat) else (1 : Rat) / 4)) *
            ((if i.val = 0 then (1 : Rat) else (1 : Rat) / 4) -
              ternRound ((1 : Rat) / 2) (if i.val = 0 then (1 : Rat) else (1 : Rat) / 4))) =
            sumRat (fun i : Fin d => if i.val = 0 then (1 : Rat) / 4 else (1 : Rat) / 16) := by
          apply sumRat_congr
          intro i
          by_cases h : i.val = 0
          · simp only [h, ite_true, ternRound, hq_eq, rat_quarter_le_one]; grind
          · have hr : (1 : Rat) / 4 ≤ (1 : Rat) / 4 := Rat.le_refl
            simp only [h, ite_false, ternRound, hq_eq, hr, ite_true]; grind
        rw [h1, sumRat_zero_override hd ((1 : Rat) / 4) ((1 : Rat) / 16)]
        grind
      rw [hnorm_w, herr_w]
      grind

/-! ## Theorem 4: Exact Algebraic `RMS` Contraction Law `(d * α + 1)^2 ≥ 3 d + 1` -/

/-- Exact rational attainment of the `RMS` lower bound whenever `s^2 = 3 d + 1` (`d ≥ 1`). -/
theorem rms_witness_exact (d s : Nat) (hd : 1 ≤ d) (hs : s * s = 3 * d + 1) :
    (d : Rat) * ((1 : Rat) * 1) = normSq (rmsWitness d s) ∧
    ternAlpha 1 (rmsWitness d s) = ((s : Rat) - 1) / (d : Rat) ∧
    ((d : Rat) * ternAlpha 1 (rmsWitness d s) + 1) *
      ((d : Rat) * ternAlpha 1 (rmsWitness d s) + 1) = 3 * (d : Rat) + 1 := by
  have hd_pos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hd_ne : (d : Rat) ≠ 0 := (Rat.lt_iff_le_and_ne.mp hd_pos).2.symm
  have hs_ge2 : 2 ≤ s := by
    cases s with
    | zero => simp at hs
    | succ k =>
      cases k with
      | zero => simp at hs; omega
      | succ _ => omega
  have hs_rat : (s : Rat) * (s : Rat) = 3 * (d : Rat) + 1 := by
    have hcast : ((s * s : Nat) : Rat) = ((3 * d + 1 : Nat) : Rat) :=
      congrArg (fun n : Nat => (n : Rat)) hs
    grind
  have hnorm : normSq (rmsWitness d s) = (d : Rat) := by
    unfold normSq rmsWitness
    have h1 : sumRat (fun i : Fin d =>
        (if i.val = 0 then (s : Rat) / 2 else (1 : Rat) / 2) *
        (if i.val = 0 then (s : Rat) / 2 else (1 : Rat) / 2)) =
        sumRat (fun i : Fin d => if i.val = 0 then ((s : Rat) * (s : Rat)) / 4 else (1 : Rat) / 4) := by
      apply sumRat_congr
      intro i
      by_cases h : i.val = 0
      · simp only [h, ite_true]; grind
      · simp only [h, ite_false]; grind
    rw [h1, sumRat_zero_override hd (((s : Rat) * (s : Rat)) / 4) ((1 : Rat) / 4)]
    grind
  have hs2_ge : (1 : Rat) / 2 ≤ (s : Rat) / 2 := by
    have hle : ((1 : Nat) : Rat) ≤ (s : Rat) := rat_natCast_le (by omega)
    have h1 : ((1 : Nat) : Rat) = 1 := by grind
    rw [h1] at hle
    exact rat_div_le_div_of_nonneg hle (by decide : (0 : Rat) < 2)
  have herr : ternErrSq 1 (rmsWitness d s) = (d : Rat) - ((s : Rat) - 1) := by
    unfold ternErrSq rmsWitness
    have h1 : sumRat (fun i : Fin d =>
        ((if i.val = 0 then (s : Rat) / 2 else (1 : Rat) / 2) -
          ternRound 1 (if i.val = 0 then (s : Rat) / 2 else (1 : Rat) / 2)) *
        ((if i.val = 0 then (s : Rat) / 2 else (1 : Rat) / 2) -
          ternRound 1 (if i.val = 0 then (s : Rat) / 2 else (1 : Rat) / 2))) =
        sumRat (fun i : Fin d =>
          if i.val = 0 then ((s : Rat) / 2 - 1) * ((s : Rat) / 2 - 1) else (1 : Rat) / 4) := by
      apply sumRat_congr
      intro i
      by_cases h : i.val = 0
      · simp only [h, ite_true, ternRound, hs2_ge]
      · have hr : (1 : Rat) / 2 ≤ (1 : Rat) / 2 := Rat.le_refl
        simp only [h, ite_false, ternRound, hr, ite_true]; grind
    rw [h1, sumRat_zero_override hd (((s : Rat) / 2 - 1) * ((s : Rat) / 2 - 1)) ((1 : Rat) / 4)]
    grind
  have halpha : ternAlpha 1 (rmsWitness d s) = ((s : Rat) - 1) / (d : Rat) := by
    unfold ternAlpha
    rw [herr, hnorm]
    grind
  refine ⟨by rw [hnorm]; grind, halpha, ?_⟩
  rw [halpha]
  grind

/-- **Theorem 4 (Exact Algebraic `RMS` Contraction Law):**
    For ALL `d ≥ 1`, EVERY `x : Fin d → Rat`, and EVERY `γ > 0` with `d * γ^2 = normSq x`,
    letting `α := ternAlpha γ x`:
    `3 * (d : Rat) + 1 ≤ ((d : Rat) * α + 1) * ((d : Rat) * α + 1)`,
    attained with exact rational equality at `d = 8` (`α = 1/2`, `rmsWitness 8 5`) and
    `d = 16` (`α = 3/8`, `rmsWitness 16 7`). -/
theorem bitnet_rms_contraction_exact_algebraic (d : Nat) (hd : 1 ≤ d) :
    (∀ (x : Fin d → Rat) (γ : Rat), 0 < γ → (d : Rat) * (γ * γ) = normSq x →
      let α := ternAlpha γ x
      3 * (d : Rat) + 1 ≤ ((d : Rat) * α + 1) * ((d : Rat) * α + 1)) ∧
    ((8 : Rat) * ((1 : Rat) * 1) = normSq (rmsWitness 8 5) ∧
      ternAlpha 1 (rmsWitness 8 5) = (1 : Rat) / 2) ∧
    ((16 : Rat) * ((1 : Rat) * 1) = normSq (rmsWitness 16 7) ∧
      ternAlpha 1 (rmsWitness 16 7) = (3 : Rat) / 8) := by
  have hd_pos : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hd_ne : (d : Rat) ≠ 0 := (Rat.lt_iff_le_and_ne.mp hd_pos).2.symm
  refine ⟨?_, ?_, ?_⟩
  · intro x γ hγ hrms
    dsimp only
    have hγ_ne : γ ≠ 0 := (Rat.lt_iff_le_and_ne.mp hγ).2.symm
    let z : Fin d → Rat := fun i => (x i).abs / γ
    have hz_nn : ∀ i, 0 ≤ z i := fun i => rat_div_nonneg (rat_abs_nonneg (x i)) hγ
    have hz_norm : sumRat (fun i => z i * z i) = (d : Rat) := by
      have hnorm := normSq_rescaled hγ x
      rw [← hrms] at hnorm
      have hγ2_ne : γ * γ ≠ 0 := by grind
      grind
    let y : Fin d → Rat := fun i => if (1 : Rat) / 2 ≤ z i then z i - (1 : Rat) / 2 else 0
    have hy_nn : ∀ i, 0 ≤ y i := fun i => by
      dsimp [y]
      by_cases h : (1 : Rat) / 2 ≤ z i
      · simp only [h, ite_true]; exact rat_sub_nonneg_of_le h
      · simp only [h, ite_false]; exact Rat.le_refl
    let Y : Rat := sumRat y
    -- 1. d * α = 2 * Y
    have hda : (d : Rat) * ternAlpha γ x = 2 * Y := by
      unfold ternAlpha
      have hgain := gain_rescaled hγ x
      have h2Y : sumRat (fun i => if (1 : Rat) / 2 ≤ z i then 2 * z i - 1 else 0) = 2 * Y := by
        dsimp [Y, y]
        rw [← sumRat_mul_left]
        apply sumRat_congr
        intro i
        by_cases h : (1 : Rat) / 2 ≤ z i
        · simp only [h, ite_true]; grind
        · simp only [h, ite_false]; grind
      rw [h2Y] at hgain
      have hnorm_ne : normSq x ≠ 0 := by rw [← hrms]; grind
      grind
    -- 2. Coordinate-wise: z_i^2 ≤ y_i^2 + y_i + 1/4
    have hcoord : ∀ i : Fin d, z i * z i ≤ y i * y i + y i + (1 : Rat) / 4 := by
      intro i
      dsimp [y]
      by_cases h : (1 : Rat) / 2 ≤ z i
      · simp only [h, ite_true]
        have heq : (z i - (1 : Rat) / 2) * (z i - (1 : Rat) / 2) + (z i - (1 : Rat) / 2) +
            (1 : Rat) / 4 = z i * z i := by grind
        rw [heq]
        exact Rat.le_refl
      · simp only [h, ite_false]
        have hlt : z i ≤ (1 : Rat) / 2 := Rat.le_of_lt (Rat.not_le.mp h)
        have hsq := rat_mul_le_mul_of_nonneg (hz_nn i) (hz_nn i) hlt hlt
        have heq : (0 : Rat) * 0 + 0 + (1 : Rat) / 4 = ((1 : Rat) / 2) * ((1 : Rat) / 2) := by grind
        rw [heq]
        exact hsq
    have hsum := sumRat_le_sumRat hcoord
    rw [hz_norm, sumRat_add, sumRat_add, sumRat_const] at hsum
    have hysq : sumRat (fun i => y i * y i) ≤ Y * Y := sumRat_sq_le_sq_sumRat y hy_nn
    have hd_le : (d : Rat) ≤ Y * Y + Y + (d : Rat) * ((1 : Rat) / 4) :=
      Rat.le_trans hsum (Rat.add_le_add_right.mpr (Rat.add_le_add_right.mpr hysq))
    rw [hda]
    apply rat_le_of_sub_nonneg
    have h4 := Rat.mul_le_mul_of_nonneg_left (rat_sub_nonneg_of_le hd_le) (by decide : (0 : Rat) ≤ 4)
    have heq : (2 * Y + 1) * (2 * Y + 1) - (3 * (d : Rat) + 1) =
        4 * (Y * Y + Y + (d : Rat) * ((1 : Rat) / 4) - (d : Rat)) := by grind
    have h0 : (4 : Rat) * 0 = 0 := by grind
    rw [h0] at h4
    rw [heq]
    exact h4
  · have h8 := rms_witness_exact 8 5 (by decide) (by decide)
    exact ⟨h8.1, by rw [h8.2.1]; grind⟩
  · have h16 := rms_witness_exact 16 7 (by decide) (by decide)
    exact ⟨h16.1, by rw [h16.2.1]; grind⟩

end BitnetContraction
