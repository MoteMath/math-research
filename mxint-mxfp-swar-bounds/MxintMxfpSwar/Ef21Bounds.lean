/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxintMxfpSwar.RatOrder

/-!
# Theorems 1 & 2: Universal All-`B` `MXINT_w` EF21 Contraction & Exact `MXINT_w` vs `MXFP_w` Crossover

Proves:
1. `mxint_all_b_ef21_contraction_exact`: Universal all-`B` (`B ≥ 1, w ≥ 2`) worst-case EF21
   bounds with tight attainment for symmetric `MXINT_w` under Continuous AbsMax and OCP `E8M0`.
2. `mxint_vs_mxfp_exact_blocksize_crossover`: Universal `MXFP` AbsMax upper bound and exact
   integer block-size crossovers `B*(w)` for `MXINT4` vs `MXFP4-E2M1` (`8 / 3`), `MXINT6` vs
   `MXFP6-E2M3` (`12 / 4`) and `MXFP6-E3M2` (`47 / 13`), `MXINT8` vs `MXFP8-E4M3` (`223 / 57`,
   strictly winning at both `B = 16` and `B = 32`), and `MXINT8` vs `MXFP8-E2M5` (`13 / 5`).
-/

namespace MxintMxfpSwar

/-! ### Helper Lemmas for Theorem 1 -/

private theorem rat_pos_one : (0 : Rat) < 1 := rat_natCast_pos (by decide : 0 < 1)
private theorem rat_pos_four : (0 : Rat) < 4 := rat_natCast_pos (by decide : 0 < 4)
private theorem rat_pos_quarter : (0 : Rat) < (1 / 4 : Rat) := rat_div_pos rat_pos_one rat_pos_four
private theorem rat_nn_quarter : (0 : Rat) ≤ (1 / 4 : Rat) := Rat.le_of_lt rat_pos_quarter
private theorem rat_nn_half : (0 : Rat) ≤ (1 / 2 : Rat) :=
  Rat.le_of_lt (rat_div_pos rat_pos_one (rat_natCast_pos (by decide : 0 < 2)))

private theorem two_pow_ge_two {w : Nat} (hw : 2 ≤ w) : 2 ≤ 2 ^ (w - 1) := by
  have h1 : 1 ≤ w - 1 := by omega
  have h2 : 2 ^ 1 ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) h1
  omega

theorem mxintMax_pos {w : Nat} (hw : 2 ≤ w) : 1 ≤ mxintMax w := by
  unfold mxintMax
  have h := two_pow_ge_two hw
  omega

theorem mxintMaxRat_ge_one {w : Nat} (hw : 2 ≤ w) : (1 : Rat) ≤ mxintMaxRat w :=
  rat_natCast_le (mxintMax_pos hw)

theorem mxintMaxRat_pos {w : Nat} (hw : 2 ≤ w) : (0 : Rat) < mxintMaxRat w :=
  rat_lt_of_lt_of_le rat_pos_one (mxintMaxRat_ge_one hw)

theorem mxintMaxRat_sq_ge_one {w : Nat} (hw : 2 ≤ w) :
    (1 : Rat) ≤ mxintMaxRat w * mxintMaxRat w := by
  have h1 := mxintMaxRat_ge_one hw
  have h2 := rat_mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (mxintMaxRat_pos hw))
  exact Rat.le_trans h1 (by simpa [Rat.mul_one] using h2)

private theorem natCast_pred_add_one {B : Nat} (hB : 1 ≤ B) :
    ((B - 1 : Nat) : Rat) + 1 = (B : Rat) := by
  have h : (B - 1) + 1 = B := Nat.sub_add_cancel hB
  conv => rhs; rw [← h]
  rw [Rat.natCast_add]
  rfl

theorem mxint_absmax_upper {w B : Nat} (hw : 2 ≤ w) (_hB : 1 ≤ B)
    (u e : Fin B → Rat) (i0 : Fin B)
    (hAnchor : ratAbs (u i0) = mxintMaxRat w)
    (hAnchorErr : e i0 = 0)
    (hErr : IsMxintErr u e) :
    finSum e / l2NormSq u ≤ omegaMxintAbsMax w B := by
  unfold omegaMxintAbsMax
  let M := mxintMaxRat w
  let bm1 : Rat := ((B - 1 : Nat) : Rat)
  let Se := finSumExcept i0 e
  let Su := finSumExcept i0 (fun j => u j * u j)
  have hMpos : (0 : Rat) < M := mxintMaxRat_pos hw
  have hM2pos : (0 : Rat) < M * M := rat_mul_pos hMpos hMpos
  have hbm1_nn : (0 : Rat) ≤ bm1 := rat_natCast_nonneg (B - 1)
  have hu0sq : u i0 * u i0 = M * M := by
    rw [← ratAbs_sq (u i0), hAnchor]
  have hFe : finSum e = Se := by
    rw [finSum_split_at i0 e, hAnchorErr, Rat.zero_add]
  have hNorm : l2NormSq u = M * M + Su := by
    rw [l2NormSq_split_at i0 u, hu0sq]
  have hSu_nn : (0 : Rat) ≤ Su := finSumExcept_nonneg i0 (fun j _ => rat_sq_nonneg (u j))
  have hNormPos : (0 : Rat) < l2NormSq u := by
    rw [hNorm]; exact rat_add_pos_of_pos_of_nonneg hM2pos hSu_nn
  have h4pos : (0 : Rat) < 4 * M * M := by
    have : 4 * M * M = 4 * (M * M) := by grind
    rw [this]; exact rat_mul_pos rat_pos_four hM2pos
  have hDenPos : (0 : Rat) < 4 * M * M + bm1 := rat_add_pos_of_pos_of_nonneg h4pos hbm1_nn
  change finSum e / l2NormSq u ≤ bm1 / (4 * M * M + bm1)
  rw [rat_div_le_div_iff hNormPos hDenPos, hFe, hNorm]
  have hSe_quarter : Se ≤ bm1 * (1 / 4 : Rat) := by
    have h1 : Se ≤ finSumExcept i0 (fun _ => (1 / 4 : Rat)) :=
      finSumExcept_le i0 (fun j _ => (hErr j).2.1)
    rw [finSumExcept_const] at h1
    exact h1
  have hSe_Su : Se ≤ Su := finSumExcept_le i0 (fun j _ => (hErr j).2.2)
  have hTerm1 : Se * (4 * M * M) ≤ bm1 * (M * M) := by
    have h := rat_mul_le_mul_of_nonneg_right hSe_quarter (Rat.le_of_lt h4pos)
    have heq : bm1 * (1 / 4 : Rat) * (4 * M * M) = bm1 * (M * M) := by grind
    rw [heq] at h; exact h
  have hTerm2 : Se * bm1 ≤ bm1 * Su := by
    have h := rat_mul_le_mul_of_nonneg_right hSe_Su hbm1_nn
    have heq : Su * bm1 = bm1 * Su := by grind
    rw [heq] at h; exact h
  have hSum := rat_add_le_add hTerm1 hTerm2
  have hl : Se * (4 * M * M + bm1) = Se * (4 * M * M) + Se * bm1 := by grind
  have hr : bm1 * (M * M + Su) = bm1 * (M * M) + bm1 * Su := by grind
  rw [hl, hr]; exact hSum

theorem mxint_absmax_tight {w B : Nat} (hw : 2 ≤ w) (hB : 1 ≤ B) :
    let u : Fin B → Rat := fun j => if j.val = 0 then mxintMaxRat w else 1 / 2
    let e : Fin B → Rat := fun j => if j.val = 0 then 0 else 1 / 4
    let i0 : Fin B := ⟨0, hB⟩
    ratAbs (u i0) = mxintMaxRat w ∧
    e i0 = 0 ∧
    IsMxintErr u e ∧
    finSum e / l2NormSq u = omegaMxintAbsMax w B := by
  intro u e i0
  let M := mxintMaxRat w
  let bm1 : Rat := ((B - 1 : Nat) : Rat)
  have hMpos : (0 : Rat) < M := mxintMaxRat_pos hw
  have hM2pos : (0 : Rat) < M * M := rat_mul_pos hMpos hMpos
  have hbm1_nn : (0 : Rat) ≤ bm1 := rat_natCast_nonneg (B - 1)
  have hAnchor : ratAbs (u i0) = M := by
    change ratAbs M = M
    unfold ratAbs
    have hnot : ¬ (M < 0) := Rat.not_lt.mpr (Rat.le_of_lt hMpos)
    simp [hnot]
  have hAnchorErr : e i0 = 0 := rfl
  have hErr : IsMxintErr u e := by
    intro j
    by_cases hj : j.val = 0
    · simp only [u, e, hj, ↓reduceIte]
      exact ⟨Rat.le_refl, rat_nn_quarter, rat_sq_nonneg M⟩
    · simp only [u, e, hj, ↓reduceIte]
      refine ⟨rat_nn_quarter, Rat.le_refl, ?_⟩
      have : (1 / 2 : Rat) * (1 / 2 : Rat) = 1 / 4 := by grind
      rw [this]; exact Rat.le_refl
  have hFe : finSum e = bm1 * (1 / 4 : Rat) := by
    rw [finSum_split_at i0 e, hAnchorErr, Rat.zero_add]
    have hc : finSumExcept i0 e = finSumExcept i0 (fun _ => (1 / 4 : Rat)) := by
      unfold finSumExcept
      apply finSum_congr
      intro j
      by_cases hj : j = i0
      · simp [hj]
      · have hval : j.val ≠ 0 := by intro h0; apply hj; exact Fin.ext h0
        simp [hj, e, hval]
    rw [hc, finSumExcept_const]
  have hNorm : l2NormSq u = M * M + bm1 * (1 / 4 : Rat) := by
    rw [l2NormSq_split_at i0 u]
    have hu0 : u i0 * u i0 = M * M := rfl
    have hc : finSumExcept i0 (fun j => u j * u j) = finSumExcept i0 (fun _ => (1 / 4 : Rat)) := by
      unfold finSumExcept
      apply finSum_congr
      intro j
      by_cases hj : j = i0
      · simp [hj]
      · have hval : j.val ≠ 0 := by intro h0; apply hj; exact Fin.ext h0
        simp only [hj, ↓reduceIte, u, hval]
        grind
    rw [hu0, hc, finSumExcept_const]
  refine ⟨hAnchor, hAnchorErr, hErr, ?_⟩
  unfold omegaMxintAbsMax
  rw [hFe, hNorm]
  change (bm1 * (1 / 4 : Rat)) / (M * M + bm1 * (1 / 4 : Rat)) = bm1 / (4 * M * M + bm1)
  have hD1 : M * M + bm1 * (1 / 4 : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg hM2pos (Rat.mul_nonneg hbm1_nn rat_nn_quarter))
  have hD2 : 4 * M * M + bm1 ≠ 0 := by
    have h4 : (0 : Rat) < 4 * M * M := by
      have : 4 * M * M = 4 * (M * M) := by grind
      rw [this]; exact rat_mul_pos rat_pos_four hM2pos
    exact Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg h4 hbm1_nn)
  rw [rat_div_eq_div_iff hD1 hD2]
  grind

theorem mxint_e8m0_upper {w B : Nat} (hw : 2 ≤ w) (hB : 1 ≤ B)
    (u e : Fin B → Rat) (i0 : Fin B)
    (hAnchor : mxintMaxRat w / 2 ≤ ratAbs (u i0))
    (hErr : IsMxintErr u e) :
    finSum e / l2NormSq u ≤ omegaMxintE8M0 w B := by
  unfold omegaMxintE8M0
  let M := mxintMaxRat w
  let bm1 : Rat := ((B - 1 : Nat) : Rat)
  let Se := finSumExcept i0 e
  let Su := finSumExcept i0 (fun j => u j * u j)
  have hMpos : (0 : Rat) < M := mxintMaxRat_pos hw
  have hM2ge1 : (1 : Rat) ≤ M * M := mxintMaxRat_sq_ge_one hw
  have hM2pos : (0 : Rat) < M * M := rat_lt_of_lt_of_le rat_pos_one hM2ge1
  have hbm1_nn : (0 : Rat) ≤ bm1 := rat_natCast_nonneg (B - 1)
  have hBpos : (0 : Rat) < (B : Rat) := rat_natCast_pos hB
  have hB_eq : bm1 + 1 = (B : Rat) := natCast_pred_add_one hB
  have hu0sq : M * M / 4 ≤ u i0 * u i0 := by
    rw [← ratAbs_sq (u i0)]
    have hnn : (0 : Rat) ≤ M / 2 := by
      have heq : M / 2 = M * (1 / 2 : Rat) := by grind
      rw [heq]; exact Rat.mul_nonneg (Rat.le_of_lt hMpos) rat_nn_half
    have h1 := rat_mul_le_mul_of_nonneg_left hAnchor hnn
    have h2 := rat_mul_le_mul_of_nonneg_right hAnchor (Rat.le_trans hnn hAnchor)
    have h3 := Rat.le_trans h1 h2
    have heq : (M / 2) * (M / 2) = M * M / 4 := by grind
    rw [heq] at h3
    exact h3
  have hFe : finSum e = e i0 + Se := finSum_split_at i0 e
  have hNorm : l2NormSq u = u i0 * u i0 + Su := l2NormSq_split_at i0 u
  have hSu_nn : (0 : Rat) ≤ Su := finSumExcept_nonneg i0 (fun j _ => rat_sq_nonneg (u j))
  have hM2q_pos : (0 : Rat) < M * M / 4 := by
    have : M * M / 4 = (M * M) * (1 / 4 : Rat) := by grind
    rw [this]; exact rat_mul_pos hM2pos rat_pos_quarter
  have hNormPos : (0 : Rat) < l2NormSq u := by
    rw [hNorm]
    exact rat_add_pos_of_pos_of_nonneg (rat_lt_of_lt_of_le hM2q_pos hu0sq) hSu_nn
  have hDenPos : (0 : Rat) < M * M + bm1 := rat_add_pos_of_pos_of_nonneg hM2pos hbm1_nn
  change finSum e / l2NormSq u ≤ (B : Rat) / (M * M + bm1)
  rw [rat_div_le_div_iff hNormPos hDenPos, hFe, hNorm]
  have hSe_quarter : Se ≤ bm1 * (1 / 4 : Rat) := by
    have h1 : Se ≤ finSumExcept i0 (fun _ => (1 / 4 : Rat)) :=
      finSumExcept_le i0 (fun j _ => (hErr j).2.1)
    rw [finSumExcept_const] at h1
    exact h1
  have hSe_Su : Se ≤ Su := finSumExcept_le i0 (fun j _ => (hErr j).2.2)
  have hT1 : e i0 * (M * M + bm1) ≤ (1 / 4 : Rat) * (M * M + bm1) :=
    rat_mul_le_mul_of_nonneg_right (hErr i0).2.1 (Rat.le_of_lt hDenPos)
  have hT2 : Se * (M * M - 1) ≤ (bm1 * (1 / 4 : Rat)) * (M * M - 1) :=
    rat_mul_le_mul_of_nonneg_right hSe_quarter (rat_sub_nonneg hM2ge1)
  have hT3 : Se * (B : Rat) ≤ Su * (B : Rat) :=
    rat_mul_le_mul_of_nonneg_right hSe_Su (Rat.le_of_lt hBpos)
  have hT4 : (B : Rat) * (M * M / 4) ≤ (B : Rat) * (u i0 * u i0) :=
    rat_mul_le_mul_of_nonneg_left hu0sq (Rat.le_of_lt hBpos)
  have hL : (e i0 + Se) * (M * M + bm1) =
      e i0 * (M * M + bm1) + Se * (M * M - 1) + Se * (B : Rat) := by grind
  have hR : (1 / 4 : Rat) * (M * M + bm1) + (bm1 * (1 / 4 : Rat)) * (M * M - 1) =
      (B : Rat) * (M * M / 4) := by grind
  have h12 := rat_add_le_add hT1 hT2
  rw [hR] at h12
  have h12' := Rat.le_trans h12 hT4
  have hAll := rat_add_le_add h12' hT3
  rw [hL]
  have hR2 : (B : Rat) * (u i0 * u i0) + Su * (B : Rat) = (B : Rat) * (u i0 * u i0 + Su) := by grind
  rw [hR2] at hAll
  exact hAll

theorem mxint_e8m0_tight {w B : Nat} (hw : 2 ≤ w) (hB : 1 ≤ B) :
    let u : Fin B → Rat := fun j => if j.val = 0 then mxintMaxRat w / 2 else 1 / 2
    let e : Fin B → Rat := fun _ => 1 / 4
    let i0 : Fin B := ⟨0, hB⟩
    mxintMaxRat w / 2 ≤ ratAbs (u i0) ∧
    IsMxintErr u e ∧
    finSum e / l2NormSq u = omegaMxintE8M0 w B := by
  intro u e i0
  let M := mxintMaxRat w
  let bm1 : Rat := ((B - 1 : Nat) : Rat)
  have hMpos : (0 : Rat) < M := mxintMaxRat_pos hw
  have hM2ge1 : (1 : Rat) ≤ M * M := mxintMaxRat_sq_ge_one hw
  have hM2pos : (0 : Rat) < M * M := rat_lt_of_lt_of_le rat_pos_one hM2ge1
  have hbm1_nn : (0 : Rat) ≤ bm1 := rat_natCast_nonneg (B - 1)
  have hB_eq : bm1 + 1 = (B : Rat) := natCast_pred_add_one hB
  have hMhalf_nn : (0 : Rat) ≤ M / 2 := by
    have : M / 2 = M * (1 / 2 : Rat) := by grind
    rw [this]; exact Rat.mul_nonneg (Rat.le_of_lt hMpos) rat_nn_half
  have hAnchor : M / 2 ≤ ratAbs (u i0) := by
    change M / 2 ≤ ratAbs (M / 2)
    unfold ratAbs
    have hnot : ¬ (M / 2 < 0) := Rat.not_lt.mpr hMhalf_nn
    simp [hnot]
  have hErr : IsMxintErr u e := by
    intro j
    by_cases hj : j.val = 0
    · simp only [u, e, hj, ↓reduceIte]
      refine ⟨rat_nn_quarter, Rat.le_refl, ?_⟩
      have hq : (M / 2) * (M / 2) = M * M / 4 := by grind
      rw [hq]
      have h1 := rat_mul_le_mul_of_nonneg_right hM2ge1 rat_nn_quarter
      have h2 : (1 : Rat) * (1 / 4 : Rat) = 1 / 4 := by grind
      have h3 : M * M * (1 / 4 : Rat) = M * M / 4 := by grind
      rw [h2, h3] at h1; exact h1
    · simp only [u, e, hj, ↓reduceIte]
      refine ⟨rat_nn_quarter, Rat.le_refl, ?_⟩
      have : (1 / 2 : Rat) * (1 / 2 : Rat) = 1 / 4 := by grind
      rw [this]; exact Rat.le_refl
  have hFe : finSum e = (B : Rat) * (1 / 4 : Rat) := finSum_const (1 / 4 : Rat)
  have hNorm : l2NormSq u = (M / 2) * (M / 2) + bm1 * (1 / 4 : Rat) := by
    rw [l2NormSq_split_at i0 u]
    have hu0 : u i0 * u i0 = (M / 2) * (M / 2) := rfl
    have hc : finSumExcept i0 (fun j => u j * u j) = finSumExcept i0 (fun _ => (1 / 4 : Rat)) := by
      unfold finSumExcept
      apply finSum_congr
      intro j
      by_cases hj : j = i0
      · simp [hj]
      · have hval : j.val ≠ 0 := by intro h0; apply hj; exact Fin.ext h0
        simp only [hj, ↓reduceIte, u, hval]
        grind
    rw [hu0, hc, finSumExcept_const]
  refine ⟨hAnchor, hErr, ?_⟩
  unfold omegaMxintE8M0
  rw [hFe, hNorm]
  change ((B : Rat) * (1 / 4 : Rat)) / ((M / 2) * (M / 2) + bm1 * (1 / 4 : Rat)) = (B : Rat) / (M * M + bm1)
  have hD1 : (M / 2) * (M / 2) + bm1 * (1 / 4 : Rat) ≠ 0 := by
    have hp : (0 : Rat) < (M / 2) * (M / 2) := by
      have : (M / 2) * (M / 2) = (M * M) * (1 / 4 : Rat) := by grind
      rw [this]; exact rat_mul_pos hM2pos rat_pos_quarter
    exact Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg hp (Rat.mul_nonneg hbm1_nn rat_nn_quarter))
  have hD2 : M * M + bm1 ≠ 0 := Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg hM2pos hbm1_nn)
  rw [rat_div_eq_div_iff hD1 hD2]
  grind

/-- **Theorem 1 (`mxint_all_b_ef21_contraction_exact`)**:
    Universal all-`B` (`B ≥ 1, w ≥ 2`) exact worst-case EF21 contraction bounds with tight
    attainment for symmetric `MXINT_w` (`M = 2^(w-1) - 1`) under both Continuous AbsMax and
    OCP `E8M0` scaling. -/
theorem mxint_all_b_ef21_contraction_exact :
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      ∀ (u e : Fin B → Rat) (i0 : Fin B),
        ratAbs (u i0) = mxintMaxRat w → e i0 = 0 → IsMxintErr u e →
        finSum e / l2NormSq u ≤ omegaMxintAbsMax w B) ∧
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      ∃ (u e : Fin B → Rat) (i0 : Fin B),
        ratAbs (u i0) = mxintMaxRat w ∧ e i0 = 0 ∧ IsMxintErr u e ∧
        finSum e / l2NormSq u = omegaMxintAbsMax w B) ∧
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      ∀ (u e : Fin B → Rat) (i0 : Fin B),
        mxintMaxRat w / 2 ≤ ratAbs (u i0) → IsMxintErr u e →
        finSum e / l2NormSq u ≤ omegaMxintE8M0 w B) ∧
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      ∃ (u e : Fin B → Rat) (i0 : Fin B),
        mxintMaxRat w / 2 ≤ ratAbs (u i0) ∧ IsMxintErr u e ∧
        finSum e / l2NormSq u = omegaMxintE8M0 w B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w B hw hB u e i0 ha he herr
    exact mxint_absmax_upper hw hB u e i0 ha he herr
  · intro w B hw hB
    exact ⟨fun j => if j.val = 0 then mxintMaxRat w else 1 / 2,
           fun j => if j.val = 0 then 0 else 1 / 4,
           ⟨0, hB⟩, mxint_absmax_tight hw hB⟩
  · intro w B hw hB u e i0 ha herr
    exact mxint_e8m0_upper hw hB u e i0 ha herr
  · intro w B hw hB
    exact ⟨fun j => if j.val = 0 then mxintMaxRat w / 2 else 1 / 2,
           fun _ => 1 / 4,
           ⟨0, hB⟩, mxint_e8m0_tight hw hB⟩

/-! ### Helper Lemmas for Theorem 2 (`MXINT_w` vs `MXFP_w` Exact Crossovers) -/

/-- Universal `MXFP` Continuous AbsMax EF21 upper bound over all vectors `u : Fin B → Rat`. -/
theorem mxfp_absmax_upper (spec : MxfpSpec)
    (hM : (0 : Rat) < spec.M)
    (hRhoPos : (0 : Rat) < spec.rhoNorm)
    (hRhoLt1 : spec.rhoNorm < 1)
    (hEhiEq : spec.eHi = spec.rhoNorm * (spec.vHi * spec.vHi))
    (_hEhiNN : (0 : Rat) ≤ spec.eHi)
    {B : Nat} (hB : 1 ≤ B)
    (u e : Fin B → Rat) (i0 : Fin B)
    (hAnchor : ratAbs (u i0) = spec.M)
    (hAnchorErr : e i0 = 0)
    (hErr : IsMxfpErr spec u e) :
    finSum e / l2NormSq u ≤ omegaMxfpAbsMax spec B := by
  let bm1 : Rat := ((B - 1 : Nat) : Rat)
  let c1h2 : Rat := (spec.c1 / 2) * (spec.c1 / 2)
  let lam := omegaMxfpAbsMax spec B
  have hM2pos : (0 : Rat) < spec.M * spec.M := rat_mul_pos hM hM
  have hc1h2_nn : (0 : Rat) ≤ c1h2 := rat_sq_nonneg (spec.c1 / 2)
  have hu0sq : u i0 * u i0 = spec.M * spec.M := by
    rw [← ratAbs_sq (u i0), hAnchor]
  have hSu_nn : (0 : Rat) ≤ finSumExcept i0 (fun j => u j * u j) :=
    finSumExcept_nonneg i0 (fun j _ => rat_sq_nonneg (u j))
  have hNormPos : (0 : Rat) < l2NormSq u := by
    rw [l2NormSq_split_at i0 u, hu0sq]
    exact rat_add_pos_of_pos_of_nonneg hM2pos hSu_nn
  by_cases hB1 : B = 1
  · subst hB1
    have hFe : finSum e = 0 := by
      rw [finSum_split_at i0 e, hAnchorErr, Rat.zero_add]
      have h0 : finSumExcept i0 e = finSumExcept i0 (fun _ => (0 : Rat)) := by
        unfold finSumExcept
        apply finSum_congr
        intro j
        have hj : j = i0 := Fin.ext (by omega)
        simp [hj]
      rw [h0, finSumExcept_const, Rat.mul_zero]
    have hLamNN : (0 : Rat) ≤ lam := by
      dsimp only [lam]
      unfold omegaMxfpAbsMax
      have h0 : (0 : Rat) ≤ ((1 - 1 : Nat) : Rat) * spec.eHi /
          (spec.M * spec.M + ((1 - 1 : Nat) : Rat) * (spec.vHi * spec.vHi)) := by
        have hzero : ((1 - 1 : Nat) : Rat) = 0 := rfl
        rw [hzero, Rat.zero_mul, Rat.div_def, Rat.zero_mul]
        exact Rat.le_refl
      exact Rat.le_trans h0 (le_ratMax_left _ _)
    rw [hFe]
    have h0div : (0 : Rat) / l2NormSq u = 0 := by rw [Rat.div_def, Rat.zero_mul]
    rw [h0div]; exact hLamNN
  · have hbm1_pos : (0 : Rat) < bm1 := rat_natCast_pos (by omega)
    let bNorm := (bm1 * spec.eHi) / (spec.M * spec.M + bm1 * (spec.vHi * spec.vHi))
    let bSub := (bm1 * c1h2) / (spec.M * spec.M + bm1 * c1h2)
    have hDenNormPos : (0 : Rat) < spec.M * spec.M + bm1 * (spec.vHi * spec.vHi) :=
      rat_add_pos_of_pos_of_nonneg hM2pos (Rat.mul_nonneg (Rat.le_of_lt hbm1_pos) (rat_sq_nonneg _))
    have hDenSubPos : (0 : Rat) < spec.M * spec.M + bm1 * c1h2 :=
      rat_add_pos_of_pos_of_nonneg hM2pos (Rat.mul_nonneg (Rat.le_of_lt hbm1_pos) hc1h2_nn)
    have hbNorm_le : bNorm ≤ lam := le_ratMax_left bNorm bSub
    have hbSub_le : bSub ≤ lam := le_ratMax_right bNorm bSub
    have hbNorm_lt1 : bNorm < 1 := by
      apply rat_div_lt_of_mul_lt hDenNormPos
      have h1 : bm1 * spec.eHi ≤ bm1 * (spec.vHi * spec.vHi) := by
        rw [hEhiEq]
        have hlt := rat_mul_le_mul_of_nonneg_right (Rat.le_of_lt hRhoLt1) (rat_sq_nonneg spec.vHi)
        have hlt2 := rat_mul_le_mul_of_nonneg_left hlt (Rat.le_of_lt hbm1_pos)
        have hl : bm1 * (spec.rhoNorm * (spec.vHi * spec.vHi)) = bm1 * (spec.rhoNorm * (spec.vHi * spec.vHi)) := rfl
        have hr : bm1 * (1 * (spec.vHi * spec.vHi)) = bm1 * (spec.vHi * spec.vHi) := by grind
        rw [hr] at hlt2; exact hlt2
      have h3 : bm1 * spec.eHi < spec.M * spec.M + bm1 * (spec.vHi * spec.vHi) := by
        apply rat_lt_of_sub_pos
        have hsub : (spec.M * spec.M + bm1 * (spec.vHi * spec.vHi)) - bm1 * spec.eHi =
            spec.M * spec.M + (bm1 * (spec.vHi * spec.vHi) - bm1 * spec.eHi) := by grind
        rw [hsub]
        exact rat_add_pos_of_pos_of_nonneg hM2pos (rat_sub_nonneg h1)
      simpa [Rat.one_mul] using h3
    have hbSub_lt1 : bSub < 1 := by
      apply rat_div_lt_of_mul_lt hDenSubPos
      have h3 : bm1 * c1h2 < spec.M * spec.M + bm1 * c1h2 := by
        apply rat_lt_of_sub_pos
        have : spec.M * spec.M + bm1 * c1h2 - bm1 * c1h2 = spec.M * spec.M := by grind
        rw [this]; exact hM2pos
      simpa [Rat.one_mul] using h3
    have hLamLt1 : lam < 1 := ratMax_lt_iff.mpr ⟨hbNorm_lt1, hbSub_lt1⟩
    have hLamNN : (0 : Rat) ≤ lam := by
      have hbSub_nn : (0 : Rat) ≤ bSub := by
        apply rat_le_div_of_mul_le hDenSubPos
        rw [Rat.zero_mul]
        exact Rat.mul_nonneg (Rat.le_of_lt hbm1_pos) hc1h2_nn
      exact Rat.le_trans hbSub_nn hbSub_le
    have hCoord : ∀ j : Fin B, j ≠ i0 →
        e j - lam * (u j * u j) ≤ lam * (spec.M * spec.M) / bm1 := by
      intro j _
      rcases (hErr j).2 with ⟨heHi, heRho⟩ | ⟨heSub, heSq⟩
      · cases Rat.le_total (a := lam) (b := spec.rhoNorm) with
        | inl hLamLeRho =>
          have h1 : lam * e j ≤ lam * (spec.rhoNorm * (u j * u j)) :=
            rat_mul_le_mul_of_nonneg_left heRho hLamNN
          have h2 : (spec.rhoNorm - lam) * e j ≤ (spec.rhoNorm - lam) * spec.eHi :=
            rat_mul_le_mul_of_nonneg_left heHi (rat_sub_nonneg hLamLeRho)
          have hStep1 : spec.rhoNorm * (e j - lam * (u j * u j)) ≤
              spec.rhoNorm * (spec.eHi - lam * (spec.vHi * spec.vHi)) := by
            have hA := rat_add_le_add h2 h1
            have hL : (spec.rhoNorm - lam) * e j + lam * e j = spec.rhoNorm * e j := by grind
            have hR : (spec.rhoNorm - lam) * spec.eHi + lam * (spec.rhoNorm * (u j * u j)) =
                spec.rhoNorm * spec.eHi - lam * (spec.rhoNorm * (spec.vHi * spec.vHi)) +
                spec.rhoNorm * (lam * (u j * u j)) := by rw [← hEhiEq]; grind
            rw [hL, hR] at hA
            have hSub := rat_sub_nonneg hA
            apply rat_le_of_sub_nonneg
            have hEq : spec.rhoNorm * (spec.eHi - lam * (spec.vHi * spec.vHi)) -
                spec.rhoNorm * (e j - lam * (u j * u j)) =
                spec.rhoNorm * spec.eHi - lam * (spec.rhoNorm * (spec.vHi * spec.vHi)) +
                spec.rhoNorm * (lam * (u j * u j)) - spec.rhoNorm * e j := by grind
            rw [hEq]; exact hSub
          have hStep1' : e j - lam * (u j * u j) ≤ spec.eHi - lam * (spec.vHi * spec.vHi) := by
            apply rat_le_of_mul_pos_right hRhoPos
            rw [Rat.mul_comm _ spec.rhoNorm, Rat.mul_comm _ spec.rhoNorm]
            exact hStep1
          have hStep2 : spec.eHi - lam * (spec.vHi * spec.vHi) ≤
              spec.eHi - bNorm * (spec.vHi * spec.vHi) := by
            have hm := rat_mul_le_mul_of_nonneg_right hbNorm_le (rat_sq_nonneg spec.vHi)
            apply rat_le_of_sub_nonneg
            have : (spec.eHi - bNorm * (spec.vHi * spec.vHi)) -
                (spec.eHi - lam * (spec.vHi * spec.vHi)) =
                lam * (spec.vHi * spec.vHi) - bNorm * (spec.vHi * spec.vHi) := by grind
            rw [this]; exact rat_sub_nonneg hm
          have hStep3 : spec.eHi - bNorm * (spec.vHi * spec.vHi) =
              bNorm * (spec.M * spec.M) / bm1 := by
            have hbm : bNorm * (spec.M * spec.M + bm1 * (spec.vHi * spec.vHi)) = bm1 * spec.eHi :=
              rat_div_mul_cancel (Rat.ne_of_gt hDenNormPos)
            apply Eq.symm
            rw [rat_div_eq_iff (Rat.ne_of_gt hbm1_pos)]
            grind
          have hStep4 : bNorm * (spec.M * spec.M) / bm1 ≤ lam * (spec.M * spec.M) / bm1 := by
            rw [rat_div_le_div_iff hbm1_pos hbm1_pos]
            have h := rat_mul_le_mul_of_nonneg_right hbNorm_le (Rat.le_of_lt hM2pos)
            exact rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hbm1_pos)
          exact Rat.le_trans hStep1' (Rat.le_trans hStep2 (by rw [hStep3]; exact hStep4))
        | inr hRhoLeLam =>
          have h1 : e j - lam * (u j * u j) ≤ 0 := by
            have hm := rat_mul_le_mul_of_nonneg_right hRhoLeLam (rat_sq_nonneg (u j))
            have hle := Rat.le_trans heRho hm
            have := rat_sub_nonneg hle
            grind
          have h2 : (0 : Rat) ≤ lam * (spec.M * spec.M) / bm1 := by
            apply rat_le_div_of_mul_le hbm1_pos
            rw [Rat.zero_mul]
            exact Rat.mul_nonneg hLamNN (Rat.le_of_lt hM2pos)
          exact Rat.le_trans h1 h2
      · have h1 : e j - lam * (u j * u j) ≤ (1 - lam) * e j := by
          have hm := rat_mul_le_mul_of_nonneg_left heSq hLamNN
          apply rat_le_of_sub_nonneg
          have : (1 - lam) * e j - (e j - lam * (u j * u j)) = lam * (u j * u j) - lam * e j := by grind
          rw [this]; exact rat_sub_nonneg hm
        have h2 : (1 - lam) * e j ≤ (1 - lam) * c1h2 :=
          rat_mul_le_mul_of_nonneg_left heSub (rat_sub_nonneg (Rat.le_of_lt hLamLt1))
        have h3 : (1 - lam) * c1h2 ≤ (1 - bSub) * c1h2 := by
          have hle : 1 - lam ≤ 1 - bSub := by
            apply rat_le_of_sub_nonneg
            have : (1 - bSub) - (1 - lam) = lam - bSub := by grind
            rw [this]; exact rat_sub_nonneg hbSub_le
          exact rat_mul_le_mul_of_nonneg_right hle hc1h2_nn
        have h4 : (1 - bSub) * c1h2 = bSub * (spec.M * spec.M) / bm1 := by
          have hbm : bSub * (spec.M * spec.M + bm1 * c1h2) = bm1 * c1h2 :=
            rat_div_mul_cancel (Rat.ne_of_gt hDenSubPos)
          apply Eq.symm
          rw [rat_div_eq_iff (Rat.ne_of_gt hbm1_pos)]
          grind
        have h5 : bSub * (spec.M * spec.M) / bm1 ≤ lam * (spec.M * spec.M) / bm1 := by
          rw [rat_div_le_div_iff hbm1_pos hbm1_pos]
          have h := rat_mul_le_mul_of_nonneg_right hbSub_le (Rat.le_of_lt hM2pos)
          exact rat_mul_le_mul_of_nonneg_right h (Rat.le_of_lt hbm1_pos)
        exact Rat.le_trans h1 (Rat.le_trans h2 (Rat.le_trans h3 (by rw [h4]; exact h5)))
    have hSumEx : finSumExcept i0 (fun j => e j - lam * (u j * u j)) ≤ lam * (spec.M * spec.M) := by
      have h1 := finSumExcept_le i0 hCoord
      rw [finSumExcept_const] at h1
      have hc : bm1 * (lam * (spec.M * spec.M) / bm1) = lam * (spec.M * spec.M) := by
        rw [Rat.mul_comm, rat_div_mul_cancel (Rat.ne_of_gt hbm1_pos)]
      rw [hc] at h1
      exact h1
    have hTotal : finSum (fun j => e j - lam * (u j * u j)) ≤ 0 := by
      rw [finSum_split_at i0, hAnchorErr, hu0sq]
      have hsub := rat_sub_nonneg hSumEx
      grind
    have hLinear : finSum e - lam * l2NormSq u ≤ 0 := by
      have hEq : finSum (fun j => e j - lam * (u j * u j)) = finSum e - lam * l2NormSq u := by
        rw [finSum_sub, finSum_mul_left]
        rfl
      rw [← hEq]; exact hTotal
    apply rat_div_le_of_mul_le hNormPos
    have := rat_sub_nonneg hLinear
    grind

/-! ### Fast Pure-`Int` Linear-Fractional Comparison Helpers -/

private theorem cross_lt_ge (a1 a2 c1 c2 d1 d2 e1 e2 : Int) {B B0 : Nat}
    (hB : B0 ≤ B) (hB0 : 1 ≤ B0)
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (he1 : 0 < e1) (he2 : 0 ≤ e2)
    (hPoly : let b0 : Int := ((B0 - 1 : Nat) : Int)
             let k0 := (d1 + d2 * b0) * (c1 + c2 * b0) - (a1 + a2 * b0) * (e1 + e2 * b0)
             let k1 := (d2 * c1 + d1 * c2 - a2 * e1 - a1 * e2) + 2 * (d2 * c2 - a2 * e2) * b0
             let k2 := d2 * c2 - a2 * e2
             0 < k0 ∧ 0 ≤ k1 ∧ 0 ≤ k2) :
    ((a1 : Rat) + (a2 : Rat) * ((B - 1 : Nat) : Rat)) / ((c1 : Rat) + (c2 : Rat) * ((B - 1 : Nat) : Rat)) <
    ((d1 : Rat) + (d2 : Rat) * ((B - 1 : Nat) : Rat)) / ((e1 : Rat) + (e2 : Rat) * ((B - 1 : Nat) : Rat)) := by
  have hc : (0 : Rat) < (c1 : Rat) + (c2 : Rat) * ((B - 1 : Nat) : Rat) :=
    rat_add_pos_of_pos_of_nonneg (rat_intCast_pos hc1) (Rat.mul_nonneg (rat_intCast_nonneg hc2) (rat_natCast_nonneg _))
  have he : (0 : Rat) < (e1 : Rat) + (e2 : Rat) * ((B - 1 : Nat) : Rat) :=
    rat_add_pos_of_pos_of_nonneg (rat_intCast_pos he1) (Rat.mul_nonneg (rat_intCast_nonneg he2) (rat_natCast_nonneg _))
  rw [rat_div_lt_div_iff hc he]
  let b : Int := ((B - 1 : Nat) : Int)
  let b0 : Int := ((B0 - 1 : Nat) : Int)
  let t : Int := ((B - B0 : Nat) : Int)
  have ht_nn : 0 ≤ t := Int.natCast_nonneg _
  have hb_eq : b = b0 + t := by omega
  rcases hPoly with ⟨hk0, hk1, hk2⟩
  have hInt : (a1 + a2 * b) * (e1 + e2 * b) < (d1 + d2 * b) * (c1 + c2 * b) := by
    have hId : (d1 + d2 * b) * (c1 + c2 * b) - (a1 + a2 * b) * (e1 + e2 * b) =
        ((d1 + d2 * b0) * (c1 + c2 * b0) - (a1 + a2 * b0) * (e1 + e2 * b0)) +
        (((d2 * c1 + d1 * c2 - a2 * e1 - a1 * e2) + 2 * (d2 * c2 - a2 * e2) * b0) * t +
         (d2 * c2 - a2 * e2) * (t * t)) := by
      rw [hb_eq]; grind
    have hk0' : 0 < (d1 + d2 * b0) * (c1 + c2 * b0) - (a1 + a2 * b0) * (e1 + e2 * b0) := hk0
    have hk1' : 0 ≤ (d2 * c1 + d1 * c2 - a2 * e1 - a1 * e2) + 2 * (d2 * c2 - a2 * e2) * b0 := hk1
    have h1 : 0 ≤ (((d2 * c1 + d1 * c2 - a2 * e1 - a1 * e2) + 2 * (d2 * c2 - a2 * e2) * b0) * t) :=
      Int.mul_nonneg hk1' ht_nn
    have h2 : 0 ≤ (d2 * c2 - a2 * e2) * (t * t) := Int.mul_nonneg hk2 (Int.mul_nonneg ht_nn ht_nn)
    omega
  have hRat := rat_intCast_lt hInt
  simp only [Rat.intCast_mul, Rat.intCast_add] at hRat
  exact hRat

private theorem cross_lt_range (a1 a2 c1 c2 d1 d2 e1 e2 : Int) {B Blo Bhi : Nat}
    (hLo : Blo ≤ B) (hHi : B ≤ Bhi) (hLo1 : 1 ≤ Blo)
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (he1 : 0 < e1) (he2 : 0 ≤ e2)
    (hPoly : let bLo : Int := ((Blo - 1 : Nat) : Int)
             let bHi : Int := ((Bhi - 1 : Nat) : Int)
             let fLo := (d1 + d2 * bLo) * (c1 + c2 * bLo) - (a1 + a2 * bLo) * (e1 + e2 * bLo)
             let fHi := (d1 + d2 * bHi) * (c1 + c2 * bHi) - (a1 + a2 * bHi) * (e1 + e2 * bHi)
             let k2 := d2 * c2 - a2 * e2
             0 < fLo ∧ 0 < fHi ∧ k2 ≤ 0) :
    ((a1 : Rat) + (a2 : Rat) * ((B - 1 : Nat) : Rat)) / ((c1 : Rat) + (c2 : Rat) * ((B - 1 : Nat) : Rat)) <
    ((d1 : Rat) + (d2 : Rat) * ((B - 1 : Nat) : Rat)) / ((e1 : Rat) + (e2 : Rat) * ((B - 1 : Nat) : Rat)) := by
  have hc : (0 : Rat) < (c1 : Rat) + (c2 : Rat) * ((B - 1 : Nat) : Rat) :=
    rat_add_pos_of_pos_of_nonneg (rat_intCast_pos hc1) (Rat.mul_nonneg (rat_intCast_nonneg hc2) (rat_natCast_nonneg _))
  have he : (0 : Rat) < (e1 : Rat) + (e2 : Rat) * ((B - 1 : Nat) : Rat) :=
    rat_add_pos_of_pos_of_nonneg (rat_intCast_pos he1) (Rat.mul_nonneg (rat_intCast_nonneg he2) (rat_natCast_nonneg _))
  rw [rat_div_lt_div_iff hc he]
  let b : Int := ((B - 1 : Nat) : Int)
  let bLo : Int := ((Blo - 1 : Nat) : Int)
  let bHi : Int := ((Bhi - 1 : Nat) : Int)
  let s : Int := ((B - Blo : Nat) : Int)
  let r : Int := ((Bhi - B : Nat) : Int)
  have hs_nn : 0 ≤ s := Int.natCast_nonneg _
  have hr_nn : 0 ≤ r := Int.natCast_nonneg _
  have hb_lo : b = bLo + s := by omega
  have hb_hi : bHi = bLo + (s + r) := by omega
  rcases hPoly with ⟨hfLo, hfHi, hk2⟩
  have hfLo' : 0 < (d1 + d2 * bLo) * (c1 + c2 * bLo) - (a1 + a2 * bLo) * (e1 + e2 * bLo) := hfLo
  have hfHi' : 0 < (d1 + d2 * bHi) * (c1 + c2 * bHi) - (a1 + a2 * bHi) * (e1 + e2 * bHi) := hfHi
  have hInt : (a1 + a2 * b) * (e1 + e2 * b) < (d1 + d2 * b) * (c1 + c2 * b) := by
    by_cases hEq : Blo = Bhi
    · have : b = bLo := by omega
      rw [this]; omega
    · have hSpan : 0 < s + r := by omega
      have hScaled : (s + r) * ((d1 + d2 * b) * (c1 + c2 * b) - (a1 + a2 * b) * (e1 + e2 * b)) =
          r * ((d1 + d2 * bLo) * (c1 + c2 * bLo) - (a1 + a2 * bLo) * (e1 + e2 * bLo)) +
          s * ((d1 + d2 * bHi) * (c1 + c2 * bHi) - (a1 + a2 * bHi) * (e1 + e2 * bHi)) +
          (-(d2 * c2 - a2 * e2)) * (s * r * (s + r)) := by
        rw [hb_lo, hb_hi]; grind
      have hQuad : 0 ≤ (-(d2 * c2 - a2 * e2)) * (s * r * (s + r)) :=
        Int.mul_nonneg (by omega) (Int.mul_nonneg (Int.mul_nonneg hs_nn hr_nn) (by omega))
      have hPos : 0 < (s + r) * ((d1 + d2 * b) * (c1 + c2 * b) - (a1 + a2 * b) * (e1 + e2 * b)) := by
        rw [hScaled]
        by_cases hs0 : s = 0
        · have hr_pos : 0 < r := by omega
          have h1 : 0 < r * ((d1 + d2 * bLo) * (c1 + c2 * bLo) - (a1 + a2 * bLo) * (e1 + e2 * bLo)) :=
            Int.mul_pos hr_pos hfLo'
          have h2 : 0 ≤ s * ((d1 + d2 * bHi) * (c1 + c2 * bHi) - (a1 + a2 * bHi) * (e1 + e2 * bHi)) :=
            Int.mul_nonneg hs_nn (by omega)
          omega
        · have hs_pos : 0 < s := by omega
          have h1 : 0 ≤ r * ((d1 + d2 * bLo) * (c1 + c2 * bLo) - (a1 + a2 * bLo) * (e1 + e2 * bLo)) :=
            Int.mul_nonneg hr_nn (by omega)
          have h2 : 0 < s * ((d1 + d2 * bHi) * (c1 + c2 * bHi) - (a1 + a2 * bHi) * (e1 + e2 * bHi)) :=
            Int.mul_pos hs_pos hfHi'
          omega
      by_cases hlt : (a1 + a2 * b) * (e1 + e2 * b) < (d1 + d2 * b) * (c1 + c2 * b)
      · exact hlt
      · have hnonpos : (d1 + d2 * b) * (c1 + c2 * b) - (a1 + a2 * b) * (e1 + e2 * b) ≤ 0 := by omega
        have hmul : (s + r) * ((d1 + d2 * b) * (c1 + c2 * b) - (a1 + a2 * b) * (e1 + e2 * b)) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hnonpos
        omega
  have hRat := rat_intCast_lt hInt
  simp only [Rat.intCast_mul, Rat.intCast_add] at hRat
  exact hRat

private theorem frac_scale {a b k : Rat} (hb : b ≠ 0) (hk : k ≠ 0) :
    a / b = (k * a) / (k * b) := by
  have hkb : k * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hk h
    | inr h => exact hb h
  rw [rat_div_eq_div_iff hb hkb]
  grind

private theorem pos_rat_lin (c1 c2 : Int) (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (n : Nat) :
    (c1 : Rat) + (c2 : Rat) * (n : Rat) ≠ 0 :=
  Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (rat_intCast_pos hc1)
    (Rat.mul_nonneg (rat_intCast_nonneg hc2) (rat_natCast_nonneg n)))

private theorem frac_eq_int (p q r s : Rat) (a1 a2 c1 c2 : Int) (k : Rat) (B : Nat)
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hk : k ≠ 0)
    (hNum : k * (p + q * ((B - 1 : Nat) : Rat)) = (a1 : Rat) + (a2 : Rat) * ((B - 1 : Nat) : Rat))
    (hDen : k * (r + s * ((B - 1 : Nat) : Rat)) = (c1 : Rat) + (c2 : Rat) * ((B - 1 : Nat) : Rat)) :
    (p + q * ((B - 1 : Nat) : Rat)) / (r + s * ((B - 1 : Nat) : Rat)) =
    ((a1 : Rat) + (a2 : Rat) * ((B - 1 : Nat) : Rat)) / ((c1 : Rat) + (c2 : Rat) * ((B - 1 : Nat) : Rat)) := by
  have hD2 : (c1 : Rat) + (c2 : Rat) * ((B - 1 : Nat) : Rat) ≠ 0 := pos_rat_lin c1 c2 hc1 hc2 (B - 1)
  have hD1 : r + s * ((B - 1 : Nat) : Rat) ≠ 0 := by
    intro h0; rw [h0, Rat.mul_zero] at hDen; exact hD2 hDen.symm
  rw [frac_scale hD1 hk, hNum, hDen]

/-! ### Pairwise Crossover Proofs (AbsMax and OCP `E8M0`) -/

private theorem mxint4_vs_mxfp4_absmax :
    (∀ B : Nat, 2 ≤ B → B < 8 → omegaMxintAbsMax 4 B < omegaMxfpAbsMax mxfp4E2M1 B) ∧
    (∀ B : Nat, 8 ≤ B → omegaMxfpAbsMax mxfp4E2M1 B < omegaMxintAbsMax 4 B) := by
  constructor
  · intro B h2 h8
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp4E2M1 mxintMaxRat mxintMax
    have hlt := cross_lt_range 0 1 196 1 0 1 36 25 (Blo := 2) (Bhi := 7) (B := B)
      h2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hL : ((B - 1 : Nat) : Rat) / (4 * ((7 : Nat) : Rat) * ((7 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((196 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    have hR : (((B - 1 : Nat) : Rat) * 1) / (6 * 6 + ((B - 1 : Nat) : Rat) * (5 * 5)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((36 : Int) + (25 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    rw [← hL, ← hR] at hlt
    exact rat_lt_of_lt_of_le hlt (le_ratMax_left _ _)
  · intro B h8
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp4E2M1 mxintMaxRat mxintMax
    apply ratMax_lt_iff.mpr
    have hInt : ((B - 1 : Nat) : Rat) / (4 * ((7 : Nat) : Rat) * ((7 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((196 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    rw [hInt]
    constructor
    · have hL : (((B - 1 : Nat) : Rat) * 1) / (6 * 6 + ((B - 1 : Nat) : Rat) * (5 * 5)) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((36 : Int) + (25 : Int) * ((B - 1 : Nat) : Rat)) := by
        congr 1 <;> grind
      rw [hL]
      exact cross_lt_ge 0 1 36 25 0 1 196 1 (B0 := 8) (B := B)
        h8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hL : (((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) /
          (6 * 6 + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((576 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 16) 36 (1 / 16) 0 1 576 1 16 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : (((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) =
            0 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (6 : Rat) * 6 + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2)) =
            36 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hL]
      exact cross_lt_ge 0 1 576 1 0 1 196 1 (B0 := 8) (B := B)
        h8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem mxint4_vs_mxfp4_e8m0 :
    (∀ B : Nat, 1 ≤ B → B < 3 → omegaMxintE8M0 4 B < omegaMxfp4E2M1E8M0 B) ∧
    (∀ B : Nat, 3 ≤ B → omegaMxfp4E2M1E8M0 B < omegaMxintE8M0 4 B) := by
  constructor
  · intro B h1 h3
    unfold omegaMxintE8M0 omegaMxfp4E2M1E8M0 omegaMxfpE8M0 mxfp4E2M1 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one h1; grind
    have hInt : (B : Rat) / (((7 : Nat) : Rat) * ((7 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((49 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    have hHi : (1 + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) /
        (5 * 5 + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) =
        ((16 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((400 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      have h := frac_eq_int 1 (1 / 16) 25 (1 / 16) 16 1 400 1 16 B (by decide) (by decide) (by grind) (by grind) (by grind)
      have h1 : (1 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2)) =
          1 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      have h2 : (5 : Rat) * 5 + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2)) =
          25 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      rw [h2, h1]; exact h
    have hlt := cross_lt_range 1 1 49 1 16 1 400 1 (Blo := 1) (Bhi := 2) (B := B)
      h1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hInt]
    exact rat_lt_of_lt_of_le (by rw [← hHi] at hlt; exact hlt)
      (Rat.le_trans (le_ratMax_left _ _) (le_ratMax_left _ _))
  · intro B h3
    unfold omegaMxintE8M0 omegaMxfp4E2M1E8M0 omegaMxfpE8M0 mxfp4E2M1 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one (by omega : 1 ≤ B); grind
    have hInt : (B : Rat) / (((7 : Nat) : Rat) * ((7 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((49 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    rw [hInt]
    apply ratMax_lt_iff.mpr
    refine ⟨ratMax_lt_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · have hHi : (1 + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) /
          (5 * 5 + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) =
          ((16 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((400 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 1 (1 / 16) 25 (1 / 16) 16 1 400 1 16 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : (1 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2)) =
            1 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (5 : Rat) * 5 + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2)) =
            25 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hHi]
      exact cross_lt_ge 16 1 400 1 1 1 49 1 (B0 := 3) (B := B)
        h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hLo : (((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) /
          ((6 / 2) * (6 / 2) + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((144 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 16) 9 (1 / 16) 0 1 144 1 16 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : (((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2))) =
            0 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : ((6 : Rat) / 2) * (6 / 2) + ((B - 1 : Nat) : Rat) * (((1 / 2 : Rat) / 2) * ((1 / 2 : Rat) / 2)) =
            9 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hLo]
      exact cross_lt_ge 0 1 144 1 1 1 49 1 (B0 := 3) (B := B)
        h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hMid : ((1 / 4 : Rat) + ((B - 1 : Nat) : Rat) * (1 / 16 : Rat)) /
          ((49 / 4 : Rat) + ((B - 1 : Nat) : Rat) * (1 / 16 : Rat)) =
          ((4 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((196 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int (1 / 4) (1 / 16) (49 / 4) (1 / 16) 4 1 196 1 16 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : (1 / 4 : Rat) + ((B - 1 : Nat) : Rat) * (1 / 16 : Rat) = (1 / 4 : Rat) + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (49 / 4 : Rat) + ((B - 1 : Nat) : Rat) * (1 / 16 : Rat) = (49 / 4 : Rat) + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hMid]
      exact cross_lt_ge 4 1 196 1 1 1 49 1 (B0 := 3) (B := B)
        h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem mxint6_vs_mxfp6_e2m3 :
    (∀ B : Nat, 2 ≤ B → B < 12 → omegaMxintAbsMax 6 B < omegaMxfpAbsMax mxfp6E2M3 B) ∧
    (∀ B : Nat, 12 ≤ B → omegaMxfpAbsMax mxfp6E2M3 B < omegaMxintAbsMax 6 B) ∧
    (∀ B : Nat, 1 ≤ B → B < 4 → omegaMxintE8M0 6 B < omegaMxfpE8M0 mxfp6E2M3 B) ∧
    (∀ B : Nat, 4 ≤ B → omegaMxfpE8M0 mxfp6E2M3 B < omegaMxintE8M0 6 B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B h2 h12
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp6E2M3 mxintMaxRat mxintMax
    have hInt : ((B - 1 : Nat) : Rat) / (4 * ((31 : Nat) : Rat) * ((31 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((3844 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    have hNorm : (((B - 1 : Nat) : Rat) * (1 / 16 : Rat)) /
        ((15 / 2) * (15 / 2) + ((B - 1 : Nat) : Rat) * ((17 / 4) * (17 / 4))) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((900 : Int) + (289 : Int) * ((B - 1 : Nat) : Rat)) := by
      have h := frac_eq_int 0 (1 / 16) (225 / 4) (289 / 16) 0 1 900 289 16 B (by decide) (by decide) (by grind) (by grind) (by grind)
      have h1 : ((B - 1 : Nat) : Rat) * (1 / 16 : Rat) = 0 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      have h2 : (15 / 2 : Rat) * (15 / 2) + ((B - 1 : Nat) : Rat) * ((17 / 4) * (17 / 4)) =
          (225 / 4 : Rat) + (289 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      rw [h2, h1]; exact h
    have hlt := cross_lt_range 0 1 3844 1 0 1 900 289 (Blo := 2) (Bhi := 11) (B := B)
      h2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hInt]; exact rat_lt_of_lt_of_le (by rw [← hNorm] at hlt; exact hlt) (le_ratMax_left _ _)
  · intro B h12
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp6E2M3 mxintMaxRat mxintMax
    have hInt : ((B - 1 : Nat) : Rat) / (4 * ((31 : Nat) : Rat) * ((31 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((3844 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    rw [hInt]
    apply ratMax_lt_iff.mpr
    constructor
    · have hNorm : (((B - 1 : Nat) : Rat) * (1 / 16 : Rat)) /
          ((15 / 2) * (15 / 2) + ((B - 1 : Nat) : Rat) * ((17 / 4) * (17 / 4))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((900 : Int) + (289 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 16) (225 / 4) (289 / 16) 0 1 900 289 16 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (1 / 16 : Rat) = 0 + (1 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (15 / 2 : Rat) * (15 / 2) + ((B - 1 : Nat) : Rat) * ((17 / 4) * (17 / 4)) =
            (225 / 4 : Rat) + (289 / 16 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hNorm]
      exact cross_lt_ge 0 1 900 289 0 1 3844 1 (B0 := 12) (B := B)
        h12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hSub : (((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2))) /
          ((15 / 2) * (15 / 2) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((14400 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 256) (225 / 4) (1 / 256) 0 1 14400 1 256 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2)) = 0 + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (15 / 2 : Rat) * (15 / 2) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2)) =
            (225 / 4 : Rat) + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hSub]
      exact cross_lt_ge 0 1 14400 1 0 1 3844 1 (B0 := 12) (B := B)
        h12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro B h1 h4
    unfold omegaMxintE8M0 omegaMxfpE8M0 mxfp6E2M3 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one h1; grind
    have hInt : (B : Rat) / (((31 : Nat) : Rat) * ((31 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((961 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    have hHi : ((1 / 16 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2))) /
        ((17 / 4) * (17 / 4) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2))) =
        ((16 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((4624 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      have h := frac_eq_int (1 / 16) (1 / 256) (289 / 16) (1 / 256) 16 1 4624 1 256 B (by decide) (by decide) (by grind) (by grind) (by grind)
      have h1 : (1 / 16 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2)) =
          (1 / 16 : Rat) + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      have h2 : (17 / 4 : Rat) * (17 / 4) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2)) =
          (289 / 16 : Rat) + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      rw [h2, h1]; exact h
    have hlt := cross_lt_range 1 1 961 1 16 1 4624 1 (Blo := 1) (Bhi := 3) (B := B)
      h1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hInt]; exact rat_lt_of_lt_of_le (by rw [← hHi] at hlt; exact hlt) (le_ratMax_left _ _)
  · intro B h4
    unfold omegaMxintE8M0 omegaMxfpE8M0 mxfp6E2M3 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one (by omega : 1 ≤ B); grind
    have hInt : (B : Rat) / (((31 : Nat) : Rat) * ((31 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((961 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    rw [hInt]
    apply ratMax_lt_iff.mpr
    constructor
    · have hHi : ((1 / 16 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2))) /
          ((17 / 4) * (17 / 4) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2))) =
          ((16 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((4624 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int (1 / 16) (1 / 256) (289 / 16) (1 / 256) 16 1 4624 1 256 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : (1 / 16 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2)) =
            (1 / 16 : Rat) + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (17 / 4 : Rat) * (17 / 4) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2)) =
            (289 / 16 : Rat) + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hHi]
      exact cross_lt_ge 16 1 4624 1 1 1 961 1 (B0 := 4) (B := B)
        h4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hLo : (((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2))) /
          (((15 / 2 : Rat) / 2) * ((15 / 2 : Rat) / 2) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((3600 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 256) (225 / 16) (1 / 256) 0 1 3600 1 256 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2)) = 0 + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : ((15 / 2 : Rat) / 2) * ((15 / 2 : Rat) / 2) + ((B - 1 : Nat) : Rat) * (((1 / 8 : Rat) / 2) * ((1 / 8 : Rat) / 2)) =
            (225 / 16 : Rat) + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hLo]
      exact cross_lt_ge 0 1 3600 1 1 1 961 1 (B0 := 4) (B := B)
        h4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem mxint6_vs_mxfp6_e3m2 :
    (∀ B : Nat, 2 ≤ B → B < 47 → omegaMxintAbsMax 6 B < omegaMxfpAbsMax mxfp6E3M2 B) ∧
    (∀ B : Nat, 47 ≤ B → omegaMxfpAbsMax mxfp6E3M2 B < omegaMxintAbsMax 6 B) ∧
    (∀ B : Nat, 1 ≤ B → B < 13 → omegaMxintE8M0 6 B < omegaMxfpE8M0 mxfp6E3M2 B) ∧
    (∀ B : Nat, 13 ≤ B → omegaMxfpE8M0 mxfp6E3M2 B < omegaMxintE8M0 6 B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B h2 h47
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp6E3M2 mxintMaxRat mxintMax
    have hInt : ((B - 1 : Nat) : Rat) / (4 * ((31 : Nat) : Rat) * ((31 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((3844 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    have hNorm : (((B - 1 : Nat) : Rat) * 4) / (28 * 28 + ((B - 1 : Nat) : Rat) * (18 * 18)) =
        ((0 : Int) + (4 : Int) * ((B - 1 : Nat) : Rat)) / ((784 : Int) + (324 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    have hlt := cross_lt_range 0 1 3844 1 0 4 784 324 (Blo := 2) (Bhi := 46) (B := B)
      h2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hInt]; exact rat_lt_of_lt_of_le (by rw [← hNorm] at hlt; exact hlt) (le_ratMax_left _ _)
  · intro B h47
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp6E3M2 mxintMaxRat mxintMax
    have hInt : ((B - 1 : Nat) : Rat) / (4 * ((31 : Nat) : Rat) * ((31 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((3844 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    rw [hInt]
    apply ratMax_lt_iff.mpr
    constructor
    · have hNorm : (((B - 1 : Nat) : Rat) * 4) / (28 * 28 + ((B - 1 : Nat) : Rat) * (18 * 18)) =
          ((0 : Int) + (4 : Int) * ((B - 1 : Nat) : Rat)) / ((784 : Int) + (324 : Int) * ((B - 1 : Nat) : Rat)) := by
        congr 1 <;> grind
      rw [hNorm]
      exact cross_lt_ge 0 4 784 324 0 1 3844 1 (B0 := 47) (B := B)
        h47 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hSub : (((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2))) /
          (28 * 28 + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((802816 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 1024) 784 (1 / 1024) 0 1 802816 1 1024 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2)) = 0 + (1 / 1024 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (28 : Rat) * 28 + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2)) =
            784 + (1 / 1024 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hSub]
      exact cross_lt_ge 0 1 802816 1 0 1 3844 1 (B0 := 47) (B := B)
        h47 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro B h1 h13
    unfold omegaMxintE8M0 omegaMxfpE8M0 mxfp6E3M2 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one h1; grind
    have hInt : (B : Rat) / (((31 : Nat) : Rat) * ((31 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((961 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    have hHi : (4 + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2))) /
        (18 * 18 + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2))) =
        ((4096 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((331776 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      have h := frac_eq_int 4 (1 / 1024) 324 (1 / 1024) 4096 1 331776 1 1024 B (by decide) (by decide) (by grind) (by grind) (by grind)
      have h1 : (4 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2)) =
          4 + (1 / 1024 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      have h2 : (18 : Rat) * 18 + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2)) =
          324 + (1 / 1024 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      rw [h2, h1]; exact h
    have hlt := cross_lt_range 1 1 961 1 4096 1 331776 1 (Blo := 1) (Bhi := 12) (B := B)
      h1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hInt]; exact rat_lt_of_lt_of_le (by rw [← hHi] at hlt; exact hlt) (le_ratMax_left _ _)
  · intro B h13
    unfold omegaMxintE8M0 omegaMxfpE8M0 mxfp6E3M2 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one (by omega : 1 ≤ B); grind
    have hInt : (B : Rat) / (((31 : Nat) : Rat) * ((31 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((961 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    rw [hInt]
    apply ratMax_lt_iff.mpr
    constructor
    · have hHi : (4 + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2))) /
          (18 * 18 + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2))) =
          ((4096 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((331776 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 4 (1 / 1024) 324 (1 / 1024) 4096 1 331776 1 1024 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : (4 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2)) =
            4 + (1 / 1024 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (18 : Rat) * 18 + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2)) =
            324 + (1 / 1024 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hHi]
      exact cross_lt_ge 4096 1 331776 1 1 1 961 1 (B0 := 13) (B := B)
        h13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hLo : (((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2))) /
          ((28 / 2) * (28 / 2) + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((200704 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 1024) 196 (1 / 1024) 0 1 200704 1 1024 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2)) = 0 + (1 / 1024 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : ((28 : Rat) / 2) * (28 / 2) + ((B - 1 : Nat) : Rat) * (((1 / 16 : Rat) / 2) * ((1 / 16 : Rat) / 2)) =
            196 + (1 / 1024 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hLo]
      exact cross_lt_ge 0 1 200704 1 1 1 961 1 (B0 := 13) (B := B)
        h13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem mxint8_vs_mxfp8_e4m3 :
    (∀ B : Nat, 2 ≤ B → B < 223 → omegaMxintAbsMax 8 B < omegaMxfpAbsMax mxfp8E4M3 B) ∧
    (∀ B : Nat, 223 ≤ B → omegaMxfpAbsMax mxfp8E4M3 B < omegaMxintAbsMax 8 B) ∧
    (∀ B : Nat, 1 ≤ B → B < 57 → omegaMxintE8M0 8 B < omegaMxfpE8M0 mxfp8E4M3 B) ∧
    (∀ B : Nat, 57 ≤ B → omegaMxfpE8M0 mxfp8E4M3 B < omegaMxintE8M0 8 B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B h2 h223
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp8E4M3 mxintMaxRat mxintMax
    have hInt : ((B - 1 : Nat) : Rat) / (4 * ((127 : Nat) : Rat) * ((127 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((64516 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    have hNorm : (((B - 1 : Nat) : Rat) * 256) / (448 * 448 + ((B - 1 : Nat) : Rat) * (272 * 272)) =
        ((0 : Int) + (256 : Int) * ((B - 1 : Nat) : Rat)) / ((200704 : Int) + (73984 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    have hlt := cross_lt_range 0 1 64516 1 0 256 200704 73984 (Blo := 2) (Bhi := 222) (B := B)
      h2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hInt]; exact rat_lt_of_lt_of_le (by rw [← hNorm] at hlt; exact hlt) (le_ratMax_left _ _)
  · intro B h223
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp8E4M3 mxintMaxRat mxintMax
    have hInt : ((B - 1 : Nat) : Rat) / (4 * ((127 : Nat) : Rat) * ((127 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((64516 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    rw [hInt]
    apply ratMax_lt_iff.mpr
    constructor
    · have hNorm : (((B - 1 : Nat) : Rat) * 256) / (448 * 448 + ((B - 1 : Nat) : Rat) * (272 * 272)) =
          ((0 : Int) + (256 : Int) * ((B - 1 : Nat) : Rat)) / ((200704 : Int) + (73984 : Int) * ((B - 1 : Nat) : Rat)) := by
        congr 1 <;> grind
      rw [hNorm]
      exact cross_lt_ge 0 256 200704 73984 0 1 64516 1 (B0 := 223) (B := B)
        h223 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hSub : (((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2))) /
          (448 * 448 + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((210453397504 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 1048576) 200704 (1 / 1048576) 0 1 210453397504 1 1048576 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2)) = 0 + (1 / 1048576 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (448 : Rat) * 448 + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2)) =
            200704 + (1 / 1048576 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hSub]
      exact cross_lt_ge 0 1 210453397504 1 0 1 64516 1 (B0 := 223) (B := B)
        h223 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro B h1 h57
    unfold omegaMxintE8M0 omegaMxfpE8M0 mxfp8E4M3 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one h1; grind
    have hInt : (B : Rat) / (((127 : Nat) : Rat) * ((127 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((16129 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    have hHi : (256 + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2))) /
        (272 * 272 + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2))) =
        ((268435456 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((77577846784 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      have h := frac_eq_int 256 (1 / 1048576) 73984 (1 / 1048576) 268435456 1 77577846784 1 1048576 B (by decide) (by decide) (by grind) (by grind) (by grind)
      have h1 : (256 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2)) =
          256 + (1 / 1048576 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      have h2 : (272 : Rat) * 272 + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2)) =
          73984 + (1 / 1048576 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      rw [h2, h1]; exact h
    have hlt := cross_lt_range 1 1 16129 1 268435456 1 77577846784 1 (Blo := 1) (Bhi := 56) (B := B)
      h1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hInt]; exact rat_lt_of_lt_of_le (by rw [← hHi] at hlt; exact hlt) (le_ratMax_left _ _)
  · intro B h57
    unfold omegaMxintE8M0 omegaMxfpE8M0 mxfp8E4M3 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one (by omega : 1 ≤ B); grind
    have hInt : (B : Rat) / (((127 : Nat) : Rat) * ((127 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((16129 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    rw [hInt]
    apply ratMax_lt_iff.mpr
    constructor
    · have hHi : (256 + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2))) /
          (272 * 272 + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2))) =
          ((268435456 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((77577846784 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 256 (1 / 1048576) 73984 (1 / 1048576) 268435456 1 77577846784 1 1048576 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : (256 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2)) =
            256 + (1 / 1048576 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (272 : Rat) * 272 + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2)) =
            73984 + (1 / 1048576 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hHi]
      exact cross_lt_ge 268435456 1 77577846784 1 1 1 16129 1 (B0 := 57) (B := B)
        h57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hLo : (((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2))) /
          ((448 / 2) * (448 / 2) + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((52613349376 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 1048576) 50176 (1 / 1048576) 0 1 52613349376 1 1048576 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2)) = 0 + (1 / 1048576 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : ((448 : Rat) / 2) * (448 / 2) + ((B - 1 : Nat) : Rat) * (((1 / 512 : Rat) / 2) * ((1 / 512 : Rat) / 2)) =
            50176 + (1 / 1048576 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hLo]
      exact cross_lt_ge 0 1 52613349376 1 1 1 16129 1 (B0 := 57) (B := B)
        h57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem mxint8_vs_mxfp8_e2m5 :
    (∀ B : Nat, 2 ≤ B → B < 13 → omegaMxintAbsMax 8 B < omegaMxfpAbsMax mxfp8E2M5 B) ∧
    (∀ B : Nat, 13 ≤ B → omegaMxfpAbsMax mxfp8E2M5 B < omegaMxintAbsMax 8 B) ∧
    (∀ B : Nat, 1 ≤ B → B < 5 → omegaMxintE8M0 8 B < omegaMxfpE8M0 mxfp8E2M5 B) ∧
    (∀ B : Nat, 5 ≤ B → omegaMxfpE8M0 mxfp8E2M5 B < omegaMxintE8M0 8 B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B h2 h13
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp8E2M5 mxintMaxRat mxintMax
    have hInt : ((B - 1 : Nat) : Rat) / (4 * ((127 : Nat) : Rat) * ((127 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((64516 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    have hNorm : (((B - 1 : Nat) : Rat) * (1 / 256 : Rat)) /
        ((63 / 8) * (63 / 8) + ((B - 1 : Nat) : Rat) * ((65 / 16) * (65 / 16))) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((15876 : Int) + (4225 : Int) * ((B - 1 : Nat) : Rat)) := by
      have h := frac_eq_int 0 (1 / 256) (3969 / 64) (4225 / 256) 0 1 15876 4225 256 B (by decide) (by decide) (by grind) (by grind) (by grind)
      have h1 : ((B - 1 : Nat) : Rat) * (1 / 256 : Rat) = 0 + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      have h2 : (63 / 8 : Rat) * (63 / 8) + ((B - 1 : Nat) : Rat) * ((65 / 16) * (65 / 16)) =
          (3969 / 64 : Rat) + (4225 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      rw [h2, h1]; exact h
    have hlt := cross_lt_range 0 1 64516 1 0 1 15876 4225 (Blo := 2) (Bhi := 12) (B := B)
      h2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hInt]; exact rat_lt_of_lt_of_le (by rw [← hNorm] at hlt; exact hlt) (le_ratMax_left _ _)
  · intro B h13
    unfold omegaMxintAbsMax omegaMxfpAbsMax mxfp8E2M5 mxintMaxRat mxintMax
    have hInt : ((B - 1 : Nat) : Rat) / (4 * ((127 : Nat) : Rat) * ((127 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((64516 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      congr 1 <;> grind
    rw [hInt]
    apply ratMax_lt_iff.mpr
    constructor
    · have hNorm : (((B - 1 : Nat) : Rat) * (1 / 256 : Rat)) /
          ((63 / 8) * (63 / 8) + ((B - 1 : Nat) : Rat) * ((65 / 16) * (65 / 16))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((15876 : Int) + (4225 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 256) (3969 / 64) (4225 / 256) 0 1 15876 4225 256 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (1 / 256 : Rat) = 0 + (1 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (63 / 8 : Rat) * (63 / 8) + ((B - 1 : Nat) : Rat) * ((65 / 16) * (65 / 16)) =
            (3969 / 64 : Rat) + (4225 / 256 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hNorm]
      exact cross_lt_ge 0 1 15876 4225 0 1 64516 1 (B0 := 13) (B := B)
        h13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hSub : (((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2))) /
          ((63 / 8) * (63 / 8) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((254016 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 4096) (3969 / 64) (1 / 4096) 0 1 254016 1 4096 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2)) = 0 + (1 / 4096 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (63 / 8 : Rat) * (63 / 8) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2)) =
            (3969 / 64 : Rat) + (1 / 4096 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hSub]
      exact cross_lt_ge 0 1 254016 1 0 1 64516 1 (B0 := 13) (B := B)
        h13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro B h1 h5
    unfold omegaMxintE8M0 omegaMxfpE8M0 mxfp8E2M5 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one h1; grind
    have hInt : (B : Rat) / (((127 : Nat) : Rat) * ((127 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((16129 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    have hHi : ((1 / 256 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2))) /
        ((65 / 16) * (65 / 16) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2))) =
        ((16 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((67600 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      have h := frac_eq_int (1 / 256) (1 / 4096) (4225 / 256) (1 / 4096) 16 1 67600 1 4096 B (by decide) (by decide) (by grind) (by grind) (by grind)
      have h1 : (1 / 256 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2)) =
          (1 / 256 : Rat) + (1 / 4096 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      have h2 : (65 / 16 : Rat) * (65 / 16) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2)) =
          (4225 / 256 : Rat) + (1 / 4096 : Rat) * ((B - 1 : Nat) : Rat) := by grind
      rw [h2, h1]; exact h
    have hlt := cross_lt_range 1 1 16129 1 16 1 67600 1 (Blo := 1) (Bhi := 4) (B := B)
      h1 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hInt]; exact rat_lt_of_lt_of_le (by rw [← hHi] at hlt; exact hlt) (le_ratMax_left _ _)
  · intro B h5
    unfold omegaMxintE8M0 omegaMxfpE8M0 mxfp8E2M5 mxintMaxRat mxintMax
    have hBeq : (B : Rat) = (1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat) := by
      have := natCast_pred_add_one (by omega : 1 ≤ B); grind
    have hInt : (B : Rat) / (((127 : Nat) : Rat) * ((127 : Nat) : Rat) + ((B - 1 : Nat) : Rat)) =
        ((1 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((16129 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
      rw [hBeq]; congr 1; grind
    rw [hInt]
    apply ratMax_lt_iff.mpr
    constructor
    · have hHi : ((1 / 256 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2))) /
          ((65 / 16) * (65 / 16) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2))) =
          ((16 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((67600 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int (1 / 256) (1 / 4096) (4225 / 256) (1 / 4096) 16 1 67600 1 4096 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : (1 / 256 : Rat) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2)) =
            (1 / 256 : Rat) + (1 / 4096 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : (65 / 16 : Rat) * (65 / 16) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2)) =
            (4225 / 256 : Rat) + (1 / 4096 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hHi]
      exact cross_lt_ge 16 1 67600 1 1 1 16129 1 (B0 := 5) (B := B)
        h5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hLo : (((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2))) /
          (((63 / 8 : Rat) / 2) * ((63 / 8 : Rat) / 2) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2))) =
          ((0 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) / ((63504 : Int) + (1 : Int) * ((B - 1 : Nat) : Rat)) := by
        have h := frac_eq_int 0 (1 / 4096) (3969 / 256) (1 / 4096) 0 1 63504 1 4096 B (by decide) (by decide) (by grind) (by grind) (by grind)
        have h1 : ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2)) = 0 + (1 / 4096 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        have h2 : ((63 / 8 : Rat) / 2) * ((63 / 8 : Rat) / 2) + ((B - 1 : Nat) : Rat) * (((1 / 32 : Rat) / 2) * ((1 / 32 : Rat) / 2)) =
            (3969 / 256 : Rat) + (1 / 4096 : Rat) * ((B - 1 : Nat) : Rat) := by grind
        rw [h2, h1]; exact h
      rw [hLo]
      exact cross_lt_ge 0 1 63504 1 1 1 16129 1 (B0 := 5) (B := B)
        h5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Theorem 2 (`mxint_vs_mxfp_exact_blocksize_crossover`)**:
    Universal `MXFP` Continuous AbsMax upper bound plus exact all-`B` integer block-size
    crossovers `B*(w)` for `MXINT_w` vs `MXFP_w` under BOTH Continuous AbsMax and OCP `E8M0`,
    proving in particular that `MXINT8` strictly beats OCP `MXFP8-E4M3` at BOTH `B = 16` and `B = 32`. -/
theorem mxint_vs_mxfp_exact_blocksize_crossover :
    (∀ (spec : MxfpSpec),
      (0 : Rat) < spec.M → (0 : Rat) < spec.rhoNorm → spec.rhoNorm < 1 →
      spec.eHi = spec.rhoNorm * (spec.vHi * spec.vHi) → (0 : Rat) ≤ spec.eHi →
      ∀ (B : Nat), 1 ≤ B → ∀ (u e : Fin B → Rat) (i0 : Fin B),
        ratAbs (u i0) = spec.M → e i0 = 0 → IsMxfpErr spec u e →
        finSum e / l2NormSq u ≤ omegaMxfpAbsMax spec B) ∧
    ((∀ B : Nat, 2 ≤ B → B < 8 → omegaMxintAbsMax 4 B < omegaMxfpAbsMax mxfp4E2M1 B) ∧
     (∀ B : Nat, 8 ≤ B → omegaMxfpAbsMax mxfp4E2M1 B < omegaMxintAbsMax 4 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 3 → omegaMxintE8M0 4 B < omegaMxfp4E2M1E8M0 B) ∧
     (∀ B : Nat, 3 ≤ B → omegaMxfp4E2M1E8M0 B < omegaMxintE8M0 4 B)) ∧
    ((∀ B : Nat, 2 ≤ B → B < 12 → omegaMxintAbsMax 6 B < omegaMxfpAbsMax mxfp6E2M3 B) ∧
     (∀ B : Nat, 12 ≤ B → omegaMxfpAbsMax mxfp6E2M3 B < omegaMxintAbsMax 6 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 4 → omegaMxintE8M0 6 B < omegaMxfpE8M0 mxfp6E2M3 B) ∧
     (∀ B : Nat, 4 ≤ B → omegaMxfpE8M0 mxfp6E2M3 B < omegaMxintE8M0 6 B)) ∧
    ((∀ B : Nat, 2 ≤ B → B < 47 → omegaMxintAbsMax 6 B < omegaMxfpAbsMax mxfp6E3M2 B) ∧
     (∀ B : Nat, 47 ≤ B → omegaMxfpAbsMax mxfp6E3M2 B < omegaMxintAbsMax 6 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 13 → omegaMxintE8M0 6 B < omegaMxfpE8M0 mxfp6E3M2 B) ∧
     (∀ B : Nat, 13 ≤ B → omegaMxfpE8M0 mxfp6E3M2 B < omegaMxintE8M0 6 B)) ∧
    ((∀ B : Nat, 2 ≤ B → B < 223 → omegaMxintAbsMax 8 B < omegaMxfpAbsMax mxfp8E4M3 B) ∧
     (∀ B : Nat, 223 ≤ B → omegaMxfpAbsMax mxfp8E4M3 B < omegaMxintAbsMax 8 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 57 → omegaMxintE8M0 8 B < omegaMxfpE8M0 mxfp8E4M3 B) ∧
     (∀ B : Nat, 57 ≤ B → omegaMxfpE8M0 mxfp8E4M3 B < omegaMxintE8M0 8 B) ∧
     omegaMxintAbsMax 8 16 < omegaMxfpAbsMax mxfp8E4M3 16 ∧
     omegaMxintAbsMax 8 32 < omegaMxfpAbsMax mxfp8E4M3 32 ∧
     omegaMxintE8M0 8 16 < omegaMxfpE8M0 mxfp8E4M3 16 ∧
     omegaMxintE8M0 8 32 < omegaMxfpE8M0 mxfp8E4M3 32) ∧
    ((∀ B : Nat, 2 ≤ B → B < 13 → omegaMxintAbsMax 8 B < omegaMxfpAbsMax mxfp8E2M5 B) ∧
     (∀ B : Nat, 13 ≤ B → omegaMxfpAbsMax mxfp8E2M5 B < omegaMxintAbsMax 8 B) ∧
     (∀ B : Nat, 1 ≤ B → B < 5 → omegaMxintE8M0 8 B < omegaMxfpE8M0 mxfp8E2M5 B) ∧
     (∀ B : Nat, 5 ≤ B → omegaMxfpE8M0 mxfp8E2M5 B < omegaMxintE8M0 8 B)) := by
  refine ⟨?_, ?_, mxint6_vs_mxfp6_e2m3, mxint6_vs_mxfp6_e3m2, ?_, mxint8_vs_mxfp8_e2m5⟩
  · intro spec hM hRhoPos hRhoLt1 hEhiEq hEhiNN B hB u e i0 ha he herr
    exact mxfp_absmax_upper spec hM hRhoPos hRhoLt1 hEhiEq hEhiNN hB u e i0 ha he herr
  · exact ⟨mxint4_vs_mxfp4_absmax.1, mxint4_vs_mxfp4_absmax.2,
           mxint4_vs_mxfp4_e8m0.1, mxint4_vs_mxfp4_e8m0.2⟩
  · rcases mxint8_vs_mxfp8_e4m3 with ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4,
      h1 16 (by decide) (by decide), h1 32 (by decide) (by decide),
      h3 16 (by decide) (by decide), h3 32 (by decide) (by decide)⟩

end MxintMxfpSwar
