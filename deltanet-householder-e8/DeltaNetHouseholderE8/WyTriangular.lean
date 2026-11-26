/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltaNetHouseholderE8.RatOrder

/-!
# Theorem 4: Exact WY Triangular Inverse & Linear `ℓ_1`-Norm Growth (`‖T‖_∞ = 2C - 1`)

Proves that for aligned unit keys (`K K^T = 1 1^T`) at `β = 2`, the WY triangular
matrix `A = I + 2 * strictLower(1 1^T)` has exact two-sided inverse
`T_{i, j} = (-1)^{i - j} * 2` for `i > j` (`1` on diagonal, `0` above),
with exact row `ℓ_1`-norm `2 * i + 1` and exact matrix `∞`-norm `‖T‖_∞ = 2C - 1`
(`127` at chunk size `C = 64`).
-/

namespace DeltaNetHouseholderE8

def altSign (d : Nat) : Rat :=
  if d % 2 = 0 then 1 else -1

theorem altSign_zero : altSign 0 = 1 := by decide

theorem altSign_succ (d : Nat) : altSign (d + 1) = -altSign d := by
  unfold altSign
  by_cases h : d % 2 = 0
  · have h1 : (d + 1) % 2 ≠ 0 := by omega
    simp [h, h1]
  · have h1 : (d + 1) % 2 = 0 := by omega
    simp [h, h1]

theorem wyAlignedInv_eq_altSign {C : Nat} {i j : Fin C} (hlt : j.val < i.val) :
    wyAlignedInv C i j = 2 * altSign (i.val - j.val) := by
  unfold wyAlignedInv altSign
  have hne : i.val ≠ j.val := Nat.ne_of_gt hlt
  simp only [hne, ite_false, hlt, ite_true]
  split <;> grind

theorem finSumAux_wy_AT (C : Nat) (i j : Fin C) (k : Nat) (hk : k ≤ C) :
    finSumAux k (fun l => wyAlignedMat C i ⟨l.val, Nat.lt_of_lt_of_le l.isLt hk⟩ *
      wyAlignedInv C ⟨l.val, Nat.lt_of_lt_of_le l.isLt hk⟩ j) =
      if i.val < j.val then 0
      else if i.val = j.val then (if i.val < k then 1 else 0)
      else if k ≤ j.val then 0
      else if k ≤ i.val then 2 * altSign (k - 1 - j.val)
      else 0 := by
  induction k with
  | zero =>
    simp only [finSumAux]
    split
    · rfl
    · split
      · simp
      · simp
  | succ k ih =>
    have hk_le : k ≤ C := Nat.le_of_succ_le hk
    have hk_lt : k < C := hk
    simp only [finSumAux]
    rw [ih hk_le]
    by_cases hij_lt : i.val < j.val
    · simp only [hij_lt, ite_true]
      have hterm : wyAlignedMat C i ⟨k, hk_lt⟩ * wyAlignedInv C ⟨k, hk_lt⟩ j = 0 := by
        unfold wyAlignedMat wyAlignedInv
        by_cases hki : k ≤ i.val
        · have hkj : k < j.val := Nat.lt_of_le_of_lt hki hij_lt
          have hne : k ≠ j.val := Nat.ne_of_lt hkj
          have hnlt : ¬(j.val < k) := by omega
          simp [hne, hnlt]
        · have hne : i.val ≠ k := by omega
          have hnlt : ¬(k < i.val) := by omega
          simp [hne, hnlt]
      rw [hterm, Rat.zero_add]
    · by_cases hij_eq : i.val = j.val
      · simp only [hij_eq, ite_false, ite_true, Nat.lt_irrefl]
        by_cases hjk : j.val < k
        · have hjk' : j.val < k + 1 := Nat.lt_succ_of_lt hjk
          simp only [hjk, hjk', ite_true]
          have hne : i.val ≠ k := by omega
          have hnlt : ¬(k < i.val) := by omega
          have hterm : wyAlignedMat C i ⟨k, hk_lt⟩ * wyAlignedInv C ⟨k, hk_lt⟩ j = 0 := by
            unfold wyAlignedMat; simp [hne, hnlt]
          rw [hterm, Rat.add_zero]
        · by_cases hkj : k = j.val
          · have hjk' : j.val < k + 1 := by omega
            simp only [hjk, hjk', ite_false, ite_true]
            have hterm : wyAlignedMat C i ⟨k, hk_lt⟩ * wyAlignedInv C ⟨k, hk_lt⟩ j = 1 := by
              unfold wyAlignedMat wyAlignedInv
              simp [hkj, hij_eq]
            rw [hterm, Rat.zero_add]
          · have hjk' : ¬(j.val < k + 1) := by omega
            simp only [hjk, hjk', ite_false]
            have hne : k ≠ j.val := by omega
            have hnlt : ¬(j.val < k) := by omega
            have hterm : wyAlignedMat C i ⟨k, hk_lt⟩ * wyAlignedInv C ⟨k, hk_lt⟩ j = 0 := by
              unfold wyAlignedInv; simp [hne, hnlt]
            rw [hterm, Rat.zero_add]
      · have hji : j.val < i.val := by omega
        simp only [hij_lt, hij_eq, ite_false]
        by_cases hkj : k + 1 ≤ j.val
        · have hkj0 : k ≤ j.val := by omega
          simp only [hkj, hkj0, ite_true]
          have hne : k ≠ j.val := by omega
          have hnlt : ¬(j.val < k) := by omega
          have hterm : wyAlignedMat C i ⟨k, hk_lt⟩ * wyAlignedInv C ⟨k, hk_lt⟩ j = 0 := by
            unfold wyAlignedInv; simp [hne, hnlt]
          rw [hterm, Rat.zero_add]
        · by_cases hkj_eq : k = j.val
          · have hkj0 : k ≤ j.val := by omega
            have hki1 : k + 1 ≤ i.val := by omega
            simp only [hkj, hkj0, hki1, ite_false, ite_true]
            have hne : i.val ≠ k := by omega
            have hlt : k < i.val := by omega
            have hterm : wyAlignedMat C i ⟨k, hk_lt⟩ * wyAlignedInv C ⟨k, hk_lt⟩ j = 2 := by
              unfold wyAlignedMat wyAlignedInv
              simp [hij_eq, hji, hkj_eq]
            have hsub : k + 1 - 1 - j.val = 0 := by omega
            rw [hterm, Rat.zero_add, hsub, altSign_zero, Rat.mul_one]
          · have hjk : j.val < k := by omega
            have hkj0 : ¬(k ≤ j.val) := by omega
            simp only [hkj, hkj0, ite_false]
            by_cases hki1 : k + 1 ≤ i.val
            · have hki0 : k ≤ i.val := by omega
              simp only [hki1, hki0, ite_true]
              have hne : i.val ≠ k := by omega
              have hlt : k < i.val := by omega
              have hA : wyAlignedMat C i ⟨k, hk_lt⟩ = 2 := by
                unfold wyAlignedMat; simp [hne, hlt]
              have hT : wyAlignedInv C ⟨k, hk_lt⟩ j = 2 * altSign (k - j.val) :=
                wyAlignedInv_eq_altSign hjk
              rw [hA, hT]
              have hd : k - j.val = (k - 1 - j.val) + 1 := by omega
              have hd2 : k + 1 - 1 - j.val = (k - 1 - j.val) + 1 := by omega
              rw [hd, hd2, altSign_succ]
              grind
            · by_cases hki_eq : k = i.val
              · have hki0 : k ≤ i.val := by omega
                simp only [hki1, hki0, ite_false, ite_true]
                have hA : wyAlignedMat C i ⟨k, hk_lt⟩ = 1 := by
                  unfold wyAlignedMat; simp [hki_eq]
                have hT : wyAlignedInv C ⟨k, hk_lt⟩ j = 2 * altSign (k - j.val) :=
                  wyAlignedInv_eq_altSign hjk
                rw [hA, hT]
                have hd : k - j.val = (k - 1 - j.val) + 1 := by omega
                rw [hd, altSign_succ]
                grind
              · have hki0 : ¬(k ≤ i.val) := by omega
                simp only [hki1, hki0, ite_false]
                have hne : i.val ≠ k := by omega
                have hnlt : ¬(k < i.val) := by omega
                have hA : wyAlignedMat C i ⟨k, hk_lt⟩ = 0 := by
                  unfold wyAlignedMat; simp [hne, hnlt]
                rw [hA, Rat.zero_mul, Rat.zero_add]

theorem finSumAux_wy_TA (C : Nat) (i j : Fin C) (k : Nat) (hk : k ≤ C) :
    finSumAux k (fun l => wyAlignedInv C i ⟨l.val, Nat.lt_of_lt_of_le l.isLt hk⟩ *
      wyAlignedMat C ⟨l.val, Nat.lt_of_lt_of_le l.isLt hk⟩ j) =
      if i.val < j.val then 0
      else if i.val = j.val then (if i.val < k then 1 else 0)
      else if k ≤ j.val then 0
      else if k ≤ i.val then -2 * altSign (i.val - k)
      else 0 := by
  induction k with
  | zero =>
    simp only [finSumAux]
    split
    · rfl
    · split
      · simp
      · simp
  | succ k ih =>
    have hk_le : k ≤ C := Nat.le_of_succ_le hk
    have hk_lt : k < C := hk
    simp only [finSumAux]
    rw [ih hk_le]
    by_cases hij_lt : i.val < j.val
    · simp only [hij_lt, ite_true]
      have hterm : wyAlignedInv C i ⟨k, hk_lt⟩ * wyAlignedMat C ⟨k, hk_lt⟩ j = 0 := by
        unfold wyAlignedInv wyAlignedMat
        by_cases hki : k ≤ i.val
        · have hkj : k < j.val := Nat.lt_of_le_of_lt hki hij_lt
          have hne : k ≠ j.val := Nat.ne_of_lt hkj
          have hnlt : ¬(j.val < k) := by omega
          simp [hne, hnlt]
        · have hne : i.val ≠ k := by omega
          have hnlt : ¬(k < i.val) := by omega
          simp [hne, hnlt]
      rw [hterm, Rat.zero_add]
    · by_cases hij_eq : i.val = j.val
      · simp only [hij_eq, ite_false, ite_true, Nat.lt_irrefl]
        by_cases hjk : j.val < k
        · have hjk' : j.val < k + 1 := Nat.lt_succ_of_lt hjk
          simp only [hjk, hjk', ite_true]
          have hne : i.val ≠ k := by omega
          have hnlt : ¬(k < i.val) := by omega
          have hterm : wyAlignedInv C i ⟨k, hk_lt⟩ * wyAlignedMat C ⟨k, hk_lt⟩ j = 0 := by
            unfold wyAlignedInv; simp [hne, hnlt]
          rw [hterm, Rat.add_zero]
        · by_cases hkj : k = j.val
          · have hjk' : j.val < k + 1 := by omega
            simp only [hjk, hjk', ite_false, ite_true]
            have hterm : wyAlignedInv C i ⟨k, hk_lt⟩ * wyAlignedMat C ⟨k, hk_lt⟩ j = 1 := by
              unfold wyAlignedInv wyAlignedMat
              simp [hkj, hij_eq]
            rw [hterm, Rat.zero_add]
          · have hjk' : ¬(j.val < k + 1) := by omega
            simp only [hjk, hjk', ite_false]
            have hne : k ≠ j.val := by omega
            have hnlt : ¬(j.val < k) := by omega
            have hterm : wyAlignedInv C i ⟨k, hk_lt⟩ * wyAlignedMat C ⟨k, hk_lt⟩ j = 0 := by
              unfold wyAlignedMat; simp [hne, hnlt]
            rw [hterm, Rat.zero_add]
      · have hji : j.val < i.val := by omega
        simp only [hij_lt, hij_eq, ite_false]
        by_cases hkj : k + 1 ≤ j.val
        · have hkj0 : k ≤ j.val := by omega
          simp only [hkj, hkj0, ite_true]
          have hne : k ≠ j.val := by omega
          have hnlt : ¬(j.val < k) := by omega
          have hterm : wyAlignedInv C i ⟨k, hk_lt⟩ * wyAlignedMat C ⟨k, hk_lt⟩ j = 0 := by
            unfold wyAlignedMat; simp [hne, hnlt]
          rw [hterm, Rat.zero_add]
        · by_cases hkj_eq : k = j.val
          · have hkj0 : k ≤ j.val := by omega
            have hki1 : k + 1 ≤ i.val := by omega
            simp only [hkj, hkj0, hki1, ite_false, ite_true]
            have hki_lt : k < i.val := by omega
            have hT : wyAlignedInv C i ⟨k, hk_lt⟩ = 2 * altSign (i.val - k) :=
              wyAlignedInv_eq_altSign hki_lt
            have hA : wyAlignedMat C ⟨k, hk_lt⟩ j = 1 := by
              unfold wyAlignedMat; simp [hkj_eq]
            rw [hT, hA, Rat.mul_one, Rat.zero_add]
            have hd : i.val - k = (i.val - (k + 1)) + 1 := by omega
            rw [hd, altSign_succ]
            grind
          · have hjk : j.val < k := by omega
            have hkj0 : ¬(k ≤ j.val) := by omega
            simp only [hkj, hkj0, ite_false]
            by_cases hki1 : k + 1 ≤ i.val
            · have hki0 : k ≤ i.val := by omega
              simp only [hki1, hki0, ite_true]
              have hki_lt : k < i.val := by omega
              have hT : wyAlignedInv C i ⟨k, hk_lt⟩ = 2 * altSign (i.val - k) :=
                wyAlignedInv_eq_altSign hki_lt
              have hne : k ≠ j.val := by omega
              have hA : wyAlignedMat C ⟨k, hk_lt⟩ j = 2 := by
                unfold wyAlignedMat; simp [hne, hjk]
              rw [hT, hA]
              have hd : i.val - k = (i.val - (k + 1)) + 1 := by omega
              rw [hd, altSign_succ]
              grind
            · by_cases hki_eq : k = i.val
              · have hki0 : k ≤ i.val := by omega
                simp only [hki1, hki0, ite_false, ite_true]
                have hT : wyAlignedInv C i ⟨k, hk_lt⟩ = 1 := by
                  unfold wyAlignedInv; simp [hki_eq]
                have hne : k ≠ j.val := by omega
                have hA : wyAlignedMat C ⟨k, hk_lt⟩ j = 2 := by
                  unfold wyAlignedMat; simp [hne, hjk]
                have hsub : i.val - k = 0 := by omega
                rw [hT, hA, hsub, altSign_zero]
                grind
              · have hki0 : ¬(k ≤ i.val) := by omega
                simp only [hki1, hki0, ite_false]
                have hne : i.val ≠ k := by omega
                have hnlt : ¬(k < i.val) := by omega
                have hT : wyAlignedInv C i ⟨k, hk_lt⟩ = 0 := by
                  unfold wyAlignedInv; simp [hne, hnlt]
                rw [hT, Rat.zero_mul, Rat.zero_add]

theorem wy_matMul_right_inv (C : Nat) (i j : Fin C) :
    matMul (wyAlignedMat C) (wyAlignedInv C) i j = identityMat C i j := by
  unfold matMul finSum identityMat
  have h := finSumAux_wy_AT C i j C (Nat.le_refl C)
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [i.isLt]
  · have hval : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
    by_cases hlt : i.val < j.val
    · simp [hij, hlt]
    · have h1 : ¬(C ≤ j.val) := Nat.not_le.mpr j.isLt
      have h2 : ¬(C ≤ i.val) := Nat.not_le.mpr i.isLt
      simp [hij, hlt, hval, h1, h2]

theorem wy_matMul_left_inv (C : Nat) (i j : Fin C) :
    matMul (wyAlignedInv C) (wyAlignedMat C) i j = identityMat C i j := by
  unfold matMul finSum identityMat
  have h := finSumAux_wy_TA C i j C (Nat.le_refl C)
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [i.isLt]
  · have hval : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
    by_cases hlt : i.val < j.val
    · simp [hij, hlt]
    · have h1 : ¬(C ≤ j.val) := Nat.not_le.mpr j.isLt
      have h2 : ¬(C ≤ i.val) := Nat.not_le.mpr i.isLt
      simp [hij, hlt, hval, h1, h2]

theorem finSumAux_wy_rowL1 (C : Nat) (i : Fin C) (k : Nat) (hk : k ≤ C) :
    finSumAux k (fun j => ratAbs (wyAlignedInv C i ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)) =
      if k ≤ i.val then 2 * (k : Rat) else 2 * (i.val : Rat) + 1 := by
  induction k with
  | zero =>
    simp [finSumAux]
  | succ k ih =>
    have hk_le : k ≤ C := Nat.le_of_succ_le hk
    have hk_lt : k < C := hk
    simp only [finSumAux]
    rw [ih hk_le]
    by_cases hki1 : k + 1 ≤ i.val
    · have hki0 : k ≤ i.val := by omega
      simp only [hki1, hki0, ite_true]
      have hlt : k < i.val := by omega
      have hne : i.val ≠ k := by omega
      have habs : ratAbs (wyAlignedInv C i ⟨k, hk_lt⟩) = 2 := by
        unfold wyAlignedInv
        simp only [hne, ite_false, hlt, ite_true]
        split <;> decide
      rw [habs, Rat.natCast_add]
      grind
    · by_cases hki_eq : k = i.val
      · have hki0 : k ≤ i.val := by omega
        simp only [hki1, hki0, ite_false, ite_true]
        have habs : ratAbs (wyAlignedInv C i ⟨k, hk_lt⟩) = 1 := by
          unfold wyAlignedInv
          simp only [hki_eq, ite_true]
          exact ratAbs_of_nonneg (by decide)
        rw [habs, hki_eq]
      · have hki0 : ¬(k ≤ i.val) := by omega
        simp only [hki1, hki0, ite_false]
        have hne : i.val ≠ k := by omega
        have hnlt : ¬(k < i.val) := by omega
        have habs : ratAbs (wyAlignedInv C i ⟨k, hk_lt⟩) = 0 := by
          unfold wyAlignedInv
          simp [hne, hnlt, ratAbs]
        rw [habs, Rat.add_zero]

theorem wy_rowL1Norm_eq (C : Nat) (i : Fin C) :
    rowL1Norm (wyAlignedInv C) i = 2 * (i.val : Rat) + 1 := by
  unfold rowL1Norm finSum
  have h := finSumAux_wy_rowL1 C i C (Nat.le_refl C)
  rw [h]
  have hnot : ¬(C ≤ i.val) := Nat.not_le.mpr i.isLt
  simp [hnot]

/-- Headline Theorem 4 (`wy_triangular_inverse_norm_growth_exact`). -/
theorem wy_triangular_inverse_norm_growth_exact :
    (∀ (C : Nat) (i j : Fin C),
      matMul (wyAlignedMat C) (wyAlignedInv C) i j = identityMat C i j ∧
      matMul (wyAlignedInv C) (wyAlignedMat C) i j = identityMat C i j) ∧
    (∀ (C : Nat) (i j : Fin C), j.val < i.val →
      wyAlignedInv C i j = if (i.val - j.val) % 2 = 0 then 2 else -2) ∧
    (∀ (C : Nat) (i : Fin C),
      rowL1Norm (wyAlignedInv C) i = 2 * (i.val : Rat) + 1) ∧
    (∀ (C : Nat) (hC : 0 < C),
      (∀ i : Fin C, rowL1Norm (wyAlignedInv C) i ≤ 2 * (C : Rat) - 1) ∧
      rowL1Norm (wyAlignedInv C) ⟨C - 1, Nat.sub_lt hC (by decide)⟩ = 2 * (C : Rat) - 1) ∧
    (rowL1Norm (wyAlignedInv 64) ⟨63, by decide⟩ = 127) := by
  refine ⟨fun C i j => ⟨wy_matMul_right_inv C i j, wy_matMul_left_inv C i j⟩,
    ?_, wy_rowL1Norm_eq, ?_, ?_⟩
  · intro C i j hlt
    unfold wyAlignedInv
    have hne : i.val ≠ j.val := Nat.ne_of_gt hlt
    simp [hne, hlt]
  · intro C hC
    have hCcast : (C : Rat) = ((C - 1 : Nat) : Rat) + 1 := by
      have h : C = (C - 1) + 1 := (Nat.sub_add_cancel hC).symm
      calc
        (C : Rat) = (((C - 1) + 1 : Nat) : Rat) := by rw [← h]
        _ = ((C - 1 : Nat) : Rat) + 1 := by rw [Rat.natCast_add]; rfl
    constructor
    · intro i
      rw [wy_rowL1Norm_eq, hCcast]
      have hle : (i.val : Rat) ≤ ((C - 1 : Nat) : Rat) :=
        rat_natCast_le (Nat.le_sub_one_of_lt i.isLt)
      have hmul := rat_mul_le_mul_of_nonneg_left hle (by decide : (0 : Rat) ≤ 2)
      have hadd := rat_add_le_add hmul (Rat.le_refl (a := (1 : Rat)))
      have heq : 2 * (((C - 1 : Nat) : Rat) + 1) - 1 = 2 * ((C - 1 : Nat) : Rat) + 1 := by grind
      rw [heq]; exact hadd
    · rw [wy_rowL1Norm_eq, hCcast]
      grind
  · rw [wy_rowL1Norm_eq]
    grind

end DeltaNetHouseholderE8
