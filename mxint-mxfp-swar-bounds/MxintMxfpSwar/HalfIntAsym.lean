/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxintMxfpSwar.RatOrder

/-!
# Theorems 4 & 5: Zero-Free Half-Integer `O(1/B)` Collapse & Asymmetric `MXINT4 [-8, 7]` Crossover

Proves:
4. `half_integer_zero_free_o_one_over_b_collapse`: Exact unrescaled AbsMax divergence,
   exact `O(1/B)` optimal-rescaled contraction collapse `α = (2^w - 1)^2 / ((2^w - 1)^2 + B - 1)`,
   and exact OCP `E8M0` divergence thresholds `B_div^E8M0(w) = 4^(w-1) - 2^(w-1) + 1`
   (`{3, 13, 57, 993, 16257}` for `w ∈ {2, 3, 4, 6, 8}`).
5. `mxint4_asym_beats_sym_crossover_b16`: Asymmetric `MXINT4 [-8, 7]` ties symmetric `[-7, 7]`
   at exact `B = 15` (`1/15`) and strictly beats it for ALL `B ≥ 16`, signed-scale asymmetric
   beats symmetric for all `B ≥ 2`, plus the exact OCP `E8M0` `7 vs 8` scale-cliff `4×` MSE penalty.
-/

namespace MxintMxfpSwar

/-! ### Helper Lemmas for Theorem 4 -/

private theorem two_pow_sub_one_pos {w : Nat} (hw : 2 ≤ w) : 1 ≤ 2 ^ w - 1 := by
  have h1 : 4 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    omega
  omega

private theorem two_pow_sub_one_sq_pos {w : Nat} (hw : 2 ≤ w) :
    (0 : Rat) < ((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat) := by
  have h1 : (0 : Rat) < ((2 ^ w - 1 : Nat) : Rat) := rat_natCast_pos (two_pow_sub_one_pos hw)
  exact rat_mul_pos h1 h1

private theorem halfDivE8M0_identity {w : Nat} (hw : 2 ≤ w) :
    4 * halfDivE8M0 w - 3 = (2 ^ w - 1) * (2 ^ w - 1) := by
  unfold halfDivE8M0
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    have : w = (w - 1) + 1 := by omega
    conv => lhs; rw [this]
    rw [Nat.pow_succ, Nat.mul_comm]
  have h4 : 4 ^ (w - 1) = 2 ^ (w - 1) * 2 ^ (w - 1) := by
    have : (4 : Nat) = 2 * 2 := by decide
    rw [this, Nat.mul_pow]
  have hp1 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_pow _ _ (by decide)
  rw [h2, h4]
  let k := 2 ^ (w - 1)
  let m := k - 1
  have hk : k = m + 1 := by omega
  have h1 : 2 * k - 1 = 2 * m + 1 := by omega
  have h3 : k * k - k + 1 = m * m + m + 1 := by
    have hk2 : k * k = m * m + 2 * m + 1 := by rw [hk]; grind
    omega
  change 4 * (k * k - k + 1) - 3 = (2 * k - 1) * (2 * k - 1)
  rw [h1, h3]
  have hsq : (2 * m + 1) * (2 * m + 1) = 4 * (m * m) + 4 * m + 1 := by grind
  rw [hsq]
  have h4m : 4 * (m * m + m + 1) = 4 * (m * m) + 4 * m + 4 := by grind
  rw [h4m]
  omega

/-- **Theorem 4 (`half_integer_zero_free_o_one_over_b_collapse`)**:
    Proves that zero-free half-integer `MXINT_w` (`±1/2, ..., ±(2^w - 1)/2`) suffers:
    - Exact unrescaled AbsMax defect `(B - 1) / (2^w - 1)^2` attained on `(M, 0, ..., 0)`,
      diverging (`ω ≥ 1`) iff `B ≥ (2^w - 1)^2 + 1`;
    - Exact optimal-rescaled `O(1/B)` contraction collapse
      `α_rescaled(w, B) = (2^w - 1)^2 / ((2^w - 1)^2 + B - 1) < (2^w - 1)^2 / (B - 1)`
      and vanishing below any `ε > 0`;
    - Exact OCP `E8M0` defect `(4B - 3) / (2^w - 1)^2` attained on `(M/2, 0, ..., 0)`,
      diverging (`ω ≥ 1`) iff `B ≥ 4^(w-1) - 2^(w-1) + 1`, with exact thresholds
      `{3, 13, 57, 993, 16257}` for `w ∈ {2, 3, 4, 6, 8}`. -/
theorem half_integer_zero_free_o_one_over_b_collapse :
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      let u : Fin B → Rat := fun j => if j.val = 0 then halfIntMax w else 0
      let e : Fin B → Rat := fun j => if j.val = 0 then 0 else 1 / 4
      finSum e / l2NormSq u = omegaHalfAbsMax w B ∧
      ((1 : Rat) ≤ omegaHalfAbsMax w B ↔ (2 ^ w - 1) * (2 ^ w - 1) + 1 ≤ B)) ∧
    (∀ (w B : Nat), 2 ≤ w → 2 ≤ B →
      alphaHalfRescaled w B < ((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat) /
        ((B - 1 : Nat) : Rat)) ∧
    (∀ (w : Nat), 2 ≤ w → ∀ (ε : Rat), (0 : Rat) < ε →
      ∃ B : Nat, 1 ≤ B ∧ alphaHalfRescaled w B < ε) ∧
    (∀ (w B : Nat), 2 ≤ w → 1 ≤ B →
      let u : Fin B → Rat := fun j => if j.val = 0 then halfIntMax w / 2 else 0
      let e : Fin B → Rat := fun j => if j.val = 0 then 1 / 16 else 1 / 4
      finSum e / l2NormSq u = omegaHalfE8M0 w B ∧
      ((1 : Rat) ≤ omegaHalfE8M0 w B ↔ halfDivE8M0 w ≤ B)) ∧
    (halfDivE8M0 2 = 3 ∧ halfDivE8M0 3 = 13 ∧ halfDivE8M0 4 = 57 ∧
     halfDivE8M0 6 = 993 ∧ halfDivE8M0 8 = 16257) := by
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · intro w B hw hB
    dsimp only
    let i0 : Fin B := ⟨0, hB⟩
    let d : Rat := ((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat)
    have hdPos : (0 : Rat) < d := two_pow_sub_one_sq_pos hw
    have hFe : finSum (fun j : Fin B => if j.val = 0 then (0 : Rat) else 1 / 4) =
        ((B - 1 : Nat) : Rat) * (1 / 4 : Rat) := by
      rw [finSum_split_at i0]
      simp only [i0, ↓reduceIte, Rat.zero_add]
      have hc : finSumExcept i0 (fun j : Fin B => if j.val = 0 then (0 : Rat) else 1 / 4) =
          finSumExcept i0 (fun _ => (1 / 4 : Rat)) := by
        unfold finSumExcept
        apply finSum_congr; intro j
        by_cases hj : j = i0
        · simp [hj]
        · have hv : j.val ≠ 0 := by intro h0; apply hj; exact Fin.ext h0
          simp [hj, hv]
      rw [hc, finSumExcept_const]
    have hNorm : l2NormSq (fun j : Fin B => if j.val = 0 then halfIntMax w else 0) = d / 4 := by
      rw [l2NormSq_split_at i0]
      have hc : finSumExcept i0 (fun j : Fin B =>
          (if j.val = 0 then halfIntMax w else 0) * (if j.val = 0 then halfIntMax w else 0)) = 0 := by
        have h0 : finSumExcept i0 (fun j : Fin B =>
            (if j.val = 0 then halfIntMax w else 0) * (if j.val = 0 then halfIntMax w else 0)) =
            finSumExcept i0 (fun _ => (0 : Rat)) := by
          unfold finSumExcept
          apply finSum_congr; intro j
          by_cases hj : j = i0
          · simp [hj]
          · have hv : j.val ≠ 0 := by intro h0; apply hj; exact Fin.ext h0
            simp [hj, hv]
        rw [h0, finSumExcept_const, Rat.mul_zero]
      rw [hc, Rat.add_zero]
      simp only [i0, ↓reduceIte, halfIntMax]
      change (((2 ^ w - 1 : Nat) : Rat) / 2) * (((2 ^ w - 1 : Nat) : Rat) / 2) = d / 4
      dsimp only [d]; grind
    constructor
    · rw [hFe, hNorm]
      unfold omegaHalfAbsMax
      have hd4 : d / 4 ≠ 0 := by
        intro h0
        have : d = 0 := by grind
        exact Rat.ne_of_gt hdPos this
      rw [rat_div_eq_div_iff hd4 (Rat.ne_of_gt hdPos)]
      grind
    · unfold omegaHalfAbsMax
      have h1 : (1 : Rat) ≤ ((B - 1 : Nat) : Rat) / d ↔ d ≤ ((B - 1 : Nat) : Rat) := by
        constructor
        · intro hle
          have hm := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hdPos)
          rw [Rat.one_mul, rat_div_mul_cancel (Rat.ne_of_gt hdPos)] at hm
          exact hm
        · intro hle
          apply rat_le_div_of_mul_le hdPos
          rw [Rat.one_mul]; exact hle
      rw [h1]
      have hdNat : d = (((2 ^ w - 1) * (2 ^ w - 1) : Nat) : Rat) := by
        dsimp only [d]; rw [Rat.natCast_mul]
      rw [hdNat]
      constructor
      · intro hle
        by_cases hok : (2 ^ w - 1) * (2 ^ w - 1) + 1 ≤ B
        · exact hok
        · have hnat : B - 1 < (2 ^ w - 1) * (2 ^ w - 1) := by omega
          exact False.elim (Rat.not_lt.mpr hle (rat_natCast_lt hnat))
      · intro hnat
        exact rat_natCast_le (by omega)
  · intro w B hw hB
    unfold alphaHalfRescaled
    let d : Rat := ((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat)
    let bm1 : Rat := ((B - 1 : Nat) : Rat)
    have hdPos : (0 : Rat) < d := two_pow_sub_one_sq_pos hw
    have hbm1Pos : (0 : Rat) < bm1 := rat_natCast_pos (by omega)
    change d / (d + bm1) < d / bm1
    rw [rat_div_lt_div_iff (rat_add_pos hdPos hbm1Pos) hbm1Pos]
    apply rat_lt_of_sub_pos
    have hEq : d * (d + bm1) - d * bm1 = d * d := by grind
    rw [hEq]
    exact rat_mul_pos hdPos hdPos
  · intro w hw ε hε
    let d : Rat := ((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat)
    have hdPos : (0 : Rat) < d := two_pow_sub_one_sq_pos hw
    let q : Rat := d / ε
    have hqPos : (0 : Rat) < q := rat_div_pos hdPos hε
    let N : Nat := q.ceil.toNat + 1
    refine ⟨N + 1, by omega, ?_⟩
    unfold alphaHalfRescaled
    have hNpos : (0 : Rat) < (N : Rat) := rat_natCast_pos (by omega)
    have hNsim : ((N + 1 - 1 : Nat) : Rat) = (N : Rat) := by simp
    change d / (d + ((N + 1 - 1 : Nat) : Rat)) < ε
    rw [hNsim]
    have hDenPos : (0 : Rat) < d + (N : Rat) := rat_add_pos hdPos hNpos
    apply rat_div_lt_of_mul_lt hDenPos
    have hq_le_ceil : q ≤ (q.ceil : Rat) := Rat.le_ceil
    have hceil_le_N : (q.ceil : Rat) < (N : Rat) := by
      have hInt : q.ceil < (N : Int) := by omega
      have h := rat_intCast_lt hInt
      rw [Rat.intCast_natCast] at h
      exact h
    have hq_lt_N : q < (N : Rat) := rat_lt_of_le_of_lt hq_le_ceil hceil_le_N
    have hd_lt : d < ε * (N : Rat) := by
      have hm := rat_mul_lt_mul_of_pos_left hq_lt_N hε
      have hcancel : ε * q = d := by
        dsimp only [q]
        rw [Rat.mul_comm, rat_div_mul_cancel (Rat.ne_of_gt hε)]
      rw [hcancel] at hm
      exact hm
    have hN_lt_dN : ε * (N : Rat) < ε * (d + (N : Rat)) := by
      apply rat_mul_lt_mul_of_pos_left _ hε
      apply rat_lt_of_sub_pos
      have : (d + (N : Rat)) - (N : Rat) = d := by grind
      rw [this]; exact hdPos
    exact rat_lt_of_lt_of_le hd_lt (Rat.le_of_lt hN_lt_dN)
  · intro w B hw hB
    dsimp only
    let i0 : Fin B := ⟨0, hB⟩
    let d : Rat := ((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat)
    have hdPos : (0 : Rat) < d := two_pow_sub_one_sq_pos hw
    have hFe : finSum (fun j : Fin B => if j.val = 0 then (1 / 16 : Rat) else 1 / 4) =
        (1 / 16 : Rat) + ((B - 1 : Nat) : Rat) * (1 / 4 : Rat) := by
      rw [finSum_split_at i0]
      simp only [i0, ↓reduceIte]
      have hc : finSumExcept i0 (fun j : Fin B => if j.val = 0 then (1 / 16 : Rat) else 1 / 4) =
          finSumExcept i0 (fun _ => (1 / 4 : Rat)) := by
        unfold finSumExcept
        apply finSum_congr; intro j
        by_cases hj : j = i0
        · simp [hj]
        · have hv : j.val ≠ 0 := by intro h0; apply hj; exact Fin.ext h0
          simp [hj, hv]
      rw [hc, finSumExcept_const]
    have hNorm : l2NormSq (fun j : Fin B => if j.val = 0 then halfIntMax w / 2 else 0) = d / 16 := by
      rw [l2NormSq_split_at i0]
      have hc : finSumExcept i0 (fun j : Fin B =>
          (if j.val = 0 then halfIntMax w / 2 else 0) * (if j.val = 0 then halfIntMax w / 2 else 0)) = 0 := by
        have h0 : finSumExcept i0 (fun j : Fin B =>
            (if j.val = 0 then halfIntMax w / 2 else 0) * (if j.val = 0 then halfIntMax w / 2 else 0)) =
            finSumExcept i0 (fun _ => (0 : Rat)) := by
          unfold finSumExcept
          apply finSum_congr; intro j
          by_cases hj : j = i0
          · simp [hj]
          · have hv : j.val ≠ 0 := by intro h0; apply hj; exact Fin.ext h0
            simp [hj, hv]
        rw [h0, finSumExcept_const, Rat.mul_zero]
      rw [hc, Rat.add_zero]
      simp only [i0, ↓reduceIte, halfIntMax]
      change (((2 ^ w - 1 : Nat) : Rat) / 2 / 2) * (((2 ^ w - 1 : Nat) : Rat) / 2 / 2) = d / 16
      dsimp only [d]; grind
    constructor
    · rw [hFe, hNorm]
      unfold omegaHalfE8M0
      have hd16 : d / 16 ≠ 0 := by
        intro h0
        have : d = 0 := by grind
        exact Rat.ne_of_gt hdPos this
      rw [rat_div_eq_div_iff hd16 (Rat.ne_of_gt hdPos)]
      have h4B : ((4 * B - 3 : Nat) : Rat) = 1 + 4 * ((B - 1 : Nat) : Rat) := by
        have hnat : 4 * B - 3 = 1 + 4 * (B - 1) := by omega
        rw [hnat, Rat.natCast_add, Rat.natCast_mul]
        rfl
      rw [h4B]; grind
    · unfold omegaHalfE8M0
      have h1 : (1 : Rat) ≤ ((4 * B - 3 : Nat) : Rat) / d ↔ d ≤ ((4 * B - 3 : Nat) : Rat) := by
        constructor
        · intro hle
          have hm := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hdPos)
          rw [Rat.one_mul, rat_div_mul_cancel (Rat.ne_of_gt hdPos)] at hm
          exact hm
        · intro hle
          apply rat_le_div_of_mul_le hdPos
          rw [Rat.one_mul]; exact hle
      rw [h1]
      have hdNat : d = (((2 ^ w - 1) * (2 ^ w - 1) : Nat) : Rat) := by
        dsimp only [d]; rw [Rat.natCast_mul]
      rw [hdNat]
      have hid := halfDivE8M0_identity hw
      constructor
      · intro hle
        by_cases hok : halfDivE8M0 w ≤ B
        · exact hok
        · have hnat : 4 * B - 3 < (2 ^ w - 1) * (2 ^ w - 1) := by omega
          exact False.elim (Rat.not_lt.mpr hle (rat_natCast_lt hnat))
      · intro hnat
        exact rat_natCast_le (by omega)

/-! ### Theorem 5: Asymmetric `MXINT4 [-8, 7]` vs Symmetric `[-7, 7]` Crossover & `E8M0` Scale Cliff -/

/-- **Theorem 5 (`mxint4_asym_beats_sym_crossover_b16`)**:
    Proves:
    - Exact tie at `B = 15`: `ω_sym(15) = ω_asym(15) = 1/15`;
    - For ALL `1 ≤ B ≤ 14`: symmetric `[-7, 7]` strictly beats unsigned-scale asymmetric `[-8, 7]`;
    - For ALL `B ≥ 16`: unsigned-scale asymmetric `[-8, 7]` strictly beats symmetric `[-7, 7]`
      (including exact values `19/271 < 15/211` at `B = 16` and `5/41 < 31/227` at `B = 32`);
    - Signed-scale asymmetric `[-8, 7]` strictly beats symmetric `[-7, 7]` for ALL `B ≥ 2`;
    - Exact OCP `E8M0` non-power-of-two `7 vs 8` scale cliff on Uniform blocks: crossing `max|x| ∈ (7, 8]`
      doubles symmetric `[-7, 7]`'s `E8M0` scale from `1` to `2`, quadrupling uniform MSE (`4×` penalty),
      whereas asymmetric `[-8, 7]` (`-8 = -2^3`) remains at scale `1`. -/
theorem mxint4_asym_beats_sym_crossover_b16 :
    (omegaMxint4SymAbsMax 15 = 1 / 15 ∧ omegaMxint4AsymAbsMax 15 = 1 / 15) ∧
    (∀ B : Nat, 1 ≤ B → B ≤ 14 → omegaMxint4SymAbsMax B < omegaMxint4AsymAbsMax B) ∧
    (∀ B : Nat, 16 ≤ B → omegaMxint4AsymAbsMax B < omegaMxint4SymAbsMax B) ∧
    (omegaMxint4AsymAbsMax 16 = 19 / 271 ∧ omegaMxint4SymAbsMax 16 = 15 / 211 ∧
     omegaMxint4AsymAbsMax 32 = 5 / 41 ∧ omegaMxint4SymAbsMax 32 = 31 / 227) ∧
    (∀ B : Nat, 2 ≤ B → omegaMxint4AsymSignedAbsMax B < omegaMxint4SymAbsMax B) ∧
    (∀ (k : Nat) (xMax : Rat),
      (7 : Rat) * ((2 ^ k : Nat) : Rat) < xMax → xMax ≤ (8 : Rat) * ((2 ^ k : Nat) : Rat) →
      let sSym : Rat := ((2 ^ (k + 1) : Nat) : Rat)
      let sAsym : Rat := ((2 ^ k : Nat) : Rat)
      xMax ≤ (7 : Rat) * sSym ∧
      ¬ (xMax ≤ (7 : Rat) * sAsym) ∧
      xMax ≤ (8 : Rat) * sAsym ∧
      uniformStepMse sSym / uniformStepMse sAsym = 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by unfold omegaMxint4SymAbsMax; grind, by unfold omegaMxint4AsymAbsMax; grind⟩
  · intro B h1 h14
    unfold omegaMxint4SymAbsMax omegaMxint4AsymAbsMax
    have hD1 : (0 : Rat) < 196 + ((B - 1 : Nat) : Rat) :=
      rat_add_pos_of_pos_of_nonneg (rat_natCast_pos (by decide : 0 < 196)) (rat_natCast_nonneg _)
    have hD2 : (0 : Rat) < 256 + ((B - 1 : Nat) : Rat) :=
      rat_add_pos_of_pos_of_nonneg (rat_natCast_pos (by decide : 0 < 256)) (rat_natCast_nonneg _)
    rw [rat_div_lt_div_iff hD1 hD2]
    have hB3 : ((B + 3 : Nat) : Rat) = ((B - 1 : Nat) : Rat) + 4 := by
      have hnat : B + 3 = (B - 1) + 4 := by omega
      rw [hnat, Rat.natCast_add]; rfl
    rw [hB3]
    apply rat_lt_of_sub_pos
    have hId : (((B - 1 : Nat) : Rat) + 4) * (196 + ((B - 1 : Nat) : Rat)) -
        ((B - 1 : Nat) : Rat) * (256 + ((B - 1 : Nat) : Rat)) =
        56 + 56 * ((14 - B : Nat) : Rat) := by
      have hnat : (B - 1) + (14 - B) = 13 := by omega
      have hr : ((B - 1 : Nat) : Rat) + ((14 - B : Nat) : Rat) = 13 := by
        rw [← Rat.natCast_add, hnat]; rfl
      grind
    rw [hId]
    exact rat_add_pos_of_pos_of_nonneg (rat_natCast_pos (by decide : 0 < 56))
      (Rat.mul_nonneg (rat_natCast_nonneg 56) (rat_natCast_nonneg _))
  · intro B h16
    unfold omegaMxint4SymAbsMax omegaMxint4AsymAbsMax
    have hD1 : (0 : Rat) < 256 + ((B - 1 : Nat) : Rat) :=
      rat_add_pos_of_pos_of_nonneg (rat_natCast_pos (by decide : 0 < 256)) (rat_natCast_nonneg _)
    have hD2 : (0 : Rat) < 196 + ((B - 1 : Nat) : Rat) :=
      rat_add_pos_of_pos_of_nonneg (rat_natCast_pos (by decide : 0 < 196)) (rat_natCast_nonneg _)
    rw [rat_div_lt_div_iff hD1 hD2]
    have hB3 : ((B + 3 : Nat) : Rat) = ((B - 1 : Nat) : Rat) + 4 := by
      have hnat : B + 3 = (B - 1) + 4 := by omega
      rw [hnat, Rat.natCast_add]; rfl
    rw [hB3]
    apply rat_lt_of_sub_pos
    have hId : ((B - 1 : Nat) : Rat) * (256 + ((B - 1 : Nat) : Rat)) -
        (((B - 1 : Nat) : Rat) + 4) * (196 + ((B - 1 : Nat) : Rat)) =
        56 + 56 * ((B - 16 : Nat) : Rat) := by
      have hnat : B - 1 = 15 + (B - 16) := by omega
      have hr : ((B - 1 : Nat) : Rat) = 15 + ((B - 16 : Nat) : Rat) := by
        rw [hnat, Rat.natCast_add]; rfl
      grind
    rw [hId]
    exact rat_add_pos_of_pos_of_nonneg (rat_natCast_pos (by decide : 0 < 56))
      (Rat.mul_nonneg (rat_natCast_nonneg 56) (rat_natCast_nonneg _))
  · exact ⟨by unfold omegaMxint4AsymAbsMax; grind, by unfold omegaMxint4SymAbsMax; grind,
           by unfold omegaMxint4AsymAbsMax; grind, by unfold omegaMxint4SymAbsMax; grind⟩
  · intro B h2
    unfold omegaMxint4AsymSignedAbsMax omegaMxint4SymAbsMax
    have hD1 : (0 : Rat) < 256 + ((B - 1 : Nat) : Rat) :=
      rat_add_pos_of_pos_of_nonneg (rat_natCast_pos (by decide : 0 < 256)) (rat_natCast_nonneg _)
    have hD2 : (0 : Rat) < 196 + ((B - 1 : Nat) : Rat) :=
      rat_add_pos_of_pos_of_nonneg (rat_natCast_pos (by decide : 0 < 196)) (rat_natCast_nonneg _)
    rw [rat_div_lt_div_iff hD1 hD2]
    apply rat_lt_of_sub_pos
    have hId : ((B - 1 : Nat) : Rat) * (256 + ((B - 1 : Nat) : Rat)) -
        ((B - 1 : Nat) : Rat) * (196 + ((B - 1 : Nat) : Rat)) =
        60 * ((B - 1 : Nat) : Rat) := by grind
    rw [hId]
    exact rat_mul_pos (rat_natCast_pos (by decide : 0 < 60)) (rat_natCast_pos (by omega))
  · intro k xMax hLo hHi
    dsimp only
    have hp : (0 : Rat) < ((2 ^ k : Nat) : Rat) := rat_natCast_pos (Nat.pow_pos (by decide))
    have hpow : ((2 ^ (k + 1) : Nat) : Rat) = 2 * ((2 ^ k : Nat) : Rat) := by
      have h : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h, Rat.natCast_mul]; rfl
    refine ⟨?_, ?_, hHi, ?_⟩
    · rw [hpow]
      have h1 : (8 : Rat) * ((2 ^ k : Nat) : Rat) ≤ (7 : Rat) * (2 * ((2 ^ k : Nat) : Rat)) := by
        have hle : (8 : Rat) ≤ 14 := rat_natCast_le (by decide : 8 ≤ 14)
        have hm := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hp)
        grind
      exact Rat.le_trans hHi h1
    · exact Rat.not_le.mpr hLo
    · unfold uniformStepMse
      rw [hpow]
      have hne : ((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat) / 12 ≠ 0 := by
        have hp2 : (0 : Rat) < ((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat) := rat_mul_pos hp hp
        intro h0
        have : ((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat) = 0 := by grind
        exact Rat.ne_of_gt hp2 this
      rw [rat_div_eq_iff hne]
      grind

end MxintMxfpSwar
