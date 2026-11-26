/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxfpDoublelogFtz.Ef21Envelopes

/-!
# Theorems 3 & 4: Universal Double-Log Crossover (`4^b` Cancellation) & OCP E8M0 Shift Laws

Proves:
- **Theorem 3 (`mxfp_doublelog_crossover_4b_cancellation_law`):**
  For ANY `a ≥ 2, b ≥ 1`, equating `E_a M_b`'s continuous subnormal-underflow ramp
  `k / (4 * M(a, b)^2 + k)` with `E_{a+1} M_{b-1}`'s normal-precision plateau
  `1 / (2^b + 1)^2` cancels `4^b` identically, yielding exact rational crossover
  `B*_cont(a, b) = ((2^(b+1) - 1)^2 / (4 * ((2^b + 1)^2 - 1))) * 2^(2^(a+1))`,
  strictly trapped in `((1/4) * 2^(2^(a+1)), 2^(2^(a+1)))` for all `b ≥ 1`, and
  strictly trapped in `((1/2) * 2^(2^(a+1)), 2^(2^(a+1)))` (with exact lower bound `49/96`)
  for all `b ≥ 2` — proving bitwidth-invariant `a*_cont(w, B) = ⌊log₂ log₂ B⌋`.

- **Theorem 4 (`mxfp_e8m0_doublelog_shift_law`):**
  For ANY `a ≥ 2, b ≥ 2`, OCP E8M0 power-of-2 scaling shifts the crossover down to
  `B*_e8m0(a, b) = min(B*_e8m0_uf(a, b), B*_e8m0_norm(a, b))`, strictly trapped in
  `((1/8) * 2^(2^(a+1)), (3/16) * 2^(2^(a+1)))` (2.41–2.97 bits below `2^(a+1)`),
  plus exact concrete crossover certifications for `MXFP4`, `MXFP5`, `MXFP6`, `MXFP7`, `MXFP8`.
-/

namespace MxfpDoublelogFtz

/-! ## Helper: Denominator Positivity & Algebraic Identities -/

theorem contCrossover_den_pos {b : Nat} (hb : 1 ≤ b) :
    (0 : Rat) < 4 * (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1) := by
  have ht : (2 : Rat) ≤ ((2 ^ b : Nat) : Rat) := rat_pow2_ge_two hb
  have h1 : (3 : Rat) ≤ ((2 ^ b + 1 : Nat) : Rat) := by
    have : ((2 ^ b + 1 : Nat) : Rat) = ((2 ^ b : Nat) : Rat) + 1 := by grind
    rw [this]
    have := (Rat.add_le_add_right (c := (1 : Rat))).mpr ht
    grind
  have hsq : (9 : Rat) ≤ ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) := by
    have hpos : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) := natCast_pos (Nat.succ_pos _)
    have h9 : (3 : Rat) * 3 ≤ ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) := by
      have s1 := rat_mul_le_mul_of_nonneg_left h1 (by decide : (0 : Rat) ≤ 3)
      have s2 := rat_mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hpos)
      exact Rat.le_trans s1 s2
    have h33 : (3 : Rat) * 3 = 9 := by grind
    rw [h33] at h9
    exact h9
  have hsub : (8 : Rat) ≤ ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1 := by
    have := (Rat.add_le_add_right (c := (-1 : Rat))).mpr hsq
    grind
  have hpos8 : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1 :=
    rat_lt_of_lt_of_le (by decide : (0 : Rat) < 8) hsub
  exact rat_mul_pos (by decide : (0 : Rat) < 4) hpos8

/-- Key `4^b` cancellation identity in `Rat`:
`4 * M(a, b)^2 = ((2^(b+1) - 1)^2 / 4) * 2^(2^(a+1)) = contCrossover a b * ((2^b + 1)^2 - 1)`. -/
theorem four_mxfpMaxInt_sq_eq_crossover_mul {a b : Nat} (ha : 2 ≤ a) (hb : 1 ≤ b) :
    4 * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) =
      contCrossover a b * (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1) := by
  have h16 : (16 * (mxfpMaxInt a b * mxfpMaxInt a b) : Nat) =
      (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) * 2 ^ (2 ^ (a + 1)) :=
    sixteen_mul_mxfpMaxInt_sq ha
  have h16r : (16 : Rat) * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) =
      ((2 ^ (b + 1) - 1 : Nat) : Rat) * ((2 ^ (b + 1) - 1 : Nat) : Rat) *
        ((2 ^ (2 ^ (a + 1)) : Nat) : Rat) := by
    have := congrArg (fun x : Nat => (x : Rat)) h16
    grind
  unfold contCrossover contCrossoverPref
  have hden := contCrossover_den_pos hb
  have hdne : 4 * (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1) ≠ 0 :=
    Rat.ne_of_gt hden
  have hinv := Rat.inv_mul_cancel _ hdne
  rw [Rat.div_def]
  grind

/-- Exact Continuous-scaling crossover equation:
`k / (4 * M(a, b)^2 + k) = 1 / (2^b + 1)^2` when `k = contCrossover a b`. -/
theorem contCrossover_solves_equation {a b : Nat} (ha : 2 ≤ a) (hb : 1 ≤ b) :
    contCrossover a b /
      (4 * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) + contCrossover a b) =
      1 / (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat)) := by
  have hM := mxfpMaxInt_pos ha hb
  have h4m : (0 : Rat) < 4 * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) :=
    rat_mul_pos (by decide : (0 : Rat) < 4) (natCast_pos (Nat.mul_pos hM hM))
  have hcross_pos : (0 : Rat) < contCrossover a b := by
    unfold contCrossover contCrossoverPref
    have hnum_pos : (0 : Rat) < ((2 ^ (b + 1) - 1 : Nat) : Rat) := by
      have : 4 ≤ 2 ^ (b + 1) := nat_pow2_ge_four (by omega)
      exact natCast_pos (by omega)
    exact rat_mul_pos (rat_div_pos (rat_mul_pos hnum_pos hnum_pos) (contCrossover_den_pos hb))
      (rat_pow2_pos _)
  have hden1 : (0 : Rat) < 4 * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) + contCrossover a b :=
    rat_add_pos h4m hcross_pos
  have hq : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) := natCast_pos (Nat.succ_pos _)
  have hden2 : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) :=
    rat_mul_pos hq hq
  rw [rat_div_eq_div_iff (Rat.ne_of_gt hden1) (Rat.ne_of_gt hden2)]
  have hkey := four_mxfpMaxInt_sq_eq_crossover_mul ha hb
  grind

/-- Exact Continuous-scaling crossover comparison iff for ANY `k ≥ 0`:
`k / (4 * M(a, b)^2 + k) < 1 / (2^b + 1)^2 ↔ k < contCrossover a b`. -/
theorem contUf_lt_next_plateau_iff {a b : Nat} (ha : 2 ≤ a) (hb : 1 ≤ b)
    {k : Rat} (hk : (0 : Rat) ≤ k) :
    k / (4 * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) + k) <
      1 / (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat)) ↔
    k < contCrossover a b := by
  have hM := mxfpMaxInt_pos ha hb
  have h4m : (0 : Rat) < 4 * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) :=
    rat_mul_pos (by decide : (0 : Rat) < 4) (natCast_pos (Nat.mul_pos hM hM))
  have hden1 : (0 : Rat) < 4 * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) + k :=
    rat_add_pos_of_pos_of_nonneg h4m hk
  have hq : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) := natCast_pos (Nat.succ_pos _)
  have hden2 : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) :=
    rat_mul_pos hq hq
  rw [rat_div_lt_div_iff hden1 hden2]
  have hkey := four_mxfpMaxInt_sq_eq_crossover_mul ha hb
  have hd_pos : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1 := by
    have h4 := contCrossover_den_pos hb
    have hinv := rat_inv_pos (by decide : (0 : Rat) < 4)
    have hm := rat_mul_pos hinv h4
    have : (4 : Rat)⁻¹ * (4 * (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1)) =
        ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1 := by grind
    rw [this] at hm
    exact hm
  constructor
  · intro h
    have h1 : k * (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1) <
        contCrossover a b * (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1) := by
      apply rat_lt_of_sub_pos
      have hsub := rat_sub_pos h
      grind
    have h2 := rat_mul_lt_mul_of_pos_right h1 (rat_inv_pos hd_pos)
    have hinv := Rat.mul_inv_cancel _ (Rat.ne_of_gt hd_pos)
    have hl : k * (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1) *
        (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1)⁻¹ = k := by grind
    have hr : contCrossover a b * (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1) *
        (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) - 1)⁻¹ = contCrossover a b := by grind
    rw [hl, hr] at h2
    exact h2
  · intro h
    have h1 := rat_mul_lt_mul_of_pos_right h hd_pos
    apply rat_lt_of_sub_pos
    have hsub := rat_sub_pos h1
    grind

/-- Exact Continuous prefactor bounds:
- For ALL `b ≥ 1`: `1/4 < contCrossoverPref b < 1`.
- For ALL `b ≥ 2`: `1/2 < 49/96 ≤ contCrossoverPref b < 1`. -/
theorem contCrossoverPref_bounds_ge1 {b : Nat} (hb : 1 ≤ b) :
    (1 / 4 : Rat) < contCrossoverPref b ∧ contCrossoverPref b < 1 := by
  unfold contCrossoverPref
  have hden := contCrossover_den_pos hb
  have h2b_ge2 : 2 ≤ 2 ^ b := nat_pow2_ge_two hb
  have ht : (2 : Rat) ≤ ((2 ^ b : Nat) : Rat) := rat_pow2_ge_two hb
  have h2b1 : ((2 ^ (b + 1) - 1 : Nat) : Rat) = 2 * ((2 ^ b : Nat) : Rat) - 1 := by
    have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ]; omega
    have hsub : (2 ^ (b + 1) - 1) + 1 = 2 * 2 ^ b := by omega
    have := congrArg (fun x : Nat => (x : Rat)) hsub
    grind
  have hd1 : ((2 ^ b + 1 : Nat) : Rat) = ((2 ^ b : Nat) : Rat) + 1 := by grind
  constructor
  · rw [rat_div_lt_div_iff (by decide : (0 : Rat) < 4) hden]
    rw [h2b1, hd1]
    apply rat_lt_of_sub_pos
    have hident : (2 * ((2 ^ b : Nat) : Rat) - 1) * (2 * ((2 ^ b : Nat) : Rat) - 1) * 4 -
        1 * (4 * ((((2 ^ b : Nat) : Rat) + 1) * (((2 ^ b : Nat) : Rat) + 1) - 1)) =
        4 * (3 * ((2 ^ b : Nat) : Rat) * (((2 ^ b : Nat) : Rat) - 2) + 1) := by grind
    rw [hident]
    have hge0 : (0 : Rat) ≤ ((2 ^ b : Nat) : Rat) - 2 := rat_sub_nonneg ht
    have hmul : (0 : Rat) ≤ 3 * ((2 ^ b : Nat) : Rat) * (((2 ^ b : Nat) : Rat) - 2) :=
      Rat.mul_nonneg (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 3) (natCast_nonneg _)) hge0
    have hquad : (0 : Rat) < 3 * ((2 ^ b : Nat) : Rat) * (((2 ^ b : Nat) : Rat) - 2) + 1 := by
      rw [Rat.add_comm]
      exact rat_add_pos_of_pos_of_nonneg (by decide : (0 : Rat) < 1) hmul
    exact rat_mul_pos (by decide : (0 : Rat) < 4) hquad
  · have h1 : (1 : Rat) = 1 / 1 := by grind
    conv => rhs; rw [h1]
    rw [rat_div_lt_div_iff hden (by decide : (0 : Rat) < 1)]
    rw [h2b1, hd1]
    apply rat_lt_of_sub_pos
    have hident : 1 * (4 * ((((2 ^ b : Nat) : Rat) + 1) * (((2 ^ b : Nat) : Rat) + 1) - 1)) -
        (2 * ((2 ^ b : Nat) : Rat) - 1) * (2 * ((2 ^ b : Nat) : Rat) - 1) * 1 =
        12 * ((2 ^ b : Nat) : Rat) - 1 := by grind
    rw [hident]
    have h24 : (24 : Rat) ≤ 12 * ((2 ^ b : Nat) : Rat) := by
      have := rat_mul_le_mul_of_nonneg_left ht (by decide : (0 : Rat) ≤ 12)
      have h12 : (12 : Rat) * 2 = 24 := by grind
      rw [h12] at this; exact this
    have h23 : (23 : Rat) ≤ 12 * ((2 ^ b : Nat) : Rat) - 1 := by
      have := (Rat.add_le_add_right (c := (-1 : Rat))).mpr h24
      grind
    exact rat_lt_of_lt_of_le (by decide : (0 : Rat) < 23) h23

theorem contCrossoverPref_ge_49_96 {b : Nat} (hb : 2 ≤ b) :
    (49 / 96 : Rat) ≤ contCrossoverPref b := by
  unfold contCrossoverPref
  have hden := contCrossover_den_pos (b := b) (by omega)
  have ht : (4 : Rat) ≤ ((2 ^ b : Nat) : Rat) := rat_pow2_ge_four hb
  have h2b1 : ((2 ^ (b + 1) - 1 : Nat) : Rat) = 2 * ((2 ^ b : Nat) : Rat) - 1 := by
    have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ]; omega
    have h2b_ge4 : 4 ≤ 2 ^ b := nat_pow2_ge_four hb
    have hsub : (2 ^ (b + 1) - 1) + 1 = 2 * 2 ^ b := by omega
    have := congrArg (fun x : Nat => (x : Rat)) hsub
    grind
  have hd1 : ((2 ^ b + 1 : Nat) : Rat) = ((2 ^ b : Nat) : Rat) + 1 := by grind
  rw [rat_div_le_div_iff (by decide : (0 : Rat) < 96) hden]
  rw [h2b1, hd1]
  apply rat_le_of_sub_nonneg
  have hident : (2 * ((2 ^ b : Nat) : Rat) - 1) * (2 * ((2 ^ b : Nat) : Rat) - 1) * 96 -
      49 * (4 * ((((2 ^ b : Nat) : Rat) + 1) * (((2 ^ b : Nat) : Rat) + 1) - 1)) =
      4 * (((2 ^ b : Nat) : Rat) - 4) * (47 * ((2 ^ b : Nat) : Rat) - 6) := by grind
  rw [hident]
  have h1 : (0 : Rat) ≤ ((2 ^ b : Nat) : Rat) - 4 := rat_sub_nonneg ht
  have h47 : (188 : Rat) ≤ 47 * ((2 ^ b : Nat) : Rat) := by
    have := rat_mul_le_mul_of_nonneg_left ht (by decide : (0 : Rat) ≤ 47)
    have h474 : (47 : Rat) * 4 = 188 := by grind
    rw [h474] at this; exact this
  have h2 : (0 : Rat) ≤ 47 * ((2 ^ b : Nat) : Rat) - 6 :=
    rat_sub_nonneg (Rat.le_trans (by decide : (6 : Rat) ≤ 188) h47)
  exact Rat.mul_nonneg (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 4) h1) h2

/-- **Headline Theorem 3:** Universal Double-Log Crossover & `4^b` Cancellation Law. -/
theorem mxfp_doublelog_crossover_4b_cancellation_law :
    (∀ a b : Nat, 2 ≤ a → 1 ≤ b →
      contCrossover a b /
        (4 * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) + contCrossover a b) =
        1 / (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat)) ∧
      (∀ k : Rat, (0 : Rat) ≤ k →
        (k / (4 * ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) + k) <
          1 / (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat)) ↔
         k < contCrossover a b)) ∧
      (1 / 4 : Rat) * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat) < contCrossover a b ∧
      contCrossover a b < ((2 ^ (2 ^ (a + 1)) : Nat) : Rat)) ∧
    (∀ a b : Nat, 2 ≤ a → 2 ≤ b →
      (1 / 2 : Rat) * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat) < contCrossover a b ∧
      (49 / 96 : Rat) * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat) ≤ contCrossover a b ∧
      contCrossover a b < ((2 ^ (2 ^ (a + 1)) : Nat) : Rat)) ∧
    (contCrossoverPref 1 = 9 / 32 ∧
     contCrossoverPref 2 = 49 / 96 ∧
     contCrossoverPref 3 = 45 / 64 ∧
     contCrossoverPref 4 = 961 / 1152 ∧
     contCrossoverPref 5 = 3969 / 4352) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    have hpow := rat_pow2_pos (2 ^ (a + 1))
    have hpb := contCrossoverPref_bounds_ge1 hb
    refine ⟨contCrossover_solves_equation ha hb,
      fun k hk => contUf_lt_next_plateau_iff ha hb hk, ?_, ?_⟩
    · unfold contCrossover
      exact rat_mul_lt_mul_of_pos_right hpb.1 hpow
    · unfold contCrossover
      have h1 := rat_mul_lt_mul_of_pos_right hpb.2 hpow
      simpa using h1
  · intro a b ha hb
    have hpow := rat_pow2_pos (2 ^ (a + 1))
    have hpb := contCrossoverPref_bounds_ge1 (b := b) (by omega)
    have h49 := contCrossoverPref_ge_49_96 hb
    have hhalf : (1 / 2 : Rat) < contCrossoverPref b :=
      rat_lt_of_lt_of_le (rat_div_lt_div_of_nat (by decide) (by decide) (by decide)) h49
    refine ⟨?_, ?_, ?_⟩
    · unfold contCrossover
      exact rat_mul_lt_mul_of_pos_right hhalf hpow
    · unfold contCrossover
      exact rat_mul_le_mul_of_nonneg_right h49 (Rat.le_of_lt hpow)
    · unfold contCrossover
      have h1 := rat_mul_lt_mul_of_pos_right hpb.2 hpow
      simpa using h1
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (unfold contCrossoverPref; grind)

/-! ## Theorem 4: OCP E8M0 Double-Log Shift Law -/

/-- Exact E8M0 Regime-3 (underflow) crossover equation:
`k / (M(a, b)^2 + k) = 1 / (2^b + 1)^2` at `k = e8m0UfCrossoverPref b * 2^(2^(a+1))`. -/
theorem e8m0UfCrossover_solves_equation {a b : Nat} (ha : 2 ≤ a) (hb : 1 ≤ b) :
    let k := e8m0UfCrossoverPref b * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat)
    k / (((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) + k) =
      1 / (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat)) := by
  intro k
  have hM := mxfpMaxInt_pos ha hb
  have hm2 : (0 : Rat) < ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) :=
    natCast_pos (Nat.mul_pos hM hM)
  have hk_eq : k = contCrossover a b / 4 := by
    simp only [k, e8m0UfCrossoverPref, contCrossover]
    grind
  have hcross_pos : (0 : Rat) < contCrossover a b := by
    have hpb := contCrossoverPref_bounds_ge1 hb
    unfold contCrossover
    have hq4 : (0 : Rat) < 1 / 4 := rat_div_pos (by decide) (by decide)
    exact rat_mul_pos (rat_lt_trans hq4 hpb.1) (rat_pow2_pos _)
  have hk_pos : (0 : Rat) < k := by
    rw [hk_eq]
    exact rat_div_pos hcross_pos (by decide : (0 : Rat) < 4)
  have hden1 : (0 : Rat) < ((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) + k :=
    rat_add_pos hm2 hk_pos
  have hq : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) := natCast_pos (Nat.succ_pos _)
  have hden2 : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) :=
    rat_mul_pos hq hq
  rw [rat_div_eq_div_iff (Rat.ne_of_gt hden1) (Rat.ne_of_gt hden2)]
  have hkey := four_mxfpMaxInt_sq_eq_crossover_mul ha hb
  rw [hk_eq]
  grind

/-- Exact E8M0 Regime-1 (top-binade anchor + subnormal) crossover equation:
`(s^2 + k) / ((2^(b+1) + 1)^2 * s^2 + k) = 1 / (2^b + 1)^2` at
`k = e8m0NormCrossoverPref b * 2^(2^(a+1))`, where `s = 2^(2^a - 2)`. -/
theorem e8m0NormCrossover_solves_equation {a b : Nat} (ha : 2 ≤ a) :
    let s : Rat := ((2 ^ (2 ^ a - 2) : Nat) : Rat)
    let q : Rat := ((2 ^ (b + 1) + 1 : Nat) : Rat)
    let k := e8m0NormCrossoverPref b * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat)
    (s * s + k) / (q * q * s * s + k) =
      1 / (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat)) := by
  intro s q k
  have hs_pos : (0 : Rat) < s := rat_pow2_pos _
  have hq_pos : (0 : Rat) < q := natCast_pos (Nat.succ_pos _)
  have ht_pos : (0 : Rat) < ((2 ^ b : Nat) : Rat) := rat_pow2_pos b
  have hpref_pos : (0 : Rat) < e8m0NormCrossoverPref b := by
    unfold e8m0NormCrossoverPref
    exact rat_div_pos
      (rat_add_pos (rat_mul_pos (by decide : (0 : Rat) < 3) ht_pos) (by decide : (0 : Rat) < 2))
      (rat_mul_pos (by decide : (0 : Rat) < 16) (rat_add_pos ht_pos (by decide : (0 : Rat) < 2)))
  have hk_pos : (0 : Rat) < k := rat_mul_pos hpref_pos (rat_pow2_pos _)
  have hden1 : (0 : Rat) < q * q * s * s + k :=
    rat_add_pos (rat_mul_pos (rat_mul_pos (rat_mul_pos hq_pos hq_pos) hs_pos) hs_pos) hk_pos
  have hqb : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) := natCast_pos (Nat.succ_pos _)
  have hden2 : (0 : Rat) < ((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat) :=
    rat_mul_pos hqb hqb
  rw [rat_div_eq_div_iff (Rat.ne_of_gt hden1) (Rat.ne_of_gt hden2)]
  -- Use 16 * s^2 = 2^(2^(a+1))
  have h16s : (16 : Rat) * (s * s) = ((2 ^ (2 ^ (a + 1)) : Nat) : Rat) := by
    have hnat : 16 * (2 ^ (2 ^ a - 2) * 2 ^ (2 ^ a - 2)) = 2 ^ (2 ^ (a + 1)) := by
      rw [pow2_exp_sq ha, sixteen_mul_pow2_sub4 ha]
    have := congrArg (fun x : Nat => (x : Rat)) hnat
    simpa [s] using this
  have hq_eq : q = 2 * ((2 ^ b : Nat) : Rat) + 1 := by
    have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ]; omega
    have hnat : 2 ^ (b + 1) + 1 = 2 * 2 ^ b + 1 := by omega
    have := congrArg (fun x : Nat => (x : Rat)) hnat
    simpa [q] using this
  have hqb_eq : ((2 ^ b + 1 : Nat) : Rat) = ((2 ^ b : Nat) : Rat) + 1 := by grind
  have hd_ne : (16 : Rat) * (((2 ^ b : Nat) : Rat) + 2) ≠ 0 :=
    Rat.ne_of_gt (rat_mul_pos (by decide : (0 : Rat) < 16)
      (rat_add_pos ht_pos (by decide : (0 : Rat) < 2)))
  have hinv := Rat.inv_mul_cancel _ hd_ne
  simp only [k, e8m0NormCrossoverPref]
  rw [Rat.div_def, ← h16s, hq_eq, hqb_eq]
  grind

/-- Exact E8M0 crossover prefactor trapping for ALL `b ≥ 2`:
`1/8 < 49/384 ≤ e8m0CrossoverPref b < 3/16`. -/
theorem e8m0CrossoverPref_bounds {b : Nat} (hb : 2 ≤ b) :
    (1 / 8 : Rat) < e8m0CrossoverPref b ∧
    (49 / 384 : Rat) ≤ e8m0CrossoverPref b ∧
    e8m0CrossoverPref b < (3 / 16 : Rat) := by
  have ht : (4 : Rat) ≤ ((2 ^ b : Nat) : Rat) := rat_pow2_ge_four hb
  have ht_pos : (0 : Rat) < ((2 ^ b : Nat) : Rat) := rat_pow2_pos b
  have huf49 : (49 / 384 : Rat) ≤ e8m0UfCrossoverPref b := by
    unfold e8m0UfCrossoverPref
    have h49 := contCrossoverPref_ge_49_96 hb
    have hq4 : (0 : Rat) ≤ 1 / 4 := Rat.le_of_lt (rat_div_pos (by decide) (by decide))
    have h := rat_mul_le_mul_of_nonneg_right h49 hq4
    have hl : (49 / 96 : Rat) * (1 / 4) = 49 / 384 := by grind
    have hr : contCrossoverPref b * (1 / 4) = contCrossoverPref b / 4 := by grind
    rw [hl, hr] at h
    exact h
  have hnorm_ge : (7 / 48 : Rat) ≤ e8m0NormCrossoverPref b := by
    unfold e8m0NormCrossoverPref
    have hden : (0 : Rat) < 16 * (((2 ^ b : Nat) : Rat) + 2) :=
      rat_mul_pos (by decide : (0 : Rat) < 16) (rat_add_pos ht_pos (by decide : (0 : Rat) < 2))
    rw [rat_div_le_div_iff (by decide : (0 : Rat) < 48) hden]
    apply rat_le_of_sub_nonneg
    have hident : (3 * ((2 ^ b : Nat) : Rat) + 2) * 48 - 7 * (16 * (((2 ^ b : Nat) : Rat) + 2)) =
        32 * (((2 ^ b : Nat) : Rat) - 4) := by grind
    rw [hident]
    exact Rat.mul_nonneg (by decide : (0 : Rat) ≤ 32) (rat_sub_nonneg ht)
  have hnorm_lt : e8m0NormCrossoverPref b < (3 / 16 : Rat) := by
    unfold e8m0NormCrossoverPref
    have hden : (0 : Rat) < 16 * (((2 ^ b : Nat) : Rat) + 2) :=
      rat_mul_pos (by decide : (0 : Rat) < 16) (rat_add_pos ht_pos (by decide : (0 : Rat) < 2))
    rw [rat_div_lt_div_iff hden (by decide : (0 : Rat) < 16)]
    apply rat_lt_of_sub_pos
    have hident : 3 * (16 * (((2 ^ b : Nat) : Rat) + 2)) - (3 * ((2 ^ b : Nat) : Rat) + 2) * 16 =
        64 := by grind
    rw [hident]
    decide
  have hmin_ge : (49 / 384 : Rat) ≤ e8m0CrossoverPref b := by
    unfold e8m0CrossoverPref
    exact rat_le_min huf49
      (Rat.le_trans (rat_div_le_div_of_nat (by decide) (by decide) (by decide)) hnorm_ge)
  have hmin_lt : e8m0CrossoverPref b < (3 / 16 : Rat) :=
    rat_lt_of_le_of_lt (rat_min_le_right _ _) hnorm_lt
  exact ⟨rat_lt_of_lt_of_le (rat_div_lt_div_of_nat (by decide) (by decide) (by decide)) hmin_ge,
    hmin_ge, hmin_lt⟩

/-- **Headline Theorem 4:** OCP E8M0 Double-Log Shift Law + exact concrete crossover tables
for `MXFP4`, `MXFP5`, `MXFP6`, `MXFP7`, and `MXFP8`. -/
theorem mxfp_e8m0_doublelog_shift_law :
    (∀ a b : Nat, 2 ≤ a → 2 ≤ b →
      (let k := e8m0UfCrossoverPref b * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat)
       k / (((mxfpMaxInt a b * mxfpMaxInt a b : Nat) : Rat) + k) =
         1 / (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat))) ∧
      (let s : Rat := ((2 ^ (2 ^ a - 2) : Nat) : Rat)
       let q : Rat := ((2 ^ (b + 1) + 1 : Nat) : Rat)
       let k := e8m0NormCrossoverPref b * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat)
       (s * s + k) / (q * q * s * s + k) =
         1 / (((2 ^ b + 1 : Nat) : Rat) * ((2 ^ b + 1 : Nat) : Rat))) ∧
      (1 / 8 : Rat) * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat) < e8m0Crossover a b ∧
      (49 / 384 : Rat) * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat) ≤ e8m0Crossover a b ∧
      e8m0Crossover a b < (3 / 16 : Rat) * ((2 ^ (2 ^ (a + 1)) : Nat) : Rat)) ∧
    -- Concrete exact crossover certifications across MXFP4..MXFP8 (E8M0 & Continuous):
    -- w = 4 (MXFP4): INT4 -> E2M1 at B* = 3 (E8M0) / 8 (Cont)
    ((deltaE8m0Int 3 2 ≤ deltaE8m0 2 1 false 2 ∧ deltaE8m0 2 1 false 3 < deltaE8m0Int 3 3) ∧
     (deltaContInt 3 7 ≤ deltaCont 2 1 false 7 ∧ deltaCont 2 1 false 8 < deltaContInt 3 8)) ∧
    -- w = 5 (MXFP5): INT5 -> E2M2 -> E3M1 at B* = 4, 34 (E8M0) / 10, 131 (Cont)
    ((deltaE8m0Int 4 3 ≤ deltaE8m0 2 2 false 3 ∧ deltaE8m0 2 2 false 4 < deltaE8m0Int 4 4 ∧
      deltaE8m0 2 2 false 33 ≤ deltaE8m0 3 1 false 33 ∧ deltaE8m0 3 1 false 34 < deltaE8m0 2 2 false 34) ∧
     (deltaContInt 4 9 ≤ deltaCont 2 2 false 9 ∧ deltaCont 2 2 false 10 < deltaContInt 4 10 ∧
      deltaCont 2 2 false 130 ≤ deltaCont 3 1 false 130 ∧ deltaCont 3 1 false 131 < deltaCont 2 2 false 131)) ∧
    -- w = 6 (MXFP6): INT6 -> E2M3 -> E3M2 -> E4M1 at B* = 4, 44, 8364 (E8M0) / 12, 179, 33451 (Cont)
    ((deltaE8m0Int 5 3 ≤ deltaE8m0 2 3 false 3 ∧ deltaE8m0 2 3 false 4 < deltaE8m0Int 5 4 ∧
      deltaE8m0 2 3 false 43 ≤ deltaE8m0 3 2 false 43 ∧ deltaE8m0 3 2 false 44 < deltaE8m0 2 3 false 44 ∧
      deltaE8m0 3 2 false 8363 ≤ deltaE8m0 4 1 false 8363 ∧ deltaE8m0 4 1 false 8364 < deltaE8m0 3 2 false 8364) ∧
     (deltaContInt 5 11 ≤ deltaCont 2 3 false 11 ∧ deltaCont 2 3 false 12 < deltaContInt 5 12 ∧
      deltaCont 2 3 false 178 ≤ deltaCont 3 2 false 178 ∧ deltaCont 3 2 false 179 < deltaCont 2 3 false 179 ∧
      deltaCont 3 2 false 33450 ≤ deltaCont 4 1 false 33450 ∧ deltaCont 4 1 false 33451 < deltaCont 3 2 false 33451)) ∧
    -- w = 7 (MXFP7): INT7 -> E2M4 -> E3M3 -> E4M2 -> E5M1
    ((deltaE8m0Int 6 4 ≤ deltaE8m0 2 4 false 4 ∧ deltaE8m0 2 4 false 5 < deltaE8m0Int 6 5 ∧
      deltaE8m0 2 4 false 46 ≤ deltaE8m0 3 3 false 46 ∧ deltaE8m0 3 3 false 47 < deltaE8m0 2 4 false 47 ∧
      deltaE8m0 3 3 false 10651 ≤ deltaE8m0 4 2 false 10651 ∧ deltaE8m0 4 2 false 10652 < deltaE8m0 3 3 false 10652 ∧
      deltaE8m0 4 2 false 548055723 ≤ deltaE8m0 5 1 false 548055723 ∧ deltaE8m0 5 1 false 548055724 < deltaE8m0 4 2 false 548055724) ∧
     (deltaContInt 6 12 ≤ deltaCont 2 4 false 12 ∧ deltaCont 2 4 false 13 < deltaContInt 6 13 ∧
      deltaCont 2 4 false 211 ≤ deltaCont 3 3 false 211 ∧ deltaCont 3 3 false 212 < deltaCont 2 4 false 212 ∧
      deltaCont 3 3 false 46078 ≤ deltaCont 4 2 false 46078 ∧ deltaCont 4 2 false 46079 < deltaCont 3 3 false 46079 ∧
      deltaCont 4 2 false 2192222890 ≤ deltaCont 5 1 false 2192222890 ∧ deltaCont 5 1 false 2192222891 < deltaCont 4 2 false 2192222891)) ∧
    -- w = 8 (MXFP8): INT8 -> E2M5 -> E3M4 -> E4M3 -> E5M2
    ((deltaE8m0Int 7 4 ≤ deltaE8m0 2 5 false 4 ∧ deltaE8m0 2 5 false 5 < deltaE8m0Int 7 5 ∧
      deltaE8m0 2 5 false 47 ≤ deltaE8m0 3 4 false 47 ∧ deltaE8m0 3 4 false 48 < deltaE8m0 2 5 false 48 ∧
      deltaE8m0 3 4 false 11379 ≤ deltaE8m0 4 3 false 11379 ∧ deltaE8m0 4 3 false 11380 < deltaE8m0 3 4 false 11380 ∧
      deltaE8m0 4 3 false 697932187 ≤ deltaE8m0 5 2 false 697932187 ∧ deltaE8m0 5 2 false 697932188 < deltaE8m0 4 3 false 697932188) ∧
     (deltaContInt 7 12 ≤ deltaCont 2 5 false 12 ∧ deltaCont 2 5 false 13 < deltaContInt 7 13 ∧
      deltaCont 2 5 false 230 ≤ deltaCont 3 4 false 230 ∧ deltaCont 3 4 false 231 < deltaCont 2 5 false 231 ∧
      deltaCont 3 4 false 54668 ≤ deltaCont 4 3 false 54668 ∧ deltaCont 4 3 false 54669 < deltaCont 3 4 false 54669 ∧
      deltaCont 4 3 false 3019898878 ≤ deltaCont 5 2 false 3019898878 ∧ deltaCont 5 2 false 3019898879 < deltaCont 4 3 false 3019898879)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    have hpow := rat_pow2_pos (2 ^ (a + 1))
    have hpb := e8m0CrossoverPref_bounds hb
    refine ⟨e8m0UfCrossover_solves_equation ha (by omega),
      e8m0NormCrossover_solves_equation ha, ?_, ?_, ?_⟩
    · unfold e8m0Crossover
      exact rat_mul_lt_mul_of_pos_right hpb.1 hpow
    · unfold e8m0Crossover
      exact rat_mul_le_mul_of_nonneg_right hpb.2.1 (Rat.le_of_lt hpow)
    · unfold e8m0Crossover
      exact rat_mul_lt_mul_of_pos_right hpb.2.2 hpow
  · -- w = 4 (MXFP4)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [deltaE8m0Int_eq_nat, deltaE8m0_eq_nat false 2 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 3 (by decide) (by decide) (by decide), deltaE8m0Int_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaContInt_eq_nat, deltaCont_eq_nat false 7 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 8 (by decide) (by decide), deltaContInt_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
  · -- w = 5 (MXFP5)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [deltaE8m0Int_eq_nat, deltaE8m0_eq_nat false 3 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 4 (by decide) (by decide) (by decide), deltaE8m0Int_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 33 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 33 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 34 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 34 (by decide) (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaContInt_eq_nat, deltaCont_eq_nat false 9 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 10 (by decide) (by decide), deltaContInt_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 130 (by decide) (by decide),
          deltaCont_eq_nat false 130 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 131 (by decide) (by decide),
          deltaCont_eq_nat false 131 (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
  · -- w = 6 (MXFP6)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [deltaE8m0Int_eq_nat, deltaE8m0_eq_nat false 3 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 4 (by decide) (by decide) (by decide), deltaE8m0Int_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 43 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 43 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 44 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 44 (by decide) (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 8363 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 8363 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 8364 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 8364 (by decide) (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaContInt_eq_nat, deltaCont_eq_nat false 11 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 12 (by decide) (by decide), deltaContInt_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 178 (by decide) (by decide),
          deltaCont_eq_nat false 178 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 179 (by decide) (by decide),
          deltaCont_eq_nat false 179 (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 33450 (by decide) (by decide),
          deltaCont_eq_nat false 33450 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 33451 (by decide) (by decide),
          deltaCont_eq_nat false 33451 (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
  · -- w = 7 (MXFP7)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [deltaE8m0Int_eq_nat, deltaE8m0_eq_nat false 4 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 5 (by decide) (by decide) (by decide), deltaE8m0Int_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 46 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 46 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 47 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 47 (by decide) (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 10651 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 10651 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 10652 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 10652 (by decide) (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 548055723 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 548055723 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 548055724 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 548055724 (by decide) (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaContInt_eq_nat, deltaCont_eq_nat false 12 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 13 (by decide) (by decide), deltaContInt_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 211 (by decide) (by decide),
          deltaCont_eq_nat false 211 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 212 (by decide) (by decide),
          deltaCont_eq_nat false 212 (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 46078 (by decide) (by decide),
          deltaCont_eq_nat false 46078 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 46079 (by decide) (by decide),
          deltaCont_eq_nat false 46079 (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 2192222890 (by decide) (by decide),
          deltaCont_eq_nat false 2192222890 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 2192222891 (by decide) (by decide),
          deltaCont_eq_nat false 2192222891 (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
  · -- w = 8 (MXFP8)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [deltaE8m0Int_eq_nat, deltaE8m0_eq_nat false 4 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 5 (by decide) (by decide) (by decide), deltaE8m0Int_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 47 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 47 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 48 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 48 (by decide) (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 11379 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 11379 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 11380 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 11380 (by decide) (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 697932187 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 697932187 (by decide) (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaE8m0_eq_nat false 697932188 (by decide) (by decide) (by decide),
          deltaE8m0_eq_nat false 697932188 (by decide) (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaContInt_eq_nat, deltaCont_eq_nat false 12 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 13 (by decide) (by decide), deltaContInt_eq_nat]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 230 (by decide) (by decide),
          deltaCont_eq_nat false 230 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 231 (by decide) (by decide),
          deltaCont_eq_nat false 231 (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 54668 (by decide) (by decide),
          deltaCont_eq_nat false 54668 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 54669 (by decide) (by decide),
          deltaCont_eq_nat false 54669 (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 3019898878 (by decide) (by decide),
          deltaCont_eq_nat false 3019898878 (by decide) (by decide)]
      exact rat_div_le_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 3019898879 (by decide) (by decide),
          deltaCont_eq_nat false 3019898879 (by decide) (by decide)]
      exact rat_div_lt_div_of_nat (by decide) (by decide) (by decide)

end MxfpDoublelogFtz
