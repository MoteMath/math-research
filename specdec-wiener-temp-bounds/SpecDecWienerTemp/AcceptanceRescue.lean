/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecWienerTemp.RatOrder

/-!
# Exact Rational Binary and Multi-Class Wiener-MMSE Acceptance Rescue Witnesses

Proves Theorem 6 (`wiener_temperature_exact_acceptance_rescue_witnesses`):
1. Exact zero-mean, uncorrelated signal-plus-noise ensemble (`z ∈ {-4, +4}` with probs
   `1/2, 1/2`, `σ_z^2 = 16`; `e ∈ {-8, 0, +8}` with probs `3/8, 1/4, 3/8`, `σ_q^2 = 48`):
   - `E[z] = 0`, `E[e] = 0`, `Cov(z, e) = 0`
   - `ρ^2 = σ_q^2 / σ_z^2 = 3`, `T_MMSE^* = 4`, `T_var = 2` (`T_var^2 = 4`)
2. Exact binary (`V = 2`) softmax acceptance rescue witness at rational base `r = 3/2` and `5/4`:
   `E[α(p, q(T = 1))] < E[α(p, q(T_var = 2))] < E[α(p, q(T_MMSE^* = 4))]`
3. Exact 3-class (`V = 3`) softmax acceptance rescue witness at rational base `r = 3/2` and `5/4`:
   `E[α(p, q(T = 1))] < E[α(p, q(T_var = 2))] < E[α(p, q(T_MMSE^* = 4))]`
4. Exact zero-extra-compute fused dequantization scale absorption identity:
   `(s_deq · z_hat) / T = (s_deq / T) · z_hat` for all `T ≠ 0`.
-/

namespace SpecDecWienerTemp

/-! ### Exact Closed-Form Helpers for Binary and Symmetric 3-Class Softmax Acceptance -/

theorem ratMin_of_le {a b : Rat} (h : a ≤ b) : ratMin a b = a := by
  unfold ratMin; simp [h]

theorem ratMin_of_ge {a b : Rat} (h : b ≤ a) : ratMin a b = b := by
  unfold ratMin
  split
  · rename_i hab; exact Rat.le_antisymm hab h
  · rfl

theorem ratZPow_pos {r : Rat} (hr : (0 : Rat) < r) (k : Int) : (0 : Rat) < ratZPow r k := by
  unfold ratZPow
  split
  · exact ratPow_pos hr k.toNat
  · exact rat_div_pos (by decide) (ratPow_pos hr (-k).toNat)

theorem ratPow_ge_one {r : Rat} (hr : (1 : Rat) ≤ r) (n : Nat) : (1 : Rat) ≤ ratPow r n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [ratPow]
    have h0 : (0 : Rat) ≤ ratPow r k := Rat.le_trans (by decide : (0 : Rat) ≤ 1) ih
    have ha : (1 : Rat) * 1 ≤ ratPow r k * 1 := rat_mul_le_mul_of_nonneg_right ih (by decide)
    have hb : ratPow r k * 1 ≤ ratPow r k * r := rat_mul_le_mul_of_nonneg_left hr h0
    rw [Rat.mul_one] at ha
    exact Rat.le_trans ha hb

theorem ratPow_mono {r : Rat} (hr : (1 : Rat) ≤ r) {m n : Nat} (h : m ≤ n) :
    ratPow r m ≤ ratPow r n := by
  have ⟨k, hk⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [hk]
  clear hk h n
  induction k with
  | zero => simp
  | succ j ih =>
    have heq : m + (j + 1) = (m + j) + 1 := by omega
    rw [heq]; simp only [ratPow]
    have hnn : (0 : Rat) ≤ ratPow r (m + j) :=
      Rat.le_trans (by decide : (0 : Rat) ≤ 1) (ratPow_ge_one hr (m + j))
    have hstep : ratPow r (m + j) * 1 ≤ ratPow r (m + j) * r :=
      rat_mul_le_mul_of_nonneg_left hr hnn
    rw [Rat.mul_one] at hstep
    exact Rat.le_trans ih hstep

theorem ratZPow_mono {r : Rat} (hr : (1 : Rat) ≤ r) {a b : Int} (h : a ≤ b) :
    ratZPow r a ≤ ratZPow r b := by
  have hrpos : (0 : Rat) < r := rat_lt_of_lt_of_le (by decide) hr
  unfold ratZPow
  split
  · rename_i ha0
    have hb0 : 0 ≤ b := by omega
    simp only [hb0, ↓reduceIte]
    exact ratPow_mono hr (by omega)
  · rename_i ha0
    split
    · rename_i hb0
      have h1 : (1 : Rat) / ratPow r (-a).toNat ≤ 1 := by
        apply rat_div_le_of_mul_le (ratPow_pos hrpos _)
        rw [Rat.one_mul]
        exact ratPow_ge_one hr _
      exact Rat.le_trans h1 (ratPow_ge_one hr _)
    · rename_i hb0
      rw [rat_div_le_div_iff (ratPow_pos hrpos _) (ratPow_pos hrpos _),
          Rat.one_mul, Rat.one_mul]
      exact ratPow_mono hr (by omega)

/-- For `r ≥ 1` and `a ≤ b`, binary softmax acceptance is `r^a / (r^a + 1) + 1 / (r^b + 1)`. -/
theorem binAccept_of_le {r : Rat} (hr : (1 : Rat) ≤ r) {a b : Int} (hab : a ≤ b) :
    acceptRate (binRatSoftmax r a) (binRatSoftmax r b) =
      ratZPow r a / (ratZPow r a + 1) + 1 / (ratZPow r b + 1) := by
  have hrpos : (0 : Rat) < r := rat_lt_of_lt_of_le (by decide) hr
  have hwa : (0 : Rat) < ratZPow r a := ratZPow_pos hrpos a
  have hwb : (0 : Rat) < ratZPow r b := ratZPow_pos hrpos b
  have hle : ratZPow r a ≤ ratZPow r b := ratZPow_mono hr hab
  have hda : (0 : Rat) < ratZPow r a + 1 := rat_add_pos hwa (by decide)
  have hdb : (0 : Rat) < ratZPow r b + 1 := rat_add_pos hwb (by decide)
  have h0 : ratZPow r a / (ratZPow r a + 1) ≤ ratZPow r b / (ratZPow r b + 1) := by
    rw [rat_div_le_div_iff hda hdb]
    have hsub : (0 : Rat) ≤ ratZPow r b - ratZPow r a := rat_sub_nonneg hle
    apply rat_le_of_sub_nonneg
    grind
  have h1 : (1 : Rat) / (ratZPow r b + 1) ≤ 1 / (ratZPow r a + 1) := by
    rw [rat_div_le_div_iff hdb hda, Rat.one_mul, Rat.one_mul]
    exact rat_add_le_add hle Rat.le_refl
  have hz0 : ratZPow r 0 = 1 := by simp [ratZPow, ratPow]
  simp only [acceptRate, binRatSoftmax, ratSoftmax, normProb, finSum, finSumAux, Rat.zero_add,
    ↓reduceIte, Nat.one_ne_zero, hz0]
  rw [ratMin_of_le h0, ratMin_of_ge h1]

theorem binAccept_of_ge {r : Rat} (hr : (1 : Rat) ≤ r) {a b : Int} (hba : b ≤ a) :
    acceptRate (binRatSoftmax r a) (binRatSoftmax r b) =
      ratZPow r b / (ratZPow r b + 1) + 1 / (ratZPow r a + 1) := by
  have hrpos : (0 : Rat) < r := rat_lt_of_lt_of_le (by decide) hr
  have hwa : (0 : Rat) < ratZPow r a := ratZPow_pos hrpos a
  have hwb : (0 : Rat) < ratZPow r b := ratZPow_pos hrpos b
  have hle : ratZPow r b ≤ ratZPow r a := ratZPow_mono hr hba
  have hda : (0 : Rat) < ratZPow r a + 1 := rat_add_pos hwa (by decide)
  have hdb : (0 : Rat) < ratZPow r b + 1 := rat_add_pos hwb (by decide)
  have h0 : ratZPow r b / (ratZPow r b + 1) ≤ ratZPow r a / (ratZPow r a + 1) := by
    rw [rat_div_le_div_iff hdb hda]
    have hsub : (0 : Rat) ≤ ratZPow r a - ratZPow r b := rat_sub_nonneg hle
    apply rat_le_of_sub_nonneg
    grind
  have h1 : (1 : Rat) / (ratZPow r a + 1) ≤ 1 / (ratZPow r b + 1) := by
    rw [rat_div_le_div_iff hda hdb, Rat.one_mul, Rat.one_mul]
    exact rat_add_le_add hle Rat.le_refl
  have hz0 : ratZPow r 0 = 1 := by simp [ratZPow, ratPow]
  simp only [acceptRate, binRatSoftmax, ratSoftmax, normProb, finSum, finSumAux, Rat.zero_add,
    ↓reduceIte, Nat.one_ne_zero, hz0]
  rw [ratMin_of_ge h0, ratMin_of_le h1]

/-- Exact closed form of `expectedBinAccept r T_div` for `T_div ∈ {1, 2, 4}` (via `binAccept_of_le/ge`).
    Here we prove the four exact strict inequalities by expanding into explicit rational sums
    without any `if`-branching. -/
theorem expectedBinAccept_T1 {r : Rat} (hr : (1 : Rat) ≤ r) :
    expectedBinAccept r 1 =
      (1 / 2) * ((3 / 8) * (ratZPow r (-12) / (ratZPow r (-12) + 1) + 1 / (ratZPow r (-4) + 1)) +
                 (1 / 4) * (ratZPow r (-4) / (ratZPow r (-4) + 1) + 1 / (ratZPow r (-4) + 1)) +
                 (3 / 8) * (ratZPow r (-4) / (ratZPow r (-4) + 1) + 1 / (ratZPow r 4 + 1))) +
      (1 / 2) * ((3 / 8) * (ratZPow r (-4) / (ratZPow r (-4) + 1) + 1 / (ratZPow r 4 + 1)) +
                 (1 / 4) * (ratZPow r 4 / (ratZPow r 4 + 1) + 1 / (ratZPow r 4 + 1)) +
                 (3 / 8) * (ratZPow r 4 / (ratZPow r 4 + 1) + 1 / (ratZPow r 12 + 1))) := by
  simp only [expectedBinAccept, finSum, finSumAux, sigProb, sigVal, noiseProb, noiseVal, Rat.zero_add]
  have h1 := binAccept_of_ge hr (a := -4) (b := -12) (by decide)
  have h2 := binAccept_of_le hr (a := -4) (b := -4) (by decide)
  have h3 := binAccept_of_le hr (a := -4) (b := 4) (by decide)
  have h4 := binAccept_of_ge hr (a := 4) (b := -4) (by decide)
  have h5 := binAccept_of_le hr (a := 4) (b := 4) (by decide)
  have h6 := binAccept_of_le hr (a := 4) (b := 12) (by decide)
  have hd1 : (-4 + -8 : Int) / 1 = -12 := by decide
  have hd2 : (-4 + 0 : Int) / 1 = -4 := by decide
  have hd3 : (-4 + 8 : Int) / 1 = 4 := by decide
  have hd4 : (4 + -8 : Int) / 1 = -4 := by decide
  have hd5 : (4 + 0 : Int) / 1 = 4 := by decide
  have hd6 : (4 + 8 : Int) / 1 = 12 := by decide
  rw [hd1, hd2, hd3, hd4, hd5, hd6, h1, h2, h3, h4, h5, h6]

theorem expectedBinAccept_T2 {r : Rat} (hr : (1 : Rat) ≤ r) :
    expectedBinAccept r 2 =
      (1 / 2) * ((3 / 8) * (ratZPow r (-6) / (ratZPow r (-6) + 1) + 1 / (ratZPow r (-4) + 1)) +
                 (1 / 4) * (ratZPow r (-4) / (ratZPow r (-4) + 1) + 1 / (ratZPow r (-2) + 1)) +
                 (3 / 8) * (ratZPow r (-4) / (ratZPow r (-4) + 1) + 1 / (ratZPow r 2 + 1))) +
      (1 / 2) * ((3 / 8) * (ratZPow r (-2) / (ratZPow r (-2) + 1) + 1 / (ratZPow r 4 + 1)) +
                 (1 / 4) * (ratZPow r 2 / (ratZPow r 2 + 1) + 1 / (ratZPow r 4 + 1)) +
                 (3 / 8) * (ratZPow r 4 / (ratZPow r 4 + 1) + 1 / (ratZPow r 6 + 1))) := by
  simp only [expectedBinAccept, finSum, finSumAux, sigProb, sigVal, noiseProb, noiseVal, Rat.zero_add]
  have h1 := binAccept_of_ge hr (a := -4) (b := -6) (by decide)
  have h2 := binAccept_of_le hr (a := -4) (b := -2) (by decide)
  have h3 := binAccept_of_le hr (a := -4) (b := 2) (by decide)
  have h4 := binAccept_of_ge hr (a := 4) (b := -2) (by decide)
  have h5 := binAccept_of_ge hr (a := 4) (b := 2) (by decide)
  have h6 := binAccept_of_le hr (a := 4) (b := 6) (by decide)
  have hd1 : (-4 + -8 : Int) / 2 = -6 := by decide
  have hd2 : (-4 + 0 : Int) / 2 = -2 := by decide
  have hd3 : (-4 + 8 : Int) / 2 = 2 := by decide
  have hd4 : (4 + -8 : Int) / 2 = -2 := by decide
  have hd5 : (4 + 0 : Int) / 2 = 2 := by decide
  have hd6 : (4 + 8 : Int) / 2 = 6 := by decide
  rw [hd1, hd2, hd3, hd4, hd5, hd6, h1, h2, h3, h4, h5, h6]

theorem expectedBinAccept_T4 {r : Rat} (hr : (1 : Rat) ≤ r) :
    expectedBinAccept r 4 =
      (1 / 2) * ((3 / 8) * (ratZPow r (-4) / (ratZPow r (-4) + 1) + 1 / (ratZPow r (-3) + 1)) +
                 (1 / 4) * (ratZPow r (-4) / (ratZPow r (-4) + 1) + 1 / (ratZPow r (-1) + 1)) +
                 (3 / 8) * (ratZPow r (-4) / (ratZPow r (-4) + 1) + 1 / (ratZPow r 1 + 1))) +
      (1 / 2) * ((3 / 8) * (ratZPow r (-1) / (ratZPow r (-1) + 1) + 1 / (ratZPow r 4 + 1)) +
                 (1 / 4) * (ratZPow r 1 / (ratZPow r 1 + 1) + 1 / (ratZPow r 4 + 1)) +
                 (3 / 8) * (ratZPow r 3 / (ratZPow r 3 + 1) + 1 / (ratZPow r 4 + 1))) := by
  simp only [expectedBinAccept, finSum, finSumAux, sigProb, sigVal, noiseProb, noiseVal, Rat.zero_add]
  have h1 := binAccept_of_le hr (a := -4) (b := -3) (by decide)
  have h2 := binAccept_of_le hr (a := -4) (b := -1) (by decide)
  have h3 := binAccept_of_le hr (a := -4) (b := 1) (by decide)
  have h4 := binAccept_of_ge hr (a := 4) (b := -1) (by decide)
  have h5 := binAccept_of_ge hr (a := 4) (b := 1) (by decide)
  have h6 := binAccept_of_ge hr (a := 4) (b := 3) (by decide)
  have hd1 : (-4 + -8 : Int) / 4 = -3 := by decide
  have hd2 : (-4 + 0 : Int) / 4 = -1 := by decide
  have hd3 : (-4 + 8 : Int) / 4 = 1 := by decide
  have hd4 : (4 + -8 : Int) / 4 = -1 := by decide
  have hd5 : (4 + 0 : Int) / 4 = 1 := by decide
  have hd6 : (4 + 8 : Int) / 4 = 3 := by decide
  rw [hd1, hd2, hd3, hd4, hd5, hd6, h1, h2, h3, h4, h5, h6]

/-- Exact evaluation helper for `ratZPow (a / b) k` as an `Int` fraction. -/
theorem ratZPow_div_pos (a b : Int) (_ha : (0 : Int) < a) (hb : (0 : Int) < b) (k : Nat) :
    ratZPow ((a : Rat) / (b : Rat)) (k : Int) = ((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat) := by
  have hb_ne : (b : Rat) ≠ 0 := Rat.ne_of_gt (rat_intCast_lt hb)
  unfold ratZPow
  have h0 : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg k
  simp only [h0, ↓reduceIte, Int.toNat_natCast]
  exact ratPow_div a b hb_ne k

theorem ratZPow_div_neg (a b : Int) (ha : (0 : Int) < a) (hb : (0 : Int) < b) (k : Nat) (hk : 0 < k) :
    ratZPow ((a : Rat) / (b : Rat)) (-(k : Int)) = ((b ^ k : Int) : Rat) / ((a ^ k : Int) : Rat) := by
  have ha_ne : (a : Rat) ≠ 0 := Rat.ne_of_gt (rat_intCast_lt ha)
  have hb_ne : (b : Rat) ≠ 0 := Rat.ne_of_gt (rat_intCast_lt hb)
  unfold ratZPow
  have h0 : ¬ ((0 : Int) ≤ -(k : Int)) := by omega
  simp only [h0, ↓reduceIte, Int.neg_neg, Int.toNat_natCast]
  rw [ratPow_div a b hb_ne k]
  have hak_ne : ((a ^ k : Int) : Rat) ≠ 0 := Rat.ne_of_gt (rat_intCast_lt (Int.pow_pos ha))
  have hbk_ne : ((b ^ k : Int) : Rat) ≠ 0 := Rat.ne_of_gt (rat_intCast_lt (Int.pow_pos hb))
  symm
  rw [rat_div_eq_iff hak_ne]
  have hdiv_ne : ((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat) ≠ 0 := by
    intro h
    have := (rat_div_eq_iff hbk_ne).mp h
    rw [Rat.zero_mul] at this
    exact hak_ne this
  apply rat_eq_of_mul_eq_mul_right hdiv_ne
  have hL : ((b ^ k : Int) : Rat) * (((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat)) =
      ((a ^ k : Int) : Rat) := rat_mul_div_cancel hbk_ne
  have hR : ((1 : Rat) / (((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat))) *
      ((a ^ k : Int) : Rat) * (((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat)) =
      ((a ^ k : Int) : Rat) := by
    calc ((1 : Rat) / (((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat))) *
          ((a ^ k : Int) : Rat) * (((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat))
        = (((1 : Rat) / (((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat))) *
            (((a ^ k : Int) : Rat) / ((b ^ k : Int) : Rat))) * ((a ^ k : Int) : Rat) := by grind
      _ = 1 * ((a ^ k : Int) : Rat) := by rw [rat_div_mul_cancel hdiv_ne]
      _ = ((a ^ k : Int) : Rat) := by grind
  rw [hL, hR]

theorem ensemble_moments_exact :
    finSum sigProb = 1 ∧
    finSum noiseProb = 1 ∧
    finSum (fun i : Fin 2 => sigProb i * (sigVal i : Rat)) = 0 ∧
    finSum (fun j : Fin 3 => noiseProb j * (noiseVal j : Rat)) = 0 ∧
    finSum (fun i : Fin 2 => sigProb i * ((sigVal i : Rat) * (sigVal i : Rat))) = 16 ∧
    finSum (fun j : Fin 3 => noiseProb j * ((noiseVal j : Rat) * (noiseVal j : Rat))) = 48 ∧
    finSum (fun i : Fin 2 => sigProb i * finSum (fun j : Fin 3 =>
      noiseProb j * ((sigVal i : Rat) * (noiseVal j : Rat)))) = 0 ∧
    wienerTemp 16 48 = 4 ∧
    ((2 : Rat) * 2 = wienerTemp 16 48) := by
  simp only [finSum, finSumAux, sigProb, sigVal, noiseProb, noiseVal, wienerTemp]
  grind

/-! ### Exact Binary Softmax Rescue Witness (`r = 3/2` and `r = 5/4`) -/

theorem bin_frac_term {a b : Int} (ha : (0 : Int) < a) (hb : (0 : Int) < b) :
    ((a : Rat) / (b : Rat)) / ((a : Rat) / (b : Rat) + 1) = (a : Rat) / ((a + b : Int) : Rat) ∧
    (1 : Rat) / ((a : Rat) / (b : Rat) + 1) = (b : Rat) / ((a + b : Int) : Rat) := by
  have hb_ne : (b : Rat) ≠ 0 := Rat.ne_of_gt (rat_intCast_lt hb)
  have hab_pos : (0 : Int) < a + b := by omega
  have hab_ne : ((a + b : Int) : Rat) ≠ 0 := Rat.ne_of_gt (rat_intCast_lt hab_pos)
  have hden : (a : Rat) / (b : Rat) + 1 = ((a + b : Int) : Rat) / (b : Rat) := by
    symm
    rw [rat_div_eq_iff hb_ne, Rat.intCast_add]
    have h1 : ((a : Rat) / (b : Rat) + 1) * (b : Rat) = ((a : Rat) / (b : Rat)) * (b : Rat) + (b : Rat) := by grind
    rw [h1, rat_div_mul_cancel hb_ne]
  have hden_ne : ((a + b : Int) : Rat) / (b : Rat) ≠ 0 := by
    intro h0
    have := (rat_div_eq_iff hb_ne).mp h0
    rw [Rat.zero_mul] at this
    exact hab_ne this
  rw [hden]
  constructor
  · rw [rat_div_eq_iff hden_ne]
    apply rat_eq_of_mul_eq_mul_right hb_ne
    rw [rat_div_mul_cancel hb_ne]
    symm
    calc ((a : Rat) / ((a + b : Int) : Rat)) * (((a + b : Int) : Rat) / (b : Rat)) * (b : Rat)
        = ((a : Rat) / ((a + b : Int) : Rat)) * ((((a + b : Int) : Rat) / (b : Rat)) * (b : Rat)) := by grind
      _ = ((a : Rat) / ((a + b : Int) : Rat)) * ((a + b : Int) : Rat) := by rw [rat_div_mul_cancel hb_ne]
      _ = (a : Rat) := rat_div_mul_cancel hab_ne
  · rw [rat_div_eq_iff hden_ne]
    apply rat_eq_of_mul_eq_mul_right hb_ne
    rw [Rat.one_mul]
    symm
    calc ((b : Rat) / ((a + b : Int) : Rat)) * (((a + b : Int) : Rat) / (b : Rat)) * (b : Rat)
        = ((b : Rat) / ((a + b : Int) : Rat)) * ((((a + b : Int) : Rat) / (b : Rat)) * (b : Rat)) := by grind
      _ = ((b : Rat) / ((a + b : Int) : Rat)) * ((a + b : Int) : Rat) := by rw [rat_div_mul_cancel hb_ne]
      _ = (b : Rat) := rat_div_mul_cancel hab_ne

theorem binary_rescue_3_2 :
    expectedBinAccept (3 / 2) 1 < expectedBinAccept (3 / 2) 2 ∧
    expectedBinAccept (3 / 2) 2 < expectedBinAccept (3 / 2) 4 := by
  have hr : (1 : Rat) ≤ (3 / 2 : Rat) := by grind
  rw [expectedBinAccept_T1 hr, expectedBinAccept_T2 hr, expectedBinAccept_T4 hr]
  have hz1 : ratZPow (3 / 2) 1 = (3 : Rat) / 2 := ratZPow_div_pos 3 2 (by decide) (by decide) 1
  have hz2 : ratZPow (3 / 2) 2 = (9 : Rat) / 4 := ratZPow_div_pos 3 2 (by decide) (by decide) 2
  have hz3 : ratZPow (3 / 2) 3 = (27 : Rat) / 8 := ratZPow_div_pos 3 2 (by decide) (by decide) 3
  have hz4 : ratZPow (3 / 2) 4 = (81 : Rat) / 16 := ratZPow_div_pos 3 2 (by decide) (by decide) 4
  have hz6 : ratZPow (3 / 2) 6 = (729 : Rat) / 64 := ratZPow_div_pos 3 2 (by decide) (by decide) 6
  have hz12 : ratZPow (3 / 2) 12 = (531441 : Rat) / 4096 := ratZPow_div_pos 3 2 (by decide) (by decide) 12
  have hzn1 : ratZPow (3 / 2) (-1) = (2 : Rat) / 3 := ratZPow_div_neg 3 2 (by decide) (by decide) 1 (by decide)
  have hzn2 : ratZPow (3 / 2) (-2) = (4 : Rat) / 9 := ratZPow_div_neg 3 2 (by decide) (by decide) 2 (by decide)
  have hzn3 : ratZPow (3 / 2) (-3) = (8 : Rat) / 27 := ratZPow_div_neg 3 2 (by decide) (by decide) 3 (by decide)
  have hzn4 : ratZPow (3 / 2) (-4) = (16 : Rat) / 81 := ratZPow_div_neg 3 2 (by decide) (by decide) 4 (by decide)
  have hzn6 : ratZPow (3 / 2) (-6) = (64 : Rat) / 729 := ratZPow_div_neg 3 2 (by decide) (by decide) 6 (by decide)
  have hzn12 : ratZPow (3 / 2) (-12) = (4096 : Rat) / 531441 := ratZPow_div_neg 3 2 (by decide) (by decide) 12 (by decide)
  rw [hz1, hz2, hz3, hz4, hz6, hz12, hzn1, hzn2, hzn3, hzn4, hzn6, hzn12]
  grind

theorem binary_rescue_5_4 :
    expectedBinAccept (5 / 4) 1 < expectedBinAccept (5 / 4) 2 ∧
    expectedBinAccept (5 / 4) 2 < expectedBinAccept (5 / 4) 4 := by
  have hr : (1 : Rat) ≤ (5 / 4 : Rat) := by grind
  rw [expectedBinAccept_T1 hr, expectedBinAccept_T2 hr, expectedBinAccept_T4 hr]
  have hz1 : ratZPow (5 / 4) 1 = (5 : Rat) / 4 := ratZPow_div_pos 5 4 (by decide) (by decide) 1
  have hz2 : ratZPow (5 / 4) 2 = (25 : Rat) / 16 := ratZPow_div_pos 5 4 (by decide) (by decide) 2
  have hz3 : ratZPow (5 / 4) 3 = (125 : Rat) / 64 := ratZPow_div_pos 5 4 (by decide) (by decide) 3
  have hz4 : ratZPow (5 / 4) 4 = (625 : Rat) / 256 := ratZPow_div_pos 5 4 (by decide) (by decide) 4
  have hz6 : ratZPow (5 / 4) 6 = (15625 : Rat) / 4096 := ratZPow_div_pos 5 4 (by decide) (by decide) 6
  have hz12 : ratZPow (5 / 4) 12 = (244140625 : Rat) / 16777216 := ratZPow_div_pos 5 4 (by decide) (by decide) 12
  have hzn1 : ratZPow (5 / 4) (-1) = (4 : Rat) / 5 := ratZPow_div_neg 5 4 (by decide) (by decide) 1 (by decide)
  have hzn2 : ratZPow (5 / 4) (-2) = (16 : Rat) / 25 := ratZPow_div_neg 5 4 (by decide) (by decide) 2 (by decide)
  have hzn3 : ratZPow (5 / 4) (-3) = (64 : Rat) / 125 := ratZPow_div_neg 5 4 (by decide) (by decide) 3 (by decide)
  have hzn4 : ratZPow (5 / 4) (-4) = (256 : Rat) / 625 := ratZPow_div_neg 5 4 (by decide) (by decide) 4 (by decide)
  have hzn6 : ratZPow (5 / 4) (-6) = (4096 : Rat) / 15625 := ratZPow_div_neg 5 4 (by decide) (by decide) 6 (by decide)
  have hzn12 : ratZPow (5 / 4) (-12) = (16777216 : Rat) / 244140625 := ratZPow_div_neg 5 4 (by decide) (by decide) 12 (by decide)
  rw [hz1, hz2, hz3, hz4, hz6, hz12, hzn1, hzn2, hzn3, hzn4, hzn6, hzn12]
  grind

/-! ### Exact 3-Class Softmax Rescue Witness (`r = 3/2` and `r = 5/4`) -/

/-- Exact acceptance of symmetric 3-class softmax `(z, -z, 0)` vs `(zt, -zt, 0)` when
    `p_0, p_1, p_2` and `q_0, q_1, q_2` are ordered cleanly. -/
theorem triAccept_explicit (r : Rat) (a b : Int) :
    acceptRate (triRatSoftmax r a (-a) 0) (triRatSoftmax r b (-b) 0) =
      let wa := ratZPow r a
      let wna := ratZPow r (-a)
      let wb := ratZPow r b
      let wnb := ratZPow r (-b)
      let sa := wa + wna + 1
      let sb := wb + wnb + 1
      ratMin (wa / sa) (wb / sb) + ratMin (wna / sa) (wnb / sb) + ratMin (1 / sa) (1 / sb) := by
  simp only [acceptRate, triRatSoftmax, ratSoftmax, normProb, finSum, finSumAux, Rat.zero_add,
    ↓reduceIte, Nat.one_ne_zero]
  rfl

theorem triAccept_case {r : Rat} {a b : Int} {wa wna wb wnb c0 c1 c2 : Rat}
    (hwa : ratZPow r a = wa) (hwna : ratZPow r (-a) = wna)
    (hwb : ratZPow r b = wb) (hwnb : ratZPow r (-b) = wnb)
    (h0 : ratMin (wa / (wa + wna + 1)) (wb / (wb + wnb + 1)) = c0)
    (h1 : ratMin (wna / (wa + wna + 1)) (wnb / (wb + wnb + 1)) = c1)
    (h2 : ratMin (1 / (wa + wna + 1)) (1 / (wb + wnb + 1)) = c2) :
    acceptRate (triRatSoftmax r a (-a) 0) (triRatSoftmax r b (-b) 0) = c0 + c1 + c2 := by
  rw [triAccept_explicit]
  simp only [hwa, hwna, hwb, hwnb, h0, h1, h2]

theorem tri_symm {r : Rat} (a b : Int) :
    acceptRate (triRatSoftmax r (-a) (-(-a)) 0) (triRatSoftmax r (-b) (-(-b)) 0) =
    acceptRate (triRatSoftmax r a (-a) 0) (triRatSoftmax r b (-b) 0) := by
  rw [triAccept_explicit, triAccept_explicit]
  simp only [Int.neg_neg]
  have h1 : ratZPow r (-a) + ratZPow r a + 1 = ratZPow r a + ratZPow r (-a) + 1 := by grind
  have h2 : ratZPow r (-b) + ratZPow r b + 1 = ratZPow r b + ratZPow r (-b) + 1 := by grind
  rw [h1, h2]
  grind

theorem expectedTriAccept_T1 (r : Rat) :
    expectedTriAccept r 1 =
      (3 / 8) * acceptRate (triRatSoftmax r 4 (-4) 0) (triRatSoftmax r (-4) (-(-4)) 0) +
      (1 / 4) * acceptRate (triRatSoftmax r 4 (-4) 0) (triRatSoftmax r 4 (-4) 0) +
      (3 / 8) * acceptRate (triRatSoftmax r 4 (-4) 0) (triRatSoftmax r 12 (-12) 0) := by
  simp only [expectedTriAccept, finSum, finSumAux, sigProb, sigVal, noiseProb, noiseVal, Rat.zero_add]
  have hd1 : (-4 + -8 : Int) / 1 = -12 := by decide
  have hd1n : (-(-4 + -8) : Int) / 1 = -(-12) := by decide
  have hd2 : (-4 + 0 : Int) / 1 = -4 := by decide
  have hd2n : (-(-4 + 0) : Int) / 1 = -(-4) := by decide
  have hd3 : (-4 + 8 : Int) / 1 = 4 := by decide
  have hd3n : (-(-4 + 8) : Int) / 1 = -4 := by decide
  have hd4 : (4 + -8 : Int) / 1 = -4 := by decide
  have hd4n : (-(4 + -8) : Int) / 1 = -(-4) := by decide
  have hd5 : (4 + 0 : Int) / 1 = 4 := by decide
  have hd5n : (-(4 + 0) : Int) / 1 = -4 := by decide
  have hd6 : (4 + 8 : Int) / 1 = 12 := by decide
  have hd6n : (-(4 + 8) : Int) / 1 = -12 := by decide
  rw [hd1, hd1n, hd2, hd2n, hd3, hd3n, hd4, hd4n, hd5, hd5n, hd6, hd6n]
  have hs1 := tri_symm (r := r) 4 12
  have hs2 := tri_symm (r := r) 4 4
  have hs3 := tri_symm (r := r) 4 (-4)
  simp only [Int.neg_neg] at hs1 hs2 hs3 ⊢
  rw [hs1, hs2, hs3]
  grind

theorem expectedTriAccept_T2 (r : Rat) :
    expectedTriAccept r 2 =
      (3 / 8) * acceptRate (triRatSoftmax r 4 (-4) 0) (triRatSoftmax r (-2) (-(-2)) 0) +
      (1 / 4) * acceptRate (triRatSoftmax r 4 (-4) 0) (triRatSoftmax r 2 (-2) 0) +
      (3 / 8) * acceptRate (triRatSoftmax r 4 (-4) 0) (triRatSoftmax r 6 (-6) 0) := by
  simp only [expectedTriAccept, finSum, finSumAux, sigProb, sigVal, noiseProb, noiseVal, Rat.zero_add]
  have hd1 : (-4 + -8 : Int) / 2 = -6 := by decide
  have hd1n : (-(-4 + -8) : Int) / 2 = -(-6) := by decide
  have hd2 : (-4 + 0 : Int) / 2 = -2 := by decide
  have hd2n : (-(-4 + 0) : Int) / 2 = -(-2) := by decide
  have hd3 : (-4 + 8 : Int) / 2 = 2 := by decide
  have hd3n : (-(-4 + 8) : Int) / 2 = -2 := by decide
  have hd4 : (4 + -8 : Int) / 2 = -2 := by decide
  have hd4n : (-(4 + -8) : Int) / 2 = -(-2) := by decide
  have hd5 : (4 + 0 : Int) / 2 = 2 := by decide
  have hd5n : (-(4 + 0) : Int) / 2 = -2 := by decide
  have hd6 : (4 + 8 : Int) / 2 = 6 := by decide
  have hd6n : (-(4 + 8) : Int) / 2 = -6 := by decide
  rw [hd1, hd1n, hd2, hd2n, hd3, hd3n, hd4, hd4n, hd5, hd5n, hd6, hd6n]
  have hs1 := tri_symm (r := r) 4 6
  have hs2 := tri_symm (r := r) 4 2
  have hs3 := tri_symm (r := r) 4 (-2)
  simp only [Int.neg_neg] at hs1 hs2 hs3 ⊢
  rw [hs1, hs2, hs3]
  grind

theorem expectedTriAccept_T4 (r : Rat) :
    expectedTriAccept r 4 =
      (3 / 8) * acceptRate (triRatSoftmax r 4 (-4) 0) (triRatSoftmax r (-1) (-(-1)) 0) +
      (1 / 4) * acceptRate (triRatSoftmax r 4 (-4) 0) (triRatSoftmax r 1 (-1) 0) +
      (3 / 8) * acceptRate (triRatSoftmax r 4 (-4) 0) (triRatSoftmax r 3 (-3) 0) := by
  simp only [expectedTriAccept, finSum, finSumAux, sigProb, sigVal, noiseProb, noiseVal, Rat.zero_add]
  have hd1 : (-4 + -8 : Int) / 4 = -3 := by decide
  have hd1n : (-(-4 + -8) : Int) / 4 = -(-3) := by decide
  have hd2 : (-4 + 0 : Int) / 4 = -1 := by decide
  have hd2n : (-(-4 + 0) : Int) / 4 = -(-1) := by decide
  have hd3 : (-4 + 8 : Int) / 4 = 1 := by decide
  have hd3n : (-(-4 + 8) : Int) / 4 = -1 := by decide
  have hd4 : (4 + -8 : Int) / 4 = -1 := by decide
  have hd4n : (-(4 + -8) : Int) / 4 = -(-1) := by decide
  have hd5 : (4 + 0 : Int) / 4 = 1 := by decide
  have hd5n : (-(4 + 0) : Int) / 4 = -1 := by decide
  have hd6 : (4 + 8 : Int) / 4 = 3 := by decide
  have hd6n : (-(4 + 8) : Int) / 4 = -3 := by decide
  rw [hd1, hd1n, hd2, hd2n, hd3, hd3n, hd4, hd4n, hd5, hd5n, hd6, hd6n]
  have hs1 := tri_symm (r := r) 4 3
  have hs2 := tri_symm (r := r) 4 1
  have hs3 := tri_symm (r := r) 4 (-1)
  simp only [Int.neg_neg] at hs1 hs2 hs3 ⊢
  rw [hs1, hs2, hs3]
  grind

/-- Helper: resolve `ratMin` for two explicit rational numbers using `grind`. -/
theorem triAccept_eval {r : Rat} {a b : Int} {wa wna wb wnb : Rat}
    (hwa : ratZPow r a = wa) (hwna : ratZPow r (-a) = wna)
    (hwb : ratZPow r b = wb) (hwnb : ratZPow r (-b) = wnb)
    {s0 s1 s2 : Rat}
    (h0 : ratMin (wa / (wa + wna + 1)) (wb / (wb + wnb + 1)) = s0)
    (h1 : ratMin (wna / (wa + wna + 1)) (wnb / (wb + wnb + 1)) = s1)
    (h2 : ratMin (1 / (wa + wna + 1)) (1 / (wb + wnb + 1)) = s2) :
    acceptRate (triRatSoftmax r a (-a) 0) (triRatSoftmax r b (-b) 0) = s0 + s1 + s2 :=
  triAccept_case hwa hwna hwb hwnb h0 h1 h2

theorem multiclass_rescue_3_2 :
    expectedTriAccept (3 / 2) 1 < expectedTriAccept (3 / 2) 2 ∧
    expectedTriAccept (3 / 2) 2 < expectedTriAccept (3 / 2) 4 := by
  rw [expectedTriAccept_T1, expectedTriAccept_T2, expectedTriAccept_T4]
  have hz1 : ratZPow (3 / 2) 1 = (3 : Rat) / 2 := ratZPow_div_pos 3 2 (by decide) (by decide) 1
  have hz2 : ratZPow (3 / 2) 2 = (9 : Rat) / 4 := ratZPow_div_pos 3 2 (by decide) (by decide) 2
  have hz3 : ratZPow (3 / 2) 3 = (27 : Rat) / 8 := ratZPow_div_pos 3 2 (by decide) (by decide) 3
  have hz4 : ratZPow (3 / 2) 4 = (81 : Rat) / 16 := ratZPow_div_pos 3 2 (by decide) (by decide) 4
  have hz6 : ratZPow (3 / 2) 6 = (729 : Rat) / 64 := ratZPow_div_pos 3 2 (by decide) (by decide) 6
  have hz12 : ratZPow (3 / 2) 12 = (531441 : Rat) / 4096 := ratZPow_div_pos 3 2 (by decide) (by decide) 12
  have hzn1 : ratZPow (3 / 2) (-1) = (2 : Rat) / 3 := ratZPow_div_neg 3 2 (by decide) (by decide) 1 (by decide)
  have hzn2 : ratZPow (3 / 2) (-2) = (4 : Rat) / 9 := ratZPow_div_neg 3 2 (by decide) (by decide) 2 (by decide)
  have hzn3 : ratZPow (3 / 2) (-3) = (8 : Rat) / 27 := ratZPow_div_neg 3 2 (by decide) (by decide) 3 (by decide)
  have hzn4 : ratZPow (3 / 2) (-4) = (16 : Rat) / 81 := ratZPow_div_neg 3 2 (by decide) (by decide) 4 (by decide)
  have hzn6 : ratZPow (3 / 2) (-6) = (64 : Rat) / 729 := ratZPow_div_neg 3 2 (by decide) (by decide) 6 (by decide)
  have hzn12 : ratZPow (3 / 2) (-12) = (4096 : Rat) / 531441 := ratZPow_div_neg 3 2 (by decide) (by decide) 12 (by decide)
  -- For any b ≤ 4 (b ∈ {-4, -2, -1, 1, 2, 3, 4}), p0 ≥ q0, p1 ≤ q1, and for |b| ≤ 4, p2 ≤ q2;
  -- for b > 4 (b ∈ {6, 12}), p0 ≤ q0, p1 ≥ q1, p2 ≥ q2!
  have ht_n4 : acceptRate (triRatSoftmax (3 / 2) 4 (-4) 0) (triRatSoftmax (3 / 2) (-4) (-(-4)) 0) =
      ((16 : Rat) / 81) / ((81 : Rat) / 16 + 16 / 81 + 1) +
      ((16 : Rat) / 81) / ((81 : Rat) / 16 + 16 / 81 + 1) +
      (1 : Rat) / ((81 : Rat) / 16 + 16 / 81 + 1) := by
    refine triAccept_eval hz4 hzn4 hzn4 (by simp only [Int.neg_neg]; exact hz4) ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]; grind
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_4 : acceptRate (triRatSoftmax (3 / 2) 4 (-4) 0) (triRatSoftmax (3 / 2) 4 (-4) 0) = 1 := by
    simp only [triAccept_explicit, ratMin_self, hz4, hzn4]; grind
  have ht_12 : acceptRate (triRatSoftmax (3 / 2) 4 (-4) 0) (triRatSoftmax (3 / 2) 12 (-12) 0) =
      ((81 : Rat) / 16) / ((81 : Rat) / 16 + 16 / 81 + 1) +
      ((4096 : Rat) / 531441) / ((531441 : Rat) / 4096 + 4096 / 531441 + 1) +
      (1 : Rat) / ((531441 : Rat) / 4096 + 4096 / 531441 + 1) := by
    refine triAccept_eval hz4 hzn4 hz12 hzn12 ?_ ?_ ?_
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_ge (by grind)]
  have ht_n2 : acceptRate (triRatSoftmax (3 / 2) 4 (-4) 0) (triRatSoftmax (3 / 2) (-2) (-(-2)) 0) =
      ((4 : Rat) / 9) / ((4 : Rat) / 9 + 9 / 4 + 1) +
      ((16 : Rat) / 81) / ((81 : Rat) / 16 + 16 / 81 + 1) +
      (1 : Rat) / ((81 : Rat) / 16 + 16 / 81 + 1) := by
    refine triAccept_eval hz4 hzn4 hzn2 (by simp only [Int.neg_neg]; exact hz2) ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_2 : acceptRate (triRatSoftmax (3 / 2) 4 (-4) 0) (triRatSoftmax (3 / 2) 2 (-2) 0) =
      ((9 : Rat) / 4) / ((9 : Rat) / 4 + 4 / 9 + 1) +
      ((16 : Rat) / 81) / ((81 : Rat) / 16 + 16 / 81 + 1) +
      (1 : Rat) / ((81 : Rat) / 16 + 16 / 81 + 1) := by
    refine triAccept_eval hz4 hzn4 hz2 hzn2 ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_6 : acceptRate (triRatSoftmax (3 / 2) 4 (-4) 0) (triRatSoftmax (3 / 2) 6 (-6) 0) =
      ((81 : Rat) / 16) / ((81 : Rat) / 16 + 16 / 81 + 1) +
      ((64 : Rat) / 729) / ((729 : Rat) / 64 + 64 / 729 + 1) +
      (1 : Rat) / ((729 : Rat) / 64 + 64 / 729 + 1) := by
    refine triAccept_eval hz4 hzn4 hz6 hzn6 ?_ ?_ ?_
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_ge (by grind)]
  have ht_n1 : acceptRate (triRatSoftmax (3 / 2) 4 (-4) 0) (triRatSoftmax (3 / 2) (-1) (-(-1)) 0) =
      ((2 : Rat) / 3) / ((2 : Rat) / 3 + 3 / 2 + 1) +
      ((16 : Rat) / 81) / ((81 : Rat) / 16 + 16 / 81 + 1) +
      (1 : Rat) / ((81 : Rat) / 16 + 16 / 81 + 1) := by
    refine triAccept_eval hz4 hzn4 hzn1 (by simp only [Int.neg_neg]; exact hz1) ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_1 : acceptRate (triRatSoftmax (3 / 2) 4 (-4) 0) (triRatSoftmax (3 / 2) 1 (-1) 0) =
      ((3 : Rat) / 2) / ((3 : Rat) / 2 + 2 / 3 + 1) +
      ((16 : Rat) / 81) / ((81 : Rat) / 16 + 16 / 81 + 1) +
      (1 : Rat) / ((81 : Rat) / 16 + 16 / 81 + 1) := by
    refine triAccept_eval hz4 hzn4 hz1 hzn1 ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_3 : acceptRate (triRatSoftmax (3 / 2) 4 (-4) 0) (triRatSoftmax (3 / 2) 3 (-3) 0) =
      ((27 : Rat) / 8) / ((27 : Rat) / 8 + 8 / 27 + 1) +
      ((16 : Rat) / 81) / ((81 : Rat) / 16 + 16 / 81 + 1) +
      (1 : Rat) / ((81 : Rat) / 16 + 16 / 81 + 1) := by
    refine triAccept_eval hz4 hzn4 hz3 hzn3 ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  rw [ht_n4, ht_4, ht_12, ht_n2, ht_2, ht_6, ht_n1, ht_1, ht_3]
  grind

theorem multiclass_rescue_5_4 :
    expectedTriAccept (5 / 4) 1 < expectedTriAccept (5 / 4) 2 ∧
    expectedTriAccept (5 / 4) 2 < expectedTriAccept (5 / 4) 4 := by
  rw [expectedTriAccept_T1, expectedTriAccept_T2, expectedTriAccept_T4]
  have hz1 : ratZPow (5 / 4) 1 = (5 : Rat) / 4 := ratZPow_div_pos 5 4 (by decide) (by decide) 1
  have hz2 : ratZPow (5 / 4) 2 = (25 : Rat) / 16 := ratZPow_div_pos 5 4 (by decide) (by decide) 2
  have hz3 : ratZPow (5 / 4) 3 = (125 : Rat) / 64 := ratZPow_div_pos 5 4 (by decide) (by decide) 3
  have hz4 : ratZPow (5 / 4) 4 = (625 : Rat) / 256 := ratZPow_div_pos 5 4 (by decide) (by decide) 4
  have hz6 : ratZPow (5 / 4) 6 = (15625 : Rat) / 4096 := ratZPow_div_pos 5 4 (by decide) (by decide) 6
  have hz12 : ratZPow (5 / 4) 12 = (244140625 : Rat) / 16777216 := ratZPow_div_pos 5 4 (by decide) (by decide) 12
  have hzn1 : ratZPow (5 / 4) (-1) = (4 : Rat) / 5 := ratZPow_div_neg 5 4 (by decide) (by decide) 1 (by decide)
  have hzn2 : ratZPow (5 / 4) (-2) = (16 : Rat) / 25 := ratZPow_div_neg 5 4 (by decide) (by decide) 2 (by decide)
  have hzn3 : ratZPow (5 / 4) (-3) = (64 : Rat) / 125 := ratZPow_div_neg 5 4 (by decide) (by decide) 3 (by decide)
  have hzn4 : ratZPow (5 / 4) (-4) = (256 : Rat) / 625 := ratZPow_div_neg 5 4 (by decide) (by decide) 4 (by decide)
  have hzn6 : ratZPow (5 / 4) (-6) = (4096 : Rat) / 15625 := ratZPow_div_neg 5 4 (by decide) (by decide) 6 (by decide)
  have hzn12 : ratZPow (5 / 4) (-12) = (16777216 : Rat) / 244140625 := ratZPow_div_neg 5 4 (by decide) (by decide) 12 (by decide)
  have ht_n4 : acceptRate (triRatSoftmax (5 / 4) 4 (-4) 0) (triRatSoftmax (5 / 4) (-4) (-(-4)) 0) =
      ((256 : Rat) / 625) / ((625 : Rat) / 256 + 256 / 625 + 1) +
      ((256 : Rat) / 625) / ((625 : Rat) / 256 + 256 / 625 + 1) +
      (1 : Rat) / ((625 : Rat) / 256 + 256 / 625 + 1) := by
    refine triAccept_eval hz4 hzn4 hzn4 (by simp only [Int.neg_neg]; exact hz4) ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]; grind
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_4 : acceptRate (triRatSoftmax (5 / 4) 4 (-4) 0) (triRatSoftmax (5 / 4) 4 (-4) 0) = 1 := by
    simp only [triAccept_explicit, ratMin_self, hz4, hzn4]; grind
  have ht_12 : acceptRate (triRatSoftmax (5 / 4) 4 (-4) 0) (triRatSoftmax (5 / 4) 12 (-12) 0) =
      ((625 : Rat) / 256) / ((625 : Rat) / 256 + 256 / 625 + 1) +
      ((16777216 : Rat) / 244140625) / ((244140625 : Rat) / 16777216 + 16777216 / 244140625 + 1) +
      (1 : Rat) / ((244140625 : Rat) / 16777216 + 16777216 / 244140625 + 1) := by
    refine triAccept_eval hz4 hzn4 hz12 hzn12 ?_ ?_ ?_
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_ge (by grind)]
  have ht_n2 : acceptRate (triRatSoftmax (5 / 4) 4 (-4) 0) (triRatSoftmax (5 / 4) (-2) (-(-2)) 0) =
      ((16 : Rat) / 25) / ((16 : Rat) / 25 + 25 / 16 + 1) +
      ((256 : Rat) / 625) / ((625 : Rat) / 256 + 256 / 625 + 1) +
      (1 : Rat) / ((625 : Rat) / 256 + 256 / 625 + 1) := by
    refine triAccept_eval hz4 hzn4 hzn2 (by simp only [Int.neg_neg]; exact hz2) ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_2 : acceptRate (triRatSoftmax (5 / 4) 4 (-4) 0) (triRatSoftmax (5 / 4) 2 (-2) 0) =
      ((25 : Rat) / 16) / ((25 : Rat) / 16 + 16 / 25 + 1) +
      ((256 : Rat) / 625) / ((625 : Rat) / 256 + 256 / 625 + 1) +
      (1 : Rat) / ((625 : Rat) / 256 + 256 / 625 + 1) := by
    refine triAccept_eval hz4 hzn4 hz2 hzn2 ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_6 : acceptRate (triRatSoftmax (5 / 4) 4 (-4) 0) (triRatSoftmax (5 / 4) 6 (-6) 0) =
      ((625 : Rat) / 256) / ((625 : Rat) / 256 + 256 / 625 + 1) +
      ((4096 : Rat) / 15625) / ((15625 : Rat) / 4096 + 4096 / 15625 + 1) +
      (1 : Rat) / ((15625 : Rat) / 4096 + 4096 / 15625 + 1) := by
    refine triAccept_eval hz4 hzn4 hz6 hzn6 ?_ ?_ ?_
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_ge (by grind)]
  have ht_n1 : acceptRate (triRatSoftmax (5 / 4) 4 (-4) 0) (triRatSoftmax (5 / 4) (-1) (-(-1)) 0) =
      ((4 : Rat) / 5) / ((4 : Rat) / 5 + 5 / 4 + 1) +
      ((256 : Rat) / 625) / ((625 : Rat) / 256 + 256 / 625 + 1) +
      (1 : Rat) / ((625 : Rat) / 256 + 256 / 625 + 1) := by
    refine triAccept_eval hz4 hzn4 hzn1 (by simp only [Int.neg_neg]; exact hz1) ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_1 : acceptRate (triRatSoftmax (5 / 4) 4 (-4) 0) (triRatSoftmax (5 / 4) 1 (-1) 0) =
      ((5 : Rat) / 4) / ((5 : Rat) / 4 + 4 / 5 + 1) +
      ((256 : Rat) / 625) / ((625 : Rat) / 256 + 256 / 625 + 1) +
      (1 : Rat) / ((625 : Rat) / 256 + 256 / 625 + 1) := by
    refine triAccept_eval hz4 hzn4 hz1 hzn1 ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  have ht_3 : acceptRate (triRatSoftmax (5 / 4) 4 (-4) 0) (triRatSoftmax (5 / 4) 3 (-3) 0) =
      ((125 : Rat) / 64) / ((125 : Rat) / 64 + 64 / 125 + 1) +
      ((256 : Rat) / 625) / ((625 : Rat) / 256 + 256 / 625 + 1) +
      (1 : Rat) / ((625 : Rat) / 256 + 256 / 625 + 1) := by
    refine triAccept_eval hz4 hzn4 hz3 hzn3 ?_ ?_ ?_
    · rw [ratMin_of_ge (by grind)]
    · rw [ratMin_of_le (by grind)]
    · rw [ratMin_of_le (by grind)]
  rw [ht_n4, ht_4, ht_12, ht_n2, ht_2, ht_6, ht_n1, ht_1, ht_3]
  grind

theorem fused_dequant_scale_absorption (s_deq z_hat T : Rat) (hT : T ≠ 0) :
    (s_deq * z_hat) / T = (s_deq / T) * z_hat := by
  apply rat_eq_of_mul_eq_mul_right hT
  rw [rat_div_mul_cancel hT]
  symm
  calc (s_deq / T) * z_hat * T
      = ((s_deq / T) * T) * z_hat := by grind
    _ = s_deq * z_hat := by rw [rat_div_mul_cancel hT]

/-- Headline Theorem 6 (`wiener_temperature_exact_acceptance_rescue_witnesses`). -/
theorem wiener_temperature_exact_acceptance_rescue_witnesses :
    (finSum sigProb = 1 ∧
     finSum noiseProb = 1 ∧
     finSum (fun i : Fin 2 => sigProb i * (sigVal i : Rat)) = 0 ∧
     finSum (fun j : Fin 3 => noiseProb j * (noiseVal j : Rat)) = 0 ∧
     finSum (fun i : Fin 2 => sigProb i * ((sigVal i : Rat) * (sigVal i : Rat))) = 16 ∧
     finSum (fun j : Fin 3 => noiseProb j * ((noiseVal j : Rat) * (noiseVal j : Rat))) = 48 ∧
     finSum (fun i : Fin 2 => sigProb i * finSum (fun j : Fin 3 =>
       noiseProb j * ((sigVal i : Rat) * (noiseVal j : Rat)))) = 0 ∧
     wienerTemp 16 48 = 4 ∧
     (2 : Rat) * 2 = wienerTemp 16 48) ∧
    (expectedBinAccept (3 / 2) 1 < expectedBinAccept (3 / 2) 2 ∧
     expectedBinAccept (3 / 2) 2 < expectedBinAccept (3 / 2) 4 ∧
     expectedBinAccept (5 / 4) 1 < expectedBinAccept (5 / 4) 2 ∧
     expectedBinAccept (5 / 4) 2 < expectedBinAccept (5 / 4) 4) ∧
    (expectedTriAccept (3 / 2) 1 < expectedTriAccept (3 / 2) 2 ∧
     expectedTriAccept (3 / 2) 2 < expectedTriAccept (3 / 2) 4 ∧
     expectedTriAccept (5 / 4) 1 < expectedTriAccept (5 / 4) 2 ∧
     expectedTriAccept (5 / 4) 2 < expectedTriAccept (5 / 4) 4) ∧
    (∀ s_deq z_hat T : Rat, T ≠ 0 →
      (s_deq * z_hat) / T = (s_deq / T) * z_hat) :=
  ⟨ensemble_moments_exact,
   ⟨binary_rescue_3_2.1, binary_rescue_3_2.2, binary_rescue_5_4.1, binary_rescue_5_4.2⟩,
   ⟨multiclass_rescue_3_2.1, multiclass_rescue_3_2.2, multiclass_rescue_5_4.1, multiclass_rescue_5_4.2⟩,
   fused_dequant_scale_absorption⟩

end SpecDecWienerTemp
