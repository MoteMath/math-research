/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnDyadicSlack.Defs

/-!
# Exact Dyadic Power-of-Two Rescaling & Eager One-ULP-Per-Step Collapse

Pure-`Init` (zero Mathlib) proofs of:
1. `dyadic_power_of_two_rescale_zero_mantissa_error`: multiplying any normal binary float
   `(s, e, m)` by exact `2^-k` shifts only the exponent `e ↦ e - k` with exact `0`
   mantissa rounding error, contrasting with eager non-dyadic RNE midpoints which inject
   exact half-ULP error `1 / 2^(p+1) > 0`.
2. `eager_online_softmax_one_ulp_per_step_collapse`: universal inductive IEEE-754 RNE
   proof that sequential multiplication by `α = 1 - 2^{-(p+1)}` loses exact `1` ULP per
   step (`seqPow p (m * 2^p) = 2^-m`), strictly underestimating true exponential decay
   `(1 - 2^{-(p+1)})^(m * 2^p)` for all `p ≥ 1, m ≥ 1`, whereas lazy dyadic deferral
   eliminates intermediate multiplicative drift completely.
-/

namespace FlashAttnDyadicSlack

/-! ### Pure-`Init` `Rat` Order & Cancellation Helpers -/

theorem rat_natCast_add (a b : Nat) : (((a + b : Nat) : Rat)) = (a : Rat) + (b : Rat) :=
  Rat.natCast_add a b

theorem rat_natCast_mul (a b : Nat) : (((a * b : Nat) : Rat)) = (a : Rat) * (b : Rat) :=
  Rat.natCast_mul a b

theorem rat_add_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) ≤ b) :
    (0 : Rat) ≤ a + b := by
  have h1 := (Rat.add_le_add_right (c := b)).mpr ha
  rw [Rat.zero_add] at h1
  exact Rat.le_trans hb h1

theorem rat_natCast_nonneg (a : Nat) : (0 : Rat) ≤ (a : Rat) := by
  induction a with
  | zero => decide
  | succ a ih =>
    rw [Rat.natCast_add]
    exact rat_add_nonneg ih (by decide : (0 : Rat) ≤ (1 : Rat))

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have hle : a ≤ c := Rat.le_trans (Rat.le_of_lt h1) h2
  have hne : a ≠ c := by
    intro heq
    have hba : b ≤ a := heq ▸ h2
    exact Rat.ne_of_gt h1 (Rat.le_antisymm hba (Rat.le_of_lt h1))
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_natCast_pos {a : Nat} (h : 0 < a) : (0 : Rat) < (a : Rat) := by
  cases a with
  | zero => omega
  | succ a =>
    rw [Rat.natCast_add]
    have h1 := (Rat.add_le_add_right (c := (1 : Rat))).mpr (rat_natCast_nonneg a)
    rw [Rat.zero_add] at h1
    exact rat_lt_of_lt_of_le (by decide : (0 : Rat) < (1 : Rat)) h1

theorem rat_natCast_le {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have hsum : b = a + (b - a) := (Nat.add_sub_cancel' h).symm
  rw [hsum, Rat.natCast_add]
  have h1 := (Rat.add_le_add_right (c := (a : Rat))).mpr (rat_natCast_nonneg (b - a))
  rw [Rat.zero_add, Rat.add_comm] at h1
  exact h1

theorem rat_natCast_lt {a b : Nat} (h : a < b) : (a : Rat) < (b : Rat) := by
  have hsum : b = a + (b - a) := (Nat.add_sub_cancel' (Nat.le_of_lt h)).symm
  have hpos : 0 < b - a := by omega
  rw [hsum, Rat.natCast_add]
  have h1 := (Rat.add_lt_add_right (c := (a : Rat))).mpr (rat_natCast_pos hpos)
  rw [Rat.zero_add, Rat.add_comm] at h1
  exact h1

theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c :=
  rat_lt_of_lt_of_le h1 (Rat.le_of_lt h2)

theorem rat_mul_right_cancel {a b c : Rat} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have h1 := congrArg (· * c⁻¹) h
  rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_inv_cancel c hc, Rat.mul_one, Rat.mul_one] at h1
  exact h1

theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by
  have := (Rat.add_le_add_right (c := -b)).mpr h
  grind

theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by
  have := (Rat.add_le_add_right (c := b)).mpr h
  grind

theorem rat_sub_pos {a b : Rat} (h : b < a) : (0 : Rat) < a - b := by
  have h1 : (0 : Rat) ≤ a - b := rat_sub_nonneg (Rat.le_of_lt h)
  have hne : a - b ≠ 0 := by
    intro h0
    have heq : a = b := by grind
    exact Rat.ne_of_gt h heq
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_lt_of_sub_pos {a b : Rat} (h : (0 : Rat) < a - b) : b < a := by
  have h1 : b ≤ a := rat_le_of_sub_nonneg (Rat.le_of_lt h)
  have hne : b ≠ a := by
    intro h0
    have : a - b = 0 := by grind
    exact Rat.ne_of_gt h this
  exact Rat.lt_of_le_of_ne h1 hne

theorem rat_mul_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a * b := by
  have h1 : (0 : Rat) ≤ a * b := Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hb)
  have hne : a * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact Rat.ne_of_gt ha h
    | inr h => exact Rat.ne_of_gt hb h
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_inv_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < a⁻¹ := by
  have hne : a ≠ 0 := Rat.ne_of_gt ha
  cases (Rat.le_total (a := (0 : Rat)) (b := a⁻¹)) with
  | inl hge =>
    have hinv_ne : a⁻¹ ≠ 0 := by
      intro heq
      have hmul : a * a⁻¹ = 0 := by rw [heq, Rat.mul_zero]
      rw [Rat.mul_inv_cancel a hne] at hmul
      exact absurd hmul (by decide)
    exact Rat.lt_of_le_of_ne hge (Ne.symm hinv_ne)
  | inr hle =>
    have hneg : (0 : Rat) ≤ -a⁻¹ := by
      have := rat_sub_nonneg hle
      grind
    have hprod : (0 : Rat) ≤ a * (-a⁻¹) := Rat.mul_nonneg (Rat.le_of_lt ha) hneg
    have heq : a * (-a⁻¹) = -1 := by
      rw [Rat.mul_neg, Rat.mul_inv_cancel a hne]
    rw [heq] at hprod
    exact absurd hprod (by decide)

theorem rat_div_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

theorem rat_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

theorem rat_mul_le_mul_of_nonneg_left {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    c * a ≤ c * b := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ b - a := rat_sub_nonneg h
  have h2 : (0 : Rat) ≤ c * (b - a) := Rat.mul_nonneg hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]; exact h2

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_le_mul_of_nonneg_left h hc

theorem rat_mul_lt_mul_of_pos_left {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    c * a < c * b := by
  apply rat_lt_of_sub_pos
  have h1 : (0 : Rat) < b - a := rat_sub_pos h
  have h2 : (0 : Rat) < c * (b - a) := rat_mul_pos hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]; exact h2

theorem rat_mul_lt_mul_of_pos_right {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    a * c < b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_lt_mul_of_pos_left h hc

theorem rat_lt_of_mul_lt_mul_right {a b c : Rat} (hc : (0 : Rat) < c) (h : a * c < b * c) :
    a < b := by
  have hinv := rat_inv_pos hc
  have h1 := rat_mul_lt_mul_of_pos_right h hinv
  have hne := Rat.ne_of_gt hc
  rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_inv_cancel c hne, Rat.mul_one, Rat.mul_one] at h1
  exact h1

/-! ### Helper Arithmetic Lemmas on `pow2Rat`, `invPow2Rat`, `pow2IntRat`, and `ratPow` -/

theorem pow2Rat_pos (k : Nat) : (0 : Rat) < pow2Rat k := by
  unfold pow2Rat
  exact rat_natCast_lt (Nat.two_pow_pos k)

theorem pow2Rat_ne_zero (k : Nat) : pow2Rat k ≠ (0 : Rat) :=
  Rat.ne_of_gt (pow2Rat_pos k)

theorem pow2Rat_add (a b : Nat) : pow2Rat (a + b) = pow2Rat a * pow2Rat b := by
  unfold pow2Rat
  rw [Nat.pow_add]
  exact rat_natCast_mul (2 ^ a) (2 ^ b)

theorem invPow2Rat_pos (k : Nat) : (0 : Rat) < invPow2Rat k := by
  unfold invPow2Rat
  exact rat_div_pos (by decide : (0 : Rat) < 1) (pow2Rat_pos k)

theorem invPow2Rat_ne_zero (k : Nat) : invPow2Rat k ≠ (0 : Rat) :=
  Rat.ne_of_gt (invPow2Rat_pos k)

theorem invPow2Rat_mul_pow2Rat (k : Nat) : invPow2Rat k * pow2Rat k = (1 : Rat) := by
  unfold invPow2Rat
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.inv_mul_cancel (pow2Rat k) (pow2Rat_ne_zero k)

theorem pow2Rat_mul_invPow2Rat (k : Nat) : pow2Rat k * invPow2Rat k = (1 : Rat) := by
  rw [Rat.mul_comm]
  exact invPow2Rat_mul_pow2Rat k

theorem invPow2Rat_add (a b : Nat) : invPow2Rat (a + b) = invPow2Rat a * invPow2Rat b := by
  apply rat_mul_right_cancel (pow2Rat_ne_zero (a + b))
  rw [invPow2Rat_mul_pow2Rat, pow2Rat_add]
  symm
  calc
    (invPow2Rat a * invPow2Rat b) * (pow2Rat a * pow2Rat b)
        = (invPow2Rat a * pow2Rat a) * (invPow2Rat b * pow2Rat b) := by grind
    _ = 1 * 1 := by rw [invPow2Rat_mul_pow2Rat, invPow2Rat_mul_pow2Rat]
    _ = 1 := by grind

theorem pow2IntRat_sub_nat (e : Int) (k : Nat) :
    pow2IntRat (e - (k : Int)) = pow2IntRat e * invPow2Rat k := by
  apply rat_mul_right_cancel (pow2Rat_ne_zero k)
  rw [Rat.mul_assoc, invPow2Rat_mul_pow2Rat, Rat.mul_one]
  unfold pow2IntRat
  split
  · rename_i h1
    have h2 : (0 : Int) ≤ e := by omega
    simp only [h2, ↓reduceIte]
    have hsum : (e - (k : Int)).toNat + k = e.toNat := by omega
    change pow2Rat (e - (k : Int)).toNat * pow2Rat k = pow2Rat e.toNat
    rw [← pow2Rat_add, hsum]
  · rename_i h1
    split
    · rename_i h2
      have hsum : (-(e - (k : Int))).toNat + e.toNat = k := by omega
      change invPow2Rat (-(e - (k : Int))).toNat * pow2Rat k = pow2Rat e.toNat
      have hk : pow2Rat k = pow2Rat (-(e - (k : Int))).toNat * pow2Rat e.toNat := by
        have h1' : pow2Rat ((-(e - (k : Int))).toNat + e.toNat) =
            pow2Rat (-(e - (k : Int))).toNat * pow2Rat e.toNat :=
          pow2Rat_add _ _
        rw [hsum] at h1'
        exact h1'
      rw [hk, ← Rat.mul_assoc, invPow2Rat_mul_pow2Rat, Rat.one_mul]
    · rename_i h2
      have hsum : (-(e - (k : Int))).toNat = (-e).toNat + k := by omega
      change invPow2Rat (-(e - (k : Int))).toNat * pow2Rat k = invPow2Rat (-e).toNat
      rw [hsum, invPow2Rat_add, Rat.mul_assoc, invPow2Rat_mul_pow2Rat, Rat.mul_one]

theorem pow2IntRat_neg_nat (m : Nat) : pow2IntRat (-(m : Int)) = invPow2Rat m := by
  cases m with
  | zero =>
    unfold pow2IntRat invPow2Rat pow2Rat
    simp
    grind
  | succ m =>
    unfold pow2IntRat invPow2Rat pow2Rat
    have hlt : ¬ ((0 : Int) ≤ -((m + 1 : Nat) : Int)) := by omega
    rw [ite_eq_right (fun h => absurd h hlt)]
    have hnat : (-(-((m + 1 : Nat) : Int))).toNat = m + 1 := by omega
    rw [hnat]

/-! ### Theorem 1: Exact Zero Mantissa Rounding Error of Dyadic `2^-k` Rescaling -/

theorem scaleNegPow2_toRat {p : Nat} (x : NormalFloat p) (k : Nat) :
    (x.scaleNegPow2 k).toRat = x.toRat * invPow2Rat k := by
  unfold NormalFloat.toRat NormalFloat.scaleNegPow2 NormalFloat.signRat NormalFloat.sig
  dsimp only
  rw [pow2IntRat_sub_nat]
  grind

theorem scaleNegPow2_compose {p : Nat} (x : NormalFloat p) (k1 k2 : Nat) :
    (x.scaleNegPow2 k1).scaleNegPow2 k2 = x.scaleNegPow2 (k1 + k2) := by
  unfold NormalFloat.scaleNegPow2
  have hexp : x.exp - (k1 : Int) - (k2 : Int) = x.exp - ((k1 + k2 : Nat) : Int) := by omega
  simp [hexp]

theorem rneNatDiv_midpoint_even (q : Nat) (hq : q % 2 = 0) :
    rneNatDiv (2 * q + 1) 2 = q := by
  unfold rneNatDiv
  have hdiv : (2 * q + 1) / 2 = q := by omega
  have hmod : (2 * q + 1) % 2 = 1 := by omega
  simp [hdiv, hmod, hq]

theorem eager_midpoint_half_ulp_error (p : Nat) (hp : 1 ≤ p) :
    rneNatDiv (2 ^ (p + 1) + 1) 2 = 2 ^ p ∧
    (((2 ^ (p + 1) + 1 : Nat) : Rat) / pow2Rat (p + 1)) -
      ((rneNatDiv (2 ^ (p + 1) + 1) 2 : Rat) / pow2Rat p) = invPow2Rat (p + 1) ∧
    (0 : Rat) < invPow2Rat (p + 1) := by
  have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have heven : 2 ^ p % 2 = 0 := by
    cases p with
    | zero => omega
    | succ p' =>
      rw [Nat.pow_succ]
      omega
  have hrne : rneNatDiv (2 ^ (p + 1) + 1) 2 = 2 ^ p := by
    rw [hpow]
    exact rneNatDiv_midpoint_even (2 ^ p) heven
  refine ⟨hrne, ?_, invPow2Rat_pos (p + 1)⟩
  rw [hrne]
  have h1 : ((2 ^ p : Nat) : Rat) / pow2Rat p = 1 := by
    change pow2Rat p / pow2Rat p = 1
    rw [Rat.div_def]
    exact Rat.mul_inv_cancel (pow2Rat p) (pow2Rat_ne_zero p)
  rw [h1]
  have hne : pow2Rat (p + 1) ≠ 0 := pow2Rat_ne_zero (p + 1)
  apply rat_mul_right_cancel hne
  have hsub : ((((2 ^ (p + 1) + 1 : Nat) : Rat) / pow2Rat (p + 1)) - 1) * pow2Rat (p + 1) =
      ((((2 ^ (p + 1) + 1 : Nat) : Rat) / pow2Rat (p + 1)) * pow2Rat (p + 1)) - pow2Rat (p + 1) := by
    grind
  rw [hsub, invPow2Rat_mul_pow2Rat]
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel (pow2Rat (p + 1)) hne, Rat.mul_one]
  unfold pow2Rat
  rw [rat_natCast_add]
  have hcast1 : ((1 : Nat) : Rat) = (1 : Rat) := rfl
  rw [hcast1]
  grind

/-- Headline Theorem 1 (`dyadic_power_of_two_rescale_zero_mantissa_error`). -/
theorem dyadic_power_of_two_rescale_zero_mantissa_error :
    (∀ (p k : Nat) (x : NormalFloat p),
      (x.scaleNegPow2 k).neg = x.neg ∧
      (x.scaleNegPow2 k).mant = x.mant ∧
      (x.scaleNegPow2 k).exp = x.exp - (k : Int) ∧
      (x.scaleNegPow2 k).toRat = x.toRat * invPow2Rat k ∧
      (x.scaleNegPow2 k).toRat - x.toRat * invPow2Rat k = 0) ∧
    (∀ (p k1 k2 : Nat) (x : NormalFloat p),
      (x.scaleNegPow2 k1).scaleNegPow2 k2 = x.scaleNegPow2 (k1 + k2) ∧
      ((x.scaleNegPow2 k1).scaleNegPow2 k2).toRat = x.toRat * invPow2Rat (k1 + k2)) ∧
    (∀ (p k : Nat) (eMin eMax : Int) (x : NormalFloat p),
      eMin + (k : Int) ≤ x.exp → x.exp ≤ eMax →
      eMin ≤ (x.scaleNegPow2 k).exp ∧ (x.scaleNegPow2 k).exp ≤ eMax) ∧
    (∀ (p : Nat), 1 ≤ p →
      rneNatDiv (2 ^ (p + 1) + 1) 2 = 2 ^ p ∧
      (((2 ^ (p + 1) + 1 : Nat) : Rat) / pow2Rat (p + 1)) -
        ((rneNatDiv (2 ^ (p + 1) + 1) 2 : Rat) / pow2Rat p) = invPow2Rat (p + 1) ∧
      (0 : Rat) < invPow2Rat (p + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p k x
    have hval := scaleNegPow2_toRat x k
    refine ⟨rfl, rfl, rfl, hval, ?_⟩
    rw [hval]
    exact Rat.sub_self
  · intro p k1 k2 x
    have hc := scaleNegPow2_compose x k1 k2
    refine ⟨hc, ?_⟩
    rw [hc]
    exact scaleNegPow2_toRat x (k1 + k2)
  · intro p k eMin eMax x hlo hhi
    unfold NormalFloat.scaleNegPow2
    dsimp only
    omega
  · intro p hp
    exact eager_midpoint_half_ulp_error p hp

/-! ### Theorem 2: Eager Online-Softmax One-ULP-Per-Step Collapse -/

theorem rneMulStep_interior (p : Nat) (e : Int) (s : Nat)
    (hlo : 2 ^ p < s) (hhi : s < 2 ^ (p + 1)) :
    rneMulOneMinusHalfUlpStep p (e, s) = (e, s - 1) := by
  unfold rneMulOneMinusHalfUlpStep
  dsimp only
  have hnotle : ¬ s ≤ 2 ^ p := by omega
  rw [ite_eq_right (fun h => absurd h hnotle)]
  congr 1
  unfold rneNatDiv
  have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hden_pos : 0 < 2 ^ (p + 1) := Nat.two_pow_pos (p + 1)
  have hdecomp : s * (2 ^ (p + 1) - 1) = (s - 1) * 2 ^ (p + 1) + (2 ^ (p + 1) - s) := by
    have hs1 : 1 ≤ s := by
      have : 0 < 2 ^ p := Nat.two_pow_pos p
      omega
    have h1 : s * (2 ^ (p + 1) - 1) + s = s * 2 ^ (p + 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have hge : s ≤ s * 2 ^ (p + 1) := Nat.le_mul_of_pos_right s hden_pos
      exact Nat.sub_add_cancel hge
    have h2 : (s - 1) * 2 ^ (p + 1) + (2 ^ (p + 1) - s) + s = s * 2 ^ (p + 1) := by
      rw [Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hhi)]
      rw [Nat.mul_sub_right_distrib, Nat.one_mul]
      have hge : 2 ^ (p + 1) ≤ s * 2 ^ (p + 1) := Nat.le_mul_of_pos_left (2 ^ (p + 1)) hs1
      exact Nat.sub_add_cancel hge
    omega
  have hr_lt : 2 ^ (p + 1) - s < 2 ^ (p + 1) := by omega
  have hdiv : (s * (2 ^ (p + 1) - 1)) / 2 ^ (p + 1) = s - 1 := by
    rw [hdecomp, Nat.mul_comm (s - 1), Nat.mul_add_div hden_pos, Nat.div_eq_of_lt hr_lt, Nat.add_zero]
  have hmod : (s * (2 ^ (p + 1) - 1)) % 2 ^ (p + 1) = 2 ^ (p + 1) - s := by
    rw [hdecomp, Nat.mul_comm (s - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
  have h2r : 2 * (2 ^ (p + 1) - s) < 2 ^ (p + 1) := by omega
  simp [hdiv, hmod, h2r]

theorem rneMulStep_boundary (p : Nat) (e : Int) :
    rneMulOneMinusHalfUlpStep p (e, 2 ^ p) = (e - 1, 2 ^ (p + 1) - 1) := by
  unfold rneMulOneMinusHalfUlpStep
  simp

theorem seqPowState_add (p a b : Nat) (st : Int × Nat) :
    seqPowState p (a + b) st = seqPowState p b (seqPowState p a st) := by
  induction a generalizing st with
  | zero => simp [seqPowState]
  | succ a ih =>
    rw [Nat.succ_add]
    exact ih (rneMulOneMinusHalfUlpStep p st)

theorem seqPowState_descend (p : Nat) (e : Int) :
    ∀ (k s : Nat), 2 ^ p + k = s → s < 2 ^ (p + 1) →
      seqPowState p k (e, s) = (e, 2 ^ p)
  | 0, s, hsum, _ => by
    have hs : s = 2 ^ p := by omega
    simp [seqPowState, hs]
  | k + 1, s, hsum, hhi => by
    have hlo : 2 ^ p < s := by omega
    simp only [seqPowState]
    rw [rneMulStep_interior p e s hlo hhi]
    exact seqPowState_descend p e k (s - 1) (by omega) (by omega)

theorem seqPowState_binade_drop (p : Nat) (e : Int) :
    seqPowState p (2 ^ p) (e, 2 ^ p) = (e - 1, 2 ^ p) := by
  have hpos : 0 < 2 ^ p := Nat.two_pow_pos p
  have hsplit : 2 ^ p = 1 + (2 ^ p - 1) := by omega
  have hlhs : seqPowState p (2 ^ p) (e, 2 ^ p) =
      seqPowState p (1 + (2 ^ p - 1)) (e, 2 ^ p) :=
    congrArg (fun n => seqPowState p n (e, 2 ^ p)) hsplit
  rw [hlhs, seqPowState_add]
  have hstep1 : seqPowState p 1 (e, 2 ^ p) = (e - 1, 2 ^ (p + 1) - 1) := by
    simp [seqPowState, rneMulStep_boundary]
  rw [hstep1]
  have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by
    rw [Nat.pow_succ, Nat.mul_comm]
  exact seqPowState_descend p (e - 1) (2 ^ p - 1) (2 ^ (p + 1) - 1) (by omega) (by omega)

theorem seqPowState_multi_binade (p m : Nat) (e : Int) :
    seqPowState p (m * 2 ^ p) (e, 2 ^ p) = (e - (m : Int), 2 ^ p) := by
  induction m generalizing e with
  | zero =>
    simp [seqPowState]
  | succ m ih =>
    rw [Nat.succ_mul, Nat.add_comm, seqPowState_add, seqPowState_binade_drop, ih]
    have hexp : e - 1 - (m : Int) = e - ((m + 1 : Nat) : Int) := by omega
    simp [hexp]

theorem seqPow_exact (p m : Nat) :
    seqPow p (m * 2 ^ p) = invPow2Rat m := by
  unfold seqPow posFloatVal
  rw [seqPowState_multi_binade]
  dsimp only
  have h1 : ((2 ^ p : Nat) : Rat) / pow2Rat p = 1 := by
    change pow2Rat p / pow2Rat p = 1
    rw [Rat.div_def]
    exact Rat.mul_inv_cancel (pow2Rat p) (pow2Rat_ne_zero p)
  rw [h1, Rat.one_mul]
  have hz : (0 : Int) - (m : Int) = -(m : Int) := by omega
  rw [hz]
  exact pow2IntRat_neg_nat m

/-! ### Strict Bernoulli Separation from True Exponential Decay `(1 - 2^{-(p+1)})^(m * 2^p)` -/

theorem ratPow_add (x : Rat) (a b : Nat) :
    ratPow x (a + b) = ratPow x a * ratPow x b := by
  induction b with
  | zero => simp [ratPow]
  | succ b ih =>
    rw [Nat.add_succ, ratPow, ratPow, ih, Rat.mul_assoc]

theorem ratPow_mul (x : Rat) (a b : Nat) :
    ratPow x (a * b) = ratPow (ratPow x b) a := by
  induction a with
  | zero => simp [ratPow]
  | succ a ih =>
    rw [Nat.succ_mul, ratPow_add, ratPow, ih]

theorem ratPow_pos {x : Rat} (hx : (0 : Rat) < x) (n : Nat) :
    (0 : Rat) < ratPow x n := by
  induction n with
  | zero => exact (by decide : (0 : Rat) < 1)
  | succ n ih => exact rat_mul_pos ih hx

theorem ratPow_lt_ratPow_of_lt {a b : Rat} (ha : (0 : Rat) < a) (hab : a < b) :
    ∀ n : Nat, 1 ≤ n → ratPow a n < ratPow b n
  | 0, hn => by omega
  | 1, _ => by simpa [ratPow] using hab
  | n + 2, _ => by
    have ih := ratPow_lt_ratPow_of_lt ha hab (n + 1) (by omega)
    have hpb := ratPow_pos (rat_lt_trans ha hab) (n + 1)
    change ratPow a (n + 1) * a < ratPow b (n + 1) * b
    have h1 : ratPow a (n + 1) * a < ratPow b (n + 1) * a :=
      rat_mul_lt_mul_of_pos_right ih ha
    have h2 : ratPow b (n + 1) * a < ratPow b (n + 1) * b :=
      rat_mul_lt_mul_of_pos_left hab hpb
    exact rat_lt_trans h1 h2

theorem bernoulli_ge (y : Rat) (hy0 : (0 : Rat) ≤ y) (hy1 : y ≤ 1) (n : Nat) :
    (1 : Rat) - (n : Rat) * y ≤ ratPow (1 - y) n := by
  induction n with
  | zero =>
    simp [ratPow]
    have h : (1 : Rat) - 0 = 1 := by grind
    rw [h]
    exact Rat.le_refl
  | succ n ih =>
    have h1my : (0 : Rat) ≤ 1 - y := rat_sub_nonneg hy1
    have hstep : (1 - (n : Rat) * y) * (1 - y) ≤ ratPow (1 - y) n * (1 - y) :=
      rat_mul_le_mul_of_nonneg_right ih h1my
    have hny2 : (0 : Rat) ≤ (n : Rat) * (y * y) :=
      Rat.mul_nonneg (rat_natCast_nonneg n) (Rat.mul_nonneg hy0 hy0)
    have halg : (1 : Rat) - ((n + 1 : Nat) : Rat) * y ≤ (1 - (n : Rat) * y) * (1 - y) := by
      apply rat_le_of_sub_nonneg
      rw [rat_natCast_add]
      have hcast1 : ((1 : Nat) : Rat) = (1 : Rat) := rfl
      rw [hcast1]
      have heq : (1 - (n : Rat) * y) * (1 - y) - (1 - ((n : Rat) + 1) * y) = (n : Rat) * (y * y) := by
        grind
      rw [heq]
      exact hny2
    exact Rat.le_trans halg hstep

theorem true_decay_gt_half (p : Nat) (hp : 1 ≤ p) :
    invPow2Rat 1 < ratPow (1 - invPow2Rat (p + 1)) (2 ^ p) := by
  let a : Rat := invPow2Rat (p + 1)
  let y : Rat := invPow2Rat p - invPow2Rat (2 * p + 2)
  have h2a : (2 : Rat) * a = invPow2Rat p := by
    show (2 : Rat) * invPow2Rat (p + 1) = invPow2Rat p
    apply rat_mul_right_cancel (pow2Rat_ne_zero (p + 1))
    rw [Rat.mul_assoc, invPow2Rat_mul_pow2Rat, Rat.mul_one]
    have hpow : pow2Rat (p + 1) = pow2Rat p * (2 : Rat) := by
      rw [pow2Rat_add]
      rfl
    rw [hpow, ← Rat.mul_assoc, invPow2Rat_mul_pow2Rat, Rat.one_mul]
  have ha2 : a * a = invPow2Rat (2 * p + 2) := by
    show invPow2Rat (p + 1) * invPow2Rat (p + 1) = invPow2Rat (2 * p + 2)
    rw [← invPow2Rat_add]
    have hidx : p + 1 + (p + 1) = 2 * p + 2 := by omega
    rw [hidx]
  have hsq : ratPow (1 - a) 2 = 1 - y := by
    change (1 * (1 - a)) * (1 - a) = 1 - (invPow2Rat p - invPow2Rat (2 * p + 2))
    have : (1 - a) * (1 - a) = 1 - (2 * a - a * a) := by grind
    rw [Rat.one_mul, this, h2a, ha2]
  have hpow_split : 2 ^ p = 2 ^ (p - 1) * 2 := by
    cases p with
    | zero => omega
    | succ p' =>
      simp [Nat.pow_succ]
  have hy0 : (0 : Rat) ≤ y := by
    have hle : pow2Rat p ≤ pow2Rat (2 * p + 2) :=
      rat_natCast_le (Nat.pow_le_pow_right (by omega) (by omega))
    have hmul : invPow2Rat (2 * p + 2) ≤ invPow2Rat p := by
      have h1 := rat_mul_le_mul_of_nonneg_left hle (Rat.le_of_lt (invPow2Rat_pos (2 * p + 2)))
      rw [invPow2Rat_mul_pow2Rat] at h1
      have h2 := rat_mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (invPow2Rat_pos p))
      rw [Rat.mul_assoc, pow2Rat_mul_invPow2Rat, Rat.mul_one, Rat.one_mul] at h2
      exact h2
    exact rat_sub_nonneg hmul
  have hy1 : y ≤ 1 := by
    have hpos2 := invPow2Rat_pos (2 * p + 2)
    have hle1 : invPow2Rat p ≤ 1 := by
      have h1 : (1 : Rat) ≤ pow2Rat p := rat_natCast_le (Nat.two_pow_pos p)
      have h2 := rat_mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (invPow2Rat_pos p))
      rw [Rat.mul_one, invPow2Rat_mul_pow2Rat] at h2
      exact h2
    apply rat_le_of_sub_nonneg
    have hsub : (0 : Rat) ≤ 1 - invPow2Rat p := rat_sub_nonneg hle1
    have hge0 : (0 : Rat) ≤ (1 - invPow2Rat p) + invPow2Rat (2 * p + 2) := by
      have := (Rat.add_le_add_right (c := invPow2Rat (2 * p + 2))).mpr hsub
      have h0 : (0 : Rat) ≤ invPow2Rat (2 * p + 2) := Rat.le_of_lt hpos2
      have := Rat.le_trans h0 (by simpa [Rat.zero_add] using this)
      exact this
    have heq : (1 : Rat) - y = (1 - invPow2Rat p) + invPow2Rat (2 * p + 2) := by
      show (1 : Rat) - (invPow2Rat p - invPow2Rat (2 * p + 2)) = _
      grind
    rw [heq]
    exact hge0
  have hbern := bernoulli_ge y hy0 hy1 (2 ^ (p - 1))
  rw [hpow_split, ratPow_mul, hsq]
  have hterm1 : ((2 ^ (p - 1) : Nat) : Rat) * invPow2Rat p = invPow2Rat 1 := by
    apply rat_mul_right_cancel (pow2Rat_ne_zero p)
    rw [Rat.mul_assoc, invPow2Rat_mul_pow2Rat, Rat.mul_one]
    have hp_eq : p = 1 + (p - 1) := by omega
    have hrhs : invPow2Rat 1 * pow2Rat p = pow2Rat (p - 1) := by
      have hpp : pow2Rat p = pow2Rat 1 * pow2Rat (p - 1) := by
        rw [← pow2Rat_add, ← hp_eq]
      rw [hpp, ← Rat.mul_assoc, invPow2Rat_mul_pow2Rat, Rat.one_mul]
    rw [hrhs]
    rfl
  have hterm2_pos : (0 : Rat) < ((2 ^ (p - 1) : Nat) : Rat) * invPow2Rat (2 * p + 2) :=
    rat_mul_pos (pow2Rat_pos (p - 1)) (invPow2Rat_pos (2 * p + 2))
  have hstrict : invPow2Rat 1 < (1 : Rat) - ((2 ^ (p - 1) : Nat) : Rat) * y := by
    apply rat_lt_of_sub_pos
    have hhalf : (1 : Rat) - invPow2Rat 1 - invPow2Rat 1 = 0 := by
      unfold invPow2Rat pow2Rat
      simp
      grind
    have heq : (1 : Rat) - ((2 ^ (p - 1) : Nat) : Rat) * y - invPow2Rat 1 =
        ((2 ^ (p - 1) : Nat) : Rat) * invPow2Rat (2 * p + 2) := by
      have hdist : ((2 ^ (p - 1) : Nat) : Rat) * y =
          ((2 ^ (p - 1) : Nat) : Rat) * invPow2Rat p -
          ((2 ^ (p - 1) : Nat) : Rat) * invPow2Rat (2 * p + 2) := by
        show _ * (invPow2Rat p - invPow2Rat (2 * p + 2)) = _
        grind
      rw [hdist, hterm1]
      grind
    rw [heq]
    exact hterm2_pos
  exact rat_lt_of_lt_of_le hstrict hbern

theorem invPow2Rat_eq_ratPow_half (m : Nat) :
    invPow2Rat m = ratPow (invPow2Rat 1) m := by
  induction m with
  | zero =>
    unfold invPow2Rat pow2Rat ratPow
    simp
    grind
  | succ m ih =>
    rw [ratPow, ← ih, ← invPow2Rat_add]

/-- Headline Theorem 2 (`eager_online_softmax_one_ulp_per_step_collapse`). -/
theorem eager_online_softmax_one_ulp_per_step_collapse :
    (∀ (p : Nat) (e : Int) (s : Nat), 2 ^ p < s → s < 2 ^ (p + 1) →
      rneMulOneMinusHalfUlpStep p (e, s) = (e, s - 1)) ∧
    (∀ (p : Nat) (e : Int),
      rneMulOneMinusHalfUlpStep p (e, 2 ^ p) = (e - 1, 2 ^ (p + 1) - 1) ∧
      seqPowState p (2 ^ p) (e, 2 ^ p) = (e - 1, 2 ^ p)) ∧
    (∀ (p m : Nat), seqPow p (m * 2 ^ p) = invPow2Rat m) ∧
    (seqPow 7 512 = (1 / 16 : Rat) ∧ seqPow 10 2048 = (1 / 4 : Rat)) ∧
    (∀ (p m : Nat), 1 ≤ p → 1 ≤ m →
      seqPow p (m * 2 ^ p) < ratPow (1 - invPow2Rat (p + 1)) (m * 2 ^ p)) ∧
    (∀ (p k : Nat) (x : NormalFloat p),
      (x.scaleNegPow2 k).toRat = x.toRat * invPow2Rat k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p e s hlo hhi
    exact rneMulStep_interior p e s hlo hhi
  · intro p e
    exact ⟨rneMulStep_boundary p e, seqPowState_binade_drop p e⟩
  · intro p m
    exact seqPow_exact p m
  · constructor
    · have h7 := seqPow_exact 7 4
      have h512 : 4 * 2 ^ 7 = 512 := by decide
      rw [h512] at h7
      rw [h7]
      unfold invPow2Rat pow2Rat
      simp
    · have h10 := seqPow_exact 10 2
      have h2048 : 2 * 2 ^ 10 = 2048 := by decide
      rw [h2048] at h10
      rw [h10]
      unfold invPow2Rat pow2Rat
      simp
  · intro p m hp hm
    rw [seqPow_exact, invPow2Rat_eq_ratPow_half, ratPow_mul]
    exact ratPow_lt_ratPow_of_lt (invPow2Rat_pos 1) (true_decay_gt_half p hp) m hm
  · intro p k x
    exact scaleNegPow2_toRat x k

end FlashAttnDyadicSlack
