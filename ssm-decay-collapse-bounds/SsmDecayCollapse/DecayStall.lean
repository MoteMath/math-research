/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmDecayCollapse.RatZpow

/-!
# Theorem 1: Exact IEEE-754 RNE Decay-Stall & Midpoint Quantization Law

Proves that for every IEEE-754 binary floating-point format with `p ≥ 1` explicit
mantissa bits (`u = 2^(-(p + 1))`):
1. `aMax p = 1 - 2^(-(p + 1))` is a normal IEEE-754 value strictly below `1`, and is
   the largest normal IEEE-754 value strictly below `1`.
2. The exact RNE midpoint `aStall p = 1 - 2^(-(p + 2))` rounds to `1` under `ieeeRne p`,
   and every `a ∈ [aStall p, 1]` snaps to `1` while every `a ∈ [aMax p, aStall p)`
   rounds to `aMax p`.
3. Concrete exact rational instantiations for FP8-E5M2 (`p = 2`), FP8-E4M3 (`p = 3`),
   BF16 (`p = 7`), FP16 (`p = 10`), and FP32 (`p = 23`).
-/

namespace SsmDecayCollapse

theorem zpow2_neg_one : zpow2 (-1) = 1 / 2 := by
  have h := zpow2_neg_ofNat 1
  simpa using h

theorem rat_sub_mul (a b c : Rat) : (a - b) * c = a * c - b * c := by
  grind

theorem rat_natCast_sub_one {n : Nat} (hn : 1 ≤ n) :
    ((n - 1 : Nat) : Rat) = (n : Rat) - 1 := by
  have hadd : (n - 1) + 1 = n := by omega
  have h1 : (((n - 1) + 1 : Nat) : Rat) = (n : Rat) := by rw [hadd]
  rw [Rat.natCast_add] at h1
  have hcast1 : ((1 : Nat) : Rat) = 1 := rfl
  rw [hcast1] at h1
  grind

theorem aMax_eq_floatVal (p : Nat) :
    aMax p = floatVal p (-1) (2 ^ p - 1) := by
  unfold aMax floatVal
  have h1 : 1 ≤ 2 ^ p := nat_two_pow_pos p
  have hsum : 2 ^ p + (2 ^ p - 1) = 2 ^ (p + 1) - 1 := by
    rw [Nat.pow_succ]
    omega
  rw [hsum]
  have hexp : (-1 : Int) - (p : Int) = -((p + 1 : Nat) : Int) := by omega
  rw [hexp]
  rw [rat_natCast_sub_one (nat_two_pow_pos (p + 1)), rat_sub_mul, Rat.one_mul,
    ← zpow2_ofNat (p + 1), zpow2_mul_cancel]

theorem aMax_isIeeeNormal (p : Nat) : IsIeeeNormal p (aMax p) := by
  refine ⟨-1, 2 ^ p - 1, ?_, aMax_eq_floatVal p⟩
  have h1 : 1 ≤ 2 ^ p := nat_two_pow_pos p
  omega

theorem aMax_lt_one (p : Nat) : aMax p < 1 := by
  unfold aMax
  have hp : 0 < zpow2 (-((p + 1 : Nat) : Int)) := zpow2_pos _
  grind

theorem half_le_aMax (p : Nat) : zpow2 (-1) ≤ aMax p := by
  rw [aMax_eq_floatVal]
  have h1 : 1 ≤ 2 ^ p := nat_two_pow_pos p
  exact (floatVal_bounds p (-1) (2 ^ p - 1) (by omega)).1

theorem isIeeeNormal_le_aMax_of_lt_one {p : Nat} {x : Rat}
    (hx : IsIeeeNormal p x) (hlt : x < 1) : x ≤ aMax p := by
  rcases hx with ⟨k, m, hm, rfl⟩
  have hb := floatVal_bounds p k m hm
  have hk_le : k ≤ -1 := by
    by_cases h0 : 0 ≤ k
    · have h1 : (1 : Rat) ≤ zpow2 k := by
        rw [← zpow2_zero]
        exact zpow2_le_zpow2 h0
      grind
    · omega
  by_cases hk : k = -1
  · subst hk
    rw [aMax_eq_floatVal]
    unfold floatVal
    have hle : ((2 ^ p + m : Nat) : Rat) ≤ ((2 ^ p + (2 ^ p - 1) : Nat) : Rat) := by
      apply Rat.natCast_le_natCast.mpr
      omega
    exact rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt (zpow2_pos _))
  · have hk2 : k + 1 ≤ -1 := by omega
    have h1 : floatVal p k m < zpow2 (-1) := by
      have h2 := zpow2_le_zpow2 hk2
      grind
    have h3 : zpow2 (-1) ≤ aMax p := half_le_aMax p
    grind

theorem aMax_lt_aStall (p : Nat) : aMax p < aStall p := by
  unfold aMax aStall
  have hlt : zpow2 (-((p + 2 : Nat) : Int)) < zpow2 (-((p + 1 : Nat) : Int)) :=
    zpow2_lt_zpow2 (by omega)
  grind

theorem aStall_lt_one (p : Nat) : aStall p < 1 := by
  unfold aStall
  have hp : 0 < zpow2 (-((p + 2 : Nat) : Int)) := zpow2_pos _
  grind

theorem ieeeRne_aStall_eq_one (p : Nat) (_hp : 1 ≤ p) : ieeeRne p (aStall p) = 1 := by
  have hlo : zpow2 (-1) ≤ aStall p := by
    have h1 := half_le_aMax p
    have h2 := aMax_lt_aStall p
    grind
  have hhi : aStall p < zpow2 (-1 + 1) := by
    have h0 : (-1 : Int) + 1 = 0 := by omega
    rw [h0, zpow2_zero]
    exact aStall_lt_one p
  rw [ieeeRne_eq_of_binade p hlo hhi]
  have hexp1 : (p : Int) - (-1 : Int) = ((p + 1 : Nat) : Int) := by omega
  have hexp2 : (-1 : Int) - (p : Int) = -((p + 1 : Nat) : Int) := by omega
  rw [hexp1, hexp2]
  have hscale : aStall p * zpow2 ((p + 1 : Nat) : Int) =
      (((2 ^ (p + 1) - 1 : Nat) : Int) : Rat) + 1 / 2 := by
    unfold aStall
    rw [rat_sub_mul, Rat.one_mul, ← zpow2_add]
    have hsub : -((p + 2 : Nat) : Int) + ((p + 1 : Nat) : Int) = -1 := by omega
    rw [hsub, zpow2_ofNat, zpow2_neg_one]
    have hci : (((2 ^ (p + 1) - 1 : Nat) : Int) : Rat) = ((2 ^ (p + 1) - 1 : Nat) : Rat) := rfl
    rw [hci, rat_natCast_sub_one (nat_two_pow_pos (p + 1))]
    grind
  rw [hscale, rneInt_midpoint]
  have hodd : ((2 ^ (p + 1) - 1 : Nat) : Int) % 2 ≠ 0 := by
    have heven : 2 ^ (p + 1) = 2 * 2 ^ p := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hge : 2 ≤ 2 ^ (p + 1) := by
      have := nat_two_pow_pos p
      omega
    omega
  have hbeq : (((2 ^ (p + 1) - 1 : Nat) : Int) % 2 == 0) = false := by
    cases h : (((2 ^ (p + 1) - 1 : Nat) : Int) % 2 == 0)
    · rfl
    · exfalso
      exact hodd (beq_iff_eq.mp h)
  rw [hbeq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hge : 1 ≤ 2 ^ (p + 1) := nat_two_pow_pos (p + 1)
  have hsucc : (((2 ^ (p + 1) - 1 : Nat) : Int) + 1) = ((2 ^ (p + 1) : Nat) : Int) := by omega
  rw [hsucc]
  have hcast : (((2 ^ (p + 1) : Nat) : Int) : Rat) = zpow2 ((p + 1 : Nat) : Int) := by
    rw [zpow2_ofNat]
    rfl
  rw [hcast, zpow2_mul_cancel]

theorem ieeeRne_eq_one_of_ge_aStall (p : Nat) (hp : 1 ≤ p) {a : Rat}
    (hlo : aStall p ≤ a) (hhi : a ≤ 1) : ieeeRne p a = 1 := by
  by_cases ha1 : a = 1
  · subst ha1
    exact ieeeRne_one p
  · by_cases hastall : a = aStall p
    · subst hastall
      exact ieeeRne_aStall_eq_one p hp
    · have hgt : aStall p < a := by grind
      have hlt : a < 1 := by grind
      have hblo : zpow2 (-1) ≤ a := by
        have h1 := half_le_aMax p
        have h2 := aMax_lt_aStall p
        grind
      have hbhi : a < zpow2 (-1 + 1) := by
        have h0 : (-1 : Int) + 1 = 0 := by omega
        rw [h0, zpow2_zero]
        exact hlt
      rw [ieeeRne_eq_of_binade p hblo hbhi]
      have hexp1 : (p : Int) - (-1 : Int) = ((p + 1 : Nat) : Int) := by omega
      have hexp2 : (-1 : Int) - (p : Int) = -((p + 1 : Nat) : Int) := by omega
      rw [hexp1, hexp2]
      have hpos : 0 < zpow2 ((p + 1 : Nat) : Int) := zpow2_pos _
      have hscale_lo : (((2 ^ (p + 1) : Nat) : Int) : Rat) - 1 / 2 < a * zpow2 ((p + 1 : Nat) : Int) := by
        have hmul := rat_mul_lt_mul_of_pos_right hgt hpos
        have hst : aStall p * zpow2 ((p + 1 : Nat) : Int) = (((2 ^ (p + 1) : Nat) : Int) : Rat) - 1 / 2 := by
          unfold aStall
          rw [rat_sub_mul, Rat.one_mul, ← zpow2_add]
          have hsub : -((p + 2 : Nat) : Int) + ((p + 1 : Nat) : Int) = -1 := by omega
          rw [hsub, zpow2_ofNat, zpow2_neg_one]
          rfl
        rw [hst] at hmul
        exact hmul
      have hscale_hi : a * zpow2 ((p + 1 : Nat) : Int) < (((2 ^ (p + 1) : Nat) : Int) : Rat) + 1 / 2 := by
        have hmul := rat_mul_lt_mul_of_pos_right hlt hpos
        rw [Rat.one_mul] at hmul
        rw [zpow2_ofNat] at hmul ⊢
        have hci : (((2 ^ (p + 1) : Nat) : Int) : Rat) = ((2 ^ (p + 1) : Nat) : Rat) := rfl
        rw [hci]
        grind
      rw [rneInt_eq_of_bounds hscale_lo hscale_hi]
      have hcast : (((2 ^ (p + 1) : Nat) : Int) : Rat) = zpow2 ((p + 1 : Nat) : Int) := by
        rw [zpow2_ofNat]; rfl
      rw [hcast, zpow2_mul_cancel]

theorem ieeeRne_eq_aMax_of_lt_aStall (p : Nat) (_hp : 1 ≤ p) {a : Rat}
    (hlo : aMax p ≤ a) (hhi : a < aStall p) : ieeeRne p a = aMax p := by
  have hblo : zpow2 (-1) ≤ a := by
    have h1 := half_le_aMax p
    grind
  have hbhi : a < zpow2 (-1 + 1) := by
    have h0 : (-1 : Int) + 1 = 0 := by omega
    rw [h0, zpow2_zero]
    have h2 := aStall_lt_one p
    grind
  rw [ieeeRne_eq_of_binade p hblo hbhi]
  have hexp1 : (p : Int) - (-1 : Int) = ((p + 1 : Nat) : Int) := by omega
  have hexp2 : (-1 : Int) - (p : Int) = -((p + 1 : Nat) : Int) := by omega
  rw [hexp1, hexp2]
  have hpos : 0 < zpow2 ((p + 1 : Nat) : Int) := zpow2_pos _
  have hamax_scale : aMax p * zpow2 ((p + 1 : Nat) : Int) = (((2 ^ (p + 1) - 1 : Nat) : Int) : Rat) := by
    unfold aMax
    rw [rat_sub_mul, Rat.one_mul, ← zpow2_add]
    have h0 : -((p + 1 : Nat) : Int) + ((p + 1 : Nat) : Int) = 0 := by omega
    rw [h0, zpow2_zero, zpow2_ofNat]
    have hci : (((2 ^ (p + 1) - 1 : Nat) : Int) : Rat) = ((2 ^ (p + 1) - 1 : Nat) : Rat) := rfl
    rw [hci, rat_natCast_sub_one (nat_two_pow_pos (p + 1))]
  have hscale_lo : (((2 ^ (p + 1) - 1 : Nat) : Int) : Rat) - 1 / 2 < a * zpow2 ((p + 1 : Nat) : Int) := by
    have hmul := rat_mul_le_mul_of_nonneg_right hlo (Rat.le_of_lt hpos)
    rw [hamax_scale] at hmul
    grind
  have hscale_hi : a * zpow2 ((p + 1 : Nat) : Int) < (((2 ^ (p + 1) - 1 : Nat) : Int) : Rat) + 1 / 2 := by
    have hmul := rat_mul_lt_mul_of_pos_right hhi hpos
    have hst : aStall p * zpow2 ((p + 1 : Nat) : Int) = (((2 ^ (p + 1) - 1 : Nat) : Int) : Rat) + 1 / 2 := by
      unfold aStall
      rw [rat_sub_mul, Rat.one_mul, ← zpow2_add]
      have hsub : -((p + 2 : Nat) : Int) + ((p + 1 : Nat) : Int) = -1 := by omega
      rw [hsub, zpow2_ofNat, zpow2_neg_one]
      have hci : (((2 ^ (p + 1) - 1 : Nat) : Int) : Rat) = ((2 ^ (p + 1) - 1 : Nat) : Rat) := rfl
      rw [hci, rat_natCast_sub_one (nat_two_pow_pos (p + 1))]
      grind
    rw [hst] at hmul
    exact hmul
  rw [rneInt_eq_of_bounds hscale_lo hscale_hi]
  rw [← hamax_scale, Rat.mul_assoc, zpow2_mul_cancel, Rat.mul_one]

theorem aMax_eval (p : Nat) :
    aMax p = (((2 ^ (p + 1) - 1 : Nat) : Rat)) / ((2 ^ (p + 1) : Nat) : Rat) := by
  unfold aMax
  rw [zpow2_neg_ofNat]
  have hne : ((2 ^ (p + 1) : Nat) : Rat) ≠ 0 := rat_two_pow_ne_zero (p + 1)
  rw [rat_natCast_sub_one (nat_two_pow_pos (p + 1))]
  rw [Rat.div_def, Rat.div_def, rat_sub_mul, Rat.mul_inv_cancel _ hne, Rat.one_mul]

theorem aStall_eval (p : Nat) :
    aStall p = (((2 ^ (p + 2) - 1 : Nat) : Rat)) / ((2 ^ (p + 2) : Nat) : Rat) := by
  unfold aStall
  rw [zpow2_neg_ofNat]
  have hne : ((2 ^ (p + 2) : Nat) : Rat) ≠ 0 := rat_two_pow_ne_zero (p + 2)
  rw [rat_natCast_sub_one (nat_two_pow_pos (p + 2))]
  rw [Rat.div_def, Rat.div_def, rat_sub_mul, Rat.mul_inv_cancel _ hne, Rat.one_mul]

/-- Headline Theorem 1 (`ieee_decay_stall_midpoint_exact`). -/
theorem ieee_decay_stall_midpoint_exact :
    (∀ p : Nat, 1 ≤ p →
      IsIeeeNormal p (aMax p) ∧
      aMax p < 1 ∧
      (∀ x : Rat, IsIeeeNormal p x → x < 1 → x ≤ aMax p) ∧
      ieeeRne p (aStall p) = 1 ∧
      (∀ a : Rat, aStall p ≤ a → a ≤ 1 → ieeeRne p a = 1) ∧
      (∀ a : Rat, aMax p ≤ a → a < aStall p → ieeeRne p a = aMax p)) ∧
    (aMax 2 = 7 / 8 ∧ aStall 2 = 15 / 16) ∧
    (aMax 3 = 15 / 16 ∧ aStall 3 = 31 / 32) ∧
    (aMax 7 = 255 / 256 ∧ aStall 7 = 511 / 512) ∧
    (aMax 10 = 2047 / 2048 ∧ aStall 10 = 4095 / 4096) ∧
    (aMax 23 = 16777215 / 16777216 ∧ aStall 23 = 33554431 / 33554432) := by
  refine ⟨fun p hp => ⟨aMax_isIeeeNormal p, aMax_lt_one p, fun x hx hlt => isIeeeNormal_le_aMax_of_lt_one hx hlt,
    ieeeRne_aStall_eq_one p hp, fun a hlo hhi => ieeeRne_eq_one_of_ge_aStall p hp hlo hhi,
    fun a hlo hhi => ieeeRne_eq_aMax_of_lt_aStall p hp hlo hhi⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [aMax_eval]; rfl, by rw [aStall_eval]; rfl⟩
  · exact ⟨by rw [aMax_eval]; rfl, by rw [aStall_eval]; rfl⟩
  · exact ⟨by rw [aMax_eval]; rfl, by rw [aStall_eval]; rfl⟩
  · exact ⟨by rw [aMax_eval]; rfl, by rw [aStall_eval]; rfl⟩
  · exact ⟨by rw [aMax_eval]; rfl, by rw [aStall_eval]; rfl⟩

end SsmDecayCollapse
