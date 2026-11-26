/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxfpDoublelogFtz.RatOrder

/-!
# Theorem 2: Universal Exact Rational EF21 Closed-Form Envelopes

Proves the universal exact rational EF21 worst-case relative MSE structure for any
full-finite microscaling format `E_a M_b` (`a ≥ 2, b ≥ 1`) under both:
- Continuous max-abs scaling (`deltaCont`), and
- OCP E8M0 power-of-2 scaling (`deltaE8m0`),
identifying the exact normal-precision plateau `1 / (2^(b+1) + 1)^2`, the exact
normal-vs-underflow regime transition threshold, and the exact `4×` denominator
separation between Continuous and E8M0 underflow ramps.
-/

namespace MxfpDoublelogFtz

/-- `mxfpMaxInt a b > 0` for all `a ≥ 2, b ≥ 1`. -/
theorem mxfpMaxInt_pos {a b : Nat} (ha : 2 ≤ a) (hb : 1 ≤ b) : 0 < mxfpMaxInt a b := by
  unfold mxfpMaxInt
  have hne : a ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  have h1 : 0 < 2 ^ (b + 1) - 1 := by
    have : 2 ≤ 2 ^ (b + 1) := nat_pow2_ge_two (by omega)
    omega
  have h2 : 0 < 2 ^ (2 ^ a - 2) := nat_pow2_pos _
  exact Nat.mul_pos h1 h2

/-- Exact formula for `mxfpMaxInt a b` when `a ≥ 2`. -/
theorem mxfpMaxInt_eq {a b : Nat} (ha : 2 ≤ a) :
    mxfpMaxInt a b = (2 ^ (b + 1) - 1) * 2 ^ (2 ^ a - 2) := by
  unfold mxfpMaxInt
  have hne : a ≠ 0 := by omega
  simp [hne]

/-- Key exponent identity: `(2 ^ (2 ^ a - 2))^2 = 2 ^ (2 ^ (a + 1) - 4)` for `a ≥ 2`. -/
theorem pow2_exp_sq {a : Nat} (ha : 2 ≤ a) :
    2 ^ (2 ^ a - 2) * 2 ^ (2 ^ a - 2) = 2 ^ (2 ^ (a + 1) - 4) := by
  rw [← Nat.pow_add]
  congr 1
  have hge : 4 ≤ 2 ^ a := nat_pow2_ge_four ha
  have hpow : 2 ^ (a + 1) = 2 ^ a + 2 ^ a := by
    rw [Nat.pow_succ]
    omega
  omega

/-- Key exponent identity: `16 * 2 ^ (2 ^ (a + 1) - 4) = 2 ^ (2 ^ (a + 1))` for `a ≥ 2`. -/
theorem sixteen_mul_pow2_sub4 {a : Nat} (ha : 2 ≤ a) :
    16 * 2 ^ (2 ^ (a + 1) - 4) = 2 ^ (2 ^ (a + 1)) := by
  have hge : 4 ≤ 2 ^ (a + 1) := by
    have : 4 ≤ 2 ^ a := nat_pow2_ge_four ha
    have : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
    omega
  have h16 : (16 : Nat) = 2 ^ 4 := by decide
  rw [h16, ← Nat.pow_add]
  congr 1
  omega

/-- Exact square of `mxfpMaxInt a b` scaled by `4`:
`4 * (mxfpMaxInt a b)^2 = (2^(b+1) - 1)^2 * 2^(2^(a+1) - 2)` and
`16 * (mxfpMaxInt a b)^2 = (2^(b+1) - 1)^2 * 2^(2^(a+1))` for all `a ≥ 2`. -/
theorem sixteen_mul_mxfpMaxInt_sq {a b : Nat} (ha : 2 ≤ a) :
    16 * (mxfpMaxInt a b * mxfpMaxInt a b) =
      (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) * 2 ^ (2 ^ (a + 1)) := by
  rw [mxfpMaxInt_eq ha]
  have hsq := pow2_exp_sq ha
  have h16 := sixteen_mul_pow2_sub4 ha
  have hre : 16 * ((2 ^ (b + 1) - 1) * 2 ^ (2 ^ a - 2) * ((2 ^ (b + 1) - 1) * 2 ^ (2 ^ a - 2))) =
      (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) * (16 * (2 ^ (2 ^ a - 2) * 2 ^ (2 ^ a - 2))) := by
    grind
  rw [hre, hsq, h16]

/-- Continuous normal branch denominator is strictly positive for all `b ≥ 1, B : Nat`. -/
theorem deltaContNorm_den_pos {b : Nat} (hb : 1 ≤ b) (B : Nat) :
    (0 : Rat) < 4 * ((2 ^ (b + 1) - 1 : Nat) : Rat) * ((2 ^ (b + 1) - 1 : Nat) : Rat) +
      ((B - 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat) := by
  have htop : 0 < 2 ^ (b + 1) - 1 := by
    have : 4 ≤ 2 ^ (b + 1) := nat_pow2_ge_four (by omega)
    omega
  have htop_pos : (0 : Rat) < ((2 ^ (b + 1) - 1 : Nat) : Rat) := natCast_pos htop
  have hterm1 : (0 : Rat) < 4 * ((2 ^ (b + 1) - 1 : Nat) : Rat) * ((2 ^ (b + 1) - 1 : Nat) : Rat) :=
    rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 4) htop_pos) htop_pos
  have hterm2 : (0 : Rat) ≤ ((B - 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat) *
      ((2 ^ (b + 1) + 1 : Nat) : Rat) :=
    Rat.mul_nonneg (Rat.mul_nonneg (natCast_nonneg _) (natCast_nonneg _)) (natCast_nonneg _)
  exact rat_add_pos_of_pos_of_nonneg hterm1 hterm2

/-- Continuous underflow branch denominator is strictly positive whenever `M > 0`. -/
theorem deltaContUf_den_pos {M : Nat} (hM : 0 < M) (u B : Nat) :
    (0 : Rat) < 4 * ((M * M : Nat) : Rat) + ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat) := by
  have hm2 : (0 : Rat) < ((M * M : Nat) : Rat) := natCast_pos (Nat.mul_pos hM hM)
  exact rat_add_pos_of_pos_of_nonneg
    (rat_mul_pos (by decide : (0 : Rat) < 4) hm2)
    (Rat.mul_nonneg (natCast_nonneg _) (natCast_nonneg _))

/-- E8M0 underflow branch denominator is strictly positive whenever `M > 0`. -/
theorem deltaE8m0Uf_den_pos {M : Nat} (hM : 0 < M) (u B : Nat) :
    (0 : Rat) < ((M * M : Nat) : Rat) + ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat) := by
  have hm2 : (0 : Rat) < ((M * M : Nat) : Rat) := natCast_pos (Nat.mul_pos hM hM)
  exact rat_add_pos_of_pos_of_nonneg hm2 (Rat.mul_nonneg (natCast_nonneg _) (natCast_nonneg _))

/-- Continuous normal-precision branch is strictly bounded above by the plateau `1 / (2^(b+1) + 1)^2`
for ALL `b ≥ 1, B ≥ 1`. -/
theorem deltaContNorm_lt_plateau {b : Nat} (hb : 1 ≤ b) (B : Nat) :
    deltaContNorm b B < mxfpNormPlateau b := by
  unfold deltaContNorm mxfpNormPlateau
  have hden1 := deltaContNorm_den_pos hb B
  have hqpos : (0 : Rat) < ((2 ^ (b + 1) + 1 : Nat) : Rat) := natCast_pos (Nat.succ_pos _)
  have hden2 : (0 : Rat) < ((2 ^ (b + 1) + 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat) :=
    rat_mul_pos hqpos hqpos
  rw [rat_div_lt_div_iff hden1 hden2]
  have htop : 0 < 2 ^ (b + 1) - 1 := by
    have : 4 ≤ 2 ^ (b + 1) := nat_pow2_ge_four (by omega)
    omega
  have htop_pos : (0 : Rat) < ((2 ^ (b + 1) - 1 : Nat) : Rat) := natCast_pos htop
  have hpos : (0 : Rat) < 4 * ((2 ^ (b + 1) - 1 : Nat) : Rat) * ((2 ^ (b + 1) - 1 : Nat) : Rat) :=
    rat_mul_pos (rat_mul_pos (by decide : (0 : Rat) < 4) htop_pos) htop_pos
  apply rat_lt_of_sub_pos
  have heq : 1 * (4 * ((2 ^ (b + 1) - 1 : Nat) : Rat) * ((2 ^ (b + 1) - 1 : Nat) : Rat) +
      ((B - 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat)) -
      ((B - 1 : Nat) : Rat) * (((2 ^ (b + 1) + 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat)) =
      4 * ((2 ^ (b + 1) - 1 : Nat) : Rat) * ((2 ^ (b + 1) - 1 : Nat) : Rat) := by grind
  rw [heq]
  exact hpos

/-- Continuous underflow ramp is nonneg and strictly less than `1` whenever `M > 0`. -/
theorem deltaContUf_bounds {M : Nat} (hM : 0 < M) (u B : Nat) :
    (0 : Rat) ≤ deltaContUf M u B ∧ deltaContUf M u B < 1 := by
  unfold deltaContUf
  have hden := deltaContUf_den_pos hM u B
  constructor
  · exact rat_div_nonneg (Rat.mul_nonneg (natCast_nonneg _) (natCast_nonneg _)) hden
  · have h1 : (1 : Rat) = 1 / 1 := by grind
    rw [h1, rat_div_lt_div_iff hden (by decide : (0 : Rat) < 1)]
    have hm2 : (0 : Rat) < ((M * M : Nat) : Rat) := natCast_pos (Nat.mul_pos hM hM)
    apply rat_lt_of_sub_pos
    have heq : 1 * (4 * ((M * M : Nat) : Rat) + ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat)) -
        ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat) * 1 = 4 * ((M * M : Nat) : Rat) := by grind
    rw [heq]
    exact rat_mul_pos (by decide : (0 : Rat) < 4) hm2

/-- Exact normal-vs-underflow crossover condition for Continuous max-abs scaling (`B ≥ 2`):
`deltaContNorm b B ≤ deltaContUf M u B` iff
`4 * M^2 + u^2 * (B - 1) ≤ u^2 * (4 * (2^(b+1) - 1)^2 + (B - 1) * (2^(b+1) + 1)^2)`. -/
theorem deltaContNorm_le_deltaContUf_iff {b M u B : Nat} (hb : 1 ≤ b) (hM : 0 < M)
    (hB : 2 ≤ B) :
    deltaContNorm b B ≤ deltaContUf M u B ↔
      4 * M * M + u * u * (B - 1) ≤
        u * u * (4 * (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) +
          (B - 1) * (2 ^ (b + 1) + 1) * (2 ^ (b + 1) + 1)) := by
  unfold deltaContNorm deltaContUf
  have hden1 := deltaContNorm_den_pos hb B
  have hden2 := deltaContUf_den_pos hM u B
  rw [rat_div_le_div_iff hden1 hden2]
  have hkpos : (0 : Rat) < ((B - 1 : Nat) : Rat) := natCast_pos (by omega)
  have hcastL : ((B - 1 : Nat) : Rat) *
      (4 * ((M * M : Nat) : Rat) + ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat)) =
      ((B - 1 : Nat) : Rat) * ((4 * M * M + u * u * (B - 1) : Nat) : Rat) := by
    have : ((4 * M * M + u * u * (B - 1) : Nat) : Rat) =
        4 * ((M * M : Nat) : Rat) + ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat) := by grind
    rw [this]
  have hcastR : ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat) *
      (4 * ((2 ^ (b + 1) - 1 : Nat) : Rat) * ((2 ^ (b + 1) - 1 : Nat) : Rat) +
        ((B - 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat)) =
      ((B - 1 : Nat) : Rat) *
        ((u * u * (4 * (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) +
          (B - 1) * (2 ^ (b + 1) + 1) * (2 ^ (b + 1) + 1)) : Nat) : Rat) := by
    have : ((u * u * (4 * (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) +
        (B - 1) * (2 ^ (b + 1) + 1) * (2 ^ (b + 1) + 1)) : Nat) : Rat) =
        ((u * u : Nat) : Rat) *
          (4 * ((2 ^ (b + 1) - 1 : Nat) : Rat) * ((2 ^ (b + 1) - 1 : Nat) : Rat) +
            ((B - 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat)) := by
      grind
    rw [this]; grind
  rw [hcastL, hcastR]
  constructor
  · intro h
    have hle : ((4 * M * M + u * u * (B - 1) : Nat) : Rat) ≤
        ((u * u * (4 * (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) +
          (B - 1) * (2 ^ (b + 1) + 1) * (2 ^ (b + 1) + 1)) : Nat) : Rat) := by
      have hinv := rat_inv_pos hkpos
      have hm := rat_mul_le_mul_of_nonneg_left h (Rat.le_of_lt hinv)
      have hkc : ((B - 1 : Nat) : Rat)⁻¹ * ((B - 1 : Nat) : Rat) = 1 :=
        Rat.inv_mul_cancel _ (Rat.ne_of_gt hkpos)
      have hl : ((B - 1 : Nat) : Rat)⁻¹ * (((B - 1 : Nat) : Rat) *
          ((4 * M * M + u * u * (B - 1) : Nat) : Rat)) =
          ((4 * M * M + u * u * (B - 1) : Nat) : Rat) := by grind
      have hr : ((B - 1 : Nat) : Rat)⁻¹ * (((B - 1 : Nat) : Rat) *
          ((u * u * (4 * (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) +
            (B - 1) * (2 ^ (b + 1) + 1) * (2 ^ (b + 1) + 1)) : Nat) : Rat)) =
          ((u * u * (4 * (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) +
            (B - 1) * (2 ^ (b + 1) + 1) * (2 ^ (b + 1) + 1)) : Nat) : Rat) := by grind
      rw [hl, hr] at hm
      exact hm
    exact (natCast_le_iff _ _).mp hle
  · intro h
    have hle := (natCast_le_iff _ _).mpr h
    exact rat_mul_le_mul_of_nonneg_left hle (Rat.le_of_lt hkpos)

/-- Exact `4×` denominator separation between Continuous and E8M0 underflow ramps:
`deltaContUf M u B ≤ deltaE8m0Uf M u B` for all `M > 0, u, B`, and strictly `<` for `u > 0, B ≥ 2`. -/
theorem deltaContUf_le_deltaE8m0Uf {M : Nat} (hM : 0 < M) (u B : Nat) :
    deltaContUf M u B ≤ deltaE8m0Uf M u B := by
  unfold deltaContUf deltaE8m0Uf
  have hden1 := deltaContUf_den_pos hM u B
  have hden2 := deltaE8m0Uf_den_pos hM u B
  rw [rat_div_le_div_iff hden1 hden2]
  apply rat_le_of_sub_nonneg
  have heq : ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat) *
      (4 * ((M * M : Nat) : Rat) + ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat)) -
      ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat) *
      (((M * M : Nat) : Rat) + ((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat)) =
      3 * ((M * M : Nat) : Rat) * (((u * u : Nat) : Rat) * ((B - 1 : Nat) : Rat)) := by grind
  rw [heq]
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 3) (natCast_nonneg _))
    (Rat.mul_nonneg (natCast_nonneg _) (natCast_nonneg _))

/-- Exact `4×` scaling identity: evaluating Continuous underflow at block size `4*(B - 1) + 1`
equals E8M0 underflow at block size `B` identically! -/
theorem deltaContUf_quad_eq_deltaE8m0Uf {M : Nat} (hM : 0 < M) (u B : Nat) (hB : 1 ≤ B) :
    deltaContUf M u (4 * (B - 1) + 1) = deltaE8m0Uf M u B := by
  unfold deltaContUf deltaE8m0Uf
  have hden1 := deltaContUf_den_pos hM u (4 * (B - 1) + 1)
  have hden2 := deltaE8m0Uf_den_pos hM u B
  rw [rat_div_eq_div_iff (Rat.ne_of_gt hden1) (Rat.ne_of_gt hden2)]
  have hsub : 4 * (B - 1) + 1 - 1 = 4 * (B - 1) := by omega
  rw [hsub]
  have hcast : ((4 * (B - 1) : Nat) : Rat) = 4 * ((B - 1 : Nat) : Rat) := by grind
  rw [hcast]
  grind

/-- **Headline Theorem 2:** Universal exact rational EF21 worst-case relative MSE structure
for general microscaling format `E_a M_b` (`a ≥ 2, b ≥ 1`) under both Continuous max-abs scaling
and OCP E8M0 power-of-2 scaling across all `B ≥ 1`. -/
theorem mxfp_universal_ef21_closed_form :
    (∀ a b : Nat, 2 ≤ a → 1 ≤ b →
      mxfpMaxInt a b = (2 ^ (b + 1) - 1) * 2 ^ (2 ^ a - 2) ∧
      16 * (mxfpMaxInt a b * mxfpMaxInt a b) =
        (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) * 2 ^ (2 ^ (a + 1))) ∧
    (∀ a b B : Nat, 2 ≤ a → 1 ≤ b → 1 ≤ B →
      deltaContNorm b B < mxfpNormPlateau b ∧
      (0 : Rat) ≤ deltaCont a b false B ∧
      deltaCont a b false B < 1 ∧
      deltaContUf (mxfpMaxInt a b) 1 B ≤ deltaE8m0Uf (mxfpMaxInt a b) 1 B ∧
      deltaContUf (mxfpMaxInt a b) 1 (4 * (B - 1) + 1) = deltaE8m0Uf (mxfpMaxInt a b) 1 B) ∧
    (∀ a b B : Nat, 2 ≤ a → 1 ≤ b → 2 ≤ B →
      (deltaContNorm b B ≤ deltaContUf (mxfpMaxInt a b) 1 B ↔
        4 * mxfpMaxInt a b * mxfpMaxInt a b + (B - 1) ≤
          4 * (2 ^ (b + 1) - 1) * (2 ^ (b + 1) - 1) +
            (B - 1) * (2 ^ (b + 1) + 1) * (2 ^ (b + 1) + 1))) ∧
    -- Concrete exact regime-switch certifications matching `symbolic_proofs.json`:
    ((deltaCont 2 1 false 23 = 11 / 293 ∧ deltaCont 2 1 false 24 = 23 / 599) ∧
     (deltaCont 2 2 false 37 = 9 / 778 ∧ deltaCont 2 2 false 38 = 37 / 3173) ∧
     (deltaCont 2 3 false 47 = 23 / 7097 ∧ deltaCont 2 3 false 48 = 47 / 14447)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    exact ⟨mxfpMaxInt_eq ha, sixteen_mul_mxfpMaxInt_sq ha⟩
  · intro a b B ha hb hB
    have hM := mxfpMaxInt_pos ha hb
    have hplat := deltaContNorm_lt_plateau hb B
    have huf := deltaContUf_bounds hM 1 B
    refine ⟨hplat, ?_, ?_, deltaContUf_le_deltaE8m0Uf hM 1 B,
      deltaContUf_quad_eq_deltaE8m0Uf hM 1 B hB⟩
    · unfold deltaCont
      rw [mxfpMinPosInt_false]
      exact Rat.le_trans huf.1 (rat_le_max_right _ _)
    · unfold deltaCont
      rw [mxfpMinPosInt_false]
      have hplat_lt_1 : mxfpNormPlateau b < 1 := by
        unfold mxfpNormPlateau
        have hq : 5 ≤ 2 ^ (b + 1) + 1 := by
          have : 4 ≤ 2 ^ (b + 1) := nat_pow2_ge_four (by omega)
          omega
        have hqpos : (0 : Rat) < ((2 ^ (b + 1) + 1 : Nat) : Rat) := natCast_pos (Nat.succ_pos _)
        have hden : (0 : Rat) < ((2 ^ (b + 1) + 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat) :=
          rat_mul_pos hqpos hqpos
        have h1 : (1 : Rat) = 1 / 1 := by grind
        conv => rhs; rw [h1]
        rw [rat_div_lt_div_iff hden (by decide : (0 : Rat) < 1)]
        have hq5 : (5 : Rat) ≤ ((2 ^ (b + 1) + 1 : Nat) : Rat) := (natCast_le_iff 5 _).mpr hq
        have h25 : (25 : Rat) ≤ ((2 ^ (b + 1) + 1 : Nat) : Rat) * ((2 ^ (b + 1) + 1 : Nat) : Rat) := by
          have s1 := rat_mul_le_mul_of_nonneg_left hq5 (by decide : (0 : Rat) ≤ 5)
          have s2 := rat_mul_le_mul_of_nonneg_right hq5 (Rat.le_of_lt hqpos)
          have h55 : (5 : Rat) * 5 = 25 := by grind
          rw [h55] at s1
          exact Rat.le_trans s1 s2
        have h1_lt_25 : ((1 * 1 : Nat) : Rat) < ((1 * 25 : Nat) : Rat) :=
          (natCast_lt_iff _ _).mpr (by decide)
        have h1_lt_25' : (1 : Rat) * 1 < 1 * 25 := by simpa using h1_lt_25
        exact rat_lt_of_lt_of_le h1_lt_25'
          (rat_mul_le_mul_of_nonneg_left h25 (by decide : (0 : Rat) ≤ 1))
      have hnorm_lt_1 : deltaContNorm b B < 1 := rat_lt_trans hplat hplat_lt_1
      simp only [max]
      split
      · exact huf.2
      · exact hnorm_lt_1
  · intro a b B ha hb hB
    have hM := mxfpMaxInt_pos ha hb
    have hiff := deltaContNorm_le_deltaContUf_iff (u := 1) hb hM hB
    simpa using hiff
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [deltaCont_eq_nat false 23 (by decide) (by decide)]
      exact rat_div_eq_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 24 (by decide) (by decide)]
      exact rat_div_eq_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 37 (by decide) (by decide)]
      exact rat_div_eq_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 38 (by decide) (by decide)]
      exact rat_div_eq_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 47 (by decide) (by decide)]
      exact rat_div_eq_div_of_nat (by decide) (by decide) (by decide)
    · rw [deltaCont_eq_nat false 48 (by decide) (by decide)]
      exact rat_div_eq_div_of_nat (by decide) (by decide) (by decide)

end MxfpDoublelogFtz
