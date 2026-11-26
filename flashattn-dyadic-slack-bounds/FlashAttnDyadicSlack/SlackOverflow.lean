/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnDyadicSlack.Defs

/-!
# Exact Lazy-Slack Overflow Boundaries (`FP8-E4M3` / `FP16`) & `FP16` `65520` Overflow Cliff

Pure-`Init` (zero Mathlib) proofs of:
3. `slack_threshold_fp16_fp8_overflow_boundary_exact`: exact integer overflow boundaries
   for lazy slack `τ` (weight amplification `2^τ`): `FP8-E4M3` (`max = 448`) safety iff
   `τ ≤ 8`, general power-of-two tile width `2^b * 2^τ ≤ 65504 ↔ b + τ ≤ 15`, concrete
   `B_c = 64` `FP16` safety iff `τ ≤ 9` (overflowing at `τ ≥ 10`), and exact certification
   of the Pareto-safe windows `τ* ∈ [4, 6]` (`FP16`) and `[6, 8]` (`BF16 + FP8`).
4. `fp16_flat_attention_65520_overflow_cliff_exact`: bit-exact IEEE-754 `FP16` RNE proof
   that `FP16_MAX = 65504`, `ulp = 32`, overflow midpoint `65520 = 65504 + 16`, so flat
   uniform attention stays finite at `L = 65504` and `65519`, overflows to `+Inf` at exact
   `L = 65520` (and for all `L ≥ 65520` including `65536` and `131072`), producing
   `Inf / Inf = NaN` or `finite / Inf = 0` silent collapse even after subtracting `m = max(s)`.
-/

namespace FlashAttnDyadicSlack

/-! ### Theorem 3: Exact Lazy-Slack `FP8-E4M3` & `FP16` Overflow Boundaries -/

theorem two_pow_le_fp8E4M3Max_iff (τ : Nat) :
    2 ^ τ ≤ fp8E4M3Max ↔ τ ≤ 8 := by
  constructor
  · intro h
    if hle : τ ≤ 8 then
      exact hle
    else
      have hge : 9 ≤ τ := by omega
      have hpow : 2 ^ 9 ≤ 2 ^ τ := Nat.pow_le_pow_right (by omega) hge
      have h512 : 2 ^ 9 = 512 := by decide
      unfold fp8E4M3Max at h
      omega
  · intro h
    have hpow : 2 ^ τ ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) h
    have h256 : 2 ^ 8 = 256 := by decide
    unfold fp8E4M3Max
    omega

theorem two_pow_le_fp16MaxNormal_iff (n : Nat) :
    2 ^ n ≤ fp16MaxNormal ↔ n ≤ 15 := by
  constructor
  · intro h
    if hle : n ≤ 15 then
      exact hle
    else
      have hge : 16 ≤ n := by omega
      have hpow : 2 ^ 16 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hge
      have h65536 : 2 ^ 16 = 65536 := by decide
      have hmax : fp16MaxNormal = 65504 := by decide
      omega
  · intro h
    have hpow : 2 ^ n ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) h
    have h32768 : 2 ^ 15 = 32768 := by decide
    have hmax : fp16MaxNormal = 65504 := by decide
    omega

theorem tile_mul_two_pow_le_fp16Max_iff (b τ : Nat) :
    2 ^ b * 2 ^ τ ≤ fp16MaxNormal ↔ b + τ ≤ 15 := by
  rw [← Nat.pow_add]
  exact two_pow_le_fp16MaxNormal_iff (b + τ)

theorem bc64_mul_two_pow_le_fp16Max_iff (τ : Nat) :
    tileWidthBc * 2 ^ τ ≤ fp16MaxNormal ↔ τ ≤ 9 := by
  have hbc : tileWidthBc = 2 ^ 6 := by decide
  rw [hbc, tile_mul_two_pow_le_fp16Max_iff]
  omega

/-- Headline Theorem 3 (`slack_threshold_fp16_fp8_overflow_boundary_exact`). -/
theorem slack_threshold_fp16_fp8_overflow_boundary_exact :
    (fp8E4M3Max = 448 ∧ fp16MaxNormal = 65504 ∧ tileWidthBc = 64) ∧
    (∀ τ : Nat, 2 ^ τ ≤ fp8E4M3Max ↔ τ ≤ 8) ∧
    (2 ^ 8 = 256 ∧ 2 ^ 8 ≤ fp8E4M3Max ∧
     2 ^ 9 = 512 ∧ fp8E4M3Max < 2 ^ 9 ∧
     2 ^ 12 = 4096 ∧ fp8E4M3Max < 2 ^ 12) ∧
    (∀ b τ : Nat, 2 ^ b * 2 ^ τ ≤ fp16MaxNormal ↔ b + τ ≤ 15) ∧
    (∀ τ : Nat, tileWidthBc * 2 ^ τ ≤ fp16MaxNormal ↔ τ ≤ 9) ∧
    (tileWidthBc * 2 ^ 9 = 32768 ∧ tileWidthBc * 2 ^ 9 ≤ fp16MaxNormal ∧
     tileWidthBc * 2 ^ 10 = 65536 ∧ fp16MaxNormal < tileWidthBc * 2 ^ 10 ∧
     tileWidthBc * 2 ^ 12 = 262144 ∧ fp16MaxNormal < tileWidthBc * 2 ^ 12) ∧
    (∀ τ : Nat, 4 ≤ τ → τ ≤ 6 →
      2 ^ τ ≤ fp8E4M3Max ∧ tileWidthBc * 2 ^ τ ≤ 4096 ∧
      15 * (tileWidthBc * 2 ^ τ) ≤ fp16MaxNormal) ∧
    (∀ τ : Nat, 6 ≤ τ → τ ≤ 8 →
      2 ^ τ ≤ fp8E4M3Max ∧ tileWidthBc * 2 ^ τ ≤ 16384 ∧
      tileWidthBc * 2 ^ τ ≤ fp16MaxNormal) := by
  refine ⟨⟨rfl, by decide, rfl⟩, two_pow_le_fp8E4M3Max_iff, by decide,
          tile_mul_two_pow_le_fp16Max_iff, bc64_mul_two_pow_le_fp16Max_iff, by decide, ?_, ?_⟩
  · intro τ hlo hhi
    have hfp8 : 2 ^ τ ≤ fp8E4M3Max := (two_pow_le_fp8E4M3Max_iff τ).mpr (by omega)
    have hpow : 2 ^ τ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hhi
    have htile : tileWidthBc * 2 ^ τ ≤ 4096 := by
      unfold tileWidthBc
      have : 2 ^ 6 = 64 := by decide
      omega
    have hmax : fp16MaxNormal = 65504 := by decide
    refine ⟨hfp8, htile, ?_⟩
    omega
  · intro τ hlo hhi
    have hfp8 : 2 ^ τ ≤ fp8E4M3Max := (two_pow_le_fp8E4M3Max_iff τ).mpr hhi
    have hpow : 2 ^ τ ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) hhi
    have htile : tileWidthBc * 2 ^ τ ≤ 16384 := by
      unfold tileWidthBc
      have : 2 ^ 8 = 256 := by decide
      omega
    have hmax : fp16MaxNormal = 65504 := by decide
    refine ⟨hfp8, htile, ?_⟩
    omega

/-! ### Theorem 4: Bit-Exact `FP16` Flat-Attention `65520` Overflow Cliff -/

theorem fp16_binade15_overflow_iff (L : Nat) (hlo : 2 ^ 15 ≤ L) (hhi : L < 2 ^ 16) :
    binadeRneNat 10 15 L = 2 ^ 16 ↔ fp16OverflowThreshold ≤ L := by
  have hu : 2 ^ (15 - 10) = 32 := by decide
  have hh : 2 ^ (15 - 10 - 1) = 16 := by decide
  have hthr : fp16OverflowThreshold = 65520 := by decide
  have h15 : 2 ^ 15 = 32768 := by decide
  have h16 : 2 ^ 16 = 65536 := by decide
  unfold binadeRneNat
  have hnotle : ¬ (15 ≤ 10) := by omega
  rw [ite_eq_right (fun h => absurd h hnotle)]
  dsimp only
  rw [hu, hh, hthr, h16]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · omega

theorem fp16RneNatToExt_isInf_iff (L : Nat) :
    fp16RneNatToExt L = .posInf ↔ fp16OverflowThreshold ≤ L := by
  have hthr : fp16OverflowThreshold = 65520 := by decide
  have h15 : 2 ^ 15 = 32768 := by decide
  have h16 : 2 ^ 16 = 65536 := by decide
  unfold fp16RneNatToExt
  split
  · rename_i hlt15
    constructor
    · intro h; cases h
    · intro h; omega
  · rename_i hge15
    split
    · rename_i hlt16
      dsimp only
      have hiff := fp16_binade15_overflow_iff L (by omega) hlt16
      split
      · rename_i heq
        exact ⟨fun _ => hiff.mp heq, fun _ => rfl⟩
      · rename_i hne
        constructor
        · intro h; cases h
        · intro h; exact absurd (hiff.mpr h) hne
    · rename_i hge16
      exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- Headline Theorem 4 (`fp16_flat_attention_65520_overflow_cliff_exact`). -/
theorem fp16_flat_attention_65520_overflow_cliff_exact :
    (fp16MaxNormal = 65504 ∧ fp16TopUlp = 32 ∧ fp16OverflowThreshold = 65520) ∧
    (∀ L : Nat, 2 ^ 15 ≤ L → L < 2 ^ 16 →
      (binadeRneNat 10 15 L = 2 ^ 16 ↔ fp16OverflowThreshold ≤ L)) ∧
    (∀ L : Nat, fp16RneNatToExt L = .posInf ↔ fp16OverflowThreshold ≤ L) ∧
    (fp16RneNatToExt 65504 = .finite 65504 ∧
     fp16RneNatToExt 65519 = .finite 65504 ∧
     fp16RneNatToExt 65520 = .posInf ∧
     fp16RneNatToExt 65536 = .posInf ∧
     fp16RneNatToExt 131072 = .posInf) ∧
    (fpDiv .posInf .posInf = .nan ∧
     (∀ x : Rat, fpDiv (.finite x) .posInf = .finite 0)) ∧
    (∀ L : Nat,
      exactAttentionL (List.replicate L ((1 : Rat), (1 : Rat))) = (L : Rat)) := by
  refine ⟨by decide, fp16_binade15_overflow_iff, fp16RneNatToExt_isInf_iff, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, by decide⟩
  · refine ⟨rfl, ?_⟩
    intro x
    rfl
  · intro L
    unfold exactAttentionL
    have hfold : ∀ (n : Nat) (acc : Rat),
        (List.replicate n ((1 : Rat), (1 : Rat))).foldl (fun a wv => a + wv.1) acc =
          acc + (n : Rat) := by
      intro n
      induction n with
      | zero =>
        intro acc
        change acc = acc + (0 : Rat)
        exact (Rat.add_zero acc).symm
      | succ n ih =>
        intro acc
        simp only [List.replicate_succ, List.foldl_cons]
        rw [ih]
        have hadd : (((n + 1 : Nat) : Rat)) = (n : Rat) + (1 : Rat) :=
          Rat.natCast_add n 1
        rw [hadd]
        grind
    rw [hfold L 0, Rat.zero_add]

end FlashAttnDyadicSlack
