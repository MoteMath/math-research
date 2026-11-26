/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnDyadicSlack

/-!
# Verified Solutions (`flashattn-dyadic-slack-bounds`)
-/

namespace FlashAttnDyadicSlackChallenge

open FlashAttnDyadicSlack

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
      (0 : Rat) < invPow2Rat (p + 1)) :=
  FlashAttnDyadicSlack.dyadic_power_of_two_rescale_zero_mantissa_error

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
      (x.scaleNegPow2 k).toRat = x.toRat * invPow2Rat k) :=
  FlashAttnDyadicSlack.eager_online_softmax_one_ulp_per_step_collapse

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
      tileWidthBc * 2 ^ τ ≤ fp16MaxNormal) :=
  FlashAttnDyadicSlack.slack_threshold_fp16_fp8_overflow_boundary_exact

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
      exactAttentionL (List.replicate L ((1 : Rat), (1 : Rat))) = (L : Rat)) :=
  FlashAttnDyadicSlack.fp16_flat_attention_65520_overflow_cliff_exact

theorem dyadic_exponent_normalization_cancels_identically :
    (∀ (x : NormalFloat 10), (-13 : Int) ≤ x.exp →
      (-14 : Int) ≤ (x.scaleNegPow2 1).exp ∧
      (x.scaleNegPow2 1).neg = x.neg ∧
      (x.scaleNegPow2 1).mant = x.mant ∧
      (x.scaleNegPow2 1).toRat = x.toRat * invPow2Rat 1) ∧
    (∀ (O l : Rat) (k : Nat), l ≠ 0 →
      (O * invPow2Rat k) / (l * invPow2Rat k) = O / l) ∧
    (∀ (p k : Nat) (xO xl : NormalFloat p), xl.toRat ≠ 0 →
      (xO.scaleNegPow2 k).toRat / (xl.scaleNegPow2 k).toRat = xO.toRat / xl.toRat) ∧
    (∀ (xs : List (Rat × Rat)),
      (∀ wv ∈ xs, (0 : Rat) ≤ wv.1 ∧ wv.1 ≤ fp16NormThreshold) →
      let (O, l, k) := dyadicNormRun xs
      (0 : Rat) ≤ l ∧
      l < fp16NormThreshold ∧
      l < (fp16MaxNormal : Rat) ∧
      O = exactAttentionO xs * invPow2Rat k ∧
      l = exactAttentionL xs * invPow2Rat k ∧
      (exactAttentionL xs ≠ 0 → O / l = exactAttentionO xs / exactAttentionL xs)) :=
  FlashAttnDyadicSlack.dyadic_exponent_normalization_cancels_identically

theorem flash_tile_int32_kulisch_associativity_and_exactness :
    (∀ (pInt vInt : Int),
      ((fp8ProdToQ20 pInt vInt : Int) : Rat) / (kulischScale : Rat) =
        ((pInt : Rat) / pow2Rat 9) * ((vInt : Rat) / pow2Rat 9) ∧
      ((ue3m1ProdToQ20 pInt vInt : Int) : Rat) / (kulischScale : Rat) =
        ((pInt : Rat) / pow2Rat 7) * ((vInt : Rat) / pow2Rat 9)) ∧
    (∀ (xs : List Int) (M : Int),
      xs.length ≤ tileWidthBc → 0 ≤ M → (tileWidthBc : Int) * M ≤ int32Max →
      (∀ x ∈ xs, -M ≤ x ∧ x ≤ M) →
      inInt32Range (kulischSum xs)) ∧
    (∀ (xs : List Int),
      xs.length ≤ tileWidthBc →
      (∀ x ∈ xs, -(4 * (kulischScale : Int)) ≤ x ∧ x ≤ 4 * (kulischScale : Int)) →
      inInt32Range (kulischSum xs) ∧
      -(2 ^ 28 : Int) ≤ kulischSum xs ∧ kulischSum xs ≤ (2 ^ 28 : Int)) ∧
    (∀ (xs : List Int),
      (kulischSum xs : Rat) / (kulischScale : Rat) =
        ratSum (xs.map (fun (t : Int) => (t : Rat) / (kulischScale : Rat))) ∧
      kulischFoldl xs = kulischSum xs) ∧
    (∀ (xs ys : List Int),
      kulischSum (xs ++ ys) = kulischSum xs + kulischSum ys ∧
      kulischSum xs.reverse = kulischSum xs ∧
      (xs.Perm ys → kulischSum xs = kulischSum ys)) :=
  FlashAttnDyadicSlack.flash_tile_int32_kulisch_associativity_and_exactness

end FlashAttnDyadicSlackChallenge
