/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OctonionRopeWelch

/-!
# Verified Solutions (`octonion-rope-welch-frames`)
-/

namespace OctonionRopeWelchChallenge

open OctonionRopeWelch

theorem quaternion_pow2_rigidity_obstruction :
    (∀ (r : Nat), 3 ≤ r → ∀ (a b c d : Int),
      a * a + b * b + c * c + d * d = (2 : Int) ^ r →
      2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ d) ∧
    (∀ (r : Nat), 1 ≤ r → ∀ (a b c d : Int),
      a * a + b * b + c * c + d * d = (2 : Int) ^ r →
      ∃ a0 b0 c0 d0 : Int,
        a = (2 : Int) ^ ((r - 1) / 2) * a0 ∧
        b = (2 : Int) ^ ((r - 1) / 2) * b0 ∧
        c = (2 : Int) ^ ((r - 1) / 2) * c0 ∧
        d = (2 : Int) ^ ((r - 1) / 2) * d0 ∧
        (if r % 2 = 1 then (a0, b0, c0, d0) ∈ baseHurwitz2
         else (a0, b0, c0, d0) ∈ baseHurwitz4)) ∧
    baseHurwitz2.length = 24 ∧
    baseHurwitz2.Nodup ∧
    (∀ q ∈ baseHurwitz2, q.1 * q.1 + q.2.1 * q.2.1 + q.2.2.1 * q.2.2.1 + q.2.2.2 * q.2.2.2 = 2) ∧
    baseHurwitz4.length = 24 ∧
    baseHurwitz4.Nodup ∧
    (∀ q ∈ baseHurwitz4, q.1 * q.1 + q.2.1 * q.2.1 + q.2.2.1 * q.2.2.1 + q.2.2.2 * q.2.2.2 = 4) :=
  OctonionRopeWelch.quaternion_pow2_rigidity_obstruction

theorem pythagorean_and_octonion_rope_exact_orthogonal :
    (∀ a b : Int, isOrthogonal (pythagoreanRoPE a b) ((a * a + b * b) * (a * a + b * b))) ∧
    (∀ a b : Int, a * a + b * b ≠ 0 → isRatOrthogonal (pythagoreanRoPERat a b)) ∧
    (∀ a b c d : Int, isOrthogonal (quaternionLeft a b c d) (a * a + b * b + c * c + d * d)) ∧
    (∀ x : Fin 8 → Int, isOrthogonal (octonionLeft x) (sumInt (fun i => x i * x i))) ∧
    (sumInt (fun i => llama2Octonion0 i * llama2Octonion0 i) = ((2 : Int) ^ 16) * ((2 : Int) ^ 16)) ∧
    isRatOrthogonal (octonionRoPERat llama2Octonion0 ((2 : Int) ^ 16)) :=
  OctonionRopeWelch.pythagorean_and_octonion_rope_exact_orthogonal

theorem welch_frame_energy_lower_bound (m d s : Nat) (S : IntMat m d)
    (hcol : ∀ j : Fin d, colInner S j j = (s : Int)) :
    ((d : Int) * (s : Int)) * ((d : Int) * (s : Int)) ≤
      (m : Int) * ((d : Int) * ((s : Int) * (s : Int)) + offDiagGramEnergy S) ∧
    (d : Int) * ((s : Int) * (s : Int)) * ((d : Int) - (m : Int)) ≤
      (m : Int) * offDiagGramEnergy S :=
  OctonionRopeWelch.welch_frame_energy_lower_bound m d s S hcol

theorem welch_tight_sparse_ternary_frames_exact :
    isWelchTightSparseTernaryFrame 3 1 frame_8_16_s3 ∧
    isWelchTightSparseTernaryFrame 4 2 frame_8_16_s4 ∧
    isWelchTightSparseTernaryFrame 5 2 frame_8_16_s5 ∧
    isWelchTightSparseTernaryFrame 3 1 frame_12_24_s3 ∧
    isWelchTightSparseTernaryFrame 4 1 frame_12_24_s4 :=
  OctonionRopeWelch.welch_tight_sparse_ternary_frames_exact

theorem softmax_topk_gap_l1_exact (N K : Nat) (hK : 0 < K) (hKN : K ≤ N)
    (E : Rat) (hE : 0 < E) :
    (∀ (w : Fin N → Rat), (∀ i, 0 < w i) →
      (∀ i j : Fin N, i.val < K → K ≤ j.val → w j * E ≤ w i) →
      let H := sumRat (fun i : Fin N => if i.val < K then w i else 0)
      let T := sumRat (fun i : Fin N => if i.val < K then 0 else w i)
      l1DistRat (softmaxRat w) (topKSoftmaxRat K w) = (2 * T) / (H + T) ∧
      l1DistRat (softmaxRat w) (topKSoftmaxRat K w) ≤
        (2 * ((N - K : Nat) : Rat)) / ((K : Rat) * E + ((N - K : Nat) : Rat))) ∧
    (∃ (w : Fin N → Rat), (∀ i, 0 < w i) ∧
      (∀ i j : Fin N, i.val < K → K ≤ j.val → w j * E ≤ w i) ∧
      l1DistRat (softmaxRat w) (topKSoftmaxRat K w) =
        (2 * ((N - K : Nat) : Rat)) / ((K : Rat) * E + ((N - K : Nat) : Rat))) :=
  OctonionRopeWelch.softmax_topk_gap_l1_exact N K hK hKN E hE

theorem softmax_quantized_logit_l1_exact (N : Nat) (hN : 2 ≤ N)
    (R : Rat) (hR : 1 ≤ R) :
    (∀ (w w' : Fin N → Rat), (∀ i, 0 < w i) → (∀ i, 0 < w' i) →
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) →
      l1DistRat (softmaxRat w) (softmaxRat w') ≤ (2 * (R - 1)) / (R + 1)) ∧
    (∃ (w w' : Fin N → Rat), (∀ i, 0 < w i) ∧ (∀ i, 0 < w' i) ∧
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) ∧
      l1DistRat (softmaxRat w) (softmaxRat w') = (2 * (R - 1)) / (R + 1)) :=
  OctonionRopeWelch.softmax_quantized_logit_l1_exact N hN R hR

end OctonionRopeWelchChallenge
