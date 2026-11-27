/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeightedCarryJetRationality

/-!
# Verified Solutions (`weighted-carry-jet-rationality`)
-/

namespace WeightedCarryJetRationalityChallenge

open WeightedCarryTransducer in
/-- Theorem 1 (Bilinear jet-lift soundness): the w-th power of the 4S x 4S jet matrix applied to jetBeta computes all four weighted carry-borrow moments at width w. -/
theorem jetMat_pow_sound {S A : Nat} (M : CorrMachine S A) (w : Nat) :
    matVec (matPow (jetMat M) w) (jetBeta M) =
      pack4 (evalMfgFrom M w) (evalMfFrom M w) (evalMgFrom M w) (evalM0From M w) :=
  WeightedCarryTransducer.jetMat_pow_sound M w

open WeightedCarryTransducer in
/-- Theorem 2 (Krylov rationality in Z[[t]]): any integer sequence satisfying a finite linear recurrence has an exact rational formal power series identity over Z[[t]]. -/
theorem fps_rational_of_recurrence (c : List Int) (Z : Nat → Int)
    (hRec : SatisfiesRec c Z 0) :
    ∀ n : Nat, fpsMul (ofPoly (denomPoly c)) Z n = ofPoly (numerPoly c Z) n :=
  WeightedCarryTransducer.fps_rational_of_recurrence c Z hRec

open WeightedCarryTransducer in
/-- Theorem 3 (Binary carry-borrow rational GF): the binary carry-borrow joint moment sequence satisfies the exact degree-5 rational generating function identity in Z[[t]]. -/
theorem binary_carry_borrow_gf :
    ∀ n : Nat,
      fpsMul (ofPoly [1, -16, 100, -304, 448, -256])
        (fun w => sumTwistedCB 2 twistOne w ⟨0, by omega⟩ ⟨0, by omega⟩) n =
      ofPoly [0, 0, 4, -4, -16] n :=
  WeightedCarryTransducer.binary_carry_borrow_gf

open WeightedCarryTransducer in
/-- Theorem 4 (Binary parity-correlation rational GF): the parity-twisted binary carry-borrow correlation satisfies the exact degree-3 rational generating function identity in Z[[t]]. -/
theorem binary_parity_corr_gf :
    ∀ n : Nat,
      fpsMul (ofPoly [1, -2, -4, 8])
        (fun w => sumTwistedCB 2 twistParity w ⟨0, by omega⟩ ⟨0, by omega⟩) n =
      ofPoly [0, 0, -4, 4, -8] n :=
  WeightedCarryTransducer.binary_parity_corr_gf

open WeightedCarryTransducer in
/-- Theorem 5 (Binary triangular-square covariance law): for every width w >= 1, binary carry and borrow counts have exact signed squared-triangular covariance. -/
theorem binary_triangular_square_covariance (w : Nat) (hw : 1 ≤ w) (c0 b0 : Fin 2) :
    (4 : Int) ^ w * sumTwistedCB 2 twistOne w c0 b0 -
      sumTwistedC 2 twistOne w c0 b0 * sumTwistedB 2 twistOne w c0 b0 =
    -(if c0 = b0 then (1 : Int) else -1) *
      (((2 : Int) ^ (w - 1) * ((2 : Int) ^ w - 1)) * ((2 : Int) ^ (w - 1) * ((2 : Int) ^ w - 1))) :=
  WeightedCarryTransducer.binary_triangular_square_covariance w hw c0 b0

open WeightedCarryTransducer in
/-- Theorem 6 (Odd-radix exact independence): in every odd base B = 2m + 1 (m >= 1) and every width w, carry and borrow counts have exact zero covariance. -/
theorem odd_radix_zero_covariance (m : Nat) (hm : 1 ≤ m) (w : Nat) (c0 b0 : Fin 2) :
    let B := 2 * m + 1
    (B : Int) ^ (2 * w) * sumTwistedCB B twistOne w c0 b0 =
      sumTwistedC B twistOne w c0 b0 * sumTwistedB B twistOne w c0 b0 :=
  WeightedCarryTransducer.odd_radix_zero_covariance m hm w c0 b0

open WeightedCarryTransducer in
/-- Theorem 7 (Even-radix perfect-square covariance): in every even base B = 2m (m >= 1) and width w >= 1, carry-borrow covariance is an exact signed perfect square. -/
theorem even_radix_perfect_square_covariance (m : Nat) (hm : 1 ≤ m) (w : Nat) (hw : 1 ≤ w) (c0 b0 : Fin 2) :
    let B := 2 * m
    (B : Int) ^ (2 * w) * sumTwistedCB B twistOne w c0 b0 -
      sumTwistedC B twistOne w c0 b0 * sumTwistedB B twistOne w c0 b0 =
    -(if c0 = b0 then (1 : Int) else -1) *
      (((m : Int) * (B : Int) ^ (w - 1) * repunit B w) * ((m : Int) * (B : Int) ^ (w - 1) * repunit B w)) :=
  WeightedCarryTransducer.even_radix_perfect_square_covariance m hm w hw c0 b0

open WeightedCarryTransducer in
/-- Theorem 8 (Radix parity-partition dichotomy): the parity-twisted partition sum vanishes identically in every even base B and grows as +-B^(2*(w/2)) in every odd base. -/
theorem radix_parity_partition_formula (B : Nat) (hB : 2 ≤ B) (w : Nat) (c0 b0 : Fin 2) :
    sumTwisted0 B twistParity w c0 b0 =
      if w = 0 then 1
      else if B % 2 = 0 then 0
      else (if w % 2 = 0 ∨ c0 = b0 then (1 : Int) else -1) * (B : Int) ^ (2 * (w / 2)) :=
  WeightedCarryTransducer.radix_parity_partition_formula B hB w c0 b0

end WeightedCarryJetRationalityChallenge
