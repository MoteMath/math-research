/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NegabinaryCarryDet

/-!
# Verified Proofs of the Challenge Statements (`negabinary-carry-determinants`)
-/

namespace NegabinaryCarryDetChallenge

open NegabinaryCarryDet Matrix BigOperators

theorem negAdd_popcount_conservation (i j : ℕ) :
    (popcount i : ℤ) + popcount j - popcount (negAdd 0 i j) =
      3 * ((negNegBorrows 0 i j : ℤ) - negPosCarries 0 i j) :=
  NegabinaryCarryDet.negAdd_popcount_conservation i j

theorem runPrefix_iff_bits (i k : ℕ) :
    runPrefix i k = true ↔
      (∀ r, k.testBit r = true → i.testBit r = true) ∧
      (∀ r, k.testBit r = true → k.testBit (r + 1) = false → i.testBit (r + 1) = false) :=
  NegabinaryCarryDet.runPrefix_iff_bits i k

theorem negZeroPosCarryMat_eq_LDL {R : Type*} [CommRing R] (n : ℕ) :
    negZeroPosCarryMat R n = runPrefixMat R n * thueMorseDiag R n * (runPrefixMat R n)ᵀ :=
  NegabinaryCarryDet.negZeroPosCarryMat_eq_LDL n

theorem det_negZeroPosCarryMat {R : Type*} [CommRing R] (n : ℕ) :
    (negZeroPosCarryMat R n).det = ∏ k : Fin n, (-1 : R) ^ popcount k.1 :=
  NegabinaryCarryDet.det_negZeroPosCarryMat n

theorem det_negZeroBorrowMat {R : Type*} [CommRing R] (n : ℕ) :
    (negZeroBorrowMat R n).det = ∏ k : Fin n, (-1 : R) ^ popcount k.1 :=
  NegabinaryCarryDet.det_negZeroBorrowMat n

theorem negZeroPosCarry_ne_disjointBit :
    (negPosCarries 0 1 3 = 0 ∧ (1 &&& 3) ≠ 0) ∧
    (negPosCarries 0 3 3 = 0 ∧ (3 &&& 3) ≠ 0) :=
  NegabinaryCarryDet.negZeroPosCarry_ne_disjointBit

theorem det_negParityMat_decouple {R : Type*} [CommRing R] (n : ℕ) :
    (negParityMat R 0 n).det =
      (negParityMat R 0 ((n + 1) / 2)).det * (negKMat R (n / 2)).det :=
  NegabinaryCarryDet.det_negParityMat_decouple n

theorem det_negKMat_decouple {R : Type*} [CommRing R] (m : ℕ) :
    (negKMat R m).det =
      (-1 : R) ^ m * (negJMat R ((m + 1) / 2)).det * (negKMat R (m / 2)).det :=
  NegabinaryCarryDet.det_negKMat_decouple m

theorem negParityMat_n34_anomaly :
    (negParityMat ℤ 0 33).det = (2 : ℤ) ^ 32 * ∏ k : Fin 33, (-1 : ℤ) ^ popcount k.1 ∧
    (negParityMat ℤ 0 34).det = 3 * (2 : ℤ) ^ 33 * ∏ k : Fin 34, (-1 : ℤ) ^ popcount k.1 :=
  NegabinaryCarryDet.negParityMat_n34_anomaly

end NegabinaryCarryDetChallenge
