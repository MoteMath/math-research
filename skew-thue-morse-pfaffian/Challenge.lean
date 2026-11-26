/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SkewThueMorsePfaffian.Defs

/-!
# Trusted Challenge Statements (`skew-thue-morse-pfaffian`)

Statements of the exact determinant unimodularity (`det = 1`) for the even-sized skew-symmetric
Thue-Morse matrices `A_{2m}^{(s)}` at shifts `s = 0, 1, 2` and vanishing (`det = 0`) at all odd
sizes `2m + 1` over arbitrary commutative rings `R`.
-/

namespace SkewThueMorseChallenge

open SkewThueMorsePfaffian

/-- Theorem 1 (Unimodularity of skew-symmetric Thue-Morse matrix at shift `s = 0`):
for every `m : ℕ` and every commutative ring `R`, `det(A_{2m}^{(0)}) = 1`. -/
theorem det_skewThueMorse_even {R : Type*} [CommRing R] (m : ℕ) :
    (skewThueMorseMatrix (R := R) 0 (2 * m)).det = 1 := by
  sorry

/-- Theorem 2 (Unimodularity at shift `s = 1`):
for every `m : ℕ` and every commutative ring `R`, `det(A_{2m}^{(1)}) = 1`. -/
theorem det_skewThueMorse_shift1_even {R : Type*} [CommRing R] (m : ℕ) :
    (skewThueMorseMatrix (R := R) 1 (2 * m)).det = 1 := by
  sorry

/-- Theorem 3 (Unimodularity at shift `s = 2`, i.e., the trailing `2m × 2m` cofactor of `A_{2m+1}^{(0)}`):
for every `m : ℕ` and every commutative ring `R`, `det(A_{2m}^{(2)}) = 1`. -/
theorem det_skewThueMorse_shift2_even {R : Type*} [CommRing R] (m : ℕ) :
    (skewThueMorseMatrix (R := R) 2 (2 * m)).det = 1 := by
  sorry

/-- Theorem 4 (Odd-size vanishing):
for every shift `s : ℕ`, every `m : ℕ`, and every commutative ring `R`, `det(A_{2m + 1}^{(s)}) = 0`. -/
theorem det_skewThueMorse_odd {R : Type*} [CommRing R] (s m : ℕ) :
    (skewThueMorseMatrix (R := R) s (2 * m + 1)).det = 0 := by
  sorry

end SkewThueMorseChallenge
