/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SkewThueMorsePfaffian

/-!
# Verified Solutions (`skew-thue-morse-pfaffian`)
-/

namespace SkewThueMorseChallenge

open SkewThueMorsePfaffian

theorem det_skewThueMorse_even {R : Type*} [CommRing R] (m : ℕ) :
    (skewThueMorseMatrix (R := R) 0 (2 * m)).det = 1 :=
  SkewThueMorsePfaffian.det_skewThueMorse_even m

theorem det_skewThueMorse_shift1_even {R : Type*} [CommRing R] (m : ℕ) :
    (skewThueMorseMatrix (R := R) 1 (2 * m)).det = 1 :=
  SkewThueMorsePfaffian.det_skewThueMorse_shift1_even m

theorem det_skewThueMorse_shift2_even {R : Type*} [CommRing R] (m : ℕ) :
    (skewThueMorseMatrix (R := R) 2 (2 * m)).det = 1 :=
  SkewThueMorsePfaffian.det_skewThueMorse_shift2_even m

theorem det_skewThueMorse_odd {R : Type*} [CommRing R] (s m : ℕ) :
    (skewThueMorseMatrix (R := R) s (2 * m + 1)).det = 0 :=
  SkewThueMorsePfaffian.det_skewThueMorse_odd s m

end SkewThueMorseChallenge
