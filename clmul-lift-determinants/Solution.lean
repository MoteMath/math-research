/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ClmulLiftDeterminants

/-!
# Verified Solutions (`clmul-lift-determinants`)
-/

namespace ClmulLiftChallenge

open ClmulLiftDeterminants

theorem det_oddClmulMatrix_pow_two {R : Type*} [CommRing R] (t : R) (k : ℕ) (hk : 1 ≤ k) :
    (oddClmulMatrix t (2 ^ k)).det =
      (if k = 2 then (1 : R) else -1) * (2 : R) ^ (k * 2 ^ (k - 1)) * t ^ ((k - 1) * 2 ^ k + 1) :=
  ClmulLiftDeterminants.det_oddClmulMatrix_pow_two t k hk

theorem det_oddClmulMatrix_pow_two_add_one {R : Type*} [CommRing R] (t : R) (k : ℕ) :
    (oddClmulMatrix t (2 ^ k + 1)).det =
      (-2 * t ^ (k + 1)) * (oddClmulMatrix t (2 ^ k)).det :=
  ClmulLiftDeterminants.det_oddClmulMatrix_pow_two_add_one t k

theorem det_oddClmulMatrix_pow_two_sub_one {R : Type*} [CommRing R] (t : R) (k : ℕ) (hk : 1 ≤ k) :
    (oddClmulMatrix t (2 ^ k - 1)).det =
      (if k ≤ 3 then (1 : R) else (-1 : R) ^ (k - 1)) *
        (2 : R) ^ (k * 2 ^ (k - 1) - k) * t ^ ((k - 1) * 2 ^ k + 1 - k) :=
  ClmulLiftDeterminants.det_oddClmulMatrix_pow_two_sub_one t k hk

theorem det_oddClmulMatrix_eq_zero_of_gap {R : Type*} [CommRing R] (t : R) (k n : ℕ)
    (hlo : 2 ^ k + 2 ≤ n) (hhi : n ≤ 2 ^ (k + 1) - 2) :
    (oddClmulMatrix t n).det = 0 :=
  ClmulLiftDeterminants.det_oddClmulMatrix_eq_zero_of_gap t k n hlo hhi

theorem det_oddClmulMatrix_ne_zero_iff {R : Type*} [CommRing R] [IsDomain R] (t : R)
    (h2 : (2 : R) ≠ 0) (ht : t ≠ 0) (n : ℕ) :
    (oddClmulMatrix t n).det ≠ 0 ↔
      ∃ k : ℕ, n = 2 ^ k - 1 ∨ n = 2 ^ k ∨ n = 2 ^ k + 1 :=
  ClmulLiftDeterminants.det_oddClmulMatrix_ne_zero_iff t h2 ht n

end ClmulLiftChallenge
