/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ClmulLiftDeterminants.Defs

/-!
# Trusted Challenge Statements (`clmul-lift-determinants`)

Statements of the exact monomial determinant formulas for the odd carry-less `F_2[x]`-lift matrix
`M_n(t)` at `n ∈ {2^k - 1, 2^k, 2^k + 1}`, identical vanishing on every gap
`2^k + 2 ≤ n ≤ 2^{k+1} - 2` over arbitrary commutative rings `R`, and the exact non-vanishing
characterization over integral domains with `2 ≠ 0` and `t ≠ 0`.
-/

namespace ClmulLiftChallenge

open ClmulLiftDeterminants

/-- Theorem 1 (Exact monomial determinant at `n = 2^k`):
for every `k ≥ 1`, every commutative ring `R`, and every `t : R`,
`det(M_{2^k}(t)) = ± 2^{k · 2^{k-1}} · t^{(k-1) · 2^k + 1}`. -/
theorem det_oddClmulMatrix_pow_two {R : Type*} [CommRing R] (t : R) (k : ℕ) (hk : 1 ≤ k) :
    (oddClmulMatrix t (2 ^ k)).det =
      (if k = 2 then (1 : R) else -1) * (2 : R) ^ (k * 2 ^ (k - 1)) * t ^ ((k - 1) * 2 ^ k + 1) := by
  sorry

/-- Theorem 2 (Exact `2^k → 2^k + 1` recurrence):
for every `k : ℕ`, every commutative ring `R`, and every `t : R`,
`det(M_{2^k + 1}(t)) = (-2 * t^{k + 1}) * det(M_{2^k}(t))`. -/
theorem det_oddClmulMatrix_pow_two_add_one {R : Type*} [CommRing R] (t : R) (k : ℕ) :
    (oddClmulMatrix t (2 ^ k + 1)).det =
      (-2 * t ^ (k + 1)) * (oddClmulMatrix t (2 ^ k)).det := by
  sorry

/-- Theorem 3 (Exact monomial determinant at `n = 2^k - 1`):
for every `k ≥ 1`, every commutative ring `R`, and every `t : R`,
`det(M_{2^k - 1}(t)) = ± 2^{k · 2^{k-1} - k} · t^{(k-1) · 2^k + 1 - k}`. -/
theorem det_oddClmulMatrix_pow_two_sub_one {R : Type*} [CommRing R] (t : R) (k : ℕ) (hk : 1 ≤ k) :
    (oddClmulMatrix t (2 ^ k - 1)).det =
      (if k ≤ 3 then (1 : R) else (-1 : R) ^ (k - 1)) *
        (2 : R) ^ (k * 2 ^ (k - 1) - k) * t ^ ((k - 1) * 2 ^ k + 1 - k) := by
  sorry

/-- Theorem 4 (Identical vanishing on every gap `2^k + 2 ≤ n ≤ 2^{k+1} - 2`):
for every commutative ring `R` and every `t : R`, `det(M_n(t)) = 0`. -/
theorem det_oddClmulMatrix_eq_zero_of_gap {R : Type*} [CommRing R] (t : R) (k n : ℕ)
    (hlo : 2 ^ k + 2 ≤ n) (hhi : n ≤ 2 ^ (k + 1) - 2) :
    (oddClmulMatrix t n).det = 0 := by
  sorry

/-- Theorem 5 (Complete non-vanishing locus):
over any integral domain `R` with `(2 : R) ≠ 0` and `t ≠ 0`, `det(M_n(t)) ≠ 0` if and only if
`n ∈ {2^k - 1, 2^k, 2^k + 1}` for some `k : ℕ`. -/
theorem det_oddClmulMatrix_ne_zero_iff {R : Type*} [CommRing R] [IsDomain R] (t : R)
    (h2 : (2 : R) ≠ 0) (ht : t ≠ 0) (n : ℕ) :
    (oddClmulMatrix t n).det ≠ 0 ↔
      ∃ k : ℕ, n = 2 ^ k - 1 ∨ n = 2 ^ k ∨ n = 2 ^ k + 1 := by
  sorry

end ClmulLiftChallenge
