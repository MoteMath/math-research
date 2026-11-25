/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryDeterminants.Defs

/-!
# Trusted Challenge Statements (`carry-determinants`)

This file imports `CarryDeterminants.Defs` alone (which imports Mathlib alone) and states
all 11 headline theorems with `sorry` placeholders for `leanprover/comparator`.
-/

namespace CarryDeterminantsChallenge

open NovelCarry Matrix Polynomial

/-- Theorem 1A (Vanishing direction): if `n - 1` has any non-extremal mixed-radix digit,
then `det (carryMatrix b k n x) = 0` for every weight vector `x : ℕ → R`. -/
theorem carryMatrix_det_eq_zero_of_non_extremal {R : Type*} [CommRing R]
    (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) (k n : ℕ) (hn1 : 1 ≤ n) (x : ℕ → R)
    {r : ℕ} (hr : r < k) (hd0 : mdigit b (n - 1) r ≠ 0) (hd1 : mdigit b (n - 1) r ≠ b r - 1) :
    (carryMatrix b k n x).det = 0 := by
  sorry

/-- Theorem 1B (Unique place-value pairing): under the Cantor extremal-digit condition on `n - 1`,
there is a unique permutation `π` of `Fin n` fixing `0` with `i + π(i) = place b r` for each `i ≠ 0`. -/
theorem existsUnique_placeValue_perm (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) :
    ∀ n : ℕ, ∀ k : ℕ, (hn1 : 1 ≤ n) → n ≤ place b k →
      (∀ r < k, mdigit b (n - 1) r = 0 ∨ mdigit b (n - 1) r = b r - 1) →
      ∃! π : Equiv.Perm (Fin n),
        π ⟨0, hn1⟩ = ⟨0, hn1⟩ ∧
        ∀ i : Fin n, i.1 ≠ 0 → ∃ r ≤ k, i.1 + (π i).1 = place b r := by
  sorry

/-- Theorem 1C (Cantor non-vanishing, mixed radix): over any nontrivial commutative ring `R`,
`det (mixedCarryPolyMatrix b k n) ≠ 0` iff every mixed-radix digit of `n - 1` lies in `{0, b r - 1}`. -/
theorem mixedCarryPolyMatrix_det_ne_zero_iff {R : Type*} [CommRing R] [Nontrivial R]
    (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ place b k) :
    (mixedCarryPolyMatrix (R := R) b k n).det ≠ 0 ↔
      ∀ r < k, mdigit b (n - 1) r = 0 ∨ mdigit b (n - 1) r = b r - 1 := by
  sorry

/-- Theorem 1D (Cantor non-vanishing, uniform base `B`): over any nontrivial commutative ring `R`,
`det (baseCarryPolyMatrix B k n) ≠ 0` iff every base-`B` digit of `n - 1` lies in `{0, B - 1}`. -/
theorem baseCarryPolyMatrix_det_ne_zero_iff {R : Type*} [CommRing R] [Nontrivial R]
    (B k n : ℕ) (hB : 2 ≤ B) (hn1 : 1 ≤ n) (hnk : n ≤ B ^ k) :
    (baseCarryPolyMatrix (R := R) B k n).det ≠ 0 ↔
      ∀ r < k, mdigit (fun _ => B) (n - 1) r = 0 ∨ mdigit (fun _ => B) (n - 1) r = B - 1 := by
  sorry

/-- Theorem 1E (Binary specialization): for `B = 2`, every `1 ≤ n ≤ 2^k` has non-vanishing
polynomial carry determinant over every nontrivial commutative ring `R`. -/
theorem binaryCarryPolyMatrix_det_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ 2 ^ k) :
    (baseCarryPolyMatrix (R := R) 2 k n).det ≠ 0 := by
  sorry

/-- Theorem 2A (Multivariate mixed-radix Hankel factorization): exact closed-form determinant
of `mixedHankelMatrix b k y` over any commutative ring `R`. -/
theorem det_mixedHankelMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (y : Fin (k + 1) → R) :
    (mixedHankelMatrix b k y).det =
      (-1 : R) ^ ((place b k - 1).choose 2) *
        ∏ r : Fin k, (y (Fin.last k) - (y r.castSucc) ^ (place b k / place b r.1)) ^
          ((b r.1 - 1) * place b r.1) := by
  sorry

/-- Theorem 2B (Multivariate full mixed-radix carry factorization): exact closed-form determinant
of `carryMatrix b k (place b k) x` over any commutative ring `R`. -/
theorem det_carryMatrix_full {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (x : ℕ → R) :
    (carryMatrix b k (place b k) x).det =
      (-1 : R) ^ ((place b k - 1).choose 2) *
        ∏ r : Fin k, ((∏ j ∈ Finset.Ico r.1 k, (x j) ^ suffixProd b k j) - 1) ^
          ((b r.1 - 1) * place b r.1) := by
  sorry

/-- Corollary 2.1 (Weighted linear carry determinant). -/
theorem det_weightedLinearCarryMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (w : ℕ → R) :
    (Matrix.of fun i j : Fin (place b k - 1) =>
      ∑ r ∈ Finset.range k, (carryBit b (i.1 + 1) (j.1 + 1) r : R) * w r).det =
    (-1 : R) ^ ((place b k - 1).choose 2) *
      ∏ r : Fin k, (∑ j ∈ Finset.Ico r.1 k, (suffixProd b k j : R) * w j) ^
        ((b r.1 - 1) * place b r.1) := by
  sorry

/-- Corollary 2.2 (Kummer `p`-adic valuation binomial determinant). -/
theorem det_kummer_padicValNat_choose (p k : ℕ) [hp : Fact p.Prime] :
    (Matrix.of fun i j : Fin (p ^ k - 1) =>
      (padicValNat p ((i.1 + 1 + (j.1 + 1)).choose (i.1 + 1)) : ℤ)).det =
    (-1 : ℤ) ^ ((p ^ k - 1).choose 2) *
      ∏ r : Fin k, (((p ^ (k - r.1) - 1) / (p - 1) : ℕ) : ℤ) ^ ((p - 1) * p ^ r.1) := by
  sorry

/-- Corollary 2.3 (Binary carry-word determinant `det((i + j) ^^^ i ^^^ j)`). -/
theorem det_binary_carry_word (k : ℕ) :
    (Matrix.of fun i j : Fin (2 ^ k - 1) =>
      ((((i.1 + 1) + (j.1 + 1)) ^^^ (i.1 + 1) ^^^ (j.1 + 1)) : ℤ)).det =
    (-1 : ℤ) ^ ((2 ^ k - 1).choose 2) * (2 : ℤ) ^ (k * (2 ^ k - 1)) *
      ∏ r : Fin k, ((k - r.1 : ℤ)) ^ (2 ^ r.1) := by
  sorry

/-- Corollary 2.4 (Thue-Morse power-of-two Hankel determinant). -/
theorem det_thueMorse_pow_two (k : ℕ) (hk : 2 ≤ k) :
    (Matrix.of fun i j : Fin (2 ^ k) =>
      (-1 : ℤ) ^ mdigitSum (fun _ => 2) (k + 1) (i.1 + j.1)).det = (2 : ℤ) ^ (2 ^ k - 1) := by
  sorry

end CarryDeterminantsChallenge
