/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryDeterminants

/-!
# Verified Proofs of the Challenge Statements (`carry-determinants`)
-/

namespace CarryDeterminantsChallenge

open NovelCarry Matrix Polynomial

theorem carryMatrix_det_eq_zero_of_non_extremal {R : Type*} [CommRing R]
    (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) (k n : ℕ) (hn1 : 1 ≤ n) (x : ℕ → R)
    {r : ℕ} (hr : r < k) (hd0 : mdigit b (n - 1) r ≠ 0) (hd1 : mdigit b (n - 1) r ≠ b r - 1) :
    (carryMatrix b k n x).det = 0 :=
  NovelCarry.carryMatrix_det_eq_zero_of_non_extremal b hb k n hn1 x hr hd0 hd1

theorem existsUnique_placeValue_perm (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) :
    ∀ n : ℕ, ∀ k : ℕ, (hn1 : 1 ≤ n) → n ≤ place b k →
      (∀ r < k, mdigit b (n - 1) r = 0 ∨ mdigit b (n - 1) r = b r - 1) →
      ∃! π : Equiv.Perm (Fin n),
        π ⟨0, hn1⟩ = ⟨0, hn1⟩ ∧
        ∀ i : Fin n, i.1 ≠ 0 → ∃ r ≤ k, i.1 + (π i).1 = place b r :=
  NovelCarry.existsUnique_placeValue_perm b hb

theorem mixedCarryPolyMatrix_det_ne_zero_iff {R : Type*} [CommRing R] [Nontrivial R]
    (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r) (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ place b k) :
    (mixedCarryPolyMatrix (R := R) b k n).det ≠ 0 ↔
      ∀ r < k, mdigit b (n - 1) r = 0 ∨ mdigit b (n - 1) r = b r - 1 :=
  NovelCarry.mixedCarryPolyMatrix_det_ne_zero_iff b hb k n hn1 hnk

theorem baseCarryPolyMatrix_det_ne_zero_iff {R : Type*} [CommRing R] [Nontrivial R]
    (B k n : ℕ) (hB : 2 ≤ B) (hn1 : 1 ≤ n) (hnk : n ≤ B ^ k) :
    (baseCarryPolyMatrix (R := R) B k n).det ≠ 0 ↔
      ∀ r < k, mdigit (fun _ => B) (n - 1) r = 0 ∨ mdigit (fun _ => B) (n - 1) r = B - 1 :=
  NovelCarry.baseCarryPolyMatrix_det_ne_zero_iff B k n hB hn1 hnk

theorem binaryCarryPolyMatrix_det_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ 2 ^ k) :
    (baseCarryPolyMatrix (R := R) 2 k n).det ≠ 0 :=
  NovelCarry.binaryCarryPolyMatrix_det_ne_zero k n hn1 hnk

theorem det_mixedHankelMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (y : Fin (k + 1) → R) :
    (mixedHankelMatrix b k y).det =
      (-1 : R) ^ ((place b k - 1).choose 2) *
        ∏ r : Fin k, (y (Fin.last k) - (y r.castSucc) ^ (place b k / place b r.1)) ^
          ((b r.1 - 1) * place b r.1) :=
  NovelCarry.det_mixedHankelMatrix b hb k y

theorem det_carryMatrix_full {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (x : ℕ → R) :
    (carryMatrix b k (place b k) x).det =
      (-1 : R) ^ ((place b k - 1).choose 2) *
        ∏ r : Fin k, ((∏ j ∈ Finset.Ico r.1 k, (x j) ^ suffixProd b k j) - 1) ^
          ((b r.1 - 1) * place b r.1) :=
  NovelCarry.det_carryMatrix_full b hb k x

theorem det_weightedLinearCarryMatrix {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) (w : ℕ → R) :
    (Matrix.of fun i j : Fin (place b k - 1) =>
      ∑ r ∈ Finset.range k, (carryBit b (i.1 + 1) (j.1 + 1) r : R) * w r).det =
    (-1 : R) ^ ((place b k - 1).choose 2) *
      ∏ r : Fin k, (∑ j ∈ Finset.Ico r.1 k, (suffixProd b k j : R) * w j) ^
        ((b r.1 - 1) * place b r.1) :=
  NovelCarry.det_weightedLinearCarryMatrix b hb k w

theorem det_kummer_padicValNat_choose (p k : ℕ) [hp : Fact p.Prime] :
    (Matrix.of fun i j : Fin (p ^ k - 1) =>
      (padicValNat p ((i.1 + 1 + (j.1 + 1)).choose (i.1 + 1)) : ℤ)).det =
    (-1 : ℤ) ^ ((p ^ k - 1).choose 2) *
      ∏ r : Fin k, (((p ^ (k - r.1) - 1) / (p - 1) : ℕ) : ℤ) ^ ((p - 1) * p ^ r.1) :=
  NovelCarry.det_kummer_padicValNat_choose p k

theorem det_binary_carry_word (k : ℕ) :
    (Matrix.of fun i j : Fin (2 ^ k - 1) =>
      ((((i.1 + 1) + (j.1 + 1)) ^^^ (i.1 + 1) ^^^ (j.1 + 1)) : ℤ)).det =
    (-1 : ℤ) ^ ((2 ^ k - 1).choose 2) * (2 : ℤ) ^ (k * (2 ^ k - 1)) *
      ∏ r : Fin k, ((k - r.1 : ℤ)) ^ (2 ^ r.1) :=
  NovelCarry.det_binary_carry_word k

theorem det_thueMorse_pow_two (k : ℕ) (hk : 2 ≤ k) :
    (Matrix.of fun i j : Fin (2 ^ k) =>
      (-1 : ℤ) ^ mdigitSum (fun _ => 2) (k + 1) (i.1 + j.1)).det = (2 : ℤ) ^ (2 ^ k - 1) :=
  NovelCarry.det_thueMorse_pow_two k hk

end CarryDeterminantsChallenge
