/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ZeroCarrySpanningTrees

/-!
# Verified Proofs of the Challenge Statements (`zero-carry-spanning-trees`)
-/

namespace ZeroCarrySpanningTreesChallenge

open ZeroCarrySpanningTrees

theorem det_zeroCarryWalk_charpoly (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) (x : ℚ) :
    (x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - zeroCarryWalkMatrix b k).det =
      ∏ j : Fin (place b k),
        (x - ∏ r ∈ Finset.range k,
          ((-1 : ℚ) ^ mdigit b j.1 r / ((mdigit b j.1 r + 1 : ℕ) : ℚ))) :=
  ZeroCarrySpanningTrees.det_zeroCarryWalk_charpoly b hb k x

theorem det_zeroCarryCofactor_mixed {R : Type*} [CommRing R]
    (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    (∏ r ∈ Finset.range k, ((b r * (b r + 1) / 2 : ℕ) : R)) *
      (zeroCarryCofactor (R := R) b k).det =
      ∏ j : Fin (place b k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : R)) -
          ∏ r ∈ Finset.range k, (-1 : R) ^ mdigit b (j.1 + 1) r) :=
  ZeroCarrySpanningTrees.det_zeroCarryCofactor_mixed b hb k

theorem det_zeroCarryCofactor_base {R : Type*} [CommRing R]
    (B : ℕ) (hB : 1 ≤ B) (k : ℕ) :
    (((B * (B + 1) / 2 : ℕ) : R) ^ k) *
      (zeroCarryCofactor (R := R) (fun _ => B) k).det =
      ∏ j : Fin (place (fun _ => B) k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit (fun _ => B) (j.1 + 1) r + 1 : ℕ) : R)) -
          ∏ r ∈ Finset.range k, (-1 : R) ^ mdigit (fun _ => B) (j.1 + 1) r) :=
  ZeroCarrySpanningTrees.det_zeroCarryCofactor_base B hB k

theorem det_binaryZeroCarryCofactor {R : Type*} [CommRing R] (k : ℕ) :
    (binaryZeroCarryCofactor (R := R) k).det =
      ∏ m ∈ Finset.Ico 2 (k + 1),
        ((2 : R) ^ m - (-1 : R) ^ m) ^ (k.choose m) :=
  ZeroCarrySpanningTrees.det_binaryZeroCarryCofactor k

theorem det_singleRadixZeroCarryCofactor {R : Type*} [CommRing R] (B : ℕ) (hB : 1 ≤ B) :
    ((B * (B + 1) / 2 : ℕ) : R) *
      (zeroCarryCofactor (R := R) (fun _ => B) 1).det =
      ∏ j ∈ Finset.Ico 1 B, (((j + 1 : ℕ) : R) - (-1 : R) ^ j) :=
  ZeroCarrySpanningTrees.det_singleRadixZeroCarryCofactor B hB

end ZeroCarrySpanningTreesChallenge
