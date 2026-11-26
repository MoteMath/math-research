/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SparseE2M1Rotations

/-!
# Verified Solutions (`sparse-e2m1-rotations`)
-/

namespace SparseE2M1Challenge

open SparseE2M1Rotations

theorem walshHadamard_doubly24_factorization (k : Nat) :
    let Q1 := kron (walshHadamard k) B1
    let Q2 := kron (idMat (2 ^ k)) B2
    matMul Q1 Q2 = walshHadamardOf (2 ^ k * 4) ∧
    isDoubly24Sparse Q1 ∧
    isDoubly24Sparse Q2 ∧
    matEntriesIn isTernary Q1 ∧
    matEntriesIn isTernary Q2 ∧
    isOrthogonal Q1 (2 * ((2 ^ k : Nat) : Int)) ∧
    isOrthogonal Q2 2 :=
  SparseE2M1Rotations.walshHadamard_doubly24_factorization k

theorem single24_coherence_lower_bound (m : Nat) (hm : 1 ≤ m)
    (c M : Int) (hM : 0 ≤ M) (Q : IntMat (m * 4) (m * 4))
    (hsp : is24SparseRows Q)
    (horth : isRowOrthogonal Q c)
    (hbound : ∀ i j, -M ≤ Q i j ∧ Q i j ≤ M) :
    2 * c ≤ ((m * 4 : Nat) : Int) * (M * M) :=
  SparseE2M1Rotations.single24_coherence_lower_bound m hm c M hM Q hsp horth hbound

theorem walsh_weighing_attains_coherence_bound (k : Nat) :
    let W := kron (walshHadamard k) B1
    let c : Int := 2 * ((2 ^ k : Nat) : Int)
    isDoubly24Sparse W ∧
    isOrthogonal W c ∧
    isRowOrthogonal W c ∧
    (∀ i j, -1 ≤ W i j ∧ W i j ≤ 1) ∧
    ((2 ^ k * 4 : Nat) : Int) * (1 * 1) = 2 * c :=
  SparseE2M1Rotations.walsh_weighing_attains_coherence_bound k

theorem skewConference_e2m1_orthogonal (n : Nat) (C : IntMat n n) (a : Int)
    (hskew : transpose C = negMat C)
    (hconf : matMul (transpose C) C = scaleMat ((n : Int) - 1) (idMat n)) :
    isOrthogonal (addMat (scaleMat a (idMat n)) C) (a * a + (n : Int) - 1) ∧
    (isDoubledE2M1 a → (∀ i, C i i = 0) → matEntriesIn isTernary C →
      matEntriesIn isDoubledE2M1 (addMat (scaleMat a (idMat n)) C)) :=
  SparseE2M1Rotations.skewConference_e2m1_orthogonal n C a hskew hconf

theorem q32_pow2_e2m1_exact :
    isOrthogonal Q32 (16 * 16) ∧
    matEntriesIn (fun x => x = -3 ∨ x = -1 ∨ x = 1 ∨ x = 3) Q32 ∧
    matEntriesIn isDoubledE2M1 Q32 :=
  SparseE2M1Rotations.q32_pow2_e2m1_exact

theorem q16_skew41_e2m1_exact :
    isOrthogonal Q16 31 ∧
    matEntriesIn (fun x => x = -1 ∨ x = 1 ∨ x = 4) Q16 ∧
    matEntriesIn isDoubledE2M1 Q16 :=
  SparseE2M1Rotations.q16_skew41_e2m1_exact

theorem g4k_doubly24_e2m1_orthogonal (k : Nat) :
    let G := kron (walshHadamard k) G4_1_2
    isDoubly24Sparse G ∧
    matEntriesIn isDoubledE2M1 G ∧
    isOrthogonal G (5 * ((2 ^ k : Nat) : Int)) :=
  SparseE2M1Rotations.g4k_doubly24_e2m1_orthogonal k

end SparseE2M1Challenge
