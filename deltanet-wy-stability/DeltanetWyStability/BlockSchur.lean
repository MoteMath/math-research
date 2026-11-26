/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltanetWyStability.RatAlg

/-!
# Theorem 5: Universal Exact 2×2 Block-Schur Lower-Triangular Matrix Inverse
-/

namespace DeltanetWyStability

/-- Block multiplication law for 2×2 block lower-triangular matrices:
    `[[A1, 0], [C1, D1]] * [[A2, 0], [C2, D2]] = [[A1*A2, 0], [C1*A2 + D1*C2, D1*D2]]`. -/
theorem blockLower_mul {n m : Nat}
    (A1 A2 : RatMat n n) (C1 C2 : RatMat m n) (D1 D2 : RatMat m m) :
    matMul (blockLower A1 C1 D1) (blockLower A2 C2 D2) =
      blockLower (matMul A1 A2) (matAdd (matMul C1 A2) (matMul D1 C2)) (matMul D1 D2) := by
  funext i j
  unfold matMul blockLower matAdd
  rw [sumFin_add]
  by_cases hi : i.val < n
  · by_cases hj : j.val < n
    · simp only [hi, hj, ↓reduceDIte]
      have h1 : sumFin (fun k : Fin n =>
            (if h : k.val < n then A1 ⟨i.val, hi⟩ ⟨k.val, h⟩ else 0) *
            (if h : k.val < n then A2 ⟨k.val, h⟩ ⟨j.val, hj⟩
             else C2 ⟨k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) (Nat.lt_of_lt_of_le k.isLt (Nat.le_add_right n m))⟩ ⟨j.val, hj⟩)) =
          sumFin (fun k : Fin n => A1 ⟨i.val, hi⟩ k * A2 k ⟨j.val, hj⟩) := by
        apply sumFin_congr; intro k; simp [k.isLt]
      have h2 : sumFin (fun k : Fin m =>
            (if h : n + k.val < n then A1 ⟨i.val, hi⟩ ⟨n + k.val, h⟩ else 0) *
            (if h : n + k.val < n then A2 ⟨n + k.val, h⟩ ⟨j.val, hj⟩
             else C2 ⟨n + k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) (Nat.add_lt_add_left k.isLt n)⟩ ⟨j.val, hj⟩)) = 0 := by
        rw [sumFin_congr (g := fun _ => 0)]
        · exact sumFin_zero m
        · intro k
          have hnot : ¬ n + k.val < n := by omega
          simp [hnot]
      rw [h1, h2]; grind
    · simp only [hi, hj, ↓reduceDIte]
      have h1 : sumFin (fun k : Fin n =>
            (if h : k.val < n then A1 ⟨i.val, hi⟩ ⟨k.val, h⟩ else 0) *
            (if h : k.val < n then (0 : Rat)
             else D2 ⟨k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) (Nat.lt_of_lt_of_le k.isLt (Nat.le_add_right n m))⟩
                     ⟨j.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hj) j.isLt⟩)) = 0 := by
        rw [sumFin_congr (g := fun _ => 0)]
        · exact sumFin_zero n
        · intro k; simp [k.isLt]
      have h2 : sumFin (fun k : Fin m =>
            (if h : n + k.val < n then A1 ⟨i.val, hi⟩ ⟨n + k.val, h⟩ else 0) *
            (if h : n + k.val < n then (0 : Rat)
             else D2 ⟨n + k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) (Nat.add_lt_add_left k.isLt n)⟩
                     ⟨j.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hj) j.isLt⟩)) = 0 := by
        rw [sumFin_congr (g := fun _ => 0)]
        · exact sumFin_zero m
        · intro k
          have hnot : ¬ n + k.val < n := by omega
          simp [hnot]
      rw [h1, h2]; grind
  · by_cases hj : j.val < n
    · simp only [hi, hj, ↓reduceDIte]
      have h1 : sumFin (fun k : Fin n =>
            (if hk : k.val < n then
              C1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩ ⟨k.val, hk⟩
             else
              D1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩
                 ⟨k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Nat.lt_of_lt_of_le k.isLt (Nat.le_add_right n m))⟩) *
            (if hk : k.val < n then A2 ⟨k.val, hk⟩ ⟨j.val, hj⟩
             else C2 ⟨k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Nat.lt_of_lt_of_le k.isLt (Nat.le_add_right n m))⟩
                     ⟨j.val, hj⟩)) =
          sumFin (fun k : Fin n =>
            C1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩ k *
            A2 k ⟨j.val, hj⟩) := by
        apply sumFin_congr; intro k; simp [k.isLt]
      have h2 : sumFin (fun k : Fin m =>
            (if hk : n + k.val < n then
              C1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩ ⟨n + k.val, hk⟩
             else
              D1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩
                 ⟨n + k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Nat.add_lt_add_left k.isLt n)⟩) *
            (if hk : n + k.val < n then A2 ⟨n + k.val, hk⟩ ⟨j.val, hj⟩
             else C2 ⟨n + k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Nat.add_lt_add_left k.isLt n)⟩
                     ⟨j.val, hj⟩)) =
          sumFin (fun k : Fin m =>
            D1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩ k *
            C2 k ⟨j.val, hj⟩) := by
        apply sumFin_congr
        intro k
        have hnot : ¬ n + k.val < n := by omega
        simp only [hnot, ↓reduceDIte]
        have hk : (⟨n + k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hnot) (Nat.add_lt_add_left k.isLt n)⟩ : Fin m) = k :=
          Fin.ext (Nat.add_sub_cancel_left n k.val)
        rw [hk]
      rw [h1, h2]
    · simp only [hi, hj, ↓reduceDIte]
      have h1 : sumFin (fun k : Fin n =>
            (if hk : k.val < n then
              C1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩ ⟨k.val, hk⟩
             else
              D1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩
                 ⟨k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Nat.lt_of_lt_of_le k.isLt (Nat.le_add_right n m))⟩) *
            (if hk : k.val < n then (0 : Rat)
             else D2 ⟨k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Nat.lt_of_lt_of_le k.isLt (Nat.le_add_right n m))⟩
                     ⟨j.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hj) j.isLt⟩)) = 0 := by
        rw [sumFin_congr (g := fun _ => 0)]
        · exact sumFin_zero n
        · intro k; simp [k.isLt]
      have h2 : sumFin (fun k : Fin m =>
            (if hk : n + k.val < n then
              C1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩ ⟨n + k.val, hk⟩
             else
              D1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩
                 ⟨n + k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Nat.add_lt_add_left k.isLt n)⟩) *
            (if hk : n + k.val < n then (0 : Rat)
             else D2 ⟨n + k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hk) (Nat.add_lt_add_left k.isLt n)⟩
                     ⟨j.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hj) j.isLt⟩)) =
          sumFin (fun k : Fin m =>
            D1 ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩ k *
            D2 k ⟨j.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hj) j.isLt⟩) := by
        apply sumFin_congr
        intro k
        have hnot : ¬ n + k.val < n := by omega
        simp only [hnot, ↓reduceDIte]
        have hk : (⟨n + k.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hnot) (Nat.add_lt_add_left k.isLt n)⟩ : Fin m) = k :=
          Fin.ext (Nat.add_sub_cancel_left n k.val)
        rw [hk]
      rw [h1, h2]; grind

theorem blockLower_id (n m : Nat) :
    blockLower (idMat n) (fun _ _ => (0 : Rat)) (idMat m) = idMat (n + m) := by
  funext i j
  unfold blockLower idMat
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · simp only [hi, hj, ↓reduceDIte]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : (⟨i.val, hi⟩ : Fin n) ≠ ⟨j.val, hj⟩ := by
        intro h
        have hv : i.val = j.val := congrArg (fun x : Fin n => x.val) h
        exact hij (Fin.ext hv)
      simp [hij, hne]
  · simp only [hi, hj, ↓reduceDIte]
    have hij : i ≠ j := fun h => by subst h; exact hj hi
    simp [hij]
  · simp only [hi, hj, ↓reduceDIte]
    have hij : i ≠ j := fun h => by subst h; exact hi hj
    simp [hij]
  · simp only [hi, hj, ↓reduceDIte]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : (⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hi) i.isLt⟩ : Fin m) ≠
          ⟨j.val - n, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hj) j.isLt⟩ := by
        intro h
        have hv : i.val - n = j.val - n := congrArg Fin.val h
        apply hij
        exact Fin.ext (by omega)
      simp [hij, hne]

theorem matMul_neg_right {m p n : Nat} (A : RatMat m p) (B : RatMat p n) :
    matMul A (matNeg B) = matNeg (matMul A B) := by
  funext i j
  unfold matMul matNeg
  rw [← sumFin_neg_fn]
  exact sumFin_congr (fun k => by grind)

theorem matMul_neg_left {m p n : Nat} (A : RatMat m p) (B : RatMat p n) :
    matMul (matNeg A) B = matNeg (matMul A B) := by
  funext i j
  unfold matMul matNeg
  rw [← sumFin_neg_fn]
  exact sumFin_congr (fun k => by grind)

theorem matAdd_neg_right {m n : Nat} (A : RatMat m n) :
    matAdd A (matNeg A) = fun _ _ => 0 := by
  funext i j
  unfold matAdd matNeg
  grind

theorem matAdd_neg_left {m n : Nat} (A : RatMat m n) :
    matAdd (matNeg A) A = fun _ _ => 0 := by
  funext i j
  unfold matAdd matNeg
  grind

/-- Headline Theorem 5: Universal Exact 2×2 Block-Schur Lower-Triangular Inverse. -/
theorem block_schur_wy_exact_inverse (n m : Nat)
    (A A_inv : RatMat n n) (C : RatMat m n) (D D_inv : RatMat m m)
    (hAL : matMul A_inv A = idMat n) (hAR : matMul A A_inv = idMat n)
    (hDL : matMul D_inv D = idMat m) (hDR : matMul D D_inv = idMat m) :
    matMul (blockLower A C D) (blockSchurInv A_inv C D_inv) = idMat (n + m) ∧
    matMul (blockSchurInv A_inv C D_inv) (blockLower A C D) = idMat (n + m) := by
  unfold blockSchurInv
  constructor
  · rw [blockLower_mul, hAR, hDR, matMul_neg_right, ← matMul_assoc D (matMul D_inv C) A_inv,
        ← matMul_assoc D D_inv C, hDR, matMul_id_left, matAdd_neg_right, blockLower_id]
  · rw [blockLower_mul, hAL, hDL, matMul_neg_left, matMul_assoc (matMul D_inv C) A_inv A,
        hAL, matMul_id_right, matAdd_neg_left, blockLower_id]

end DeltanetWyStability
