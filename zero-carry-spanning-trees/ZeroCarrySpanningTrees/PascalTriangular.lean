/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# 1D Pascal-Hockey-Stick Triangularization of the Zero-Carry Transition Matrix

For every base `b ≥ 1`, let:
- `(B_b)_{i,i} = b - i`,
- `(T_b)_{i,j} = 1` if `i + j < b` else `0`,
- `W_b = B_b⁻¹ T_b` over `ℚ`,
- `(P_b)_{i,j} = C(b - 1 - i, j)` (the reversed Pascal matrix),
- `(U_b)_{r,c} = (-1)^r / (r + 1) * C(b - 1 - r, c - r)` (upper triangular).

This module proves:
1. `walkMat1_mul_pascalRev`: `W_b * P_b = P_b * U_b`,
2. `pascalRev_det_ne_zero`: `det P_b ≠ 0`,
3. `upperMat1_upper`: `U_b` is upper triangular with diagonal `(-1)^r / (r + 1)`.
-/

namespace ZeroCarrySpanningTrees

open scoped BigOperators
open Matrix Finset

/-- Hockey-stick sum: `∑_{u < m} C(u, c) = C(m, c + 1)`. -/
theorem sum_range_choose_eq (c : ℕ) : ∀ m : ℕ, ∑ u ∈ range m, u.choose c = m.choose (c + 1)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_range_choose_eq c m, Nat.choose_succ_succ, add_comm]

/-- Alternating binomial reduction:
`∑_{m=0}^{n} (-1)^m C(d, m) C(b - m, n - m) = C(b - d, n)` for all `d ≤ b` and `n : ℕ`. -/
theorem sum_alternating_choose_sub (d : ℕ) :
    ∀ (b n : ℕ), d ≤ b →
      ∑ m ∈ range (n + 1), ((-1 : ℚ) ^ m) * ((d.choose m : ℕ) : ℚ) * (((b - m).choose (n - m) : ℕ) : ℚ) =
        (((b - d).choose n : ℕ) : ℚ) := by
  induction d with
  | zero =>
    intro b n _
    rw [Finset.sum_eq_single 0]
    · simp
    · intro m _ hm
      have h0 : Nat.choose 0 m = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hm)
      simp [h0]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
  | succ d ih =>
    intro b n hdb
    cases n with
    | zero =>
      simp
    | succ n =>
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
      have hsplit :
          ∑ m ∈ range (n + 1),
              (-1 : ℚ) ^ (m + 1) * (((d + 1).choose (m + 1) : ℕ) : ℚ) *
                (((b - (m + 1)).choose (n + 1 - (m + 1)) : ℕ) : ℚ) =
          (∑ m ∈ range (n + 1),
              (-1 : ℚ) ^ (m + 1) * ((d.choose (m + 1) : ℕ) : ℚ) *
                (((b - (m + 1)).choose (n - m) : ℕ) : ℚ)) +
          (∑ m ∈ range (n + 1),
              (-1 : ℚ) ^ (m + 1) * ((d.choose m : ℕ) : ℚ) *
                (((b - (m + 1)).choose (n - m) : ℕ) : ℚ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Nat.choose_succ_succ d m, Nat.cast_add, Nat.add_sub_add_right]
        ring
      rw [hsplit]
      have hfirst :
          (∑ m ∈ range (n + 1),
              (-1 : ℚ) ^ (m + 1) * ((d.choose (m + 1) : ℕ) : ℚ) *
                (((b - (m + 1)).choose (n - m) : ℕ) : ℚ)) +
            ((b.choose (n + 1) : ℕ) : ℚ) =
          (((b - d).choose (n + 1) : ℕ) : ℚ) := by
        have hih := ih b (n + 1) (Nat.le_of_succ_le hdb)
        rw [Finset.sum_range_succ'] at hih
        simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at hih
        convert hih using 2
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Nat.add_sub_add_right]
      have hsecond :
          (∑ m ∈ range (n + 1),
              (-1 : ℚ) ^ (m + 1) * ((d.choose m : ℕ) : ℚ) *
                (((b - (m + 1)).choose (n - m) : ℕ) : ℚ)) =
          -((((b - 1 - d).choose n : ℕ) : ℚ)) := by
        have hih := ih (b - 1) n (by omega)
        rw [← hih, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        have hsub : b - (m + 1) = b - 1 - m := by omega
        rw [hsub, pow_succ]
        ring
      have hbd : b - d = (b - (d + 1)) + 1 := by omega
      have hbd1 : b - 1 - d = b - (d + 1) := by omega
      have hpascal : (((b - d).choose (n + 1) : ℕ) : ℚ) =
          (((b - (d + 1)).choose n : ℕ) : ℚ) + (((b - (d + 1)).choose (n + 1) : ℕ) : ℚ) := by
        rw [hbd, Nat.choose_succ_succ, Nat.cast_add]
      linarith [hfirst, hsecond, hpascal, congrArg (fun t => ((t.choose n : ℕ) : ℚ)) hbd1]

/-- 1D hockey-stick sum for reversed binomial columns:
`∑_{j = 0}^{b - 1 - i} C(b - 1 - j, c) = C(b, c + 1) - C(i, c + 1)` over `ℚ` for `i < b`. -/
theorem sum_rev_choose_hockey (b i c : ℕ) (hi : i < b) :
    (∑ j ∈ range (b - i), (((b - 1 - j).choose c : ℕ) : ℚ)) =
      ((b.choose (c + 1) : ℕ) : ℚ) - ((i.choose (c + 1) : ℕ) : ℚ) := by
  have hnat :
      (∑ j ∈ range (b - i), (b - 1 - j).choose c) + i.choose (c + 1) = b.choose (c + 1) := by
    have hfull := sum_range_choose_eq c b
    have hlow := sum_range_choose_eq c i
    have hsplit : ∑ u ∈ range b, u.choose c =
        (∑ u ∈ range i, u.choose c) + ∑ j ∈ range (b - i), (i + j).choose c := by
      have : b = i + (b - i) := by omega
      conv_lhs => rw [this, Finset.sum_range_add]
    have hrev : ∑ j ∈ range (b - i), (b - 1 - j).choose c =
        ∑ j ∈ range (b - i), (i + j).choose c := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hlt : j < b - i := Finset.mem_range.mp hj
      congr 1
      omega
    omega
  have hq : ((∑ j ∈ range (b - i), (b - 1 - j).choose c : ℕ) : ℚ) +
      ((i.choose (c + 1) : ℕ) : ℚ) = ((b.choose (c + 1) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  push_cast at hq
  linarith

/-- Reversed Pascal matrix `(P_b)_{i, j} = C(b - 1 - i, j)` over `ℚ`. -/
def pascalRev (b : ℕ) : Matrix (Fin b) (Fin b) ℚ :=
  Matrix.of fun i j => (((b - 1 - i.1).choose j.1 : ℕ) : ℚ)

/-- 1D zero-carry indicator matrix `(T_b)_{i, j} = 1` if `i + j < b` else `0` over `ℚ`. -/
def zeroCarryMat1 (b : ℕ) : Matrix (Fin b) (Fin b) ℚ :=
  Matrix.of fun i j => if i.1 + j.1 < b then 1 else 0

/-- 1D diagonal degree-plus-self matrix `B_b = diag(b - i)` over `ℚ`. -/
def degDiag1 (b : ℕ) : Matrix (Fin b) (Fin b) ℚ :=
  Matrix.diagonal fun i => ((b - i.1 : ℕ) : ℚ)

/-- 1D normalized transition matrix `W_b = B_b⁻¹ T_b` over `ℚ`. -/
def walkMat1 (b : ℕ) : Matrix (Fin b) (Fin b) ℚ :=
  Matrix.of fun i j => if i.1 + j.1 < b then (((b - i.1 : ℕ) : ℚ))⁻¹ else 0

/-- 1D upper-triangular target matrix `(U_b)_{r, c} = (-1)^r / (r + 1) * C(b - 1 - r, c - r)`. -/
def upperMat1 (b : ℕ) : Matrix (Fin b) (Fin b) ℚ :=
  Matrix.of fun r c =>
    if r.1 ≤ c.1 then
      ((-1 : ℚ) ^ r.1 / ((r.1 + 1 : ℕ) : ℚ)) * (((b - 1 - r.1).choose (c.1 - r.1) : ℕ) : ℚ)
    else 0

theorem pascalRev_col0 (b : ℕ) (hb : 0 < b) (i : Fin b) :
    pascalRev b i ⟨0, hb⟩ = 1 := by
  simp [pascalRev]

theorem upperMat1_upper (b : ℕ) :
    ∀ r c : Fin b, c < r → upperMat1 b r c = 0 := by
  intro r c hcr
  simp only [upperMat1, Matrix.of_apply]
  simp [Nat.not_le.mpr hcr]

theorem upperMat1_diag (b : ℕ) (r : Fin b) :
    upperMat1 b r r = (-1 : ℚ) ^ r.1 / ((r.1 + 1 : ℕ) : ℚ) := by
  simp [upperMat1]

/-- Key 1D matrix identity: `T_b * P_b = B_b * P_b * U_b` over `ℚ`. -/
theorem zeroCarryMat1_mul_pascalRev (b : ℕ) :
    zeroCarryMat1 b * pascalRev b = degDiag1 b * (pascalRev b * upperMat1 b) := by
  ext i c
  rw [degDiag1, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, zeroCarryMat1, pascalRev, upperMat1, Matrix.of_apply]
  have hlhs :
      ∑ j : Fin b, (if i.1 + j.1 < b then (1 : ℚ) else 0) * (((b - 1 - j.1).choose c.1 : ℕ) : ℚ) =
      ((b.choose (c.1 + 1) : ℕ) : ℚ) - ((i.1.choose (c.1 + 1) : ℕ) : ℚ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (if i.1 + j < b then (1 : ℚ) else 0) * (((b - 1 - j).choose c.1 : ℕ) : ℚ))]
    have hfilter :
        ∑ j ∈ range b, (if i.1 + j < b then (1 : ℚ) else 0) * (((b - 1 - j).choose c.1 : ℕ) : ℚ) =
        ∑ j ∈ range (b - i.1), (((b - 1 - j).choose c.1 : ℕ) : ℚ) := by
      have hsub : b = (b - i.1) + i.1 := by omega
      have hsplit_sum := Finset.sum_range_add
        (fun j => (if i.1 + j < b then (1 : ℚ) else 0) * (((b - 1 - j).choose c.1 : ℕ) : ℚ))
        (b - i.1) i.1
      rw [← hsub] at hsplit_sum
      rw [hsplit_sum]
      have hleft :
          ∑ j ∈ range (b - i.1), (if i.1 + j < b then (1 : ℚ) else 0) * (((b - 1 - j).choose c.1 : ℕ) : ℚ) =
          ∑ j ∈ range (b - i.1), (((b - 1 - j).choose c.1 : ℕ) : ℚ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hlt : j < b - i.1 := Finset.mem_range.mp hj
        have hlt' : i.1 + j < b := by omega
        simp [hlt']
      have hright :
          ∑ j ∈ range i.1, (if i.1 + (b - i.1 + j) < b then (1 : ℚ) else 0) *
            (((b - 1 - (b - i.1 + j)).choose c.1 : ℕ) : ℚ) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        have hge : ¬ (i.1 + (b - i.1 + j) < b) := by omega
        simp [hge]
      rw [hleft, hright, add_zero]
    rw [hfilter]
    exact sum_rev_choose_hockey b i.1 c.1 i.2
  rw [hlhs, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun r => ((b - i.1 : ℕ) : ℚ) *
      ((((b - 1 - i.1).choose r : ℕ) : ℚ) *
        (if r ≤ c.1 then ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (((b - 1 - r).choose (c.1 - r) : ℕ) : ℚ) else 0)))]
  have htrunc :
      ∑ r ∈ range b, ((b - i.1 : ℕ) : ℚ) *
        ((((b - 1 - i.1).choose r : ℕ) : ℚ) *
          (if r ≤ c.1 then ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (((b - 1 - r).choose (c.1 - r) : ℕ) : ℚ) else 0)) =
      ∑ r ∈ range (c.1 + 1),
        ((-1 : ℚ) ^ r) * ((((b - i.1).choose (r + 1) : ℕ) : ℚ)) * (((b - 1 - r).choose (c.1 - r) : ℕ) : ℚ) := by
    have hsplit : b = (c.1 + 1) + (b - (c.1 + 1)) := by omega
    have hsplit_sum := Finset.sum_range_add
      (fun r => ((b - i.1 : ℕ) : ℚ) *
        ((((b - 1 - i.1).choose r : ℕ) : ℚ) *
          (if r ≤ c.1 then ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (((b - 1 - r).choose (c.1 - r) : ℕ) : ℚ) else 0)))
      (c.1 + 1) (b - (c.1 + 1))
    rw [← hsplit] at hsplit_sum
    rw [hsplit_sum]
    have hzero :
        ∑ r ∈ range (b - (c.1 + 1)), ((b - i.1 : ℕ) : ℚ) *
          ((((b - 1 - i.1).choose (c.1 + 1 + r) : ℕ) : ℚ) *
            (if c.1 + 1 + r ≤ c.1 then
              ((-1 : ℚ) ^ (c.1 + 1 + r) / ((c.1 + 1 + r + 1 : ℕ) : ℚ)) *
                (((b - 1 - (c.1 + 1 + r)).choose (c.1 - (c.1 + 1 + r)) : ℕ) : ℚ)
             else 0)) = 0 := by
      refine Finset.sum_eq_zero fun r _ => ?_
      have hgt : ¬ (c.1 + 1 + r ≤ c.1) := by omega
      simp [hgt]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrc : r ≤ c.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    simp only [hrc, ↓reduceIte]
    have hbi : b - i.1 = (b - 1 - i.1) + 1 := by omega
    have hch_nat : (b - i.1) * (b - 1 - i.1).choose r = (r + 1) * (b - i.1).choose (r + 1) := by
      rw [hbi]
      simpa [Nat.mul_comm] using Nat.add_one_mul_choose_eq (b - 1 - i.1) r
    have hch_q : ((b - i.1 : ℕ) : ℚ) * (((b - 1 - i.1).choose r : ℕ) : ℚ) =
        ((r + 1 : ℕ) : ℚ) * (((b - i.1).choose (r + 1) : ℕ) : ℚ) := by
      exact_mod_cast hch_nat
    have hr1 : ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    calc
      ((b - i.1 : ℕ) : ℚ) * ((((b - 1 - i.1).choose r : ℕ) : ℚ) *
          (((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (((b - 1 - r).choose (c.1 - r) : ℕ) : ℚ)))
          = (((b - i.1 : ℕ) : ℚ) * (((b - 1 - i.1).choose r : ℕ) : ℚ)) *
              ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (((b - 1 - r).choose (c.1 - r) : ℕ) : ℚ) := by ring
      _ = (((r + 1 : ℕ) : ℚ) * (((b - i.1).choose (r + 1) : ℕ) : ℚ)) *
              ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (((b - 1 - r).choose (c.1 - r) : ℕ) : ℚ) := by rw [hch_q]
      _ = (-1 : ℚ) ^ r * (((b - i.1).choose (r + 1) : ℕ) : ℚ) *
              (((b - 1 - r).choose (c.1 - r) : ℕ) : ℚ) := by field_simp
  rw [htrunc]
  have halt := sum_alternating_choose_sub (b - i.1) b (c.1 + 1) (Nat.sub_le b i.1)
  have hbi2 : b - (b - i.1) = i.1 := by omega
  rw [hbi2, Finset.sum_range_succ'] at halt
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at halt
  have hneg :
      ∑ r ∈ range (c.1 + 1),
          (-1 : ℚ) ^ (r + 1) * (((b - i.1).choose (r + 1) : ℕ) : ℚ) *
            (((b - (r + 1)).choose (c.1 + 1 - (r + 1)) : ℕ) : ℚ) =
      -(∑ r ∈ range (c.1 + 1),
          (-1 : ℚ) ^ r * (((b - i.1).choose (r + 1) : ℕ) : ℚ) *
            (((b - 1 - r).choose (c.1 - r) : ℕ) : ℚ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h1 : b - (r + 1) = b - 1 - r := by omega
    rw [h1, Nat.add_sub_add_right, pow_succ]
    ring
  linarith

/-- Direct 1D walk triangularization: `W_b * P_b = P_b * U_b` over `ℚ`. -/
theorem walkMat1_mul_pascalRev (b : ℕ) :
    walkMat1 b * pascalRev b = pascalRev b * upperMat1 b := by
  have h := zeroCarryMat1_mul_pascalRev b
  ext i c
  have hij := congrArg (fun M : Matrix (Fin b) (Fin b) ℚ => M i c) h
  rw [degDiag1, Matrix.diagonal_mul] at hij
  have hbi : ((b - i.1 : ℕ) : ℚ) ≠ 0 := by
    have : 0 < b - i.1 := by omega
    exact_mod_cast this.ne'
  have hwalk : (walkMat1 b * pascalRev b) i c =
      (((b - i.1 : ℕ) : ℚ))⁻¹ * (zeroCarryMat1 b * pascalRev b) i c := by
    simp only [Matrix.mul_apply, walkMat1, zeroCarryMat1, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hwalk, hij]
  field_simp

/-- Reversed Pascal matrix has nonzero determinant (`± 1`) over `ℚ`. -/
theorem pascalRev_det_ne_zero (b : ℕ) : (pascalRev b).det ≠ 0 := by
  let σ : Equiv.Perm (Fin b) := Fin.revPerm
  let M : Matrix (Fin b) (Fin b) ℚ := (pascalRev b).submatrix σ id
  have hM_entry : ∀ i j : Fin b, M i j = ((i.1.choose j.1 : ℕ) : ℚ) := by
    intro i j
    simp only [M, σ, pascalRev, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Fin.revPerm_apply,
      Fin.val_rev]
    congr 2
    omega
  have hM_low : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.1 < j.1 := hij
    rw [hM_entry, Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
  have hM_det : M.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular M hM_low]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [hM_entry, Nat.choose_self, Nat.cast_one]
  have hperm : M.det = (Equiv.Perm.sign σ : ℚ) * (pascalRev b).det := by
    simpa [M] using Matrix.det_permute σ (pascalRev b)
  intro hzero
  rw [hzero, mul_zero] at hperm
  linarith [hM_det, hperm]

end ZeroCarrySpanningTrees
