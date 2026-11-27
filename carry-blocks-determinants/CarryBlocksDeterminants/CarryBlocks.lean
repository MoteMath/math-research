/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryBlocksDeterminants.Defs
import CarryBlocksDeterminants.PlateauHankel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Mixed-Radix Carry-Blocks and Binary Gray-Code Carry-Transition Determinants

Proves:
- `det_mixedCarryBlocks_exp`: for any mixed radix `b` (`∀ r, 1 ≤ b r`), any `k`, and any `x` in a
  commutative ring `R`,
  `det (x ^ carryBlocks b k i j)_{0 ≤ i, j < P_k} = (-1) ^ (P_k - 1).choose 2 * (x - 1) ^ (P_k - 1)`.
- `det_mixedCarryBlocks_linear`: unimodularity of the linear carry-blocks matrix on `1 ≤ i, j < P_k`,
  `det (carryBlocks b k (i + 1) (j + 1)) = (-1) ^ (P_k - 1).choose 2`, via polynomial coefficient
  extraction over `Polynomial R` (no division, valid in every characteristic).
- `det_grayCarryTransitions`: exact evaluation of the binary Gray-code carry-transition matrix,
  `det (popcnt (gray (i + j) ^^^ gray i ^^^ gray j))_{1 ≤ i, j < 2^k} = (-1) ^ (2^k - 1).choose 2 * 2 ^ (2^k - 1)`.
-/

namespace CarryBlocksDeterminants

open Matrix Finset Polynomial

section BlockMatrixHelpers

/-- Block upper-triangular matrix on `Fin m × Fin p` with identical diagonal blocks `D` has
determinant `D.det ^ m`. -/
lemma det_block_upperTriangular_const {R : Type*} [CommRing R] :
    ∀ {m p : ℕ} (M : Matrix (Fin m × Fin p) (Fin m × Fin p) R) (D : Matrix (Fin p) (Fin p) R),
      (∀ a c : Fin m, c.val < a.val → ∀ u v : Fin p, M (a, u) (c, v) = 0) →
      (∀ a : Fin m, ∀ u v : Fin p, M (a, u) (a, v) = D u v) →
      M.det = D.det ^ m
  | 0, p, M, D, _, _ => by
      simp
  | m + 1, p, M, D, hzero, hdiag => by
      let e : Fin p ⊕ (Fin m × Fin p) ≃ Fin (m + 1) × Fin p := {
        toFun := fun
          | Sum.inl u => (0, u)
          | Sum.inr (a, u) => (a.succ, u)
        invFun := fun (a, u) =>
          if h : a.val = 0 then Sum.inl u
          else Sum.inr (⟨a.val - 1, by omega⟩, u)
        left_inv := by
          rintro (u | ⟨a, u⟩)
          · simp
          · simp
        right_inv := by
          rintro ⟨a, u⟩
          by_cases h : a.val = 0
          · simp only [h, ↓reduceDIte]
            exact Prod.ext (Fin.ext h.symm) rfl
          · simp only [h, ↓reduceDIte]
            refine Prod.ext ?_ rfl
            ext
            simp
            omega
      }
      rw [show M.det = (M.submatrix e e).det from (Matrix.det_reindex_self e.symm M).symm]
      set C := M.submatrix e e
      have hbl : Matrix.toBlocks₂₁ C = 0 := by
        ext ⟨a, u⟩ v
        simp only [Matrix.toBlocks₂₁, C, Matrix.submatrix_apply, Matrix.of_apply,
          Matrix.zero_apply, e, Equiv.coe_fn_mk]
        exact hzero a.succ 0 (by simp) u v
      have hsplit : C.det = (Matrix.toBlocks₁₁ C).det * (Matrix.toBlocks₂₂ C).det := by
        conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
        rw [hbl, Matrix.det_fromBlocks_zero₂₁]
      have h11 : Matrix.toBlocks₁₁ C = D := by
        ext u v
        simp only [Matrix.toBlocks₁₁, C, Matrix.submatrix_apply, Matrix.of_apply,
          e, Equiv.coe_fn_mk]
        exact hdiag 0 u v
      have h22 : (Matrix.toBlocks₂₂ C).det = D.det ^ m := by
        apply det_block_upperTriangular_const _ D
        · intro a c hlt u v
          simp only [Matrix.toBlocks₂₂, C, Matrix.submatrix_apply, Matrix.of_apply,
            e, Equiv.coe_fn_mk]
          exact hzero a.succ c.succ (by simp; omega) u v
        · intro a u v
          simp only [Matrix.toBlocks₂₂, C, Matrix.submatrix_apply, Matrix.of_apply,
            e, Equiv.coe_fn_mk]
          exact hdiag a.succ u v
      rw [hsplit, h11, h22, pow_succ, mul_comm]

/-- Reversing the first coordinate of `Fin m × Fin p`. -/
def revFirstPerm (m p : ℕ) : Equiv.Perm (Fin m × Fin p) :=
  Equiv.prodCongr (Fin.revPerm (n := m)) (Equiv.refl (Fin p))

/-- Sign of reversing the first coordinate of `Fin m × Fin p`. -/
lemma sign_revFirst (m : ℕ) :
    ∀ p : ℕ, (Equiv.Perm.sign (revFirstPerm m p) : ℤ) = (-1 : ℤ) ^ (p * m.choose 2)
  | 0 => by
      have h1 : revFirstPerm m 0 = 1 := by
        ext x
        · exact absurd x.2.isLt (by omega)
        · exact absurd x.2.isLt (by omega)
      rw [h1, map_one]
      simp
  | p + 1 => by
      let e : (Fin m × Fin p) ⊕ Fin m ≃ Fin m × Fin (p + 1) := {
        toFun := fun
          | Sum.inl (a, u) => (a, u.castSucc)
          | Sum.inr a => (a, Fin.last p)
        invFun := fun (a, u) =>
          if h : u.val < p then Sum.inl (a, ⟨u.val, h⟩) else Sum.inr a
        left_inv := by
          rintro (⟨a, u⟩ | a)
          · simp [u.isLt]
          · simp
        right_inv := by
          rintro ⟨a, u⟩
          by_cases h : u.val < p
          · simp [h]
          · simp only [h, ↓reduceDIte]
            refine Prod.ext rfl ?_
            ext
            simp only [Fin.val_last]
            omega
      }
      have hconj :
          revFirstPerm m (p + 1) =
            e.permCongr (Equiv.Perm.sumCongr (revFirstPerm m p) (Fin.revPerm (n := m))) := by
        ext ⟨a, u⟩
        · by_cases h : u.val < p
          · simp [revFirstPerm, e, h]
          · simp [revFirstPerm, e, h]
        · by_cases h : u.val < p
          · simp [revFirstPerm, e, h]
          · simp only [revFirstPerm, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map_apply,
              Equiv.permCongr_apply, e, Equiv.coe_fn_symm_mk, h, ↓reduceDIte,
              Equiv.Perm.sumCongr_apply, Sum.map_inr, Equiv.coe_fn_mk, Fin.val_last]
            omega
      rw [hconj, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]
      push_cast
      rw [sign_revFirst m p, sign_fin_revPerm m, ← pow_add]
      congr 1
      ring

/-- Block anti-lower-triangular matrix on `Fin m × Fin p` with identical anti-diagonal blocks `D`
has determinant `(-1) ^ (p * m.choose 2) * D.det ^ m`. -/
lemma det_block_antiLowerTriangular_const {R : Type*} [CommRing R] {m p : ℕ}
    (M : Matrix (Fin m × Fin p) (Fin m × Fin p) R) (D : Matrix (Fin p) (Fin p) R)
    (hzero : ∀ a c : Fin m, a.val + c.val < m - 1 → ∀ u v : Fin p, M (a, u) (c, v) = 0)
    (hdiag : ∀ a c : Fin m, a.val + c.val = m - 1 → ∀ u v : Fin p, M (a, u) (c, v) = D u v) :
    M.det = (-1 : R) ^ (p * m.choose 2) * D.det ^ m := by
  let σ : Equiv.Perm (Fin m × Fin p) := revFirstPerm m p
  have hperm : (M.submatrix σ id).det = (Equiv.Perm.sign σ : R) * M.det := by
    rw [Matrix.det_permute]
  have hsign : (Equiv.Perm.sign σ : R) = (-1 : R) ^ (p * m.choose 2) := by
    have hz := sign_revFirst m p
    have hc := congrArg (Int.cast (R := R)) hz
    simpa [σ] using hc
  have hupper : (M.submatrix σ id).det = D.det ^ m := by
    apply det_block_upperTriangular_const _ D
    · intro a c hlt u v
      simp only [Matrix.submatrix_apply, id_eq, σ, revFirstPerm, Equiv.prodCongr_apply,
        Prod.map_apply, Fin.revPerm_apply, Equiv.refl_apply]
      apply hzero a.rev c
      simp only [Fin.val_rev]
      omega
    · intro a u v
      simp only [Matrix.submatrix_apply, id_eq, σ, revFirstPerm, Equiv.prodCongr_apply,
        Prod.map_apply, Fin.revPerm_apply, Equiv.refl_apply]
      apply hdiag a.rev a
      simp only [Fin.val_rev]
      omega
  have hsq : (-1 : R) ^ (p * m.choose 2) * (-1 : R) ^ (p * m.choose 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [hsign] at hperm
  calc M.det = (-1 : R) ^ (p * m.choose 2) * ((-1 : R) ^ (p * m.choose 2) * M.det) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = (-1 : R) ^ (p * m.choose 2) * (M.submatrix σ id).det := by rw [← hperm]
    _ = (-1 : R) ^ (p * m.choose 2) * D.det ^ m := by rw [hupper]

/-- Subtracting block-row `0` from all block-rows `a ≠ 0` preserves determinant on `Fin B × Fin P`. -/
lemma det_sub_blockRow_zero {R : Type*} [CommRing R] {B P : ℕ} [NeZero B]
    (M : Matrix (Fin B × Fin P) (Fin B × Fin P) R) :
    (Matrix.of fun (au cv : Fin B × Fin P) =>
      if au.1 = 0 then M au cv else M au cv - M (0, au.2) cv).det = M.det := by
  let L : Matrix (Fin B × Fin P) (Fin B × Fin P) R :=
    Matrix.of fun (a, u) (c, v) =>
      (if (a, u) = (c, v) then (1 : R) else 0) + (if a ≠ 0 ∧ c = 0 ∧ u = v then (-1 : R) else 0)
  have hmul : L * M = Matrix.of fun (au cv : Fin B × Fin P) =>
      if au.1 = 0 then M au cv else M au cv - M (0, au.2) cv := by
    ext ⟨a, u⟩ ⟨c, v⟩
    simp only [Matrix.mul_apply, L, Matrix.of_apply, add_mul]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ x : Fin B × Fin P, (if (a, u) = x then (1 : R) else 0) * M x (c, v) =
        M (a, u) (c, v) := by
      rw [Finset.sum_eq_single (a, u)]
      · simp
      · intro x _ hx; simp [Ne.symm hx]
      · simp
    have h2 : ∑ x : Fin B × Fin P,
        (if a ≠ 0 ∧ x.1 = 0 ∧ u = x.2 then (-1 : R) else 0) * M x (c, v) =
        if a = 0 then 0 else -M (0, u) (c, v) := by
      by_cases ha : a = 0
      · simp [ha]
      · rw [Finset.sum_eq_single ((0 : Fin B), u)]
        · simp [ha]
        · intro x _ hx
          have : ¬ (a ≠ 0 ∧ x.1 = 0 ∧ u = x.2) := by
            rintro ⟨_, h1, h2⟩
            exact hx (Prod.ext h1 h2.symm)
          simp [this]
        · simp
    rw [h1, h2]
    by_cases ha : a = 0 <;> simp [ha, sub_eq_add_neg]
  rw [← hmul, Matrix.det_mul]
  suffices hL : L.det = 1 by rw [hL, one_mul]
  have hL_tri : L.det = (1 : Matrix (Fin P) (Fin P) R).det ^ B := by
    -- `Lᵀ` is block upper triangular with diagonal blocks `1`!
    rw [← Matrix.det_transpose]
    apply det_block_upperTriangular_const _ 1
    · intro a c hlt u v
      simp only [Matrix.transpose_apply, L, Matrix.of_apply]
      have hne : (c, v) ≠ (a, u) := by
        intro h
        have hc := congrArg (fun x => x.1.val) h
        dsimp only at hc
        omega
      have ha0 : a ≠ 0 := by
        intro h
        subst h
        simp at hlt
      simp [hne, ha0]
    · intro a u v
      simp only [Matrix.transpose_apply, L, Matrix.of_apply, Matrix.one_apply]
      have hna : ¬ (a ≠ 0 ∧ a = 0 ∧ v = u) := by rintro ⟨h1, h2, _⟩; exact h1 h2
      simp only [hna, ↓reduceIte, add_zero, Prod.mk.injEq, true_and]
      by_cases huv : u = v <;> simp [huv, eq_comm]
  rw [hL_tri, Matrix.det_one, one_pow]

end BlockMatrixHelpers

section CarryBlockLemmas

lemma place_dvd_place_of_le (b : ℕ → ℕ) : ∀ {r k : ℕ}, r ≤ k → place b r ∣ place b k
  | r, k, h => by
      induction h with
      | refl => exact dvd_refl _
      | @step m _ ih => exact dvd_mul_of_dvd_left ih (b m)

lemma carryBit_mod_place (b : ℕ → ℕ) {r k : ℕ} (hr : r < k) (a c u v : ℕ) :
    carryBit b r (a * place b k + u) (c * place b k + v) = carryBit b r u v := by
  have hdvd : place b (r + 1) ∣ place b k := place_dvd_place_of_le b hr
  obtain ⟨q, hq⟩ := hdvd
  have h1 : (a * place b k + u) % place b (r + 1) = u % place b (r + 1) := by
    rw [hq, show a * (place b (r + 1) * q) + u = u + place b (r + 1) * (a * q) by ring]
    exact Nat.add_mul_mod_self_left u (place b (r + 1)) (a * q)
  have h2 : (c * place b k + v) % place b (r + 1) = v % place b (r + 1) := by
    rw [hq, show c * (place b (r + 1) * q) + v = v + place b (r + 1) * (c * q) by ring]
    exact Nat.add_mul_mod_self_left v (place b (r + 1)) (c * q)
  simp only [carryBit, h1, h2]

lemma carryBlocks_mod_place (b : ℕ → ℕ) :
    ∀ {r k : ℕ}, r ≤ k → ∀ a c u v : ℕ,
      carryBlocks b r (a * place b k + u) (c * place b k + v) = carryBlocks b r u v
  | 0, _, _, _, _, _, _ => rfl
  | r + 1, k, hr, a, c, u, v => by
      simp only [carryBlocks]
      rw [carryBlocks_mod_place b (Nat.le_of_succ_le hr) a c u v]
      rw [carryBit_mod_place b hr a c u v]
      cases r with
      | zero => simp
      | succ r' =>
          simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, false_or]
          rw [carryBit_mod_place b (Nat.lt_of_succ_lt hr) a c u v]

/-- Fundamental block-splitting recurrence for `carryBlocks b (k + 1)`. -/
lemma carryBlocks_succ_block (b : ℕ → ℕ) (k a c u v : ℕ)
    (hu : u < place b k) (hv : v < place b k) (ha : a < b k) (hc : c < b k) :
    carryBlocks b (k + 1) (a * place b k + u) (c * place b k + v) =
      carryBlocks b k u v + if u + v < place b k ∧ b k ≤ a + c then 1 else 0 := by
  simp only [carryBlocks]
  rw [carryBlocks_mod_place b (le_refl k) a c u v]
  congr 1
  have hP1 : place b (k + 1) = place b k * b k := rfl
  have hi_lt : a * place b k + u < place b (k + 1) := by
    rw [hP1]
    have h1 : a + 1 ≤ b k := ha
    nlinarith
  have hj_lt : c * place b k + v < place b (k + 1) := by
    rw [hP1]
    have h1 : c + 1 ≤ b k := hc
    nlinarith
  have hbit_k : carryBit b k (a * place b k + u) (c * place b k + v) = 1 ↔
      place b k * b k ≤ (a + c) * place b k + (u + v) := by
    unfold carryBit
    rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt, hP1]
    split_ifs with h
    · exact ⟨fun _ => by linarith, fun _ => rfl⟩
    · exact ⟨fun h0 => by norm_num at h0, fun hle => absurd (by linarith) h⟩
  cases k with
  | zero =>
      simp only [place] at hu hv hbit_k ⊢
      have hu0 : u = 0 := by omega
      have hv0 : v = 0 := by omega
      subst hu0; subst hv0
      simp only [true_or, and_true, add_zero, zero_lt_one, true_and, mul_one] at hbit_k ⊢
      have hiff : carryBit b 0 a c = 1 ↔ b 0 ≤ a + c := by simpa using hbit_k
      by_cases h : b 0 ≤ a + c
      · simp [h, hiff.mpr h]
      · have hne : carryBit b 0 a c ≠ 1 := fun h1 => h (hiff.mp h1)
        simp [h, hne]
  | succ k' =>
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, false_or]
      have hprev_iff : carryBit b k' (a * place b (k' + 1) + u) (c * place b (k' + 1) + v) = 0 ↔
          u + v < place b (k' + 1) := by
        rw [carryBit_mod_place b (Nat.lt_succ_self k') a c u v]
        simp only [carryBit, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv]
        split_ifs with h
        · exact ⟨fun h0 => by norm_num at h0, fun hlt => by omega⟩
        · exact ⟨fun _ => by omega, fun _ => rfl⟩
      have hiff :
          (carryBit b (k' + 1) (a * place b (k' + 1) + u) (c * place b (k' + 1) + v) = 1 ∧
            carryBit b k' (a * place b (k' + 1) + u) (c * place b (k' + 1) + v) = 0) ↔
          (u + v < place b (k' + 1) ∧ b (k' + 1) ≤ a + c) := by
        rw [hbit_k, hprev_iff]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h2, ?_⟩
          by_contra hlt
          push Not at hlt
          have hle : a + c + 1 ≤ b (k' + 1) := hlt
          have hmul : (a + c + 1) * place b (k' + 1) ≤ b (k' + 1) * place b (k' + 1) :=
            Nat.mul_le_mul_right _ hle
          nlinarith
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h1⟩
          have hmul : b (k' + 1) * place b (k' + 1) ≤ (a + c) * place b (k' + 1) :=
            Nat.mul_le_mul_right _ h2
          nlinarith
      by_cases h : u + v < place b (k' + 1) ∧ b (k' + 1) ≤ a + c
      · simp [h, hiff.mpr h]
      · have hne : ¬ (carryBit b (k' + 1) (a * place b (k' + 1) + u) (c * place b (k' + 1) + v) = 1 ∧
            carryBit b k' (a * place b (k' + 1) + u) (c * place b (k' + 1) + v) = 0) :=
          fun h1 => h (hiff.mp h1)
        simp [h, hne]

/-- Zero carries occur when `u + v = place b k - 1` (every mixed-radix digit sums to `b_r - 1`). -/
lemma carryBit_eq_zero_of_add_eq_place_sub_one (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    {k r u v : ℕ} (hr : r < k) (huv : u + v = place b k - 1) :
    carryBit b r u v = 0 := by
  simp only [carryBit]
  suffices h : u % place b (r + 1) + v % place b (r + 1) < place b (r + 1) by
    have hnot : ¬ (place b (r + 1) ≤ u % place b (r + 1) + v % place b (r + 1)) := by omega
    simp [hnot]
  have hdvd : place b (r + 1) ∣ place b k := place_dvd_place_of_le b hr
  obtain ⟨q, hq⟩ := hdvd
  have hPpos : 1 ≤ place b (r + 1) := place_pos b hb (r + 1)
  have hPkpos : 1 ≤ place b k := place_pos b hb k
  have hqpos : 1 ≤ q := by
    by_contra h0
    have : q = 0 := by omega
    rw [this, mul_zero] at hq
    omega
  have hmod_sum : (u % place b (r + 1) + v % place b (r + 1)) % place b (r + 1) =
      place b (r + 1) - 1 := by
    rw [← Nat.add_mod, huv, hq]
    have heq : place b (r + 1) * q - 1 = (place b (r + 1) - 1) + place b (r + 1) * (q - 1) := by
      have : place b (r + 1) * q = place b (r + 1) + place b (r + 1) * (q - 1) := by
        calc place b (r + 1) * q = place b (r + 1) * (1 + (q - 1)) := by congr 1; omega
          _ = place b (r + 1) + place b (r + 1) * (q - 1) := by ring
      omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hu_lt : u % place b (r + 1) < place b (r + 1) := Nat.mod_lt u (by omega)
  have hv_lt : v % place b (r + 1) < place b (r + 1) := Nat.mod_lt v (by omega)
  set s := u % place b (r + 1) + v % place b (r + 1)
  have hs_lt : s < 2 * place b (r + 1) := by omega
  by_contra hge
  push Not at hge
  have hmod2 : s % place b (r + 1) = s - place b (r + 1) := by
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  omega

lemma carryBlocks_eq_zero_of_add_eq_place_sub_one (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) :
    ∀ {r k u v : ℕ}, r ≤ k → u + v = place b k - 1 → carryBlocks b r u v = 0
  | 0, _, _, _, _, _ => rfl
  | r + 1, k, u, v, hr, huv => by
      simp only [carryBlocks]
      rw [carryBlocks_eq_zero_of_add_eq_place_sub_one b hb (Nat.le_of_succ_le hr) huv]
      rw [carryBit_eq_zero_of_add_eq_place_sub_one b hb hr huv]
      simp

lemma carryBlocks_zero_left (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) : ∀ k j : ℕ, carryBlocks b k 0 j = 0
  | 0, _ => rfl
  | k + 1, j => by
      simp only [carryBlocks, carryBlocks_zero_left b hb k j, zero_add]
      have h0 : carryBit b k 0 j = 0 := by
        simp only [carryBit, Nat.zero_mod, zero_add]
        have hP : 0 < place b (k + 1) := place_pos b hb (k + 1)
        have hlt : j % place b (k + 1) < place b (k + 1) := Nat.mod_lt j hP
        have hnot : ¬ (place b (k + 1) ≤ j % place b (k + 1)) := by omega
        simp [hnot]
      simp [h0]

lemma carryBlocks_zero_right (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) : ∀ k i : ℕ, carryBlocks b k i 0 = 0
  | 0, _ => rfl
  | k + 1, i => by
      simp only [carryBlocks, carryBlocks_zero_right b hb k i, zero_add]
      have h0 : carryBit b k i 0 = 0 := by
        simp only [carryBit, Nat.zero_mod, add_zero]
        have hP : 0 < place b (k + 1) := place_pos b hb (k + 1)
        have hlt : i % place b (k + 1) < place b (k + 1) := Nat.mod_lt i hP
        have hnot : ¬ (place b (k + 1) ≤ i % place b (k + 1)) := by omega
        simp [hnot]
      simp [h0]

/-- Sign-exponent parity identity for the block recursion:
`(B*P - 1).choose 2` and `(P - 1).choose 2 + (B - 1) * P.choose 2 + P * (B - 1).choose 2`
have the same parity for all `P ≥ 1, B ≥ 1`. -/
lemma neg_one_pow_carryBlocks_step {R : Type*} [CommRing R] {P B : ℕ} (hP : 1 ≤ P) (hB : 1 ≤ B) :
    (-1 : R) ^ ((P - 1).choose 2 + P * (B - 1).choose 2 + (B - 1) * P.choose 2) =
      (-1 : R) ^ ((P * B - 1).choose 2) := by
  have h2choose : ∀ n : ℕ, 2 * n.choose 2 = n * (n - 1) := fun n => by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
  have hdiff :
      ((P * B - 1).choose 2 : ℤ) -
        (((P - 1).choose 2 : ℤ) + (P : ℤ) * ((B - 1).choose 2 : ℤ) +
          ((B - 1 : ℕ) : ℤ) * (P.choose 2 : ℤ)) =
        2 * ((B.choose 2 : ℤ) * (P.choose 2 : ℤ)) := by
    have h1 : (2 : ℤ) * ((P * B - 1).choose 2 : ℤ) = ((P * B - 1 : ℕ) : ℤ) * ((P * B - 1 - 1 : ℕ) : ℤ) := by
      exact_mod_cast h2choose (P * B - 1)
    have h2 : (2 : ℤ) * ((P - 1).choose 2 : ℤ) = ((P - 1 : ℕ) : ℤ) * ((P - 1 - 1 : ℕ) : ℤ) := by
      exact_mod_cast h2choose (P - 1)
    have h3 : (2 : ℤ) * ((B - 1).choose 2 : ℤ) = ((B - 1 : ℕ) : ℤ) * ((B - 1 - 1 : ℕ) : ℤ) := by
      exact_mod_cast h2choose (B - 1)
    have h4 : (2 : ℤ) * (P.choose 2 : ℤ) = (P : ℤ) * ((P - 1 : ℕ) : ℤ) := by
      exact_mod_cast h2choose P
    have h5 : (2 : ℤ) * (B.choose 2 : ℤ) = (B : ℤ) * ((B - 1 : ℕ) : ℤ) := by
      exact_mod_cast h2choose B
    have hPB : 1 ≤ P * B := by nlinarith
    -- Multiply the desired identity by 4 and use integer algebra!
    have h4eq : 4 * (((P * B - 1).choose 2 : ℤ) -
        (((P - 1).choose 2 : ℤ) + (P : ℤ) * ((B - 1).choose 2 : ℤ) +
          ((B - 1 : ℕ) : ℤ) * (P.choose 2 : ℤ))) =
        4 * (2 * ((B.choose 2 : ℤ) * (P.choose 2 : ℤ))) := by
      have hcast_PB : ((P * B - 1 : ℕ) : ℤ) = (P : ℤ) * (B : ℤ) - 1 := by omega
      have hcast_P : ((P - 1 : ℕ) : ℤ) = (P : ℤ) - 1 := by omega
      have hcast_B : ((B - 1 : ℕ) : ℤ) = (B : ℤ) - 1 := by omega
      have hPB2 : ((P * B - 1 : ℕ) : ℤ) * ((P * B - 1 - 1 : ℕ) : ℤ) =
          ((P : ℤ) * (B : ℤ) - 1) * ((P : ℤ) * (B : ℤ) - 2) := by
        by_cases hPB_eq : P * B = 1
        · have hPBz : (P : ℤ) * (B : ℤ) = 1 := by exact_mod_cast hPB_eq
          simp [hPB_eq, hPBz]
        · have : ((P * B - 1 - 1 : ℕ) : ℤ) = (P : ℤ) * (B : ℤ) - 2 := by omega
          rw [hcast_PB, this]
      have hP2 : ((P - 1 : ℕ) : ℤ) * ((P - 1 - 1 : ℕ) : ℤ) = ((P : ℤ) - 1) * ((P : ℤ) - 2) := by
        by_cases hP_eq : P = 1
        · simp [hP_eq]
        · have : ((P - 1 - 1 : ℕ) : ℤ) = (P : ℤ) - 2 := by omega
          rw [hcast_P, this]
      have hB2 : ((B - 1 : ℕ) : ℤ) * ((B - 1 - 1 : ℕ) : ℤ) = ((B : ℤ) - 1) * ((B : ℤ) - 2) := by
        by_cases hB_eq : B = 1
        · simp [hB_eq]
        · have : ((B - 1 - 1 : ℕ) : ℤ) = (B : ℤ) - 2 := by omega
          rw [hcast_B, this]
      have h4_lhs :
          4 * (((P * B - 1).choose 2 : ℤ) -
            (((P - 1).choose 2 : ℤ) + (P : ℤ) * ((B - 1).choose 2 : ℤ) +
              ((B - 1 : ℕ) : ℤ) * (P.choose 2 : ℤ))) =
          2 * (2 * ((P * B - 1).choose 2 : ℤ)) -
            2 * (2 * ((P - 1).choose 2 : ℤ)) -
            2 * (P : ℤ) * (2 * ((B - 1).choose 2 : ℤ)) -
            2 * ((B - 1 : ℕ) : ℤ) * (2 * (P.choose 2 : ℤ)) := by ring
      have h4_rhs : 4 * (2 * ((B.choose 2 : ℤ) * (P.choose 2 : ℤ))) =
          2 * ((2 * (B.choose 2 : ℤ)) * (2 * (P.choose 2 : ℤ))) := by ring
      rw [h4_lhs, h4_rhs, h1, h2, h3, h4, h5, hPB2, hP2, hB2, hcast_P, hcast_B]
      ring
    linarith
  have hle : (P - 1).choose 2 + P * (B - 1).choose 2 + (B - 1) * P.choose 2 ≤ (P * B - 1).choose 2 := by
    have hnonneg : (0 : ℤ) ≤ 2 * ((B.choose 2 : ℤ) * (P.choose 2 : ℤ)) := by positivity
    omega
  have hnat : (P * B - 1).choose 2 =
      ((P - 1).choose 2 + P * (B - 1).choose 2 + (B - 1) * P.choose 2) +
        2 * (B.choose 2 * P.choose 2) := by
    omega
  rw [hnat, pow_add (-1 : R) _ (2 * (B.choose 2 * P.choose 2)), pow_mul (-1 : R) 2]
  norm_num

end CarryBlockLemmas

/-- **Exponential Mixed-Radix Carry-Blocks Determinant Theorem.**
For any mixed radix `b : ℕ → ℕ` with `∀ r, 1 ≤ b r`, any `k : ℕ`, and any `x` in a commutative
ring `R`, the `P_k × P_k` matrix `(x ^ carryBlocks b k i j)` has exact determinant
`(-1) ^ (P_k - 1).choose 2 * (x - 1) ^ (P_k - 1)`. -/
theorem det_mixedCarryBlocks_exp {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) :
    ∀ (k : ℕ) (x : R),
      (mixedCarryBlocksExpMatrix b k x).det =
        (-1 : R) ^ ((place b k - 1).choose 2) * (x - 1) ^ (place b k - 1)
  | 0, x => by
      simp [mixedCarryBlocksExpMatrix, place, carryBlocks]
      rfl
  | k + 1, x => by
      set P := place b k
      set B := b k
      have hP : 1 ≤ P := place_pos b hb k
      have hB : 1 ≤ B := hb k
      have : NeZero B := ⟨by omega⟩
      let eProd : Fin B × Fin P ≃ Fin (place b (k + 1)) := {
        toFun := fun (a, u) => ⟨a.val * P + u.val, by
          show a.val * P + u.val < P * B
          have ha : a.val + 1 ≤ B := a.isLt
          nlinarith [u.isLt]⟩
        invFun := fun i => (⟨i.val / P, by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          have hi : i.val < P * B := i.isLt
          linarith⟩, ⟨i.val % P, Nat.mod_lt _ (by omega)⟩)
        left_inv := by
          rintro ⟨a, u⟩
          apply Prod.ext
          · ext
            simp only
            rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt u.isLt, add_zero]
          · ext
            simp only
            rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt u.isLt]
        right_inv := by
          intro i
          ext
          simp only
          rw [mul_comm]
          exact Nat.div_add_mod i.val P
      }
      rw [show (mixedCarryBlocksExpMatrix b (k + 1) x).det =
        ((mixedCarryBlocksExpMatrix b (k + 1) x).submatrix eProd eProd).det
        from (Matrix.det_reindex_self eProd.symm _).symm]
      set M : Matrix (Fin B × Fin P) (Fin B × Fin P) R :=
        (mixedCarryBlocksExpMatrix b (k + 1) x).submatrix eProd eProd
      have hM_val : ∀ (a c : Fin B) (u v : Fin P),
          M (a, u) (c, v) =
            x ^ (carryBlocks b k u.val v.val +
              if u.val + v.val < P ∧ B ≤ a.val + c.val then 1 else 0) := by
        intro a c u v
        simp only [M, Matrix.submatrix_apply, mixedCarryBlocksExpMatrix, Matrix.of_apply,
          eProd, Equiv.coe_fn_mk]
        rw [carryBlocks_succ_block b k a.val c.val u.val v.val u.isLt v.isLt a.isLt c.isLt]
      rw [← det_sub_blockRow_zero M]
      set N : Matrix (Fin B × Fin P) (Fin B × Fin P) R :=
        Matrix.of fun au cv => if au.1 = 0 then M au cv else M au cv - M (0, au.2) cv
      -- Split `Fin B × Fin P ≃ Fin P ⊕ (Fin (B - 1) × Fin P)` separating `a = 0` from `a ≥ 1`.
      let eSplit : Fin P ⊕ (Fin (B - 1) × Fin P) ≃ Fin B × Fin P := {
        toFun := fun
          | Sum.inl u => (0, u)
          | Sum.inr (a, u) => (⟨a.val + 1, by omega⟩, u)
        invFun := fun (a, u) =>
          if h : a.val = 0 then Sum.inl u
          else Sum.inr (⟨a.val - 1, by omega⟩, u)
        left_inv := by
          rintro (u | ⟨a, u⟩)
          · simp
          · simp
        right_inv := by
          rintro ⟨a, u⟩
          by_cases h : a.val = 0
          · simp only [h, ↓reduceDIte]
            exact Prod.ext (Fin.ext h.symm) rfl
          · simp only [h, ↓reduceDIte]
            refine Prod.ext ?_ rfl
            ext; simp; omega
      }
      rw [show N.det = (N.submatrix eSplit eSplit).det from (Matrix.det_reindex_self eSplit.symm N).symm]
      set C := N.submatrix eSplit eSplit
      have hbl : Matrix.toBlocks₂₁ C = 0 := by
        ext ⟨a, u⟩ v
        simp only [Matrix.toBlocks₂₁, C, Matrix.submatrix_apply, Matrix.of_apply,
          Matrix.zero_apply, eSplit, Equiv.coe_fn_mk, N]
        have hne : (⟨a.val + 1, by omega⟩ : Fin B) ≠ 0 := by
          intro h; have := congrArg Fin.val h; simp at this
        simp only [hne, ↓reduceIte]
        rw [hM_val, hM_val]
        have hlt1 : ¬ B ≤ a.val + 1 := by omega
        have hB0 : B ≠ 0 := by omega
        simp [hlt1, hB0]
      have hsplit : C.det = (Matrix.toBlocks₁₁ C).det * (Matrix.toBlocks₂₂ C).det := by
        conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
        rw [hbl, Matrix.det_fromBlocks_zero₂₁]
      have h11 : Matrix.toBlocks₁₁ C = mixedCarryBlocksExpMatrix b k x := by
        ext u v
        simp only [Matrix.toBlocks₁₁, C, Matrix.submatrix_apply, Matrix.of_apply,
          eSplit, Equiv.coe_fn_mk, N, ↓reduceIte, mixedCarryBlocksExpMatrix]
        rw [hM_val]
        have hB0 : B ≠ 0 := by omega
        simp [hB0]
      let D : Matrix (Fin P) (Fin P) R :=
        Matrix.of fun u v =>
          x ^ (carryBlocks b k u.val v.val + if u.val + v.val < P then 1 else 0) -
            x ^ (carryBlocks b k u.val v.val)
      have hD_det : D.det = (-1 : R) ^ (P.choose 2) * (x - 1) ^ P := by
        apply det_of_antiUpperTriangular D (x - 1)
        · intro u v hgt
          simp only [D, Matrix.of_apply]
          have hnot : ¬ u.val + v.val < P := by omega
          simp [hnot]
        · intro u v heq
          simp only [D, Matrix.of_apply]
          have hlt : u.val + v.val < P := by omega
          have hcb : carryBlocks b k u.val v.val = 0 :=
            carryBlocks_eq_zero_of_add_eq_place_sub_one b hb (le_refl k) heq
          simp [hlt, hcb]
      have h22 : (Matrix.toBlocks₂₂ C).det =
          (-1 : R) ^ (P * (B - 1).choose 2) * D.det ^ (B - 1) := by
        apply det_block_antiLowerTriangular_const _ D
        · intro a c hlt u v
          simp only [Matrix.toBlocks₂₂, C, Matrix.submatrix_apply, Matrix.of_apply,
            eSplit, Equiv.coe_fn_mk, N]
          have hne : (⟨a.val + 1, by omega⟩ : Fin B) ≠ 0 := by
            intro h; have := congrArg Fin.val h; simp at this
          simp only [hne, ↓reduceIte]
          rw [hM_val, hM_val]
          have hnot1 : ¬ B ≤ (a.val + 1) + (c.val + 1) := by omega
          have hnot2 : ¬ B ≤ c.val + 1 := by omega
          simp [hnot1, hnot2]
        · intro a c heq u v
          simp only [Matrix.toBlocks₂₂, C, Matrix.submatrix_apply, Matrix.of_apply,
            eSplit, Equiv.coe_fn_mk, N, D]
          have hne : (⟨a.val + 1, by omega⟩ : Fin B) ≠ 0 := by
            intro h; have := congrArg Fin.val h; simp at this
          simp only [hne, ↓reduceIte]
          rw [hM_val, hM_val]
          have hge1 : B ≤ (a.val + 1) + (c.val + 1) := by omega
          have hnot2 : ¬ B ≤ c.val + 1 := by omega
          simp [hge1, hnot2]
      rw [hsplit, h11, h22, det_mixedCarryBlocks_exp b hb k x, hD_det]
      have hexp_x : (P - 1) + P * (B - 1) = P * B - 1 := by
        have hPB : P * B = P + P * (B - 1) := by
          calc P * B = P * (1 + (B - 1)) := by congr 1; omega
            _ = P + P * (B - 1) := by ring
        omega
      calc (-1 : R) ^ ((P - 1).choose 2) * (x - 1) ^ (P - 1) *
            ((-1 : R) ^ (P * (B - 1).choose 2) * ((-1 : R) ^ (P.choose 2) * (x - 1) ^ P) ^ (B - 1))
          = (-1 : R) ^ ((P - 1).choose 2 + P * (B - 1).choose 2 + (B - 1) * P.choose 2) *
              (x - 1) ^ ((P - 1) + P * (B - 1)) := by
              rw [mul_pow, ← pow_mul, ← pow_mul, pow_add, pow_add, pow_add]
              rw [mul_comm (P.choose 2) (B - 1)]
              ring
        _ = (-1 : R) ^ ((P * B - 1).choose 2) * (x - 1) ^ (P * B - 1) := by
              rw [neg_one_pow_carryBlocks_step hP hB, hexp_x]

/-- **Unimodular Mixed-Radix Carry-Blocks Determinant Theorem.**
For any mixed radix `b` (`∀ r, 1 ≤ b r`), any `k : ℕ`, and any commutative ring `R`, the linear
carry-blocks matrix `(carryBlocks b k (i + 1) (j + 1))_{0 ≤ i, j < P_k - 1}` is unimodular with
determinant `(-1) ^ (P_k - 1).choose 2`. Proved without division via polynomial coefficient
extraction over `Polynomial R`. -/
theorem det_mixedCarryBlocks_linear {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r)
    (k : ℕ) :
    (mixedCarryBlocksMatrix b k (R := R)).det = (-1 : R) ^ ((place b k - 1).choose 2) := by
  set n := place b k
  have hn : 1 ≤ n := place_pos b hb k
  -- Work over `Polynomial R` at `x = X + 1`.
  let M : Matrix (Fin n) (Fin n) R[X] := mixedCarryBlocksExpMatrix b k (X + 1)
  have hM_det : M.det = (-1 : R[X]) ^ ((n - 1).choose 2) * X ^ (n - 1) := by
    have h := det_mixedCarryBlocks_exp (R := R[X]) b hb k (X + 1)
    rw [add_sub_cancel_right] at h
    exact h
  let z : Fin n := ⟨0, by omega⟩
  rw [← det_sub_fixed_row M z (fun i => i ≠ z) (by simp)] at hM_det
  set A : Matrix (Fin n) (Fin n) R[X] :=
    Matrix.of fun i j => if i ≠ z then M i j - M z j else M i j
  let e : Fin 1 ⊕ Fin (n - 1) ≃ Fin n := {
    toFun := fun
      | Sum.inl _ => z
      | Sum.inr i => ⟨i.val + 1, by omega⟩
    invFun := fun i =>
      if h : i.val = 0 then Sum.inl 0 else Sum.inr ⟨i.val - 1, by omega⟩
    left_inv := by
      rintro (u | i)
      · fin_cases u; simp [z]
      · simp
    right_inv := by
      intro i
      by_cases h : i.val = 0
      · simp only [h, ↓reduceDIte]; ext; exact h.symm
      · simp only [h, ↓reduceDIte]; ext; simp; omega
  }
  rw [show A.det = (A.submatrix e e).det from (Matrix.det_reindex_self e.symm A).symm] at hM_det
  set C := A.submatrix e e
  have hbl : Matrix.toBlocks₂₁ C = 0 := by
    apply Matrix.ext
    intro i u
    fin_cases u
    have hne : e (Sum.inr i) ≠ z := by
      intro h; have := congrArg Fin.val h; simp [e, z] at this
    simp only [Matrix.toBlocks₂₁, C, Matrix.submatrix_apply, Matrix.of_apply, Matrix.zero_apply, A]
    split_ifs
    simp only [M, mixedCarryBlocksExpMatrix, Matrix.of_apply, e, Equiv.coe_fn_mk, z]
    rw [carryBlocks_zero_right b hb, carryBlocks_zero_left b hb, sub_self]
  have h11 : (Matrix.toBlocks₁₁ C).det = 1 := by
    rw [Matrix.det_fin_one]
    simp only [Matrix.toBlocks₁₁, C, Matrix.submatrix_apply, Matrix.of_apply, e, Equiv.coe_fn_mk,
      A, ne_eq, not_true_eq_false, ↓reduceIte, M, mixedCarryBlocksExpMatrix, z]
    rw [carryBlocks_zero_left b hb, pow_zero]
  let Q : Matrix (Fin (n - 1)) (Fin (n - 1)) R[X] :=
    Matrix.of fun i j => ∑ r ∈ Finset.range (carryBlocks b k (i.val + 1) (j.val + 1)), ((X : R[X]) + 1) ^ r
  have h22 : Matrix.toBlocks₂₂ C = (X : R[X]) • Q := by
    apply Matrix.ext
    intro i j
    have hne : e (Sum.inr i) ≠ z := by
      intro h; have := congrArg Fin.val h; simp [e, z] at this
    simp only [Matrix.toBlocks₂₂, C, Matrix.submatrix_apply, Matrix.of_apply, A,
      Matrix.smul_apply, smul_eq_mul, Q]
    split_ifs
    simp only [M, mixedCarryBlocksExpMatrix, Matrix.of_apply, e, Equiv.coe_fn_mk, z]
    rw [carryBlocks_zero_left b hb, pow_zero]
    have hgeom := geom_sum_mul (X + 1 : R[X]) (carryBlocks b k (i.val + 1) (j.val + 1))
    rw [add_sub_cancel_right] at hgeom
    rw [mul_comm, hgeom]
  have hsplit : C.det = (Matrix.toBlocks₁₁ C).det * (Matrix.toBlocks₂₂ C).det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
    rw [hbl, Matrix.det_fromBlocks_zero₂₁]
  rw [hsplit, h11, one_mul, h22, Matrix.det_smul, Fintype.card_fin] at hM_det
  have hcoeff := congrArg (fun p : R[X] => p.coeff (n - 1)) hM_det
  have hlhs : ((X : R[X]) ^ (n - 1) * Q.det).coeff (n - 1) = Q.det.coeff 0 := by
    simpa using Polynomial.coeff_X_pow_mul Q.det (n - 1) 0
  rw [hlhs] at hcoeff
  have hrhs : ((-1 : R[X]) ^ ((n - 1).choose 2) * X ^ (n - 1)).coeff (n - 1) =
      (-1 : R) ^ ((n - 1).choose 2) := by
    have hneg : (-1 : R[X]) ^ ((n - 1).choose 2) = Polynomial.C ((-1 : R) ^ ((n - 1).choose 2)) := by
      rw [map_pow, map_neg, map_one]
    rw [hneg, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  rw [hrhs] at hcoeff
  -- Evaluate `Q.det` at `0`: `Q.det.eval 0 = Q.det.coeff 0 = (Q.map (eval 0)).det`.
  have heval : Q.det.eval 0 = (mixedCarryBlocksMatrix b k (R := R)).det := by
    have hmap := RingHom.map_det (Polynomial.evalRingHom (0 : R)) Q
    simp only [Polynomial.coe_evalRingHom] at hmap
    rw [hmap]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Q, Matrix.of_apply,
      Polynomial.coe_evalRingHom, mixedCarryBlocksMatrix]
    rw [Polynomial.eval_finsetSum]
    simp [Finset.sum_const]
  rw [Polynomial.coeff_zero_eq_eval_zero] at hcoeff
  exact heval.symm.trans hcoeff

section BinaryAndGray

lemma place_two : ∀ k, place (fun _ => 2) k = 2 ^ k
  | 0 => rfl
  | k + 1 => by simp [place, place_two k, pow_succ]

lemma xor_mod_two (a b : ℕ) : (a ^^^ b) % 2 = if a % 2 = b % 2 then 0 else 1 := by
  have h0 : (a ^^^ b).testBit 0 = (a.testBit 0 != b.testBit 0) := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h0
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  have hab := Nat.mod_two_eq_zero_or_one (a ^^^ b)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;>
    simp [ha, hb, hab] at h0 ⊢

lemma xor_div_two (a b : ℕ) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_div_two,
    Nat.testBit_xor]

/-- Binary carry word `(x + y) ^^^ x ^^^ y`. -/
private def binCarryWord (x y : ℕ) : ℕ := (x + y) ^^^ x ^^^ y

/-- Number of maximal `1`-runs in a binary word `n`. -/
private def binBlocks : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if (n + 1) % 2 = 1 ∧ ((n + 1) / 2) % 2 = 0 then 1 else 0) + binBlocks ((n + 1) / 2)
termination_by n => n

private lemma popcnt_step (n : ℕ) : popcnt n = n % 2 + popcnt (n / 2) := by
  cases n with
  | zero => simp [popcnt]
  | succ m => rw [popcnt]

private lemma binBlocks_step (n : ℕ) :
    binBlocks n = (if n % 2 = 1 ∧ (n / 2) % 2 = 0 then 1 else 0) + binBlocks (n / 2) := by
  cases n with
  | zero => simp [binBlocks]
  | succ m => rw [binBlocks]

private lemma popcnt_gray_eq_two_mul_blocks :
    ∀ n : ℕ, popcnt (gray n) = 2 * binBlocks n - n % 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [gray, popcnt, binBlocks]
    | succ m =>
      set k := m + 1
      have hlt : k / 2 < k := Nat.div_lt_self (by omega) (by decide)
      have hih := ih (k / 2) hlt
      rw [gray, popcnt_step, xor_mod_two, xor_div_two, ← gray, hih]
      conv_rhs => rw [binBlocks_step]
      have hkm := Nat.mod_two_eq_zero_or_one k
      have hk2m := Nat.mod_two_eq_zero_or_one (k / 2)
      have hle : (k / 2) % 2 ≤ 2 * binBlocks (k / 2) := by
        rcases hk2m with h0 | h1
        · omega
        · have hpos : 0 < binBlocks (k / 2) := by
            have : ∀ t, 0 < t → 0 < binBlocks t := by
              intro t
              induction t using Nat.strong_induction_on with
              | h t iht =>
                intro ht
                rw [binBlocks_step]
                by_cases h1 : t % 2 = 1 ∧ (t / 2) % 2 = 0
                · simp [h1]
                · have ht2 : 0 < t / 2 := by omega
                  have := iht (t / 2) (Nat.div_lt_self ht (by decide)) ht2
                  omega
            exact this (k / 2) (by omega)
          omega
      rcases hkm with hk0 | hk1 <;> rcases hk2m with h20 | h21 <;>
        (try simp [hk0, h20]) <;> (try simp [hk0, h21]) <;>
        (try simp [hk1, h20]) <;> (try simp [hk1, h21]) <;> omega

private lemma gray_add_xor (x y : ℕ) :
    gray (x + y) ^^^ gray x ^^^ gray y = gray (binCarryWord x y) := by
  simp only [gray, binCarryWord]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_div_two]
  cases ((x + y).testBit i) <;> cases (x.testBit i) <;> cases (y.testBit i) <;>
    cases ((x + y).testBit (i + 1)) <;> cases (x.testBit (i + 1)) <;> cases (y.testBit (i + 1)) <;>
    rfl

private lemma binCarryWord_mod_two (x y : ℕ) : binCarryWord x y % 2 = 0 := by
  simp only [binCarryWord, xor_mod_two]
  have hx := Nat.mod_two_eq_zero_or_one x
  have hy := Nat.mod_two_eq_zero_or_one y
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [Nat.add_mod, hx, hy]

private lemma binCarryWord_testBit_succ (x y r : ℕ) :
    (binCarryWord x y).testBit (r + 1) = decide (carryBit (fun _ => 2) r x y = 1) := by
  simp only [binCarryWord, carryBit, place_two, Nat.testBit_xor]
  have hdiv : ∀ n : ℕ, n.testBit (r + 1) = decide ((n / 2 ^ (r + 1)) % 2 = 1) := fun n => by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod]
    have h01 := Nat.mod_two_eq_zero_or_one (n / 2 ^ (r + 1))
    rcases h01 with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [hdiv (x + y), hdiv x, hdiv y]
  have hq : (x + y) / 2 ^ (r + 1) =
      x / 2 ^ (r + 1) + y / 2 ^ (r + 1) +
        if 2 ^ (r + 1) ≤ x % 2 ^ (r + 1) + y % 2 ^ (r + 1) then 1 else 0 := by
    have hpos : 0 < 2 ^ (r + 1) := by positivity
    have hx := Nat.div_add_mod x (2 ^ (r + 1))
    have hy := Nat.div_add_mod y (2 ^ (r + 1))
    have hxm : x % 2 ^ (r + 1) < 2 ^ (r + 1) := Nat.mod_lt x hpos
    have hym : y % 2 ^ (r + 1) < 2 ^ (r + 1) := Nat.mod_lt y hpos
    by_cases hc : 2 ^ (r + 1) ≤ x % 2 ^ (r + 1) + y % 2 ^ (r + 1)
    · simp only [hc, ↓reduceIte]
      have hrem_lt : x % 2 ^ (r + 1) + y % 2 ^ (r + 1) - 2 ^ (r + 1) < 2 ^ (r + 1) := by omega
      have hsum : x + y =
          2 ^ (r + 1) * (x / 2 ^ (r + 1) + y / 2 ^ (r + 1) + 1) +
            (x % 2 ^ (r + 1) + y % 2 ^ (r + 1) - 2 ^ (r + 1)) := by
        have hsub : 2 ^ (r + 1) + (x % 2 ^ (r + 1) + y % 2 ^ (r + 1) - 2 ^ (r + 1)) =
            x % 2 ^ (r + 1) + y % 2 ^ (r + 1) := by omega
        linarith
      rw [hsum, Nat.mul_add_div hpos, Nat.div_eq_of_lt hrem_lt, add_zero]
    · simp only [hc, ↓reduceIte, add_zero]
      have hrem_lt : x % 2 ^ (r + 1) + y % 2 ^ (r + 1) < 2 ^ (r + 1) := by omega
      have hsum : x + y =
          2 ^ (r + 1) * (x / 2 ^ (r + 1) + y / 2 ^ (r + 1)) +
            (x % 2 ^ (r + 1) + y % 2 ^ (r + 1)) := by
        linarith
      rw [hsum, Nat.mul_add_div hpos, Nat.div_eq_of_lt hrem_lt, add_zero]
  rw [hq]
  have ha := Nat.mod_two_eq_zero_or_one (x / 2 ^ (r + 1))
  have hb := Nat.mod_two_eq_zero_or_one (y / 2 ^ (r + 1))
  by_cases hc : 2 ^ (r + 1) ≤ x % 2 ^ (r + 1) + y % 2 ^ (r + 1)
  · simp only [hc, ↓reduceIte]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [Nat.add_mod, ha, hb]
  · simp only [hc, ↓reduceIte, add_zero]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [Nat.add_mod, ha, hb]

private lemma binBlocks_eq_sum_starts (n k : ℕ) (hn : n < 2 ^ (k + 1)) (h0 : n % 2 = 0) :
    binBlocks n = ∑ r ∈ Finset.range k,
      if n.testBit (r + 1) = true ∧ n.testBit r = false then 1 else 0 := by
  -- `binBlocks n` counts `1 -> 0` transitions `(testBit r = true ∧ testBit (r+1) = false)`, while
  -- `carryBlocks` counts `0 -> 1` transitions; both equal the number of maximal `1`-runs.
  -- Prove directly by induction on `k`: for any `m < 2^k` and any `b0 : Bool`,
  -- `binBlocks (2 * m + b0.toNat) = ...`.
  suffices hgen : ∀ k m : ℕ, m < 2 ^ k →
      (∑ r ∈ Finset.range k,
        if m.testBit r = true ∧ (r = 0 ∨ m.testBit (r - 1) = false) then 1 else 0) = binBlocks m by
    have hm : n / 2 < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [pow_succ] using hn
    have hbin : binBlocks n = binBlocks (n / 2) := by
      rw [binBlocks_step, h0]; simp
    rw [hbin, ← hgen k (n / 2) hm]
    apply Finset.sum_congr rfl
    intro r _
    have htb : ∀ t : ℕ, (n / 2).testBit t = n.testBit (t + 1) := fun t => Nat.testBit_div_two n t
    cases r with
    | zero =>
        have htb0 : n.testBit 0 = false := by simp [Nat.testBit_zero, h0]
        simp [htb 0, htb0]
    | succ r' =>
        simp [htb (r' + 1), htb r']
  intro k
  induction k with
  | zero =>
      intro m hm
      have : m = 0 := by omega
      subst this
      simp [binBlocks]
  | succ k ih =>
      intro m hm
      -- Compare `0 -> 1` transitions with `1 -> 0` transitions on `(m.testBit 0, ..., m.testBit k)`:
      -- Prove the stronger identity on `Finset.range (k + 1)`:
      -- `(# of 0->1 transitions in 0..k) = (# of 1->0 transitions in 0..k)`!
      -- Use `m % 2` and `m / 2`!
      have hm2 : m / 2 < 2 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        simpa [pow_succ] using hm
      have hih := ih (m / 2) hm2
      rw [Finset.sum_range_succ']
      have htb : ∀ t : ℕ, m.testBit (t + 1) = (m / 2).testBit t := fun t => (Nat.testBit_div_two m t).symm
      have hshift :
          (∑ r ∈ Finset.range k,
            if m.testBit (r + 1) = true ∧ (r + 1 = 0 ∨ m.testBit r = false) then 1 else 0) +
          (if m.testBit 0 = true then 1 else 0) =
          (∑ r ∈ Finset.range k,
            if (m / 2).testBit r = true ∧ (r = 0 ∨ (m / 2).testBit (r - 1) = false) then 1 else 0) +
            (if m % 2 = 1 ∧ (m / 2) % 2 = 0 then 1 else 0) := by
        cases k with
        | zero =>
            have hlt2 : m < 2 := by simpa using hm
            have hm2_0 : m / 2 = 0 := by omega
            have h01 := Nat.mod_two_eq_zero_or_one m
            rcases h01 with h0 | h1
            · simp [Nat.testBit_zero, h0, hm2_0]
            · simp [Nat.testBit_zero, h1, hm2_0]
        | succ k' =>
            rw [Finset.sum_range_succ', Finset.sum_range_succ']
            have hrest :
                (∑ r ∈ Finset.range k',
                  if m.testBit (r + 1 + 1) = true ∧ (r + 1 + 1 = 0 ∨ m.testBit (r + 1) = false)
                  then 1 else 0) =
                (∑ r ∈ Finset.range k',
                  if (m / 2).testBit (r + 1) = true ∧ (r + 1 = 0 ∨ (m / 2).testBit r = false)
                  then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro r _
              simp [htb (r + 1), htb r]
            rw [hrest]
            have h01 := Nat.mod_two_eq_zero_or_one m
            have h21 := Nat.mod_two_eq_zero_or_one (m / 2)
            have ht0 : m.testBit 0 = decide (m % 2 = 1) := by simp [Nat.testBit_zero]
            have ht1 : m.testBit 1 = decide ((m / 2) % 2 = 1) := by
              rw [htb 0]; simp [Nat.testBit_zero]
            have ht20 : (m / 2).testBit 0 = decide ((m / 2) % 2 = 1) := by simp [Nat.testBit_zero]
            rcases h01 with h0 | h1 <;> rcases h21 with h20 | h21
            · simp [ht0, ht1, ht20, h0, h20]
            · simp [ht0, ht1, ht20, h0, h21]
            · simp [ht0, ht1, ht20, h1, h20]
            · simp [ht0, ht1, ht20, h1, h21]
      simp only [Nat.add_sub_cancel, true_or, and_true]
      rw [hshift, hih, add_comm, ← binBlocks_step]

lemma popcnt_gray_eq_two_mul_carryBlocks {k i j : ℕ} (hi : i < 2 ^ k) (hj : j < 2 ^ k) :
    popcnt (gray (i + j) ^^^ gray i ^^^ gray j) = 2 * carryBlocks (fun _ => 2) k i j := by
  rw [gray_add_xor, popcnt_gray_eq_two_mul_blocks, binCarryWord_mod_two, Nat.sub_zero]
  congr 1
  have hcw_lt : binCarryWord i j < 2 ^ (k + 1) := by
    simp only [binCarryWord]
    apply Nat.xor_lt_two_pow
    · apply Nat.xor_lt_two_pow
      · rw [pow_succ]; omega
      · exact lt_trans hi (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k))
    · exact lt_trans hj (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k))
  rw [binBlocks_eq_sum_starts (binCarryWord i j) k hcw_lt (binCarryWord_mod_two i j)]
  -- Show `carryBlocks (fun _ => 2) k i j` equals the same sum!
  suffices hsum : ∀ m : ℕ, carryBlocks (fun _ => 2) m i j =
      ∑ r ∈ Finset.range m,
        if (binCarryWord i j).testBit (r + 1) = true ∧ (binCarryWord i j).testBit r = false
        then 1 else 0 by
    exact (hsum k).symm
  intro m
  induction m with
  | zero => simp [carryBlocks]
  | succ m ihm =>
      rw [carryBlocks, Finset.sum_range_succ, ihm]
      congr 1
      rw [binCarryWord_testBit_succ i j m]
      cases m with
      | zero =>
          have hb0 : (binCarryWord i j).testBit 0 = false := by
            simp [Nat.testBit_zero, binCarryWord_mod_two]
          simp [hb0]
      | succ m' =>
          simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, false_or]
          rw [binCarryWord_testBit_succ i j m']
          have h01 : carryBit (fun _ => 2) m' i j = 0 ∨ carryBit (fun _ => 2) m' i j = 1 := by
            simp only [carryBit]; split_ifs <;> simp
          rcases h01 with h0 | h1
          · simp [h0]
          · simp [h1]

/-- **Binary Carry-Blocks Unimodularity (`b = fun _ => 2`).** -/
theorem det_binaryCarryBlocks {R : Type*} [CommRing R] (k : ℕ) :
    (mixedCarryBlocksMatrix (fun _ => 2) k (R := R)).det =
      (-1 : R) ^ ((2 ^ k - 1).choose 2) := by
  simpa [place_two] using det_mixedCarryBlocks_linear (R := R) (fun _ => 2) (fun _ => by decide) k

/-- **Binary Gray-Code Carry-Transition Determinant Theorem.**
For every `k : ℕ` and any commutative ring `R`,
`det (popcnt (gray (i + j) ^^^ gray i ^^^ gray j))_{1 ≤ i, j < 2^k} = (-1)^((2^k - 1).choose 2) * 2^(2^k - 1)`. -/
theorem det_grayCarryTransitions {R : Type*} [CommRing R] (k : ℕ) :
    (grayCarryTransitionMatrix (R := R) k).det =
      (-1 : R) ^ ((2 ^ k - 1).choose 2) * (2 : R) ^ (2 ^ k - 1) := by
  let e : Fin (2 ^ k - 1) ≃ Fin (place (fun _ => 2) k - 1) :=
    Fin.castOrderIso (by rw [place_two]) |>.toEquiv
  have hmat : grayCarryTransitionMatrix (R := R) k =
      (2 : R) • ((mixedCarryBlocksMatrix (fun _ => 2) k (R := R)).submatrix e e) := by
    ext i j
    simp only [grayCarryTransitionMatrix, Matrix.smul_apply, Matrix.submatrix_apply,
      mixedCarryBlocksMatrix, Matrix.of_apply, smul_eq_mul]
    have hi : i.val + 1 < 2 ^ k := by omega
    have hj : j.val + 1 < 2 ^ k := by omega
    have hval := popcnt_gray_eq_two_mul_carryBlocks hi hj
    rw [hval]
    have he1 : (e i).val = i.val := rfl
    have he2 : (e j).val = j.val := rfl
    rw [he1, he2]
    push_cast
    rfl
  rw [hmat, Matrix.det_smul, Fintype.card_fin,
    show ((mixedCarryBlocksMatrix (fun _ => 2) k (R := R)).submatrix e e).det =
      (Matrix.reindex e.symm e.symm (mixedCarryBlocksMatrix (fun _ => 2) k (R := R))).det from rfl,
    Matrix.det_reindex_self, det_binaryCarryBlocks, mul_comm]

end BinaryAndGray

end CarryBlocksDeterminants

