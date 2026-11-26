/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryBlocksDeterminants.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Plateau Hankel Determinants and Mixed-Radix Digit-Length Determinants

Proves the two universal plateau Hankel determinant formulas over any commutative ring `R`:
- `det_plateauHankel_one`: for any `N ≥ 2` and any `f : ℕ → R` with `f (N - 1) = a` and
  `f n = a + d` on `[N, 2N - 2]`, the 1-based `(N - 1) × (N - 1)` Hankel determinant is
  `(-1) ^ (N - 1).choose 2 * d ^ (N - 2) * (a + d)` (completely independent of `f(2)..f(N-2)`).
- `det_plateauHankel_zero`: for any `1 ≤ M`, `2 * M ≤ N`, and any `f : ℕ → R` with `f n = a` on
  `[M, N)` and `f n = a + d` on `[N, 2N - 2]`, the 0-based `N × N` Hankel determinant is
  `(-1) ^ (N - 1).choose 2 * d ^ (N - 2) * (f 0 * (a + d) - a ^ 2)` (completely independent of
  `f(1)..f(M-1)`).
- Immediate corollaries `det_mixedDigitLen_one` and `det_mixedDigitLen_zero` for the mixed-radix
  digit-length function `mlen b k`.
-/

namespace CarryBlocksDeterminants

open Matrix Finset

section AntiTriangular

/-- Determinant of an anti-upper-triangular `n × n` matrix with constant anti-diagonal `c`. -/
lemma det_of_antiUpperTriangular {R : Type*} [CommRing R] :
    ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c : R),
      (∀ i j : Fin n, n - 1 < i.val + j.val → M i j = 0) →
      (∀ i j : Fin n, i.val + j.val = n - 1 → M i j = c) →
      M.det = (-1 : R) ^ (n.choose 2) * c ^ n
  | 0, M, c, _, _ => by
      simp
  | n + 1, M, c, hzero, hdiag => by
      rw [Matrix.det_succ_row M (Fin.last n)]
      have hterm : ∀ j : Fin (n + 1), j ≠ 0 →
          (-1 : R) ^ ((Fin.last n : Fin (n + 1)).val + j.val) * M (Fin.last n) j *
            (M.submatrix (Fin.last n).succAbove j.succAbove).det = 0 := by
        intro j hj
        have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
        have hM : M (Fin.last n) j = 0 := hzero (Fin.last n) j (by simp only [Fin.val_last]; omega)
        simp [hM]
      rw [Finset.sum_eq_single 0 (fun j _ hj => hterm j hj) (by simp)]
      have h0 : M (Fin.last n) 0 = c := hdiag (Fin.last n) 0 (by simp)
      have hsub : (M.submatrix (Fin.last n).succAbove (0 : Fin (n + 1)).succAbove).det =
          (-1 : R) ^ (n.choose 2) * c ^ n := by
        apply det_of_antiUpperTriangular _ c
        · intro i j hij
          apply hzero
          simp [Fin.succAbove_last]
          omega
        · intro i j hij
          apply hdiag
          simp [Fin.succAbove_last]
          omega
      rw [h0, hsub]
      simp only [Fin.val_last, Fin.val_zero, add_zero]
      have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      rw [hchoose, pow_add, pow_succ]
      ring

/-- Upper-triangular `n × n` matrix with constant diagonal `c` has determinant `c ^ n`. -/
lemma det_of_upperTriangular_const {R : Type*} [CommRing R] :
    ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c : R),
      (∀ i j : Fin n, j.val < i.val → M i j = 0) →
      (∀ i : Fin n, M i i = c) →
      M.det = c ^ n
  | 0, M, c, _, _ => by simp
  | n + 1, M, c, hzero, hdiag => by
      rw [Matrix.det_succ_column_zero]
      have hterm : ∀ i : Fin (n + 1), i ≠ 0 →
          (-1 : R) ^ (i.val : ℕ) * M i 0 * (M.submatrix i.succAbove Fin.succ).det = 0 := by
        intro i hi
        have hipos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
        have hM : M i 0 = 0 := hzero i 0 hipos
        simp [hM]
      rw [Finset.sum_eq_single 0 (fun i _ hi => hterm i hi) (by simp)]
      have h0 : M 0 0 = c := hdiag 0
      have hsub : (M.submatrix (0 : Fin (n + 1)).succAbove Fin.succ).det = c ^ n := by
        apply det_of_upperTriangular_const _ c
        · intro i j hij
          apply hzero
          simp
          exact hij
        · intro i
          simpa using hdiag i.succ
      rw [h0, hsub]
      simp [pow_succ, mul_comm]

/-- Adding a scalar multiple of a fixed row `r` to all rows `i ≠ r` preserves `det`. -/
lemma det_sub_fixed_row {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (r : n) (p : n → Prop) [DecidablePred p] (hr : ¬ p r) :
    (Matrix.of fun i j => if p i then M i j - M r j else M i j).det = M.det := by
  let L : Matrix n n R := Matrix.of fun i k =>
    (if i = k then (1 : R) else 0) + (if p i ∧ k = r then (-1 : R) else 0)
  have hmul : L * M = Matrix.of fun i j => if p i then M i j - M r j else M i j := by
    ext i j
    simp only [Matrix.mul_apply, L, Matrix.of_apply, add_mul]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ k : n, (if i = k then (1 : R) else 0) * M k j = M i j := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [Ne.symm hki]
      · simp
    have h2 : ∑ k : n, (if p i ∧ k = r then (-1 : R) else 0) * M k j =
        if p i then -M r j else 0 := by
      by_cases hpi : p i
      · rw [Finset.sum_eq_single r]
        · simp [hpi]
        · intro k _ hkr
          simp [hkr]
        · simp
      · simp [hpi]
    rw [h1, h2]
    by_cases hpi : p i <;> simp [hpi, sub_eq_add_neg]
  rw [← hmul, Matrix.det_mul]
  suffices hL : L.det = 1 by rw [hL, one_mul]
  rw [Matrix.det_apply]
  have hterm : ∀ σ : Equiv.Perm n, σ ≠ 1 →
      Equiv.Perm.sign σ • ∏ i : n, L (σ i) i = 0 := by
    intro σ hσ
    suffices hprod : ∏ i : n, L (σ i) i = 0 by simp [hprod]
    by_contra hne
    have hall : ∀ i : n, L (σ i) i ≠ 0 := by
      intro i hi
      exact hne (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hstep : ∀ i : n, σ i = i ∨ (i = r ∧ p (σ i)) := by
      intro i
      have hi := hall i
      dsimp only [L, Matrix.of_apply] at hi
      by_cases heq : σ i = i
      · exact Or.inl heq
      · right
        by_contra hnot
        have : (if σ i = i then (1 : R) else 0) + (if p (σ i) ∧ i = r then (-1 : R) else 0) = 0 := by
          have h2 : ¬ (p (σ i) ∧ i = r) := fun h => hnot ⟨h.2, h.1⟩
          simp [heq, h2]
        exact hi this
    have hfix_ne : ∀ i : n, i ≠ r → σ i = i := by
      intro i hir
      rcases hstep i with h | ⟨h, _⟩
      · exact h
      · exact absurd h hir
    have hfix_r : σ r = r := by
      by_contra hne_r
      have h1 : σ (σ r) = σ r := hfix_ne (σ r) hne_r
      exact hne_r (σ.injective h1)
    apply hσ
    ext i
    by_cases hi : i = r
    · subst hi; exact hfix_r
    · exact hfix_ne i hi
  rw [Finset.sum_eq_single 1 (fun σ _ hσ => hterm σ hσ) (by simp)]
  simp only [map_one, one_smul]
  apply Finset.prod_eq_one
  intro i _
  dsimp only [L, Matrix.of_apply]
  have : ¬ (p i ∧ i = r) := by
    rintro ⟨hp, rfl⟩
    exact hr hp
  simp [this]

/-- Subtracting column `c` from all columns `j` satisfying `p j` (with `¬ p c`) preserves `det`. -/
lemma det_sub_fixed_col {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (c : n) (p : n → Prop) [DecidablePred p] (hc : ¬ p c) :
    (Matrix.of fun i j => if p j then M i j - M i c else M i j).det = M.det := by
  have h := det_sub_fixed_row Mᵀ c p hc
  rw [Matrix.det_transpose] at h
  rw [← h, ← Matrix.det_transpose]
  congr 1

/-- Sign of `Fin.revPerm` as an element of `ℤ`. -/
lemma sign_fin_revPerm (n : ℕ) :
    (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) = (-1 : ℤ) ^ (n.choose 2) := by
  let M : Matrix (Fin n) (Fin n) ℤ := (1 : Matrix (Fin n) (Fin n) ℤ).submatrix id Fin.revPerm
  have h1 : M.det = (Equiv.Perm.sign (Fin.revPerm (n := n)) : ℤ) := by
    change ((1 : Matrix (Fin n) (Fin n) ℤ).submatrix id Fin.revPerm).det = _
    rw [Matrix.det_permute', Matrix.det_one, mul_one]
    simp
  have h2 : M.det = (-1 : ℤ) ^ (n.choose 2) * (1 : ℤ) ^ n := by
    apply det_of_antiUpperTriangular M 1
    · intro i j hij
      simp only [M, Matrix.submatrix_apply, id_eq, Matrix.one_apply, Fin.revPerm_apply]
      have hne : i ≠ j.rev := by
        intro heq
        have hv := congrArg Fin.val heq
        simp [Fin.val_rev] at hv
        omega
      simp [hne]
    · intro i j hij
      simp only [M, Matrix.submatrix_apply, id_eq, Matrix.one_apply, Fin.revPerm_apply]
      have heq : i = j.rev := by
        ext
        simp [Fin.val_rev]
        omega
      simp [heq]
  rw [one_pow, mul_one] at h2
  exact h1.symm.trans h2

end AntiTriangular

/-- Universal 1-based plateau Hankel determinant theorem: for any `N ≥ 2` and any `f : ℕ → R`
with `f (N - 1) = a` and `f n = a + d` for `N ≤ n ≤ 2 * N - 2`, the `(N - 1) × (N - 1)` Hankel
determinant is `(-1) ^ (N - 1).choose 2 * d ^ (N - 2) * (a + d)`, completely independent of
`f 0, f 1, ..., f (N - 2)`. -/
theorem det_plateauHankel_one {R : Type*} [CommRing R] {N : ℕ} (hN : 2 ≤ N)
    (f : ℕ → R) (a d : R)
    (hmid : f (N - 1) = a)
    (hhi : ∀ n, N ≤ n → n ≤ 2 * N - 2 → f n = a + d) :
    (hankelOneMatrix N f).det = (-1 : R) ^ ((N - 1).choose 2) * d ^ (N - 2) * (a + d) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) R := hankelOneMatrix (m + 2) f
  change M.det = (-1 : R) ^ ((m + 1).choose 2) * d ^ m * (a + d)
  let r : Fin (m + 1) := Fin.last m
  have hstep := det_sub_fixed_row M r (fun i => i ≠ r) (by simp)
  rw [← hstep]
  set A : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of fun i j => if i ≠ r then M i j - M r j else M i j
  rw [Matrix.det_succ_column A (Fin.last m)]
  have hcol_zero : ∀ i : Fin (m + 1), i ≠ Fin.last m →
      (-1 : R) ^ (i.val + (Fin.last m : Fin (m + 1)).val) * A i (Fin.last m) *
        (A.submatrix i.succAbove (Fin.last m).succAbove).det = 0 := by
    intro i hi
    have hA : A i (Fin.last m) = 0 := by
      simp only [A, Matrix.of_apply, r, hi, ne_eq, not_false_eq_true, ↓reduceIte,
        M, hankelOneMatrix, Fin.val_last]
      rw [hhi (i.val + m + 2) (by omega) (by omega), hhi (m + m + 2) (by omega) (by omega),
        sub_self]
    simp [hA]
  rw [Finset.sum_eq_single (Fin.last m) (fun i _ hi => hcol_zero i hi) (by simp)]
  have hcorner : A (Fin.last m) (Fin.last m) = a + d := by
    simp only [A, Matrix.of_apply, r, ne_eq, not_true_eq_false, ↓reduceIte,
      M, hankelOneMatrix, Fin.val_last]
    exact hhi (m + m + 2) (by omega) (by omega)
  have hminor : (A.submatrix (Fin.last m).succAbove (Fin.last m).succAbove).det =
      (-1 : R) ^ (m.choose 2) * (-d) ^ m := by
    apply det_of_antiUpperTriangular _ (-d)
    · intro i j hij
      simp only [Matrix.submatrix_apply, A, Matrix.of_apply, Fin.succAbove_last, r,
        Fin.castSucc_ne_last, ne_eq, not_false_eq_true, ↓reduceIte, M, hankelOneMatrix,
        Fin.val_castSucc, Fin.val_last]
      rw [hhi (i.val + j.val + 2) (by omega) (by omega), hhi (m + j.val + 2) (by omega) (by omega),
        sub_self]
    · intro i j hij
      simp only [Matrix.submatrix_apply, A, Matrix.of_apply, Fin.succAbove_last, r,
        Fin.castSucc_ne_last, ne_eq, not_false_eq_true, ↓reduceIte, M, hankelOneMatrix,
        Fin.val_castSucc, Fin.val_last]
      have h1 : i.val + j.val + 2 = m + 1 := by omega
      have hmid' : f (m + 1) = a := by simpa using hmid
      rw [h1, hmid', hhi (m + j.val + 2) (by omega) (by omega)]
      ring
  rw [hcorner, hminor]
  simp only [Fin.val_last]
  have h2m : (-1 : R) ^ (m + m) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  have hneg : (-d) ^ m = (-1 : R) ^ m * d ^ m := by
    rw [neg_eq_neg_one_mul, mul_pow]
  have hchoose : (m + 1).choose 2 = m.choose 2 + m := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
  rw [h2m, one_mul, hneg, hchoose, pow_add]
  ring

section PlateauZeroHelpers

/-- Inner column reversal on `Fin (m + 2)`: fixes `0` and `m + 1`, reverses `1..m`. -/
def innerRevPerm (m : ℕ) : Equiv.Perm (Fin (m + 2)) where
  toFun x :=
    if h0 : x.val = 0 then x
    else if h1 : x.val = m + 1 then x
    else ⟨m + 1 - x.val, by omega⟩
  invFun x :=
    if h0 : x.val = 0 then x
    else if h1 : x.val = m + 1 then x
    else ⟨m + 1 - x.val, by omega⟩
  left_inv x := by
    by_cases h0 : x.val = 0
    · simp [h0]
    · by_cases h1 : x.val = m + 1
      · simp [h1]
      · have h0' : m + 1 - x.val ≠ 0 := by omega
        have h1' : m + 1 - x.val ≠ m + 1 := by omega
        ext
        simp [h0, h1, h0', h1']
        omega
  right_inv x := by
    by_cases h0 : x.val = 0
    · simp [h0]
    · by_cases h1 : x.val = m + 1
      · simp [h1]
      · have h0' : m + 1 - x.val ≠ 0 := by omega
        have h1' : m + 1 - x.val ≠ m + 1 := by omega
        ext
        simp [h0, h1, h0', h1']
        omega

/-- Sign of `innerRevPerm m` equals `(-1) ^ (m.choose 2)`. -/
lemma sign_innerRevPerm (m : ℕ) :
    (Equiv.Perm.sign (innerRevPerm m) : ℤ) = (-1 : ℤ) ^ (m.choose 2) := by
  let e : Fin m ⊕ Fin 2 ≃ Fin (m + 2) := {
    toFun := fun
      | Sum.inl i => ⟨i.val + 1, by omega⟩
      | Sum.inr j => if j.val = 0 then ⟨0, by omega⟩ else ⟨m + 1, by omega⟩
    invFun := fun x =>
      if h0 : x.val = 0 then Sum.inr ⟨0, by decide⟩
      else if h1 : x.val = m + 1 then Sum.inr ⟨1, by decide⟩
      else Sum.inl ⟨x.val - 1, by omega⟩
    left_inv := by
      rintro (i | j)
      · dsimp only
        have h1 : ¬ (i.val + 1 = 0) := by omega
        have h2 : ¬ (i.val + 1 = m + 1) := by omega
        simp only [h1, h2, ↓reduceDIte]
        congr 1
      · fin_cases j
        · simp
        · dsimp only
          have h1 : ¬ (m + 1 = 0) := by omega
          have h2 : ¬ ((⟨1, by decide⟩ : Fin 2).val = 0) := by decide
          simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
    right_inv := by
      intro x
      dsimp only
      by_cases h0 : x.val = 0
      · simp only [h0, ↓reduceDIte]; ext; simp [h0]
      · by_cases h1 : x.val = m + 1
        · have hne : ¬ (m + 1 = 0) := by omega
          simp only [h1, hne, ↓reduceDIte]; ext; simp [h1]
        · simp only [h0, h1, ↓reduceDIte]; ext; dsimp only; omega
  }
  have hconj : innerRevPerm m = e.permCongr (Equiv.Perm.sumCongr (Fin.revPerm (n := m)) 1) := by
    ext x
    simp only [Equiv.permCongr_apply, Equiv.Perm.sumCongr_apply, innerRevPerm, e,
      Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    by_cases h0 : x.val = 0
    · simp only [h0, ↓reduceDIte, Sum.map_inr, Equiv.Perm.one_apply, ↓reduceIte]
    · by_cases h1 : x.val = m + 1
      · have hne : ¬ (m + 1 = 0) := by omega
        simp only [h1, hne, ↓reduceDIte, Sum.map_inr, Equiv.Perm.one_apply]
        have h10 : ¬ ((⟨1, by decide⟩ : Fin 2).val = 0) := by decide
        simp [h10]
      · simp only [h0, h1, ↓reduceDIte, Sum.map_inl, Fin.revPerm_apply, Fin.val_rev]
        omega
  rw [hconj, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, map_one, mul_one]
  exact sign_fin_revPerm m

/-- Block split `((Fin (M - 1) ⊕ Fin 2) ⊕ Fin (N - 1 - M)) ≃ Fin N` ordering indices as
`[1..M-1, 0, N-1, M..N-2]`. -/
def plateauBlockEquiv {M N : ℕ} (hM : 1 ≤ M) (hMN : 2 * M ≤ N) :
    ((Fin (M - 1) ⊕ Fin 2) ⊕ Fin (N - 1 - M)) ≃ Fin N where
  toFun
    | Sum.inl (Sum.inl i) => ⟨i.val + 1, by omega⟩
    | Sum.inl (Sum.inr j) => if j.val = 0 then ⟨0, by omega⟩ else ⟨N - 1, by omega⟩
    | Sum.inr k => ⟨M + k.val, by omega⟩
  invFun x :=
    if h0 : x.val = 0 then Sum.inl (Sum.inr ⟨0, by decide⟩)
    else if h1 : x.val = N - 1 then Sum.inl (Sum.inr ⟨1, by decide⟩)
    else if h2 : x.val < M then Sum.inl (Sum.inl ⟨x.val - 1, by omega⟩)
    else Sum.inr ⟨x.val - M, by omega⟩
  left_inv := by
    rintro ((i | j) | k)
    · dsimp only
      have h1 : ¬ (i.val + 1 = 0) := by omega
      have h2 : ¬ (i.val + 1 = N - 1) := by omega
      have h3 : i.val + 1 < M := by omega
      simp only [h1, h2, h3, ↓reduceDIte]
      congr 2
    · fin_cases j
      · simp
      · dsimp only
        have h1 : ¬ (N - 1 = 0) := by omega
        have h2 : ¬ ((⟨1, by decide⟩ : Fin 2).val = 0) := by decide
        simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
    · dsimp only
      have h1 : ¬ (M + k.val = 0) := by omega
      have h2 : ¬ (M + k.val = N - 1) := by omega
      have h3 : ¬ (M + k.val < M) := by omega
      simp only [h1, h2, h3, ↓reduceDIte]
      congr 1; ext; simp
  right_inv x := by
    dsimp only
    by_cases h0 : x.val = 0
    · simp only [h0, ↓reduceDIte]; ext; simp [h0]
    · by_cases h1 : x.val = N - 1
      · have hne : ¬ (N - 1 = 0) := by omega
        have h10 : ¬ ((⟨1, by decide⟩ : Fin 2).val = 0) := by decide
        simp only [h1, hne, h10, ↓reduceDIte, ↓reduceIte]; ext; simp [h1]
      · by_cases h2 : x.val < M
        · simp only [h0, h1, h2, ↓reduceDIte]; ext; dsimp only; omega
        · simp only [h0, h1, h2, ↓reduceDIte]; ext; dsimp only; omega

end PlateauZeroHelpers

/-- Universal 0-based plateau Hankel determinant theorem: for any `1 ≤ M`, `2 * M ≤ N`, and any
`f : ℕ → R` with `f n = a` on `[M, N)` and `f n = a + d` on `[N, 2 * N - 2]`, the `N × N` Hankel
determinant is `(-1) ^ (N - 1).choose 2 * d ^ (N - 2) * (f 0 * (a + d) - a ^ 2)`, completely
independent of `f 1, ..., f (M - 1)`. -/
theorem det_plateauHankel_zero {R : Type*} [CommRing R] {M N : ℕ}
    (hM : 1 ≤ M) (hMN : 2 * M ≤ N)
    (f : ℕ → R) (a d : R)
    (hmid : ∀ n, M ≤ n → n < N → f n = a)
    (hhi : ∀ n, N ≤ n → n ≤ 2 * N - 2 → f n = a + d) :
    (hankelZeroMatrix N f).det =
      (-1 : R) ^ ((N - 1).choose 2) * d ^ (N - 2) * (f 0 * (a + d) - a ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
  let H : Matrix (Fin (m + 2)) (Fin (m + 2)) R := hankelZeroMatrix (m + 2) f
  change H.det = (-1 : R) ^ ((m + 1).choose 2) * d ^ m * (f 0 * (a + d) - a ^ 2)
  let lastIdx : Fin (m + 2) := Fin.last (m + 1)
  let isInner : Fin (m + 2) → Prop := fun x => 0 < x.val ∧ x.val < m + 1
  have hnot : ¬ isInner lastIdx := by simp [isInner, lastIdx]
  -- Step 1: subtract row (m + 1) from inner rows, then column (m + 1) from inner columns.
  have hrow := det_sub_fixed_row H lastIdx isInner hnot
  set A1 : Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
    Matrix.of fun i j => if isInner i then H i j - H lastIdx j else H i j
  have hcol := det_sub_fixed_col A1 lastIdx isInner hnot
  set A : Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
    Matrix.of fun i j => if isInner j then A1 i j - A1 i lastIdx else A1 i j
  have hdetA : A.det = H.det := hcol.trans hrow
  -- Explicit formula for entries of A:
  have hA_val : ∀ i j : Fin (m + 2),
      A i j =
        if isInner j then
          (if isInner i then H i j - H lastIdx j - (H i lastIdx - H lastIdx lastIdx)
           else H i j - H i lastIdx)
        else
          (if isInner i then H i j - H lastIdx j else H i j) := by
    intro i j
    simp only [A, A1, Matrix.of_apply]
    split_ifs <;> rfl
  -- Step 2: reverse inner columns via `innerRevPerm m`, obtaining matrix `B`.
  let σ := innerRevPerm m
  let B : Matrix (Fin (m + 2)) (Fin (m + 2)) R := A.submatrix id σ
  have hdetB : B.det = (-1 : R) ^ (m.choose 2) * H.det := by
    change (A.submatrix id σ).det = _
    rw [Matrix.det_permute', hdetA]
    have hs : (Equiv.Perm.sign σ : R) = (-1 : R) ^ (m.choose 2) := by
      have hsz := sign_innerRevPerm m
      have hcast := congrArg (Int.cast (R := R)) hsz
      simpa using hcast
    rw [hs]
  -- Key entry properties of `B`:
  have hσ_inner : ∀ x : Fin (m + 2), isInner x → (σ x).val = m + 1 - x.val := by
    intro x hx
    simp only [σ, innerRevPerm, Equiv.coe_fn_mk]
    have h0 : x.val ≠ 0 := by omega
    have h1 : x.val ≠ m + 1 := by omega
    simp [h0, h1]
  have hσ_inner_isInner : ∀ x : Fin (m + 2), isInner x → isInner (σ x) := by
    intro x hx
    change 0 < (σ x).val ∧ (σ x).val < m + 1
    rw [hσ_inner x hx]
    omega
  have hσ_zero : σ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    ext; simp [σ, innerRevPerm]
  have hσ_last : σ lastIdx = lastIdx := by
    ext; simp [σ, innerRevPerm, lastIdx]
  -- Inner-inner entries of B: upper-triangular with `-d` on diagonal!
  have hB_inner_gt : ∀ i j : Fin (m + 2), isInner i → isInner j → j.val < i.val → B i j = 0 := by
    intro i j hi hj hlt
    simp only [B, Matrix.submatrix_apply, id_eq]
    rw [hA_val i (σ j)]
    have hσj := hσ_inner_isInner j hj
    have hσjv := hσ_inner j hj
    simp only [hi, hσj, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, lastIdx, Fin.val_last]
    rw [hhi (i.val + (σ j).val) (by omega) (by omega),
      hhi (m + 1 + (σ j).val) (by omega) (by omega),
      hhi (i.val + (m + 1)) (by omega) (by omega),
      hhi (m + 1 + (m + 1)) (by omega) (by omega)]
    ring
  have hB_inner_diag : ∀ i : Fin (m + 2), isInner i → B i i = -d := by
    intro i hi
    simp only [B, Matrix.submatrix_apply, id_eq]
    rw [hA_val i (σ i)]
    have hσi := hσ_inner_isInner i hi
    have hσiv := hσ_inner i hi
    simp only [hi, hσi, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, lastIdx, Fin.val_last]
    rw [hmid (i.val + (σ i).val) (by omega) (by omega),
      hhi (m + 1 + (σ i).val) (by omega) (by omega),
      hhi (i.val + (m + 1)) (by omega) (by omega),
      hhi (m + 1 + (m + 1)) (by omega) (by omega)]
    ring
  -- Boundary-inner zeros:
  have hB_zero_ltM : ∀ j : Fin (m + 2), isInner j → j.val < M → B ⟨0, by omega⟩ j = 0 := by
    intro j hj hjM
    simp only [B, Matrix.submatrix_apply, id_eq]
    rw [hA_val ⟨0, by omega⟩ (σ j)]
    have hσj := hσ_inner_isInner j hj
    have hσjv := hσ_inner j hj
    have hn0 : ¬ isInner ⟨0, by omega⟩ := by simp [isInner]
    simp only [hn0, hσj, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, lastIdx, Fin.val_last]
    rw [hmid (0 + (σ j).val) (by omega) (by omega), hmid (0 + (m + 1)) (by omega) (by omega),
      sub_self]
  have hB_last_inner : ∀ j : Fin (m + 2), isInner j → B lastIdx j = 0 := by
    intro j hj
    simp only [B, Matrix.submatrix_apply, id_eq]
    rw [hA_val lastIdx (σ j)]
    have hσj := hσ_inner_isInner j hj
    have hσjv := hσ_inner j hj
    simp only [hnot, hσj, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, lastIdx, Fin.val_last]
    rw [hhi (m + 1 + (σ j).val) (by omega) (by omega),
      hhi (m + 1 + (m + 1)) (by omega) (by omega), sub_self]
  have hB_geM_zero : ∀ i : Fin (m + 2), isInner i → M ≤ i.val → B i ⟨0, by omega⟩ = 0 := by
    intro i hi hiM
    simp only [B, Matrix.submatrix_apply, id_eq, hσ_zero]
    rw [hA_val i ⟨0, by omega⟩]
    have hn0 : ¬ isInner ⟨0, by omega⟩ := by simp [isInner]
    simp only [hi, hn0, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, lastIdx, Fin.val_last]
    rw [hmid (i.val + 0) (by omega) (by omega), hmid (m + 1 + 0) (by omega) (by omega), sub_self]
  have hB_inner_last : ∀ i : Fin (m + 2), isInner i → B i lastIdx = 0 := by
    intro i hi
    simp only [B, Matrix.submatrix_apply, id_eq, hσ_last]
    rw [hA_val i lastIdx]
    simp only [hi, hnot, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, lastIdx, Fin.val_last]
    rw [hhi (i.val + (m + 1)) (by omega) (by omega),
      hhi (m + 1 + (m + 1)) (by omega) (by omega), sub_self]
  -- Step 3: Conjugate `B` by `e := plateauBlockEquiv hM hMN` (same perm on rows and cols!).
  let e := plateauBlockEquiv hM hMN
  have hdetC : (B.submatrix e e).det = B.det := Matrix.det_reindex_self e.symm B
  -- `B.submatrix e e` is block upper triangular in `((Fin (M-1) ⊕ Fin 2) ⊕ Fin (m+1-M))`!
  set C := B.submatrix e e
  have he_inl_val : ∀ i : Fin (M - 1), (e (Sum.inl (Sum.inl i))).val = i.val + 1 := fun _ => rfl
  have he_inr_val : ∀ k : Fin (m + 2 - 1 - M), (e (Sum.inr k)).val = M + k.val := fun _ => rfl
  have he_inl_inl : ∀ i : Fin (M - 1), isInner (e (Sum.inl (Sum.inl i))) := by
    intro i; change 0 < (e (Sum.inl (Sum.inl i))).val ∧ (e (Sum.inl (Sum.inl i))).val < m + 1
    rw [he_inl_val]; omega
  have he_inr : ∀ k : Fin (m + 2 - 1 - M), isInner (e (Sum.inr k)) := by
    intro k; change 0 < (e (Sum.inr k)).val ∧ (e (Sum.inr k)).val < m + 1
    rw [he_inr_val]; omega
  have he_zero : e (Sum.inl (Sum.inr 0)) = ⟨0, by omega⟩ := by
    ext; simp [e, plateauBlockEquiv]
  have he_last : e (Sum.inl (Sum.inr 1)) = lastIdx := by
    ext; simp [e, plateauBlockEquiv, lastIdx]
  have hC_bl : Matrix.toBlocks₂₁ C = 0 := by
    ext k x
    simp only [Matrix.toBlocks₂₁, C, Matrix.submatrix_apply, Matrix.of_apply, Matrix.zero_apply]
    have hk : isInner (e (Sum.inr k)) := he_inr k
    have hkM : M ≤ (e (Sum.inr k)).val := by rw [he_inr_val]; omega
    rcases x with (i | j)
    · apply hB_inner_gt _ _ hk (he_inl_inl i)
      rw [he_inr_val, he_inl_val]; omega
    · fin_cases j
      · dsimp only
        rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, he_zero]
        exact hB_geM_zero _ hk hkM
      · dsimp only
        rw [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, he_last]
        exact hB_inner_last _ hk
  have hC_split1 : C.det = (Matrix.toBlocks₁₁ C).det * (Matrix.toBlocks₂₂ C).det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
    rw [hC_bl, Matrix.det_fromBlocks_zero₂₁]
  -- Top-left block `C11` is also block upper triangular in `Fin (M-1) ⊕ Fin 2`!
  set C11 := Matrix.toBlocks₁₁ C
  have hC11_bl : Matrix.toBlocks₂₁ C11 = 0 := by
    ext j i
    simp only [Matrix.toBlocks₂₁, C11, Matrix.toBlocks₁₁, C, Matrix.submatrix_apply,
      Matrix.of_apply, Matrix.zero_apply]
    have hi : isInner (e (Sum.inl (Sum.inl i))) := he_inl_inl i
    have hiM : (e (Sum.inl (Sum.inl i))).val < M := by rw [he_inl_val]; omega
    fin_cases j
    · dsimp only
      rw [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, he_zero]
      exact hB_zero_ltM _ hi hiM
    · dsimp only
      rw [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, he_last]
      exact hB_last_inner _ hi
  have hC11_split : C11.det = (Matrix.toBlocks₁₁ C11).det * (Matrix.toBlocks₂₂ C11).det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C11]
    rw [hC11_bl, Matrix.det_fromBlocks_zero₂₁]
  -- Evaluate the three diagonal blocks:
  have hdet_blk1 : (Matrix.toBlocks₁₁ C11).det = (-d) ^ (M - 1) := by
    apply det_of_upperTriangular_const _ (-d)
    · intro i j hlt
      simp only [Matrix.toBlocks₁₁, C11, C, Matrix.submatrix_apply, Matrix.of_apply]
      apply hB_inner_gt _ _ (he_inl_inl i) (he_inl_inl j)
      rw [he_inl_val, he_inl_val]; omega
    · intro i
      simp only [Matrix.toBlocks₁₁, C11, C, Matrix.submatrix_apply, Matrix.of_apply]
      exact hB_inner_diag _ (he_inl_inl i)
  have hdet_blk3 : (Matrix.toBlocks₂₂ C).det = (-d) ^ (m + 2 - 1 - M) := by
    apply det_of_upperTriangular_const _ (-d)
    · intro i j hlt
      simp only [Matrix.toBlocks₂₂, C, Matrix.submatrix_apply, Matrix.of_apply]
      apply hB_inner_gt _ _ (he_inr i) (he_inr j)
      rw [he_inr_val, he_inr_val]; omega
    · intro i
      simp only [Matrix.toBlocks₂₂, C, Matrix.submatrix_apply, Matrix.of_apply]
      exact hB_inner_diag _ (he_inr i)
  have hdet_blk2 : (Matrix.toBlocks₂₂ C11).det = f 0 * (a + d) - a ^ 2 := by
    rw [Matrix.det_fin_two]
    have hn0 : ¬ isInner ⟨0, by omega⟩ := by simp [isInner]
    have h00 : Matrix.toBlocks₂₂ C11 0 0 = f 0 := by
      simp only [Matrix.toBlocks₂₂, C11, Matrix.toBlocks₁₁, C, Matrix.submatrix_apply,
        Matrix.of_apply, he_zero, B, id_eq, hσ_zero]
      rw [hA_val]
      simp only [hn0, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, add_zero]
    have h01 : Matrix.toBlocks₂₂ C11 0 1 = a := by
      simp only [Matrix.toBlocks₂₂, C11, Matrix.toBlocks₁₁, C, Matrix.submatrix_apply,
        Matrix.of_apply, he_zero, he_last, B, id_eq, hσ_last]
      rw [hA_val]
      simp only [hn0, hnot, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, lastIdx, Fin.val_last]
      exact hmid (0 + (m + 1)) (by omega) (by omega)
    have h10 : Matrix.toBlocks₂₂ C11 1 0 = a := by
      simp only [Matrix.toBlocks₂₂, C11, Matrix.toBlocks₁₁, C, Matrix.submatrix_apply,
        Matrix.of_apply, he_last, he_zero, B, id_eq, hσ_zero]
      rw [hA_val]
      simp only [hn0, hnot, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, lastIdx, Fin.val_last]
      exact hmid (m + 1 + 0) (by omega) (by omega)
    have h11 : Matrix.toBlocks₂₂ C11 1 1 = a + d := by
      simp only [Matrix.toBlocks₂₂, C11, Matrix.toBlocks₁₁, C, Matrix.submatrix_apply,
        Matrix.of_apply, he_last, B, id_eq, hσ_last]
      rw [hA_val]
      simp only [hnot, ↓reduceIte, H, hankelZeroMatrix, Matrix.of_apply, lastIdx, Fin.val_last]
      exact hhi (m + 1 + (m + 1)) (by omega) (by omega)
    rw [h00, h01, h10, h11]
    ring
  -- Combine `hdetB`, `hdetC`, `hC_split1`, `hC11_split`!
  have hB_eval : B.det = (-d) ^ m * (f 0 * (a + d) - a ^ 2) := by
    rw [← hdetC, hC_split1, hC11_split, hdet_blk1, hdet_blk2, hdet_blk3]
    have hexp : (M - 1) + (m + 2 - 1 - M) = m := by omega
    calc (-d) ^ (M - 1) * (f 0 * (a + d) - a ^ 2) * (-d) ^ (m + 2 - 1 - M)
        = (-d) ^ ((M - 1) + (m + 2 - 1 - M)) * (f 0 * (a + d) - a ^ 2) := by
            rw [pow_add]; ring
      _ = (-d) ^ m * (f 0 * (a + d) - a ^ 2) := by rw [hexp]
  -- Multiply both sides of `hdetB` by `(-1) ^ (m.choose 2)`!
  have hsign_sq : (-1 : R) ^ (m.choose 2) * (-1 : R) ^ (m.choose 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc H.det = (-1 : R) ^ (m.choose 2) * ((-1 : R) ^ (m.choose 2) * H.det) := by
        rw [← mul_assoc, hsign_sq, one_mul]
    _ = (-1 : R) ^ (m.choose 2) * B.det := by rw [hdetB]
    _ = (-1 : R) ^ (m.choose 2) * ((-d) ^ m * (f 0 * (a + d) - a ^ 2)) := by rw [hB_eval]
    _ = (-1 : R) ^ ((m + 1).choose 2) * d ^ m * (f 0 * (a + d) - a ^ 2) := by
        have hneg : (-d) ^ m = (-1 : R) ^ m * d ^ m := by
          rw [neg_eq_neg_one_mul, mul_pow]
        have hchoose : (m + 1).choose 2 = m.choose 2 + m := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
        rw [hneg, hchoose, pow_add]
        ring

section MixedDigitLen

lemma place_pos (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) : ∀ k, 1 ≤ place b k
  | 0 => by simp [place]
  | k + 1 => by
      simp only [place]
      have h1 := place_pos b hb k
      have h2 := hb k
      nlinarith

lemma mlen_zero (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) : ∀ k, mlen b k 0 = 0
  | 0 => by simp [mlen]
  | k + 1 => by
      have hpos : 0 < place b (k + 1) := place_pos b hb (k + 1)
      simp [mlen, hpos, mlen_zero b hb k]

lemma mlen_of_ge {b : ℕ → ℕ} (k n : ℕ) (h : place b (k + 1) ≤ n) :
    mlen b (k + 1) n = k + 2 := by
  have hlt : ¬ n < place b (k + 1) := by omega
  simp [mlen, hlt]

lemma mlen_of_range {b : ℕ → ℕ} :
    ∀ k n : ℕ, place b k ≤ n → n < place b (k + 1) → mlen b (k + 1) n = k + 1
  | 0, n, h1, h2 => by
      have hne : n ≠ 0 := by
        simp [place] at h1
        omega
      simp [mlen, h2, hne]
  | k + 1, n, h1, h2 => by
      have hlt : ¬ n < place b (k + 1) := by omega
      simp [mlen, h2, hlt]

/-- Universal 1-based mixed-radix digit-length Hankel determinant: for any mixed radix `b` with
`∀ r, 2 ≤ b r` and any `k ≥ 1`, `det (mlen b k (i + j + 2))_{0 ≤ i, j < P_k - 1}` equals
`(-1) ^ (P_k - 1).choose 2 * (k + 1)`. -/
theorem det_mixedDigitLen_one {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (k : ℕ) (hk : 1 ≤ k) :
    (hankelOneMatrix (place b k) (fun n => (mlen b k n : R))).det =
      (-1 : R) ^ ((place b k - 1).choose 2) * ((k + 1 : ℕ) : R) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hb1 : ∀ r, 1 ≤ b r := fun r => le_trans (by decide) (hb r)
  have hP0 : 1 ≤ place b k' := place_pos b hb1 k'
  have hP : 2 * place b k' ≤ place b (k' + 1) := by
    simp only [place]
    have hbk := hb k'
    nlinarith
  have hN : 2 ≤ place b (k' + 1) := by omega
  have hmid : (mlen b (k' + 1) (place b (k' + 1) - 1) : R) = ((k' + 1 : ℕ) : R) := by
    have hm := mlen_of_range (b := b) k' (place b (k' + 1) - 1) (by omega) (by omega)
    exact congrArg Nat.cast hm
  have hhi : ∀ n, place b (k' + 1) ≤ n → n ≤ 2 * place b (k' + 1) - 2 →
      (mlen b (k' + 1) n : R) = ((k' + 1 : ℕ) : R) + 1 := by
    intro n hn _
    have hm := mlen_of_ge (b := b) k' n hn
    rw [hm]
    push_cast
    ring
  have hdet := det_plateauHankel_one hN (fun n => (mlen b (k' + 1) n : R))
    ((k' + 1 : ℕ) : R) 1 hmid hhi
  simpa [one_pow, mul_one, Nat.cast_add, Nat.cast_one] using hdet

/-- Universal 0-based mixed-radix digit-length Hankel determinant: for any mixed radix `b` with
`∀ r, 2 ≤ b r` and any `k ≥ 1`, `det (mlen b k (i + j))_{0 ≤ i, j < P_k}` equals
`-((-1) ^ (P_k - 1).choose 2) * k ^ 2`. -/
theorem det_mixedDigitLen_zero {R : Type*} [CommRing R] (b : ℕ → ℕ) (hb : ∀ r, 2 ≤ b r)
    (k : ℕ) (hk : 1 ≤ k) :
    (hankelZeroMatrix (place b k) (fun n => (mlen b k n : R))).det =
      (-1 : R) ^ ((place b k - 1).choose 2 + 1) * ((k : R) ^ 2) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hb1 : ∀ r, 1 ≤ b r := fun r => le_trans (by decide) (hb r)
  have hM : 1 ≤ place b k' := place_pos b hb1 k'
  have hMN : 2 * place b k' ≤ place b (k' + 1) := by
    simp only [place]
    have hbk := hb k'
    nlinarith
  have hmid : ∀ n, place b k' ≤ n → n < place b (k' + 1) →
      (mlen b (k' + 1) n : R) = ((k' + 1 : ℕ) : R) := by
    intro n h1 h2
    exact congrArg Nat.cast (mlen_of_range (b := b) k' n h1 h2)
  have hhi : ∀ n, place b (k' + 1) ≤ n → n ≤ 2 * place b (k' + 1) - 2 →
      (mlen b (k' + 1) n : R) = ((k' + 1 : ℕ) : R) + 1 := by
    intro n hn _
    have hm := mlen_of_ge (b := b) k' n hn
    rw [hm]
    push_cast
    ring
  have hdet := det_plateauHankel_zero hM hMN (fun n => (mlen b (k' + 1) n : R))
    ((k' + 1 : ℕ) : R) 1 hmid hhi
  rw [mlen_zero b hb1 (k' + 1)] at hdet
  rw [hdet, pow_succ]
  push_cast
  ring

end MixedDigitLen

end CarryBlocksDeterminants
