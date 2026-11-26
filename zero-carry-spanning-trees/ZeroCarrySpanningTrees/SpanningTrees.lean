/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ZeroCarrySpanningTrees.Defs
import ZeroCarrySpanningTrees.PascalTriangular
import Mathlib.Data.BitVec
import Mathlib.Tactic

/-!
# Mixed-Radix Zero-Carry Graph Spanning Trees & Alternating-Harmonic Spectrum

Proves all 5 headline theorems of `zero-carry-spanning-trees`:
1. `det_zeroCarryWalk_charpoly`: exact splitting of `det(x • 1 - W_{b,k})` over `ℚ`.
2. `det_zeroCarryCofactor_mixed`: exact cleared-denominator Kirchhoff spanning-tree formula
   for arbitrary mixed radix `b_r ≥ 1` over any commutative ring `R`.
3. `det_zeroCarryCofactor_base`: uniform base-`B` specialization.
4. `det_binaryZeroCarryCofactor`: exact binary zero-carry (`i &&& j = 0`) spanning-tree count
   `∏_{m = 2}^k (2^m - (-1)^m)^{C(k, m)}` over any commutative ring `R`.
5. `det_singleRadixZeroCarryCofactor`: `k = 1` threshold half-graph specialization.
-/

namespace ZeroCarrySpanningTrees

open scoped BigOperators
open Matrix Finset

/-! ## Section 1: Mixed-Radix Digit Machinery -/

theorem place_pos (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) : ∀ k, 0 < place b k
  | 0 => by simp [place]
  | k + 1 => Nat.mul_pos (place_pos b hb k) (hb k)

theorem place_const (B : ℕ) : ∀ k, place (fun _ => B) k = B ^ k
  | 0 => by simp [place]
  | k + 1 => by simp [place, place_const B k, pow_succ]

theorem mdigit_lt (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (n r : ℕ) : mdigit b n r < b r :=
  Nat.mod_lt _ (hb r)

theorem mdigit_zero (b : ℕ → ℕ) (r : ℕ) : mdigit b 0 r = 0 := by
  simp [mdigit]

theorem place_dvd_place {b : ℕ → ℕ} {r k : ℕ} (h : r ≤ k) : place b r ∣ place b k := by
  induction k with
  | zero =>
    have hr : r = 0 := Nat.le_zero.mp h
    subst hr; exact dvd_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact dvd_refl _
    · exact dvd_mul_of_dvd_left (ih (Nat.lt_succ_iff.mp hlt)) (b k)

theorem mdigit_lo_add_mul (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) {k lo hi r : ℕ}
    (_hlo : lo < place b k) (hr : r < k) :
    mdigit b (lo + place b k * hi) r = mdigit b lo r := by
  unfold mdigit
  have hdvd : place b (r + 1) ∣ place b k := place_dvd_place hr
  rcases hdvd with ⟨q, hq⟩
  have hpr : 0 < place b r := place_pos b hb r
  have hdiv : (lo + place b k * hi) / place b r = lo / place b r + b r * (q * hi) := by
    have h1 : place b k * hi = place b r * (b r * (q * hi)) := by
      rw [hq, place]; ring
    rw [h1, Nat.add_mul_div_left _ _ hpr]
  rw [hdiv, Nat.add_mul_mod_self_left]

theorem mdigit_hi_add_mul (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) {k lo hi : ℕ}
    (hlo : lo < place b k) (hhi : hi < b k) :
    mdigit b (lo + place b k * hi) k = hi := by
  unfold mdigit
  have hpk : 0 < place b k := place_pos b hb k
  rw [Nat.add_mul_div_left _ _ hpk, Nat.div_eq_of_lt hlo, zero_add, Nat.mod_eq_of_lt hhi]

/-- Equivalence `Fin (place b (k + 1)) ≃ Fin (place b k) × Fin (b k)` via `(i % P_k, i / P_k)`. -/
def mixedEquiv (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    Fin (place b (k + 1)) ≃ Fin (place b k) × Fin (b k) where
  toFun i :=
    (⟨i.1 % place b k, Nat.mod_lt _ (place_pos b hb k)⟩,
     ⟨i.1 / place b k, (Nat.div_lt_iff_lt_mul (place_pos b hb k)).mpr (by simpa [place, mul_comm] using i.2)⟩)
  invFun p :=
    ⟨p.1.1 + place b k * p.2.1, by
      have h1 : p.1.1 < place b k := p.1.2
      have h2 : p.2.1 + 1 ≤ b k := p.2.2
      calc p.1.1 + place b k * p.2.1
          < place b k + place b k * p.2.1 := Nat.add_lt_add_right h1 _
        _ = place b k * (p.2.1 + 1) := by ring
        _ ≤ place b k * b k := Nat.mul_le_mul_left _ h2⟩
  left_inv i := by
    ext
    simp [Nat.mod_add_div]
  right_inv p := by
    have hpk := place_pos b hb k
    ext
    · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.1.2]
    · simp [Nat.add_mul_div_left _ _ hpk, Nat.div_eq_of_lt p.1.2]

/-- If `x < y < place b k`, there is a digit `r < k` where `mdigit b x r < mdigit b y r`
(specifically, the highest differing digit). -/
theorem exists_mdigit_lt_of_lt (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) :
    ∀ k x y, x < y → y < place b k →
      ∃ r ∈ Finset.range k, mdigit b x r < mdigit b y r
  | 0, x, y, hxy, hy => by simp [place] at hy; omega
  | k + 1, x, y, hxy, hy => by
    have hpk := place_pos b hb k
    have hx : x < place b (k + 1) := lt_trans hxy hy
    have hx_hi : x / place b k < b k :=
      (Nat.div_lt_iff_lt_mul hpk).mpr (by simpa [place, mul_comm] using hx)
    have hy_hi : y / place b k < b k :=
      (Nat.div_lt_iff_lt_mul hpk).mpr (by simpa [place, mul_comm] using hy)
    have hdiv_le : x / place b k ≤ y / place b k := Nat.div_le_div_right (le_of_lt hxy)
    rcases lt_or_eq_of_le hdiv_le with hlt | heq
    · refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), ?_⟩
      simpa [mdigit, Nat.mod_eq_of_lt hx_hi, Nat.mod_eq_of_lt hy_hi] using hlt
    · have hmod_lt : x % place b k < y % place b k := by
        have hx' := Nat.div_add_mod x (place b k)
        have hy' := Nat.div_add_mod y (place b k)
        rw [heq] at hx'
        omega
      rcases exists_mdigit_lt_of_lt b hb k (x % place b k) (y % place b k) hmod_lt (Nat.mod_lt _ hpk) with
        ⟨r, hr, hlt⟩
      refine ⟨r, Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hr)), ?_⟩
      have hxr : mdigit b x r = mdigit b (x % place b k) r := by
        have hx' : x = x % place b k + place b k * (x / place b k) := by
          have := Nat.div_add_mod x (place b k); omega
        conv_lhs => rw [hx']
        exact mdigit_lo_add_mul b hb (Nat.mod_lt _ hpk) (Finset.mem_range.mp hr)
      have hyr : mdigit b y r = mdigit b (y % place b k) r := by
        have hy' : y = y % place b k + place b k * (y / place b k) := by
          have := Nat.div_add_mod y (place b k); omega
        conv_lhs => rw [hy']
        exact mdigit_lo_add_mul b hb (Nat.mod_lt _ hpk) (Finset.mem_range.mp hr)
      rw [hxr, hyr]
      exact hlt

/-- Complement digit identity: `mdigit b (place b k - 1 - x) r = b r - 1 - mdigit b x r`. -/
theorem mdigit_complement (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) :
    ∀ k x r, x < place b k → r < k →
      mdigit b (place b k - 1 - x) r = b r - 1 - mdigit b x r
  | 0, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | k + 1, x, r, hx, hr => by
    have hpk := place_pos b hb k
    have hbk := hb k
    let lo := x % place b k
    let hi := x / place b k
    have hlo : lo < place b k := Nat.mod_lt _ hpk
    have hhi : hi < b k :=
      (Nat.div_lt_iff_lt_mul hpk).mpr (by simpa [place, mul_comm] using hx)
    have hx_eq : x = lo + place b k * hi := by
      dsimp only [lo, hi]
      have := Nat.div_add_mod x (place b k)
      omega
    have hcomp_eq : place b (k + 1) - 1 - x =
        (place b k - 1 - lo) + place b k * (b k - 1 - hi) := by
      rw [place, hx_eq]
      have h1 : place b k * b k = place b k * (b k - 1) + place b k := by
        calc place b k * b k = place b k * ((b k - 1) + 1) := by congr 1; omega
          _ = place b k * (b k - 1) + place b k := by ring
      have h2 : place b k * (b k - 1) = place b k * hi + place b k * (b k - 1 - hi) := by
        rw [← Nat.mul_add]; congr 1; omega
      omega
    rw [hcomp_eq]
    have hlo_comp : place b k - 1 - lo < place b k :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hpk Nat.one_pos)
    have hhi_comp : b k - 1 - hi < b k :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hbk Nat.one_pos)
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hlt | rfl
    · rw [mdigit_lo_add_mul b hb hlo_comp hlt]
      conv_rhs => rw [hx_eq, mdigit_lo_add_mul b hb hlo hlt]
      exact mdigit_complement b hb k lo r hlo hlt
    · rw [mdigit_hi_add_mul b hb hlo_comp hhi_comp]
      conv_rhs => rw [hx_eq, mdigit_hi_add_mul b hb hlo hhi]

/-- Mixed-radix digit injectivity on `0 ≤ x, y < place b k`. -/
theorem eq_of_mdigit_eq (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) {k x y : ℕ}
    (hx : x < place b k) (hy : y < place b k)
    (h : ∀ r ∈ Finset.range k, mdigit b x r = mdigit b y r) : x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rcases exists_mdigit_lt_of_lt b hb k x y hlt hy with ⟨r, hr, hlt'⟩
    exact absurd (h r hr) (ne_of_lt hlt')
  · rcases exists_mdigit_lt_of_lt b hb k y x hgt hx with ⟨r, hr, hlt'⟩
    exact absurd (h r hr).symm (ne_of_lt hlt')

/-! ## Section 2: Inductive Kronecker-Pascal Triangularization over `ℚ` -/

/-- Mixed-radix Kronecker-Pascal matrix `(P_{b,k})_{i,j} = ∏_{r < k} C(b_r - 1 - d_r(i), d_r(j))`. -/
def pascalKron (b : ℕ → ℕ) (k : ℕ) : Matrix (Fin (place b k)) (Fin (place b k)) ℚ :=
  Matrix.of fun i j =>
    ∏ r ∈ Finset.range k, (((b r - 1 - mdigit b i.1 r).choose (mdigit b j.1 r) : ℕ) : ℚ)

/-- Mixed-radix Kronecker upper-triangular matrix `U_{b,k}`. -/
def upperKron (b : ℕ → ℕ) (k : ℕ) : Matrix (Fin (place b k)) (Fin (place b k)) ℚ :=
  Matrix.of fun i j =>
    ∏ r ∈ Finset.range k,
      if mdigit b i.1 r ≤ mdigit b j.1 r then
        ((-1 : ℚ) ^ mdigit b i.1 r / ((mdigit b i.1 r + 1 : ℕ) : ℚ)) *
          (((b r - 1 - mdigit b i.1 r).choose (mdigit b j.1 r - mdigit b i.1 r) : ℕ) : ℚ)
      else 0

/-- Diagonal matrix `B_{b,k}` with `(i,i)`-entry `∏_{r < k} (b_r - d_r(i))` over `ℚ`. -/
def degDiagKron (b : ℕ → ℕ) (k : ℕ) : Matrix (Fin (place b k)) (Fin (place b k)) ℚ :=
  Matrix.diagonal fun i => ∏ r ∈ Finset.range k, ((b r - mdigit b i.1 r : ℕ) : ℚ)

theorem pascalKron_col0 (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) (i : Fin (place b k)) :
    pascalKron b k i ⟨0, place_pos b hb k⟩ = 1 := by
  simp [pascalKron, mdigit_zero]

private theorem forall_mem_range_succ {P : ℕ → Prop} {k : ℕ} :
    (∀ r ∈ Finset.range (k + 1), P r) ↔ (∀ r ∈ Finset.range k, P r) ∧ P k := by
  simp only [Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · intro h; exact ⟨fun r hr => h r (le_of_lt hr), h k (le_refl k)⟩
  · rintro ⟨h1, h2⟩ r hr
    rcases lt_or_eq_of_le hr with hlt | rfl
    · exact h1 r hlt
    · exact h2

theorem upperKron_upper (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    (upperKron b k).BlockTriangular id := by
  intro i j hij
  have hlt : j.1 < i.1 := hij
  rcases exists_mdigit_lt_of_lt b hb k j.1 i.1 hlt i.2 with ⟨r, hr, hdig⟩
  simp only [upperKron, Matrix.of_apply]
  refine Finset.prod_eq_zero hr ?_
  simp [Nat.not_le.mpr hdig]

theorem upperKron_diag (b : ℕ → ℕ) (k : ℕ) (j : Fin (place b k)) :
    upperKron b k j j =
      ∏ r ∈ Finset.range k, ((-1 : ℚ) ^ mdigit b j.1 r / ((mdigit b j.1 r + 1 : ℕ) : ℚ)) := by
  simp [upperKron]

theorem pascalKron_det_ne_zero (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    (pascalKron b k).det ≠ 0 := by
  let M : Matrix (Fin (place b k)) (Fin (place b k)) ℚ := (pascalKron b k).submatrix Fin.revPerm id
  have hM_entry : ∀ i j : Fin (place b k),
      M i j = ∏ r ∈ Finset.range k, (((mdigit b i.1 r).choose (mdigit b j.1 r) : ℕ) : ℚ) := by
    intro i j
    simp only [M, pascalKron, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Fin.revPerm_apply,
      Fin.val_rev]
    refine Finset.prod_congr rfl fun r hr => ?_
    have hcomp := mdigit_complement b hb k i.1 r i.2 (Finset.mem_range.mp hr)
    have hdlt := mdigit_lt b hb i.1 r
    have hsub : place b k - (i.1 + 1) = place b k - 1 - i.1 := by omega
    rw [hsub, hcomp]
    congr 2
    omega
  have hM_low : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.1 < j.1 := hij
    rcases exists_mdigit_lt_of_lt b hb k i.1 j.1 hlt j.2 with ⟨r, hr, hdig⟩
    rw [hM_entry]
    refine Finset.prod_eq_zero hr ?_
    rw [Nat.choose_eq_zero_of_lt hdig, Nat.cast_zero]
  have hM_det : M.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular M hM_low]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [hM_entry]
    refine Finset.prod_eq_one fun r _ => ?_
    rw [Nat.choose_self, Nat.cast_one]
  have hperm : M.det = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (place b k))) : ℚ) * (pascalKron b k).det := by
    simpa [M] using Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin (place b k))) (pascalKron b k)
  intro hzero
  rw [hzero, mul_zero] at hperm
  linarith [hM_det, hperm]

/-- Inductive Kronecker-Pascal triangularization:
`zeroCarryWalkMatrix b k * pascalKron b k = pascalKron b k * upperKron b k` over `ℚ`. -/
theorem zeroCarryWalk_mul_pascalKron (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) :
    ∀ k, zeroCarryWalkMatrix b k * pascalKron b k = pascalKron b k * upperKron b k
  | 0 => by
    ext i j
    have hi : i = ⟨0, by simp [place]⟩ := Fin.ext (by have := i.2; simp [place] at this; omega)
    have hj : j = ⟨0, by simp [place]⟩ := Fin.ext (by have := j.2; simp [place] at this; omega)
    subst hi; subst hj
    simp [zeroCarryWalkMatrix, pascalKron, upperKron, place]
  | k + 1 => by
    have ih := zeroCarryWalk_mul_pascalKron b hb k
    have h1 := walkMat1_mul_pascalRev (b k)
    ext i j
    let e := mixedEquiv b hb k
    let pi := e i; let pj := e j
    have hi_eq : i = e.symm pi := (e.symm_apply_apply i).symm
    have hj_eq : j = e.symm pj := (e.symm_apply_apply j).symm
    have hwalk_split : ∀ x y : Fin (place b (k + 1)),
        zeroCarryWalkMatrix b (k + 1) x y =
          zeroCarryWalkMatrix b k (e x).1 (e y).1 * walkMat1 (b k) (e x).2 (e y).2 := by
      intro x y
      have hx : x.1 = (e x).1.1 + place b k * (e x).2.1 := by
        simpa [e, mixedEquiv] using (Nat.mod_add_div x.1 (place b k)).symm
      have hy : y.1 = (e y).1.1 + place b k * (e y).2.1 := by
        simpa [e, mixedEquiv] using (Nat.mod_add_div y.1 (place b k)).symm
      have hdig_lt_x : ∀ r ∈ Finset.range k, mdigit b x.1 r = mdigit b (e x).1.1 r := fun r hr => by
        rw [hx]; exact mdigit_lo_add_mul b hb (e x).1.2 (Finset.mem_range.mp hr)
      have hdig_lt_y : ∀ r ∈ Finset.range k, mdigit b y.1 r = mdigit b (e y).1.1 r := fun r hr => by
        rw [hy]; exact mdigit_lo_add_mul b hb (e y).1.2 (Finset.mem_range.mp hr)
      have hdig_k_x : mdigit b x.1 k = (e x).2.1 := by
        rw [hx]; exact mdigit_hi_add_mul b hb (e x).1.2 (e x).2.2
      have hdig_k_y : mdigit b y.1 k = (e y).2.1 := by
        rw [hy]; exact mdigit_hi_add_mul b hb (e y).1.2 (e y).2.2
      simp only [zeroCarryWalkMatrix, walkMat1, Matrix.of_apply, Finset.prod_range_succ,
        forall_mem_range_succ]
      have hcond_lo :
          (∀ r ∈ Finset.range k, mdigit b x.1 r + mdigit b y.1 r < b r) ↔
          (∀ r ∈ Finset.range k, mdigit b (e x).1.1 r + mdigit b (e y).1.1 r < b r) := by
        constructor <;> intro h r hr
        · rw [← hdig_lt_x r hr, ← hdig_lt_y r hr]; exact h r hr
        · rw [hdig_lt_x r hr, hdig_lt_y r hr]; exact h r hr
      have hprod_lo :
          ∏ r ∈ Finset.range k, ((b r - mdigit b x.1 r : ℕ) : ℚ) =
          ∏ r ∈ Finset.range k, ((b r - mdigit b (e x).1.1 r : ℕ) : ℚ) :=
        Finset.prod_congr rfl fun r hr => by rw [hdig_lt_x r hr]
      rw [hdig_k_x, hdig_k_y, hprod_lo]
      simp only [hcond_lo]
      split_ifs <;> first | (exfalso; tauto) | (rw [mul_inv, mul_comm]) | simp
    have hpas_split : ∀ x y : Fin (place b (k + 1)),
        pascalKron b (k + 1) x y =
          pascalKron b k (e x).1 (e y).1 * pascalRev (b k) (e x).2 (e y).2 := by
      intro x y
      have hx : x.1 = (e x).1.1 + place b k * (e x).2.1 := by
        simpa [e, mixedEquiv] using (Nat.mod_add_div x.1 (place b k)).symm
      have hy : y.1 = (e y).1.1 + place b k * (e y).2.1 := by
        simpa [e, mixedEquiv] using (Nat.mod_add_div y.1 (place b k)).symm
      simp only [pascalKron, pascalRev, Matrix.of_apply, Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl fun r hr => ?_
        rw [hx, hy, mdigit_lo_add_mul b hb (e x).1.2 (Finset.mem_range.mp hr),
            mdigit_lo_add_mul b hb (e y).1.2 (Finset.mem_range.mp hr)]
      · rw [hx, hy, mdigit_hi_add_mul b hb (e x).1.2 (e x).2.2,
            mdigit_hi_add_mul b hb (e y).1.2 (e y).2.2]
    have hupp_split : ∀ x y : Fin (place b (k + 1)),
        upperKron b (k + 1) x y =
          upperKron b k (e x).1 (e y).1 * upperMat1 (b k) (e x).2 (e y).2 := by
      intro x y
      have hx : x.1 = (e x).1.1 + place b k * (e x).2.1 := by
        simpa [e, mixedEquiv] using (Nat.mod_add_div x.1 (place b k)).symm
      have hy : y.1 = (e y).1.1 + place b k * (e y).2.1 := by
        simpa [e, mixedEquiv] using (Nat.mod_add_div y.1 (place b k)).symm
      simp only [upperKron, upperMat1, Matrix.of_apply, Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl fun r hr => ?_
        rw [hx, hy, mdigit_lo_add_mul b hb (e x).1.2 (Finset.mem_range.mp hr),
            mdigit_lo_add_mul b hb (e y).1.2 (Finset.mem_range.mp hr)]
      · rw [hx, hy, mdigit_hi_add_mul b hb (e x).1.2 (e x).2.2,
            mdigit_hi_add_mul b hb (e y).1.2 (e y).2.2]
    simp only [Matrix.mul_apply]
    have hlhs :
        ∑ m : Fin (place b (k + 1)), zeroCarryWalkMatrix b (k + 1) i m * pascalKron b (k + 1) m j =
        (∑ m1 : Fin (place b k), zeroCarryWalkMatrix b k pi.1 m1 * pascalKron b k m1 pj.1) *
        (∑ m2 : Fin (b k), walkMat1 (b k) pi.2 m2 * pascalRev (b k) m2 pj.2) := by
      rw [Fintype.sum_equiv e _ (fun p =>
          (zeroCarryWalkMatrix b k pi.1 p.1 * walkMat1 (b k) pi.2 p.2) *
          (pascalKron b k p.1 pj.1 * pascalRev (b k) p.2 pj.2))]
      · rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m1 _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m2 _ => by ring
      · intro m
        rw [hwalk_split i m, hpas_split m j]
    have hrhs :
        ∑ m : Fin (place b (k + 1)), pascalKron b (k + 1) i m * upperKron b (k + 1) m j =
        (∑ m1 : Fin (place b k), pascalKron b k pi.1 m1 * upperKron b k m1 pj.1) *
        (∑ m2 : Fin (b k), pascalRev (b k) pi.2 m2 * upperMat1 (b k) m2 pj.2) := by
      rw [Fintype.sum_equiv e _ (fun p =>
          (pascalKron b k pi.1 p.1 * pascalRev (b k) pi.2 p.2) *
          (upperKron b k p.1 pj.1 * upperMat1 (b k) p.2 pj.2))]
      · rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m1 _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m2 _ => by ring
      · intro m
        rw [hpas_split i m, hupp_split m j]
    rw [hlhs, hrhs]
    have hih_pt := congrArg (fun M : Matrix (Fin (place b k)) (Fin (place b k)) ℚ => M pi.1 pj.1) ih
    have h1_pt := congrArg (fun M : Matrix (Fin (b k)) (Fin (b k)) ℚ => M pi.2 pj.2) h1
    simp only [Matrix.mul_apply] at hih_pt h1_pt
    rw [hih_pt, h1_pt]

/-! ## Section 3: Theorem 1 (Alternating-Harmonic Characteristic Polynomial) -/

theorem det_zeroCarryWalk_charpoly (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) (x : ℚ) :
    (x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - zeroCarryWalkMatrix b k).det =
      ∏ j : Fin (place b k),
        (x - ∏ r ∈ Finset.range k,
          ((-1 : ℚ) ^ mdigit b j.1 r / ((mdigit b j.1 r + 1 : ℕ) : ℚ))) := by
  have hmul :
      (x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - zeroCarryWalkMatrix b k) * pascalKron b k =
      pascalKron b k * (x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - upperKron b k) := by
    rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        zeroCarryWalk_mul_pascalKron b hb k]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hP := pascalKron_det_ne_zero b hb k
  have heq : (x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - zeroCarryWalkMatrix b k).det =
      (x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - upperKron b k).det := by
    have : ((x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - zeroCarryWalkMatrix b k).det -
        (x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - upperKron b k).det) *
        (pascalKron b k).det = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact absurd h0 hP
  rw [heq]
  have htri : (x • (1 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ) - upperKron b k).BlockTriangular id := by
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hne,
          upperKron_upper b hb k hij]
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [Matrix.sub_apply, Matrix.smul_apply, upperKron_diag]

/-! ## Section 4: Laplacian Structure & Rank-1 Kirchhoff Cofactor Lemma -/

/-- Number of `j < place b k` with `∀ r < k, mdigit b i r + mdigit b j r < b r`
equals `∏_{r < k} (b r - mdigit b i r)`. -/
theorem card_zeroCarry_partners (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) :
    ∀ k i, i < place b k →
      ((Finset.range (place b k)).filter
        (fun j => decide (∀ r ∈ Finset.range k, mdigit b i r + mdigit b j r < b r))).card =
      ∏ r ∈ Finset.range k, (b r - mdigit b i r)
  | 0, i, hi => by
    simp [place] at hi ⊢
  | k + 1, i, hi => by
    have ih := card_zeroCarry_partners b hb k
    let e := mixedEquiv b hb k
    let ifin : Fin (place b (k + 1)) := ⟨i, hi⟩
    let pi := e ifin
    have hi_eq : i = pi.1.1 + place b k * pi.2.1 := by
      simpa [pi, ifin, e, mixedEquiv] using (Nat.mod_add_div i (place b k)).symm
    trans (((Finset.range (place b k)).filter
          (fun j1 => decide (∀ r ∈ Finset.range k, mdigit b pi.1.1 r + mdigit b j1 r < b r))) ×ˢ
         ((Finset.range (b k)).filter (fun j2 => pi.2.1 + j2 < b k))).card
    · refine Finset.card_bij (fun j _ => (j % place b k, j / place b k)) ?_ ?_ ?_
      · intro j hj
        have hj_lt : j < place b (k + 1) := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        have hcond : ∀ r ∈ Finset.range (k + 1), mdigit b i r + mdigit b j r < b r :=
          of_decide_eq_true (Finset.mem_filter.mp hj).2
        have hpk := place_pos b hb k
        have hlo : j % place b k < place b k := Nat.mod_lt _ hpk
        have hhi : j / place b k < b k :=
          (Nat.div_lt_iff_lt_mul hpk).mpr (by simpa [place, mul_comm] using hj_lt)
        have hj_eq : j = j % place b k + place b k * (j / place b k) := by
          have := Nat.div_add_mod j (place b k); omega
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
        refine ⟨⟨hlo, ?_⟩, ⟨hhi, ?_⟩⟩
        · intro r hr
          have h1 := hcond r (Finset.mem_range.mpr (Nat.lt_succ_of_lt hr))
          rwa [hi_eq, hj_eq, mdigit_lo_add_mul b hb pi.1.2 hr, mdigit_lo_add_mul b hb hlo hr] at h1
        · have h1 := hcond k (Finset.mem_range.mpr (Nat.lt_succ_self k))
          rwa [hi_eq, hj_eq, mdigit_hi_add_mul b hb pi.1.2 pi.2.2,
               mdigit_hi_add_mul b hb hlo hhi] at h1
      · intro j1 _ j2 _ heq
        have h1 : j1 % place b k = j2 % place b k := congrArg Prod.fst heq
        have h2 : j1 / place b k = j2 / place b k := congrArg Prod.snd heq
        have hd1 := Nat.div_add_mod j1 (place b k)
        have hd2 := Nat.div_add_mod j2 (place b k)
        rw [h1, h2] at hd1
        omega
      · intro p hp
        have hp1 := (Finset.mem_product.mp hp).1
        have hp2 := (Finset.mem_product.mp hp).2
        have hlo : p.1 < place b k := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
        have hcond1 : ∀ r ∈ Finset.range k, mdigit b pi.1.1 r + mdigit b p.1 r < b r :=
          of_decide_eq_true (Finset.mem_filter.mp hp1).2
        have hhi : p.2 < b k := Finset.mem_range.mp (Finset.mem_filter.mp hp2).1
        have hcond2 : pi.2.1 + p.2 < b k := (Finset.mem_filter.mp hp2).2
        have hpk := place_pos b hb k
        have hval_lt : p.1 + place b k * p.2 < place b (k + 1) := by
          rw [place]
          calc p.1 + place b k * p.2 < place b k + place b k * p.2 := Nat.add_lt_add_right hlo _
            _ = place b k * (p.2 + 1) := by ring
            _ ≤ place b k * b k := Nat.mul_le_mul_left _ hhi
        refine ⟨p.1 + place b k * p.2, ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hval_lt, decide_eq_true ?_⟩
          rw [forall_mem_range_succ]
          constructor
          · intro r hr
            rw [hi_eq, mdigit_lo_add_mul b hb pi.1.2 (Finset.mem_range.mp hr),
                mdigit_lo_add_mul b hb hlo (Finset.mem_range.mp hr)]
            exact hcond1 r hr
          · rw [hi_eq, mdigit_hi_add_mul b hb pi.1.2 pi.2.2, mdigit_hi_add_mul b hb hlo hhi]
            exact hcond2
        · ext
          · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
          · simp [Nat.add_mul_div_left _ _ hpk, Nat.div_eq_of_lt hlo]
    · rw [Finset.card_product, ih pi.1.1 pi.1.2, Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl fun r hr => ?_
        rw [hi_eq, mdigit_lo_add_mul b hb pi.1.2 (Finset.mem_range.mp hr)]
      · rw [hi_eq, mdigit_hi_add_mul b hb pi.1.2 pi.2.2]
        have hfilt : (Finset.range (b k)).filter (fun j2 => pi.2.1 + j2 < b k) =
            Finset.range (b k - pi.2.1) := by
          ext j2; simp only [Finset.mem_filter, Finset.mem_range]; omega
        rw [hfilt, Finset.card_range]

/-- Key structural identity: `zeroCarryLaplacian b k = degDiagKron b k * (1 - zeroCarryWalkMatrix b k)`
over `ℚ`! The self-loop at `i = j` (when `∀ r < k, 2 * d_r(i) < b_r`) cancels identically between
`degDiagKron` and `zeroCarryDeg`! -/
theorem zeroCarryLaplacian_eq_degDiag_mul_sub (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    zeroCarryLaplacian (R := ℚ) b k =
      degDiagKron b k * (1 - zeroCarryWalkMatrix b k) := by
  ext i j
  simp only [Matrix.mul_apply, degDiagKron, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp only [↓reduceIte, Matrix.sub_apply, zeroCarryLaplacian, zeroCarryWalkMatrix,
      Matrix.of_apply]
    have hprod_ne : (∏ r ∈ Finset.range k, ((b r - mdigit b i.1 r : ℕ) : ℚ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun r _ => ?_
      have hdlt := mdigit_lt b hb i.1 r
      have hpos : 0 < b r - mdigit b i.1 r := by omega
      exact_mod_cast hpos.ne'
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Matrix.one_apply_eq]
      have hcard := card_zeroCarry_partners b hb k i.1 i.2
      split_ifs with hself
      · rw [mul_sub, mul_one, mul_inv_cancel₀ hprod_ne]
        -- zeroCarryDeg = total partners - 1 (since i itself is a partner)
        have hdeg : zeroCarryDeg b k i.1 + 1 = ∏ r ∈ Finset.range k, (b r - mdigit b i.1 r) := by
          rw [← hcard]
          unfold zeroCarryDeg zeroCarryAdjBool
          have herase :
              ((Finset.range (place b k)).filter
                (fun x => decide (i.1 ≠ x ∧ ∀ r ∈ Finset.range k, mdigit b i.1 r + mdigit b x r < b r))) =
              ((Finset.range (place b k)).filter
                (fun x => decide (∀ r ∈ Finset.range k, mdigit b i.1 r + mdigit b x r < b r))).erase i.1 := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_erase, decide_eq_true_eq]
            tauto
          have hmem : i.1 ∈ (Finset.range (place b k)).filter
              (fun x => decide (∀ r ∈ Finset.range k, mdigit b i.1 r + mdigit b x r < b r)) := by
            simp only [Finset.mem_filter, decide_eq_true_eq]
            exact ⟨Finset.mem_range.mpr i.2, hself⟩
          rw [herase, Finset.card_erase_add_one hmem]
        have hq : (zeroCarryDeg b k i.1 : ℚ) + 1 =
            ∏ r ∈ Finset.range k, ((b r - mdigit b i.1 r : ℕ) : ℚ) := by
          exact_mod_cast hdeg
        linarith
      · rw [sub_zero, mul_one]
        -- zeroCarryDeg = total partners (since i itself is not a partner)
        have hdeg : zeroCarryDeg b k i.1 = ∏ r ∈ Finset.range k, (b r - mdigit b i.1 r) := by
          rw [← hcard]
          unfold zeroCarryDeg zeroCarryAdjBool
          congr 1
          ext x
          simp only [Finset.mem_filter, decide_eq_true_eq]
          constructor
          · rintro ⟨hx, _, hcond⟩; exact ⟨hx, hcond⟩
          · rintro ⟨hx, hcond⟩
            refine ⟨hx, ?_, hcond⟩
            rintro rfl
            exact hself hcond
        exact_mod_cast hdeg
    · simp only [hij, ↓reduceIte, Matrix.one_apply_ne hij, zero_sub, mul_neg]
      unfold zeroCarryAdjBool
      have hne_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
      split_ifs with h1 h2 h3
      · rw [mul_inv_cancel₀ hprod_ne]
      · exact absurd (of_decide_eq_true h1).2 h2
      · exact absurd (decide_eq_true ⟨hne_val, h3⟩) h1
      · ring
  · intro m _ hmi
    simp [hmi.symm]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Every row of `zeroCarryLaplacian` sums to `0`. -/
theorem zeroCarryLaplacian_row_sum (b : ℕ → ℕ) (k : ℕ) (i : Fin (place b k)) :
    ∑ j : Fin (place b k), zeroCarryLaplacian (R := ℚ) b k i j = 0 := by
  have hsum :
      ∑ j : Fin (place b k), zeroCarryLaplacian (R := ℚ) b k i j =
      (zeroCarryDeg b k i.1 : ℚ) +
        ∑ j ∈ Finset.univ.erase i, (if zeroCarryAdjBool b k i.1 j.1 = true then (-1 : ℚ) else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [zeroCarryLaplacian, Matrix.of_apply, ↓reduceIte]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [(Finset.ne_of_mem_erase hj).symm]
  rw [hsum]
  have hcnt :
      (∑ j ∈ Finset.univ.erase i, (if zeroCarryAdjBool b k i.1 j.1 = true then (-1 : ℚ) else 0)) =
      -(zeroCarryDeg b k i.1 : ℚ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((Finset.univ.erase i).filter (fun j : Fin (place b k) => zeroCarryAdjBool b k i.1 j.1 = true)).card =
        zeroCarryDeg b k i.1 := by
      unfold zeroCarryDeg
      refine Finset.card_bij (fun j _ => j.1) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨j.2, (Finset.mem_filter.mp hj).2⟩
      · intro j1 _ j2 _ h; exact Fin.ext h
      · intro j hj
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        have hadj := (Finset.mem_filter.mp hj).2
        have hne : (⟨j, hlt⟩ : Fin (place b k)) ≠ i := by
          intro heq
          have h1 : i.1 ≠ j := (of_decide_eq_true hadj).1
          exact h1 (congrArg Fin.val heq).symm
        refine ⟨⟨j, hlt⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨⟨hne, Finset.mem_univ _⟩, hadj⟩
    rw [hcard]; ring
  rw [hcnt]; ring

/-- `zeroCarryLaplacian` is symmetric. -/
theorem zeroCarryLaplacian_symm (b : ℕ → ℕ) (k : ℕ) :
    (zeroCarryLaplacian (R := ℚ) b k).transpose = zeroCarryLaplacian (R := ℚ) b k := by
  ext i j
  simp only [Matrix.transpose_apply, zeroCarryLaplacian, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [hij, Ne.symm hij, ↓reduceIte]
    have hadj : zeroCarryAdjBool b k j.1 i.1 = zeroCarryAdjBool b k i.1 j.1 := by
      unfold zeroCarryAdjBool
      congr 1
      exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, fun r hr => by rw [add_comm]; exact h2 r hr⟩,
                     fun ⟨h1, h2⟩ => ⟨h1.symm, fun r hr => by rw [add_comm]; exact h2 r hr⟩⟩
    rw [hadj]

/-- Every column of `zeroCarryLaplacian` sums to `0`. -/
theorem zeroCarryLaplacian_col_sum (b : ℕ → ℕ) (k : ℕ) (j : Fin (place b k)) :
    ∑ i : Fin (place b k), zeroCarryLaplacian (R := ℚ) b k i j = 0 := by
  have h := zeroCarryLaplacian_row_sum b k j
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs := congrArg (fun M : Matrix (Fin (place b k)) (Fin (place b k)) ℚ => M i j)
    (zeroCarryLaplacian_symm b k)
  exact hs.symm

/-- General rank-1 Kirchhoff cofactor lemma over `ℚ`:
if `L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ` has all row sums `0` and all column sums `0`,
then for any vector `v : Fin (n + 1) → ℚ`,
`det (L + fun i _ => v i) = (n + 1) * (∑ i, v i) * det (L.submatrix Fin.succ Fin.succ)`. -/
theorem det_add_rank1_eq_mul_cofactor {n : ℕ}
    (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hrow : ∀ i, ∑ j, L i j = 0)
    (hcol : ∀ j, ∑ i, L i j = 0)
    (v : Fin (n + 1) → ℚ) :
    (L + Matrix.of fun i _ => v i).det =
      ((n + 1 : ℕ) : ℚ) * (∑ i, v i) * (L.submatrix Fin.succ Fin.succ).det := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := L + Matrix.of fun i _ => v i
  -- E1 adds rows 1..n to row 0 (unit upper triangular, det = 1)
  let E1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
    Matrix.of fun i j => if i = 0 then 1 else if i = j then 1 else 0
  -- E2 adds cols 1..n to col 0 (unit lower triangular, det = 1)
  let E2 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
    Matrix.of fun i j => if j = 0 then 1 else if i = j then 1 else 0
  -- E3 subtracts (1 / (n+1)) * col 0 from each col j > 0 (unit upper triangular, det = 1)
  let E3 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
    Matrix.of fun i j =>
      if i = j then 1
      else if i = 0 then -(((n + 1 : ℕ) : ℚ))⁻¹
      else 0
  have hE1_det : E1.det = 1 := by
    have htri : E1.BlockTriangular id := by
      intro i j hij
      have hne : i ≠ j := ne_of_gt hij
      have hi0 : i ≠ 0 := by intro h; subst h; exact Nat.not_lt_zero _ hij
      simp [E1, hi0, hne]
    rw [Matrix.det_of_isUpperTriangular htri]
    refine Finset.prod_eq_one fun i _ => by simp [E1]
  have hE2_det : E2.det = 1 := by
    have htri : E2.BlockTriangular OrderDual.toDual := by
      intro i j hij
      have hne : i ≠ j := ne_of_lt hij
      have hj0 : j ≠ 0 := by intro h; subst h; exact Nat.not_lt_zero _ hij
      simp [E2, hj0, hne]
    rw [Matrix.det_of_isLowerTriangular E2 htri]
    refine Finset.prod_eq_one fun i _ => by simp [E2]
  have hE3_det : E3.det = 1 := by
    have htri : E3.BlockTriangular id := by
      intro i j hij
      have hne : i ≠ j := ne_of_gt hij
      have hi0 : i ≠ 0 := by intro h; subst h; exact Nat.not_lt_zero _ hij
      simp [E3, hne, hi0]
    rw [Matrix.det_of_isUpperTriangular htri]
    refine Finset.prod_eq_one fun i _ => by simp [E3]
  -- Compute B = E1 * M * E2
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := E1 * M * E2
  have hE1M : ∀ i j, (E1 * M) i j = if i = 0 then ∑ r, v r else M i j := by
    intro i j
    simp only [Matrix.mul_apply, E1, Matrix.of_apply]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [↓reduceIte, one_mul, M, Matrix.add_apply, Matrix.of_apply, Finset.sum_add_distrib,
        hcol j, zero_add]
    · simp only [hi0, ↓reduceIte]
      rw [Finset.sum_eq_single i]
      · simp
      · intro r _ hri; simp [hri.symm]
      · intro h; exact absurd (Finset.mem_univ i) h
  have hB : ∀ i j, B i j =
      if i = 0 then
        if j = 0 then ((n + 1 : ℕ) : ℚ) * ∑ r, v r else ∑ r, v r
      else
        if j = 0 then ((n + 1 : ℕ) : ℚ) * v i else M i j := by
    intro i j
    simp only [B, Matrix.mul_apply, hE1M, E2, Matrix.of_apply]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [↓reduceIte, mul_one]
      by_cases hi0 : i = 0
      · subst hi0
        simp [Finset.sum_const, nsmul_eq_mul]
      · simp only [hi0, ↓reduceIte, M, Matrix.add_apply, Matrix.of_apply, Finset.sum_add_distrib,
          hrow i, zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · simp only [hj0, ↓reduceIte]
      rw [Finset.sum_eq_single j]
      · simp
      · intro r _ hrj; simp [hrj]
      · intro h; exact absurd (Finset.mem_univ j) h
  -- Compute C = B * E3: block lower triangular with (0,0) = (n+1)*∑v, row 0 (j>0) = 0, bottom-right = L.submatrix Fin.succ Fin.succ
  let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := B * E3
  have hC : ∀ i j, C i j =
      if j = 0 then
        if i = 0 then ((n + 1 : ℕ) : ℚ) * ∑ r, v r else ((n + 1 : ℕ) : ℚ) * v i
      else
        if i = 0 then 0 else L i j := by
    intro i j
    have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    simp only [C, Matrix.mul_apply, E3, Matrix.of_apply]
    by_cases hj0 : j = 0
    · subst hj0
      rw [Finset.sum_eq_single 0]
      · simp [hB]
      · intro r _ hr0; simp [hr0]
      · intro h; exact absurd (Finset.mem_univ 0) h
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
      rw [Finset.sum_eq_single j]
      · have h0j : (0 : Fin (n + 1)) ≠ j := Ne.symm hj0
        simp only [h0j, ↓reduceIte, mul_one, hB, hj0]
        by_cases hi0 : i = 0
        · subst hi0; simp only [↓reduceIte]; field_simp; ring
        · simp only [hi0, ↓reduceIte, M, Matrix.add_apply, Matrix.of_apply]; field_simp; ring
      · intro r hr hrj
        have hr0 : r ≠ 0 := Finset.ne_of_mem_erase hr
        simp [hrj, hr0]
      · intro hj_mem
        exact absurd (Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ j⟩) hj_mem
  have hdet_eq : M.det = C.det := by
    have : C.det = E1.det * M.det * E2.det * E3.det := by
      simp [C, B, Matrix.det_mul]
    rw [this, hE1_det, hE2_det, hE3_det]; ring
  rw [hdet_eq]
  -- Expand C.det along row 0 (only entry (0,0) is nonzero!)
  rw [Matrix.det_succ_row_zero C]
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, hC, ↓reduceIte]
    congr 1
    congr 1
    ext i j
    simp [Matrix.submatrix_apply, hC, Fin.succ_ne_zero]
  · intro j _ hj0
    simp [hC, hj0]
  · intro h
    exact absurd (Finset.mem_univ 0) h

/-- Sum of `degDiagKron` diagonal entries equals `∏_{r < k} (b_r * (b_r + 1) / 2)`. -/
theorem sum_degDiagKron (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) :
    ∀ k, (∑ i : Fin (place b k), ∏ r ∈ Finset.range k, ((b r - mdigit b i.1 r : ℕ) : ℚ)) =
      ∏ r ∈ Finset.range k, ((b r * (b r + 1) / 2 : ℕ) : ℚ)
  | 0 => by
    simp only [Finset.prod_range_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (Finset.univ : Finset (Fin (place b 0))).card = 1 := by
      rw [Finset.card_univ, Fintype.card_fin]; rfl
    exact_mod_cast hcard
  | k + 1 => by
    have ih := sum_degDiagKron b hb k
    let e := mixedEquiv b hb k
    rw [Fintype.sum_equiv e _ (fun p =>
      (∏ r ∈ Finset.range k, ((b r - mdigit b p.1.1 r : ℕ) : ℚ)) * ((b k - p.2.1 : ℕ) : ℚ))]
    · rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ih, Finset.prod_range_succ]
      congr 1
      have htri : (∑ j : Fin (b k), (b k - j.1)) = b k * (b k + 1) / 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun j => b k - j)]
        have hrev : ∑ j ∈ Finset.range (b k), (b k - j) = ∑ j ∈ Finset.range (b k), (j + 1) := by
          rw [← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hlt := Finset.mem_range.mp hj
          omega
        rw [hrev]
        have hsum : 2 * ∑ j ∈ Finset.range (b k), (j + 1) = b k * (b k + 1) := by
          induction (b k) with
          | zero => simp
          | succ m ihm =>
            rw [Finset.sum_range_succ, mul_add, ihm]; ring
        omega
      exact_mod_cast htri
    · intro i
      have hi : i.1 = (e i).1.1 + place b k * (e i).2.1 := by
        simpa [e, mixedEquiv] using (Nat.mod_add_div i.1 (place b k)).symm
      rw [Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl fun r hr => ?_
        rw [hi, mdigit_lo_add_mul b hb (e i).1.2 (Finset.mem_range.mp hr)]
      · rw [hi, mdigit_hi_add_mul b hb (e i).1.2 (e i).2.2]

/-- Product of `degDiagKron` diagonal entries equals `∏_{i} ∏_{r < k} (mdigit b i r + 1)`. -/
theorem prod_degDiagKron (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    (∏ i : Fin (place b k), ∏ r ∈ Finset.range k, ((b r - mdigit b i.1 r : ℕ) : ℚ)) =
      ∏ i : Fin (place b k), ∏ r ∈ Finset.range k, ((mdigit b i.1 r + 1 : ℕ) : ℚ) := by
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  refine Finset.prod_congr rfl fun r hr => ?_
  have hcomp := mdigit_complement b hb k i.1 r i.2 (Finset.mem_range.mp hr)
  have hdlt := mdigit_lt b hb i.1 r
  simp only [Fin.revPerm_apply, Fin.val_rev]
  have hsub : place b k - (i.1 + 1) = place b k - 1 - i.1 := by omega
  rw [hsub, hcomp]
  congr 2
  omega

/-! ## Section 5: Theorem 2 & Corollaries over Arbitrary Commutative Rings -/

/-- Exact cleared-denominator mixed-radix spanning-tree formula over `ℚ`. -/
theorem det_zeroCarryCofactor_mixed_rat (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    (∏ r ∈ Finset.range k, ((b r * (b r + 1) / 2 : ℕ) : ℚ)) *
      (zeroCarryCofactor (R := ℚ) b k).det =
      ∏ j : Fin (place b k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ)) -
          ∏ r ∈ Finset.range k, (-1 : ℚ) ^ mdigit b (j.1 + 1) r) := by
  have hpk_pos : 0 < place b k := place_pos b hb k
  -- Identify place b k with (place b k - 1) + 1
  set n := place b k - 1
  have hN : place b k = n + 1 := (Nat.sub_add_cancel hpk_pos).symm
  let eN : Fin (n + 1) ≃ Fin (place b k) := finCongr hN.symm
  let L : Matrix (Fin (place b k)) (Fin (place b k)) ℚ := zeroCarryLaplacian b k
  let v : Fin (place b k) → ℚ := fun i => ∏ r ∈ Finset.range k, ((b r - mdigit b i.1 r : ℕ) : ℚ)
  let M : Matrix (Fin (place b k)) (Fin (place b k)) ℚ := L + Matrix.of fun i _ => v i
  -- Step 1: Evaluate det(M) via the rank-1 Kirchhoff cofactor lemma
  have hdet_M_left :
      M.det = ((place b k : ℕ) : ℚ) * (∑ i, v i) * (zeroCarryCofactor (R := ℚ) b k).det := by
    let L' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := L.submatrix eN eN
    let v' : Fin (n + 1) → ℚ := v ∘ eN
    have hrow' : ∀ i, ∑ j, L' i j = 0 := fun i => by
      simpa [L'] using Fintype.sum_equiv eN _ _ (fun _ => rfl) |>.trans (zeroCarryLaplacian_row_sum b k (eN i))
    have hcol' : ∀ j, ∑ i, L' i j = 0 := fun j => by
      simpa [L'] using Fintype.sum_equiv eN _ _ (fun _ => rfl) |>.trans (zeroCarryLaplacian_col_sum b k (eN j))
    have hrank1 := det_add_rank1_eq_mul_cofactor L' hrow' hcol' v'
    have hsub_M : M.submatrix eN eN = L' + Matrix.of fun i _ => v' i := by
      ext i j; simp [M, L', v']
    have hdet_eq : M.det = (L' + Matrix.of fun i _ => v' i).det := by
      rw [← hsub_M, Matrix.det_submatrix_equiv_self]
    have hsum_v : ∑ i, v' i = ∑ i, v i := Fintype.sum_equiv eN v' v (fun _ => rfl)
    have hcof_eq : L'.submatrix Fin.succ Fin.succ = zeroCarryCofactor (R := ℚ) b k := by
      ext i j
      simp only [L', L, zeroCarryLaplacian, zeroCarryCofactor, Matrix.submatrix_apply,
        Matrix.of_apply, eN, finCongr_apply, Fin.val_cast, Fin.val_succ]
      have hiff : Fin.cast hN.symm i.succ = Fin.cast hN.symm j.succ ↔ i = j := by
        simp [Fin.ext_iff]
      simp only [hiff]
    rw [hdet_eq, hrank1, hsum_v, hcof_eq, ← hN]
  -- Step 2: Evaluate det(M) via Kronecker-Pascal triangularization!
  -- M * P = B * P * ((1 - U) + E0) where E0 has row 0 = 1^T * P and all other rows = 0!
  let i0 : Fin (place b k) := ⟨0, hpk_pos⟩
  let E0 : Matrix (Fin (place b k)) (Fin (place b k)) ℚ :=
    Matrix.of fun r c => if r = i0 then ∑ x : Fin (place b k), pascalKron b k x c else 0
  have hMP : M * pascalKron b k = degDiagKron b k * (pascalKron b k * ((1 - upperKron b k) + E0)) := by
    have hL : L * pascalKron b k = degDiagKron b k * (pascalKron b k * (1 - upperKron b k)) := by
      dsimp only [L]
      rw [zeroCarryLaplacian_eq_degDiag_mul_sub b hb k, Matrix.mul_assoc,
          sub_mul, one_mul, zeroCarryWalk_mul_pascalKron b hb k]
      simp [mul_sub]
    have hR : (Matrix.of fun i (_ : Fin (place b k)) => v i) * pascalKron b k =
        degDiagKron b k * (pascalKron b k * E0) := by
      ext i c
      have hrhs : (degDiagKron b k * (pascalKron b k * E0)) i c =
          v i * ∑ x : Fin (place b k), pascalKron b k x c := by
        simp only [Matrix.mul_apply, degDiagKron, Matrix.diagonal_apply]
        rw [Finset.sum_eq_single i]
        · simp only [↓reduceIte, E0, Matrix.of_apply]
          rw [Finset.sum_eq_single i0]
          · simp only [↓reduceIte]
            dsimp only [i0, v]
            rw [pascalKron_col0 b hb k i, one_mul]
          · intro j _ hj0; simp [hj0]
          · intro h; exact absurd (Finset.mem_univ i0) h
        · intro r _ hri; simp [hri.symm]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hrhs]
      simp only [Matrix.mul_apply, Matrix.of_apply, ← Finset.mul_sum]
    rw [show M = L + Matrix.of fun i _ => v i from rfl, add_mul, hL, hR, ← mul_add, ← mul_add]
  have htri_T : ((1 - upperKron b k) + E0).BlockTriangular id := by
    intro r c hcr
    have hne : r ≠ c := ne_of_gt hcr
    have hr0 : r ≠ i0 := by
      intro h; subst h; exact Nat.not_lt_zero _ hcr
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_ne hne,
          upperKron_upper b hb k hcr, E0, hr0]
  have hdet_T : ((1 - upperKron b k) + E0).det =
      ((place b k : ℕ) : ℚ) *
        ∏ j : Fin (place b k - 1),
          (1 - ∏ r ∈ Finset.range k, ((-1 : ℚ) ^ mdigit b (j.1 + 1) r / ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ))) := by
    rw [Matrix.det_of_isUpperTriangular htri_T]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
    have h00 : ((1 - upperKron b k) + E0) i0 i0 = ((place b k : ℕ) : ℚ) := by
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq, upperKron_diag,
        E0, Matrix.of_apply, ↓reduceIte]
      dsimp only [i0]
      simp only [mdigit_zero, pow_zero, zero_add, Nat.cast_one, div_one, Finset.prod_const_one,
        sub_self, zero_add, pascalKron_col0 b hb k, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [h00]
    congr 1
    symm
    refine Finset.prod_bij (fun j _ => eN (Fin.succ j)) ?_ ?_ ?_ ?_
    · intro j _
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h; have := congrArg Fin.val h; simp [eN, i0] at this
    · intro j1 _ j2 _ h
      exact Fin.succ_injective _ (eN.injective h)
    · intro j hj
      have hj0 : j ≠ i0 := (Finset.mem_erase.mp hj).1
      have hpos : 0 < j.1 := Nat.pos_of_ne_zero fun h => hj0 (Fin.ext h)
      refine ⟨⟨j.1 - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      ext; simp [eN]; omega
    · intro j _
      have hjne : eN (Fin.succ j) ≠ i0 := by
        intro h; have := congrArg Fin.val h; simp [eN, i0] at this
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq, upperKron_diag,
        E0, Matrix.of_apply, hjne, ↓reduceIte, add_zero]
      simp only [eN, finCongr_apply, Fin.val_cast, Fin.val_succ]
  have hdet_M_right :
      M.det = ((place b k : ℕ) : ℚ) *
        ∏ j : Fin (place b k - 1),
          ((∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ)) -
            ∏ r ∈ Finset.range k, (-1 : ℚ) ^ mdigit b (j.1 + 1) r) := by
    have hdet := congrArg Matrix.det hMP
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul] at hdet
    have hP := pascalKron_det_ne_zero b hb k
    have hM_eq : M.det = (degDiagKron b k).det * ((1 - upperKron b k) + E0).det := by
      have : (M.det - (degDiagKron b k).det * ((1 - upperKron b k) + E0).det) * (pascalKron b k).det = 0 := by
        linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · exact absurd h0 hP
    rw [hM_eq, hdet_T, degDiagKron, Matrix.det_diagonal, prod_degDiagKron b hb k]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
    have h0_one : (∏ r ∈ Finset.range k, ((mdigit b i0.1 r + 1 : ℕ) : ℚ)) = 1 := by
      simp [i0, mdigit_zero]
    rw [h0_one, one_mul]
    -- Reindex Finset.univ.erase i0 to Fin (place b k - 1) and merge the two products!
    have hreidx :
        (∏ j ∈ Finset.univ.erase i0, ∏ r ∈ Finset.range k, ((mdigit b j.1 r + 1 : ℕ) : ℚ)) =
        ∏ j : Fin (place b k - 1), ∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ) := by
      refine Finset.prod_bij (fun j hj => ⟨j.1 - 1, by
        have hj0 : j ≠ i0 := (Finset.mem_erase.mp hj).1
        have : 0 < j.1 := Nat.pos_of_ne_zero fun h => hj0 (Fin.ext h)
        omega⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro j1 hj1 j2 hj2 h
        have h1 : 0 < j1.1 := Nat.pos_of_ne_zero fun hz => (Finset.mem_erase.mp hj1).1 (Fin.ext hz)
        have h2 : 0 < j2.1 := Nat.pos_of_ne_zero fun hz => (Finset.mem_erase.mp hj2).1 (Fin.ext hz)
        exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
      · intro j _
        refine ⟨eN (Fin.succ j), Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · intro h; have := congrArg Fin.val h; simp [eN, i0] at this
        · ext; simp [eN]
      · intro j hj
        have h1 : 0 < j.1 := Nat.pos_of_ne_zero fun hz => (Finset.mem_erase.mp hj).1 (Fin.ext hz)
        have : j.1 - 1 + 1 = j.1 := by omega
        simp [this]
    rw [hreidx]
    calc
      (∏ j : Fin (place b k - 1), ∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ)) *
        (((place b k : ℕ) : ℚ) * ∏ j : Fin (place b k - 1),
          (1 - ∏ r ∈ Finset.range k, ((-1 : ℚ) ^ mdigit b (j.1 + 1) r / ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ))))
          = ((place b k : ℕ) : ℚ) *
              ((∏ j : Fin (place b k - 1), ∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ)) *
               (∏ j : Fin (place b k - 1),
                 (1 - ∏ r ∈ Finset.range k, ((-1 : ℚ) ^ mdigit b (j.1 + 1) r / ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ))))) := by ring
      _ = ((place b k : ℕ) : ℚ) *
            ∏ j : Fin (place b k - 1),
              ((∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ)) -
                ∏ r ∈ Finset.range k, (-1 : ℚ) ^ mdigit b (j.1 + 1) r) := by
          congr 1
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [mul_sub, mul_one, Finset.prod_div_distrib]
          have hden : (∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ)) ≠ 0 :=
            Finset.prod_ne_zero_iff.mpr fun r _ => by positivity
          rw [mul_div_cancel₀ _ hden]
  -- Equate left and right and cancel place b k > 0!
  have hcomb : ((place b k : ℕ) : ℚ) * ((∑ i, v i) * (zeroCarryCofactor (R := ℚ) b k).det) =
      ((place b k : ℕ) : ℚ) *
        ∏ j : Fin (place b k - 1),
          ((∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℚ)) -
            ∏ r ∈ Finset.range k, (-1 : ℚ) ^ mdigit b (j.1 + 1) r) := by
    linarith [hdet_M_left, hdet_M_right]
  have hpk_q : ((place b k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpk_pos.ne'
  have hfinal := mul_left_cancel₀ hpk_q hcomb
  rwa [sum_degDiagKron b hb k] at hfinal

/-- Transfer helper: `zeroCarryCofactor` over `R` is the image of `zeroCarryCofactor` over `ℤ`
under `Int.castRingHom R`. -/
theorem map_zeroCarryCofactor {R : Type*} [CommRing R] (b : ℕ → ℕ) (k : ℕ) :
    (Int.castRingHom R).mapMatrix (zeroCarryCofactor (R := ℤ) b k) = zeroCarryCofactor (R := R) b k := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, zeroCarryCofactor, Matrix.of_apply]
  split_ifs <;> simp

/-- Theorem 2 over `ℤ`. -/
theorem det_zeroCarryCofactor_mixed_int (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    (∏ r ∈ Finset.range k, ((b r * (b r + 1) / 2 : ℕ) : ℤ)) *
      (zeroCarryCofactor (R := ℤ) b k).det =
      ∏ j : Fin (place b k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : ℤ)) -
          ∏ r ∈ Finset.range k, (-1 : ℤ) ^ mdigit b (j.1 + 1) r) := by
  apply Int.cast_injective (α := ℚ)
  have hmap : ((zeroCarryCofactor (R := ℤ) b k).det : ℚ) = (zeroCarryCofactor (R := ℚ) b k).det := by
    calc ((zeroCarryCofactor (R := ℤ) b k).det : ℚ)
        = (Int.castRingHom ℚ) (zeroCarryCofactor (R := ℤ) b k).det := rfl
      _ = ((Int.castRingHom ℚ).mapMatrix (zeroCarryCofactor (R := ℤ) b k)).det :=
          RingHom.map_det (Int.castRingHom ℚ) _
      _ = (zeroCarryCofactor (R := ℚ) b k).det := by rw [map_zeroCarryCofactor]
  simp only [Int.cast_mul, Int.cast_prod, Int.cast_sub, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, hmap]
  exact det_zeroCarryCofactor_mixed_rat b hb k

/-- Theorem 2 (Exact mixed-radix zero-carry graph spanning-tree formula over ANY `CommRing R`). -/
theorem det_zeroCarryCofactor_mixed {R : Type*} [CommRing R]
    (b : ℕ → ℕ) (hb : ∀ r, 1 ≤ b r) (k : ℕ) :
    (∏ r ∈ Finset.range k, ((b r * (b r + 1) / 2 : ℕ) : R)) *
      (zeroCarryCofactor (R := R) b k).det =
      ∏ j : Fin (place b k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit b (j.1 + 1) r + 1 : ℕ) : R)) -
          ∏ r ∈ Finset.range k, (-1 : R) ^ mdigit b (j.1 + 1) r) := by
  have h := congrArg (Int.castRingHom R) (det_zeroCarryCofactor_mixed_int b hb k)
  simp only [map_mul, map_prod, map_sub, map_pow, map_neg, map_one, map_natCast,
    RingHom.map_det, map_zeroCarryCofactor] at h
  exact h

/-- Corollary 2.1 (Uniform base-`B` specialization over any `CommRing R`). -/
theorem det_zeroCarryCofactor_base {R : Type*} [CommRing R]
    (B : ℕ) (hB : 1 ≤ B) (k : ℕ) :
    (((B * (B + 1) / 2 : ℕ) : R) ^ k) *
      (zeroCarryCofactor (R := R) (fun _ => B) k).det =
      ∏ j : Fin (place (fun _ => B) k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit (fun _ => B) (j.1 + 1) r + 1 : ℕ) : R)) -
          ∏ r ∈ Finset.range k, (-1 : R) ^ mdigit (fun _ => B) (j.1 + 1) r) := by
  simpa [Finset.prod_const, Finset.card_range] using
    det_zeroCarryCofactor_mixed (R := R) (fun _ => B) (fun _ => hB) k

/-! ## Section 6: Corollary 2.2 (Binary Zero-Carry / Bitwise-Disjoint Graph) -/

private theorem testBit_eq_false_of_lt_two_pow {n r : ℕ} (h : n < 2 ^ r) : n.testBit r = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt h]
  simp

theorem mdigit_two_eq_testBit (n r : ℕ) :
    mdigit (fun _ => 2) n r = if n.testBit r then 1 else 0 := by
  unfold mdigit
  rw [place_const 2 r, Nat.testBit_eq_decide_div_mod_eq]
  have hmod : (n / 2 ^ r) % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases h : (n / 2 ^ r) % 2 = 1
  · simp [h]
  · have h0 : (n / 2 ^ r) % 2 = 0 := by omega
    simp [h0]

theorem land_eq_zero_iff_mdigit_two {k i j : ℕ} (hi : i < 2 ^ k) (_hj : j < 2 ^ k) :
    (i &&& j) = 0 ↔ ∀ r ∈ Finset.range k, mdigit (fun _ => 2) i r + mdigit (fun _ => 2) j r < 2 := by
  constructor
  · intro hand r _
    rw [mdigit_two_eq_testBit, mdigit_two_eq_testBit]
    have hbit : (i &&& j).testBit r = false := by rw [hand]; simp
    rw [Nat.testBit_and] at hbit
    cases h1 : i.testBit r <;> cases h2 : j.testBit r <;> simp_all
  · intro h
    apply Nat.eq_of_testBit_eq
    intro r
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hr : r < k
    · have hlt := h r (Finset.mem_range.mpr hr)
      rw [mdigit_two_eq_testBit, mdigit_two_eq_testBit] at hlt
      cases h1 : i.testBit r <;> cases h2 : j.testBit r <;> simp_all
    · have hge : k ≤ r := Nat.not_lt.mp hr
      have h1 : i.testBit r = false :=
        testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hge))
      simp [h1]

theorem binaryZeroCarryDeg_eq (k i : ℕ) (hi : i < 2 ^ k) :
    binaryZeroCarryDeg k i = zeroCarryDeg (fun _ => 2) k i := by
  unfold binaryZeroCarryDeg zeroCarryDeg zeroCarryAdjBool
  rw [place_const 2 k]
  congr 1
  ext j
  simp only [Finset.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hj, hne, hand⟩
    exact ⟨hj, hne, (land_eq_zero_iff_mdigit_two hi (Finset.mem_range.mp hj)).mp hand⟩
  · rintro ⟨hj, hne, hdig⟩
    exact ⟨hj, hne, (land_eq_zero_iff_mdigit_two hi (Finset.mem_range.mp hj)).mpr hdig⟩

private theorem testBit_two_pow_add_of_false {a S : ℕ} (hS : S.testBit a = false) (r : ℕ) :
    (2 ^ a + S).testBit r = ((a == r) || S.testBit r) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.testBit_eq_decide_div_mod_eq] at hS
  have hS0 : (S / 2 ^ a) % 2 = 0 := by
    have hlt : (S / 2 ^ a) % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases h1 : (S / 2 ^ a) % 2 = 1
    · simp [h1] at hS
    · omega
  rcases lt_trichotomy r a with hlt | rfl | hgt
  · have hpow : 2 ^ a = 2 ^ r * (2 * 2 ^ (a - r - 1)) := by
      have : a = r + 1 + (a - r - 1) := by omega
      conv_lhs => rw [this, pow_add, pow_add, pow_one]
      ring
    have hpos : 0 < 2 ^ r := by positivity
    have hdiv : (2 ^ a + S) / 2 ^ r = 2 * 2 ^ (a - r - 1) + S / 2 ^ r := by
      rw [hpow, Nat.mul_add_div hpos]
    rw [hdiv, Nat.mul_add_mod]
    have hne : (a == r) = false := beq_false_of_ne (ne_of_gt hlt)
    simp [hne]
  · have hpos : 0 < 2 ^ r := by positivity
    have hdiv : (2 ^ r + S) / 2 ^ r = 1 + S / 2 ^ r := by
      have : 2 ^ r + S = 2 ^ r * 1 + S := by ring
      rw [this, Nat.mul_add_div hpos]
    rw [hdiv]
    have hmod : (1 + S / 2 ^ r) % 2 = 1 := by omega
    simp [hmod]
  · have hdiv_next : (2 ^ a + S) / 2 ^ (a + 1) = S / 2 ^ (a + 1) := by
      have hpos_a : 0 < 2 ^ a := by positivity
      have h1 : (2 ^ a + S) / 2 ^ a = 1 + S / 2 ^ a := by
        have : 2 ^ a + S = 2 ^ a * 1 + S := by ring
        rw [this, Nat.mul_add_div hpos_a]
      rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h1]
      omega
    have hdiv_r : (2 ^ a + S) / 2 ^ r = S / 2 ^ r := by
      have hr : r = (a + 1) + (r - (a + 1)) := by omega
      rw [hr, pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv_next]
    rw [hdiv_r]
    have hne : (a == r) = false := beq_false_of_ne (ne_of_lt hgt)
    simp [hne]

/-- Number of `j ∈ [0, 2^k)` with exactly `m` set bits among positions `< k` is `k.choose m`. -/
theorem card_fin_bitcount (k m : ℕ) :
    (Finset.univ.filter (fun j : Fin (2 ^ k) =>
      ((Finset.range k).filter (fun r => j.1.testBit r = true)).card = m)).card = k.choose m := by
  -- Bijection with powersetCard m (range k) via j ↦ {r < k | j.testBit r}
  conv_rhs => rw [← Finset.card_range k, ← Finset.card_powersetCard m (Finset.range k)]
  refine Finset.card_bij (fun j _ => (Finset.range k).filter (fun r => j.1.testBit r = true))
    ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, (Finset.mem_filter.mp hj).2⟩
  · intro j1 _ j2 _ heq
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro r
    by_cases hr : r < k
    · have hiff : r ∈ (Finset.range k).filter (fun r => j1.1.testBit r = true) ↔
                  r ∈ (Finset.range k).filter (fun r => j2.1.testBit r = true) := by rw [heq]
      simp only [Finset.mem_filter, Finset.mem_range, hr, true_and] at hiff
      cases h1 : j1.1.testBit r <;> cases h2 : j2.1.testBit r <;> simp_all
    · have hge : k ≤ r := Nat.not_lt.mp hr
      rw [testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le j1.2 (Nat.pow_le_pow_right (by omega) hge)),
          testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le j2.2 (Nat.pow_le_pow_right (by omega) hge))]
  · intro s hs
    rcases Finset.mem_powersetCard.mp hs with ⟨hsub, hcard⟩
    let val : ℕ := ∑ r ∈ s, 2 ^ r
    have hval_lt : val < 2 ^ k := by
      calc val = ∑ r ∈ s, 2 ^ r := rfl
        _ ≤ ∑ r ∈ Finset.range k, 2 ^ r := Finset.sum_le_sum_of_subset hsub
        _ < 2 ^ k := by
          have hsum_pow : ∀ n, ∑ r ∈ Finset.range n, 2 ^ r + 1 = 2 ^ n := fun n => by
            induction n with
            | zero => simp
            | succ t iht => rw [Finset.sum_range_succ, pow_succ]; omega
          have := hsum_pow k
          omega
    have hbit : ∀ r, val.testBit r = decide (r ∈ s) := by
      have hgen : ∀ (t : Finset ℕ) (r : ℕ), (∑ u ∈ t, 2 ^ u).testBit r = decide (r ∈ t) := by
        intro t
        induction t using Finset.induction_on with
        | empty => intro r; simp
        | insert a t ha ih =>
          intro r
          rw [Finset.sum_insert ha]
          have hS : (∑ v ∈ t, 2 ^ v).testBit a = false := by
            rw [ih, decide_eq_false ha]
          rw [testBit_two_pow_add_of_false hS r, ih]
          by_cases hra : a = r
          · subst hra; simp
          · simp [hra, Ne.symm hra]
      exact hgen s
    refine ⟨⟨val, hval_lt⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hfeq : (Finset.range k).filter (fun r => val.testBit r = true) = s := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range, hbit, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun hr => ⟨Finset.mem_range.mp (hsub hr), hr⟩⟩
      rw [hfeq, hcard]
    · ext r
      simp only [Finset.mem_filter, Finset.mem_range, hbit, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun hr => ⟨Finset.mem_range.mp (hsub hr), hr⟩⟩

/-- Corollary 2.2 over `ℤ` (cancelling `3^k` in `ℤ`). -/
theorem det_binaryZeroCarryCofactor_int (k : ℕ) :
    (binaryZeroCarryCofactor (R := ℤ) k).det =
      ∏ m ∈ Finset.Ico 2 (k + 1),
        ((2 : ℤ) ^ m - (-1 : ℤ) ^ m) ^ (k.choose m) := by
  have hbase := det_zeroCarryCofactor_base (R := ℤ) 2 (by omega) k
  let e2 : Fin (2 ^ k - 1) ≃ Fin (place (fun _ => 2) k - 1) :=
    finCongr (by rw [place_const 2 k])
  have he2_val : ∀ x : Fin (2 ^ k - 1), (e2 x).1 = x.1 := fun _ => rfl
  have hmat : binaryZeroCarryCofactor (R := ℤ) k =
      (zeroCarryCofactor (R := ℤ) (fun _ => 2) k).submatrix e2 e2 := by
    ext i j
    simp only [binaryZeroCarryCofactor, zeroCarryCofactor, Matrix.submatrix_apply,
      Matrix.of_apply, he2_val]
    have hiff : e2 i = e2 j ↔ i = j := e2.injective.eq_iff
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      have hilt : i.1 + 1 < 2 ^ k := by have := i.2; omega
      rw [binaryZeroCarryDeg_eq k (i.1 + 1) hilt]
    · simp only [hij, hiff, ↓reduceIte]
      have hilt : i.1 + 1 < 2 ^ k := by have := i.2; omega
      have hjlt : j.1 + 1 < 2 ^ k := by have := j.2; omega
      unfold zeroCarryAdjBool
      have hne : i.1 + 1 ≠ j.1 + 1 := fun h => hij (Fin.ext (by omega))
      by_cases hand : (i.1 + 1) &&& (j.1 + 1) = 0
      · have htrue : decide (i.1 + 1 ≠ j.1 + 1 ∧
            ∀ r ∈ Finset.range k, mdigit (fun _ => 2) (i.1 + 1) r + mdigit (fun _ => 2) (j.1 + 1) r < 2) = true :=
          decide_eq_true ⟨hne, (land_eq_zero_iff_mdigit_two hilt hjlt).mp hand⟩
        simp only [hand, htrue, ↓reduceIte]
      · have hfalse : decide (i.1 + 1 ≠ j.1 + 1 ∧
            ∀ r ∈ Finset.range k, mdigit (fun _ => 2) (i.1 + 1) r + mdigit (fun _ => 2) (j.1 + 1) r < 2) = false :=
          decide_eq_false (fun h => hand ((land_eq_zero_iff_mdigit_two hilt hjlt).mpr h.2))
        simp only [hand, hfalse, ↓reduceIte]
        simp
  have hdet_eq : (binaryZeroCarryCofactor (R := ℤ) k).det =
      (zeroCarryCofactor (R := ℤ) (fun _ => 2) k).det := by
    rw [hmat, Matrix.det_submatrix_equiv_self]
  -- Evaluate the RHS product in hbase by grouping over popcount m ∈ Ico 1 (k + 1)
  have hrhs_eval :
      (∏ j : Fin (place (fun _ => 2) k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit (fun _ => 2) (j.1 + 1) r + 1 : ℕ) : ℤ)) -
          ∏ r ∈ Finset.range k, (-1 : ℤ) ^ mdigit (fun _ => 2) (j.1 + 1) r)) =
      (3 : ℤ) ^ k * ∏ m ∈ Finset.Ico 2 (k + 1), ((2 : ℤ) ^ m - (-1 : ℤ) ^ m) ^ (k.choose m) := by
    -- Express each factor in terms of popcount w(j+1) = ((range k).filter testBit).card
    have hfactor : ∀ j : Fin (place (fun _ => 2) k - 1),
        ((∏ r ∈ Finset.range k, ((mdigit (fun _ => 2) (j.1 + 1) r + 1 : ℕ) : ℤ)) -
          ∏ r ∈ Finset.range k, (-1 : ℤ) ^ mdigit (fun _ => 2) (j.1 + 1) r) =
        (2 : ℤ) ^ ((Finset.range k).filter (fun r => (j.1 + 1).testBit r = true)).card -
          (-1 : ℤ) ^ ((Finset.range k).filter (fun r => (j.1 + 1).testBit r = true)).card := by
      intro j
      congr 1
      · calc (∏ r ∈ Finset.range k, ((mdigit (fun _ => 2) (j.1 + 1) r + 1 : ℕ) : ℤ))
            = ∏ r ∈ Finset.range k, (if (j.1 + 1).testBit r = true then (2 : ℤ) else 1) := by
              refine Finset.prod_congr rfl fun r _ => ?_
              rw [mdigit_two_eq_testBit]; split_ifs <;> norm_num
          _ = (2 : ℤ) ^ ((Finset.range k).filter (fun r => (j.1 + 1).testBit r = true)).card := by
              rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      · calc (∏ r ∈ Finset.range k, (-1 : ℤ) ^ mdigit (fun _ => 2) (j.1 + 1) r)
            = ∏ r ∈ Finset.range k, (if (j.1 + 1).testBit r = true then (-1 : ℤ) else 1) := by
              refine Finset.prod_congr rfl fun r _ => ?_
              rw [mdigit_two_eq_testBit]; split_ifs <;> norm_num
          _ = (-1 : ℤ) ^ ((Finset.range k).filter (fun r => (j.1 + 1).testBit r = true)).card := by
              rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    simp_rw [hfactor]
    -- Group Fin (2^k - 1) by weight m ∈ Finset.Ico 1 (k + 1)
    let wt : Fin (place (fun _ => 2) k - 1) → ℕ :=
      fun j => ((Finset.range k).filter (fun r => (j.1 + 1).testBit r = true)).card
    have hwt_mem : ∀ j ∈ (Finset.univ : Finset (Fin (place (fun _ => 2) k - 1))),
        wt j ∈ Finset.Ico 1 (k + 1) := by
      intro j _
      rw [Finset.mem_Ico]
      constructor
      · refine Finset.card_pos.mpr ?_
        have hj1 : j.1 < 2 ^ k - 1 := by simpa [place_const] using j.2
        have hlt : j.1 + 1 < 2 ^ k := by omega
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hzero : j.1 + 1 = 0 := by
          apply Nat.eq_of_testBit_eq; intro r
          rw [Nat.zero_testBit]
          by_cases hr : r < k
          · cases h : (j.1 + 1).testBit r
            · rfl
            · have hm : r ∈ (Finset.range k).filter (fun r => (j.1 + 1).testBit r = true) :=
                Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, h⟩
              rw [hne] at hm; simp at hm
          · exact testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hr)))
        omega
      · exact Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by rw [Finset.card_range]))
    change (∏ j : Fin (place (fun _ => 2) k - 1), ((2 : ℤ) ^ wt j - (-1 : ℤ) ^ wt j)) = _
    rw [← Finset.prod_fiberwise_of_maps_to hwt_mem (fun j => (2 : ℤ) ^ wt j - (-1 : ℤ) ^ wt j)]
    have hfiber : ∀ m ∈ Finset.Ico 1 (k + 1),
        (∏ j ∈ Finset.univ.filter (fun j : Fin (place (fun _ => 2) k - 1) => wt j = m),
          ((2 : ℤ) ^ wt j - (-1 : ℤ) ^ wt j)) =
        ((2 : ℤ) ^ m - (-1 : ℤ) ^ m) ^ (k.choose m) := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
      rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.prod_const]
      congr 1
      rw [← card_fin_bitcount k m]
      refine Finset.card_bij (fun j _ => ⟨j.1 + 1, by
        have hj1 : j.1 < 2 ^ k - 1 := by simpa [place_const] using j.2
        omega⟩)
        ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_filter.mp hj).2
      · intro a _ c _ h; exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
      · intro x hx
        have hcard := (Finset.mem_filter.mp hx).2
        have hx0 : 0 < x.1 := by
          by_contra h0
          have hxzero : x.1 = 0 := by omega
          simp [hxzero] at hcard
          omega
        refine ⟨⟨x.1 - 1, by rw [place_const 2 k]; have := x.2; omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, wt]
          have : x.1 - 1 + 1 = x.1 := by omega
          simpa [this] using hcard
        · ext; dsimp; omega
    rw [Finset.prod_congr rfl hfiber]
    cases k with
    | zero => simp
    | succ k' =>
      have hmem1 : 1 ∈ Finset.Ico 1 (k' + 1 + 1) := Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩
      rw [← Finset.mul_prod_erase _ _ hmem1]
      have herase : (Finset.Ico 1 (k' + 1 + 1)).erase 1 = Finset.Ico 2 (k' + 1 + 1) := by
        ext m; simp only [Finset.mem_erase, Finset.mem_Ico]; omega
      rw [herase]
      simp [Nat.choose_one_right]
  have hcomb : (3 : ℤ) ^ k * (binaryZeroCarryCofactor (R := ℤ) k).det =
      (3 : ℤ) ^ k * ∏ m ∈ Finset.Ico 2 (k + 1), ((2 : ℤ) ^ m - (-1 : ℤ) ^ m) ^ (k.choose m) := by
    rw [hdet_eq, ← hrhs_eval]
    simpa using hbase
  have h3ne : (3 : ℤ) ^ k ≠ 0 := by positivity
  exact mul_left_cancel₀ h3ne hcomb

theorem map_binaryZeroCarryCofactor {R : Type*} [CommRing R] (k : ℕ) :
    (Int.castRingHom R).mapMatrix (binaryZeroCarryCofactor (R := ℤ) k) = binaryZeroCarryCofactor (R := R) k := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, binaryZeroCarryCofactor, Matrix.of_apply]
  split_ifs <;> simp

/-- Corollary 2.2 (Binary zero-carry / bitwise-disjoint graph spanning-tree formula over ANY `CommRing R`). -/
theorem det_binaryZeroCarryCofactor {R : Type*} [CommRing R] (k : ℕ) :
    (binaryZeroCarryCofactor (R := R) k).det =
      ∏ m ∈ Finset.Ico 2 (k + 1),
        ((2 : R) ^ m - (-1 : R) ^ m) ^ (k.choose m) := by
  have h := congrArg (Int.castRingHom R) (det_binaryZeroCarryCofactor_int k)
  simp only [map_prod, map_pow, map_sub, map_neg, map_one, map_ofNat,
    RingHom.map_det, map_binaryZeroCarryCofactor] at h
  exact h

/-- Corollary 2.3 (Single-radix `k = 1` threshold half-graph spanning-tree formula). -/
theorem det_singleRadixZeroCarryCofactor {R : Type*} [CommRing R] (B : ℕ) (hB : 1 ≤ B) :
    ((B * (B + 1) / 2 : ℕ) : R) *
      (zeroCarryCofactor (R := R) (fun _ => B) 1).det =
      ∏ j ∈ Finset.Ico 1 B, (((j + 1 : ℕ) : R) - (-1 : R) ^ j) := by
  have h := det_zeroCarryCofactor_base (R := R) B hB 1
  have hB1 : place (fun _ => B) 1 = B := by simp [place]
  simp only [pow_one, Finset.prod_range_one] at h
  rw [h]
  refine Finset.prod_bij (fun j _ => j.1 + 1) ?_ ?_ ?_ ?_
  · intro j _
    rw [Finset.mem_Ico]
    have hj : j.1 < B - 1 := by simpa [hB1] using j.2
    omega
  · intro a _ c _ heq; exact Fin.ext (by omega)
  · intro m hm
    rcases Finset.mem_Ico.mp hm with ⟨hm1, hmB⟩
    refine ⟨⟨m - 1, by rw [hB1]; omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  · intro j _
    have hj : j.1 < B - 1 := by simpa [hB1] using j.2
    have hjlt : j.1 + 1 < B := by omega
    have hdig : mdigit (fun _ => B) (j.1 + 1) 0 = j.1 + 1 := by
      simp [mdigit, place, Nat.mod_eq_of_lt hjlt]
    rw [hdig]

end ZeroCarrySpanningTrees
