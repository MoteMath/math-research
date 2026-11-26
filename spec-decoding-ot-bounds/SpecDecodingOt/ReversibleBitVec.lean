/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecodingOt.RatHelpers

/-!
# Theorems 5 & 6: Bit-Exact Modular `BitVec b` Reversible Transformers & Symplectic Instability

Pure-`Init` Lean 4 proofs (zero Mathlib):
1. `modular_bitvec_reversible_exact_inverse`:
   For ALL bit-widths `b : Nat`, ALL depths `L : Nat`, ALL layer functions
   `F G : Fin L → BitVec b → BitVec b`, and ALL initial states `s : BitVec b × BitVec b`:
   `revPass L F G (fwdPass L F G s) = s` AND `fwdPass L F G (revPass L F G s) = s`
   **bit-for-bit identically**, through arbitrary `2^b` two's-complement wrap-arounds.
2. `symplectic_float_reversible_unimodular`:
   For ALL `γ : Rat` and ALL `n : Nat`, the `2 × 2` symplectic coupling Jacobian
   `M(γ) = [[1 + γ², γ], [γ, 1]]` satisfies:
   - `det M(γ) = 1` and `det (M(γ)^n) = 1`
   - `tr M(γ) = 2 + γ²` (strictly hyperbolic `> 2` whenever `γ ≠ 0`)
   - `(M(γ)^n)_{0,0} ≥ 1 + n * γ²` for all `γ : Rat`
   - Exponential `ℓ_∞` row-sum growth `(M(γ)^n)_{0,0} + (M(γ)^n)_{0,1} ≥ (1 + γ)^n` for all `0 ≤ γ`.
-/

namespace SpecDecodingOt

/-! ## Theorem 5: Unconditional Bit-Exact Modular `BitVec b` Reversibility -/

private theorem revLayer_inv_fwd {b : Nat} (f g : BitVec b → BitVec b) (s : BitVec b × BitVec b) :
    revLayerInv f g (revLayerFwd f g s) = s := by
  rcases s with ⟨x, y⟩
  simp only [revLayerFwd, revLayerInv]
  have h1 : ∀ u v : BitVec b, u + v - v = u := by
    intro u v
    grind
  rw [h1, h1]

private theorem revLayer_fwd_inv {b : Nat} (f g : BitVec b → BitVec b) (s : BitVec b × BitVec b) :
    revLayerFwd f g (revLayerInv f g s) = s := by
  rcases s with ⟨x, y⟩
  simp only [revLayerFwd, revLayerInv, BitVec.sub_add_cancel]

theorem modular_bitvec_reversible_exact_inverse (b L : Nat)
    (F G : Fin L → BitVec b → BitVec b) (s : BitVec b × BitVec b) :
    revPass L F G (fwdPass L F G s) = s ∧ fwdPass L F G (revPass L F G s) = s := by
  induction L generalizing s with
  | zero =>
    exact ⟨rfl, rfl⟩
  | succ L ih =>
    constructor
    · simp only [fwdPass, revPass, revLayer_inv_fwd]
      exact (ih (fun i => F i.castSucc) (fun i => G i.castSucc) s).1
    · simp only [fwdPass, revPass]
      rw [(ih (fun i => F i.castSucc) (fun i => G i.castSucc)
        (revLayerInv (F (Fin.last L)) (G (Fin.last L)) s)).2]
      exact revLayer_fwd_inv (F (Fin.last L)) (G (Fin.last L)) s

/-! ## Theorem 6: Symplectic `2 × 2` Floating-Point Reversible Jacobian Laws -/

private theorem mat2Det_mul (A B : Mat2) : mat2Det (mat2Mul A B) = mat2Det A * mat2Det B := by
  unfold mat2Det mat2Mul
  grind

private theorem symplecticM_det (γ : Rat) : mat2Det (symplecticM γ) = 1 := by
  unfold mat2Det symplecticM
  grind

private theorem symplecticM_pow_det (γ : Rat) (n : Nat) :
    mat2Det (mat2Pow (symplecticM γ) n) = 1 := by
  induction n with
  | zero =>
    unfold mat2Pow mat2Det mat2Id
    grind
  | succ k ih =>
    simp only [mat2Pow]
    rw [mat2Det_mul, ih, symplecticM_det]
    grind

private theorem symplecticM_pow_invariants (γ : Rat) (n : Nat) :
    1 + (n : Rat) * (γ * γ) ≤ (mat2Pow (symplecticM γ) n).a00 ∧
    0 ≤ (mat2Pow (symplecticM γ) n).a01 * γ := by
  induction n with
  | zero =>
    unfold mat2Pow mat2Id
    constructor
    · have h0 : ((0 : Nat) : Rat) = 0 := rfl
      rw [h0]
      have h1 : 1 + 0 * (γ * γ) = 1 := by grind
      rw [h1]; exact Rat.le_refl
    · have h0 : (0 : Rat) * γ = 0 := by grind
      rw [h0]; exact Rat.le_refl
  | succ k ih =>
    rcases ih with ⟨ha00, ha01⟩
    let M := mat2Pow (symplecticM γ) k
    have hM00_ge1 : 1 ≤ M.a00 := by
      have hnn : 0 ≤ (k : Rat) * (γ * γ) := rat_mul_nonneg (rat_natCast_nonneg k) (rat_sq_nonneg γ)
      have h1 : 1 ≤ 1 + (k : Rat) * (γ * γ) := by
        apply rat_le_of_sub_nonneg
        have : (1 + (k : Rat) * (γ * γ)) - 1 = (k : Rat) * (γ * γ) := by grind
        rw [this]; exact hnn
      exact Rat.le_trans h1 ha00
    have hM00_nonneg : 0 ≤ M.a00 := Rat.le_trans (by decide) hM00_ge1
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      rw [Rat.natCast_add]; rfl
    constructor
    · change 1 + ((k + 1 : Nat) : Rat) * (γ * γ) ≤ M.a00 * (1 + γ * γ) + M.a01 * γ
      rw [hcast]
      apply rat_le_of_sub_nonneg
      have hEq : (M.a00 * (1 + γ * γ) + M.a01 * γ) - (1 + ((k : Rat) + 1) * (γ * γ)) =
          (M.a00 - (1 + (k : Rat) * (γ * γ))) + (M.a00 - 1) * (γ * γ) + M.a01 * γ := by grind
      rw [hEq]
      have hz : (0 : Rat) + 0 + 0 = 0 := by grind
      rw [← hz]
      exact rat_add_le_add
        (rat_add_le_add (rat_sub_nonneg_of_le ha00)
          (rat_mul_nonneg (rat_sub_nonneg_of_le hM00_ge1) (rat_sq_nonneg γ)))
        ha01
    · change 0 ≤ (M.a00 * γ + M.a01 * 1) * γ
      have hEq : (M.a00 * γ + M.a01 * 1) * γ = M.a00 * (γ * γ) + M.a01 * γ := by grind
      rw [hEq]
      have hz : (0 : Rat) + 0 = 0 := by grind
      rw [← hz]
      exact rat_add_le_add (rat_mul_nonneg hM00_nonneg (rat_sq_nonneg γ)) ha01

private theorem symplecticM_pow_exp_growth {γ : Rat} (hγ : 0 ≤ γ) (n : Nat) :
    ratPow (1 + γ) n ≤ (mat2Pow (symplecticM γ) n).a00 + (mat2Pow (symplecticM γ) n).a01 := by
  induction n with
  | zero =>
    simp only [mat2Pow, mat2Id, ratPow]
    have h1 : (1 : Rat) + 0 = 1 := by grind
    rw [h1]; exact Rat.le_refl
  | succ k ih =>
    let M := mat2Pow (symplecticM γ) k
    have hM00_nonneg : 0 ≤ M.a00 := by
      have ha00 := (symplecticM_pow_invariants γ k).1
      have hnn : 0 ≤ 1 + (k : Rat) * (γ * γ) := by
        have hz : (0 : Rat) + 0 = 0 := by grind
        rw [← hz]; exact rat_add_le_add (by decide) (rat_mul_nonneg (rat_natCast_nonneg k) (rat_sq_nonneg γ))
      exact Rat.le_trans hnn ha00
    have h1γ : 0 ≤ 1 + γ := by
      have hz : (0 : Rat) + 0 = 0 := by grind
      rw [← hz]; exact rat_add_le_add (by decide) hγ
    simp only [ratPow]
    change ratPow (1 + γ) k * (1 + γ) ≤
      (M.a00 * (1 + γ * γ) + M.a01 * γ) + (M.a00 * γ + M.a01 * 1)
    have hstep : ratPow (1 + γ) k * (1 + γ) ≤ (M.a00 + M.a01) * (1 + γ) :=
      Rat.mul_le_mul_of_nonneg_right ih h1γ
    have hge : (M.a00 + M.a01) * (1 + γ) ≤
        (M.a00 * (1 + γ * γ) + M.a01 * γ) + (M.a00 * γ + M.a01 * 1) := by
      apply rat_le_of_sub_nonneg
      have hEq : ((M.a00 * (1 + γ * γ) + M.a01 * γ) + (M.a00 * γ + M.a01 * 1)) -
          (M.a00 + M.a01) * (1 + γ) = M.a00 * (γ * γ) := by grind
      rw [hEq]
      exact rat_mul_nonneg hM00_nonneg (rat_sq_nonneg γ)
    exact Rat.le_trans hstep hge

theorem symplectic_float_reversible_unimodular (γ : Rat) (n : Nat) :
    mat2Det (symplecticM γ) = 1 ∧
    mat2Det (mat2Pow (symplecticM γ) n) = 1 ∧
    mat2Trace (symplecticM γ) = 2 + γ * γ ∧
    (γ ≠ 0 → 2 < mat2Trace (symplecticM γ)) ∧
    1 + (n : Rat) * (γ * γ) ≤ (mat2Pow (symplecticM γ) n).a00 ∧
    (0 ≤ γ → ratPow (1 + γ) n ≤ (mat2Pow (symplecticM γ) n).a00 + (mat2Pow (symplecticM γ) n).a01) := by
  refine ⟨symplecticM_det γ, symplecticM_pow_det γ n, ?_, ?_,
    (symplecticM_pow_invariants γ n).1, ?_⟩
  · unfold mat2Trace symplecticM; grind
  · intro hne
    unfold mat2Trace symplecticM
    have hsq_pos : 0 < γ * γ := by
      cases @Rat.le_total 0 γ with
      | inl h0 =>
        have hpos : 0 < γ := Rat.lt_iff_le_and_ne.mpr ⟨h0, hne.symm⟩
        exact rat_mul_pos hpos hpos
      | inr h0 =>
        have hneg : γ < 0 := Rat.lt_iff_le_and_ne.mpr ⟨h0, hne⟩
        have hnpos : 0 < -γ := by
          rw [Rat.lt_iff_le_and_ne]
          refine ⟨?_, ?_⟩
          · apply rat_le_of_sub_nonneg
            have hEq : -γ - 0 = 0 - γ := by grind
            rw [hEq]; exact rat_sub_nonneg_of_le h0
          · intro h; apply hne; grind
        have hmul := rat_mul_pos hnpos hnpos
        have hEq : (-γ) * (-γ) = γ * γ := by grind
        rw [hEq] at hmul; exact hmul
    have hadd := rat_add_lt_add_of_le_of_lt (Rat.le_refl (a := (2 : Rat))) hsq_pos
    have hL : (2 : Rat) + 0 = 2 := by grind
    have hR : 1 + γ * γ + 1 = 2 + γ * γ := by grind
    rw [hL] at hadd; rw [hR]; exact hadd
  · intro hγ
    exact symplecticM_pow_exp_growth hγ n

end SpecDecodingOt
