/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OctonionRopeWelch.Defs

/-!
# Theorem 2: Exact 2D Pythagorean, 4D Quaternion, and 8D Cayley–Dickson Octonion RoPE

Proves:
1. Universal 2D Pythagorean RoPE orthogonality over `Int` and `Rat`:
   `R_2(a, b)^T R_2(a, b) = (a^2 + b^2)^2 I_2`, and `(R_2(a, b) / (a^2 + b^2))^T (...) = I_2`
   whenever `a^2 + b^2 ≠ 0`.
2. Universal 4D Hamilton quaternion left-multiplication orthogonality:
   `L_H(a, b, c, d)^T L_H(a, b, c, d) = (a^2 + b^2 + c^2 + d^2) I_4`.
3. Universal 8D Cayley–Dickson octonion left-multiplication orthogonality:
   `L_O(x)^T L_O(x) = (∑ i : Fin 8, (x i)^2) I_8` for ALL `x : Fin 8 → Int`.
4. Concrete Llama-2 (`θ_0 = 1.0`) power-of-2 octonion RoPE witness (`>> 16` pure bit-shift,
   zero division): `x = [35409, 1, 7787, 7822, 54031, 0, 0, 0]` has `∑ (x i)^2 = (2^16)^2`
   and `(L_O(x) / 2^16)^T (L_O(x) / 2^16) = I_8` over `Rat`.
-/

namespace OctonionRopeWelch

/-- Universal 2D Pythagorean RoPE integer orthogonality. -/
theorem pythagoreanRoPE_orthogonal (a b : Int) :
    isOrthogonal (pythagoreanRoPE a b) ((a * a + b * b) * (a * a + b * b)) := by
  funext i j
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  have hi' : i = 0 ∨ i = 1 := by omega
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
  · simp only [matMul, transpose, pythagoreanRoPE, scaleMat, idMat, sumInt, Fin.castSucc]
    grind

private theorem rat_inv_mul_inv (a b : Rat) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have hab : a * b ≠ 0 := by
    intro h
    rcases Rat.mul_eq_zero.mp h with h1 | h1
    · exact ha h1
    · exact hb h1
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    have : (a * b) * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ := by grind
    rw [this, Rat.mul_inv_cancel b hb, Rat.mul_one, Rat.mul_inv_cancel a ha]
  have h2 := congrArg (fun z => (a * b)⁻¹ * z) h1
  have hL : (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹)) = b⁻¹ * a⁻¹ := by
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel (a * b) hab, Rat.one_mul]
  rw [hL, Rat.mul_one] at h2
  exact h2.symm

private theorem rat_div_mul_div (x y d : Rat) (hd : d ≠ 0) :
    (x / d) * (y / d) = (x * y) / (d * d) := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def, rat_inv_mul_inv d d hd hd]
  grind

private theorem sumRat_div {n : Nat} (f : Fin n → Rat) (d : Rat) :
    sumRat (fun i => f i / d) = sumRat f / d := by
  induction n with
  | zero => simp [sumRat, Rat.div_def]
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc)]
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]

private theorem intCast_sumInt {n : Nat} (f : Fin n → Int) :
    ((sumInt f : Int) : Rat) = sumRat (fun i => (f i : Rat)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt, sumRat, Rat.intCast_add]
    rw [ih (fun i => f i.castSucc)]

/-- Lifting integer orthogonality `A^T A = (M * M) I_n` (`M ≠ 0`) to exact rational
    orthogonality `(A / M)^T (A / M) = I_n`. -/
theorem ratOrthogonal_of_intOrthogonal {m n : Nat} (A : IntMat m n) (M : Int) (hM : M ≠ 0)
    (horth : isOrthogonal A (M * M)) :
    isRatOrthogonal (fun i j => ((A i j : Int) : Rat) / (M : Rat)) := by
  have hMr : (M : Rat) ≠ 0 := by
    intro h
    exact hM (Rat.intCast_inj.mp h)
  have hM2 : (M : Rat) * (M : Rat) ≠ 0 := by
    intro h
    rcases Rat.mul_eq_zero.mp h with h1 | h1 <;> exact hMr h1
  funext i j
  simp only [ratMatMul, ratTranspose, ratIdMat]
  have hstep :
      sumRat (fun t => ((A t i : Int) : Rat) / (M : Rat) * (((A t j : Int) : Rat) / (M : Rat))) =
      sumRat (fun t => (((A t i * A t j : Int) : Rat)) / ((M : Rat) * (M : Rat))) := by
    congr 1
    funext t
    rw [rat_div_mul_div _ _ _ hMr, Rat.intCast_mul]
  rw [hstep, sumRat_div, ← intCast_sumInt]
  have hij : sumInt (fun t => A t i * A t j) = M * M * (if i = j then 1 else 0) := by
    have h := congrFun (congrFun horth i) j
    simpa [matMul, transpose, scaleMat, idMat] using h
  rw [hij]
  by_cases hEq : i = j
  · subst hEq
    simp only [ite_true, Int.mul_one, Rat.intCast_mul, Rat.div_def]
    exact Rat.mul_inv_cancel _ hM2
  · simp only [hEq, ite_false, Int.mul_zero, Rat.intCast_zero, Rat.div_def, Rat.zero_mul]

/-- Universal 2D Pythagorean RoPE exact rational orthogonality whenever `a^2 + b^2 ≠ 0`. -/
theorem pythagoreanRoPERat_orthogonal (a b : Int) (h : a * a + b * b ≠ 0) :
    isRatOrthogonal (pythagoreanRoPERat a b) :=
  ratOrthogonal_of_intOrthogonal (pythagoreanRoPE a b) (a * a + b * b) h
    (pythagoreanRoPE_orthogonal a b)

/-- Universal 4D Hamilton quaternion left-multiplication orthogonality. -/
theorem quaternionLeft_orthogonal (a b c d : Int) :
    isOrthogonal (quaternionLeft a b c d) (a * a + b * b + c * c + d * d) := by
  funext i j
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi' with rfl | rfl | rfl | rfl <;>
  rcases hj' with rfl | rfl | rfl | rfl <;>
  · simp only [matMul, transpose, quaternionLeft, scaleMat, idMat, sumInt, Fin.castSucc]
    grind

private theorem sumInt8_expand (f : Fin 8 → Int) :
    sumInt f =
      f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
      f ⟨4, by decide⟩ + f ⟨5, by decide⟩ + f ⟨6, by decide⟩ + f ⟨7, by decide⟩ := by
  simp only [sumInt, Fin.castSucc, Fin.castAdd, Fin.castLE, Int.zero_add]

private def octEntry (a b c d e f g h : Int) (i j : Nat) : Int :=
  match i with
  | 0 => match j with | 0 => a | 1 => -b | 2 => -c | 3 => -d | 4 => -e | 5 => -f | 6 => -g | 7 => -h | _ => 0
  | 1 => match j with | 0 => b | 1 => a  | 2 => -d | 3 => c  | 4 => -f | 5 => e  | 6 => h  | 7 => -g | _ => 0
  | 2 => match j with | 0 => c | 1 => d  | 2 => a  | 3 => -b | 4 => -g | 5 => -h | 6 => e  | 7 => f  | _ => 0
  | 3 => match j with | 0 => d | 1 => -c | 2 => b  | 3 => a  | 4 => -h | 5 => g  | 6 => -f | 7 => e  | _ => 0
  | 4 => match j with | 0 => e | 1 => f  | 2 => g  | 3 => h  | 4 => a  | 5 => -b | 6 => -c | 7 => -d | _ => 0
  | 5 => match j with | 0 => f | 1 => -e | 2 => h  | 3 => -g | 4 => b  | 5 => a  | 6 => d  | 7 => -c | _ => 0
  | 6 => match j with | 0 => g | 1 => -h | 2 => -e | 3 => f  | 4 => c  | 5 => -d | 6 => a  | 7 => b  | _ => 0
  | 7 => match j with | 0 => h | 1 => g  | 2 => -f | 3 => -e | 4 => d  | 5 => c  | 6 => -b | 7 => a  | _ => 0
  | _ => 0

private def octDot (a b c d e f g h : Int) (i j : Nat) : Int :=
  octEntry a b c d e f g h 0 i * octEntry a b c d e f g h 0 j +
  octEntry a b c d e f g h 1 i * octEntry a b c d e f g h 1 j +
  octEntry a b c d e f g h 2 i * octEntry a b c d e f g h 2 j +
  octEntry a b c d e f g h 3 i * octEntry a b c d e f g h 3 j +
  octEntry a b c d e f g h 4 i * octEntry a b c d e f g h 4 j +
  octEntry a b c d e f g h 5 i * octEntry a b c d e f g h 5 j +
  octEntry a b c d e f g h 6 i * octEntry a b c d e f g h 6 j +
  octEntry a b c d e f g h 7 i * octEntry a b c d e f g h 7 j

private theorem octCol0 (a b c d e f g h : Int) (j : Nat) (hj : j < 8) :
    octDot a b c d e f g h 0 j =
      (a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) * (if 0 = j then 1 else 0) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp only [octDot, octEntry]; grind
  | _ + 8 => omega

private theorem octCol1 (a b c d e f g h : Int) (j : Nat) (hj : j < 8) :
    octDot a b c d e f g h 1 j =
      (a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) * (if 1 = j then 1 else 0) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp only [octDot, octEntry]; grind
  | _ + 8 => omega

private theorem octCol2 (a b c d e f g h : Int) (j : Nat) (hj : j < 8) :
    octDot a b c d e f g h 2 j =
      (a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) * (if 2 = j then 1 else 0) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp only [octDot, octEntry]; grind
  | _ + 8 => omega

private theorem octCol3 (a b c d e f g h : Int) (j : Nat) (hj : j < 8) :
    octDot a b c d e f g h 3 j =
      (a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) * (if 3 = j then 1 else 0) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp only [octDot, octEntry]; grind
  | _ + 8 => omega

private theorem octCol4 (a b c d e f g h : Int) (j : Nat) (hj : j < 8) :
    octDot a b c d e f g h 4 j =
      (a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) * (if 4 = j then 1 else 0) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp only [octDot, octEntry]; grind
  | _ + 8 => omega

private theorem octCol5 (a b c d e f g h : Int) (j : Nat) (hj : j < 8) :
    octDot a b c d e f g h 5 j =
      (a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) * (if 5 = j then 1 else 0) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp only [octDot, octEntry]; grind
  | _ + 8 => omega

private theorem octCol6 (a b c d e f g h : Int) (j : Nat) (hj : j < 8) :
    octDot a b c d e f g h 6 j =
      (a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) * (if 6 = j then 1 else 0) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp only [octDot, octEntry]; grind
  | _ + 8 => omega

private theorem octCol7 (a b c d e f g h : Int) (j : Nat) (hj : j < 8) :
    octDot a b c d e f g h 7 j =
      (a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) * (if 7 = j then 1 else 0) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp only [octDot, octEntry]; grind
  | _ + 8 => omega

private theorem octColDot_orth (a b c d e f g h : Int) (i j : Fin 8) :
    octDot a b c d e f g h i.val j.val =
    (a * a + b * b + c * c + d * d + e * e + f * f + g * g + h * h) *
      (if i.val = j.val then 1 else 0) := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => exact octCol0 a b c d e f g h j.val j.isLt
  | 1 => exact octCol1 a b c d e f g h j.val j.isLt
  | 2 => exact octCol2 a b c d e f g h j.val j.isLt
  | 3 => exact octCol3 a b c d e f g h j.val j.isLt
  | 4 => exact octCol4 a b c d e f g h j.val j.isLt
  | 5 => exact octCol5 a b c d e f g h j.val j.isLt
  | 6 => exact octCol6 a b c d e f g h j.val j.isLt
  | 7 => exact octCol7 a b c d e f g h j.val j.isLt
  | _ + 8 => omega

/-- Universal 8D Cayley–Dickson octonion left-multiplication orthogonality for ALL `x : Fin 8 → Int`. -/
theorem octonionLeft_orthogonal (x : Fin 8 → Int) :
    isOrthogonal (octonionLeft x) (sumInt (fun i => x i * x i)) := by
  funext i j
  simp only [matMul, transpose, scaleMat, idMat, sumInt8_expand]
  have hEq : (i = j) ↔ (i.val = j.val) := ⟨congrArg Fin.val, Fin.ext⟩
  have hite : (if i = j then (1 : Int) else 0) = (if i.val = j.val then 1 else 0) := by
    by_cases h : i = j
    · simp [h]
    · have h' : i.val ≠ j.val := fun hv => h (hEq.mpr hv)
      simp [h, h']
  rw [hite]
  exact octColDot_orth (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)
    (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) (x ⟨6, by decide⟩) (x ⟨7, by decide⟩) i j

/-- Concrete Llama-2 (`θ_0 = 1.0`) power-of-2 octonion norm identity: `∑ (x_i)^2 = (2^16)^2 = 2^32`. -/
theorem llama2Octonion0_norm :
    sumInt (fun i => llama2Octonion0 i * llama2Octonion0 i) = ((2 : Int) ^ 16) * ((2 : Int) ^ 16) := by
  decide

/-- Concrete Llama-2 (`θ_0 = 1.0`) power-of-2 octonion RoPE exact rational orthogonality (`>> 16` shift). -/
theorem llama2Octonion0_rat_orthogonal :
    isRatOrthogonal (octonionRoPERat llama2Octonion0 ((2 : Int) ^ 16)) := by
  have horth : isOrthogonal (octonionLeft llama2Octonion0) (((2 : Int) ^ 16) * ((2 : Int) ^ 16)) := by
    rw [← llama2Octonion0_norm]
    exact octonionLeft_orthogonal llama2Octonion0
  exact ratOrthogonal_of_intOrthogonal (octonionLeft llama2Octonion0) ((2 : Int) ^ 16)
    (by decide) horth

/-- Headline Theorem 2: Exact 2D Pythagorean, 4D Quaternion, and 8D Power-of-2 Octonion RoPE Orthogonality. -/
theorem pythagorean_and_octonion_rope_exact_orthogonal :
    (∀ a b : Int, isOrthogonal (pythagoreanRoPE a b) ((a * a + b * b) * (a * a + b * b))) ∧
    (∀ a b : Int, a * a + b * b ≠ 0 → isRatOrthogonal (pythagoreanRoPERat a b)) ∧
    (∀ a b c d : Int, isOrthogonal (quaternionLeft a b c d) (a * a + b * b + c * c + d * d)) ∧
    (∀ x : Fin 8 → Int, isOrthogonal (octonionLeft x) (sumInt (fun i => x i * x i))) ∧
    (sumInt (fun i => llama2Octonion0 i * llama2Octonion0 i) = ((2 : Int) ^ 16) * ((2 : Int) ^ 16)) ∧
    isRatOrthogonal (octonionRoPERat llama2Octonion0 ((2 : Int) ^ 16)) :=
  ⟨pythagoreanRoPE_orthogonal, pythagoreanRoPERat_orthogonal, quaternionLeft_orthogonal,
   octonionLeft_orthogonal, llama2Octonion0_norm, llama2Octonion0_rat_orthogonal⟩

end OctonionRopeWelch
