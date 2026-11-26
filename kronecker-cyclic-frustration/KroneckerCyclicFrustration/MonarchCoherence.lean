/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KroneckerCyclicFrustration.RatOrder

/-!
# 2-Stage Monarch Coherence Factorization & Support Lower Bound

Proves Headline Theorem 4 (`monarch_coherence_factorization_and_lower_bound`) in pure `Init`.
-/

namespace KroneckerCyclicFrustration

theorem finSumInt_mul_left : ∀ {n : Nat} (c : Int) (f : Fin n → Int),
    finSumInt (fun i => c * f i) = c * finSumInt f
  | 0, _, _ => by simp [finSumInt]
  | _ + 1, c, f => by
    simp only [finSumInt]
    rw [finSumInt_mul_left c (fun i => f i.castSucc), Int.mul_add]

theorem finSumInt_mul_right : ∀ {n : Nat} (f : Fin n → Int) (c : Int),
    finSumInt (fun i => f i * c) = finSumInt f * c
  | 0, _, _ => by simp [finSumInt]
  | _ + 1, f, c => by
    simp only [finSumInt]
    rw [finSumInt_mul_right (fun i => f i.castSucc) c, Int.add_mul]

theorem finSumInt_congr : ∀ {n : Nat} {f g : Fin n → Int},
    (∀ i, f i = g i) → finSumInt f = finSumInt g
  | 0, _, _, _ => rfl
  | _ + 1, _, _, h => by
    simp only [finSumInt]
    rw [finSumInt_congr (fun i => h i.castSucc), h]

theorem monarch_col_dot_factor {n1 n2 : Nat}
    (A : Fin n2 → Fin n2 → Int) (B : Fin n1 → Fin n1 → Int)
    (a1 a2 : Fin n2) (b1 b2 : Fin n1) :
    finSumInt (fun b' : Fin n1 =>
      finSumInt (fun a' : Fin n2 =>
        monarchEntry A B (b', a') (a1, b1) * monarchEntry A B (b', a') (a2, b2))) =
    matColDot A a1 a2 * matColDot B b1 b2 := by
  unfold monarchEntry matColDot
  have hinner : ∀ b' : Fin n1,
      finSumInt (fun a' : Fin n2 => A a' a1 * B b' b1 * (A a' a2 * B b' b2)) =
      finSumInt (fun a' : Fin n2 => A a' a1 * A a' a2) * (B b' b1 * B b' b2) := by
    intro b'
    rw [← finSumInt_mul_right]
    apply finSumInt_congr
    intro a'
    grind
  rw [finSumInt_congr hinner, finSumInt_mul_left]

theorem vecNormSq_le_vecNnz_mul_max : ∀ {n : Nat} (v : Fin n → Int) (M : Int),
    (0 : Int) ≤ M → (∀ j : Fin n, v j * v j ≤ M) →
    vecNormSq v ≤ (vecNnz v : Int) * M
  | 0, _, _, _, _ => by simp [vecNormSq, vecNnz, finSumInt, finSumNat]
  | _ + 1, v, M, hM, hbound => by
    unfold vecNormSq vecNnz
    simp only [finSumInt, finSumNat]
    have ih := vecNormSq_le_vecNnz_mul_max (fun i => v i.castSucc) M hM (fun i => hbound i.castSucc)
    dsimp only [vecNormSq, vecNnz] at ih
    have hlast := hbound ⟨_, Nat.lt_succ_self _⟩
    by_cases hv : v ⟨_, Nat.lt_succ_self _⟩ = 0
    · rw [hv]
      simp only [ite_true, Int.mul_zero, Int.add_zero, Nat.add_zero]
      exact ih
    · simp only [hv, ite_false]
      have hcast : ((finSumNat (fun i => if v i.castSucc = 0 then 0 else 1) + 1 : Nat) : Int) =
          (finSumNat (fun i => if v i.castSucc = 0 then 0 else 1) : Int) + 1 := by omega
      rw [hcast, Int.add_mul, Int.one_mul]
      exact Int.add_le_add ih hlast

theorem rat_intCast_nonneg_of_pos {z : Int} (hz : (0 : Int) < z) : (0 : Rat) < (z : Rat) := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => exact False.elim (Int.lt_irrefl 0 hz)
    | succ m =>
      clear hz
      induction m with
      | zero => decide
      | succ k ih =>
        have hstep : ((Int.ofNat (k + 1 + 1)) : Rat) = ((Int.ofNat (k + 1)) : Rat) + 1 := by
          change (((k + 1) + 1 : Nat) : Rat) = ((k + 1 : Nat) : Rat) + 1
          rw [Rat.natCast_add]
          rfl
        rw [hstep]
        exact rat_add_pos ih (by decide)
  | negSucc _ => omega

theorem rat_intCast_le {a b : Int} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have hd : b = a + (b - a) := by omega
  rw [hd, Rat.intCast_add]
  have hnn : (0 : Rat) ≤ ((b - a : Int) : Rat) := by
    by_cases h0 : b - a = 0
    · rw [h0]; decide
    · exact Rat.le_of_lt (rat_intCast_nonneg_of_pos (by omega))
  have hadd := rat_add_le_add (Rat.le_refl (a := (a : Rat))) hnn
  rw [Rat.add_zero] at hadd
  exact hadd

/-- Headline Theorem 4 (`monarch_coherence_factorization_and_lower_bound`). -/
theorem monarch_coherence_factorization_and_lower_bound :
    (∀ {n1 n2 : Nat} (A : Fin n2 → Fin n2 → Int) (B : Fin n1 → Fin n1 → Int)
      (a1 a2 : Fin n2) (b1 b2 : Fin n1),
      finSumInt (fun b' : Fin n1 =>
        finSumInt (fun a' : Fin n2 =>
          monarchEntry A B (b', a') (a1, b1) * monarchEntry A B (b', a') (a2, b2))) =
      matColDot A a1 a2 * matColDot B b1 b2) ∧
    (∀ {n1 n2 : Nat} (A : Fin n2 → Fin n2 → Int) (B : Fin n1 → Fin n1 → Int) (S_A S_B : Int),
      IsScaledOrtho A S_A → IsScaledOrtho B S_B →
      ∀ (a1 a2 : Fin n2) (b1 b2 : Fin n1),
        finSumInt (fun b' : Fin n1 =>
          finSumInt (fun a' : Fin n2 =>
            monarchEntry A B (b', a') (a1, b1) * monarchEntry A B (b', a') (a2, b2))) =
        if a1 = a2 ∧ b1 = b2 then S_A * S_B else 0) ∧
    (∀ {n1 n2 : Nat} (A : Fin n2 → Fin n2 → Int) (B : Fin n1 → Fin n1 → Int)
      (maxSqA maxSqB S_A S_B : Int),
      (0 : Int) ≤ maxSqA → (0 : Int) ≤ maxSqB →
      (∀ a' a, A a' a * A a' a ≤ maxSqA) →
      (∀ b' b, B b' b * B b' b ≤ maxSqB) →
      (∀ (a' : Fin n2) (a : Fin n2) (b' : Fin n1) (b : Fin n1),
        monarchEntry A B (b', a') (a, b) * monarchEntry A B (b', a') (a, b) ≤ maxSqA * maxSqB) ∧
      (∀ (a'0 a0 : Fin n2) (b'0 b0 : Fin n1),
        A a'0 a0 * A a'0 a0 = maxSqA → B b'0 b0 * B b'0 b0 = maxSqB →
        monarchEntry A B (b'0, a'0) (a0, b0) * monarchEntry A B (b'0, a'0) (a0, b0) =
          maxSqA * maxSqB) ∧
      ((0 : Int) < S_A → (0 : Int) < S_B →
        (((maxSqA * maxSqB : Int) : Rat) / ((S_A * S_B : Int) : Rat)) =
        ((maxSqA : Rat) / (S_A : Rat)) * ((maxSqB : Rat) / (S_B : Rat)))) ∧
    (∀ {n : Nat} (v : Fin n → Int) (M : Int),
      (0 : Int) ≤ M → (∀ j : Fin n, v j * v j ≤ M) →
      vecNormSq v ≤ (vecNnz v : Int) * M ∧
      ((0 : Int) < vecNormSq v → 0 < vecNnz v →
        (1 : Rat) / ((vecNnz v : Int) : Rat) ≤ (M : Rat) / (vecNormSq v : Rat))) := by
  refine ⟨fun A B a1 a2 b1 b2 => monarch_col_dot_factor A B a1 a2 b1 b2, ?_, ?_, ?_⟩
  · intro n1 n2 A B S_A S_B hA hB a1 a2 b1 b2
    rw [monarch_col_dot_factor, hA a1 a2, hB b1 b2]
    by_cases ha : a1 = a2 <;> by_cases hb : b1 = b2 <;> simp [ha, hb]
  · intro n1 n2 A B maxSqA maxSqB S_A S_B hMA hMB hA hB
    refine ⟨?_, ?_, ?_⟩
    · intro a' a b' b
      unfold monarchEntry
      have hsq : (A a' a * B b' b) * (A a' a * B b' b) = (A a' a * A a' a) * (B b' b * B b' b) := by grind
      rw [hsq]
      have h1 : A a' a * A a' a ≤ maxSqA := hA a' a
      have h2 : B b' b * B b' b ≤ maxSqB := hB b' b
      have hsq_nn : ∀ x : Int, (0 : Int) ≤ x * x := by
        intro x
        cases Int.le_total 0 x with
        | inl h => exact Int.mul_nonneg h h
        | inr h =>
          have eq : x * x = (-x) * (-x) := by grind
          rw [eq]
          exact Int.mul_nonneg (by omega) (by omega)
      have h4 : (0 : Int) ≤ B b' b * B b' b := hsq_nn (B b' b)
      exact Int.le_trans (Int.mul_le_mul_of_nonneg_right h1 h4)
        (Int.mul_le_mul_of_nonneg_left h2 hMA)
    · intro a'0 a0 b'0 b0 h1 h2
      unfold monarchEntry
      have hsq : (A a'0 a0 * B b'0 b0) * (A a'0 a0 * B b'0 b0) =
          (A a'0 a0 * A a'0 a0) * (B b'0 b0 * B b'0 b0) := by grind
      rw [hsq, h1, h2]
    · intro hSA hSB
      rw [Rat.intCast_mul, Rat.intCast_mul]
      exact (rat_div_mul_div
        (Rat.ne_of_gt (rat_intCast_nonneg_of_pos hSA))
        (Rat.ne_of_gt (rat_intCast_nonneg_of_pos hSB))).symm
  · intro n v M hM hbound
    have hint := vecNormSq_le_vecNnz_mul_max v M hM hbound
    refine ⟨hint, ?_⟩
    intro hS hnnz
    have hnnz_pos : (0 : Rat) < ((vecNnz v : Int) : Rat) := rat_intCast_nonneg_of_pos (by omega)
    have hS_pos : (0 : Rat) < (vecNormSq v : Rat) := rat_intCast_nonneg_of_pos hS
    apply rat_div_le_div_of_cross hnnz_pos hS_pos
    rw [Rat.one_mul, Rat.mul_comm]
    have hle := rat_intCast_le hint
    rw [Rat.intCast_mul] at hle
    exact hle

end KroneckerCyclicFrustration
