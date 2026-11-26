/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitnetContraction.Defs

/-!
# Theorem 5: Multi-Level Shifted-Sqrt Critical Dimension `d_crit(G_M) = 8 M^2 + 4` & Harmonic Constants

Pure-`Init` Lean 4 proof (zero Mathlib) of:
1. The exact universal integer sandwich for ALL `M ≥ 1`:
   `(4 M^2 + 1)^2 < 16 M^2 (M^2 + 1) < (4 M^2 + 2)^2`.
2. The exact feasibility boundary on `d : Nat` for ALL `M ≥ 2`:
   `(4 M^2 + 2 < d ∧ 16 M^2 (M^2 + 1) < (d - (4 M^2 + 2))^2) ↔ 8 M^2 + 4 ≤ d`,
   proving `d_crit(G_M) = 8 M^2 + 4` is the exact phase-transition dimension where the
   codeword `(M, 2, 1, ..., 1)` first beats ratio `1` on the shifted-sqrt extremal vector `x^(M)`.
3. Concrete critical dimensions: `dCrit 2 = 36` (Quinary), `dCrit 3 = 76` (INT3), `dCrit 7 = 396` (INT4).
4. Exact Codebook Harmonic Constants:
   `H(Ternary) = 1`, `H(Quinary) = 4/3`, `H(Odd5) = 3/2`, `H(INT3) = 23/15`,
   `H(INT4) = 88069/45045`.
-/

namespace BitnetContraction

/-- Exact integer sandwich `(4M^2 + 1)^2 < 16 M^2 (M^2 + 1) < (4M^2 + 2)^2` for all `M ≥ 1`. -/
theorem dcrit_integer_sandwich (M : Nat) (hM : 1 ≤ M) :
    (4 * M * M + 1) * (4 * M * M + 1) < 16 * M * M * (M * M + 1) ∧
    16 * M * M * (M * M + 1) < (4 * M * M + 2) * (4 * M * M + 2) := by
  have hM2 : 1 ≤ M * M := Nat.mul_le_mul hM hM
  have h8 : 8 * (M * M) ≥ 8 := by omega
  have hlhs : (4 * M * M + 1) * (4 * M * M + 1) + (8 * (M * M) - 1) =
      16 * M * M * (M * M + 1) := by grind
  have hrhs : 16 * M * M * (M * M + 1) + 4 =
      (4 * M * M + 2) * (4 * M * M + 2) := by grind
  constructor <;> omega

/-- Exact phase-transition boundary on `d : Nat`:
    `d > 4 M^2 + 2 + 4 M √(M^2 + 1)` (written in exact squared integer form) holds
    if and only if `d ≥ 8 M^2 + 4 = dCrit M`. -/
theorem dcrit_feasibility_boundary (M : Nat) (hM : 2 ≤ M) (d : Nat) :
    (4 * M * M + 2 < d ∧
      16 * M * M * (M * M + 1) < (d - (4 * M * M + 2)) * (d - (4 * M * M + 2))) ↔
    dCrit M ≤ d := by
  have hsand := dcrit_integer_sandwich M (by omega)
  have h8 : 8 * M * M = 2 * (4 * M * M) := by grind
  unfold dCrit
  constructor
  · intro ⟨hgt, hsq⟩
    by_cases hle : 8 * M * M + 4 ≤ d
    · exact hle
    · exfalso
      have hdiff : d - (4 * M * M + 2) ≤ 4 * M * M + 1 := by omega
      have hsq_le : (d - (4 * M * M + 2)) * (d - (4 * M * M + 2)) ≤
          (4 * M * M + 1) * (4 * M * M + 1) := Nat.mul_le_mul hdiff hdiff
      omega
  · intro hge
    refine ⟨by omega, ?_⟩
    have hdiff : 4 * M * M + 2 ≤ d - (4 * M * M + 2) := by omega
    have hsq_ge : (4 * M * M + 2) * (4 * M * M + 2) ≤
        (d - (4 * M * M + 2)) * (d - (4 * M * M + 2)) := Nat.mul_le_mul hdiff hdiff
    omega

/-- **Theorem 5 (Multi-Level Shifted-Sqrt Critical Dimension & Harmonic Constants):**
    Universal integer sandwich and exact feasibility boundary for `d_crit(G_M) = 8 M^2 + 4`
    for ALL `M ≥ 2`, concrete values (`36` Quinary, `76` INT3, `396` INT4), and exact
    Codebook Harmonic Constants (`1`, `4/3`, `3/2`, `23/15`, `88069/45045`). -/
theorem multilevel_shifted_sqrt_dcrit_exact (M : Nat) (hM : 2 ≤ M) :
    ((4 * M * M + 1) * (4 * M * M + 1) < 16 * M * M * (M * M + 1) ∧
     16 * M * M * (M * M + 1) < (4 * M * M + 2) * (4 * M * M + 2)) ∧
    (∀ d : Nat,
      (4 * M * M + 2 < d ∧
        16 * M * M * (M * M + 1) < (d - (4 * M * M + 2)) * (d - (4 * M * M + 2))) ↔
      dCrit M ≤ d) ∧
    (dCrit 2 = 36 ∧ dCrit 3 = 76 ∧ dCrit 7 = 396) ∧
    (harmonicConst [1] = 1 ∧
     harmonicConst [1, 2] = (4 : Rat) / 3 ∧
     harmonicConst [1, 3] = (3 : Rat) / 2 ∧
     harmonicConst [1, 2, 3] = (23 : Rat) / 15 ∧
     harmonicConst [1, 2, 3, 4, 5, 6, 7] = (88069 : Rat) / 45045) := by
  refine ⟨dcrit_integer_sandwich M (by omega), dcrit_feasibility_boundary M hM, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [harmonicConst, harmonicConstAux]; grind
    · simp only [harmonicConst, harmonicConstAux]; grind
    · simp only [harmonicConst, harmonicConstAux]; grind
    · simp only [harmonicConst, harmonicConstAux]; grind
    · simp only [harmonicConst, harmonicConstAux]; grind

end BitnetContraction
