/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LoftqCyclesRank1.Defs

/-!
# Theorems 5 & 6: Exact `3 × 3` Symmetric LoftQ Permanent 2-Cycle (`W_cyc2`) & 3-Cycle (`W_cyc3`) Witnesses

Kernel-checked, zero-`native_decide`, zero-floating-point verification of the two GPU-discovered
`3 × 3` symmetric rational/integer witnesses under `loftqStepQ16` (bit-exact `Q16.16` rank-1
symmetric SVD + `M = 1` absmax ternary quantization):
- **Theorem 5 (`loftq_explicit_3x3_symmetric_2cycle_witness`):**
  `W_cyc2 = [[149, 91, 350], [91, 920, 978], [350, 978, 297]]` enters an exact permanent
  period-2 limit cycle at iteration `12`, oscillating forever between `Q_cyc2_0` and `Q_cyc2_1`
  with a macroscopic `+13.4%` error jump on every odd step (`79857264812871 -> 90566258557330`).
- **Theorem 6 (`loftq_explicit_3x3_symmetric_3cycle_witness`):**
  `W_cyc3 = [[-671, -527, 370], [-527, 259, -458], [370, -458, -906]]` enters an exact permanent
  period-3 limit cycle at iteration `10`, cycling forever through 3 pairwise-distinct states
  `Q_cyc3_0 -> Q_cyc3_1 -> Q_cyc3_2 -> Q_cyc3_0` with exact non-monotone error cycle
  `295290317881961 -> 313694815279071 -> 299386514317059 -> 295290317881961` (`+6.2%` jump every 3rd step).
-/

namespace LoftqCyclesRank1

/-! ### Exact Limit-Cycle States -/

def Q_cyc2_0 : Sym3 := ⟨17880998, 0, 17880998, 0, 17880998, -17880998⟩
def Q_cyc2_1 : Sym3 := ⟨0, 0, 18518972, 0, 18518972, -18518972⟩

def Q_cyc3_0 : Sym3 := ⟨-34190948, -34190948, 0, 34190948, -34190948, 0⟩
def Q_cyc3_1 : Sym3 := ⟨-34910879, -34910879, 0, 0, -34910879, 0⟩
def Q_cyc3_2 : Sym3 := ⟨-34361399, -34361399, 0, 0, -34361399, 0⟩

/-! ### General Iteration Helper -/

theorem loftqIterQ16_add (W Q0 : Sym3) (a b : Nat) :
    loftqIterQ16 W Q0 (a + b) = loftqIterQ16 W (loftqIterQ16 W Q0 a) b := by
  induction b with
  | zero => rfl
  | succ k ih =>
    change loftqIterQ16 W Q0 ((a + k) + 1) = loftqStepQ16 W (loftqIterQ16 W (loftqIterQ16 W Q0 a) k)
    simp only [loftqIterQ16, ih]

/-! ### Theorem 5: Exact 2-Cycle Verification on `W_cyc2` -/

theorem W_cyc2_reach_12 : loftqIterQ16 W_cyc2_q16 zeroSym3 12 = Q_cyc2_0 := by
  have h1  : loftqStepQ16 W_cyc2_q16 zeroSym3                                       = ⟨0, 0, 19821710, 0, 19821710, -19821710⟩ := rfl
  have h2  : loftqStepQ16 W_cyc2_q16 ⟨0, 0, 19821710, 0, 19821710, -19821710⟩       = ⟨18404546, 0, 18404546, 0, 18404546, -18404546⟩ := rfl
  have h3  : loftqStepQ16 W_cyc2_q16 ⟨18404546, 0, 18404546, 0, 18404546, -18404546⟩ = ⟨0, 0, 18716362, 0, 18716362, -18716362⟩ := rfl
  have h4  : loftqStepQ16 W_cyc2_q16 ⟨0, 0, 18716362, 0, 18716362, -18716362⟩       = ⟨17959453, 0, 17959453, 0, 17959453, -17959453⟩ := rfl
  have h5  : loftqStepQ16 W_cyc2_q16 ⟨17959453, 0, 17959453, 0, 17959453, -17959453⟩ = ⟨0, 0, 18548579, 0, 18548579, -18548579⟩ := rfl
  have h6  : loftqStepQ16 W_cyc2_q16 ⟨0, 0, 18548579, 0, 18548579, -18548579⟩       = ⟨17892472, 0, 17892472, 0, 17892472, -17892472⟩ := rfl
  have h7  : loftqStepQ16 W_cyc2_q16 ⟨17892472, 0, 17892472, 0, 17892472, -17892472⟩ = ⟨0, 0, 18523706, 0, 18523706, -18523706⟩ := rfl
  have h8  : loftqStepQ16 W_cyc2_q16 ⟨0, 0, 18523706, 0, 18523706, -18523706⟩       = ⟨17882867, 0, 17882867, 0, 17882867, -17882867⟩ := rfl
  have h9  : loftqStepQ16 W_cyc2_q16 ⟨17882867, 0, 17882867, 0, 17882867, -17882867⟩ = ⟨0, 0, 18519921, 0, 18519921, -18519921⟩ := rfl
  have h10 : loftqStepQ16 W_cyc2_q16 ⟨0, 0, 18519921, 0, 18519921, -18519921⟩       = ⟨17881032, 0, 17881032, 0, 17881032, -17881032⟩ := rfl
  have h11 : loftqStepQ16 W_cyc2_q16 ⟨17881032, 0, 17881032, 0, 17881032, -17881032⟩ = ⟨0, 0, 18518973, 0, 18518973, -18518973⟩ := rfl
  have h12 : loftqStepQ16 W_cyc2_q16 ⟨0, 0, 18518973, 0, 18518973, -18518973⟩       = Q_cyc2_0 := rfl
  simp only [loftqIterQ16, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

theorem W_cyc2_step_0 : loftqStepQ16 W_cyc2_q16 Q_cyc2_0 = Q_cyc2_1 := by
  rfl

theorem W_cyc2_step_1 : loftqStepQ16 W_cyc2_q16 Q_cyc2_1 = Q_cyc2_0 := by
  rfl

theorem W_cyc2_distinct : Q_cyc2_1 ≠ Q_cyc2_0 := by
  decide

theorem W_cyc2_err_0 : loftqStepErrQ16 W_cyc2_q16 Q_cyc2_0 = 90566258557330 := by
  rfl

theorem W_cyc2_err_1 : loftqStepErrQ16 W_cyc2_q16 Q_cyc2_1 = 79857264812871 := by
  rfl

theorem W_cyc2_orbit_mod2 (t : Nat) :
    loftqIterQ16 W_cyc2_q16 Q_cyc2_0 t = if t % 2 = 0 then Q_cyc2_0 else Q_cyc2_1 := by
  induction t with
  | zero => rfl
  | succ k ih =>
    simp only [loftqIterQ16, ih]
    by_cases hk : k % 2 = 0
    · have hk1 : (k + 1) % 2 ≠ 0 := by omega
      simp only [hk, hk1, ↓reduceIte, W_cyc2_step_0]
    · have hk1 : (k + 1) % 2 = 0 := by omega
      simp only [hk, hk1, ↓reduceIte, W_cyc2_step_1]

theorem loftq_explicit_3x3_symmetric_2cycle_witness :
    loftqIterQ16 W_cyc2_q16 zeroSym3 12 = Q_cyc2_0 ∧
    loftqStepQ16 W_cyc2_q16 Q_cyc2_0 = Q_cyc2_1 ∧
    loftqStepQ16 W_cyc2_q16 Q_cyc2_1 = Q_cyc2_0 ∧
    Q_cyc2_1 ≠ Q_cyc2_0 ∧
    (∀ t : Nat,
      loftqIterQ16 W_cyc2_q16 zeroSym3 (12 + t + 2) = loftqIterQ16 W_cyc2_q16 zeroSym3 (12 + t) ∧
      loftqIterQ16 W_cyc2_q16 zeroSym3 (12 + t + 1) ≠ loftqIterQ16 W_cyc2_q16 zeroSym3 (12 + t)) ∧
    loftqStepErrQ16 W_cyc2_q16 Q_cyc2_0 = 90566258557330 ∧
    loftqStepErrQ16 W_cyc2_q16 Q_cyc2_1 = 79857264812871 ∧
    loftqStepErrQ16 W_cyc2_q16 Q_cyc2_1 * 113 < loftqStepErrQ16 W_cyc2_q16 Q_cyc2_0 * 100 := by
  refine ⟨W_cyc2_reach_12, W_cyc2_step_0, W_cyc2_step_1, W_cyc2_distinct, ?_,
          W_cyc2_err_0, W_cyc2_err_1, ?_⟩
  · intro t
    rw [Nat.add_assoc 12 t 2, loftqIterQ16_add, W_cyc2_reach_12, W_cyc2_orbit_mod2]
    rw [Nat.add_assoc 12 t 1, loftqIterQ16_add, W_cyc2_reach_12, W_cyc2_orbit_mod2]
    rw [loftqIterQ16_add, W_cyc2_reach_12, W_cyc2_orbit_mod2]
    have hmod2 : (t + 2) % 2 = t % 2 := by omega
    rw [hmod2]
    constructor
    · rfl
    · by_cases ht : t % 2 = 0
      · have ht1 : (t + 1) % 2 ≠ 0 := by omega
        simp only [ht, ht1, ↓reduceIte]
        exact W_cyc2_distinct
      · have ht1 : (t + 1) % 2 = 0 := by omega
        simp only [ht, ht1, ↓reduceIte]
        exact Ne.symm W_cyc2_distinct
  · rw [W_cyc2_err_0, W_cyc2_err_1]
    decide

/-! ### Theorem 6: Exact 3-Cycle Verification on `W_cyc3` -/

theorem W_cyc3_reach_10 : loftqIterQ16 W_cyc3_q16 zeroSym3 10 = Q_cyc3_0 := by
  have h1  : loftqStepQ16 W_cyc3_q16 zeroSym3                                         = ⟨-37487604, -37487604, 0, 0, -37487604, 0⟩ := rfl
  have h2  : loftqStepQ16 W_cyc3_q16 ⟨-37487604, -37487604, 0, 0, -37487604, 0⟩       = ⟨-35158009, -35158009, 0, 0, -35158009, 0⟩ := rfl
  have h3  : loftqStepQ16 W_cyc3_q16 ⟨-35158009, -35158009, 0, 0, -35158009, 0⟩       = ⟨-34437398, -34437398, 0, 0, -34437398, 0⟩ := rfl
  have h4  : loftqStepQ16 W_cyc3_q16 ⟨-34437398, -34437398, 0, 0, -34437398, 0⟩       = ⟨-34214960, -34214960, 0, 34214960, -34214960, 0⟩ := rfl
  have h5  : loftqStepQ16 W_cyc3_q16 ⟨-34214960, -34214960, 0, 34214960, -34214960, 0⟩ = ⟨-34929738, -34929738, 0, 0, -34929738, 0⟩ := rfl
  have h6  : loftqStepQ16 W_cyc3_q16 ⟨-34929738, -34929738, 0, 0, -34929738, 0⟩       = ⟨-34367231, -34367231, 0, 0, -34367231, 0⟩ := rfl
  have h7  : loftqStepQ16 W_cyc3_q16 ⟨-34367231, -34367231, 0, 0, -34367231, 0⟩       = ⟨-34193424, -34193424, 0, 34193424, -34193424, 0⟩ := rfl
  have h8  : loftqStepQ16 W_cyc3_q16 ⟨-34193424, -34193424, 0, 34193424, -34193424, 0⟩ = ⟨-34912873, -34912873, 0, 0, -34912873, 0⟩ := rfl
  have h9  : loftqStepQ16 W_cyc3_q16 ⟨-34912873, -34912873, 0, 0, -34912873, 0⟩       = ⟨-34361422, -34361422, 0, 0, -34361422, 0⟩ := rfl
  have h10 : loftqStepQ16 W_cyc3_q16 ⟨-34361422, -34361422, 0, 0, -34361422, 0⟩       = Q_cyc3_0 := rfl
  simp only [loftqIterQ16, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem W_cyc3_step_0 : loftqStepQ16 W_cyc3_q16 Q_cyc3_0 = Q_cyc3_1 := by
  rfl

theorem W_cyc3_step_1 : loftqStepQ16 W_cyc3_q16 Q_cyc3_1 = Q_cyc3_2 := by
  rfl

theorem W_cyc3_step_2 : loftqStepQ16 W_cyc3_q16 Q_cyc3_2 = Q_cyc3_0 := by
  rfl

theorem W_cyc3_distinct_01 : Q_cyc3_0 ≠ Q_cyc3_1 := by decide
theorem W_cyc3_distinct_12 : Q_cyc3_1 ≠ Q_cyc3_2 := by decide
theorem W_cyc3_distinct_20 : Q_cyc3_2 ≠ Q_cyc3_0 := by decide

theorem W_cyc3_err_0 : loftqStepErrQ16 W_cyc3_q16 Q_cyc3_0 = 313694815279071 := by rfl
theorem W_cyc3_err_1 : loftqStepErrQ16 W_cyc3_q16 Q_cyc3_1 = 299386514317059 := by rfl
theorem W_cyc3_err_2 : loftqStepErrQ16 W_cyc3_q16 Q_cyc3_2 = 295290317881961 := by rfl

theorem W_cyc3_orbit_mod3 (t : Nat) :
    loftqIterQ16 W_cyc3_q16 Q_cyc3_0 t =
      if t % 3 = 0 then Q_cyc3_0 else if t % 3 = 1 then Q_cyc3_1 else Q_cyc3_2 := by
  induction t with
  | zero => rfl
  | succ k ih =>
    simp only [loftqIterQ16, ih]
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have hk1 : (k + 1) % 3 = 1 := by omega
      simp only [h0, hk1, ↓reduceIte, Nat.one_ne_zero]
      exact W_cyc3_step_0
    · have hk1 : (k + 1) % 3 = 2 := by omega
      have hne0 : (2 : Nat) ≠ 0 := by decide
      have hne1 : (2 : Nat) ≠ 1 := by decide
      simp only [h1, hk1, ↓reduceIte, Nat.one_ne_zero, hne0, hne1]
      exact W_cyc3_step_1
    · have hk1 : (k + 1) % 3 = 0 := by omega
      have hne0 : (2 : Nat) ≠ 0 := by decide
      have hne1 : (2 : Nat) ≠ 1 := by decide
      simp only [h2, hk1, ↓reduceIte, hne0, hne1]
      exact W_cyc3_step_2

theorem loftq_explicit_3x3_symmetric_3cycle_witness :
    loftqIterQ16 W_cyc3_q16 zeroSym3 10 = Q_cyc3_0 ∧
    loftqStepQ16 W_cyc3_q16 Q_cyc3_0 = Q_cyc3_1 ∧
    loftqStepQ16 W_cyc3_q16 Q_cyc3_1 = Q_cyc3_2 ∧
    loftqStepQ16 W_cyc3_q16 Q_cyc3_2 = Q_cyc3_0 ∧
    Q_cyc3_0 ≠ Q_cyc3_1 ∧ Q_cyc3_1 ≠ Q_cyc3_2 ∧ Q_cyc3_2 ≠ Q_cyc3_0 ∧
    (∀ t : Nat,
      loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t + 3) = loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t) ∧
      loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t + 1) ≠ loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t) ∧
      loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t + 2) ≠ loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t)) ∧
    loftqStepErrQ16 W_cyc3_q16 Q_cyc3_0 = 313694815279071 ∧
    loftqStepErrQ16 W_cyc3_q16 Q_cyc3_1 = 299386514317059 ∧
    loftqStepErrQ16 W_cyc3_q16 Q_cyc3_2 = 295290317881961 ∧
    loftqStepErrQ16 W_cyc3_q16 Q_cyc3_2 * 106 < loftqStepErrQ16 W_cyc3_q16 Q_cyc3_0 * 100 := by
  refine ⟨W_cyc3_reach_10, W_cyc3_step_0, W_cyc3_step_1, W_cyc3_step_2,
          W_cyc3_distinct_01, W_cyc3_distinct_12, W_cyc3_distinct_20, ?_,
          W_cyc3_err_0, W_cyc3_err_1, W_cyc3_err_2, ?_⟩
  · intro t
    rw [Nat.add_assoc 10 t 3, loftqIterQ16_add, W_cyc3_reach_10, W_cyc3_orbit_mod3]
    rw [Nat.add_assoc 10 t 1, loftqIterQ16_add, W_cyc3_reach_10, W_cyc3_orbit_mod3]
    rw [Nat.add_assoc 10 t 2, loftqIterQ16_add, W_cyc3_reach_10, W_cyc3_orbit_mod3]
    rw [loftqIterQ16_add, W_cyc3_reach_10, W_cyc3_orbit_mod3]
    have hmod3 : (t + 3) % 3 = t % 3 := by omega
    rw [hmod3]
    refine ⟨rfl, ?_, ?_⟩
    · have hcases : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · have h1' : (t + 1) % 3 = 1 := by omega
        simp only [h0, h1', ↓reduceIte, Nat.one_ne_zero]; exact Ne.symm W_cyc3_distinct_01
      · have h2' : (t + 1) % 3 = 2 := by omega
        have hne0 : (2 : Nat) ≠ 0 := by decide
        have hne1 : (2 : Nat) ≠ 1 := by decide
        simp only [h1, h2', ↓reduceIte, Nat.one_ne_zero, hne0, hne1]; exact Ne.symm W_cyc3_distinct_12
      · have h0' : (t + 1) % 3 = 0 := by omega
        have hne0 : (2 : Nat) ≠ 0 := by decide
        have hne1 : (2 : Nat) ≠ 1 := by decide
        simp only [h2, h0', ↓reduceIte, hne0, hne1]; exact Ne.symm W_cyc3_distinct_20
    · have hcases : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · have h2' : (t + 2) % 3 = 2 := by omega
        have hne0 : (2 : Nat) ≠ 0 := by decide
        have hne1 : (2 : Nat) ≠ 1 := by decide
        simp only [h0, h2', ↓reduceIte, hne0, hne1]; exact W_cyc3_distinct_20
      · have h0' : (t + 2) % 3 = 0 := by omega
        simp only [h1, h0', ↓reduceIte, Nat.one_ne_zero]; exact W_cyc3_distinct_01
      · have h1' : (t + 2) % 3 = 1 := by omega
        have hne0 : (2 : Nat) ≠ 0 := by decide
        have hne1 : (2 : Nat) ≠ 1 := by decide
        simp only [h2, h1', ↓reduceIte, Nat.one_ne_zero, hne0, hne1]; exact W_cyc3_distinct_12
  · rw [W_cyc3_err_0, W_cyc3_err_2]
    decide

end LoftqCyclesRank1
