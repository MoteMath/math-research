/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CombInequalities.CombDefs

/-!
# Trusted Challenge Statements (`combinatorial-inequalities`)

This file imports `CombInequalities.CombDefs` alone (pure `Std`, zero Mathlib) and states
the 4 headline universal inequalities with `sorry` placeholders for `leanprover/comparator`.
-/

namespace CombInequalitiesChallenge

open CombMining

/-- Factor-3 bound `3 * inv(S^2 p) <= pat231 p` for two-stack sorting on `321`-avoiding permutations (a bound only; optimality of the factor 3 is not part of this statement). -/
theorem avoids321_three_stack2Inv_le_pat231 {n : Nat} (p : PermFin n) (h321 : p.Avoids321) :
    3 * p.stack2Inv ≤ p.pat231 := by
  sorry

/-- Descents after one West stack-sorting pass are bounded by input interior peaks. -/
theorem stackDes_le_peaksCnt {n : Nat} (p : PermFin n) :
    p.stackDes ≤ p.peaksCnt := by
  sorry

/-- Quadratic descent-excess ceiling for Spearman displacement on `231`-avoiding permutations. -/
theorem avoids231_two_inv_le_disp2_add_des {n : Nat} (p : PermFin n) (h231 : p.Avoids231) :
    2 * p.invCnt ≤ p.disp2 + desList p.toList * (desList p.toList + 1) := by
  sorry

/-- Finite-difference folding bound `3 |A - A| <= 2 |2A - A| + 1`. -/
theorem three_diffset_le_two_sum2Diff1_add_one (A : Nat → Bool) (N : Nat)
    (hN : 1 ≤ N) (h0 : A 0 = true) (hmax : A (N - 1) = true) :
    3 * intDiffsetCard A N ≤ 2 * intSum2Diff1Card A N + 1 := by
  sorry

end CombInequalitiesChallenge
