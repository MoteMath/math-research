/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CombInequalities

/-!
# Verified Proofs of the Challenge Statements (`combinatorial-inequalities`)
-/

namespace CombInequalitiesChallenge

open CombMining

theorem avoids321_three_stack2Inv_le_pat231 {n : Nat} (p : PermFin n) (h321 : p.Avoids321) :
    3 * p.stack2Inv ≤ p.pat231 :=
  CombMining.PermFin.avoids321_three_stack2Inv_le_pat231 p h321

theorem stackDes_le_peaksCnt {n : Nat} (p : PermFin n) :
    p.stackDes ≤ p.peaksCnt :=
  CombMining.PermFin.stackDes_le_peaksCnt p

theorem avoids231_two_inv_le_disp2_add_des {n : Nat} (p : PermFin n) (h231 : p.Avoids231) :
    2 * p.invCnt ≤ p.disp2 + desList p.toList * (desList p.toList + 1) :=
  CombMining.PermFin.avoids231_two_inv_le_disp2_add_des p h231

theorem three_diffset_le_two_sum2Diff1_add_one (A : Nat → Bool) (N : Nat)
    (hN : 1 ≤ N) (h0 : A 0 = true) (hmax : A (N - 1) = true) :
    3 * intDiffsetCard A N ≤ 2 * intSum2Diff1Card A N + 1 :=
  CombMining.three_diffset_le_two_sum2Diff1_add_one A N hN h0 hmax

end CombInequalitiesChallenge
