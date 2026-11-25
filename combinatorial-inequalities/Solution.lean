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

theorem stackInv_le_popInv {n : Nat} (p : PermFin n) :
    p.stackInv ≤ p.popInv :=
  CombMining.PermFin.stackInv_le_popInv p

theorem avoids321_three_stack2Inv_le_pat231 {n : Nat} (p : PermFin n) (h321 : p.Avoids321) :
    3 * p.stack2Inv ≤ p.pat231 :=
  CombMining.PermFin.avoids321_three_stack2Inv_le_pat231 p h321

theorem stackDes_le_peaksCnt {n : Nat} (p : PermFin n) :
    p.stackDes ≤ p.peaksCnt :=
  CombMining.PermFin.stackDes_le_peaksCnt p

theorem stackInv_le_pat231 {n : Nat} (p : PermFin n) :
    p.stackInv ≤ p.pat231 :=
  CombMining.PermFin.stackInv_le_pat231 p

theorem avoids231_two_inv_le_disp2_add_des {n : Nat} (p : PermFin n) (h231 : p.Avoids231) :
    2 * p.invCnt ≤ p.disp2 + desList p.toList * (desList p.toList + 1) :=
  CombMining.PermFin.avoids231_two_inv_le_disp2_add_des p h231

theorem sidon_sym_defect_eq (A : Nat → Bool) (mn mx : Nat)
    (hsid : IsSidonPred A) (hlt : mn < mx) (hmn : A mn = true) (hmx : A mx = true) :
    symDefectInterval A mn mx + 4 = 2 * cardInterval A mn mx :=
  CombMining.sidon_sym_defect_eq A mn mx hsid hlt hmn hmx

theorem two_card_add_symDefect_le_diffset_add_one (A : Nat → Bool) (N : Nat)
    (hN : 1 ≤ N) (h0 : A 0 = true) (hmax : A (N - 1) = true) :
    2 * cardPrefix A N + symDefectPrefix A N ≤ intDiffsetCard A N + 1 :=
  CombMining.two_card_add_symDefect_le_diffset_add_one A N hN h0 hmax

theorem three_diffset_le_two_sum2Diff1_add_one (A : Nat → Bool) (N : Nat)
    (hN : 1 ≤ N) (h0 : A 0 = true) (hmax : A (N - 1) = true) :
    3 * intDiffsetCard A N ≤ 2 * intSum2Diff1Card A N + 1 :=
  CombMining.three_diffset_le_two_sum2Diff1_add_one A N hN h0 hmax

theorem connected_diam_le_indP4_add_two {n d : Nat} (G : SimpleGraphFin n) (hd : G.DiameterNum d) :
    d ≤ G.indP4Cnt + 2 :=
  CombMining.SimpleGraphFin.connected_diam_le_indP4_add_two G hd

theorem albertson_le_orderedIndP3 {n : Nat} (G : SimpleGraphFin n) :
    G.albertson ≤ G.orderedIndP3 :=
  CombMining.SimpleGraphFin.albertson_le_orderedIndP3 G

theorem disproof_avoids231_inv_disp_lds :
    ¬ (∀ (n : Nat) (p : PermFin n) (l : Nat), 4 ≤ n → p.Avoids231 →
        ((∃ sub, p.StrictDecSubseq sub ∧ sub.length = l) ∧
          (∀ sub, p.StrictDecSubseq sub → sub.length ≤ l)) →
        2 * p.invCnt ≤ p.disp2 + l * (l - 1)) :=
  CombMining.not_Conj_Avoids231_InvDispLDS

theorem disproof_bipartite_dom_indNu_diam :
    ¬ (∀ (n : Nat) (G : SimpleGraphFin n) (g iu d : Nat), 5 ≤ n → G.Connected → G.Bipartite →
        G.DominationNum g → G.InducedMatchingNum iu → G.DiameterNum d → g + 1 ≤ iu + d) :=
  CombMining.not_Conj_Bipartite_Dom_IndNu_Diam

end CombInequalitiesChallenge
