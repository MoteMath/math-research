import BinaryGraySuperpositionTransfer

namespace BinaryGraySuperpositionTransferChallenge

open BitTransfer3

theorem glue_alpha_sound {n : Nat} (spec : GlueSpec) (L R : TermGraph n) (s : Fin 8) :
    alphaVec (glue spec L R) s = stepAlpha spec (alphaVec L) (alphaVec R) s :=
  _root_.BitTransfer3.glue_alpha_sound spec L R s

theorem gb_pm_recurrence (k : Nat) (hk : 3 ≤ k) :
    exactPM (gbGraph (k + 1) (by omega)).graph =
    exactPM (gbGraph k (by omega)).graph ^ 2 + exactPM (gbGraph (k - 1) (by omega)).graph ^ 2 :=
  _root_.BitTransfer3.gb_pm_recurrence k hk

theorem gb_doublyCyclic_pm (k : Nat) (hk : 2 ≤ k) :
    exactPM (gbDoublyCyclic k hk) = 2 * pmSeq k + 1 :=
  _root_.BitTransfer3.gb_doublyCyclic_pm k hk

theorem gbGraph_exactChrom (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    (exactChromCount (gbGraph k hk).graph q : Int) = pEval (gbChromPoly k) (q : Int) :=
  _root_.BitTransfer3.gbGraph_exactChrom k hk q

theorem gb_doublyCyclic_exactChrom (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    (exactChromCount (gbDoublyCyclic k hk) q : Int) = pEval (doublyCyclicChromPoly (gbChromVec k)) (q : Int) :=
  _root_.BitTransfer3.gb_doublyCyclic_exactChrom k hk q

theorem gb_chrom_root_two_sharp_k2 : HasLeadAt (gbChromPoly 2) 2 1 2 :=
  _root_.BitTransfer3.gb_chrom_root_two_sharp_k2

theorem sb_pm_const_one (d : Nat) : exactPM (recGraph sbSpec d).graph = 1 :=
  _root_.BitTransfer3.sb_pm_const_one d

theorem non_vacuity_witness :
    exactPM (gbGraph 4 (by omega)).graph = 5 ∧
    exactPM (gbDoublyCyclic 4 (by omega)) = 11 ∧
    exactAlpha (gbGraph 4 (by omega)).graph = some 7 ∧
    exactAlpha (gbDoublyCyclic 4 (by omega)) = some 6 ∧
    exactChromCount (gbGraph 3 (by omega)).graph 2 = 0 ∧
    exactChromCount (gbGraph 3 (by omega)).graph 3 = 60 :=
  _root_.BitTransfer3.non_vacuity_witness

end BinaryGraySuperpositionTransferChallenge
