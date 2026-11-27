import BinaryGraySuperpositionTransfer.Defs

namespace BinaryGraySuperpositionTransferChallenge

open BitTransfer3

/-- **GENERIC SOUNDNESS THEOREM 1 (`BitTransfer3.Alpha`)**: For ANY 3-terminal gluing specification `spec` and ANY two `TermGraph n` instances `L, R`, the exact tropical independence-number vector of `glue spec L R` equals `stepAlpha spec`. -/
theorem glue_alpha_sound {n : Nat} (spec : GlueSpec) (L R : TermGraph n) (s : Fin 8) :
    alphaVec (glue spec L R) s = stepAlpha spec (alphaVec L) (alphaVec R) s := by
  sorry

theorem gb_pm_recurrence (k : Nat) (hk : 3 ≤ k) :
    exactPM (gbGraph (k + 1) (by omega)).graph =
    exactPM (gbGraph k (by omega)).graph ^ 2 + exactPM (gbGraph (k - 1) (by omega)).graph ^ 2 := by
  sorry

theorem gb_doublyCyclic_pm (k : Nat) (hk : 2 ≤ k) :
    exactPM (gbDoublyCyclic k hk) = 2 * pmSeq k + 1 := by
  sorry

theorem gbGraph_exactChrom (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    (exactChromCount (gbGraph k hk).graph q : Int) = pEval (gbChromPoly k) (q : Int) := by
  sorry

theorem gb_doublyCyclic_exactChrom (k : Nat) (hk : 2 ≤ k) (q : Nat) :
    (exactChromCount (gbDoublyCyclic k hk) q : Int) = pEval (doublyCyclicChromPoly (gbChromVec k)) (q : Int) := by
  sorry

/-- Finite instance: `gbChromPoly 2` has Taylor expansion at `q = 2` with vanishing order `1` and leading coefficient `2`. (Only the `k = 2` case is stated here; nothing is claimed for `k ≥ 3`.) -/
theorem gb_chrom_root_two_sharp_k2 : HasLeadAt (gbChromPoly 2) 2 1 2 := by
  sorry

theorem sb_pm_const_one (d : Nat) : exactPM (recGraph sbSpec d).graph = 1 := by
  sorry

/-- Finite instance (concrete computation on `GB_3` and `GB_4`): perfect-matching counts, independence numbers and two colouring counts. It does not instantiate the universal theorems above. -/
theorem non_vacuity_witness :
    exactPM (gbGraph 4 (by omega)).graph = 5 ∧
    exactPM (gbDoublyCyclic 4 (by omega)) = 11 ∧
    exactAlpha (gbGraph 4 (by omega)).graph = some 7 ∧
    exactAlpha (gbDoublyCyclic 4 (by omega)) = some 6 ∧
    exactChromCount (gbGraph 3 (by omega)).graph 2 = 0 ∧
    exactChromCount (gbGraph 3 (by omega)).graph 3 = 60 := by
  sorry

end BinaryGraySuperpositionTransferChallenge
