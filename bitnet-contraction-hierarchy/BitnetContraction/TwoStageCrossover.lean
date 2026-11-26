/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitnetContraction.RatHelpers

/-!
# Theorem 6: Exact `d = 3` vs `d = 4` Greedy vs Joint Disjoint 2-Stage Residual Ternary Crossover

Pure-`Init` Lean 4 proof (zero Mathlib) of the exact 2-stage residual ternary crossover:
- At `d = 3`, on `witnessD3Disjoint = [4096, 2583, 1070]`, Joint Disjoint achieves
  `46898841 / 49188010 ≈ 0.953461` while Greedy achieves `49056967 / 49188010 ≈ 0.997336`
  (overlapping supports let Greedy strictly beat Joint Disjoint!), and even the `d = 3`
  Greedy worst-case witness `witnessD3Greedy = [4096, 1697, 1302]` gives
  `20774823 / 21352229 ≈ 0.972958 > 46898841 / 49188010`.
- At `d = 4`, the ordering reverses: on `witnessD4Greedy = [4096, 1499, 1398, 1200]`,
  Greedy drops to `83898881 / 89674484 ≈ 0.935594` while Joint Disjoint achieves
  `67117057 / 67255863 ≈ 0.997936`, and even the `d = 4` Joint Disjoint worst-case witness
  `witnessD4Disjoint = [4096, 2365, 979, 752]` gives
  `22370441 / 23894386 ≈ 0.936222 > 83898881 / 89674484`.
-/

namespace BitnetContraction

private theorem rat_div_lt_div_of_int_cross {a b c d : Int}
    (hb : (0 : Rat) < (b : Rat)) (hd : (0 : Rat) < (d : Rat))
    (h : a * d < c * b) : (a : Rat) / (b : Rat) < (c : Rat) / (d : Rat) := by
  have hdiff_int : 0 < c * b - a * d := by omega
  have hdiff_nat : 1 ≤ (c * b - a * d).toNat := by omega
  have hcast : ((c * b - a * d).toNat : Int) = c * b - a * d := by omega
  have hdiff_pos : (0 : Rat) < ((c * b - a * d : Int) : Rat) := by
    have hp := rat_natCast_pos hdiff_nat
    have heq : (((c * b - a * d).toNat : Nat) : Rat) = ((c * b - a * d : Int) : Rat) := by
      rw [← Rat.intCast_natCast, hcast]
    rw [heq] at hp
    exact hp
  have hsub : (0 : Rat) < (c : Rat) * (b : Rat) - (a : Rat) * (d : Rat) := by
    have heq : ((c * b - a * d : Int) : Rat) = (c : Rat) * (b : Rat) - (a : Rat) * (d : Rat) := by
      grind
    rw [heq] at hdiff_pos
    exact hdiff_pos
  have hbd : (0 : Rat) < (b : Rat) * (d : Rat) := rat_mul_pos hb hd
  have hprod : (0 : Rat) < ((c : Rat) * (b : Rat) - (a : Rat) * (d : Rat)) * ((b : Rat) * (d : Rat))⁻¹ :=
    rat_mul_pos hsub (rat_inv_pos hbd)
  have hb0 : (b : Rat) ≠ 0 := (Rat.lt_iff_le_and_ne.mp hb).2.symm
  have hd0 : (d : Rat) ≠ 0 := (Rat.lt_iff_le_and_ne.mp hd).2.symm
  have heq : ((c : Rat) * (b : Rat) - (a : Rat) * (d : Rat)) * ((b : Rat) * (d : Rat))⁻¹ =
      (c : Rat) / (d : Rat) - (a : Rat) / (b : Rat) := by grind
  rw [heq] at hprod
  have h2 := Rat.add_lt_add_right (c := (a : Rat) / (b : Rat)).mpr hprod
  have e3 : 0 + (a : Rat) / (b : Rat) = (a : Rat) / (b : Rat) := by grind
  have e4 : (c : Rat) / (d : Rat) - (a : Rat) / (b : Rat) + (a : Rat) / (b : Rat) =
      (c : Rat) / (d : Rat) := by grind
  rw [e3, e4] at h2
  exact h2

/-- **Theorem 6 (Exact `d = 3` vs `d = 4` Greedy vs Joint Disjoint 2-Stage Ternary Crossover):**
    Exact rational evaluation and strict crossover inequalities for Greedy vs Joint Disjoint
    2-stage residual ternary quantization at `d = 3` and `d = 4`. -/
theorem two_stage_ternary_greedy_vs_disjoint_crossover :
    (jointDisjointTwoStageAlpha witnessD3Disjoint = (46898841 : Rat) / 49188010 ∧
     greedyTwoStageAlpha witnessD3Disjoint = (49056967 : Rat) / 49188010 ∧
     jointDisjointTwoStageAlpha witnessD3Disjoint < greedyTwoStageAlpha witnessD3Disjoint ∧
     greedyTwoStageAlpha witnessD3Greedy = (20774823 : Rat) / 21352229 ∧
     jointDisjointTwoStageAlpha witnessD3Disjoint < greedyTwoStageAlpha witnessD3Greedy) ∧
    (greedyTwoStageAlpha witnessD4Greedy = (83898881 : Rat) / 89674484 ∧
     jointDisjointTwoStageAlpha witnessD4Greedy = (67117057 : Rat) / 67255863 ∧
     greedyTwoStageAlpha witnessD4Greedy < jointDisjointTwoStageAlpha witnessD4Greedy ∧
     jointDisjointTwoStageAlpha witnessD4Disjoint = (22370441 : Rat) / 23894386 ∧
     greedyTwoStageAlpha witnessD4Greedy < jointDisjointTwoStageAlpha witnessD4Disjoint) := by
  have hd3_disj_nd : jointDisjointTwoStageNumDen witnessD3Disjoint = (46898841, 49188010) := by
    decide
  have hd3_gr_on_disj_nd : greedyTwoStageNumDen witnessD3Disjoint = (294341802, 295128060) := by
    decide
  have hd3_gr_nd : greedyTwoStageNumDen witnessD3Greedy = (560920221, 576510183) := by
    decide
  have hd4_gr_nd : greedyTwoStageNumDen witnessD4Greedy = (671191048, 717395872) := by
    decide
  have hd4_disj_on_gr_nd : jointDisjointTwoStageNumDen witnessD4Greedy = (67117057, 67255863) := by
    decide
  have hd4_disj_nd : jointDisjointTwoStageNumDen witnessD4Disjoint = (22370441, 23894386) := by
    decide
  have hd3_disj : jointDisjointTwoStageAlpha witnessD3Disjoint = (46898841 : Rat) / 49188010 := by
    unfold jointDisjointTwoStageAlpha; rw [hd3_disj_nd]; grind
  have hd3_gr_on_disj : greedyTwoStageAlpha witnessD3Disjoint = (49056967 : Rat) / 49188010 := by
    unfold greedyTwoStageAlpha; rw [hd3_gr_on_disj_nd]; grind
  have hd3_gr : greedyTwoStageAlpha witnessD3Greedy = (20774823 : Rat) / 21352229 := by
    unfold greedyTwoStageAlpha; rw [hd3_gr_nd]; grind
  have hd4_gr : greedyTwoStageAlpha witnessD4Greedy = (83898881 : Rat) / 89674484 := by
    unfold greedyTwoStageAlpha; rw [hd4_gr_nd]; grind
  have hd4_disj_on_gr : jointDisjointTwoStageAlpha witnessD4Greedy = (67117057 : Rat) / 67255863 := by
    unfold jointDisjointTwoStageAlpha; rw [hd4_disj_on_gr_nd]; grind
  have hd4_disj : jointDisjointTwoStageAlpha witnessD4Disjoint = (22370441 : Rat) / 23894386 := by
    unfold jointDisjointTwoStageAlpha; rw [hd4_disj_nd]; grind
  refine ⟨⟨hd3_disj, hd3_gr_on_disj, ?_, hd3_gr, ?_⟩,
          ⟨hd4_gr, hd4_disj_on_gr, ?_, hd4_disj, ?_⟩⟩
  · rw [hd3_disj, hd3_gr_on_disj]
    exact rat_div_lt_div_of_int_cross (by decide) (by decide) (by decide)
  · rw [hd3_disj, hd3_gr]
    exact rat_div_lt_div_of_int_cross (by decide) (by decide) (by decide)
  · rw [hd4_gr, hd4_disj_on_gr]
    exact rat_div_lt_div_of_int_cross (by decide) (by decide) (by decide)
  · rw [hd4_gr, hd4_disj]
    exact rat_div_lt_div_of_int_cross (by decide) (by decide) (by decide)

end BitnetContraction
