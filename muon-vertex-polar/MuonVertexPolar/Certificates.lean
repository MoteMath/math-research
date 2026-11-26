/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonVertexPolar.Algebra

/-!
# Certified 5-Step Adversarial Trajectory Theorems (`muon-vertex-polar`)

Proves continuous worst-case 5-step confinement over all rational adversarial
trajectories starting in `[1/100, 1]` for all four Hunt-7 shifted-square winners:
- `bf16_stationary_shifted_certified` (`[942/1000, 1052/1000]` at `u = 1/256`)
- `bf16_dp5_shifted_certified` (`[987/1000, 1013/1000]` at `u = 1/256`)
- `fp8_pure_dp5_shifted_certified` (`[31/100, 165/100]` at `u = 1/16`)
- `fp8_hybrid_dp5_shifted_certified` (`[824/1000, 1163/1000]` at `u = 1/32`)

Every step check reduces to pure `Int` Bernstein arithmetic (`zero native_decide`,
`zero Rat.normalize` in kernel `decide`).
-/

namespace MuonVertexPolar

private theorem bf16_stationary_shifted_step1 {x y : Rat}
    (hxlo : ((1 : Int) : Rat) / (100 : Int) ≤ x) (hxhi : x ≤ ((1 : Int) : Rat) / (1 : Int))
    (hstep : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((331 : Int) : Rat) / (12500 : Int) ≤ y ∧ y ≤ ((105099 : Int) : Rat) / (100000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int))
    (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((1 : Int) : Rat) / (100 : Int)) (((1 : Int) : Rat) / (1 : Int))
    (((331 : Int) : Rat) / (12500 : Int)) (((105099 : Int) : Rat) / (100000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((128 : Int) : Rat) / (12800 : Int) ≤ z := by
      have heq : ((1 : Int) : Rat) / (100 : Int) = ((128 : Int) : Rat) / (12800 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((12800 : Int) : Rat) / (12800 : Int) := by
      have heq : ((1 : Int) : Rat) / (1 : Int) = ((12800 : Int) : Rat) / (12800 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 31 32 199 128 135 128 1 256 105099 100000 7378697629483820646400000 12800
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      7754937421611200661159936 (-20266659161464919555487500) 24673785126831464352187500 (-11651509643225969277421875)
      (by decide) (by decide) (by decide) (by decide)
      128 6464 12800 [8048, 8147, 8246, 8444, 8840, 9632, 12800]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((8 : Int) : Rat) / (800 : Int) ≤ z := by
      have heq : ((1 : Int) : Rat) / (100 : Int) = ((8 : Int) : Rat) / (800 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((800 : Int) : Rat) / (800 : Int) := by
      have heq : ((1 : Int) : Rat) / (1 : Int) = ((800 : Int) : Rat) / (800 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 31 32 199 128 135 128 1 256 105099 100000 7378697629483820646400000 800
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      7754937421611200661159936 (-20266659161464919555487500) 24867305010179162111812500 (-11834995162251934560621875)
      (by decide) (by decide) (by decide) (by decide)
      8 404 800 [503, 602, 800]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    right; left
    have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
    have hz1 : ((1 : Int) : Rat) / (100 : Int) ≤ z := by
      have heq : ((1 : Int) : Rat) / (100 : Int) = ((1 : Int) : Rat) / (100 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((100 : Int) : Rat) / (100 : Int) := by
      have heq : ((1 : Int) : Rat) / (1 : Int) = ((100 : Int) : Rat) / (100 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    refine ⟨sq_mul_up_le_mu_of_int (qN := 1) (qD := 1) (uN := 1) (uD := 256) (μN := 135) (μD := 128)
      (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzhi, ?_⟩
    exact lowerLeft_cert_int 31 32 199 128 135 128 1 256 331 12500 7378697629483820646400000 100
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-195387913228731570716672) 19556787274398988534687500 (-23728542548024083007812500) 11293028583041091357421875
      (by decide) (by decide) (by decide) (by decide)
      1 100 100 []
      rfl (by decide) hz1 hz2
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem bf16_stationary_shifted_step2 {x y : Rat}
    (hxlo : ((331 : Int) : Rat) / (12500 : Int) ≤ x) (hxhi : x ≤ ((105099 : Int) : Rat) / (100000 : Int))
    (hstep : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((701 : Int) : Rat) / (10000 : Int) ≤ y ∧ y ≤ ((105099 : Int) : Rat) / (100000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int))
    (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((331 : Int) : Rat) / (12500 : Int)) (((105099 : Int) : Rat) / (100000 : Int))
    (((701 : Int) : Rat) / (10000 : Int)) (((105099 : Int) : Rat) / (100000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((338944 : Int) : Rat) / (12800000 : Int) ≤ z := by
      have heq : ((331 : Int) : Rat) / (12500 : Int) = ((338944 : Int) : Rat) / (12800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((13452672 : Int) : Rat) / (12800000 : Int) := by
      have heq : ((105099 : Int) : Rat) / (100000 : Int) = ((13452672 : Int) : Rat) / (12800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 31 32 199 128 135 128 1 256 105099 100000 7378697629483820646400000 12800000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      7754937421611200661159936 (-20266659161464919555487500) 24673785126831464352187500 (-11651509643225969277421875)
      (by decide) (by decide) (by decide) (by decide)
      338944 6895808 13452672 [7715416, 7920318, 8022769, 8125220, 8535024, 10174240, 13452672]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((21184 : Int) : Rat) / (800000 : Int) ≤ z := by
      have heq : ((331 : Int) : Rat) / (12500 : Int) = ((21184 : Int) : Rat) / (800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((840792 : Int) : Rat) / (800000 : Int) := by
      have heq : ((105099 : Int) : Rat) / (100000 : Int) = ((840792 : Int) : Rat) / (800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 31 32 199 128 135 128 1 256 105099 100000 7378697629483820646400000 800000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      7754937421611200661159936 (-20266659161464919555487500) 24867305010179162111812500 (-11834995162251934560621875)
      (by decide) (by decide) (by decide) (by decide)
      21184 430988 840792 [533439, 635890, 840792]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((10249 : Int) : Rat) / (10000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((1324 : Int) : Rat) / (50000 : Int) ≤ z := by
        have heq : ((331 : Int) : Rat) / (12500 : Int) = ((1324 : Int) : Rat) / (50000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((51245 : Int) : Rat) / (50000 : Int) := by
        have heq : ((10249 : Int) : Rat) / (10000 : Int) = ((51245 : Int) : Rat) / (50000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 10249) (qD := 10000) (uN := 1) (uD := 256) (μN := 135) (μD := 128)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 31 32 199 128 135 128 1 256 701 10000 1475739525896764129280000 50000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-103449340765363165462528) 3911357454879797706937500 (-4745708509604816601562500) 2258605716608218271484375
        (by decide) (by decide) (by decide) (by decide)
        1324 51245 51245 []
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 701) (lD := 10000) (αN := 31) (αD := 32) (uN := 1) (uD := 256) (qN := 10249) (qD := 10000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem bf16_stationary_shifted_step3 {x y : Rat}
    (hxlo : ((701 : Int) : Rat) / (10000 : Int) ≤ x) (hxhi : x ≤ ((105099 : Int) : Rat) / (100000 : Int))
    (hstep : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((18467 : Int) : Rat) / (100000 : Int) ≤ y ∧ y ≤ ((105099 : Int) : Rat) / (100000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int))
    (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((701 : Int) : Rat) / (10000 : Int)) (((105099 : Int) : Rat) / (100000 : Int))
    (((18467 : Int) : Rat) / (100000 : Int)) (((105099 : Int) : Rat) / (100000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((897280 : Int) : Rat) / (12800000 : Int) ≤ z := by
      have heq : ((701 : Int) : Rat) / (10000 : Int) = ((897280 : Int) : Rat) / (12800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((13452672 : Int) : Rat) / (12800000 : Int) := by
      have heq : ((105099 : Int) : Rat) / (100000 : Int) = ((13452672 : Int) : Rat) / (12800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 31 32 199 128 135 128 1 256 105099 100000 7378697629483820646400000 12800000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      7754937421611200661159936 (-20266659161464919555487500) 24673785126831464352187500 (-11651509643225969277421875)
      (by decide) (by decide) (by decide) (by decide)
      897280 7174976 13452672 [7959688, 8057777, 8155866, 8352044, 8744400, 10313824, 13452672]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((56080 : Int) : Rat) / (800000 : Int) ≤ z := by
      have heq : ((701 : Int) : Rat) / (10000 : Int) = ((56080 : Int) : Rat) / (800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((840792 : Int) : Rat) / (800000 : Int) := by
      have heq : ((105099 : Int) : Rat) / (100000 : Int) = ((840792 : Int) : Rat) / (800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 31 32 199 128 135 128 1 256 105099 100000 7378697629483820646400000 800000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      7754937421611200661159936 (-20266659161464919555487500) 24867305010179162111812500 (-11834995162251934560621875)
      (by decide) (by decide) (by decide) (by decide)
      56080 448436 840792 [546525, 644614, 840792]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((10249 : Int) : Rat) / (10000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((701 : Int) : Rat) / (10000 : Int) ≤ z := by
        have heq : ((701 : Int) : Rat) / (10000 : Int) = ((701 : Int) : Rat) / (10000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((10249 : Int) : Rat) / (10000 : Int) := by
        have heq : ((10249 : Int) : Rat) / (10000 : Int) = ((10249 : Int) : Rat) / (10000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 10249) (qD := 10000) (uN := 1) (uD := 256) (μN := 135) (μD := 128)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 31 32 199 128 135 128 1 256 18467 100000 7378697629483820646400000 10000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-1362624091236777158770688) 19556787274398988534687500 (-23728542548024083007812500) 11293028583041091357421875
        (by decide) (by decide) (by decide) (by decide)
        701 10249 10249 []
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 18467) (lD := 100000) (αN := 31) (αD := 32) (uN := 1) (uD := 256) (qN := 10249) (qD := 10000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem bf16_stationary_shifted_step4 {x y : Rat}
    (hxlo : ((18467 : Int) : Rat) / (100000 : Int) ≤ x) (hxhi : x ≤ ((105099 : Int) : Rat) / (100000 : Int))
    (hstep : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((46951 : Int) : Rat) / (100000 : Int) ≤ y ∧ y ≤ ((105099 : Int) : Rat) / (100000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int))
    (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((18467 : Int) : Rat) / (100000 : Int)) (((105099 : Int) : Rat) / (100000 : Int))
    (((46951 : Int) : Rat) / (100000 : Int)) (((105099 : Int) : Rat) / (100000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((147736 : Int) : Rat) / (800000 : Int) ≤ z := by
      have heq : ((18467 : Int) : Rat) / (100000 : Int) = ((147736 : Int) : Rat) / (800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((840792 : Int) : Rat) / (800000 : Int) := by
      have heq : ((105099 : Int) : Rat) / (100000 : Int) = ((840792 : Int) : Rat) / (800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 31 32 199 128 135 128 1 256 105099 100000 7378697629483820646400000 800000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      7754937421611200661159936 (-20266659161464919555487500) 24673785126831464352187500 (-11651509643225969277421875)
      (by decide) (by decide) (by decide) (by decide)
      147736 494264 840792 [505093, 515922, 537580, 580896, 667528, 840792]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((18467 : Int) : Rat) / (100000 : Int) ≤ z := by
      have heq : ((18467 : Int) : Rat) / (100000 : Int) = ((18467 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((105099 : Int) : Rat) / (100000 : Int) := by
      have heq : ((105099 : Int) : Rat) / (100000 : Int) = ((105099 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 31 32 199 128 135 128 1 256 105099 100000 7378697629483820646400000 100000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      7754937421611200661159936 (-20266659161464919555487500) 24867305010179162111812500 (-11834995162251934560621875)
      (by decide) (by decide) (by decide) (by decide)
      18467 61783 105099 [83441, 105099]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((10249 : Int) : Rat) / (10000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((18467 : Int) : Rat) / (100000 : Int) ≤ z := by
        have heq : ((18467 : Int) : Rat) / (100000 : Int) = ((18467 : Int) : Rat) / (100000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((102490 : Int) : Rat) / (100000 : Int) := by
        have heq : ((10249 : Int) : Rat) / (10000 : Int) = ((102490 : Int) : Rat) / (100000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 10249) (qD := 10000) (uN := 1) (uD := 256) (μN := 135) (μD := 128)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 31 32 199 128 135 128 1 256 46951 100000 7378697629483820646400000 100000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-3464372324018948631691264) 19556787274398988534687500 (-23728542548024083007812500) 11293028583041091357421875
        (by decide) (by decide) (by decide) (by decide)
        18467 102490 102490 []
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 46951) (lD := 100000) (αN := 31) (αD := 32) (uN := 1) (uD := 256) (qN := 10249) (qD := 10000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem bf16_stationary_shifted_step5 {x y : Rat}
    (hxlo : ((46951 : Int) : Rat) / (100000 : Int) ≤ x) (hxhi : x ≤ ((105099 : Int) : Rat) / (100000 : Int))
    (hstep : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((471 : Int) : Rat) / (500 : Int) ≤ y ∧ y ≤ ((263 : Int) : Rat) / (250 : Int) := by
  apply noisyShiftedStep_step_certified
    (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int))
    (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((46951 : Int) : Rat) / (100000 : Int)) (((105099 : Int) : Rat) / (100000 : Int))
    (((471 : Int) : Rat) / (500 : Int)) (((263 : Int) : Rat) / (250 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((93902 : Int) : Rat) / (200000 : Int) ≤ z := by
      have heq : ((46951 : Int) : Rat) / (100000 : Int) = ((93902 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((210198 : Int) : Rat) / (200000 : Int) := by
      have heq : ((105099 : Int) : Rat) / (100000 : Int) = ((210198 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 31 32 199 128 135 128 1 256 263 250 295147905179352825856000 200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      310495596248679172800512 (-810666366458596782219500) 986951405073258574087500 (-466060385729038771096875)
      (by decide) (by decide) (by decide) (by decide)
      93902 122976 210198 [137513, 152050, 210198]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((46951 : Int) : Rat) / (100000 : Int) ≤ z := by
      have heq : ((46951 : Int) : Rat) / (100000 : Int) = ((46951 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((105099 : Int) : Rat) / (100000 : Int) := by
      have heq : ((105099 : Int) : Rat) / (100000 : Int) = ((105099 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 31 32 199 128 135 128 1 256 263 250 295147905179352825856000 100000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      310495596248679172800512 (-810666366458596782219500) 994692200407166484472500 (-473399806490077382424875)
      (by decide) (by decide) (by decide) (by decide)
      46951 61488 105099 [76025, 105099]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((10249 : Int) : Rat) / (10000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((751216 : Int) : Rat) / (1600000 : Int) ≤ z := by
        have heq : ((46951 : Int) : Rat) / (100000 : Int) = ((751216 : Int) : Rat) / (1600000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((1639840 : Int) : Rat) / (1600000 : Int) := by
        have heq : ((10249 : Int) : Rat) / (10000 : Int) = ((1639840 : Int) : Rat) / (1600000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 10249) (qD := 10000) (uN := 1) (uD := 256) (μN := 135) (μD := 128)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 31 32 199 128 135 128 1 256 471 500 295147905179352825856000 1600000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-278029326678950361956352) 782271490975959541387500 (-949141701920963320312500) 451721143321643654296875
        (by decide) (by decide) (by decide) (by decide)
        751216 1195528 1639840 [1417684, 1473223, 1528762, 1639840]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 471) (lD := 500) (αN := 31) (αD := 32) (uN := 1) (uD := 256) (qN := 10249) (qD := 10000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

/-- Certified 5-step trajectory confinement for `bf16_stationary_shifted` at `uBF16`:
every adversarial trajectory starting in `[1/100, 1]` ends in `[942/1000, 1052/1000]`. -/
theorem bf16_stationary_shifted_certified (σ0 σ5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ σ0) (hhi : σ0 ≤ 1)
    (htraj : NoisyShiftedTraj5 bf16StationaryParams bf16StationaryParams bf16StationaryParams bf16StationaryParams bf16StationaryParams uBF16 σ0 σ5) :
    (942 / 1000 : Rat) ≤ σ5 ∧ σ5 ≤ (1052 / 1000 : Rat) := by
  rcases htraj with ⟨σ1, σ2, σ3, σ4, hs1, hs2, hs3, hs4, hs5⟩
  have h0lo : ((1 : Int) : Rat) / (100 : Int) ≤ σ0 := hlo
  have h0hi : σ0 ≤ ((1 : Int) : Rat) / (1 : Int) := by
    have h1 : ((1 : Int) : Rat) / ((1 : Int) : Rat) = 1 := rat_div_one_eq 1
    rw [h1]; exact hhi
  have hstep1 : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ0 σ1 := by
    have ha : (bf16StationaryParams).1 = ((31 : Int) : Rat) / (32 : Int) := rfl
    have hb : (bf16StationaryParams).2.1 = ((199 : Int) : Rat) / (128 : Int) := rfl
    have hm : (bf16StationaryParams).2.2 = ((135 : Int) : Rat) / (128 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs1
  have ⟨h1lo, h1hi⟩ := bf16_stationary_shifted_step1 h0lo h0hi hstep1
  have hstep2 : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ1 σ2 := by
    have ha : (bf16StationaryParams).1 = ((31 : Int) : Rat) / (32 : Int) := rfl
    have hb : (bf16StationaryParams).2.1 = ((199 : Int) : Rat) / (128 : Int) := rfl
    have hm : (bf16StationaryParams).2.2 = ((135 : Int) : Rat) / (128 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs2
  have ⟨h2lo, h2hi⟩ := bf16_stationary_shifted_step2 h1lo h1hi hstep2
  have hstep3 : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ2 σ3 := by
    have ha : (bf16StationaryParams).1 = ((31 : Int) : Rat) / (32 : Int) := rfl
    have hb : (bf16StationaryParams).2.1 = ((199 : Int) : Rat) / (128 : Int) := rfl
    have hm : (bf16StationaryParams).2.2 = ((135 : Int) : Rat) / (128 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs3
  have ⟨h3lo, h3hi⟩ := bf16_stationary_shifted_step3 h2lo h2hi hstep3
  have hstep4 : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ3 σ4 := by
    have ha : (bf16StationaryParams).1 = ((31 : Int) : Rat) / (32 : Int) := rfl
    have hb : (bf16StationaryParams).2.1 = ((199 : Int) : Rat) / (128 : Int) := rfl
    have hm : (bf16StationaryParams).2.2 = ((135 : Int) : Rat) / (128 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs4
  have ⟨h4lo, h4hi⟩ := bf16_stationary_shifted_step4 h3lo h3hi hstep4
  have hstep5 : NoisyShiftedStep (((31 : Int) : Rat) / (32 : Int)) (((199 : Int) : Rat) / (128 : Int)) (((135 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ4 σ5 := by
    have ha : (bf16StationaryParams).1 = ((31 : Int) : Rat) / (32 : Int) := rfl
    have hb : (bf16StationaryParams).2.1 = ((199 : Int) : Rat) / (128 : Int) := rfl
    have hm : (bf16StationaryParams).2.2 = ((135 : Int) : Rat) / (128 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs5
  have ⟨h5lo, h5hi⟩ := bf16_stationary_shifted_step5 h4lo h4hi hstep5
  have hfin_lo : ((471 : Int) : Rat) / (500 : Int) = (942 / 1000 : Rat) :=
    rat_div_eq_of_cross (by decide) (by decide) (by decide)
  have hfin_hi : ((263 : Int) : Rat) / (250 : Int) = (1052 / 1000 : Rat) :=
    rat_div_eq_of_cross (by decide) (by decide) (by decide)
  rw [hfin_lo] at h5lo
  rw [hfin_hi] at h5hi
  exact ⟨h5lo, h5hi⟩

private theorem bf16_dp5_shifted_step1 {x y : Rat}
    (hxlo : ((1 : Int) : Rat) / (100 : Int) ≤ x) (hxhi : x ≤ ((1 : Int) : Rat) / (1 : Int))
    (hstep : NoisyShiftedStep (((73 : Int) : Rat) / (1024 : Int)) (((51 : Int) : Rat) / (4 : Int)) (((173 : Int) : Rat) / (256 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((2877 : Int) : Rat) / (50000 : Int) ≤ y ∧ y ≤ ((14771 : Int) : Rat) / (10000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((73 : Int) : Rat) / (1024 : Int)) (((51 : Int) : Rat) / (4 : Int))
    (((173 : Int) : Rat) / (256 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((1 : Int) : Rat) / (100 : Int)) (((1 : Int) : Rat) / (1 : Int))
    (((2877 : Int) : Rat) / (50000 : Int)) (((14771 : Int) : Rat) / (10000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((8 : Int) : Rat) / (800 : Int) ≤ z := by
      have heq : ((1 : Int) : Rat) / (100 : Int) = ((8 : Int) : Rat) / (800 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((800 : Int) : Rat) / (800 : Int) := by
      have heq : ((1 : Int) : Rat) / (1 : Int) = ((800 : Int) : Rat) / (800 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 73 1024 51 4 173 256 1 256 14771 10000 46116860184273879040000 800
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      68119214178190946729984 (-278192095059153829826875) 810336148051494546731250 (-597213057089974304671875)
      (by decide) (by decide) (by decide) (by decide)
      8 206 800 [305, 404, 800]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((4 : Int) : Rat) / (400 : Int) ≤ z := by
      have heq : ((1 : Int) : Rat) / (100 : Int) = ((4 : Int) : Rat) / (400 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((400 : Int) : Rat) / (400 : Int) := by
      have heq : ((1 : Int) : Rat) / (1 : Int) = ((400 : Int) : Rat) / (400 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 73 1024 51 4 173 256 1 256 14771 10000 46116860184273879040000 400
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      68119214178190946729984 (-278192095059153829826875) 816691725683270974548750 (-606617842487285088031875)
      (by decide) (by decide) (by decide) (by decide)
      4 103 400 [202, 400]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((2051 : Int) : Rat) / (2500 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((400 : Int) : Rat) / (40000 : Int) ≤ z := by
        have heq : ((1 : Int) : Rat) / (100 : Int) = ((400 : Int) : Rat) / (40000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((32816 : Int) : Rat) / (40000 : Int) := by
        have heq : ((2051 : Int) : Rat) / (2500 : Int) = ((32816 : Int) : Rat) / (40000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 2051) (qD := 2500) (uN := 1) (uD := 256) (μN := 173) (μD := 256)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 73 1024 51 4 173 256 1 256 2877 50000 230584300921369395200000 40000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-13267820675015594999808) 1327765248607603462734375 (-3896462514446612402343750) 2894193254950229443359375
        (by decide) (by decide) (by decide) (by decide)
        400 16608 32816 [24712, 28764, 30790, 31803, 32816]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 2877) (lD := 50000) (αN := 73) (αD := 1024) (uN := 1) (uD := 256) (qN := 2051) (qD := 2500)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem bf16_dp5_shifted_step2 {x y : Rat}
    (hxlo : ((2877 : Int) : Rat) / (50000 : Int) ≤ x) (hxhi : x ≤ ((14771 : Int) : Rat) / (10000 : Int))
    (hstep : NoisyShiftedStep (((59 : Int) : Rat) / (512 : Int)) (((65 : Int) : Rat) / (64 : Int)) (((195 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((6923 : Int) : Rat) / (50000 : Int) ≤ y ∧ y ≤ ((9193 : Int) : Rat) / (10000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((59 : Int) : Rat) / (512 : Int)) (((65 : Int) : Rat) / (64 : Int))
    (((195 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((2877 : Int) : Rat) / (50000 : Int)) (((14771 : Int) : Rat) / (10000 : Int))
    (((6923 : Int) : Rat) / (50000 : Int)) (((9193 : Int) : Rat) / (10000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((184128 : Int) : Rat) / (3200000 : Int) ≤ z := by
      have heq : ((2877 : Int) : Rat) / (50000 : Int) = ((184128 : Int) : Rat) / (3200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((4726720 : Int) : Rat) / (3200000 : Int) := by
      have heq : ((14771 : Int) : Rat) / (10000 : Int) = ((4726720 : Int) : Rat) / (3200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 59 512 65 64 195 128 1 256 9193 10000 737869762948382064640000 3200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      678323673078447632023552 (-1866108881523177787382500) 2328235447478792560312500 (-761153896291143721640625)
      (by decide) (by decide) (by decide) (by decide)
      184128 1319776 4726720 [1603688, 1745644, 1816622, 1852111, 1887600, 2455424, 4726720]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((23016 : Int) : Rat) / (400000 : Int) ≤ z := by
      have heq : ((2877 : Int) : Rat) / (50000 : Int) = ((23016 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((590840 : Int) : Rat) / (400000 : Int) := by
      have heq : ((14771 : Int) : Rat) / (10000 : Int) = ((590840 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 59 512 65 64 195 128 1 256 9193 10000 737869762948382064640000 400000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      678323673078447632023552 (-1866108881523177787382500) 2346496117655096815687500 (-773140387483794720040625)
      (by decide) (by decide) (by decide) (by decide)
      23016 164972 590840 [200461, 235950, 306928, 590840]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((6159 : Int) : Rat) / (5000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((46032 : Int) : Rat) / (800000 : Int) ≤ z := by
        have heq : ((2877 : Int) : Rat) / (50000 : Int) = ((46032 : Int) : Rat) / (800000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((985440 : Int) : Rat) / (800000 : Int) := by
        have heq : ((6159 : Int) : Rat) / (5000 : Int) = ((985440 : Int) : Rat) / (800000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 6159) (qD := 5000) (uN := 1) (uD := 256) (μN := 195) (μD := 128)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 59 512 65 64 195 128 1 256 6923 50000 3689348814741910323200000 800000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-510827236889164903350272) 8916243800527080655312500 (-11195208516516108398437500) 3688677677877743408203125
        (by decide) (by decide) (by decide) (by decide)
        46032 515736 985440 [750588, 868014, 926727, 985440]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 6923) (lD := 50000) (αN := 59) (αD := 512) (uN := 1) (uD := 256) (qN := 6159) (qD := 5000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem bf16_dp5_shifted_step3 {x y : Rat}
    (hxlo : ((6923 : Int) : Rat) / (50000 : Int) ≤ x) (hxhi : x ≤ ((9193 : Int) : Rat) / (10000 : Int))
    (hstep : NoisyShiftedStep (((11 : Int) : Rat) / (16 : Int)) (((8 : Int) : Rat) / (1 : Int)) (((171 : Int) : Rat) / (256 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((27461 : Int) : Rat) / (50000 : Int) ≤ y ∧ y ≤ ((7033 : Int) : Rat) / (6250 : Int) := by
  apply noisyShiftedStep_step_certified
    (((11 : Int) : Rat) / (16 : Int)) (((8 : Int) : Rat) / (1 : Int))
    (((171 : Int) : Rat) / (256 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((6923 : Int) : Rat) / (50000 : Int)) (((9193 : Int) : Rat) / (10000 : Int))
    (((27461 : Int) : Rat) / (50000 : Int)) (((7033 : Int) : Rat) / (6250 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((443072 : Int) : Rat) / (3200000 : Int) ≤ z := by
      have heq : ((6923 : Int) : Rat) / (50000 : Int) = ((443072 : Int) : Rat) / (3200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((2941760 : Int) : Rat) / (3200000 : Int) := by
      have heq : ((9193 : Int) : Rat) / (10000 : Int) = ((2941760 : Int) : Rat) / (3200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 11 16 8 1 171 256 1 256 7033 6250 7205759403792793600000 3200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      8108496941899954782208 (-31322139205095584178125) 78526284323249216531250 (-58550299714703363203125)
      (by decide) (by decide) (by decide) (by decide)
      443072 1067744 2941760 [1223912, 1301996, 1321517, 1341038, 1380080, 1692416, 2941760]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((27692 : Int) : Rat) / (200000 : Int) ≤ z := by
      have heq : ((6923 : Int) : Rat) / (50000 : Int) = ((27692 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((183860 : Int) : Rat) / (200000 : Int) := by
      have heq : ((9193 : Int) : Rat) / (10000 : Int) = ((183860 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 11 16 8 1 171 256 1 256 7033 6250 7205759403792793600000 200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      8108496941899954782208 (-31322139205095584178125) 79142176749313916268750 (-59472337498753440003125)
      (by decide) (by decide) (by decide) (by decide)
      27692 66734 183860 [86255, 105776, 183860]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((8157 : Int) : Rat) / (10000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((221536 : Int) : Rat) / (1600000 : Int) ≤ z := by
        have heq : ((6923 : Int) : Rat) / (50000 : Int) = ((221536 : Int) : Rat) / (1600000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((1305120 : Int) : Rat) / (1600000 : Int) := by
        have heq : ((8157 : Int) : Rat) / (10000 : Int) = ((1305120 : Int) : Rat) / (1600000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 8157) (qD := 10000) (uN := 1) (uD := 256) (μN := 171) (μD := 256)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 11 16 8 1 171 256 1 256 27461 50000 7205759403792793600000 1600000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-3957547179751078100992) 30039016531855382578125 (-75517974608451855468750) 56748887351965283203125
        (by decide) (by decide) (by decide) (by decide)
        221536 763328 1305120 [1034224, 1169672, 1237396, 1254327, 1271258, 1305120]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 27461) (lD := 50000) (αN := 11) (αD := 16) (uN := 1) (uD := 256) (qN := 8157) (qD := 10000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem bf16_dp5_shifted_step4 {x y : Rat}
    (hxlo : ((27461 : Int) : Rat) / (50000 : Int) ≤ x) (hxhi : x ≤ ((7033 : Int) : Rat) / (6250 : Int))
    (hstep : NoisyShiftedStep (((25 : Int) : Rat) / (32 : Int)) (((13 : Int) : Rat) / (16 : Int)) (((163 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((8327 : Int) : Rat) / (10000 : Int) ≤ y ∧ y ≤ ((91037 : Int) : Rat) / (100000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((25 : Int) : Rat) / (32 : Int)) (((13 : Int) : Rat) / (16 : Int))
    (((163 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((27461 : Int) : Rat) / (50000 : Int)) (((7033 : Int) : Rat) / (6250 : Int))
    (((8327 : Int) : Rat) / (10000 : Int)) (((91037 : Int) : Rat) / (100000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((878752 : Int) : Rat) / (1600000 : Int) ≤ z := by
      have heq : ((27461 : Int) : Rat) / (50000 : Int) = ((878752 : Int) : Rat) / (1600000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((1800448 : Int) : Rat) / (1600000 : Int) := by
      have heq : ((7033 : Int) : Rat) / (6250 : Int) = ((1800448 : Int) : Rat) / (1600000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 25 32 13 16 163 128 1 256 91037 100000 922337203685477580800000 1600000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      839668120119148225232896 (-1970236296348302960662500) 1946166040713041986312500 (-761153896291143721640625)
      (by decide) (by decide) (by decide) (by decide)
      878752 1109176 1800448 [1137979, 1166782, 1224388, 1339600, 1800448]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((109844 : Int) : Rat) / (200000 : Int) ≤ z := by
      have heq : ((27461 : Int) : Rat) / (50000 : Int) = ((109844 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((225056 : Int) : Rat) / (200000 : Int) := by
      have heq : ((7033 : Int) : Rat) / (6250 : Int) = ((225056 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 25 32 13 16 163 128 1 256 91037 100000 922337203685477580800000 200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      839668120119148225232896 (-1970236296348302960662500) 1961430088091183492087500 (-773140387483794720040625)
      (by decide) (by decide) (by decide) (by decide)
      109844 138647 225056 [167450, 225056]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    right; left
    have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
    have hz1 : ((1757504 : Int) : Rat) / (3200000 : Int) ≤ z := by
      have heq : ((27461 : Int) : Rat) / (50000 : Int) = ((1757504 : Int) : Rat) / (3200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((3600896 : Int) : Rat) / (3200000 : Int) := by
      have heq : ((7033 : Int) : Rat) / (6250 : Int) = ((3600896 : Int) : Rat) / (3200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    refine ⟨sq_mul_up_le_mu_of_int (qN := 7033) (qD := 6250) (uN := 1) (uD := 256) (μN := 163) (μD := 128)
      (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzhi, ?_⟩
    exact lowerLeft_cert_int 25 32 13 16 163 128 1 256 8327 10000 184467440737095516160000 3200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-153606037901779436306432) 380401839442346807812500 (-374321843731718085937500) 147547107115109736328125
      (by decide) (by decide) (by decide) (by decide)
      1757504 2679200 3600896 [3140048, 3197654, 3226457, 3255260, 3370472, 3600896]
      rfl (by decide) hz1 hz2
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem bf16_dp5_shifted_step5 {x y : Rat}
    (hxlo : ((8327 : Int) : Rat) / (10000 : Int) ≤ x) (hxhi : x ≤ ((91037 : Int) : Rat) / (100000 : Int))
    (hstep : NoisyShiftedStep (((1 : Int) : Rat) / (1 : Int)) (((31 : Int) : Rat) / (32 : Int)) (((147 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) x y) :
    ((987 : Int) : Rat) / (1000 : Int) ≤ y ∧ y ≤ ((1013 : Int) : Rat) / (1000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((1 : Int) : Rat) / (1 : Int)) (((31 : Int) : Rat) / (32 : Int))
    (((147 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int))
    (((8327 : Int) : Rat) / (10000 : Int)) (((91037 : Int) : Rat) / (100000 : Int))
    (((987 : Int) : Rat) / (1000 : Int)) (((1013 : Int) : Rat) / (1000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((83270 : Int) : Rat) / (100000 : Int) ≤ z := by
      have heq : ((8327 : Int) : Rat) / (10000 : Int) = ((83270 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((91037 : Int) : Rat) / (100000 : Int) := by
      have heq : ((91037 : Int) : Rat) / (100000 : Int) = ((91037 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 1 1 31 32 147 128 1 256 1013 1000 73786976294838206464000 100000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      74746206986671103148032 (-170872961187936190811500) 167412527560723592857500 (-72602371646232170371875)
      (by decide) (by decide) (by decide) (by decide)
      83270 91037 91037 []
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((83270 : Int) : Rat) / (100000 : Int) ≤ z := by
      have heq : ((8327 : Int) : Rat) / (10000 : Int) = ((83270 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((91037 : Int) : Rat) / (100000 : Int) := by
      have heq : ((91037 : Int) : Rat) / (100000 : Int) = ((91037 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 1 1 31 32 147 128 1 256 1013 1000 73786976294838206464000 100000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      74746206986671103148032 (-170872961187936190811500) 168725566992572405350500 (-73745698498454265603875)
      (by decide) (by decide) (by decide) (by decide)
      83270 91037 91037 []
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    right; left
    have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
    have hz1 : ((83270 : Int) : Rat) / (100000 : Int) ≤ z := by
      have heq : ((8327 : Int) : Rat) / (10000 : Int) = ((83270 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((91037 : Int) : Rat) / (100000 : Int) := by
      have heq : ((91037 : Int) : Rat) / (100000 : Int) = ((91037 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    refine ⟨sq_mul_up_le_mu_of_int (qN := 91037) (qD := 100000) (uN := 1) (uD := 256) (μN := 147) (μD := 128)
      (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzhi, ?_⟩
    exact lowerLeft_cert_int 1 1 31 32 147 128 1 256 987 1000 73786976294838206464000 100000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-72827745603005309779968) 165300576409989117787500 (-160999022358229289062500) 70368620316436951171875
      (by decide) (by decide) (by decide) (by decide)
      83270 91037 91037 []
      rfl (by decide) hz1 hz2
  · exact hxlo
  · exact hxhi
  · exact hstep

/-- Certified 5-step trajectory confinement for `bf16_dp5_shifted` at `uBF16`:
every adversarial trajectory starting in `[1/100, 1]` ends in `[987/1000, 1013/1000]`. -/
theorem bf16_dp5_shifted_certified (σ0 σ5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ σ0) (hhi : σ0 ≤ 1)
    (htraj : NoisyShiftedTraj5 bf16DP5Step1 bf16DP5Step2 bf16DP5Step3 bf16DP5Step4 bf16DP5Step5 uBF16 σ0 σ5) :
    (987 / 1000 : Rat) ≤ σ5 ∧ σ5 ≤ (1013 / 1000 : Rat) := by
  rcases htraj with ⟨σ1, σ2, σ3, σ4, hs1, hs2, hs3, hs4, hs5⟩
  have h0lo : ((1 : Int) : Rat) / (100 : Int) ≤ σ0 := hlo
  have h0hi : σ0 ≤ ((1 : Int) : Rat) / (1 : Int) := by
    have h1 : ((1 : Int) : Rat) / ((1 : Int) : Rat) = 1 := rat_div_one_eq 1
    rw [h1]; exact hhi
  have hstep1 : NoisyShiftedStep (((73 : Int) : Rat) / (1024 : Int)) (((51 : Int) : Rat) / (4 : Int)) (((173 : Int) : Rat) / (256 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ0 σ1 := by
    have ha : (bf16DP5Step1).1 = ((73 : Int) : Rat) / (1024 : Int) := rfl
    have hb : (bf16DP5Step1).2.1 = ((51 : Int) : Rat) / (4 : Int) := rfl
    have hm : (bf16DP5Step1).2.2 = ((173 : Int) : Rat) / (256 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs1
  have ⟨h1lo, h1hi⟩ := bf16_dp5_shifted_step1 h0lo h0hi hstep1
  have hstep2 : NoisyShiftedStep (((59 : Int) : Rat) / (512 : Int)) (((65 : Int) : Rat) / (64 : Int)) (((195 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ1 σ2 := by
    have ha : (bf16DP5Step2).1 = ((59 : Int) : Rat) / (512 : Int) := rfl
    have hb : (bf16DP5Step2).2.1 = ((65 : Int) : Rat) / (64 : Int) := rfl
    have hm : (bf16DP5Step2).2.2 = ((195 : Int) : Rat) / (128 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs2
  have ⟨h2lo, h2hi⟩ := bf16_dp5_shifted_step2 h1lo h1hi hstep2
  have hstep3 : NoisyShiftedStep (((11 : Int) : Rat) / (16 : Int)) (((8 : Int) : Rat) / (1 : Int)) (((171 : Int) : Rat) / (256 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ2 σ3 := by
    have ha : (bf16DP5Step3).1 = ((11 : Int) : Rat) / (16 : Int) := rfl
    have hb : (bf16DP5Step3).2.1 = ((8 : Int) : Rat) / (1 : Int) := (rat_div_one_eq 8).symm
    have hm : (bf16DP5Step3).2.2 = ((171 : Int) : Rat) / (256 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs3
  have ⟨h3lo, h3hi⟩ := bf16_dp5_shifted_step3 h2lo h2hi hstep3
  have hstep4 : NoisyShiftedStep (((25 : Int) : Rat) / (32 : Int)) (((13 : Int) : Rat) / (16 : Int)) (((163 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ3 σ4 := by
    have ha : (bf16DP5Step4).1 = ((25 : Int) : Rat) / (32 : Int) := rfl
    have hb : (bf16DP5Step4).2.1 = ((13 : Int) : Rat) / (16 : Int) := rfl
    have hm : (bf16DP5Step4).2.2 = ((163 : Int) : Rat) / (128 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs4
  have ⟨h4lo, h4hi⟩ := bf16_dp5_shifted_step4 h3lo h3hi hstep4
  have hstep5 : NoisyShiftedStep (((1 : Int) : Rat) / (1 : Int)) (((31 : Int) : Rat) / (32 : Int)) (((147 : Int) : Rat) / (128 : Int)) (((1 : Int) : Rat) / (256 : Int)) σ4 σ5 := by
    have ha : (bf16DP5Step5).1 = ((1 : Int) : Rat) / (1 : Int) := (rat_div_one_eq 1).symm
    have hb : (bf16DP5Step5).2.1 = ((31 : Int) : Rat) / (32 : Int) := rfl
    have hm : (bf16DP5Step5).2.2 = ((147 : Int) : Rat) / (128 : Int) := rfl
    have hu : uBF16 = ((1 : Int) : Rat) / (256 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs5
  have ⟨h5lo, h5hi⟩ := bf16_dp5_shifted_step5 h4lo h4hi hstep5
  have hfin_lo : ((987 : Int) : Rat) / (1000 : Int) = (987 / 1000 : Rat) :=
    rat_div_eq_of_cross (by decide) (by decide) (by decide)
  have hfin_hi : ((1013 : Int) : Rat) / (1000 : Int) = (1013 / 1000 : Rat) :=
    rat_div_eq_of_cross (by decide) (by decide) (by decide)
  rw [hfin_lo] at h5lo
  rw [hfin_hi] at h5hi
  exact ⟨h5lo, h5hi⟩

private theorem fp8_pure_dp5_shifted_step1 {x y : Rat}
    (hxlo : ((1 : Int) : Rat) / (100 : Int) ≤ x) (hxhi : x ≤ ((1 : Int) : Rat) / (1 : Int))
    (hstep : NoisyShiftedStep (((13 : Int) : Rat) / (32 : Int)) (((11 : Int) : Rat) / (2 : Int)) (((3 : Int) : Rat) / (4 : Int)) (((1 : Int) : Rat) / (16 : Int)) x y) :
    ((1227 : Int) : Rat) / (50000 : Int) ≤ y ∧ y ≤ ((33221 : Int) : Rat) / (25000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((13 : Int) : Rat) / (32 : Int)) (((11 : Int) : Rat) / (2 : Int))
    (((3 : Int) : Rat) / (4 : Int)) (((1 : Int) : Rat) / (16 : Int))
    (((1 : Int) : Rat) / (100 : Int)) (((1 : Int) : Rat) / (1 : Int))
    (((1227 : Int) : Rat) / (50000 : Int)) (((33221 : Int) : Rat) / (25000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((128 : Int) : Rat) / (12800 : Int) ≤ z := by
      have heq : ((1 : Int) : Rat) / (100 : Int) = ((128 : Int) : Rat) / (12800 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((12800 : Int) : Rat) / (12800 : Int) := by
      have heq : ((1 : Int) : Rat) / (1 : Int) = ((12800 : Int) : Rat) / (12800 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 13 32 11 2 3 4 1 16 33221 25000 26843545600000 12800
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      35670777135104 (-131791904150000) 298702416375000 (-186689010234375)
      (by decide) (by decide) (by decide) (by decide)
      128 3296 12800 [4880, 5276, 5375, 5474, 5672, 6464, 12800]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((4 : Int) : Rat) / (400 : Int) ≤ z := by
      have heq : ((1 : Int) : Rat) / (100 : Int) = ((4 : Int) : Rat) / (400 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((400 : Int) : Rat) / (400 : Int) := by
      have heq : ((1 : Int) : Rat) / (1 : Int) = ((400 : Int) : Rat) / (400 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 13 32 11 2 3 4 1 16 33221 25000 26843545600000 400
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      35670777135104 (-131791904150000) 338529405225000 (-239791662034375)
      (by decide) (by decide) (by decide) (by decide)
      4 103 400 [202, 400]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((8401 : Int) : Rat) / (10000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((100 : Int) : Rat) / (10000 : Int) ≤ z := by
        have heq : ((1 : Int) : Rat) / (100 : Int) = ((100 : Int) : Rat) / (10000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((8401 : Int) : Rat) / (10000 : Int) := by
        have heq : ((8401 : Int) : Rat) / (10000 : Int) = ((8401 : Int) : Rat) / (10000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 8401) (qD := 10000) (uN := 1) (uD := 16) (μN := 3) (μD := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 13 32 11 2 3 4 1 16 1227 50000 26843545600000 10000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-658740609024) 65968233750000 (-159753515625000) 113158740234375
        (by decide) (by decide) (by decide) (by decide)
        100 8401 8401 []
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 1227) (lD := 50000) (αN := 13) (αD := 32) (uN := 1) (uD := 16) (qN := 8401) (qD := 10000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem fp8_pure_dp5_shifted_step2 {x y : Rat}
    (hxlo : ((1227 : Int) : Rat) / (50000 : Int) ≤ x) (hxhi : x ≤ ((33221 : Int) : Rat) / (25000 : Int))
    (hstep : NoisyShiftedStep (((1 : Int) : Rat) / (8 : Int)) (((11 : Int) : Rat) / (16 : Int)) (((11 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (16 : Int)) x y) :
    ((2431 : Int) : Rat) / (100000 : Int) ≤ y ∧ y ≤ ((36323 : Int) : Rat) / (50000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((1 : Int) : Rat) / (8 : Int)) (((11 : Int) : Rat) / (16 : Int))
    (((11 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (16 : Int))
    (((1227 : Int) : Rat) / (50000 : Int)) (((33221 : Int) : Rat) / (25000 : Int))
    (((2431 : Int) : Rat) / (100000 : Int)) (((36323 : Int) : Rat) / (50000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((157056 : Int) : Rat) / (6400000 : Int) ≤ z := by
      have heq : ((1227 : Int) : Rat) / (50000 : Int) = ((157056 : Int) : Rat) / (6400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((8504576 : Int) : Rat) / (6400000 : Int) := by
      have heq : ((33221 : Int) : Rat) / (25000 : Int) = ((8504576 : Int) : Rat) / (6400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 1 8 11 16 11 8 1 16 36323 50000 214748364800000 6400000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      156006097092608 (-431892650637500) 547621096687500 (-186689010234375)
      (by decide) (by decide) (by decide) (by decide)
      157056 2243936 8504576 [3287376, 3548236, 3613451, 3678666, 3809096, 4330816, 8504576]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((4908 : Int) : Rat) / (200000 : Int) ≤ z := by
      have heq : ((1227 : Int) : Rat) / (50000 : Int) = ((4908 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((265768 : Int) : Rat) / (200000 : Int) := by
      have heq : ((33221 : Int) : Rat) / (25000 : Int) = ((265768 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 1 8 11 16 11 8 1 16 36323 50000 214748364800000 200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      156006097092608 (-431892650637500) 620637242912500 (-239791662034375)
      (by decide) (by decide) (by decide) (by decide)
      4908 70123 265768 [135338, 265768]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((91 : Int) : Rat) / (80 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((1227 : Int) : Rat) / (50000 : Int) ≤ z := by
        have heq : ((1227 : Int) : Rat) / (50000 : Int) = ((1227 : Int) : Rat) / (50000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((56875 : Int) : Rat) / (50000 : Int) := by
        have heq : ((91 : Int) : Rat) / (80 : Int) = ((56875 : Int) : Rat) / (50000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 91) (qD := 80) (uN := 1) (uD := 16) (μN := 11) (μD := 8)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 1 8 11 16 11 8 1 16 2431 100000 214748364800000 50000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-5220532748288) 213104483437500 (-292881445312500) 113158740234375
        (by decide) (by decide) (by decide) (by decide)
        1227 56875 56875 []
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 2431) (lD := 100000) (αN := 1) (αD := 8) (uN := 1) (uD := 16) (qN := 91) (qD := 80)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem fp8_pure_dp5_shifted_step3 {x y : Rat}
    (hxlo : ((2431 : Int) : Rat) / (100000 : Int) ≤ x) (hxhi : x ≤ ((36323 : Int) : Rat) / (50000 : Int))
    (hstep : NoisyShiftedStep (((9 : Int) : Rat) / (64 : Int)) (((18 : Int) : Rat) / (1 : Int)) (((13 : Int) : Rat) / (32 : Int)) (((1 : Int) : Rat) / (16 : Int)) x y) :
    ((2593 : Int) : Rat) / (50000 : Int) ≤ y ∧ y ≤ ((85257 : Int) : Rat) / (100000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((9 : Int) : Rat) / (64 : Int)) (((18 : Int) : Rat) / (1 : Int))
    (((13 : Int) : Rat) / (32 : Int)) (((1 : Int) : Rat) / (16 : Int))
    (((2431 : Int) : Rat) / (100000 : Int)) (((36323 : Int) : Rat) / (50000 : Int))
    (((2593 : Int) : Rat) / (50000 : Int)) (((85257 : Int) : Rat) / (100000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((311168 : Int) : Rat) / (12800000 : Int) ≤ z := by
      have heq : ((2431 : Int) : Rat) / (100000 : Int) = ((311168 : Int) : Rat) / (12800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((9298688 : Int) : Rat) / (12800000 : Int) := by
      have heq : ((36323 : Int) : Rat) / (50000 : Int) = ((9298688 : Int) : Rat) / (12800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 9 64 18 1 13 32 1 16 85257 100000 26843545600000 12800000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      22886001672192 (-118990361053125) 529517919937500 (-610982215312500)
      (by decide) (by decide) (by decide) (by decide)
      311168 2558048 9298688 [3681488, 3821918, 3892133, 3962348, 4243208, 4804928, 9298688]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((9724 : Int) : Rat) / (400000 : Int) ≤ z := by
      have heq : ((2431 : Int) : Rat) / (100000 : Int) = ((9724 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((290584 : Int) : Rat) / (400000 : Int) := by
      have heq : ((36323 : Int) : Rat) / (50000 : Int) = ((290584 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 9 64 18 1 13 32 1 16 85257 100000 26843545600000 400000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      22886001672192 (-118990361053125) 600120309262500 (-784772712112500)
      (by decide) (by decide) (by decide) (by decide)
      9724 79939 290584 [150154, 290584]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((6183 : Int) : Rat) / (10000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((2431 : Int) : Rat) / (100000 : Int) ≤ z := by
        have heq : ((2431 : Int) : Rat) / (100000 : Int) = ((2431 : Int) : Rat) / (100000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((61830 : Int) : Rat) / (100000 : Int) := by
        have heq : ((6183 : Int) : Rat) / (10000 : Int) = ((61830 : Int) : Rat) / (100000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 6183) (qD := 10000) (uN := 1) (uD := 16) (μN := 13) (μD := 32)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 9 64 18 1 13 32 1 16 2593 50000 26843545600000 100000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-1392106274816) 57458824453125 (-283199414062500) 370337695312500
        (by decide) (by decide) (by decide) (by decide)
        2431 61830 61830 []
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 2593) (lD := 50000) (αN := 9) (αD := 64) (uN := 1) (uD := 16) (qN := 6183) (qD := 10000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem fp8_pure_dp5_shifted_step4 {x y : Rat}
    (hxlo : ((2593 : Int) : Rat) / (50000 : Int) ≤ x) (hxhi : x ≤ ((85257 : Int) : Rat) / (100000 : Int))
    (hstep : NoisyShiftedStep (((9 : Int) : Rat) / (32 : Int)) (((14 : Int) : Rat) / (1 : Int)) (((9 : Int) : Rat) / (16 : Int)) (((1 : Int) : Rat) / (16 : Int)) x y) :
    ((8359 : Int) : Rat) / (50000 : Int) ≤ y ∧ y ≤ ((9529 : Int) : Rat) / (6250 : Int) := by
  apply noisyShiftedStep_step_certified
    (((9 : Int) : Rat) / (32 : Int)) (((14 : Int) : Rat) / (1 : Int))
    (((9 : Int) : Rat) / (16 : Int)) (((1 : Int) : Rat) / (16 : Int))
    (((2593 : Int) : Rat) / (50000 : Int)) (((85257 : Int) : Rat) / (100000 : Int))
    (((8359 : Int) : Rat) / (50000 : Int)) (((9529 : Int) : Rat) / (6250 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((1327616 : Int) : Rat) / (25600000 : Int) ≤ z := by
      have heq : ((2593 : Int) : Rat) / (50000 : Int) = ((1327616 : Int) : Rat) / (25600000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((21825792 : Int) : Rat) / (25600000 : Int) := by
      have heq : ((85257 : Int) : Rat) / (100000 : Int) = ((21825792 : Int) : Rat) / (25600000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 9 32 14 1 9 16 1 16 9529 6250 6710886400000 25600000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      10231685840896 (-44899494271875) 142562516906250 (-118802097421875)
      (by decide) (by decide) (by decide) (by decide)
      1327616 6452160 21825792 [9014432, 9094503, 9174574, 9334716, 9655000, 10295568, 11576704, 21825792]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((20744 : Int) : Rat) / (400000 : Int) ≤ z := by
      have heq : ((2593 : Int) : Rat) / (50000 : Int) = ((20744 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((341028 : Int) : Rat) / (400000 : Int) := by
      have heq : ((85257 : Int) : Rat) / (100000 : Int) = ((341028 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 9 32 14 1 9 16 1 16 9529 6250 6710886400000 400000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      10231685840896 (-44899494271875) 161570852493750 (-152594694021875)
      (by decide) (by decide) (by decide) (by decide)
      20744 100815 341028 [180886, 341028]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((1819 : Int) : Rat) / (2500 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((10372 : Int) : Rat) / (200000 : Int) ≤ z := by
        have heq : ((2593 : Int) : Rat) / (50000 : Int) = ((10372 : Int) : Rat) / (200000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((145520 : Int) : Rat) / (200000 : Int) := by
        have heq : ((1819 : Int) : Rat) / (2500 : Int) = ((145520 : Int) : Rat) / (200000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 1819) (qD := 2500) (uN := 1) (uD := 16) (μN := 9) (μD := 16)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 9 32 14 1 9 16 1 16 8359 50000 6710886400000 200000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-1121925988352) 21841643671875 (-76245996093750) 72010107421875
        (by decide) (by decide) (by decide) (by decide)
        10372 77946 145520 [111733, 145520]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 8359) (lD := 50000) (αN := 9) (αD := 32) (uN := 1) (uD := 16) (qN := 1819) (qD := 2500)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem fp8_pure_dp5_shifted_step5 {x y : Rat}
    (hxlo : ((8359 : Int) : Rat) / (50000 : Int) ≤ x) (hxhi : x ≤ ((9529 : Int) : Rat) / (6250 : Int))
    (hstep : NoisyShiftedStep (((5 : Int) : Rat) / (16 : Int)) (((11 : Int) : Rat) / (16 : Int)) (((15 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (16 : Int)) x y) :
    ((31 : Int) : Rat) / (100 : Int) ≤ y ∧ y ≤ ((33 : Int) : Rat) / (20 : Int) := by
  apply noisyShiftedStep_step_certified
    (((5 : Int) : Rat) / (16 : Int)) (((11 : Int) : Rat) / (16 : Int))
    (((15 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (16 : Int))
    (((8359 : Int) : Rat) / (50000 : Int)) (((9529 : Int) : Rat) / (6250 : Int))
    (((31 : Int) : Rat) / (100 : Int)) (((33 : Int) : Rat) / (20 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((66872 : Int) : Rat) / (400000 : Int) ≤ z := by
      have heq : ((8359 : Int) : Rat) / (50000 : Int) = ((66872 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((609856 : Int) : Rat) / (400000 : Int) := by
      have heq : ((9529 : Int) : Rat) / (6250 : Int) = ((609856 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 5 16 11 16 15 8 1 16 33 20 343597383680 400000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      566935683072 (-1316025051100) 1194809665500 (-298702416375)
      (by decide) (by decide) (by decide) (by decide)
      66872 202618 609856 [270491, 338364, 609856]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((33436 : Int) : Rat) / (200000 : Int) ≤ z := by
      have heq : ((8359 : Int) : Rat) / (50000 : Int) = ((33436 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((304928 : Int) : Rat) / (200000 : Int) := by
      have heq : ((9529 : Int) : Rat) / (6250 : Int) = ((304928 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 5 16 11 16 15 8 1 16 33 20 343597383680 200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      566935683072 (-1316025051100) 1354117620900 (-383666659255)
      (by decide) (by decide) (by decide) (by decide)
      33436 101309 304928 [169182, 304928]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((3321 : Int) : Rat) / (2500 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((16718 : Int) : Rat) / (100000 : Int) ≤ z := by
        have heq : ((8359 : Int) : Rat) / (50000 : Int) = ((16718 : Int) : Rat) / (100000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((132840 : Int) : Rat) / (100000 : Int) := by
        have heq : ((3321 : Int) : Rat) / (2500 : Int) = ((132840 : Int) : Rat) / (100000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 3321) (qD := 2500) (uN := 1) (uD := 16) (μN := 15) (μD := 8)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 5 16 11 16 15 8 1 16 31 100 1717986918400 100000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-532575944704) 3291038887500 (-3195070312500) 905269921875
        (by decide) (by decide) (by decide) (by decide)
        16718 74779 132840 [132840]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 31) (lD := 100) (αN := 5) (αD := 16) (uN := 1) (uD := 16) (qN := 3321) (qD := 2500)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

/-- Certified 5-step trajectory confinement for `fp8_pure_dp5_shifted` at `uFP8Pure`:
every adversarial trajectory starting in `[1/100, 1]` ends in `[31/100, 165/100]`. -/
theorem fp8_pure_dp5_shifted_certified (σ0 σ5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ σ0) (hhi : σ0 ≤ 1)
    (htraj : NoisyShiftedTraj5 fp8PureDP5Step1 fp8PureDP5Step2 fp8PureDP5Step3 fp8PureDP5Step4 fp8PureDP5Step5 uFP8Pure σ0 σ5) :
    (31 / 100 : Rat) ≤ σ5 ∧ σ5 ≤ (165 / 100 : Rat) := by
  rcases htraj with ⟨σ1, σ2, σ3, σ4, hs1, hs2, hs3, hs4, hs5⟩
  have h0lo : ((1 : Int) : Rat) / (100 : Int) ≤ σ0 := hlo
  have h0hi : σ0 ≤ ((1 : Int) : Rat) / (1 : Int) := by
    have h1 : ((1 : Int) : Rat) / ((1 : Int) : Rat) = 1 := rat_div_one_eq 1
    rw [h1]; exact hhi
  have hstep1 : NoisyShiftedStep (((13 : Int) : Rat) / (32 : Int)) (((11 : Int) : Rat) / (2 : Int)) (((3 : Int) : Rat) / (4 : Int)) (((1 : Int) : Rat) / (16 : Int)) σ0 σ1 := by
    have ha : (fp8PureDP5Step1).1 = ((13 : Int) : Rat) / (32 : Int) := rfl
    have hb : (fp8PureDP5Step1).2.1 = ((11 : Int) : Rat) / (2 : Int) := rfl
    have hm : (fp8PureDP5Step1).2.2 = ((3 : Int) : Rat) / (4 : Int) := rfl
    have hu : uFP8Pure = ((1 : Int) : Rat) / (16 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs1
  have ⟨h1lo, h1hi⟩ := fp8_pure_dp5_shifted_step1 h0lo h0hi hstep1
  have hstep2 : NoisyShiftedStep (((1 : Int) : Rat) / (8 : Int)) (((11 : Int) : Rat) / (16 : Int)) (((11 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (16 : Int)) σ1 σ2 := by
    have ha : (fp8PureDP5Step2).1 = ((1 : Int) : Rat) / (8 : Int) := rfl
    have hb : (fp8PureDP5Step2).2.1 = ((11 : Int) : Rat) / (16 : Int) := rfl
    have hm : (fp8PureDP5Step2).2.2 = ((11 : Int) : Rat) / (8 : Int) := rfl
    have hu : uFP8Pure = ((1 : Int) : Rat) / (16 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs2
  have ⟨h2lo, h2hi⟩ := fp8_pure_dp5_shifted_step2 h1lo h1hi hstep2
  have hstep3 : NoisyShiftedStep (((9 : Int) : Rat) / (64 : Int)) (((18 : Int) : Rat) / (1 : Int)) (((13 : Int) : Rat) / (32 : Int)) (((1 : Int) : Rat) / (16 : Int)) σ2 σ3 := by
    have ha : (fp8PureDP5Step3).1 = ((9 : Int) : Rat) / (64 : Int) := rfl
    have hb : (fp8PureDP5Step3).2.1 = ((18 : Int) : Rat) / (1 : Int) := (rat_div_one_eq 18).symm
    have hm : (fp8PureDP5Step3).2.2 = ((13 : Int) : Rat) / (32 : Int) := rfl
    have hu : uFP8Pure = ((1 : Int) : Rat) / (16 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs3
  have ⟨h3lo, h3hi⟩ := fp8_pure_dp5_shifted_step3 h2lo h2hi hstep3
  have hstep4 : NoisyShiftedStep (((9 : Int) : Rat) / (32 : Int)) (((14 : Int) : Rat) / (1 : Int)) (((9 : Int) : Rat) / (16 : Int)) (((1 : Int) : Rat) / (16 : Int)) σ3 σ4 := by
    have ha : (fp8PureDP5Step4).1 = ((9 : Int) : Rat) / (32 : Int) := rfl
    have hb : (fp8PureDP5Step4).2.1 = ((14 : Int) : Rat) / (1 : Int) := (rat_div_one_eq 14).symm
    have hm : (fp8PureDP5Step4).2.2 = ((9 : Int) : Rat) / (16 : Int) := rfl
    have hu : uFP8Pure = ((1 : Int) : Rat) / (16 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs4
  have ⟨h4lo, h4hi⟩ := fp8_pure_dp5_shifted_step4 h3lo h3hi hstep4
  have hstep5 : NoisyShiftedStep (((5 : Int) : Rat) / (16 : Int)) (((11 : Int) : Rat) / (16 : Int)) (((15 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (16 : Int)) σ4 σ5 := by
    have ha : (fp8PureDP5Step5).1 = ((5 : Int) : Rat) / (16 : Int) := rfl
    have hb : (fp8PureDP5Step5).2.1 = ((11 : Int) : Rat) / (16 : Int) := rfl
    have hm : (fp8PureDP5Step5).2.2 = ((15 : Int) : Rat) / (8 : Int) := rfl
    have hu : uFP8Pure = ((1 : Int) : Rat) / (16 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs5
  have ⟨h5lo, h5hi⟩ := fp8_pure_dp5_shifted_step5 h4lo h4hi hstep5
  have hfin_lo : ((31 : Int) : Rat) / (100 : Int) = (31 / 100 : Rat) :=
    rat_div_eq_of_cross (by decide) (by decide) (by decide)
  have hfin_hi : ((33 : Int) : Rat) / (20 : Int) = (165 / 100 : Rat) :=
    rat_div_eq_of_cross (by decide) (by decide) (by decide)
  rw [hfin_lo] at h5lo
  rw [hfin_hi] at h5hi
  exact ⟨h5lo, h5hi⟩

private theorem fp8_hybrid_dp5_shifted_step1 {x y : Rat}
    (hxlo : ((1 : Int) : Rat) / (100 : Int) ≤ x) (hxhi : x ≤ ((1 : Int) : Rat) / (1 : Int))
    (hstep : NoisyShiftedStep (((1 : Int) : Rat) / (8 : Int)) (((6 : Int) : Rat) / (1 : Int)) (((3 : Int) : Rat) / (4 : Int)) (((1 : Int) : Rat) / (32 : Int)) x y) :
    ((363 : Int) : Rat) / (12500 : Int) ≤ y ∧ y ≤ ((107517 : Int) : Rat) / (100000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((1 : Int) : Rat) / (8 : Int)) (((6 : Int) : Rat) / (1 : Int))
    (((3 : Int) : Rat) / (4 : Int)) (((1 : Int) : Rat) / (32 : Int))
    (((1 : Int) : Rat) / (100 : Int)) (((1 : Int) : Rat) / (1 : Int))
    (((363 : Int) : Rat) / (12500 : Int)) (((107517 : Int) : Rat) / (100000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((256 : Int) : Rat) / (25600 : Int) ≤ z := by
      have heq : ((1 : Int) : Rat) / (100 : Int) = ((256 : Int) : Rat) / (25600 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((25600 : Int) : Rat) / (25600 : Int) := by
      have heq : ((1 : Int) : Rat) / (1 : Int) = ((25600 : Int) : Rat) / (25600 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 1 8 6 1 3 4 1 32 107517 100000 1717986918400000 25600
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      1847127995056128 (-7202306885400000) 18015978167550000 (-11635319233209375)
      (by decide) (by decide) (by decide) (by decide)
      256 6592 25600 [9760, 10156, 10255, 10354, 10552, 11344, 12928, 25600]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((4 : Int) : Rat) / (400 : Int) ≤ z := by
      have heq : ((1 : Int) : Rat) / (100 : Int) = ((4 : Int) : Rat) / (400 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((400 : Int) : Rat) / (400 : Int) := by
      have heq : ((1 : Int) : Rat) / (1 : Int) = ((400 : Int) : Rat) / (400 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 1 8 6 1 3 4 1 32 107517 100000 1717986918400000 400
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      1847127995056128 (-7202306885400000) 19178299339650000 (-13185080796009375)
      (by decide) (by decide) (by decide) (by decide)
      4 103 400 [202, 400]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((533 : Int) : Rat) / (625 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((25 : Int) : Rat) / (2500 : Int) ≤ z := by
        have heq : ((1 : Int) : Rat) / (100 : Int) = ((25 : Int) : Rat) / (2500 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((2132 : Int) : Rat) / (2500 : Int) := by
        have heq : ((533 : Int) : Rat) / (625 : Int) = ((2132 : Int) : Rat) / (2500 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 533) (qD := 625) (uN := 1) (uD := 32) (μN := 3) (μD := 4)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 1 8 6 1 3 4 1 32 363 12500 1717986918400000 2500
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-49890340110336) 4994056184600000 (-13179429662850000) 9060857893209375
        (by decide) (by decide) (by decide) (by decide)
        25 2132 2132 []
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 363) (lD := 12500) (αN := 1) (αD := 8) (uN := 1) (uD := 32) (qN := 533) (qD := 625)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem fp8_hybrid_dp5_shifted_step2 {x y : Rat}
    (hxlo : ((363 : Int) : Rat) / (12500 : Int) ≤ x) (hxhi : x ≤ ((107517 : Int) : Rat) / (100000 : Int))
    (hstep : NoisyShiftedStep (((9 : Int) : Rat) / (64 : Int)) (((6 : Int) : Rat) / (1 : Int)) (((7 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (32 : Int)) x y) :
    ((2277 : Int) : Rat) / (20000 : Int) ≤ y ∧ y ≤ ((156707 : Int) : Rat) / (100000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((9 : Int) : Rat) / (64 : Int)) (((6 : Int) : Rat) / (1 : Int))
    (((7 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (32 : Int))
    (((363 : Int) : Rat) / (12500 : Int)) (((107517 : Int) : Rat) / (100000 : Int))
    (((2277 : Int) : Rat) / (20000 : Int)) (((156707 : Int) : Rat) / (100000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((743424 : Int) : Rat) / (25600000 : Int) ≤ z := by
      have heq : ((363 : Int) : Rat) / (12500 : Int) = ((743424 : Int) : Rat) / (25600000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((27524352 : Int) : Rat) / (25600000 : Int) := by
      have heq : ((107517 : Int) : Rat) / (100000 : Int) = ((27524352 : Int) : Rat) / (25600000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 9 64 6 1 7 8 1 32 156707 100000 1717986918400000 25600000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      2692205760217088 (-9749216906550000) 21018641195475000 (-11635319233209375)
      (by decide) (by decide) (by decide) (by decide)
      743424 7438656 27524352 [10786272, 10995498, 11100111, 11204724, 11623176, 12460080, 14133888, 27524352]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((11616 : Int) : Rat) / (400000 : Int) ≤ z := by
      have heq : ((363 : Int) : Rat) / (12500 : Int) = ((11616 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((430068 : Int) : Rat) / (400000 : Int) := by
      have heq : ((107517 : Int) : Rat) / (100000 : Int) = ((430068 : Int) : Rat) / (400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 9 64 6 1 7 8 1 32 156707 100000 1717986918400000 400000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      2692205760217088 (-9749216906550000) 22374682562925000 (-13185080796009375)
      (by decide) (by decide) (by decide) (by decide)
      11616 116229 430068 [220842, 430068]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((9211 : Int) : Rat) / (10000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((5808 : Int) : Rat) / (200000 : Int) ≤ z := by
        have heq : ((363 : Int) : Rat) / (12500 : Int) = ((5808 : Int) : Rat) / (200000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((184220 : Int) : Rat) / (200000 : Int) := by
        have heq : ((9211 : Int) : Rat) / (10000 : Int) = ((184220 : Int) : Rat) / (200000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 9211) (qD := 10000) (uN := 1) (uD := 32) (μN := 7) (μD := 8)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 9 64 6 1 7 8 1 32 2277 20000 343597383680000 200000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-39118562131968) 1349976080190000 (-3075200254665000) 1812171578641875
        (by decide) (by decide) (by decide) (by decide)
        5808 95014 184220 [139617, 184220]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 2277) (lD := 20000) (αN := 9) (αD := 64) (uN := 1) (uD := 32) (qN := 9211) (qD := 10000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem fp8_hybrid_dp5_shifted_step3 {x y : Rat}
    (hxlo : ((2277 : Int) : Rat) / (20000 : Int) ≤ x) (hxhi : x ≤ ((156707 : Int) : Rat) / (100000 : Int))
    (hstep : NoisyShiftedStep (((7 : Int) : Rat) / (32 : Int)) (((3 : Int) : Rat) / (4 : Int)) (((15 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (32 : Int)) x y) :
    ((5359 : Int) : Rat) / (20000 : Int) ≤ y ∧ y ≤ ((141089 : Int) : Rat) / (100000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((7 : Int) : Rat) / (32 : Int)) (((3 : Int) : Rat) / (4 : Int))
    (((15 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (32 : Int))
    (((2277 : Int) : Rat) / (20000 : Int)) (((156707 : Int) : Rat) / (100000 : Int))
    (((5359 : Int) : Rat) / (20000 : Int)) (((141089 : Int) : Rat) / (100000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((1457280 : Int) : Rat) / (12800000 : Int) ≤ z := by
      have heq : ((2277 : Int) : Rat) / (20000 : Int) = ((1457280 : Int) : Rat) / (12800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((20058496 : Int) : Rat) / (12800000 : Int) := by
      have heq : ((156707 : Int) : Rat) / (100000 : Int) = ((20058496 : Int) : Rat) / (12800000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 7 32 3 4 15 8 1 32 141089 100000 13743895347200000 12800000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      19391124506411008 (-46784361892950000) 45039945418875000 (-11635319233209375)
      (by decide) (by decide) (by decide) (by decide)
      1457280 6107584 20058496 [7270160, 7851448, 8142092, 8287414, 8360075, 8432736, 10757888, 20058496]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((22770 : Int) : Rat) / (200000 : Int) ≤ z := by
      have heq : ((2277 : Int) : Rat) / (20000 : Int) = ((22770 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((313414 : Int) : Rat) / (200000 : Int) := by
      have heq : ((156707 : Int) : Rat) / (100000 : Int) = ((313414 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 7 32 3 4 15 8 1 32 141089 100000 13743895347200000 200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      19391124506411008 (-46784361892950000) 47945748349125000 (-13185080796009375)
      (by decide) (by decide) (by decide) (by decide)
      22770 95431 313414 [168092, 313414]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((13483 : Int) : Rat) / (10000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((18216 : Int) : Rat) / (160000 : Int) ≤ z := by
        have heq : ((2277 : Int) : Rat) / (20000 : Int) = ((18216 : Int) : Rat) / (160000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((215728 : Int) : Rat) / (160000 : Int) := by
        have heq : ((13483 : Int) : Rat) / (10000 : Int) = ((215728 : Int) : Rat) / (160000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 13483) (qD := 10000) (uN := 1) (uD := 32) (μN := 15) (μD := 8)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 7 32 3 4 15 8 1 32 5359 20000 2748779069440000 160000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-736535351656448) 6554951506910000 (-6589714831425000) 1812171578641875
        (by decide) (by decide) (by decide) (by decide)
        18216 116972 215728 [166350, 191039, 215728]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 5359) (lD := 20000) (αN := 7) (αD := 32) (uN := 1) (uD := 32) (qN := 13483) (qD := 10000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem fp8_hybrid_dp5_shifted_step4 {x y : Rat}
    (hxlo : ((5359 : Int) : Rat) / (20000 : Int) ≤ x) (hxhi : x ≤ ((141089 : Int) : Rat) / (100000 : Int))
    (hstep : NoisyShiftedStep (((9 : Int) : Rat) / (16 : Int)) (((15 : Int) : Rat) / (16 : Int)) (((13 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (32 : Int)) x y) :
    ((8011 : Int) : Rat) / (12500 : Int) ≤ y ∧ y ≤ ((36803 : Int) : Rat) / (25000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((9 : Int) : Rat) / (16 : Int)) (((15 : Int) : Rat) / (16 : Int))
    (((13 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (32 : Int))
    (((5359 : Int) : Rat) / (20000 : Int)) (((141089 : Int) : Rat) / (100000 : Int))
    (((8011 : Int) : Rat) / (12500 : Int)) (((36803 : Int) : Rat) / (25000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((1714880 : Int) : Rat) / (6400000 : Int) ≤ z := by
      have heq : ((5359 : Int) : Rat) / (20000 : Int) = ((1714880 : Int) : Rat) / (6400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((9029696 : Int) : Rat) / (6400000 : Int) := by
      have heq : ((141089 : Int) : Rat) / (100000 : Int) = ((9029696 : Int) : Rat) / (6400000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 9 16 15 16 13 8 1 32 36803 25000 54975581388800000 6400000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      80930652874080256 (-196580263873950000) 195173096815125000 (-58176596166046875)
      (by decide) (by decide) (by decide) (by decide)
      1714880 3543584 9029696 [4000760, 4115054, 4172201, 4229348, 4457936, 5372288, 9029696]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((53590 : Int) : Rat) / (200000 : Int) ≤ z := by
      have heq : ((5359 : Int) : Rat) / (20000 : Int) = ((53590 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((282178 : Int) : Rat) / (200000 : Int) := by
      have heq : ((141089 : Int) : Rat) / (100000 : Int) = ((282178 : Int) : Rat) / (200000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 9 16 15 16 13 8 1 32 36803 25000 54975581388800000 200000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      80930652874080256 (-196580263873950000) 207764909512875000 (-65925403980046875)
      (by decide) (by decide) (by decide) (by decide)
      53590 110737 282178 [167884, 282178]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((1569 : Int) : Rat) / (1250 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((42872 : Int) : Rat) / (160000 : Int) ≤ z := by
        have heq : ((5359 : Int) : Rat) / (20000 : Int) = ((42872 : Int) : Rat) / (160000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((200832 : Int) : Rat) / (160000 : Int) := by
        have heq : ((1569 : Int) : Rat) / (1250 : Int) = ((200832 : Int) : Rat) / (160000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 1569) (qD := 1250) (uN := 1) (uD := 32) (μN := 13) (μD := 8)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 9 16 15 16 13 8 1 32 8011 12500 54975581388800000 160000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-35232750600454144) 141512319803550000 (-142777154680875000) 45304289466046875
        (by decide) (by decide) (by decide) (by decide)
        42872 121852 200832 [161342, 181087, 200832]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 8011) (lD := 12500) (αN := 9) (αD := 16) (uN := 1) (uD := 32) (qN := 1569) (qD := 1250)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

private theorem fp8_hybrid_dp5_shifted_step5 {x y : Rat}
    (hxlo : ((8011 : Int) : Rat) / (12500 : Int) ≤ x) (hxhi : x ≤ ((36803 : Int) : Rat) / (25000 : Int))
    (hstep : NoisyShiftedStep (((11 : Int) : Rat) / (16 : Int)) (((5 : Int) : Rat) / (16 : Int)) (((2 : Int) : Rat) / (1 : Int)) (((1 : Int) : Rat) / (32 : Int)) x y) :
    ((103 : Int) : Rat) / (125 : Int) ≤ y ∧ y ≤ ((1163 : Int) : Rat) / (1000 : Int) := by
  apply noisyShiftedStep_step_certified
    (((11 : Int) : Rat) / (16 : Int)) (((5 : Int) : Rat) / (16 : Int))
    (((2 : Int) : Rat) / (1 : Int)) (((1 : Int) : Rat) / (32 : Int))
    (((8011 : Int) : Rat) / (12500 : Int)) (((36803 : Int) : Rat) / (25000 : Int))
    (((103 : Int) : Rat) / (125 : Int)) (((1163 : Int) : Rat) / (1000 : Int))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_pos (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
    (rat_ofInt_div_lt_one (by decide) (by decide))
    (rat_ofInt_div_nonneg (by decide) (by decide))
  · intro z hzlo hzhi
    have hz1 : ((64088 : Int) : Rat) / (100000 : Int) ≤ z := by
      have heq : ((8011 : Int) : Rat) / (12500 : Int) = ((64088 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((147212 : Int) : Rat) / (100000 : Int) := by
      have heq : ((36803 : Int) : Rat) / (25000 : Int) = ((147212 : Int) : Rat) / (100000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperMinus_cert_int 11 16 5 16 2 1 1 32 1163 1000 2199023255552000 100000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      2557464046206976 (-4913952164352000) 3202840563120000 (-775687948880625)
      (by decide) (by decide) (by decide) (by decide)
      64088 84869 147212 [105650, 147212]
      rfl (by decide) hz1 hz2
  · intro z hzlo hzhi
    have hz1 : ((32044 : Int) : Rat) / (50000 : Int) ≤ z := by
      have heq : ((8011 : Int) : Rat) / (12500 : Int) = ((32044 : Int) : Rat) / (50000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzlo
    have hz2 : z ≤ ((73606 : Int) : Rat) / (50000 : Int) := by
      have heq : ((36803 : Int) : Rat) / (25000 : Int) = ((73606 : Int) : Rat) / (50000 : Int) :=
        rat_div_eq_of_cross (by decide) (by decide) (by decide)
      rw [← heq]; exact hzhi
    exact upperPlus_cert_int 11 16 5 16 2 1 1 32 1163 1000 2199023255552000 50000
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      2557464046206976 (-4913952164352000) 3409475438160000 (-879005386400625)
      (by decide) (by decide) (by decide) (by decide)
      32044 52825 73606 [73606]
      rfl (by decide) hz1 hz2
  · intro z hzlo _hzhi
    cases Rat.le_total (a := z) (b := ((6963 : Int) : Rat) / (5000 : Int)) with
    | inl hzq =>
      right; left
      have hz0 : (0 : Rat) ≤ z := Rat.le_trans (rat_ofInt_div_nonneg (by decide) (by decide)) hzlo
      have hz1 : ((32044 : Int) : Rat) / (50000 : Int) ≤ z := by
        have heq : ((8011 : Int) : Rat) / (12500 : Int) = ((32044 : Int) : Rat) / (50000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzlo
      have hz2 : z ≤ ((69630 : Int) : Rat) / (50000 : Int) := by
        have heq : ((6963 : Int) : Rat) / (5000 : Int) = ((69630 : Int) : Rat) / (50000 : Int) :=
          rat_div_eq_of_cross (by decide) (by decide) (by decide)
        rw [← heq]; exact hzq
      refine ⟨sq_mul_up_le_mu_of_int (qN := 6963) (qD := 5000) (uN := 1) (uD := 32) (μN := 2) (μD := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hzq, ?_⟩
      exact lowerLeft_cert_int 11 16 5 16 2 1 1 32 103 125 2199023255552000 50000
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (-1811995162574848) 3690825026048000 (-2343009717840000) 604057192880625
        (by decide) (by decide) (by decide) (by decide)
        32044 50837 69630 [69630]
        rfl (by decide) hz1 hz2
    | inr hqz =>
      left
      exact lowerBase_ge_of_int (lN := 103) (lD := 125) (αN := 11) (αD := 16) (uN := 1) (uD := 32) (qN := 6963) (qD := 5000)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hqz
  · exact hxlo
  · exact hxhi
  · exact hstep

/-- Certified 5-step trajectory confinement for `fp8_hybrid_dp5_shifted` at `uFP8Hybrid`:
every adversarial trajectory starting in `[1/100, 1]` ends in `[824/1000, 1163/1000]`. -/
theorem fp8_hybrid_dp5_shifted_certified (σ0 σ5 : Rat)
    (hlo : (1 / 100 : Rat) ≤ σ0) (hhi : σ0 ≤ 1)
    (htraj : NoisyShiftedTraj5 fp8HybridDP5Step1 fp8HybridDP5Step2 fp8HybridDP5Step3 fp8HybridDP5Step4 fp8HybridDP5Step5 uFP8Hybrid σ0 σ5) :
    (824 / 1000 : Rat) ≤ σ5 ∧ σ5 ≤ (1163 / 1000 : Rat) := by
  rcases htraj with ⟨σ1, σ2, σ3, σ4, hs1, hs2, hs3, hs4, hs5⟩
  have h0lo : ((1 : Int) : Rat) / (100 : Int) ≤ σ0 := hlo
  have h0hi : σ0 ≤ ((1 : Int) : Rat) / (1 : Int) := by
    have h1 : ((1 : Int) : Rat) / ((1 : Int) : Rat) = 1 := rat_div_one_eq 1
    rw [h1]; exact hhi
  have hstep1 : NoisyShiftedStep (((1 : Int) : Rat) / (8 : Int)) (((6 : Int) : Rat) / (1 : Int)) (((3 : Int) : Rat) / (4 : Int)) (((1 : Int) : Rat) / (32 : Int)) σ0 σ1 := by
    have ha : (fp8HybridDP5Step1).1 = ((1 : Int) : Rat) / (8 : Int) := rfl
    have hb : (fp8HybridDP5Step1).2.1 = ((6 : Int) : Rat) / (1 : Int) := (rat_div_one_eq 6).symm
    have hm : (fp8HybridDP5Step1).2.2 = ((3 : Int) : Rat) / (4 : Int) := rfl
    have hu : uFP8Hybrid = ((1 : Int) : Rat) / (32 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs1
  have ⟨h1lo, h1hi⟩ := fp8_hybrid_dp5_shifted_step1 h0lo h0hi hstep1
  have hstep2 : NoisyShiftedStep (((9 : Int) : Rat) / (64 : Int)) (((6 : Int) : Rat) / (1 : Int)) (((7 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (32 : Int)) σ1 σ2 := by
    have ha : (fp8HybridDP5Step2).1 = ((9 : Int) : Rat) / (64 : Int) := rfl
    have hb : (fp8HybridDP5Step2).2.1 = ((6 : Int) : Rat) / (1 : Int) := (rat_div_one_eq 6).symm
    have hm : (fp8HybridDP5Step2).2.2 = ((7 : Int) : Rat) / (8 : Int) := rfl
    have hu : uFP8Hybrid = ((1 : Int) : Rat) / (32 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs2
  have ⟨h2lo, h2hi⟩ := fp8_hybrid_dp5_shifted_step2 h1lo h1hi hstep2
  have hstep3 : NoisyShiftedStep (((7 : Int) : Rat) / (32 : Int)) (((3 : Int) : Rat) / (4 : Int)) (((15 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (32 : Int)) σ2 σ3 := by
    have ha : (fp8HybridDP5Step3).1 = ((7 : Int) : Rat) / (32 : Int) := rfl
    have hb : (fp8HybridDP5Step3).2.1 = ((3 : Int) : Rat) / (4 : Int) := rfl
    have hm : (fp8HybridDP5Step3).2.2 = ((15 : Int) : Rat) / (8 : Int) := rfl
    have hu : uFP8Hybrid = ((1 : Int) : Rat) / (32 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs3
  have ⟨h3lo, h3hi⟩ := fp8_hybrid_dp5_shifted_step3 h2lo h2hi hstep3
  have hstep4 : NoisyShiftedStep (((9 : Int) : Rat) / (16 : Int)) (((15 : Int) : Rat) / (16 : Int)) (((13 : Int) : Rat) / (8 : Int)) (((1 : Int) : Rat) / (32 : Int)) σ3 σ4 := by
    have ha : (fp8HybridDP5Step4).1 = ((9 : Int) : Rat) / (16 : Int) := rfl
    have hb : (fp8HybridDP5Step4).2.1 = ((15 : Int) : Rat) / (16 : Int) := rfl
    have hm : (fp8HybridDP5Step4).2.2 = ((13 : Int) : Rat) / (8 : Int) := rfl
    have hu : uFP8Hybrid = ((1 : Int) : Rat) / (32 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs4
  have ⟨h4lo, h4hi⟩ := fp8_hybrid_dp5_shifted_step4 h3lo h3hi hstep4
  have hstep5 : NoisyShiftedStep (((11 : Int) : Rat) / (16 : Int)) (((5 : Int) : Rat) / (16 : Int)) (((2 : Int) : Rat) / (1 : Int)) (((1 : Int) : Rat) / (32 : Int)) σ4 σ5 := by
    have ha : (fp8HybridDP5Step5).1 = ((11 : Int) : Rat) / (16 : Int) := rfl
    have hb : (fp8HybridDP5Step5).2.1 = ((5 : Int) : Rat) / (16 : Int) := rfl
    have hm : (fp8HybridDP5Step5).2.2 = ((2 : Int) : Rat) / (1 : Int) := (rat_div_one_eq 2).symm
    have hu : uFP8Hybrid = ((1 : Int) : Rat) / (32 : Int) := rfl
    rw [← ha, ← hb, ← hm, ← hu]; exact hs5
  have ⟨h5lo, h5hi⟩ := fp8_hybrid_dp5_shifted_step5 h4lo h4hi hstep5
  have hfin_lo : ((103 : Int) : Rat) / (125 : Int) = (824 / 1000 : Rat) :=
    rat_div_eq_of_cross (by decide) (by decide) (by decide)
  have hfin_hi : ((1163 : Int) : Rat) / (1000 : Int) = (1163 / 1000 : Rat) :=
    rat_div_eq_of_cross (by decide) (by decide) (by decide)
  rw [hfin_lo] at h5lo
  rw [hfin_hi] at h5hi
  exact ⟨h5lo, h5hi⟩

end MuonVertexPolar
