/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmTustinPade

/-!
# Verified Solutions (`ssm-tustin-pade-horizons`)
-/

namespace SsmTustinPadeChallenge

open SsmTustinPade

theorem tustin_nyquist_snap_to_minus_one_horizon_exact :
    (∀ z : Rat, (0 : Rat) < z →
      tustinA z = -1 + 4 / (z + 2) ∧ (-1 : Rat) < tustinA z ∧ tustinA z < 1) ∧
    (∀ (p : Nat) (z : Rat), (0 : Rat) < z →
      (rneSnapsToNegOne p (tustinA z) ↔ 4 / (z + 2) ≤ invPow2Rat (p + 1)) ∧
      (4 / (z + 2) ≤ invPow2Rat (p + 1) ↔ (tustinSingleRoundOscThreshold p : Rat) ≤ z)) ∧
    (tustinOscHorizon 3 = 24 ∧ tustinOscHorizon 4 = 40 ∧
     tustinOscHorizon 8 = 520 ∧ tustinOscHorizon 11 = 4104) ∧
    (∀ p : Nat, 2 ≤ p →
      binadeUlp p (p + 1) = 4 ∧
      binadeRneNat p (p + 1) (tustinOscHorizon p + 2) = tustinOscHorizon p ∧
      binadeRneNat p (p + 1) (tustinOscHorizon p - 2) = tustinOscHorizon p ∧
      binadeRneNat p (p + 1) (2 ^ (p + 1) + 4 + 2) = 2 ^ (p + 1) + 8 ∧
      binadeRneNat p (p + 1) (2 ^ (p + 1) + 4 - 2) = 2 ^ (p + 1) ∧
      ¬ rneSnapsToNegOne p (-((2 ^ (p + 1) : Rat) / ((2 ^ (p + 1) + 8 : Nat) : Rat))) ∧
      ¬ rneSnapsToNegOne p (-(((2 ^ (p + 1) - 2 : Nat) : Rat) / (2 ^ (p + 1) : Rat)))) ∧
    (∀ p k q : Nat, p + 2 ≤ k → 1 ≤ q →
      binadeRneNat p k (q * binadeUlp p k + 2) = q * binadeUlp p k ∧
      binadeRneNat p k (q * binadeUlp p k - 2) = q * binadeUlp p k) :=
  SsmTustinPade.tustin_nyquist_snap_to_minus_one_horizon_exact

theorem tustin_vs_zoh_infinite_memory_stall_two_x_gap :
    (tustinStallHorizon 3 = 1 / 8 ∧ tustinStallHorizon 4 = 1 / 16 ∧
     tustinStallHorizon 8 = 1 / 256 ∧ tustinStallHorizon 11 = 1 / 2048) ∧
    (zohStallHorizon 3 = 1 / 16 ∧ zohStallHorizon 4 = 1 / 32 ∧
     zohStallHorizon 8 = 1 / 512 ∧ zohStallHorizon 11 = 1 / 4096) ∧
    (∀ p : Nat,
      tustinStallHorizon p = 2 * zohStallHorizon p ∧
      tustinStallHorizon p / zohStallHorizon p = 2) ∧
    (∀ (p : Nat) (z : Rat), 1 ≤ p → (0 : Rat) < z → z ≤ tustinStallHorizon p →
      rneSnapsToTwoBelow p (2 - z) ∧
      rneSnapsToTwoAbove p (2 + z) ∧
      rneSnapsToPosOneAbove p (1 + z) ∧
      rneSnapsToPosOneAbove p (1 + z * z / 2)) ∧
    (∀ (p : Nat) (z ez : Rat), z ≤ zohStallHorizon p → 1 - z ≤ ez → ez ≤ 1 →
      rneSnapsToPosOneBelow p ez) ∧
    (∀ (p : Nat) (ez : Rat), 2 ≤ p →
      ez < 1 - tustinStallHorizon p + tustinStallHorizon p * tustinStallHorizon p / 2 →
      ¬ rneSnapsToPosOneBelow p ez) :=
  SsmTustinPade.tustin_vs_zoh_infinite_memory_stall_two_x_gap

theorem zoh_b_bar_catastrophic_cancellation_blackout_horizon :
    (∀ (p : Nat) (z ez : Rat),
      z ≤ zohStallHorizon p → 1 - z ≤ ez → ez ≤ 1 →
      flNearOneBelow p ez = 1 ∧ naiveZohBBar p ez z = 0) ∧
    (zohStallHorizon 3 = 1 / 16 ∧ zohStallHorizon 4 = 1 / 32 ∧
     zohStallHorizon 8 = 1 / 512 ∧ zohStallHorizon 11 = 1 / 4096) ∧
    (∀ B f : Nat, f + 3 ≤ B →
      countUnitInterval B f = B * 2 ^ f ∧
      countBlackoutInterval B f = (B - f - 2) * 2 ^ f ∧
      (countBlackoutInterval B f : Rat) / (countUnitInterval B f : Rat) =
        ((B - f - 2 : Nat) : Rat) / (B : Rat)) ∧
    (countUnitInterval 127 7 = 16256 ∧ countBlackoutInterval 127 7 = 15104 ∧
     (15104 : Rat) / 16256 = 118 / 127 ∧
     (9291 / 10000 : Rat) < (15104 : Rat) / 16256 ∧
     (15104 : Rat) / 16256 < 9292 / 10000) ∧
    (countUnitInterval 15 2 = 60 ∧ countBlackoutInterval 15 2 = 44 ∧
     (44 : Rat) / 60 = 11 / 15 ∧
     countUnitInterval 7 3 = 56 ∧ countBlackoutInterval 7 3 = 16 ∧
     (16 : Rat) / 56 = 2 / 7 ∧
     countUnitInterval 15 10 = 15360 ∧ countBlackoutInterval 15 10 = 3072 ∧
     (3072 : Rat) / 15360 = 1 / 5) :=
  SsmTustinPade.zoh_b_bar_catastrophic_cancellation_blackout_horizon

theorem pade02_unconditional_positivity_and_contraction_exact :
    (∀ z : Rat, (0 : Rat) < z → (0 : Rat) < pade02A z ∧ pade02A z < 1) ∧
    (∀ z : Rat, (0 : Rat) < z →
      pade02A z - expTaylor2 z = -(z * z * z * z) / (4 * (1 + z + z * z / 2)) ∧
      pade02A z - expTaylor3 z = z * z * z * (2 - z + z * z) / (12 * (1 + z + z * z / 2))) ∧
    (∀ z : Rat, (0 : Rat) < z → z ≤ 1 →
      (0 : Rat) < pade02A z - expTaylor3 z ∧ pade02A z - expTaylor3 z ≤ z * z * z / 6) ∧
    (∀ z : Rat, (32 : Rat) ≤ z → fp8E4M3MaxFinite < z * z / 2) ∧
    (∀ z : Rat, (22 : Rat) ≤ z → fp8E4M3MaxFinite < z * z) ∧
    ((20 : Rat) * 20 ≤ fp8E4M3MaxFinite ∧ (28 : Rat) * 28 / 2 ≤ fp8E4M3MaxFinite ∧
     fp8E4M3MaxFinite < (32 : Rat) * 32 / 2) :=
  SsmTustinPade.pade02_unconditional_positivity_and_contraction_exact

theorem pade02_b_bar_zero_blackout_and_fourth_order_accuracy :
    (∀ z : Rat, (0 : Rat) ≤ z → (0 : Rat) < pade02B z ∧ pade02B z ≤ 1) ∧
    (∀ z : Rat, (0 : Rat) ≤ z →
      pade02B z - phi1Taylor3 z =
        z * z * z * z * (2 + z) / (288 * (1 + z / 2 + z * z / 12)) ∧
      phi1Taylor4 z - pade02B z =
        z * z * z * z * (2 + z + z * z) / (1440 * (1 + z / 2 + z * z / 12))) ∧
    (∀ z : Rat, (0 : Rat) ≤ z → z ≤ 1 →
      (0 : Rat) ≤ phi1Taylor4 z - pade02B z ∧
      phi1Taylor4 z - pade02B z ≤ z * z * z * z / 360 ∧
      z * z * z * z / 360 ≤ 1 / 360) ∧
    (tustinB 1 - phi1Taylor4 1 = 1 / 30 ∧
     phi1Taylor4 1 - pade02B 1 = 1 / 570 ∧
     (1 / 360 : Rat) < tustinB 1 - phi1Taylor4 1 ∧
     19 * (phi1Taylor4 1 - pade02B 1) = tustinB 1 - phi1Taylor4 1) :=
  SsmTustinPade.pade02_b_bar_zero_blackout_and_fourth_order_accuracy

theorem ssm_trajectory_energy_conservation_and_nyquist_blowup :
    (∀ (b : Rat) (T : Nat),
      ssmState (-1) b altSign T = -(altSign T) * (T : Rat) * b ∧
      ratAbs (ssmState (-1) b altSign T) = (T : Rat) * ratAbs b ∧
      ssmState (-1) b altSign T * ssmState (-1) b altSign T =
        (T : Rat) * (T : Rat) * (b * b)) ∧
    (∀ (b : Rat) (T : Nat),
      ssmState 1 b (fun _ => 1) T = (T : Rat) * b ∧
      ratAbs (ssmState 1 b (fun _ => 1) T) = (T : Rat) * ratAbs b ∧
      ssmState 1 b (fun _ => 1) T * ssmState 1 b (fun _ => 1) T =
        (T : Rat) * (T : Rat) * (b * b)) ∧
    (∀ (a b : Rat) (u : Nat → Rat),
      (0 : Rat) < a → a < 1 → (∀ t : Nat, ratAbs (u t) ≤ 1) →
      ∀ T : Nat, ratAbs (ssmState a b u T) ≤ ratAbs b / (1 - a)) ∧
    (∀ (z : Rat) (u : Nat → Rat),
      (0 : Rat) < z → (∀ t : Nat, ratAbs (u t) ≤ 1) →
      ∀ T : Nat, ratAbs (ssmState (pade02A z) (pade02B z) u T) ≤
        pade02B z / (1 - pade02A z)) :=
  SsmTustinPade.ssm_trajectory_energy_conservation_and_nyquist_blowup

end SsmTustinPadeChallenge
