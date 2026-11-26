/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MoeBiasPlacement

/-!
# Verified Solutions (`moe-bias-placement-codes`)
-/

namespace MoeBiasPlacementChallenge

open MoeBiasPlacement

theorem aux_loss_free_mean_bias_drift_exact
    (E : Nat) (hE : 2 ≤ E) (γ : Rat) (hγ : 0 < γ) :
    (∀ L : Fin E → Rat,
      (sumFinRat (signBiasDelta γ L) / (E : Rat)).abs ≤ (((E : Rat) - 2) / (E : Rat)) * γ) ∧
    (∃ L : Fin E → Rat,
      sumFinRat (signBiasDelta γ L) / (E : Rat) = (((E : Rat) - 2) / (E : Rat)) * γ) ∧
    (∀ L b : Fin E → Rat,
      sumFinRat (meanCenteredDelta γ L) = 0 ∧
      ∀ i j : Fin E,
        (b i + meanCenteredDelta γ L i) - (b j + meanCenteredDelta γ L j) =
        (b i + signBiasDelta γ L i) - (b j + signBiasDelta γ L j)) :=
  MoeBiasPlacement.aux_loss_free_mean_bias_drift_exact E hE γ hγ

theorem dead_zone_fixed_point_threshold_exact
    (E B K : Nat) (hE : 0 < E) (hr : 0 < (B * K) % E) :
    let r := (B * K) % E
    let Lbar : Rat := ((B * K : Nat) : Rat) / (E : Rat)
    let τ_min : Rat := ((max r (E - r) : Nat) : Rat) / (E : Rat)
    (∀ L : Fin E → Nat, sumFinNat L = B * K →
      ∃ i : Fin E, τ_min ≤ ((L i : Rat) - Lbar).abs) ∧
    (∀ τ : Rat, τ < τ_min → ∀ L : Fin E → Nat, sumFinNat L = B * K →
      ¬ (∀ i : Fin E, ((L i : Rat) - Lbar).abs ≤ τ)) ∧
    (∃ L : Fin E → Nat, sumFinNat L = B * K ∧
      ∀ i : Fin E, ((L i : Rat) - Lbar).abs ≤ τ_min) :=
  MoeBiasPlacement.dead_zone_fixed_point_threshold_exact E B K hE hr

theorem fanout_intra_gpu_dispersion_duality
    (f K : Nat) (hf : 0 < f) (hfK : f ≤ K) :
    let q := K / f
    let r := K % f
    (∀ c : Fin f → Nat, sumFinNat c = K → q * (K + r - f) ≤ twiceIntraPairs c) ∧
    (∃ c : Fin f → Nat, sumFinNat c = K ∧ (∀ g : Fin f, 0 < c g) ∧
      twiceIntraPairs c = q * (K + r - f)) :=
  MoeBiasPlacement.fanout_intra_gpu_dispersion_duality f K hf hfK

theorem affine_plane_ag2_zero_hotspot_placement :
    (∀ c y : Fin 4, ag24Gpu (ag24VerticalLine c y) = c) ∧
    (∀ m b : Fin 4,
      (∀ x1 x2 : Fin 4, ag24Gpu (ag24TransverseLine m b x1) = ag24Gpu (ag24TransverseLine m b x2) → x1 = x2) ∧
      (∀ g : Fin 4, ∃ x : Fin 4, ag24Gpu (ag24TransverseLine m b x) = g)) ∧
    (∀ p1 p2 : Fin 4 × Fin 4, p1 ≠ p2 →
      (p1.1 = p2.1 → ∃ c : Fin 4, p1.1 = c ∧ p2.1 = c ∧ ∀ c' : Fin 4, p1.1 = c' ∧ p2.1 = c' → c' = c) ∧
      (p1.1 ≠ p2.1 → ∃ m b : Fin 4,
        ag24TransverseLine m b p1.1 = p1 ∧ ag24TransverseLine m b p2.1 = p2 ∧
        ∀ m' b' : Fin 4,
          ag24TransverseLine m' b' p1.1 = p1 → ag24TransverseLine m' b' p2.1 = p2 →
          m' = m ∧ b' = b)) ∧
    (∀ c y : Fin 8, ag28Gpu (ag28VerticalLine c y) = c) ∧
    (∀ m b : Fin 8,
      (∀ x1 x2 : Fin 8, ag28Gpu (ag28TransverseLine m b x1) = ag28Gpu (ag28TransverseLine m b x2) → x1 = x2) ∧
      (∀ g : Fin 8, ∃ x : Fin 8, ag28Gpu (ag28TransverseLine m b x) = g)) ∧
    (∀ p1 p2 : Fin 8 × Fin 8, p1 ≠ p2 →
      (p1.1 = p2.1 → ∃ c : Fin 8, p1.1 = c ∧ p2.1 = c ∧ ∀ c' : Fin 8, p1.1 = c' ∧ p2.1 = c' → c' = c) ∧
      (p1.1 ≠ p2.1 → ∃ m b : Fin 8,
        ag28TransverseLine m b p1.1 = p1 ∧ ag28TransverseLine m b p2.1 = p2 ∧
        ∀ m' b' : Fin 8,
          ag28TransverseLine m' b' p1.1 = p1 → ag28TransverseLine m' b' p2.1 = p2 →
          m' = m ∧ b' = b)) :=
  MoeBiasPlacement.affine_plane_ag2_zero_hotspot_placement

theorem eplb_redundant_expert_pigeonhole_bound
    (E R : Nat) (hE : 0 < E)
    (w : Fin E → Rat) (hw : ∀ i : Fin E, 0 ≤ w i)
    (rep : Fin E → Nat) (hrep_pos : ∀ i : Fin E, 1 ≤ rep i) (hrep_sum : sumFinNat rep = E + R)
    (S : Fin E → Bool) (hS : 1 ≤ countBool S) :
    let h := countBool S
    (∀ Lmax : Rat, (∀ i : Fin E, w i / (rep i : Rat) ≤ Lmax) →
      sumFinRatSubset S w ≤ Lmax * ((h + R : Nat) : Rat)) ∧
    (∃ i : Fin E, S i = true ∧
      sumFinRatSubset S w / ((h + R : Nat) : Rat) ≤ w i / (rep i : Rat)) :=
  MoeBiasPlacement.eplb_redundant_expert_pigeonhole_bound E R hE w hw rep hrep_pos hrep_sum S hS

theorem quantized_router_zero_flip_thresholds :
    (∀ z_k z_j z'_k z'_j ε : Rat,
      (z'_k - z_k).abs ≤ ε → (z'_j - z_j).abs ≤ ε → z_k - z_j > 2 * ε → z'_k > z'_j) ∧
    (∀ z_k z_j ε : Rat,
      0 ≤ ε → z_k - z_j = 2 * ε →
      ∃ z'_k z'_j : Rat, (z'_k - z_k).abs ≤ ε ∧ (z'_j - z_j).abs ≤ ε ∧ z'_k = z'_j) ∧
    (∀ (m : Nat) (z_k z_j z'_k z'_j : Rat),
      let u : Rat := 1 / ((2 ^ (m + 1) : Nat) : Rat)
      0 < z_j → z_j < z_k →
      (z'_k - z_k).abs ≤ u * z_k.abs →
      (z'_j - z_j).abs ≤ u * z_j.abs →
      z_k * (((2 ^ (m + 1) : Nat) : Rat) - 1) > z_j * (((2 ^ (m + 1) : Nat) : Rat) + 1) →
      z'_k > z'_j) ∧
    (∀ (m : Nat) (z_k z_j : Rat),
      let u : Rat := 1 / ((2 ^ (m + 1) : Nat) : Rat)
      0 < z_j →
      z_k * (((2 ^ (m + 1) : Nat) : Rat) - 1) = z_j * (((2 ^ (m + 1) : Nat) : Rat) + 1) →
      ∃ z'_k z'_j : Rat,
        (z'_k - z_k).abs ≤ u * z_k.abs ∧
        (z'_j - z_j).abs ≤ u * z_j.abs ∧
        z'_k = z'_j) ∧
    ((((2 ^ (1 + 1) : Nat) : Rat) + 1) / (((2 ^ (1 + 1) : Nat) : Rat) - 1) = 5 / 3 ∧
     (((2 ^ (2 + 1) : Nat) : Rat) + 1) / (((2 ^ (2 + 1) : Nat) : Rat) - 1) = 9 / 7 ∧
     (((2 ^ (3 + 1) : Nat) : Rat) + 1) / (((2 ^ (3 + 1) : Nat) : Rat) - 1) = 17 / 15 ∧
     (((2 ^ (7 + 1) : Nat) : Rat) + 1) / (((2 ^ (7 + 1) : Nat) : Rat) - 1) = 257 / 255 ∧
     (((2 ^ (10 + 1) : Nat) : Rat) + 1) / (((2 ^ (10 + 1) : Nat) : Rat) - 1) = 2049 / 2047) :=
  MoeBiasPlacement.quantized_router_zero_flip_thresholds

end MoeBiasPlacementChallenge
