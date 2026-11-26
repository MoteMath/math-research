/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonclipAdamwSr

/-!
# Verified Solutions (`muonclip-adamw-sr-bounds`)
-/

namespace MuonclipAdamwSrChallenge

open MuonclipAdamwSr

theorem muonclip_pitchfork_symmetry_breaking_exact :
    (∀ γ x : Rat, muonclipQuartic 1 γ x = (x * x - γ) * (x * x - x + γ)) ∧
    (∀ A γ x : Rat, x ≠ 0 →
      muonclipObj A A γ x =
        A * (1 - 2 * γ) + A * ((x * x - x + γ) / x) * ((x * x - x + γ) / x)) ∧
    (∀ A γ x : Rat, 0 < A → x ≠ 0 →
      A * (1 - 2 * γ) ≤ muonclipObj A A γ x ∧
      (x * x - x + γ = 0 → muonclipObj A A γ x = A * (1 - 2 * γ))) ∧
    (∀ A s x : Rat, 0 < A → (1 / 2 : Rat) ≤ s → 0 < x →
      muonclipObj A A (s * s) s ≤ muonclipObj A A (s * s) x ∧
      (x ≠ s → muonclipObj A A (s * s) s < muonclipObj A A (s * s) x)) ∧
    (∀ A s : Rat, 0 < A → 0 < s → s < (1 / 2 : Rat) →
      muonclipSecondDerivSym A s < 0 ∧
      (∀ x : Rat, 0 < x → x ≠ s → x + (s * s) / x < 2 - 2 * s →
        muonclipObj A A (s * s) x < muonclipObj A A (s * s) s) ∧
      muonclipObj A A (s * s) s - A * (1 - 2 * (s * s)) = A * (1 - 2 * s) * (1 - 2 * s) ∧
      0 < A * (1 - 2 * s) * (1 - 2 * s)) ∧
    (∀ A : Rat,
      ((1 / 4 : Rat) * (1 / 4) - 1 / 4 + 3 / 16 = 0 ∧
       (3 / 4 : Rat) * (3 / 4) - 3 / 4 + 3 / 16 = 0 ∧
       muonclipObj A A (3 / 16) (1 / 4) = A * (5 / 8) ∧
       muonclipObj A A (3 / 16) (3 / 4) = A * (5 / 8)) ∧
      ((1 / 8 : Rat) * (1 / 8) - 1 / 8 + 7 / 64 = 0 ∧
       (7 / 8 : Rat) * (7 / 8) - 7 / 8 + 7 / 64 = 0 ∧
       muonclipObj A A (7 / 64) (1 / 8) = A * (25 / 32) ∧
       muonclipObj A A (7 / 64) (7 / 8) = A * (25 / 32)) ∧
      (muonclipObj A A (1 / 9) (1 / 3) = A * (8 / 9) ∧
       A * (1 - 2 * (1 / 9)) = A * (7 / 9) ∧
       muonclipObj A A (1 / 9) (1 / 3) - A * (1 - 2 * (1 / 9)) = A * (1 / 9)) ∧
      (muonclipObj A A (1 / 16) (1 / 4) = A * (9 / 8) ∧
       A * (1 - 2 * (1 / 16)) = A * (7 / 8) ∧
       muonclipObj A A (1 / 16) (1 / 4) - A * (1 - 2 * (1 / 16)) = A * (1 / 4))) :=
  MuonclipAdamwSr.muonclip_pitchfork_symmetry_breaking_exact

theorem muonclip_rtn_overshoot_vs_rtz_safety :
    (rtnOvershootFactor 3 = 289 / 256 ∧
     rtnOvershootFactor 7 = 66049 / 65536 ∧
     rtnOvershootFactor 10 = 4198401 / 4194304 ∧
     rtzUndershootFactor 3 = 49 / 64 ∧
     rtzUndershootFactor 7 = 16129 / 16384) ∧
    (∀ (m : Nat) (γ S_max τ sQ sK sQ' sK' : Rat),
      0 < S_max → 0 < τ → γ = τ / S_max →
      0 ≤ sQ → 0 ≤ sK → sQ * sK = γ →
      0 ≤ sQ' → 0 ≤ sK' →
      sQ' ≤ (1 + invPow2Rat (m + 1)) * sQ →
      sK' ≤ (1 + invPow2Rat (m + 1)) * sK →
      sQ' * sK' * S_max ≤ rtnOvershootFactor m * τ) ∧
    (∀ τ : Rat, 0 < τ →
      ((9 / 8 : Rat) * (9 / 8)) / ((35 / 32 : Rat) * (35 / 32)) * τ = (1296 / 1225 : Rat) * τ ∧
      τ < (1296 / 1225 : Rat) * τ ∧
      ((129 / 128 : Rat) * (129 / 128)) / ((515 / 512 : Rat) * (515 / 512)) * τ =
        (266256 / 265225 : Rat) * τ ∧
      τ < (266256 / 265225 : Rat) * τ) ∧
    (∀ (γ S_max τ sQ sK sQ' sK' : Rat),
      0 < S_max → 0 < τ → γ = τ / S_max →
      0 ≤ sQ' → sQ' ≤ sQ → 0 ≤ sK' → sK' ≤ sK → sQ * sK = γ →
      sQ' * sK' * S_max ≤ τ) ∧
    (∀ (m : Nat) (γ S_max τ sQ sK sQ' sK' : Rat),
      1 ≤ m → 0 < S_max → 0 < τ → γ = τ / S_max →
      0 ≤ sQ → 0 ≤ sK → sQ * sK = γ →
      (1 - invPow2Rat m) * sQ ≤ sQ' →
      (1 - invPow2Rat m) * sK ≤ sK' →
      rtzUndershootFactor m * τ ≤ sQ' * sK' * S_max) :=
  MuonclipAdamwSr.muonclip_rtn_overshoot_vs_rtz_safety

theorem adamw_weight_decay_freeze_radii_exact :
    (∀ m : Nat, 1 ≤ m →
      (∀ ρ : Rat, (∀ f : Nat, f < 2 ^ m → wdFrozenRNE m f ρ) ↔ ρ ≤ wdTotalFreezeRadius m) ∧
      (∀ ρ : Rat, wdTotalFreezeRadius m < ρ → ρ < wdInteriorFreezeSup m →
        wdDecaysRNE m 0 ρ ∧ (∀ f : Nat, 1 ≤ f → f < 2 ^ m → wdFrozenRNE m f ρ)) ∧
      (∀ ρ : Rat, (∀ f : Nat, f < 2 ^ m → wdDecaysRNE m f ρ) ↔ wdUniversalDecayThreshold m ≤ ρ) ∧
      (∀ ρ : Rat, 1 / ((2 ^ (m + 1) + 4 : Nat) : Rat) < ρ → ρ < wdUniversalDecayThreshold m →
        wdFrozenRNE m 1 ρ ∧ (∀ f : Nat, f < 2 ^ m → f ≠ 1 → wdDecaysRNE m f ρ))) ∧
    ((wdTotalFreezeRadius 2 = 1 / 16 ∧ wdInteriorFreezeSup 2 = 1 / 14 ∧
      wdUniversalDecayThreshold 2 = 1 / 10) ∧
     (wdTotalFreezeRadius 3 = 1 / 32 ∧ wdInteriorFreezeSup 3 = 1 / 30 ∧
      wdUniversalDecayThreshold 3 = 1 / 18) ∧
     (wdTotalFreezeRadius 7 = 1 / 512 ∧ wdInteriorFreezeSup 7 = 1 / 510 ∧
      wdUniversalDecayThreshold 7 = 1 / 258) ∧
     (wdTotalFreezeRadius 10 = 1 / 4096 ∧ wdInteriorFreezeSup 10 = 1 / 4094 ∧
      wdUniversalDecayThreshold 10 = 1 / 2050)) :=
  MuonclipAdamwSr.adamw_weight_decay_freeze_radii_exact

theorem sr_ema_two_state_markov_exact :
    (∀ (l Δ r β : Rat), 0 < Δ → 0 ≤ r → r ≤ Δ → 0 ≤ β → β < 1 →
      (0 ≤ srEmaPi0 r Δ ∧ 0 ≤ srEmaPi1 r Δ ∧ srEmaPi0 r Δ + srEmaPi1 r Δ = 1) ∧
      (0 ≤ srEmaP01 β r Δ ∧ srEmaP01 β r Δ ≤ 1 ∧ 0 ≤ srEmaP10 β r Δ ∧ srEmaP10 β r Δ ≤ 1) ∧
      (srEmaPi0 r Δ * srEmaP01 β r Δ = srEmaPi1 r Δ * srEmaP10 β r Δ) ∧
      (srEmaPi0 r Δ * (1 - srEmaP01 β r Δ) + srEmaPi1 r Δ * srEmaP10 β r Δ = srEmaPi0 r Δ ∧
       srEmaPi0 r Δ * srEmaP01 β r Δ + srEmaPi1 r Δ * (1 - srEmaP10 β r Δ) = srEmaPi1 r Δ) ∧
      srEmaMean l Δ r = l + r ∧
      (srEmaVar l Δ r = r * (Δ - r) ∧ r * (Δ - r) ≤ (Δ * Δ) / 4) ∧
      srEmaLambda2 β r Δ = β ∧
      ((1 - srEmaP01 β r Δ) * (1 - srEmaP10 β r Δ) - srEmaP01 β r Δ * srEmaP10 β r Δ = β)) ∧
    (srEmaVarInflation (9 / 10) = 19 ∧ srEmaVarInflation (999 / 1000) = 1999) :=
  MuonclipAdamwSr.sr_ema_two_state_markov_exact

theorem preconditioner_jensen_bias_exact_sqrt_vs_v :
    (∀ a b s : Rat, a ≠ b → srDirectExpect a b s = s) ∧
    (∀ r_p t : Rat, 0 < r_p →
      jensenSqrtMax r_p - jensenSqrtFactor r_p t =
        ((r_p - 1) * (t - 1 / 2)) * ((r_p - 1) * (t - 1 / 2)) / r_p ∧
      jensenSqrtFactor r_p t ≤ jensenSqrtMax r_p ∧
      jensenSqrtFactor r_p (1 / 2) = jensenSqrtMax r_p) ∧
    (jensenSqrtMax 2 = 9 / 8 ∧ jensenSqrtFactor 2 (1 / 2) = 9 / 8 ∧
     jensenSqrtMax (3 / 2) = 25 / 24 ∧
     jensenSqrtMax (5 / 4) = 81 / 80 ∧
     jensenSqrtMax (9 / 8) = 289 / 288) ∧
    (∀ r t : Rat, 1 < r → 0 ≤ t → t ≤ 1 →
      27 * r * r * (r + 1) * (r + 1) * jensenVSq r t ≤
        4 * (r * r + r + 1) * (r * r + r + 1) * (r * r + r + 1) ∧
      jensenVSq r t ≤ jensenVMaxSq r ∧
      0 < jensenVOptT r ∧ jensenVOptT r < 1 ∧
      jensenVSq r (jensenVOptT r) = jensenVMaxSq r) ∧
    ((∀ r : Rat, r * r = 2 →
        4 * (r * r + r + 1) * (r * r + r + 1) * (r * r + r + 1) =
          27 * r * r * (r + 1) * (r + 1) * ((38 - 6 * r) / 27)) ∧
     ((14142 / 10000 : Rat) * (14142 / 10000) < 2 ∧
      2 < (14143 / 10000 : Rat) * (14143 / 10000)) ∧
     (∀ s : Rat, (14142 / 10000 : Rat) ≤ s → s ≤ (14143 / 10000 : Rat) →
        (10455 / 10000 : Rat) * (10455 / 10000) < (38 - 6 * s) / 27 ∧
        (38 - 6 * s) / 27 < (10456 / 10000 : Rat) * (10456 / 10000)) ∧
     ((27 / 10 : Rat) * ((10456 / 10000 : Rat) - 1) < (9 / 8 : Rat) - 1)) :=
  MuonclipAdamwSr.preconditioner_jensen_bias_exact_sqrt_vs_v

theorem asymmetric_muonclip_ratio_limit_exact :
    (∀ A B α : Rat, 0 < A → 0 < B →
      muonclipQuadApprox A B α - muonclipQuadApprox A B (B / (A + B)) =
        (A + B) * (α - B / (A + B)) * (α - B / (A + B)) ∧
      muonclipQuadApprox A B (B / (A + B)) ≤ muonclipQuadApprox A B α) ∧
    (∀ A B : Rat, 0 < A → 0 < B →
      let r := A / B
      muonclipQuadApprox A B (B / (A + B)) / muonclipQuadApprox A B (1 / 2) =
        4 * r / ((1 + r) * (1 + r)) ∧
      1 - 4 * r / ((1 + r) * (1 + r)) = ((r - 1) / (r + 1)) * ((r - 1) / (r + 1))) ∧
    ((1 - 4 * (4 : Rat) / ((1 + 4) * (1 + 4)) = 9 / 25) ∧
     (1 - 4 * (9 : Rat) / ((1 + 9) * (1 + 9)) = 16 / 25) ∧
     (1 - 4 * (16 : Rat) / ((1 + 16) * (1 + 16)) = 225 / 289)) ∧
    (∀ A B s : Rat, 0 < A → 0 < B → 0 < s → s < 1 →
      let r := A / B
      muonclipObj A B (s * s) 1 / muonclipObj A B (s * s) s =
        ((1 + s) * (1 + s)) / (r + 1) ∧
      1 - muonclipObj A B (s * s) 1 / muonclipObj A B (s * s) s =
        (r - s * s - 2 * s) / (r + 1)) :=
  MuonclipAdamwSr.asymmetric_muonclip_ratio_limit_exact

end MuonclipAdamwSrChallenge
