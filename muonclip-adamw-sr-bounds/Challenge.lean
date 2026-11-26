/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MuonclipAdamwSr.Defs

/-!
# Trusted Challenge Statements (`muonclip-adamw-sr-bounds`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. MuonClip pitchfork symmetry-breaking phase transition at `γ_c = 1/4`.
2. MuonClip RTN logit-cap overshoot (`289/256` FP8-E4M3, `66049/65536` BF16) vs universal RTZ safety.
3. Universal `m`-bit IEEE-754 RNE AdamW weight-decay freeze radii (`2^{-(m+2)}`), power-of-2-only decay gap,
   and universal decay threshold (`1 / (2^{m+1} + 2)`).
4. Exact 2-state SR-EMA Markov chain (zero stationary bias, `β`-independent variance, `λ_2 = β`,
   and asymptotic time-average variance inflation `(1 + β) / (1 - β)`).
5. Exact closed-form preconditioner Jensen bias comparing direct SR of `1/√v`, SR of `√v` (`9/8` at E4M0),
   and SR of `v` (`27 r^2 (r + 1)^2 J^2 ≤ 4 (r^2 + r + 1)^3`, strictly `> 2.7x` smaller at E4M0).
6. General asymmetric Frobenius norm-ratio (`r = A / B`) MuonClip perturbation savings.
-/

namespace MuonclipAdamwSrChallenge

open MuonclipAdamwSr

/-- Theorem 1 (Exact MuonClip Pitchfork Symmetry-Breaking Phase Transition at `γ_c = 1/4`):
    Proves the exact `r = 1` quartic factorization `(x^2 - γ)(x^2 - x + γ)`, the universal
    sum-of-squares identity `L(A, A, γ, x) = A(1 - 2γ) + A((x^2 - x + γ)/x)^2`, global optimality
    of symmetric `x = s = √γ` for all `s ≥ 1/2` (`γ ≥ 1/4`), strict local maximality (`L''(s) < 0`
    and open neighborhood descent) plus exact saving `A(1 - 2s)^2 > 0` for all `0 < s < 1/2`,
    and exact rational witnesses at `γ ∈ {3/16, 7/64, 1/9, 1/16}`. -/
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
       muonclipObj A A (1 / 16) (1 / 4) - A * (1 - 2 * (1 / 16)) = A * (1 / 4))) := by
  sorry

/-- Theorem 2 (MuonClip RTN Logit-Cap Overshoot vs Universal RTZ Safety):
    Proves exact RTN worst-case overshoot factors (`289/256` for FP8-E4M3, `66049/65536` for BF16,
    `4198401/4194304` for FP16), universal RTN upper bound, concrete realized RTN cap violations
    strictly exceeding `τ`, and the universal RTZ safety guarantee `s_Q' * s_K' * S_max ≤ τ`
    together with its worst-case undershoot lower bound `(1 - 2^{-m})^2 * τ`. -/
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
      rtzUndershootFactor m * τ ≤ sQ' * sK' * S_max) := by
  sorry

/-- Theorem 3 (Universal `m`-Bit IEEE-754 RNE AdamW Weight-Decay Freeze Radii):
    For every `m ≥ 1`, proves total RNE weight-decay freeze holds iff `ρ ≤ 2^{-(m+2)}`,
    only powers of 2 (`f = 0`) decay in `(2^{-(m+2)}, 1 / (2^{m+2} - 2))`, universal decay
    holds iff `ρ ≥ 1 / (2^{m+1} + 2)` with `f = 1` strictly the last mantissa to unfreeze,
    and instantiates exact values for FP8-E5M2 (`m = 2`), FP8-E4M3 (`m = 3`), BF16 (`m = 7`),
    and FP16 (`m = 10`). -/
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
      wdUniversalDecayThreshold 10 = 1 / 2050)) := by
  sorry

/-- Theorem 4 (Exact 2-State SR-EMA Markov Chain):
    For all `Δ > 0`, `0 ≤ r ≤ Δ`, `0 ≤ β < 1`, proves the exact stationary distribution
    `(1 - r/Δ, r/Δ)`, detailed balance and stationarity, exact zero bias `E_π[q_∞] = l + r`,
    exact `β`-independent stationary variance `r(Δ - r) ≤ Δ^2 / 4`, exact second eigenvalue
    `λ_2 = trace(P) - 1 = det(P) = β`, and asymptotic time-average variance inflation
    `(1 + β) / (1 - β)` (`19` at `β = 9/10`, `1999` at `β = 999/1000`). -/
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
    (srEmaVarInflation (9 / 10) = 19 ∧ srEmaVarInflation (999 / 1000) = 1999) := by
  sorry

/-- Theorem 5 (Exact Closed-Form Preconditioner Jensen Bias: `SR(1/√v)` vs `SR(√v)` vs `SR(v)`):
    Proves direct SR of `1/√v` has exact zero bias (`J = 1`), SR of `√v` on `[1, r_p]` attains
    exact worst-case `(r_p + 1)^2 / (4 r_p)` at midpoint `t = 1/2` (`9/8` at E4M0, `25/24` at E3M1,
    `81/80` at E2M2, `289/288` at E4M3), SR of `v` on `[1, r^2]` satisfies the universal cubic bound
    `27 r^2 (r + 1)^2 J_v(r, t)^2 ≤ 4 (r^2 + r + 1)^3` attained at `t*(r) = (r + 2) / (3 (r + 1))`,
    and at E4M0 (`r^2 = 2`) reduces identically to `(38 - 6 r) / 27 ∈ (1.0455^2, 1.0456^2)`,
    strictly `> 2.7x` smaller bias than `9/8`. -/
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
     ((27 / 10 : Rat) * ((10456 / 10000 : Rat) - 1) < (9 / 8 : Rat) - 1)) := by
  sorry

/-- Theorem 6 (Universal Asymmetric MuonClip Frobenius Norm-Ratio Laws):
    For any positive Frobenius norm squares `A, B > 0` (`r = A / B`), proves that the
    leading-order quadratic objective `A α^2 + B (1 - α)^2` is uniquely minimized at
    `α* = B / (A + B)` with exact perturbation ratio `4 r / (1 + r)^2` and exact saving
    `((r - 1) / (r + 1))^2` (`9/25` at `r = 4`, `16/25` at `r = 9`, `225/289` at `r = 16`),
    and proves the exact strong-clipping (`γ = s^2`) ratio `L(1) / L(s) = (1 + s)^2 / (r + 1)`. -/
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
        (r - s * s - 2 * s) / (r + 1)) := by
  sorry

end MuonclipAdamwSrChallenge
